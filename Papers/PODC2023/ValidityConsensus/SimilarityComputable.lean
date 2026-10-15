import Papers.PODC2023.ValidityConsensus.Similarity
import Mathlib.Computability.Partrec
import Mathlib.Data.Fintype.Pi

/-!
# On the Validity of Consensus — Theorems 2 and 3 with Turing-computable `Λ`

The paper's similarity condition `C_S` (Definition 2) requires the function `Λ` to be
*Turing-computable*. We use Mathlib's notion `Computable` (partial recursive and total, via
`Primcodable` encodings). Processes are `Fin n`; then `Config (Fin n) VI = Fin n → Option VI` is
`Primcodable` (`Primcodable.finArrow`) as soon as `VI` is.

* `Algorithm.IsComputable A`: the algorithm is a computable state machine (`init`, `step`,
  `send`, `decide` are computable).
* `Algorithm.lockStep A c d`: explicit lock-step simulation of the canonical synchronous run
  `canonRun c d` (`canonRun_st_eq_lockStep`), computable in `(c, τ)` (`lockStep_computable`).
* `similarityCondition_computable_auth` / `similarityCondition_computable` (**Theorem 3**, in the
  authenticated / unauthenticated model): `Λ c` is the first decision of a process of
  `π(c)` in the canonical run of `c`, found by unbounded search (`Nat.rfindOpt`), which terminates
  by Termination.
* `alwaysAdmissible_computable` (**Theorem 2**): immediate from Theorem 1.
-/

namespace Cslib.Byzantine.PartialSync

open Finset

/-! ### Computable algorithms and the lock-step simulation -/

section LockStep

variable {P M S VI VO : Type*}

/-- Explicit lock-step simulation of the canonical synchronous run of configuration `c`
(dummy proposal `d` outside `π(c)`): at every time each process receives exactly the messages
sent at that time by the processes of `π(c)`. -- CSLib candidate -/
def Algorithm.lockStep (A : Algorithm P M S VI VO) (c : Config P VI) (d : VI) : ℕ → P → S
  | 0 => fun p => A.init p ((c p).getD d)
  | τ + 1 => fun p => A.step p (A.lockStep c d τ p)
      (fun q => if c q = none then [] else A.send q (A.lockStep c d τ q) p)

variable [Fintype P] [DecidableEq P]

/-- The canonical run is the lock-step simulation. -- CSLib candidate -/
theorem canonRun_st_eq_lockStep (A : Algorithm P M S VI VO) (c : Config P VI) (d : VI)
    (τ : ℕ) : (canonRun (M := M) c d).st A τ = A.lockStep c d τ := by
  induction τ with
  | zero => funext p; simp [Algorithm.lockStep, canonRun]
  | succ τ ih =>
    funext p
    rw [Run.st_succ, ih]
    simp only [Algorithm.lockStep]
    congr 1
    funext q
    rw [Run.inbox_eq_flatMap, List.range_succ, List.flatMap_append]
    have h1 : ((List.range τ).flatMap fun τ' => (canonRun (M := M) c d).dlv A q τ' p τ) = [] := by
      refine List.flatMap_eq_nil_iff.mpr fun τ' hτ' => ?_
      simp only [List.mem_range] at hτ'
      exact Run.dlv_eq_nil_of_ne _ _ (by simp [canonRun]; omega)
    rw [h1]
    have hdl : (canonRun (M := M) c d).dl q τ p = τ := rfl
    simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Run.dlv,
      hdl, ite_true]
    by_cases hq : c q = none
    · rw [Run.out_of_faulty _ _ (by simp [canonRun, hq])]; simp [hq, canonRun]
    · rw [Run.out_of_correct _ _ (by simp [canonRun, Option.isSome_iff_ne_none, hq]), ih]
      simp [hq]

end LockStep

section Computable

variable {n : ℕ} {M S VI VO : Type*} [Primcodable M] [Primcodable S] [Primcodable VI]
  [Primcodable VO]

/-- An algorithm on processes `Fin n` is *computable* if it is a computable state machine:
the initial state (as a function of process and proposal), the transition function (of process,
state and received messages), the outgoing messages (of sender, state and receiver) and the
decision (of process and state) are all `Computable`. -- CSLib candidate -/
structure Algorithm.IsComputable (A : Algorithm (Fin n) M S VI VO) : Prop where
  init : Computable₂ A.init
  step : Computable fun x : Fin n × S × (Fin n → List M) => A.step x.1 x.2.1 x.2.2
  send : Computable fun x : Fin n × S × Fin n => A.send x.1 x.2.1 x.2.2
  decide : Computable₂ A.decide

omit [Primcodable M] [Primcodable S] [Primcodable VI] [Primcodable VO] in
/-- A function into `Fin n → σ` is computable if all its components are. -- CSLib candidate -/
theorem _root_.Computable.finArrow_of {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → Fin n → σ} (h : ∀ i, Computable fun a => f a i) : Computable f :=
  (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn h)).of_eq fun a => by
    funext i; simp

/-- The lock-step simulation of a computable algorithm is computable (in the configuration and
the time). -- CSLib candidate -/
theorem Algorithm.lockStep_computable {A : Algorithm (Fin n) M S VI VO} (hA : A.IsComputable)
    (d : VI) : Computable fun x : Config (Fin n) VI × ℕ => A.lockStep x.1 d x.2 := by
  open Computable in
  have key : ∀ x : Config (Fin n) VI × ℕ, A.lockStep x.1 d x.2 =
      Nat.rec (motive := fun _ => Fin n → S) (fun p => A.init p ((x.1 p).getD d))
        (fun _ IH p => A.step p (IH p)
          (fun q => bif (x.1 q).isSome then A.send q (IH q) p else [])) x.2 := by
    rintro ⟨c, τ⟩
    induction τ with
    | zero => rfl
    | succ τ ih =>
      simp only [Algorithm.lockStep] at ih ⊢
      rw [ih]
      funext p
      congr 1
      funext q
      cases c q <;> rfl
  open Computable in
  refine (nat_rec (f := fun x : Config (Fin n) VI × ℕ => x.2)
    (g := fun x p => A.init p ((x.1 p).getD d))
    (h := fun x y p => A.step p (y.2 p)
          (fun q => bif (x.1 q).isSome then A.send q (y.2 q) p else [])) snd
    (finArrow_of fun p => hA.init.comp (const p)
      (option_getD (fin_app.comp fst (const p)) (const d)))
    (finArrow_of fun p => hA.step.comp (pair (const p) (pair (fin_app.comp (snd.comp snd) (const p))
      (finArrow_of fun q => cond (Primrec.option_isSome.to_comp.comp
          (fin_app.comp (fst.comp fst) (const q)))
        (hA.send.comp (pair (const q) (pair (fin_app.comp (snd.comp snd) (const q)) (const p))))
        (const []))))).to₂).of_eq fun x => (key x).symm

end Computable

end Cslib.Byzantine.PartialSync

namespace ValidityConsensus

open Finset Cslib.Byzantine.PartialSync Encodable

variable {n : ℕ} {M S VI VO : Type*} [Primcodable M] [Primcodable S] [Primcodable VI]
  [Primcodable VO] {t δ : ℕ} {A : Algorithm (Fin n) M S VI VO}
  {val : ValidityProperty (Fin n) VI VO}

/-- The search space for `Λ`: index `k = ⟪τ, i⟫` asks for the decision at time `τ` of the
process encoded by `i`, if it belongs to `π(c)`, in the lock-step canonical run of `c`. -/
def decAt (A : Algorithm (Fin n) M S VI VO) (d : VI) (c : Config (Fin n) VI) (k : ℕ) :
    Option VO :=
  (decode (α := Fin n) k.unpair.2).bind fun p =>
    bif (c p).isSome then A.decide p (A.lockStep c d k.unpair.1 p) else none

theorem decAt_computable (hA : A.IsComputable) (d : VI) : Computable₂ (decAt A d) := by
  open Computable in
  exact option_bind (Computable.decode.comp (snd.comp (unpair.comp snd)))
    (cond (Primrec.option_isSome.to_comp.comp (fin_app.comp (fst.comp fst) snd))
      (hA.decide.comp snd (fin_app.comp ((Algorithm.lockStep_computable hA d).comp
        (pair (fst.comp fst) (fst.comp (unpair.comp (snd.comp fst))))) snd))
      (const none)).to₂

omit [Primcodable M] [Primcodable S] [Primcodable VI] [Primcodable VO] in
theorem decAt_spec {d : VI} {c : Config (Fin n) VI} {k : ℕ} {v : VO}
    (h : decAt A d c k = some v) :
    ∃ p, c p ≠ none ∧ (canonRun (M := M) c d).Decides A p v := by
  unfold decAt at h
  obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.mp h
  cases hcp : c p with
  | none => simp [hcp] at hp
  | some w =>
    refine ⟨p, by simp [hcp], k.unpair.1, ?_⟩
    rw [canonRun_st_eq_lockStep]
    simpa [hcp] using hp

/-- **Theorem 3 of [Civit et al., PODC 2023]** (with the computability requirement), in the
authenticated model `Au` (with an unforging algorithm): if a computable algorithm solves
consensus with validity property `val` (and `t < n`), then `val` satisfies the similarity
condition `C_S` with a *Turing-computable* `Λ`.

`Λ c` is the first decision (in the order of `Nat.rfindOpt` over pairs ⟪time, process⟫) of a
process of `π(c)` in the canonical synchronous execution of `c`; to make `Λ` total, a
configuration `c` that is not an input configuration is first replaced by the failure-free
configuration with all proposals equal to a fixed value. -/
theorem similarityCondition_computable_auth {K : Type*} {Au : Auth (Fin n) M K} [Nonempty VI]
    (hU : A.Unforging Au) (hA : SolvesConsensusAuth Au t δ A val)
    (hc : A.IsComputable) (htn : t < n) :
    ∃ Λ : Config (Fin n) VI → VO, Computable Λ ∧
      ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c) := by
  classical
  set d := Classical.arbitrary VI
  let c₀ : Config (Fin n) VI := fun _ => some d
  let norm : Config (Fin n) VI → Config (Fin n) VI := fun c =>
    if IsInputConfig t c then c else c₀
  have hnorm : ∀ c, IsInputConfig t (norm c) := by
    intro c
    by_cases h : IsInputConfig t c
    · simp [norm, h]
    · simp only [norm, h, ite_false]
      unfold IsInputConfig; simp [Config.procs, c₀]
  have hnormc : Computable norm := by
    open Computable in
    let F : (Fin n → Bool) → Bool := fun b => decide (n - t ≤ (univ.filter fun i => b i).card)
    refine (cond ((Primrec.dom_finite F).to_comp.comp
      (finArrow_of fun i => Primrec.option_isSome.to_comp.comp (fin_app.comp .id (const i))))
      .id (const c₀)).of_eq fun c => ?_
    simp [norm, F, IsInputConfig, Config.procs]
  have hdom : ∀ c, IsInputConfig t c → (Nat.rfindOpt (decAt A d c)).Dom := by
    intro c hc'
    obtain ⟨p, hp⟩ : c.procs.Nonempty := card_pos.mp (by unfold IsInputConfig at hc'; simp at hc'; omega)
    have hpF : p ∉ (canonRun (M := M) c d).faulty := by
      simp only [canonRun, Finset.mem_compl, not_not]; exact hp
    obtain ⟨v, τ, hv⟩ := hA.termination _ (canonRun.valid c d hc' δ) (canonRun_authValid c d) p hpF
    rw [canonRun_st_eq_lockStep] at hv
    refine Nat.rfindOpt_dom.mpr ⟨Nat.pair τ (encode p), v, ?_⟩
    simp only [Config.mem_procs] at hp
    simp [decAt, Nat.unpair_pair, encodek, hp, hv]
  have hpart : Partrec fun c => Nat.rfindOpt (decAt A d (norm c)) :=
    Partrec.rfindOpt ((decAt_computable hc d).comp (hnormc.comp .fst) .snd)
  refine ⟨fun c => (Nat.rfindOpt (decAt A d (norm c))).get (hdom _ (hnorm c)),
    hpart.of_eq_tot fun c => Part.get_mem _, fun c hc' => ?_⟩
  have hc'' : IsInputConfig t c := by unfold IsInputConfig; rw [hc']
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec (Part.get_mem (hdom _ (hnorm c)))
  beta_reduce
  generalize (Nat.rfindOpt (decAt A d (norm c))).get _ = v at hk ⊢
  rw [show norm c = c from ite_eq_left_iff.mpr fun h => absurd hc'' h] at hk
  obtain ⟨p, hp, hdec⟩ := decAt_spec hk
  intro c' hc' hsim
  refine canonical_similarity_auth hU hA (canonRun.valid c d hc'' δ) (canonRun.canonical c d) ?_
    hdec hc' (by rwa [canonRun.inputConf])
  simp [canonRun, Option.isSome_iff_ne_none, hp]

/-- **Theorem 3 of [Civit et al., PODC 2023]** (with the computability requirement), in the
unauthenticated model: the special case `Au = Auth.none` of
`similarityCondition_computable_auth`. -/
theorem similarityCondition_computable [Nonempty VI] (hA : SolvesConsensus t δ A val)
    (hc : A.IsComputable) (htn : t < n) :
    ∃ Λ : Config (Fin n) VI → VO, Computable Λ ∧
      ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c) :=
  similarityCondition_computable_auth A.unforging_none (hA.auth _) hc htn

omit [Primcodable M] [Primcodable S] [Primcodable VI] in
/-- **Theorem 2 of [Civit et al., PODC 2023]** (with the computability requirement): if
`n ≤ 3t`, every solvable validity property is trivial, and the always-admissible value is
produced by a Turing-computable (constant) function.

Once the elements of `V_O` are encodable (`Primcodable VO`), every constant function is
computable, so this has no content beyond Theorem 1 (`trivial_of_solvable`). -/
theorem alwaysAdmissible_computable [Nonempty VI] (h : val.Solvable t δ) (ht : 0 < t)
    (htn : t < n) (hn : n ≤ 3 * t) :
    ∃ f : Unit → VO, Computable f ∧ ∀ c, IsInputConfig t c → f () ∈ val c := by
  obtain ⟨v, hv⟩ := trivial_of_solvable h ht (by simpa using htn) (by simpa using hn)
  exact ⟨fun _ => v, Computable.const v, hv⟩

end ValidityConsensus
