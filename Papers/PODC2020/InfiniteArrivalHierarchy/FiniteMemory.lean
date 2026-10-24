import Podc.Computability.Distributed.SharedMemory.Arrival.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Pi

/-!
# Infinite memory allocation is not necessary in `Mⁿ₁` (Section 4, Lemma 4)

Perrin, Mostéfaoui, Bonin, *Extending the Wait-free Hierarchy to Multi-Threaded Systems*,
PODC 2020, Lemma 4: *if `cons⟨B⟩` can be implemented in `MAⁿ₁[O]`, then it can be implemented in
`Mⁿ₁[O]`*.

Model: processes `p₀, …, p_{n-1}` (schedules `belowN n` / `boundedBy n`), binary inputs, arbitrary
objects `T : ι → ObjSpec` (any mix of objects of any types), all allocated at set-up; `ι` may be
infinite (infinite allocation). The conclusion is an algorithm with the same code whose memory is
the finite set `S` of objects (a finite `ι`; no allocation at all at run time).

* `finite_reach` (**Claim 1**): for each input vector, only finitely many configurations are
  reachable (König's lemma: the execution tree is finitely branching, and an infinite branch would
  contain a process taking infinitely many steps without deciding — wait-freedom);
* `finite_poised`: hence only finitely many objects are ever accessed;
* `restrictAlg`, `solvesCons_restrict` (**Lemma 4**): the algorithm restricted to these objects is
  a wait-free binary consensus algorithm with finitely many objects.

Only wait-freedom is used for the finiteness; correctness is transferred by a simulation.
-/

namespace Podc.InfiniteArrivalHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {Y : Type}

section Reach

variable {X : Type} {A : Alg T ℕ X Y} {n : ℕ}

/-- Configurations reachable from `C` by steps of `p₀, …, p_{n-1}`. -/
def reachFrom (A : Alg T ℕ X Y) (n : ℕ) (C : Cfg A) : Set (Cfg A) :=
  {D | ∃ τ, belowN n τ ∧ A.run C τ = D}

lemma reachFrom_subset (C : Cfg A) :
    reachFrom A n C ⊆ {C} ∪ ⋃ p ∈ {p | p < n ∧ ∃ i, C.Poised p i}, reachFrom A n (C.step p) := by
  rintro D ⟨τ, hτ, rfl⟩
  induction τ generalizing C with
  | nil => left; rfl
  | cons p τ ih =>
    have hp : p < n := hτ p (by simp)
    have hτ' : belowN n τ := fun q hq => hτ q (by simp [hq])
    rcases Cfg.out_or_poised C p with ⟨v, hv⟩ | ⟨i, hi⟩
    · rw [Alg.run_cons, Cfg.step_of_out hv]; exact ih C hτ'
    · right
      exact Set.mem_biUnion (x := p) ⟨hp, i, hi⟩ ⟨τ, hτ', rfl⟩

/-- **Claim 1** (in the proof of Lemma 4). For a wait-free algorithm of `n` processes, only
finitely many configurations are reachable from any configuration reachable from an initial one
(König's lemma). -/
theorem finite_reach (hwf : WaitFree A (boundedBy n)) (x : ℕ → X) :
    (reachFrom A n (A.initCfg x)).Finite := by
  classical
  by_contra hinf
  -- an infinite subtree has an infinite child through a poised process
  have hstep : ∀ C : {C : Cfg A // (reachFrom A n C).Infinite},
      ∃ p, p < n ∧ (∃ i, C.1.Poised p i) ∧ (reachFrom A n (C.1.step p)).Infinite := by
    intro ⟨C, hC⟩
    by_contra hno
    push Not at hno
    apply hC
    refine ((Set.finite_singleton C).union ?_).subset (reachFrom_subset C)
    refine Set.Finite.biUnion ((Set.finite_lt_nat n).subset (fun p hp => hp.1)) ?_
    intro p ⟨hp, hi⟩
    exact hno p hp hi
  choose nx hnx hnxp hnxi using hstep
  let c : ℕ → {C : Cfg A // (reachFrom A n C).Infinite} := fun k =>
    Nat.rec ⟨A.initCfg x, hinf⟩ (fun _ C => ⟨C.1.step (nx C), hnxi C⟩) k
  let s : ℕ → ℕ := fun k => nx (c k)
  have hc : ∀ t, A.exec x (pre s t) = (c t).1 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [pre_succ, Alg.exec_concat, ih]
  have hs : boundedBy n s := fun t => hnx _
  obtain ⟨p, hp⟩ := exists_infOften_of_finite (Set.finite_lt_nat n) (fun t => hnx (c t))
  obtain ⟨t, v, hout⟩ := hwf x s hs p hp
  obtain ⟨k, hk, hkp⟩ := hp t
  obtain ⟨i, hi⟩ := hnxp (c k)
  have hout' : ((c k).1).Out p v := by
    rw [← hc k]
    obtain ⟨τ, hτ⟩ := pre_prefix s hk
    rw [← hτ, Alg.exec_append]; exact Alg.Cfg.Out.run hout τ
  have : s k = p := hkp
  simp only [s] at this
  rw [this] at hi
  exact Cfg.not_out_of_poised hi v hout'

end Reach

/-- The objects accessed by `p₀, …, p_{n-1}` in executions of `p₀, …, p_{n-1}`. -/
def usedObjs (A : Alg T ℕ Bool Y) (n : ℕ) : Set ι :=
  {i | ∃ x σ, belowN n σ ∧ ∃ p < n, (A.exec x σ).Poised p i}

/-- Only finitely many objects are ever accessed by a wait-free algorithm of `n` processes with
binary inputs. -/
theorem finite_usedObjs {A : Alg T ℕ Bool Y} {n : ℕ} (hwf : WaitFree A (boundedBy n)) :
    (usedObjs A n).Finite := by
  classical
  -- inputs that are `false` outside `p₀, …, p_{n-1}`
  let ext : (Fin n → Bool) → (ℕ → Bool) := fun f p => if h : p < n then f ⟨p, h⟩ else false
  have hsub : usedObjs A n ⊆ ⋃ f : Fin n → Bool, ⋃ C ∈ reachFrom A n (A.initCfg (ext f)),
      ⋃ p ∈ {p | p < n}, {i | C.Poised p i} := by
    rintro i ⟨x, σ, hσ, p, hp, hi⟩
    let f : Fin n → Bool := fun q => x q
    have hag : AgreeOn {q | q < n} (A.initCfg x) (A.initCfg (ext f)) :=
      Alg.initCfg_agreeOn (fun q hq => by simp [ext, f, show q < n from hq])
    have h2 := Alg.run_agreeOn hag (σ := σ) hσ
    simp only [Set.mem_iUnion]
    exact ⟨f, A.run (A.initCfg (ext f)) σ, ⟨σ, hσ, rfl⟩, p, hp,
      (h2.poised_iff (show p ∈ {q | q < n} from hp) i).1 hi⟩
  refine Set.Finite.subset ?_ hsub
  refine Set.finite_iUnion (fun f => ?_)
  refine Set.Finite.biUnion (finite_reach hwf _) (fun C _ => ?_)
  refine Set.Finite.biUnion (Set.finite_lt_nat n) (fun p _ => ?_)
  refine Set.Subsingleton.finite ?_
  intro i hi j hj
  exact Cfg.Poised.unique hi hj

/-! ### Restriction to finitely many objects -/

open Classical in
/-- The algorithm `A` restricted to the objects of `S` (an access to an object outside `S`, which
never happens for `S ⊇ usedObjs A n`, is replaced by the output of a default value `d`). -/
noncomputable def restrictAlg {X : Type} (A : Alg T ℕ X Y) (S : Set ι) (d : Y) :
    Alg (fun i : S => T i) ℕ X Y where
  L := A.L
  init := A.init
  act l := match A.act l with
    | .access i o k => if h : i ∈ S then .access ⟨i, h⟩ o k else .out d
    | .out v => .out v
  mem₀ i := A.mem₀ i

section Restrict

open Classical

variable {A : Alg T ℕ Bool Y} {n : ℕ} {S : Set ι} {d : Y}

lemma restrict_act_out {l : A.L} {v : Y} (h : A.act l = .out v) :
    (restrictAlg A S d).act l = .out v := by
  simp only [restrictAlg]; rw [h]

lemma restrict_act_access {l : A.L} {i : ι} {o : (T i).Op} {k : (T i).Resp → A.L}
    (h : A.act l = .access i o k) (hi : i ∈ S) :
    (restrictAlg A S d).act l = .access ⟨i, hi⟩ o k := by
  simp only [restrictAlg]; rw [h]; simp [hi]

/-- The restricted algorithm simulates `A` step by step on schedules of `p₀, …, p_{n-1}`. -/
lemma restrict_exec (hS : usedObjs A n ⊆ S) (x : ℕ → Bool) {σ : List ℕ} (hσ : belowN n σ) :
    ((restrictAlg A S d).exec x σ).loc = (A.exec x σ).loc ∧
      ∀ i : S, ((restrictAlg A S d).exec x σ).mem i = (A.exec x σ).mem i.1 := by
  induction σ using List.reverseRecOn with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | append_singleton σ p ih =>
    have hσ' : belowN n σ := fun q hq => hσ q (by simp [hq])
    have hp : p < n := hσ p (by simp)
    obtain ⟨ih1, ih2⟩ := ih hσ'
    rw [Alg.exec_concat, Alg.exec_concat]
    set C := A.exec x σ
    set C' := (restrictAlg A S d).exec x σ
    rcases Cfg.out_or_poised C p with ⟨v, hv⟩ | ⟨i, o, k, hi⟩
    · have hv' : C'.Out p v := by
        unfold Cfg.Out; rw [ih1]; exact restrict_act_out hv
      rw [Cfg.step_of_out hv, Cfg.step_of_out hv']
      exact ⟨ih1, ih2⟩
    · have hiS : i ∈ S := hS ⟨x, σ, hσ', p, hp, o, k, hi⟩
      have hi' : (restrictAlg A S d).act (C'.loc p) = .access ⟨i, hiS⟩ o k := by
        rw [ih1]; exact restrict_act_access hi hiS
      rw [Cfg.step_of_access hi, Cfg.step_of_access hi']
      have hmi : C'.mem ⟨i, hiS⟩ = C.mem i := ih2 _
      refine ⟨?_, fun j => ?_⟩
      · rw [hmi, ih1]; rfl
      · by_cases hj : j = ⟨i, hiS⟩
        · subst hj; simp [hmi]
        · have hj' : j.1 ≠ i := fun e => hj (Subtype.ext e)
          simp [Function.update_of_ne hj, Function.update_of_ne hj', ih2 j]

lemma restrict_out_iff (hS : usedObjs A n ⊆ S) (x : ℕ → Bool) {σ : List ℕ} (hσ : belowN n σ)
    {p : ℕ} (hp : p < n) (v : Y) :
    ((restrictAlg A S d).exec x σ).Out p v ↔ (A.exec x σ).Out p v := by
  have h1 := (restrict_exec (d := d) hS x hσ).1
  unfold Cfg.Out
  rw [h1]
  rcases Cfg.out_or_poised (A.exec x σ) p with ⟨w, hw⟩ | ⟨i, o, k, hi⟩
  · unfold Cfg.Out at hw
    rw [restrict_act_out hw, hw]
    constructor <;> intro h <;> (cases h; rfl)
  · have hiS : i ∈ S := hS ⟨x, σ, hσ, p, hp, o, k, hi⟩
    rw [restrict_act_access hi hiS, hi]
    constructor <;> intro h <;> cases h

end Restrict

/-- **Lemma 4.** If binary consensus can be solved (wait-free, by `p₀, …, p_{n-1}`) with infinite
memory allocation (`MAⁿ₁[O]`, an arbitrary family of objects `T`), then it can be solved by an
algorithm that only uses a finite set `S` of these objects (`Mⁿ₁[O]`, everything allocated at
set-up): the same code restricted to `S`. -/
theorem consensus_finiteMemory {A : Alg T ℕ Bool Bool} {n : ℕ}
    (hA : SolvesCons A (belowN n) (boundedBy n)) :
    ∃ S : Set ι, S.Finite ∧ SolvesCons (restrictAlg A S false) (belowN n) (boundedBy n) := by
  refine ⟨usedObjs A n, finite_usedObjs hA.waitFree, ⟨?_, ?_, ?_⟩⟩
  · intro x σ hσ p hp q hq v w hv hw
    exact hA.agreement x σ hσ p hp q hq v w
      ((restrict_out_iff subset_rfl x hσ (hσ p hp) v).1 hv)
      ((restrict_out_iff subset_rfl x hσ (hσ q hq) w).1 hw)
  · intro x σ hσ p hp v hv
    exact hA.validity x σ hσ p hp v ((restrict_out_iff subset_rfl x hσ (hσ p hp) v).1 hv)
  · intro x s hs p hinf
    obtain ⟨t, v, h⟩ := hA.waitFree x s hs p hinf
    have hp : p < n := by obtain ⟨u, -, hu⟩ := hinf 0; rw [← hu]; exact hs u
    have hpre : belowN n (pre s t) := fun q hq => by
      obtain ⟨u, -, hu⟩ := mem_pre.1 hq; rw [← hu]; exact hs u
    exact ⟨t, v, (restrict_out_iff subset_rfl x hpre hp v).2 h⟩

/-- The memory of the restricted algorithm is finite (non-vacuity of "finite memory"). -/
lemma finite_restrict_objs {A : Alg T ℕ Bool Bool} {n : ℕ} (hwf : WaitFree A (boundedBy n)) :
    Finite (usedObjs A n) := (finite_usedObjs hwf).to_subtype

end Podc.InfiniteArrivalHierarchy
