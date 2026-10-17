import Papers.PODC2024.AllBAExpensive.Containment
import Podc.PartialSync.Containment
import Podc.PartialSync.Computable
import Cslib.Computability.Distributed.Byzantine.PartialSync.BinaryConsensus

/-!
# All Byzantine Agreement Problems Are Expensive — §5: solvability in synchrony

Synchrony = runs with `gst = 0` of the partially synchronous model (`Cslib.Byzantine.PartialSync.Sync`).

* `ContainmentCondition t val` (**Definition 3**, CC): some `Γ` maps every input configuration
  `c` to a value admissible for every input configuration contained in `c`.
  `ContainmentConditionComputable`: the same with a Turing-computable `Γ` (processes `Fin n`).
* **Lemma 8** (necessity of CC): `containmentCondition_of_solvesConsensusAuthSync`,
  `containmentCondition_of_solvableAuthSync`, `containmentCondition_of_solvableSync`, and the
  computable versions `containmentConditionComputable_of_solvesConsensusAuthSync` /
  `..._of_solvesConsensusSync` (for computable algorithms, `Γ` is computable).
* Interactive consistency: `icValidity`, `ICSolvableSync`, `ICSolvableAuthSync`.
* **Lemma 9** (sufficiency of CC), Algorithm 2 = `reduction A Γ` (a decision post-processing
  `Algorithm.mapDecide`, so it sends exactly the messages of the IC algorithm,
  `Run.msgsUpTo_mapDecide`): `solvesConsensusAuthSync_reduction`,
  `solvableAuthSync_of_containmentCondition`, `solvableSync_of_containmentCondition` (shared
  library `Podc.PartialSync.Containment`). With IC solvability as a hypothesis, Lemmas 8 and 9 give the
  CC characterisations `solvableAuthSync_iff_containmentCondition`,
  `solvableSync_iff_containmentCondition` (Theorem 4 modulo Lemma 10).
* **Theorem 5**: `strongValidity_not_containmentCondition`, `strongValidity_not_solvableAuthSync`
  (strong consensus is not authenticated-solvable in synchrony if `n ≤ 2t`).
* **Counterexample to Lemma 10 / Theorem 4 (unauthenticated part)**: `ic2` solves interactive
  consistency in synchrony whenever `t = 0` or `n ≤ 2` (`ic2_solves`); hence for `n = 2`, `t = 1`
  (so `n ≤ 3t`) interactive consistency and weak consensus are non-trivial problems that are
  unauthenticated-solvable (`lemma10_counterexample`, `lemma10_counterexample_ic`, `not_lemma10`).
-/

namespace AllBAExpensive

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO} {Au : Auth P M K}

/-! ### Definition 3: the containment condition -/

/-- **Definition 3** of [AllBAExpensive] (containment condition, CC): there is a function `Γ`
such that for every input configuration `c`, `Γ c` is admissible for every input configuration
`c'` contained in `c` (`c ⊒ c'`). The paper additionally requires `Γ` to be Turing-computable;
see `ContainmentConditionComputable`. -/
abbrev ContainmentCondition (t : ℕ) (val : ValidityProperty P VI VO) : Prop :=
  val.ContainmentCondition t

/-! ### Lemma 8: necessity of CC -/

/-- **Lemma 8** of [AllBAExpensive] (necessity of CC), authenticated model: if an unforging
algorithm solves `val`-agreement in synchrony with `t < n`, then `val` satisfies CC. `Γ c` is a
value decided in the canonical synchronous execution of `c`. -/
theorem containmentCondition_of_solvesConsensusAuthSync [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A val) (htn : t < Fintype.card P) :
    ContainmentCondition t val := by
  classical
  set d := Classical.arbitrary VI
  have hex : ∀ c, IsInputConfig t c → ∃ v, ∃ p ∉ (canonRun (M := M) c d).faulty,
      (canonRun (M := M) c d).Decides A p v := by
    intro c hc
    obtain ⟨p, hp⟩ : c.procs.Nonempty := card_pos.mp (by unfold IsInputConfig at hc; omega)
    have hpF : p ∉ (canonRun (M := M) c d).faulty := by
      simp only [canonRun, mem_compl, not_not]; exact hp
    obtain ⟨v, hv⟩ := hA.termination _ (canonRun.valid c d hc δ) (canonRun_authValid c d) rfl
      p hpF
    exact ⟨v, p, hpF, hv⟩
  have hc₀ : IsInputConfig t (fun _ : P => some d) := by
    unfold IsInputConfig; simp [Config.procs]
  have : Nonempty VO := ⟨(hex _ hc₀).choose⟩
  refine ⟨fun c => if h : IsInputConfig t c then (hex c h).choose else Classical.arbitrary VO,
    fun c hc c' hc' hcont => ?_⟩
  simp only [hc, ↓reduceDIte]
  obtain ⟨p, hpF, hv⟩ := (hex c hc).choose_spec
  exact containment_auth hU hA htn (canonRun.valid c d hc δ) (canonRun_authValid c d) rfl hpF hv
    hc' (by rwa [canonRun.inputConf])

/-- **Lemma 8** of [AllBAExpensive], unauthenticated model. -/
theorem containmentCondition_of_solvesConsensusSync [Nonempty VI]
    (hA : SolvesConsensusSync t δ A val) (htn : t < Fintype.card P) :
    ContainmentCondition t val :=
  containmentCondition_of_solvesConsensusAuthSync A.unforging_none hA htn

/-- **Lemma 8** of [AllBAExpensive]: an authenticated-solvable problem satisfies CC. -/
theorem containmentCondition_of_solvableAuthSync [Nonempty VI] (h : val.SolvableAuthSync t δ)
    (htn : t < Fintype.card P) : ContainmentCondition t val := by
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := h
  exact containmentCondition_of_solvesConsensusAuthSync hU hA htn

/-- **Lemma 8** of [AllBAExpensive]: an unauthenticated-solvable problem satisfies CC. -/
theorem containmentCondition_of_solvableSync [Nonempty VI] (h : val.SolvableSync t δ)
    (htn : t < Fintype.card P) : ContainmentCondition t val :=
  containmentCondition_of_solvableAuthSync h.solvableAuthSync htn

/-! ### Interactive consistency -/

/-- Interactive consistency is solvable in synchrony (unauthenticated). -/
def ICSolvableSync (P VI : Type*) [Fintype P] [DecidableEq P] (t δ : ℕ) : Prop :=
  (icValidity P VI).SolvableSync t δ

/-- Interactive consistency is solvable in synchrony with signatures. -/
def ICSolvableAuthSync (P VI : Type*) [Fintype P] [DecidableEq P] (t δ : ℕ) : Prop :=
  (icValidity P VI).SolvableAuthSync t δ

/-! ### Lemma 9: sufficiency of CC (Algorithm 2) -/

/-- **Algorithm 2** of [AllBAExpensive]: run the interactive consistency algorithm `A`; once it
decides a vector `vec`, decide `Γ vec`. -/
abbrev reduction (A : Algorithm P M S VI (P → VI)) (Γ : Config P VI → VO) :
    Algorithm P M S VI VO :=
  A.mapDecide fun V => Γ fun q => some (V q)

/-- **Lemma 9** of [AllBAExpensive] (correctness of Algorithm 2): if `A` solves interactive
consistency in synchrony and `Γ` witnesses CC, then Algorithm 2 solves `val`-agreement in
synchrony (authenticated model `Au`; the unauthenticated model is `Au = Auth.none`). -/
theorem solvesConsensusAuthSync_reduction {A : Algorithm P M S VI (P → VI)}
    {Γ : Config P VI → VO} (hA : SolvesConsensusAuthSync Au t δ A (icValidity P VI))
    (hΓ : ∀ c, IsInputConfig t c → ∀ c', IsInputConfig t c' → Contains c c' → Γ c ∈ val c') :
    SolvesConsensusAuthSync Au t δ (reduction A Γ) val :=
  hA.mapDecide_containment hΓ

/-- **Lemma 9** of [AllBAExpensive] (sufficiency of CC), authenticated model: if `val` satisfies
CC and interactive consistency is authenticated-solvable in synchrony, then `val` is
authenticated-solvable in synchrony. -/
theorem solvableAuthSync_of_containmentCondition (hC : ContainmentCondition t val)
    (hIC : ICSolvableAuthSync P VI t δ) : val.SolvableAuthSync t δ :=
  hC.solvableAuthSync hIC

/-- **Lemma 9** of [AllBAExpensive] (sufficiency of CC), unauthenticated model: if `val`
satisfies CC and interactive consistency is unauthenticated-solvable in synchrony, then `val` is
unauthenticated-solvable in synchrony. -/
theorem solvableSync_of_containmentCondition (hC : ContainmentCondition t val)
    (hIC : ICSolvableSync P VI t δ) : val.SolvableSync t δ :=
  hC.solvableSync hIC

/-- **Theorem 4** of [AllBAExpensive] (authenticated part), relative to the solvability of
interactive consistency (proved in [52] by Dolev–Strong, not formalized here): a problem is
authenticated-solvable in synchrony iff it satisfies CC. -/
theorem solvableAuthSync_iff_containmentCondition [Nonempty VI] (htn : t < Fintype.card P)
    (hIC : ICSolvableAuthSync P VI t δ) :
    val.SolvableAuthSync t δ ↔ ContainmentCondition t val :=
  ⟨fun h => containmentCondition_of_solvableAuthSync h htn,
    fun h => solvableAuthSync_of_containmentCondition h hIC⟩

/-- Unauthenticated analogue of `solvableAuthSync_iff_containmentCondition`: whenever
interactive consistency is unauthenticated-solvable, a problem is unauthenticated-solvable iff it
satisfies CC. (No `n > 3t` assumption: see `lemma10_counterexample`.) -/
theorem solvableSync_iff_containmentCondition [Nonempty VI] (htn : t < Fintype.card P)
    (hIC : ICSolvableSync P VI t δ) :
    val.SolvableSync t δ ↔ ContainmentCondition t val :=
  ⟨fun h => containmentCondition_of_solvableSync h htn,
    fun h => solvableSync_of_containmentCondition h hIC⟩

/-! ### Theorem 5: strong consensus needs `n > 2t` -/

open Cslib.Byzantine.PartialSync.Binary in
/-- Strong validity does not satisfy CC if `n ≤ 2t` (proof of **Theorem 5** of
[AllBAExpensive]): split the processes into `A` with `n - t` processes proposing `0` and its
complement (`t ≥ n - t` processes) proposing `1`; the configuration contains both halves. -/
theorem strongValidity_not_containmentCondition (hn : Fintype.card P ≤ 2 * t)
    (htn : t < Fintype.card P) : ¬ ContainmentCondition t (strongValidity (P := P)) := by
  rintro ⟨Γ, hΓ⟩
  obtain ⟨X, -, hX⟩ := exists_subset_card_eq (s := (univ : Finset P))
    (n := Fintype.card P - t) (by simp)
  let c : Config P Bool := fun p => some (decide (p ∉ X))
  let c₀ : Config P Bool := fun p => if p ∈ X then some false else none
  let c₁ : Config P Bool := fun p => if p ∈ X then none else some true
  have hc : IsInputConfig t c := by unfold IsInputConfig; simp [c, Config.procs]
  have hp₀ : c₀.procs = X := by ext p; by_cases hp : p ∈ X <;> simp [c₀, hp]
  have hp₁ : c₁.procs = Xᶜ := by ext p; by_cases hp : p ∈ X <;> simp [c₁, hp]
  have hc₀ : IsInputConfig t c₀ := by unfold IsInputConfig; rw [hp₀, hX]
  have hc₁ : IsInputConfig t c₁ := by
    unfold IsInputConfig; rw [hp₁, card_compl, hX]; omega
  have h₀ := hΓ c hc c₀ hc₀ (fun p hp => by by_cases h : p ∈ X <;> simp_all [c, c₀]) false
    (fun p hp => by by_cases h : p ∈ X <;> simp_all [c₀])
  have h₁ := hΓ c hc c₁ hc₁ (fun p hp => by by_cases h : p ∈ X <;> simp_all [c, c₁]) true
    (fun p hp => by by_cases h : p ∈ X <;> simp_all [c₁])
  rw [h₀] at h₁
  exact Bool.noConfusion h₁

open Cslib.Byzantine.PartialSync.Binary in
/-- **Theorem 5** of [AllBAExpensive] (proven in [6]): strong consensus is authenticated-solvable
(in synchrony) only if `n > 2t` (for `t < n`). -/
theorem strongValidity_not_solvableAuthSync (hn : Fintype.card P ≤ 2 * t)
    (htn : t < Fintype.card P) : ¬ (strongValidity (P := P)).SolvableAuthSync t δ :=
  fun h => strongValidity_not_containmentCondition hn htn
    (containmentCondition_of_solvableAuthSync h htn)

/-! ### A counterexample to Lemma 10 (and to the unauthenticated part of Theorem 4)

Lemma 10 claims that every problem that is unauthenticated-solvable with `n ≤ 3t` is trivial
(citing the impossibility of weak consensus for `n ≤ 3t` [55]). This fails for `n = 2`, `t = 1`:
when one process is faulty, only one process is correct, so Agreement only matters in fault-free
runs. The algorithm `ic2` (exchange inputs, decide at time `δ + 1`) solves interactive
consistency whenever no valid run has both a faulty process and two distinct correct processes,
e.g. `t = 0` or `n ≤ 2`. -/

/-- Local state of `ic2`: own proposal, first value received from each process, local clock. -/
structure IC2State (P VI : Type*) where
  inp : VI
  rcv : P → Option VI
  clock : ℕ

omit [Fintype P] in
/-- The vector decided by `p` in state `s`: its own proposal for itself, the value received
from `q` for `q` (own proposal if nothing was received). -/
def IC2State.vec (p : P) (s : IC2State P VI) : P → VI :=
  fun q => if q = p then s.inp else (s.rcv q).getD s.inp

/-- The algorithm `ic2`: every process sends its proposal at every time; up to time `δ` it
records the first value received from each process; at time `δ + 1` it decides the vector
`IC2State.vec`. -/
def ic2 (P VI : Type*) [DecidableEq P] (δ : ℕ) :
    Algorithm P VI (IC2State P VI) VI (P → VI) where
  init _ v := ⟨v, fun _ => none, 0⟩
  step _ s inb := ⟨s.inp, fun q => if s.clock ≤ δ then (s.rcv q).or (inb q).head? else s.rcv q,
    s.clock + 1⟩
  send _ s _ := [s.inp]
  decide p s := if δ < s.clock then some (s.vec p) else none

namespace ic2

variable {VI : Type*} (R : Run P VI VI)

omit [Fintype P] in
theorem send_eq (p : P) (s : IC2State P VI) (q : P) : (ic2 P VI δ).send p s q = [s.inp] := rfl

omit [Fintype P] in
theorem decide_eq (p : P) (s : IC2State P VI) :
    (ic2 P VI δ).decide p s = if δ < s.clock then some (s.vec p) else none := rfl

omit [Fintype P] in
theorem st_succ' (τ : ℕ) (p : P) : R.st (ic2 P VI δ) (τ + 1) p =
    ⟨(R.st (ic2 P VI δ) τ p).inp, fun q => if (R.st (ic2 P VI δ) τ p).clock ≤ δ then
      ((R.st (ic2 P VI δ) τ p).rcv q).or (R.inbox (ic2 P VI δ) p τ q).head?
      else (R.st (ic2 P VI δ) τ p).rcv q, (R.st (ic2 P VI δ) τ p).clock + 1⟩ :=
  R.st_succ _ τ p

omit [Fintype P] in
theorem st_inp (τ : ℕ) (p : P) : (R.st (ic2 P VI δ) τ p).inp = R.inp p := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [st_succ']; exact ih

omit [Fintype P] in
theorem st_clock (τ : ℕ) (p : P) : (R.st (ic2 P VI δ) τ p).clock = τ := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [st_succ']; simp [ih]

omit [Fintype P] in
theorem st_rcv_frozen {τ : ℕ} (hτ : δ + 1 ≤ τ) (p : P) :
    (R.st (ic2 P VI δ) τ p).rcv = (R.st (ic2 P VI δ) (δ + 1) p).rcv := by
  induction τ, hτ using Nat.le_induction with
  | base => rfl
  | succ τ hτ ih =>
    rw [st_succ', ← ih]
    funext q
    simp [st_clock, show ¬ τ ≤ δ by omega]

omit [Fintype P] in
theorem vec_st {τ : ℕ} (hτ : δ + 1 ≤ τ) (p : P) :
    (R.st (ic2 P VI δ) τ p).vec p = (R.st (ic2 P VI δ) (δ + 1) p).vec p := by
  funext q
  simp only [IC2State.vec, st_inp, st_rcv_frozen R hτ]

omit [Fintype P] in
theorem decides_iff {p : P} {V : P → VI} :
    R.Decides (ic2 P VI δ) p V ↔ V = (R.st (ic2 P VI δ) (δ + 1) p).vec p := by
  constructor
  · rintro ⟨τ, h⟩
    rw [decide_eq, st_clock] at h
    split_ifs at h with hτ
    rw [← vec_st R (show δ + 1 ≤ τ by omega)]
    exact (Option.some.inj h).symm
  · rintro rfl
    exact ⟨δ + 1, by simp [decide_eq, st_clock]⟩

omit [Fintype P] in
/-- Values recorded from a correct process are its proposal. -/
theorem rcv_correct {q : P} (hq : q ∉ R.faulty) (p : P) (τ : ℕ) :
    (R.st (ic2 P VI δ) τ p).rcv q = none ∨ (R.st (ic2 P VI δ) τ p).rcv q = some (R.inp q) := by
  induction τ with
  | zero => left; rfl
  | succ τ ih =>
    rw [st_succ']
    dsimp only
    split_ifs
    · rcases ih with h | h
      · rw [h, Option.none_or]
        cases hh : (R.inbox (ic2 P VI δ) p τ q).head? with
        | none => left; rfl
        | some m =>
          right
          obtain ⟨σ, -, -, hm⟩ := Run.mem_inbox.mp (List.mem_of_mem_head? hh)
          rw [Run.out_of_correct _ _ hq] at hm
          simp only [send_eq, List.mem_singleton] at hm
          rw [hm, st_inp]
      · right; rw [h]; rfl
    · exact ih

omit [Fintype P] in
theorem rcv_mono {p q : P} {τ τ' : ℕ} (h : (R.st (ic2 P VI δ) τ p).rcv q ≠ none)
    (hτ : τ ≤ τ') : (R.st (ic2 P VI δ) τ' p).rcv q ≠ none := by
  induction τ', hτ using Nat.le_induction with
  | base => exact h
  | succ τ' _ ih =>
    rw [st_succ']
    dsimp only
    split_ifs
    · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp ih
      rw [hx]; simp
    · exact ih

omit [Fintype P] in
/-- In a synchronous run, a correct process has recorded the proposal of every correct process
by time `δ + 1`. -/
theorem rcv_sync (hR : R.Valid t δ) (h0 : R.gst = 0) {p q : P} (hp : p ∉ R.faulty)
    (hq : q ∉ R.faulty) : (R.st (ic2 P VI δ) (δ + 1) p).rcv q = some (R.inp q) := by
  have hdl : R.dl q 0 p ≤ δ := by have := hR.dl_le q 0 p hq hp; simpa [h0] using this
  have hmem : R.inp q ∈ R.inbox (ic2 P VI δ) p (R.dl q 0 p) q := by
    refine Run.mem_inbox.mpr ⟨0, Nat.zero_le _, rfl, ?_⟩
    rw [Run.out_of_correct _ _ hq, send_eq, st_inp]
    simp
  have h1 : (R.st (ic2 P VI δ) (R.dl q 0 p + 1) p).rcv q ≠ none := by
    rw [st_succ']
    dsimp only
    simp only [st_clock, hdl, ↓reduceIte]
    cases hh : (R.st (ic2 P VI δ) (R.dl q 0 p) p).rcv q with
    | some x => simp
    | none =>
      rw [Option.none_or]
      cases hl : R.inbox (ic2 P VI δ) p (R.dl q 0 p) q with
      | nil => rw [hl] at hmem; simp at hmem
      | cons a l => simp
  have h2 := rcv_mono R h1 (show R.dl q 0 p + 1 ≤ δ + 1 by omega)
  exact (rcv_correct R hq p _).resolve_left h2

omit [Fintype P] in
theorem vec_eq_inp (hR : R.Valid t δ) (h0 : R.gst = 0) {p q : P} (hp : p ∉ R.faulty)
    (hq : q ∉ R.faulty) : (R.st (ic2 P VI δ) (δ + 1) p).vec p q = R.inp q := by
  unfold IC2State.vec
  split_ifs with h
  · subst h; exact st_inp R _ _
  · rw [rcv_sync R hR h0 hp hq]; rfl

end ic2

/-- `ic2` solves interactive consistency in synchrony (unauthenticated) whenever `t = 0` or
`n ≤ 2`. -/
theorem ic2_solves {VI : Type*} (hP : t = 0 ∨ Fintype.card P ≤ 2) :
    SolvesConsensusSync t δ (ic2 P VI δ) (icValidity P VI) where
  termination R _ _ _ p _ := ⟨_, (ic2.decides_iff R).mpr rfl⟩
  agreement R hR _ h0 p hp q hq V W hV hW := by
    rw [ic2.decides_iff] at hV hW
    subst hV hW
    by_cases hpq : p = q
    · subst hpq; rfl
    have hF : R.faulty = ∅ := by
      by_contra hne
      obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr hne
      have ht : 1 ≤ t := by
        have := hR.card_faulty; have := card_pos.mpr ⟨b, hb⟩; omega
      have h3 : ({p, q, b} : Finset P).card = 3 :=
        card_eq_three.mpr ⟨p, q, b, hpq, fun h => hp (h ▸ hb), fun h => hq (h ▸ hb), rfl⟩
      have := card_le_univ ({p, q, b} : Finset P)
      omega
    funext r
    have hr : r ∉ R.faulty := by simp [hF]
    rw [ic2.vec_eq_inp R hR h0 hp hr, ic2.vec_eq_inp R hR h0 hq hr]
  validity R hR _ h0 p hp V hV := by
    rw [ic2.decides_iff] at hV
    subst hV
    intro q hq
    have hqF : q ∉ R.faulty := by
      intro h; apply hq; simp [Run.inputConf, h]
    simp only [Run.inputConf, hqF, ite_false, ic2.vec_eq_inp R hR h0 hp hqF]

/-- Interactive consistency is unauthenticated-solvable in synchrony if `t = 0` or `n ≤ 2`
(for any `t`). -/
theorem icSolvableSync_of_card_le_two {P' : Type} [Fintype P'] [DecidableEq P'] (VI : Type)
    (hP : t = 0 ∨ Fintype.card P' ≤ 2) : ICSolvableSync P' VI t δ :=
  ⟨VI, IC2State P' VI, ic2 P' VI δ, ic2_solves hP⟩

omit [DecidableEq P] in
/-- Weak validity satisfies CC (for any `t`, as soon as there is a process): `Γ c` is the common
proposal if `c` is a full configuration with all proposals equal, an arbitrary value otherwise. -/
theorem weakValidity_containmentCondition {V : Type*} [Nonempty P] [Nonempty V] :
    ContainmentCondition t (weakValidity P V) := by
  classical
  refine ⟨fun c => if h : ∃ v, ∀ p, c p = some v then h.choose else Classical.arbitrary V,
    fun c _ c' _ hcont v hv => ?_⟩
  have hc : ∀ p, c p = some v := fun p => (hcont p (by simp [hv p])).trans (hv p)
  have hex : ∃ v, ∀ p, c p = some v := ⟨v, hc⟩
  simp only [hex, ↓reduceDIte]
  obtain ⟨p₀⟩ := ‹Nonempty P›
  exact Option.some.inj ((hex.choose_spec p₀).symm.trans (hc p₀))

/-- Weak validity is not trivial (`n = 2`, `t = 1`). -/
theorem weakValidity_not_trivial : ¬ (weakValidity (Fin 2) Bool).Trivial 1 := by
  rintro ⟨w, hw⟩
  have := hw (fun _ => some !w) (by unfold IsInputConfig; simp [Config.procs]) (!w)
    (fun _ => rfl)
  cases w <;> simp at this

/-- Interactive consistency is not trivial (`n = 2`, `t = 1`). -/
theorem icValidity_not_trivial : ¬ (icValidity (Fin 2) Bool).Trivial 1 := by
  rintro ⟨V, hV⟩
  have := hV (fun _ => some !V 0) (by unfold IsInputConfig; simp [Config.procs]) 0 (by simp)
  cases h : V 0 <;> simp [h] at this

/-- **Counterexample to Lemma 10** of [AllBAExpensive] (interactive consistency): for `n = 2`,
`t = 1` (so `n ≤ 3t`), interactive consistency is a non-trivial problem that is
unauthenticated-solvable in synchrony. -/
theorem lemma10_counterexample_ic (δ : ℕ) :
    ICSolvableSync (Fin 2) Bool 1 δ ∧ ¬ (icValidity (Fin 2) Bool).Trivial 1 :=
  ⟨icSolvableSync_of_card_le_two Bool (Or.inr (by simp)), icValidity_not_trivial⟩

/-- **Counterexample to Lemma 10** of [AllBAExpensive] (weak consensus): for `n = 2`, `t = 1`
(so `n ≤ 3t`), binary weak consensus is a non-trivial problem that is unauthenticated-solvable in
synchrony (via Lemma 9 on top of `ic2`). In particular the unauthenticated part of Theorem 4
("unauthenticated-solvable iff CC and `n > 3t`") fails for `n = 2`, `t = 1`. -/
theorem lemma10_counterexample (δ : ℕ) :
    (weakValidity (Fin 2) Bool).SolvableSync 1 δ ∧ ¬ (weakValidity (Fin 2) Bool).Trivial 1 :=
  ⟨solvableSync_of_containmentCondition weakValidity_containmentCondition
    (icSolvableSync_of_card_le_two Bool (Or.inr (by simp))), weakValidity_not_trivial⟩

/-- **Lemma 10** of [AllBAExpensive] is false as stated: with `n = 2 ≤ 3 = 3t`, not every
unauthenticated-solvable problem is trivial. -/
theorem not_lemma10 (δ : ℕ) :
    ¬ ∀ val : ValidityProperty (Fin 2) Bool Bool, val.SolvableSync 1 δ → val.Trivial 1 :=
  fun h => (lemma10_counterexample δ).2 (h _ (lemma10_counterexample δ).1)

end AllBAExpensive

/-! ### Lemma 8 with a Turing-computable `Γ`

The paper requires `Γ` in Definition 3 to be Turing-computable. For processes `Fin n` and a
computable algorithm (`Algorithm.IsComputable`), `Γ c` can be computed by simulating the
canonical synchronous execution of `c` and searching for the first decision of a process of
`π(c)`, which exists by Termination
(`Algorithm.IsComputable.exists_computable_canonDecision`, shared library
`Podc.PartialSync.Computable`). -/

namespace AllBAExpensive

open Finset Cslib.Byzantine.PartialSync

variable {n : ℕ} {M S VI VO : Type*} [Primcodable M] [Primcodable S] [Primcodable VI]
  [Primcodable VO] {t δ : ℕ} {A : Algorithm (Fin n) M S VI VO}
  {val : ValidityProperty (Fin n) VI VO}

/-- **Definition 3** of [AllBAExpensive] as in the paper: CC with a Turing-computable `Γ`
(Mathlib's `Computable`, processes `Fin n`). -/
def ContainmentConditionComputable (t : ℕ) (val : ValidityProperty (Fin n) VI VO) : Prop :=
  ∃ Γ : Config (Fin n) VI → VO, Computable Γ ∧ ∀ c, IsInputConfig t c → ∀ c',
    IsInputConfig t c' → Contains c c' → Γ c ∈ val c'

omit [Primcodable M] [Primcodable S] in
theorem ContainmentConditionComputable.containmentCondition
    (h : ContainmentConditionComputable t val) : ContainmentCondition t val := by
  obtain ⟨Γ, -, hΓ⟩ := h
  exact ⟨Γ, hΓ⟩

/-- **Lemma 8** of [AllBAExpensive] with a Turing-computable `Γ`, authenticated model: if a
computable unforging algorithm solves `val`-agreement in synchrony (`t < n`), then `val`
satisfies CC with a computable `Γ`. -/
theorem containmentConditionComputable_of_solvesConsensusAuthSync {K : Type*}
    {Au : Auth (Fin n) M K} [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A val) (hc : A.IsComputable) (htn : t < n) :
    ContainmentConditionComputable t val := by
  set d := Classical.arbitrary VI
  obtain ⟨Γ, hΓc, hΓ⟩ := hc.exists_computable_canonDecision (M := M) d htn
    fun c hc' p hp => hA.termination _ (canonRun.valid c d hc' δ) (canonRun_authValid c d) rfl p
      (by simpa [canonRun, Option.isSome_iff_ne_none] using hp)
  refine ⟨Γ, hΓc, fun c hc' c' hc'' hcont => ?_⟩
  obtain ⟨p, hp, hdec⟩ := hΓ c hc'
  have hpF : p ∉ (canonRun (M := M) c d).faulty := by
    simp [canonRun, Option.isSome_iff_ne_none, hp]
  exact containment_auth hU hA (by simpa using htn) (canonRun.valid c d hc' δ)
    (canonRun_authValid c d) rfl hpF hdec hc'' (by rwa [canonRun.inputConf])

/-- **Lemma 8** of [AllBAExpensive] with a Turing-computable `Γ`, unauthenticated model. -/
theorem containmentConditionComputable_of_solvesConsensusSync [Nonempty VI]
    (hA : SolvesConsensusSync t δ A val) (hc : A.IsComputable) (htn : t < n) :
    ContainmentConditionComputable t val :=
  containmentConditionComputable_of_solvesConsensusAuthSync A.unforging_none hA hc htn

end AllBAExpensive
