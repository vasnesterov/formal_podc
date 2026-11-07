import Papers.PODC2012.CloserLookFT.ColorlessLiveness

/-!
# Section 6 of Taubenfeld (PODC 2012), shared memory: Lemma 6.1, Theorems 6.2 and 6.3

Model: asynchronous shared memory (CSLib), atomic read/write registers (`UsesRegisters`),
deterministic processes, crash failures, one-shot task executions with **required
participation** (`ReqPart`: every process invokes the task). A *register algorithm* for a task
(`HasRegAlgorithm`) uses only registers, accepts every input in every process, solves the task
(`Impl.Solves`) and has the given progress property (`WeaklyResilient`/`Resilient` of
`Podc/Computability/Distributed/SharedMemory/Resilience.lean`).

* `lemma_6_1` — **Lemma 6.1**: for colorless `T` and `t ≤ n - 2`, `T` has a weakly-`t`-resilient
  register algorithm iff it has a `t`-resilient one (`withOutput`, `solves_withOutput`,
  `resilient_withOutput`; the converse is `Resilient.weaklyResilient`).
* `theorem_6_2` — **Theorem 6.2** (`n ≥ 3`: no weakly-1-resilient consensus), from the external
  impossibility `LAAImpossibility` (Loui–Abu-Amara), taken as a hypothesis.
* `theorem_6_3` — **Theorem 6.3** (`k ≤ n - 2`: no weakly-`k`-resilient `k`-set consensus,
  `setConsensus`), from the external impossibility `SetConsensusImpossibility`
  (Borowsky–Gafni, Herlihy–Shavit, Saks–Zaharoglou), taken as a hypothesis.
* Non-vacuity: `selfDecide` (return your own input) is resilient and solves `k`-set consensus
  for `k ≥ n` and consensus on `Unit`; hence `not_setConsensusImpossibility`,
  `not_LAAImpossibility_unit` (the external hypotheses are not tautologies) and
  `hasRegAlgorithm_setConsensus_of_le` (the conclusion of Theorem 6.3 fails for `k ≥ n`).

The message-passing parts of Lemma 6.1 and Theorems 6.2/6.3 are not formalized.
-/

set_option linter.unusedSectionVars false

namespace Podc.CloserLookFT

open Cslib.SharedMemory Cslib.SharedMemory.Impl

variable {P : Type} [DecidableEq P]

/-- Admissible executions of this section: one-shot, with **required participation** (every
process invokes the task). -/
abbrev ReqPart {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι]
    (I : Impl A B P L) (e : I.InfExec) : Prop :=
  e.OneShotExec ∧ e.AllParticipate

/-- All base objects are atomic read/write registers. -/
def UsesRegisters {ι : Type} (B : ι → ObjSpec) : Prop :=
  ∀ i, ∃ (V : Type) (v₀ : V), B i = register V v₀

/-- `A'` uses registers if `A` does. -/
lemma usesRegisters_outB {ι Out : Type} {B : ι → ObjSpec} (h : UsesRegisters B) :
    UsesRegisters (OutB B Out) := by
  rintro (i | u)
  · exact h i
  · exact ⟨Option Out, none, rfl⟩

/-- `T` has an algorithm from atomic registers that accepts every input, solves `T` and has
the progress property `Prog`. -/
def HasRegAlgorithm (T : Cslib.SharedMemory.Task P) [Inhabited T.Out]
    (Prog : ∀ {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type},
      Impl (taskObj T.In T.Out) B P L → Prop) : Prop :=
  ∃ (ι : Type) (_ : DecidableEq ι) (B : ι → ObjSpec) (L : Type)
    (A : Impl (taskObj T.In T.Out) B P L),
    UsesRegisters B ∧ (∀ p o, A.allowed p o) ∧ A.Solves T ∧ Prog A

/-- **Lemma 6.1** of [Taubenfeld 2012] (shared-memory part). Required participation,
`t ≤ n - 2`, atomic registers: a colorless task has a weakly-`t`-resilient algorithm iff it has a
`t`-resilient algorithm. (The paper also assumes `n ≥ 3`; it is not needed.) -/
theorem lemma_6_1 [Fintype P] (T : Cslib.SharedMemory.Task P) [Inhabited T.Out]
    (hT : Colorless T) {t : ℕ} (ht : t ≤ Fintype.card P - 2) :
    HasRegAlgorithm T (fun A => A.WeaklyResilient (ReqPart A) t) ↔
      HasRegAlgorithm T (fun A => A.Resilient (ReqPart A) t) := by
  constructor
  · rintro ⟨ι, _, B, L, A, hreg, hall, hS, hW⟩
    exact ⟨ι ⊕ Unit, inferInstance, OutB B T.Out, _, withOutput A, usesRegisters_outB hreg,
      hall, solves_withOutput hT.adoptClosed hS, resilient_withOutput ht hW⟩
  · rintro ⟨ι, _, B, L, A, hreg, hall, hS, hR⟩
    exact ⟨ι, inferInstance, B, L, A, hreg, hall, hS, hR.weaklyResilient⟩

/-- The `k`-set consensus task: every output is the input of a participant, and at most `k`
different values are output. -/
def setConsensus (P V : Type) (k : ℕ) : Cslib.SharedMemory.Task P where
  In := V
  Out := V
  Δ ins outs := vals outs ⊆ vals ins ∧ (vals outs).encard ≤ k

instance {V : Type} [Inhabited V] {k : ℕ} : Inhabited (setConsensus P V k).Out :=
  inferInstanceAs (Inhabited V)

/-- Consensus is colorless. -/
lemma colorless_consensus (V : Type) : Colorless (consensus P V) := by
  refine ⟨fun X Y => Y.Subsingleton ∧ Y ⊆ X, fun X Y Y' h ⟨h1, h2⟩ => ⟨h1.anti h, h.trans h2⟩,
    fun ins outs => ?_⟩
  simp only [consensus, vals, Set.Subsingleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x ⟨p, hp⟩ y ⟨q, hq⟩ => h1 p q x y hp hq, fun y ⟨p, hp⟩ => h2 p y hp⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p q x y hp hq => h1 ⟨p, hp⟩ ⟨q, hq⟩, fun p y hp => h2 ⟨p, hp⟩⟩

/-- `k`-set consensus is colorless. -/
lemma colorless_setConsensus (V : Type) (k : ℕ) : Colorless (setConsensus P V k) :=
  ⟨fun X Y => Y ⊆ X ∧ Y.encard ≤ k,
    fun _ _ _ h ⟨h1, h2⟩ => ⟨h.trans h1, (Set.encard_le_encard h).trans h2⟩,
    fun _ _ => Iff.rfl⟩

/-- The impossibility of 1-resilient consensus from registers with required participation
(Loui and Abu-Amara 1987; Fischer, Lynch and Paterson 1985 for message passing), for `n`
processes `P` and values `V` (it needs at least two values). Not proved here: an explicit
hypothesis of Theorem 6.2. -/
def LAAImpossibility (P V : Type) [DecidableEq P] [Inhabited V] : Prop :=
  ¬ HasRegAlgorithm (P := P) (consensus P V) (fun A => A.Resilient (ReqPart A) 1)

/-- The impossibility of `k`-resilient `k`-set consensus from registers (Borowsky–Gafni,
Herlihy–Shavit, Saks–Zaharoglou 1993), for `n ≥ k + 1` processes and at least `k + 1` values.
Not proved here: an explicit hypothesis of Theorem 6.3. -/
def SetConsensusImpossibility (P V : Type) [DecidableEq P] [Inhabited V] (k : ℕ) : Prop :=
  ¬ HasRegAlgorithm (P := P) (setConsensus P V k) (fun A => A.Resilient (ReqPart A) k)

/-- **Theorem 6.2** of [Taubenfeld 2012] (shared-memory part). For `n ≥ 3`, there is no
weakly-1-resilient consensus algorithm from atomic registers (with required participation),
assuming the Loui–Abu-Amara impossibility of 1-resilient consensus. -/
theorem theorem_6_2 [Fintype P] (V : Type) [Inhabited V] (hn : 3 ≤ Fintype.card P)
    (hLAA : LAAImpossibility P V) :
    ¬ HasRegAlgorithm (consensus P V) (fun A => A.WeaklyResilient (ReqPart A) 1) := fun h =>
  hLAA ((lemma_6_1 (consensus P V) (colorless_consensus V) (by omega)).1 h)

/-- **Theorem 6.3** of [Taubenfeld 2012] (shared-memory part). For `n ≥ 3` and
`1 ≤ k ≤ n - 2`, there is no weakly-`k`-resilient `k`-set-consensus algorithm from atomic
registers (with required participation), assuming the impossibility of `k`-resilient `k`-set
consensus. (`n ≥ 3` and `1 ≤ k` are not needed.) -/
theorem theorem_6_3 [Fintype P] (V : Type) [Inhabited V] (k : ℕ)
    (hk : k ≤ Fintype.card P - 2) (hBG : SetConsensusImpossibility P V k) :
    ¬ HasRegAlgorithm (setConsensus P V k) (fun A => A.WeaklyResilient (ReqPart A) k) :=
  fun h => hBG ((lemma_6_1 (setConsensus P V k) (colorless_setConsensus V k) hk).1 h)

/-! ## Non-vacuity

The trivial algorithm "decide your own input" (no shared object at all) is `t`-resilient for
every `t` and solves `k`-set consensus for `k ≥ n`, and consensus for a single value. Hence the
external hypotheses `SetConsensusImpossibility P V k` and `LAAImpossibility P V` are not
tautologies (they fail for `k ≥ n`, resp. `V = Unit`), the classes of algorithms in Lemma 6.1
are inhabited, and the conclusions of Theorems 6.2/6.3 are false outside their parameter
range. -/

section NonVacuity

variable (V : Type) [Inhabited V]

/-- The trivial algorithm: return your own input immediately. -/
def selfDecide : Impl (taskObj V V) (fun _ : Empty => register Unit ()) P (Option V) where
  memInit i := i.elim
  locInit _ := none
  invoke _ _ o := some o
  act _ l := .ret (l.getD default) l

variable {V}

/-- `selfDecide` is `t`-resilient for every `t` (a pending process can only return). -/
lemma selfDecide_resilient (Adm : (selfDecide (P := P) V).InfExec → Prop) (t : ℕ) :
    (selfDecide V).Resilient Adm t := by
  intro e _ _
  suffices h : ∀ p, ¬ e.Starved p by
    have : {p | e.Starved p} = ∅ := Set.eq_empty_of_forall_notMem h
    simp [this]
  rintro p ⟨⟨t0, hb⟩, hnc⟩
  obtain ⟨j, hj, hproc⟩ := InfExec.exists_step_of_not_crashed hnc (hb t0 le_rfl)
  have hs := e.step_eq j
  cases hl : e.lbl j with
  | inv q o =>
    rw [hl] at hs hproc; simp only [Label.proc] at hproc; subst hproc
    exact hb j hj (Impl.step_inv hs).1
  | tau q =>
    rw [hl] at hs
    obtain ⟨-, -, i, -⟩ := Impl.step_tau hs
    exact i.elim
  | ret q r =>
    rw [hl] at hs hproc; simp only [Label.proc] at hproc; subst hproc
    exact hb (j + 1) (by omega) (by rw [(Impl.step_ret hs).2.1]; simp)

/-- In a one-shot execution of `selfDecide`, a process outputs its own input. -/
lemma selfDecide_output {α : List (Label P (taskObj V V))} (hα : (selfDecide V).Valid α)
    (hos : OneShot α) (p : P) (y : V) (hy : outputs α p = some y) : inputs α p = some y := by
  obtain ⟨C, hC⟩ := hα
  have key : ∀ α C, (selfDecide (P := P) V).run α = some C → OneShot α → ∀ p,
      C.loc p = inputs α p ∧ ∀ y, outputs α p = some y → inputs α p = some y := by
    intro α C h
    refine (selfDecide V).run_induction
      (Q := fun α C => OneShot α → ∀ p, C.loc p = inputs α p ∧
        ∀ y, outputs α p = some y → inputs α p = some y) ?_ ?_ h
    · intro _ p
      refine ⟨rfl, fun y hy => ?_⟩
      simp [outputs, respsOf] at hy
    · intro α C ℓ C' hrun ih hs hos q
      obtain ⟨h1, h2⟩ := ih hos.of_append q
      cases ℓ with
      | inv p o =>
        obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv hs
        have hin : ∀ y, outputs α q = some y → inputs (α ++ [.inv p o]) q = some y :=
          fun y hy => by
            rw [inputs_append_of_ne_none _ (by rw [h2 y hy]; exact Option.some_ne_none _), h2 y hy]
        refine ⟨?_, fun y hy => hin y (by rwa [outputs_append_inv] at hy)⟩
        rw [hloc]
        by_cases hq : q = p
        · subst hq
          have h3 := hos q
          simp only [opsOf_append, List.length_append, opsOf_cons, Label.invOf_inv,
            ↓reduceIte, Option.toList_some, opsOf_nil, List.append_nil,
            List.length_singleton] at h3
          have h4 : opsOf α q = [] := List.eq_nil_of_length_eq_zero (by omega)
          simp [inputs, opsOf_append, h4, selfDecide]; rfl
        · rw [Function.update_of_ne hq, h1]
          simp [inputs, opsOf_append, Label.invOf_inv, Ne.symm hq]; rfl
      | tau p =>
        obtain ⟨-, -, i, -⟩ := Impl.step_tau hs
        exact i.elim
      | ret p r =>
        obtain ⟨hp, -, -, l, hact, hloc⟩ := Impl.step_ret hs
        have hl : l = C.loc p := by cases hact; rfl
        have hr : r = (C.loc p).getD default := by cases hact; rfl
        subst hl
        have hin : inputs (α ++ [.ret p r]) q = inputs α q := by
          simp [inputs, opsOf_append]
        rw [hin, hloc, Function.update_eq_self]
        refine ⟨h1, fun y hy => ?_⟩
        rw [outputs_concat] at hy
        cases ho : outputs α q with
        | some w => rw [ho] at hy; cases hy; exact h2 _ ho
        | none =>
          rw [ho] at hy
          by_cases hq : q = p
          · subst hq
            obtain ⟨x, hx⟩ : ∃ x, inputs α q = some x := by
              have := (selfDecide V).opsOf_ne_nil_of_pend hrun hp
              simp only [inputs]
              exact Option.ne_none_iff_exists'.1 (by simpa using this)
            simp only [Label.retOf_ret, ↓reduceIte, Option.none_or] at hy
            cases hy
            rw [hr, h1, hx]; rfl
          · simp at hy; exact absurd hy.1.symm hq
  exact (key α C hC hos p).2 y hy

/-- `selfDecide` solves `k`-set consensus when `k ≥ n`. -/
lemma selfDecide_solves_setConsensus [Fintype P] {k : ℕ} (hk : Fintype.card P ≤ k) :
    (selfDecide (P := P) V).Solves (setConsensus P V k) := by
  intro α hα hos
  refine ⟨fun y ⟨p, hp⟩ => ⟨p, selfDecide_output hα hos p y hp⟩, ?_⟩
  have hsub : vals (outputs α) ⊆
      (fun p => (outputs α p).getD (default : V)) '' {p | (outputs α p).isSome} := by
    rintro x ⟨p, hp⟩
    exact ⟨p, by simp [hp], by dsimp only; rw [hp]; rfl⟩
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
  refine (Set.encard_le_encard (Set.subset_univ _)).trans ?_
  simp only [Set.encard_univ, ENat.card_eq_coe_fintype_card, Nat.cast_le]
  exact hk

/-- `selfDecide` solves consensus on a single value. -/
lemma selfDecide_solves_consensus_unit :
    (selfDecide (P := P) Unit).Solves (consensus P Unit) := by
  intro α hα hos
  exact ⟨fun _ _ _ _ _ _ => rfl, fun p y hp => ⟨p, selfDecide_output hα hos p y hp⟩⟩

/-- The `k`-set-consensus impossibility fails for `k ≥ n`: it is a genuine hypothesis. -/
lemma not_setConsensusImpossibility [Fintype P] {k : ℕ} (hk : Fintype.card P ≤ k) :
    ¬ SetConsensusImpossibility P V k := fun h =>
  h ⟨Empty, inferInstance, _, _, selfDecide V, fun i => i.elim, fun _ _ => trivial,
    selfDecide_solves_setConsensus hk, selfDecide_resilient _ _⟩

/-- The Loui–Abu-Amara impossibility fails for a single value: it is a genuine hypothesis. -/
lemma not_LAAImpossibility_unit : ¬ LAAImpossibility P Unit := fun h =>
  h ⟨Empty, inferInstance, _, _, selfDecide Unit, fun i => i.elim, fun _ _ => trivial,
    selfDecide_solves_consensus_unit, selfDecide_resilient _ _⟩

/-- The conclusion of Theorem 6.3 is false for `k ≥ n` (so the theorem is not trivially true):
there is a weakly-`k`-resilient `k`-set-consensus algorithm. -/
lemma hasRegAlgorithm_setConsensus_of_le [Fintype P] {k : ℕ} (hk : Fintype.card P ≤ k) :
    HasRegAlgorithm (setConsensus P V k) (fun A => A.WeaklyResilient (ReqPart A) k) :=
  ⟨Empty, inferInstance, _, _, selfDecide V, fun i => i.elim, fun _ _ => trivial,
    selfDecide_solves_setConsensus hk, (selfDecide_resilient _ _).weaklyResilient⟩

end NonVacuity

end Podc.CloserLookFT
