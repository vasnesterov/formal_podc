import Papers.PODC2025.TwoStepConsensusLB.ImplTwoStep
import Papers.PODC2025.TwoStepConsensusLB.ImplValidity

/-!
# Upper bounds (Theorems 1 and 2, "if"): assembly

The protocol `fig1 c` (Figure 1, with rotating ballots instead of `Ω`) satisfies

* Validity (`task_validity`, `object_validity`): no assumption;
* Termination / wait-freedom (`task_termination`, `object_waitFree`): `f < n`, every process owns
  ballots starting arbitrarily late (e.g. `rrOwner`), and (object) our fix of lines 37–38;
* the `e`-two-step properties (`task_twoStep`, `object_twoStep`): `n ≥ e + 2`.

Agreement is proved separately (via a refinement to the abstract transition system of Figure 1);
here it is a hypothesis (`TaskAgreement`, `ObjectAgreement`), and `task_solves` /
`object_solves` assemble the specifications from it.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

open _root_.Cslib.CrashPartialSync

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- Agreement of the task version of `fig1 c` (the `agreement` field of `SolvesTask`). -/
def TaskAgreement (c : Cfg P) : Prop :=
  ∀ (R : Run P V (Msg P V)) (I : P → V), R.Valid c.f → R.inv = taskInv I →
    ∀ p q τ τ' v w, R.DecidesAt (fig1 c) p τ v → R.DecidesAt (fig1 c) q τ' w → v = w

/-- Agreement of the object version of `fig1 c` (the `agreement` field of `SolvesObject`). -/
def ObjectAgreement (c : Cfg P) : Prop :=
  ∀ (R : Run P V (Msg P V)), R.Valid c.f → R.WellFormed →
    ∀ p q τ τ' v w, R.RespondsAt (fig1 c) p τ v → R.RespondsAt (fig1 c) q τ' w → v = w

/-- The task version of Figure 1 solves consensus, given Agreement. -/
theorem task_solves (c : Cfg P) (hagr : TaskAgreement (V := V) c) (hfn : c.f < Fintype.card P)
    (hown : ∀ p k, ∃ b, k ≤ b ∧ c.owner b = p) : SolvesTask (fig1 (V := V) c) c.f where
  validity R I hR hinv p τ v h := task_validity c c.f R I hR hinv p τ v h
  agreement := hagr
  termination R I hR hinv p hp := task_termination c hfn hown R I hR hinv p hp

/-- The object version of Figure 1 (with our fix) solves consensus, given Agreement. -/
theorem object_solves (c : Cfg P) (hobj : c.obj = true) (hagr : ObjectAgreement (V := V) c)
    (hfn : c.f < Fintype.card P) (hown : ∀ p k, ∃ b, k ≤ b ∧ c.owner b = p) :
    SolvesObject (fig1 (V := V) c) c.f where
  validity R hR hwf p τ v h := object_validity c c.f R hR hwf p τ v h
  agreement := hagr
  waitFree R hR hwf p τ₀ v hp hinv := object_waitFree c hobj hfn hown R hR hwf p τ₀ v hp hinv

/-- The round-robin owner assignment satisfies the leader hypothesis. -/
theorem rrOwner_hown [Nonempty P] : ∀ p k, ∃ b, k ≤ b ∧ (rrOwner (P := P)) b = p :=
  fun p k => rrOwner_surj p k

/-- **Theorem 1, "if" direction** (modulo Agreement): for `n ≥ 2f + 1` and `n ≥ e + 2`, the task
version of Figure 1 with round-robin ballots is an `f`-resilient `e`-two-step consensus task.
(The bound `n ≥ 2e + f` is needed only for Agreement, Lemma 1.) -/
theorem theorem_1_upper_of_agreement [Nonempty P] (e f : ℕ) (hn : 2 * f + 1 ≤ Fintype.card P)
    (hn' : e + 2 ≤ Fintype.card P)
    (hagr : TaskAgreement (V := V) (⟨e, f, false, rrOwner⟩ : Cfg P)) :
    SolvesTask (fig1 (V := V) (⟨e, f, false, rrOwner⟩ : Cfg P)) f ∧
      TwoStepTask (fig1 (V := V) (⟨e, f, false, rrOwner⟩ : Cfg P)) e :=
  ⟨task_solves _ hagr (by simp; omega) rrOwner_hown, task_twoStep _ rfl hn'⟩

/-- **Theorem 2, "if" direction** (modulo Agreement): for `n ≥ 2f + 1` and `n ≥ e + 2`, the object
version of Figure 1 (with our fix of lines 37–38) with round-robin ballots is an `f`-resilient
`e`-two-step consensus object. (The bound `n ≥ 2e + f - 1` is needed only for Agreement,
Lemma 5.) -/
theorem theorem_2_upper_of_agreement [Nonempty P] (e f : ℕ) (hn : 2 * f + 1 ≤ Fintype.card P)
    (hn' : e + 2 ≤ Fintype.card P)
    (hagr : ObjectAgreement (V := V) (⟨e, f, true, rrOwner⟩ : Cfg P)) :
    SolvesObject (fig1 (V := V) (⟨e, f, true, rrOwner⟩ : Cfg P)) f ∧
      TwoStepObject (fig1 (V := V) (⟨e, f, true, rrOwner⟩ : Cfg P)) e :=
  ⟨object_solves _ rfl hagr (by simp; omega) rrOwner_hown, object_twoStep _ hn'⟩

end TwoStepConsensus.Impl
