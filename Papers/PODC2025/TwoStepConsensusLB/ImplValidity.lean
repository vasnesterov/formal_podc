import Papers.PODC2025.TwoStepConsensusLB.ImplInv

/-!
# Validity of the protocol of Figure 1 (task and object)

"Validity trivially follows from the structure of the protocol" (§C.2): every value occurring in
the system was proposed. No assumption on `n`, `f`, `e` is needed.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

open _root_.Cslib.CrashPartialSync

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- **Validity** of the consensus task (Theorem 1, "if"): every decision is the input of some
process. -/
theorem task_validity (c : Cfg P) (f : ℕ) (R : Run P V (Msg P V)) (I : P → V) (hR : R.Valid f)
    (hinv : R.inv = taskInv I) (p : P) (τ : ℕ) (v : V) (h : R.DecidesAt (fig1 c) p τ v) :
    ∃ q, I q = v := by
  obtain ⟨q, τ₁, -, -, h⟩ := (values_st (c := c) hR.ord_perm τ p).2.2.1 v h
  rw [hinv] at h
  unfold taskInv at h
  split_ifs at h
  exact ⟨q, Option.some.inj h⟩

/-- **Validity** of the consensus object (Theorem 2, "if"): every response was proposed (by an
invocation) before it is returned. -/
theorem object_validity (c : Cfg P) (f : ℕ) (R : Run P V (Msg P V)) (hR : R.Valid f)
    (_hwf : R.WellFormed) (p : P) (τ : ℕ) (v : V) (h : R.RespondsAt (fig1 c) p τ v) :
    ∃ q, ∃ τ₁ < τ, R.inv q τ₁ = some v := by
  obtain ⟨q, τ₁, h1, -, h⟩ := (values_st (c := c) hR.ord_perm τ p).2.2.1 v h.2
  exact ⟨q, τ₁, h1, h⟩

end TwoStepConsensus.Impl
