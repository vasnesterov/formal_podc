import Papers.PODC2014.WritableObjects.Lemma45
import Papers.PODC2014.WritableObjects.KWordRegister
import Papers.PODC2014.WritableObjects.TauFree

/-!
# Writable objects built from `k`-word registers (towards Corollary 4.4)

Corollary 4.4 combines the transformation (Theorem 4.1) with the sequentially writable `k`-word
register of Figure 4.2 (`kWordImpl`, `kWord_seqWritable`). Here: any implementation following the
template of Figure 4.4 and satisfying condition (C), whose base objects `A[i]` are instances of
Figure 4.2 (the history of each `A[i]` is the history of an execution of `kWordImpl`, with
internal steps removed), is a linearizable `k`-word register (`template_kWord_linearizable`).
-/

namespace Podc.WritableObjects

open Cslib.SharedMemory

variable {P ι : Type} [DecidableEq P] [DecidableEq ι]

/-- A template implementation (Figure 4.4) satisfying condition (C) whose base objects are
`k`-word registers implemented as in Figure 4.2 is linearizable. -/
theorem template_kWord_linearizable (k : ℕ) (Wd : Type) (w₀ : Wd) (owner : ι → P)
    (α : List (Ev P ι (kWordReg k Wd w₀)))
    (hT : Template (kWordWritable k Wd w₀) owner α) (hC : CondC α)
    (hA : ∀ i, ∃ β, (kWordImpl k Wd w₀ P).Valid β ∧
      dropTau β = lowH (kWordWritable k Wd w₀) i α) :
    ∃ L, IsLinearization (highH (kWordWritable k Wd w₀) α) L := by
  refine lemma_4_5 _ owner α hT hC (fun i => ?_)
  obtain ⟨β, hβ, heq⟩ := hA i
  rw [← heq]
  exact (kWord_seqWritable k Wd w₀ P β hβ).dropTau

end Podc.WritableObjects
