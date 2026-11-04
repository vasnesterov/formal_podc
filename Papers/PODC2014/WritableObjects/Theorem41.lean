import Papers.PODC2014.WritableObjects.Lemma48
import Papers.PODC2014.WritableObjects.Cor44

/-!
# Theorem 4.1: the transformation is linearizable

Combining Lemma 4.8 (the algorithm of Figure 4.5 follows the template of Figure 4.4 and satisfies
condition (C), `WF.lemma_4_8_exec`) with Lemma 4.5 (`lemma_4_5`): in every execution of the
algorithm of Figure 4.5 in which the objects `A[i]` behave as sequentially writable objects, the
history of the implemented object `WT` is linearizable (`theorem_4_1`). Instantiated with the
`k`-word register of Figure 4.2 this is the linearizability part of Corollary 4.4
(`corollary_4_4`).
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} [NeZero n] {T : ObjSpec}

/-- **Theorem 4.1 of [AGW14] (thesis numbering), linearizability.** Let `T` be a writable type and
let the objects `A[0 … n(8n+9)-1]` used by the algorithm of Figure 4.5 be sequentially writable
objects of type `T`. Then every execution of the algorithm (from the initial state obtained by the
solo `Write(v₀)` of process `0`) has a linearizable high-level history.

The hypothesis `hSW` says that the history of each `A[i]` in the execution is admissible for a
sequentially writable object (linearizable whenever no `SWrite` overlaps another operation on
`A[i]`). The remaining claims of Theorem 4.1 are by construction of the model: `n(8n+9)` objects
`A[i]` and `2n² + 2n + 1` registers (`Ptr`, `Annc[q]`, `H_p[q]`, `H'_p[q]`, `S_q`), each holding
`O(n²)` values; each `Write`/`Exec` performs one `SWrite`/`Oper` plus a constant number of
register accesses (see the step relation `Step`). -/
theorem theorem_4_1 (W : Writable T) (v0 : T.State) (c : Cfg n T) (hc : IsExecution W v0 c)
    (hSW : ∀ i, SeqWritable W (lowH W i c.tr)) :
    ∃ L, IsLinearization (highH W c.tr) L := by
  obtain ⟨hT, hC⟩ := lemma_4_8_exec W v0 c hc
  exact lemma_4_5 W owner c.tr hT hC hSW

/-- **Corollary 4.4 of [AGW14] (thesis numbering), linearizability.** The algorithm of Figure 4.5
with `k`-word registers implemented as in Figure 4.2 (from `k` single-word registers each) as the
objects `A[i]` is a linearizable `k`-word register: every execution in which the history of each
`A[i]` is (up to internal steps) that of an execution of Figure 4.2 has a linearizable history.
(It uses `k · n(8n+9) + 2n² + 2n + 1 = O(k n²)` registers; each operation performs `k` accesses
of its `A[i]` plus a constant number of other accesses.) -/
theorem corollary_4_4 (k : ℕ) (Wd : Type) (w₀ : Wd) (v0 : Fin k → Wd)
    (c : Cfg n (kWordReg k Wd w₀)) (hc : IsExecution (kWordWritable k Wd w₀) v0 c)
    (hA : ∀ i, ∃ β, (kWordImpl k Wd w₀ (Fin n)).Valid β ∧
      dropTau β = lowH (kWordWritable k Wd w₀) i c.tr) :
    ∃ L, IsLinearization (highH (kWordWritable k Wd w₀) c.tr) L := by
  obtain ⟨hT, hC⟩ := lemma_4_8_exec _ v0 c hc
  exact template_kWord_linearizable k Wd w₀ owner c.tr hT hC hA

end Podc.WritableObjects.WF
