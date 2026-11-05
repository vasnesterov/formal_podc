import Papers.PODC2010.ModularConsensus.AdoptCommit

/-!
# The fast path (Sections 4.1.1 and 4.2)

"If some process `p` finishes `A₋₁` before any process with a different input arrives, then the
convergence condition implies that `p` must commit, because it cannot distinguish this execution
from one in which all processes have the same input."

In CSLib's model the indistinguishability argument is immediate: the prefix of the execution
ending with `p`'s response is itself an execution, in which all inputs are equal. So for *every*
implementation of an adopt-commit object (`fastPath`), and in particular for Procedure
AdoptCommit (`fastPath_acImpl`), a process that returns before any process with a different
input has invoked the object commits. Section 4.2 uses the same fact for `A* = A₁; A₂; …`.
-/

namespace Podc.ModularConsensus

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {V : Type} [Inhabited V] {ι : Type} [DecidableEq ι]
  {B : ι → ObjSpec} {L : Type}

/-- **Fast path.** For any implementation of an adopt-commit object: if `p` returns `r` at the end
of a one-shot execution `α ++ [ret p r]` in which every process that has invoked the object so far
has input `v`, then `r = (commit, v)`. -/
theorem fastPath (I : Impl (AC.acObj V) B P L)
    (hI : I.Solves (adoptCommitTask P V)) {α : List (Label P (AC.acObj V))}
    {p : P} {r : Decision × V} (hα : I.Valid (α ++ [.ret p r])) (hos : OneShot (α ++ [.ret p r]))
    {v : V} (hv : ∀ q x, inputs α q = some x → x = v) : r = (.commit, v) := by
  obtain ⟨C, hC⟩ := hα
  have hΔ : Convergence (inputs (α ++ [.ret p r])) (outputs (α ++ [.ret p r])) :=
    (hI _ ⟨C, hC⟩ hos).2.2
  have hin : inputs (α ++ [.ret p r]) = inputs α := by
    funext q; simp [inputs, opsOf_append]
  have hresp : respsOf α p = [] := by
    have h1 := Impl.run_resps_le_ops hC p
    have h2 := hos p
    simp only [respsOf_append, opsOf_append, List.length_append] at h1 h2
    have h3 : (respsOf [(Label.ret p r : Label P (AC.acObj V))] p).length = 1 := by simp [respsOf]
    have h4 : (opsOf [(Label.ret p r : Label P (AC.acObj V))] p).length = 0 := by simp [opsOf]
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hout : outputs (α ++ [.ret p r]) p = some r := by
    simp only [outputs, respsOf_append, hresp, List.nil_append]
    simp [respsOf]
  rw [hin] at hΔ
  obtain ⟨h1, h2⟩ := hΔ v hv p r.1 r.2 (by rw [hout])
  rw [← h1, ← h2]

/-- The fast path for Procedure AdoptCommit. -/
theorem fastPath_acImpl {W R : V → Finset ι} [DecidableEq V]
    (hWR : ∀ v v', Disjoint (W v) (R v') ↔ v = v')
    {α : List (Label P (AC.acObj V))} {p : P} {r : Decision × V}
    (hα : (AC.acImpl P W R).Valid (α ++ [.ret p r])) (hos : OneShot (α ++ [.ret p r])) {v : V}
    (hv : ∀ q x, inputs α q = some x → x = v) : r = (.commit, v) :=
  fastPath (AC.acImpl P W R) (AC.theorem8_solves hWR) hα hos hv

end Podc.ModularConsensus
