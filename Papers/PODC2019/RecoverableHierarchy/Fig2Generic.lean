import Papers.PODC2019.RecoverableHierarchy.Fig2Safe
import Papers.PODC2019.RecoverableHierarchy.Theorem6

/-!
# Figure 2 is generic (Definition 5)

A process that has accessed a consensus object `C[k]` never accesses it again (whether or not it
crashes), since `R[i] ≥ k + 1` from then on (`Used`). Hence the algorithm of Figure 2 is
*generic* in the sense of Definition 5, so Theorem 6 applies to it: with `f + 1` consensus objects
it is optimal.
-/

namespace Podc.RecoverableHierarchy.Fig2

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {n f : ℕ}

lemma Used.run {C : Cfg (A n f)} (hI : Inv C) {p : Fin n} {k : Fin (f + 1)} (hU : Used C p k)
    (β : List (Ev n)) : Used (Cslib.SharedMemory.Recoverable.run C β) p k := by
  induction β generalizing C with
  | nil => exact hU
  | cons e β ih =>
    refine ih (hI.next e) ?_
    rcases e with q | q
    · exact hU.step hI q
    · exact hU.crash q

lemma objOf_of_poised {C : Cfg (A n f)} {p : Fin n} {i : Idx n f} (h : C.Poised p i) :
    objOf C p = some i := by
  obtain ⟨o, κ, h⟩ := h
  unfold objOf; rw [h]

/-- After an access to `C[k]`, `p` is never poised on `C[k]` again. -/
lemma not_poised_after {C : Cfg (A n f)} (hI : Inv C) {p : Fin n} {k : Fin (f + 1)}
    (h : C.Poised p (.inr k)) (β : List (Ev n)) :
    ¬ (Cslib.SharedMemory.Recoverable.run (C.stepP p) β).Poised p (.inr k) := by
  obtain ⟨j, v, hpc, hj⟩ := objOf_C (objOf_of_poised h)
  rcases hl : C.loc p with ⟨i, pc⟩
  obtain ⟨rfl, hpc'⟩ := hI.locOf hl
  rw [hl] at hpc; subst hpc
  have hU : Used (C.stepP i) i k := by
    rw [stepP_scan_ge hl hj]
    exact ⟨by simp [hpc'.1], by simp, by simp⟩
  intro hp
  obtain ⟨j', v', hpc2, -⟩ := objOf_C (objOf_of_poised hp)
  exact (hU.run (hI.step i) β).2.2 j' v' hpc2

/-- **Figure 2 is generic** (Definition 5), in every execution. -/
theorem fig2_generic : Generic (A n f) (fun i => ∃ k, i = Sum.inr k) (fun _ => True) := by
  rintro x α β γ p i ⟨k, rfl⟩ - hp
  have hI := inv_reach (f := f) x α
  have := not_poised_after hI hp (β ++ [.crash p] ++ γ)
  have e : α ++ [.step p] ++ β ++ [.crash p] ++ γ = (α ++ [.step p]) ++ (β ++ [.crash p] ++ γ) := by
    simp
  rw [e, run_append, run_concat]
  exact this

end Podc.RecoverableHierarchy.Fig2
