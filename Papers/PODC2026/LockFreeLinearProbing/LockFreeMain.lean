import Papers.PODC2026.LockFreeLinearProbing.LockFreeOwn
import Papers.PODC2026.LockFreeLinearProbing.Lemma4

/-!
# Lock-freedom of the LL/SC hash table (Section 5.3, Lemmas 15–19)
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] [Fintype P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

/-- Every internal step decreases the potential. -/
lemma pot_tau (hI : Inv h N ts C) (hs : (impl h).step C (.tau p) = some C') :
    pot h C' < pot h C := by
  rcases hpc : (C.loc p).pc
  · exfalso; simp [Impl.step, impl, act, hpc] at hs
  · exact pot_fsLL hpc hs
  · exact pot_bsLL hpc hs
  · exact pot_vcSC hI hpc hs
  · exact pot_vcRD hpc hs
  · exact pot_tdSCF hI hpc hs
  · exact pot_tdSCD hI hpc hs
  · exact pot_tdLL hpc hs
  · exact pot_iLL hpc hs
  · exact pot_iSC hI hpc hs
  · exact pot_dsLL hpc hs
  · exact pot_docRD hpc hs
  · exact pot_docSC hI hpc hs
  · exact pot_docRD2 hpc hs
  · exact pot_tail hI hs (Or.inl hpc)
  · exact pot_tail hI hs (Or.inr (Or.inl hpc))
  · exact pot_tail hI hs (Or.inr (Or.inr (Or.inl hpc)))
  · exact pot_tail hI hs (Or.inr (Or.inr (Or.inr (Or.inl hpc))))
  · exact pot_tail hI hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpc)))))
  · exact pot_tail hI hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpc))))))
  · exact pot_tail hI hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpc)))))))
  · exact pot_tail hI hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpc))))))))
  · exact pot_tail hI hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpc))))))))
  · exfalso; simp [Impl.step, impl, act, hpc] at hs

/-- Every invocation decreases the potential (an idle process holds the largest budget). -/
lemma pot_inv (hI : Inv h N ts C) {o : DOp K} (hs : (impl h).step C (.inv p o) = some C') :
    pot h C' < pot h C := by
  obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hidle := hI.idle p hp
  apply pot_lt_of_budget_lt
  have hval : ∀ y, C'.val y = C.val y := fun y => by simp [Cfg.val, hmem]
  refine budget_lt_one (p := p) (fun q hq => ?_) ?_
  · simp only [bud, hloc, update_of_ne hq, hval]
  · simp only [bud, hloc, update_self, hval, budL, hidle, impl, start]; omega

/-- **Lock-freedom** (Section 5.3, Lemmas 18 and 19 with Lemma 15–17): with finitely many
processes, every infinite execution of the LL/SC hash table in which processes keep taking steps
has infinitely many responses. -/
theorem lockFree : (impl (P := P) h).LockFree :=
  Impl.lockFree_of_potential _ (pot h) fun α C ℓ C' hα hs hr => by
    obtain ⟨ts, hI⟩ := inv_of_run hα
    cases ℓ with
    | inv p o => exact pot_inv hI hs
    | tau p => exact pot_tau hI hs
    | ret p r => exact absurd rfl (hr p r)

end Podc.LockFreeLinearProbing
