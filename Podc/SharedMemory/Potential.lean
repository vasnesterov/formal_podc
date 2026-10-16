import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Wait-freedom from a potential on local states

`Impl.waitFree_of_potential`: if a potential on local states strictly decreases with every
base-object access of a process, the implementation is wait-free (each operation finishes within
`μ p l` own steps). Moved here from `Papers/PODC2024/HistoryIndependent/Alg4WaitFree.lean`
(same name and namespace) so that several papers can use it.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

-- CSLib candidate
namespace Impl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  (I : Impl A B P L)

/-- **Bounded steps ⇒ wait-free.** -/
theorem waitFree_of_potential (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) < μ p l) : I.WaitFree := by
  intro e p n hpend
  let f : ℕ → ℕ := fun m => μ p ((e.cfg m).loc p)
  -- one step: the potential does not increase, and decreases at internal steps of `p`
  have hstep : ∀ m ≥ n, f (m + 1) ≤ f m ∧ (e.lbl m = .tau p → f (m + 1) < f m) := by
    intro m hm
    have hs := e.step_eq m
    by_cases hq : (e.lbl m).proc = p
    · cases hl : e.lbl m with
      | inv q o =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (Impl.step_inv hs).1 (hpend m hm)
      | ret q r =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (by simp [(Impl.step_ret hs).2.1]) (hpend (m + 1) (by omega))
      | tau q =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
        have : f (m + 1) < f m := by
          simp only [f, hloc, Function.update_self]
          exact hμ _ _ i o k hact _
        exact ⟨this.le, fun _ => this⟩
    · have := (Impl.step_other hs hq).1
      refine ⟨by simp [f, this], fun h => absurd (by rw [h]; rfl) hq⟩
  have hmono : ∀ m ≥ n, ∀ j, f (m + j) ≤ f m := by
    intro m hm j
    induction j with
    | zero => simp
    | succ j ih => exact ((hstep (m + j) (by omega)).1).trans ih
  have key : ∀ k, ∀ m ≥ n, f m ≤ k → ∃ N, ∀ m' ≥ N, e.lbl m' ≠ .tau p := by
    intro k
    induction k with
    | zero =>
      intro m hm hf
      refine ⟨m, fun m' hm' heq => ?_⟩
      have h1 := (hstep m' (by omega)).2 heq
      have h2 := hmono m hm (m' - m)
      rw [show m + (m' - m) = m' by omega] at h2
      omega
    | succ k ih =>
      intro m hm hf
      by_cases hex : ∃ m' ≥ m, e.lbl m' = .tau p
      · obtain ⟨m', hm', heq⟩ := hex
        have h1 := (hstep m' (by omega)).2 heq
        have h2 := hmono m hm (m' - m)
        rw [show m + (m' - m) = m' by omega] at h2
        exact ih (m' + 1) (by omega) (by omega)
      · push Not at hex
        exact ⟨m, hex⟩
  exact key (f n) n le_rfl le_rfl

end Impl

end Cslib.SharedMemory
