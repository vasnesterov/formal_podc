import Cslib.Computability.Distributed.Byzantine.PartialSync.Model

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/PartialSync/Quiescence.lean

/-!
# Quiescence: runs in which nothing happens any more

To show that a concrete run of a partially synchronous algorithm is stuck forever (e.g. that no
correct process ever decides), it suffices to check, at one time `T`, that

* every correct process sends nothing and its state is a fixed point of `step` on an empty inbox,
* no batch sent before `T` is delivered at or after `T`, and
* faulty processes send nothing from `T` on.

Then the states of correct processes never change after `T` (`Run.st_eq_of_quiescent`). The
first condition is decidable on concrete states, so it can be checked by evaluation (e.g. on the
memoised simulator `simHist`).
-/

namespace Cslib.Byzantine.PartialSync

variable {P M S VI VO : Type*} [DecidableEq P]
variable (A : Algorithm P M S VI VO) (R : Run P M VI) (T : ℕ)

namespace Run

/-- **Quiescence.** If at time `T` every correct process is at a fixed point of `step` on an
empty inbox and sends nothing, no batch sent before `T` arrives at or after `T`, and faulty
processes are silent from `T` on, then the correct processes keep their time-`T` states forever. -/
theorem st_eq_of_quiescent
    (hfix : ∀ p ∉ R.faulty, A.step p (R.st A T p) (fun _ => []) = R.st A T p)
    (hsend : ∀ p ∉ R.faulty, ∀ q, A.send p (R.st A T p) q = [])
    (hdl : ∀ q τ' p τ, τ' < T → T ≤ τ → R.dl q τ' p ≠ τ)
    (hbyz : ∀ q ∈ R.faulty, ∀ τ p, T ≤ τ → R.byz q τ p = []) :
    ∀ k, ∀ p ∉ R.faulty, R.st A (T + k) p = R.st A T p := by
  suffices H : ∀ k, ∀ j ≤ k, ∀ p ∉ R.faulty, R.st A (T + j) p = R.st A T p from
    fun k => H k k le_rfl
  intro k
  induction k with
  | zero => intro j hj p _; obtain rfl : j = 0 := by omega
            rfl
  | succ k ih =>
    intro j hj p hp
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact ih j (by omega) p hp
    obtain rfl : j = k + 1 := by omega
    have hib : R.inbox A p (T + k) = fun _ => [] := by
      funext q
      rw [inbox_eq_flatMap, List.flatMap_eq_nil_iff]
      intro τ' hτ'
      simp only [List.mem_range] at hτ'
      simp only [dlv]
      split_ifs with hd
      · by_cases hlt : τ' < T
        · exact absurd hd (hdl q τ' p (T + k) hlt (by omega))
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlt)
          by_cases hqF : q ∈ R.faulty
          · rw [out_of_faulty _ _ hqF]; exact hbyz q hqF _ p (by omega)
          · rw [out_of_correct _ _ hqF, ih i (by omega) q hqF]
            exact hsend q hqF p
      · rfl
    rw [show T + (k + 1) = (T + k) + 1 by omega, st_succ, hib, ih k le_rfl p hp, hfix p hp]

end Run

end Cslib.Byzantine.PartialSync
