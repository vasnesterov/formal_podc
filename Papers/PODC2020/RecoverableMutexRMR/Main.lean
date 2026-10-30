import Papers.PODC2020.RecoverableMutexRMR.Liveness
import Papers.PODC2020.RecoverableMutexRMR.WaitFree
import Papers.PODC2020.RecoverableMutexRMR.RMRLiteral
import Papers.PODC2020.RecoverableMutexRMR.Lemma2_1_19

/-!
# Theorem 2 of Chan–Woelfel (PODC 2020), summary

The recoverable mutual exclusion algorithm of Figure 1 satisfies mutual exclusion,
critical-section re-entry (wait-free), starvation freedom (hence deadlock freedom), wait-free
recovery, wait-free recovery to exit, and has `O(m)` total RMRs in the DSM model.
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

/-- **Theorem 2** (all properties except the CC-model RMR bound, the per-passage worst case and
FCFS, which the paper proves only in its full version). -/
theorem theorem2 :
    -- mutual exclusion (Lemma 2.11)
    (∀ (e : ℕ → Ev P) t p q, (exec e t).pc p = .cs → (exec e t).pc q = .cs → p = q) ∧
    -- critical section re-entry
    (∀ (e : ℕ → Ev P) p t₀, (exec e t₀).pc p = .cs → e t₀ = .crash p → ∀ t, t₀ < t →
      (∀ u, t₀ < u → u ≤ t → (exec e u).pc p ≠ .cs) → ∀ q, (exec e t).pc q ≠ .cs) ∧
    -- starvation freedom (Lemma 2.13)
    (∀ (e : ℕ → Ev P), Fair e → FinCrashes e → ∀ p t,
      ∃ t', t ≤ t' ∧ ((exec e t').pc p = .rem ∨ (exec e t').pc p = .cs)) ∧
    -- total RMRs (DSM), every crash counted as the start of a passage
    (∀ (e : ℕ → Ev P) t, totalRMR e t ≤ 25 * numEnter e t + 76 * numCrashes e t) :=
  ⟨mutual_exclusion, fun e p t₀ h1 h2 t ht hn q => cs_reentry e p t₀ h1 h2 t ht hn q,
    fun e hF hC p t => eventually_rem_or_cs e hF hC p t, rmr_bound⟩

end Podc.RecoverableMutexRMR
