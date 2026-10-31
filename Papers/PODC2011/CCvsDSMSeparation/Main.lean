import Papers.PODC2011.CCvsDSMSeparation.LowerBound
import Papers.PODC2011.CCvsDSMSeparation.CCTerminating
import Papers.PODC2011.CCvsDSMSeparation.NonTerminating

/-!
# Main results of Golab, *A complexity separation between the cache-coherent and distributed
shared memory models* (PODC 2011)

* `theorem_6_2_terminating` (Theorem 6.2): no deterministic terminating read/write algorithm for
  the signaling problem (polling semantics) has `O(1)` amortized RMR complexity in the DSM model.
* `section_5` (Section 5): the one-Boolean algorithm solves the problem, is terminating, and has
  at most 2 RMRs per process in the CC model.
* `separation`: both together.
* `corollary_6_14_needs_terminating`: without termination (as Corollary 6.14 is literally stated)
  the lower bound fails.
-/

namespace Podc.CCvsDSMSeparation

/-- **Theorem 6.2** (with the paper's notion of a terminating algorithm). For every constant `c`
there is `N₀` such that for every `N ≥ N₀` and every deterministic terminating algorithm `A` for
`N` processes that solves the signaling problem (polling semantics, one signaler, waiters not fixed
in advance) using atomic reads and writes, there is a history of `A` (with at most one call to
`Signal()`) in which `k ≤ c² + c + 1` processes participate and incur more than `c·k` RMRs in the
DSM model. -/
theorem theorem_6_2_terminating (c : ℕ) : ∃ N₀, ∀ N ≥ N₀, ∀ {V Val S : Type*}
    (A : Algorithm N V Val S), A.Terminating → A.Solves →
    ∃ τ : List (Ev N V Val), A.Valid τ ∧ signals τ ≤ 1 ∧ (par τ).card ≤ c * c + c + 1 ∧
      c * (par τ).card < A.rmr τ := by
  obtain ⟨N₀, h⟩ := theorem_6_2 c
  exact ⟨N₀, fun N hN V Val S A hT hS => h N hN A (Algorithm.Terminating.soloTerminating A hT) hS⟩

/-- **Section 5.** The algorithm with one shared Boolean solves the signaling problem, is
terminating, and every process incurs at most 2 RMRs in the CC model (so at most `2k` in total when
`k` processes participate), in every execution with one signaler. -/
theorem section_5 (N : ℕ) [NeZero N] :
    (ccAlg N).Solves ∧ (ccAlg N).Terminating ∧
    ∀ τ, (ccAlg N).Valid τ → signals τ ≤ 1 →
      (∀ p, ccRMROf τ p ≤ 2) ∧ ccRMR τ ≤ 2 * (par τ).card :=
  ⟨ccAlg_solves, ccAlg_terminating, fun _ hv hs =>
    ⟨ccAlg_ccRMROf_le hv hs, ccAlg_ccRMR_le hv hs⟩⟩

/-- **The separation.** For every `c` and all large `N`: the signaling problem is solved by a
terminating algorithm with at most 2 RMRs per process in the CC model, while every terminating
read/write algorithm solving it has a history with `k ≤ c² + c + 1` participants and more than `c·k`
RMRs in the DSM model. -/
theorem separation (c : ℕ) : ∃ N₀, ∀ N ≥ N₀, [NeZero N] →
    ((ccAlg N).Solves ∧ (ccAlg N).Terminating ∧
      ∀ τ, (ccAlg N).Valid τ → signals τ ≤ 1 → ccRMR τ ≤ 2 * (par τ).card) ∧
    ∀ {V Val S : Type*} (A : Algorithm N V Val S), A.Terminating → A.Solves →
      ∃ τ : List (Ev N V Val), A.Valid τ ∧ signals τ ≤ 1 ∧ (par τ).card ≤ c * c + c + 1 ∧
        c * (par τ).card < A.rmr τ := by
  obtain ⟨N₀, h⟩ := theorem_6_2_terminating c
  exact ⟨N₀, fun N hN _ => ⟨⟨ccAlg_solves, ccAlg_terminating, fun _ hv hs => ccAlg_ccRMR_le hv hs⟩,
    fun A hT hS => h N hN A hT hS⟩⟩

/-- Non-vacuity: the hypotheses of Theorem 6.2 are satisfiable. -/
example : (ccAlg 5).Terminating ∧ (ccAlg 5).Solves := ⟨ccAlg_terminating, ccAlg_solves⟩

end Podc.CCvsDSMSeparation
