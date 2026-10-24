import Papers.PODC2024.DataCenterRouting.Section3
import Papers.PODC2024.DataCenterRouting.Matching
import Papers.PODC2024.DataCenterRouting.LinkDisjoint

/-!
# Section 5: maximizing throughput versus satisfying demands

* `lemma_5_2`: some maximum-throughput allocation of `MS_n` is a throughput-maximum-throughput
  allocation of `C_n` (Lemma 5.2, via König's line colouring);
* `theorem_5_4_upper`: for every routing, the max-min fair allocation of `C_n` has throughput at
  most `2 T^MmF` (first part of Theorem 5.4);
* `theorem_5_4_tight_odd` / `theorem_5_4_tight_even`: the stacked gadgets of Example 5.3 routed by
  the Doom-Switch algorithm (second part of Theorem 5.4).
-/

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

/-- **Lemma 5.2 (Folklore).** For every collection of flows in `C_n` there is a maximum-throughput
allocation `a^MT` of `MS_n` which is also a throughput-maximum-throughput allocation `a^{T-MT}` of
`C_n` (for some routing); hence `T^MT = T^{T-MT}`. -/
theorem lemma_5_2 {n : ℕ} {F : Type*} [Fintype F] (fl : Flows n F) :
    ∃ (a : F → ℝ) (r : F → Fin n), (macroSwitch fl).IsMaxThroughput a ∧
      IsThroughputMaxThroughput fl r a := by
  obtain ⟨S, hS⟩ := exists_isMaximumMatching fl
  obtain ⟨r, hr⟩ := exists_routing_feasible_of_isMatching fl hS.1
  have hMT := lemma_3_2 fl hS
  refine ⟨indicatorAlloc S, r, hMT, ⟨hr, fun b hb => hMT.2 b (Feasible.toMacroSwitch fl hb)⟩,
    fun r' a' ha' => hMT.2 a' (Feasible.toMacroSwitch fl ha'.1)⟩

/-- **Theorem 5.4, first part.** For every collection of flows in `C_n` and every routing `r`, the
throughput of the max-min fair allocation for `r` is at most twice the throughput `T^MmF` of the
max-min fair allocation in the macro-switch; in particular `T^{T-MmF} ≤ 2 T^MmF`. -/
theorem theorem_5_4_upper {n : ℕ} {F : Type*} [Fintype F] (fl : Flows n F)
    {r : F → Fin n} {a aMS : F → ℝ} (ha : (clos fl r).IsMaxMinFair a)
    (hMS : (macroSwitch fl).IsMaxMinFair aMS) : throughput a ≤ 2 * throughput aMS := by
  have := theorem_3_4_lower fl hMS (Feasible.toMacroSwitch fl ha.1)
  linarith

end Podc.DataCenterRouting
