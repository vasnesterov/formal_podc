import Papers.PODC2024.DataCenterRouting.Model

/-!
# Section 3: max-min fairness loses at most half of the throughput of a macro-switch

* `theorem_3_4_lower`: for every collection of flows in `MS_n`, `T^MmF ≥ T^MT / 2`;
* `theorem_3_4_tight`: for every `n ≥ 1` and `ε > 0` there is a collection of flows in `MS_n` with
  `T^MmF ≤ (1 + ε) T^MT / 2` (`gadget_throughputs`: Example 3.3 with `k` type-2 flows has
  `T^MmF = 1 + 1/(k+1)` and `T^MT = 2`).

The paper proves the lower bound via the bipartite maximum-matching characterization of `T^MT`
(Lemma 3.2). We use instead the general *price of max-min fairness* bound
`Network.throughput_le_mul_of_isMaxMinFair` (every flow of `MS_n` traverses two links), whose proof
uses only that every flow has a saturated link; Lemma 3.2 itself is `lemma_3_2` in
`Matching.lean`.
-/

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

/-- **Theorem 3.4, first part.** For every collection of flows in the macro-switch `MS_n`, the
throughput of the max-min fair allocation is at least half of the throughput of every feasible
allocation (in particular of the maximum throughput `T^MT`). -/
theorem theorem_3_4_lower {n : ℕ} {F : Type*} [Fintype F] (fl : Flows n F) {a b : F → ℝ}
    (ha : (macroSwitch fl).IsMaxMinFair a) (hb : (macroSwitch fl).Feasible b) :
    throughput b / 2 ≤ throughput a := by
  have := Network.throughput_le_mul_of_isMaxMinFair ha hb 2 fun f => by
    simp only [macroSwitch]
    exact (Finset.card_insert_le _ _).trans (by simp)
  push_cast at this
  linarith

/-! ### The adversarial flows of Example 3.3 / Theorem 3.4 -/

section Gadget

variable (m k : ℕ)

/-- The two servers used by the gadget: `s_1^1` / `t_1^1` (0-based `(0, 0)`). -/
abbrev gs0 : Server (m + 1) := (⟨0, by omega⟩, 0)
/-- The two servers used by the gadget: `s_2^1` / `t_2^1` (0-based `(1, 0)`). -/
abbrev gs1 : Server (m + 1) := (⟨1, by omega⟩, 0)

/-- Flows of the tightness example in `MS_{m+1}` (Figure 2): `inl 0` is the type-1 flow
`(s_1^1, t_1^1)`, `inl 1` the type-1 flow `(s_2^1, t_2^1)`, and `inr c`, `c < k`, are the `k`
type-2 flows `(s_2^1, t_1^1)`. -/
def gadget : Flows (m + 1) (Fin 2 ⊕ Fin k) where
  src
    | .inl i => if i = 0 then gs0 m else gs1 m
    | .inr _ => gs1 m
  dst
    | .inl i => if i = 0 then gs0 m else gs1 m
    | .inr _ => gs0 m

theorem gs0_ne_gs1 : gs0 m ≠ gs1 m := by
  simp [Prod.ext_iff]

theorem gadget_load_src (a : Fin 2 ⊕ Fin k → ℝ) (s : Server (m + 1)) :
    (macroSwitch (gadget m k)).load a (.srcLink s) =
      (if gs0 m = s then a (.inl 0) else 0) +
      (if gs1 m = s then a (.inl 1) + ∑ c, a (.inr c) else 0) := by
  rw [macroSwitch_load_srcLink, Fintype.sum_sum_type, Fin.sum_univ_two]
  by_cases h0 : gs0 m = s <;> by_cases h1 : gs1 m = s <;> simp [gadget, h0, h1] <;> ring

theorem gadget_load_dst (a : Fin 2 ⊕ Fin k → ℝ) (s : Server (m + 1)) :
    (macroSwitch (gadget m k)).load a (.dstLink s) =
      (if gs0 m = s then a (.inl 0) + ∑ c, a (.inr c) else 0) +
      (if gs1 m = s then a (.inl 1) else 0) := by
  rw [macroSwitch_load_dstLink, Fintype.sum_sum_type, Fin.sum_univ_two]
  by_cases h0 : gs0 m = s <;> by_cases h1 : gs1 m = s <;> simp [gadget, h0, h1] <;> ring

/-- The max-min fair allocation of the gadget: all flows get `1/(k+1)`. -/
theorem gadget_isMaxMinFair :
    (macroSwitch (gadget m k)).IsMaxMinFair (fun _ => 1 / (k + 1 : ℝ)) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hsum : ∑ _c : Fin k, 1 / (k + 1 : ℝ) = k / (k + 1) := by
    simp [div_eq_mul_inv]
  have hone : 1 / (k + 1 : ℝ) + k / (k + 1) = 1 := by field_simp; ring
  apply Network.isMaxMinFair_of_hasBottlenecks
  · refine ⟨fun _ => by positivity, fun ℓ => ?_⟩
    have hle : 1 / (k + 1 : ℝ) ≤ 1 := by rw [div_le_one hk]; linarith
    cases ℓ with
    | srcLink s =>
      rw [gadget_load_src, hsum]
      by_cases h0 : gs0 m = s <;> by_cases h1 : gs1 m = s
      · exact absurd (h0.trans h1.symm) (gs0_ne_gs1 m)
      all_goals simp only [h0, h1, ite_true, ite_false, add_zero, zero_add, macroSwitch_cap] <;>
        linarith
    | dstLink s =>
      rw [gadget_load_dst, hsum]
      by_cases h0 : gs0 m = s <;> by_cases h1 : gs1 m = s
      · exact absurd (h0.trans h1.symm) (gs0_ne_gs1 m)
      all_goals simp only [h0, h1, ite_true, ite_false, add_zero, zero_add, macroSwitch_cap] <;>
        linarith
    | up i j => rw [macroSwitch_load_up]; simp
    | down i j => rw [macroSwitch_load_down]; simp
  · intro f
    -- every flow has a bottleneck: `inl 0` on `t_1^1`, the others on `s_2^1`
    rcases f with i | c
    · fin_cases i
      · refine ⟨.dstLink (gs0 m), by simp [macroSwitch, gadget], ?_, fun _ _ => le_rfl⟩
        rw [gadget_load_dst, hsum, ite_eq_left rfl, ite_eq_right (gs0_ne_gs1 m).symm, add_zero]
        simpa using hone
      · refine ⟨.srcLink (gs1 m), by simp [macroSwitch, gadget], ?_, fun _ _ => le_rfl⟩
        rw [gadget_load_src, hsum, ite_eq_left rfl, ite_eq_right (gs0_ne_gs1 m), zero_add]
        simpa using hone
    · refine ⟨.srcLink (gs1 m), by simp [macroSwitch, gadget], ?_, fun _ _ => le_rfl⟩
      rw [gadget_load_src, hsum, ite_eq_left rfl, ite_eq_right (gs0_ne_gs1 m), zero_add]
      simpa using hone

/-- The maximum-throughput allocation of the gadget: rate `1` for both type-1 flows, `0` for the
type-2 flows. -/
theorem gadget_isMaxThroughput :
    (macroSwitch (gadget m k)).IsMaxThroughput (fun f => if f.isLeft then 1 else 0) := by
  refine ⟨⟨fun f => by dsimp only; split_ifs <;> norm_num, fun ℓ => ?_⟩, fun b hb => ?_⟩
  · cases ℓ with
    | srcLink s =>
      rw [gadget_load_src]
      by_cases h0 : gs0 m = s <;> by_cases h1 : gs1 m = s
      · exact absurd (h0.trans h1.symm) (gs0_ne_gs1 m)
      all_goals simp [h0, h1]
    | dstLink s =>
      rw [gadget_load_dst]
      by_cases h0 : gs0 m = s <;> by_cases h1 : gs1 m = s
      · exact absurd (h0.trans h1.symm) (gs0_ne_gs1 m)
      all_goals simp [h0, h1]
    | up i j => rw [macroSwitch_load_up]; simp
    | down i j => rw [macroSwitch_load_down]; simp
  · have h0 := hb.2 (.srcLink (gs0 m))
    have h1 := hb.2 (.srcLink (gs1 m))
    rw [gadget_load_src, ite_eq_left rfl, ite_eq_right (gs0_ne_gs1 m).symm, add_zero] at h0
    rw [gadget_load_src, ite_eq_left rfl, ite_eq_right (gs0_ne_gs1 m), zero_add] at h1
    simp only [throughput, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.isLeft_inl,
      Sum.isLeft_inr, ite_true, Bool.false_eq_true, ite_false, Finset.sum_const_zero]
    simp only [macroSwitch_cap] at h0 h1
    linarith

/-- **Example 3.3 generalized (proof of Theorem 3.4, second part).** For the gadget with `k`
type-2 flows, `T^MmF = 1 + 1/(k+1)` and `T^MT = 2`, for every max-min fair allocation and every
maximum-throughput allocation of `MS_{m+1}`. -/
theorem gadget_throughputs {a b : Fin 2 ⊕ Fin k → ℝ}
    (ha : (macroSwitch (gadget m k)).IsMaxMinFair a)
    (hb : (macroSwitch (gadget m k)).IsMaxThroughput b) :
    throughput a = 1 + 1 / (k + 1) ∧ throughput b = 2 := by
  have e := ha.eq (gadget_isMaxMinFair m k)
  subst e
  constructor
  · simp only [throughput, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fintype.card_sum]
    push_cast
    field_simp
    ring
  · have h1 := hb.2 _ (gadget_isMaxThroughput m k).1
    have h2 := (gadget_isMaxThroughput m k).2 _ hb.1
    have h3 : throughput (fun f : Fin 2 ⊕ Fin k => if f.isLeft then (1 : ℝ) else 0) = 2 := by
      simp only [throughput, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.isLeft_inl,
        Sum.isLeft_inr, ite_true, Bool.false_eq_true, ite_false, Finset.sum_const_zero]
      norm_num
    linarith

/-- **Example 3.3** (`k = 1`): `T^MmF = 3/2` and `T^MT = 2`. -/
theorem example_3_3 {a b : Fin 2 ⊕ Fin 1 → ℝ}
    (ha : (macroSwitch (gadget m 1)).IsMaxMinFair a)
    (hb : (macroSwitch (gadget m 1)).IsMaxThroughput b) :
    throughput a = 3 / 2 ∧ throughput b = 2 := by
  obtain ⟨h1, h2⟩ := gadget_throughputs m 1 ha hb
  exact ⟨by rw [h1]; norm_num, h2⟩

end Gadget

/-- **Theorem 3.4, second part (tightness).** For every `n ≥ 1` and every `ε > 0` there is a
collection of flows in `MS_n` (which has a max-min fair and a maximum-throughput allocation) such
that `T^MmF ≤ (1 + ε) T^MT / 2`. -/
theorem theorem_3_4_tight (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ (F : Type) (_ : Fintype F) (fl : Flows n F),
      (∃ a, (macroSwitch fl).IsMaxMinFair a) ∧ (∃ b, (macroSwitch fl).IsMaxThroughput b) ∧
      ∀ a b, (macroSwitch fl).IsMaxMinFair a → (macroSwitch fl).IsMaxThroughput b →
        throughput a ≤ (1 + ε) * throughput b / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  refine ⟨Fin 2 ⊕ Fin k, inferInstance, gadget m k, ⟨_, gadget_isMaxMinFair m k⟩,
    ⟨_, gadget_isMaxThroughput m k⟩, fun a b ha hb => ?_⟩
  obtain ⟨h1, h2⟩ := gadget_throughputs m k ha hb
  rw [h1, h2]
  have hk' : 1 / (k + 1 : ℝ) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hk
    nlinarith
  linarith

end Podc.DataCenterRouting
