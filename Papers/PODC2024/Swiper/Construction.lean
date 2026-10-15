import Papers.PODC2024.Swiper.WeightRestriction

/-!
# Swiper's construction for Weight Restriction (Appendix A.1, faithful route)

The paper's proof of Theorem 2.1 considers `(t_s)_i = ⌊w_i s + αw⌋`, a *locally minimal viable*
`s*` (`t_{s*}` viable, `t_{s*-ε}` not viable for all small `ε > 0`), the set
`J = {i | w_i s* + αw ∈ ℤ}` of parties "on the border", the assignment `t'` that takes one ticket
from every party of `J`, and then removes tickets from parties in `J` "as long as the ticket
assignment stays viable", ending with `t̂` viable and `t̂̂ = t̂ - e_j` not viable.

Here:
* `exists_locallyMinimal`: a locally minimal viable `s*` exists. The paper only says "since we
  already proved that viable values of `s` exist, it is easy to see that such `s*` exists"; no such
  earlier proof is in the paper. We supply both steps: viable values exist by the key lemma
  (`exists_viable`), and the infimum of the viable values is attained by right-continuity of the
  floor (a discreteness argument); it is positive because `t_s = 0` for small `s`.
* `border_nonempty`: `J ≠ ∅` ("Moreover, there must be some `j` such that `s* w_j + αw` is an
  integer").
* `ts_sub_eventually_eq`: footnote 6, `t' = t_{s*-ε}` for all small `ε > 0`; hence `t'` is not
  viable (`not_viable_removeTickets_border`).
* `exists_removal`: the removal process stops at some `t̂ = t* - 1_K` (`K ⊆ J`) viable with
  `t* - 1_{K ∪ {j}}` not viable, `j ∈ J \ K`.
* `removal_bound`: any such stopping point has `T ≤ ⌈αw (1 - αw) / (αn - αw) · n⌉`.
* `wr_upper_bound_swiper`: Theorem 2.1 again, via this construction.
-/

namespace Papers.PODC2024.Swiper

open Finset Filter Topology Cslib.Apportionment
open scoped Classical

variable {ι : Type*} [Fintype ι]

/-- The ticket assignment `(t_s)_i = ⌊w_i s + c⌋` (Appendix A.1 uses `c = αw`). -/
noncomputable def ts (w : ι → ℝ) (c s : ℝ) : ι → ℕ := fun i => ⌊w i * s + c⌋₊

/-- `s` is a *locally minimal viable* value: `s > 0`, `t_s` is viable, and `t_{s-ε}` is not viable
for all sufficiently small `ε > 0`. -/
def LocallyMinimal (αw αn : ℝ) (w : ι → ℝ) (s : ℝ) : Prop :=
  0 < s ∧ Viable αw αn w (ts w αw s) ∧
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ¬ Viable αw αn w (ts w αw (s - ε))

/-- The parties "on the border": `J = {i | w_i s + c ∈ ℤ}`. -/
noncomputable def border (w : ι → ℝ) (c s : ℝ) : Finset ι :=
  univ.filter fun i => ∃ k : ℕ, w i * s + c = k

/-- Take one ticket from each party of `K`. -/
noncomputable def removeTickets (t : ι → ℕ) (K : Finset ι) : ι → ℕ := fun i => if i ∈ K then t i - 1 else t i

section

variable {αw αn : ℝ} {w : ι → ℝ}

omit [Fintype ι] in
theorem ts_rounds (hw : ∀ i, 0 ≤ w i) {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) :
    Rounds w c s (ts w c s) :=
  rounds_floor fun i => add_nonneg (mul_nonneg (hw i) hs) hc

/-- Viable values of `s` exist (the step the paper refers to as "already proved"). -/
theorem exists_viable (hαw : 0 < αw) (hlt : αw < αn) (hαn : αn < 1) (hw : ∀ i, 0 ≤ w i)
    (hW : ∑ i, w i ≠ 0) : ∃ s, 0 < s ∧ Viable αw αn w (ts w αw s) := by
  have hWp := sum_pos_of_sum_ne_zero hw hW
  set B := wrBound αw αn (Fintype.card ι)
  have hB : 0 ≤ B := by
    unfold B wrBound
    have : 0 < αn - αw := by linarith
    have : 0 < 1 - αw := by linarith
    positivity
  set s := (B + Fintype.card ι + 1) / ∑ i, w i
  have hs : 0 < s := by positivity
  have ht := ts_rounds hw hαw.le hs.le
  have hT : B ≤ ∑ i, (ts w αw s i : ℝ) := by
    have h1 : ∑ i, (w i * s + αw - 1) ≤ ∑ i, (ts w αw s i : ℝ) :=
      Finset.sum_le_sum fun i _ => (ht i).1
    have h2 : ∑ i, (w i * s + αw - 1) = s * ∑ i, w i + (αw - 1) * Fintype.card ι := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
      simp; ring
    have h3 : s * ∑ i, w i = B + Fintype.card ι + 1 := div_mul_cancel₀ _ hW
    have : (0 : ℝ) ≤ Fintype.card ι := by positivity
    nlinarith
  have hWR := isWR_of_rounds hαw (by linarith) hlt hs.le ht hT
  exact ⟨s, hs, hWR.sum_ne_zero hWp hαw, hWR⟩

/-- For small `s`, `t_s = 0`, which is not viable. -/
theorem not_viable_of_small (hαw : 0 ≤ αw) (hw : ∀ i, 0 ≤ w i) {s : ℝ} (hs : 0 ≤ s)
    (hsmall : s * ∑ i, w i < 1 - αw) : ¬ Viable αw αn w (ts w αw s) := by
  rintro ⟨h0, -⟩
  apply h0
  refine Finset.sum_eq_zero fun i _ => (ts_rounds hw hαw hs).eq_zero_of_lt ?_
  have : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw j) (mem_univ i)
  nlinarith

/-- `t_s` is locally constant to the right of every `σ ≥ 0`. -/
theorem ts_eventually_eq_right (hw : ∀ i, 0 ≤ w i) {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ) :
    ∀ᶠ s in 𝓝[≥] σ, ts w c s = ts w c σ := by
  have := eventually_all.2 fun i =>
    floor_eventually_eq_right (a := w i) (c := c) (hw i) (add_nonneg (mul_nonneg (hw i) hσ) hc)
  filter_upwards [this] with s hs
  funext i
  exact hs i

/-- **Footnote 6.** For all sufficiently small `ε > 0`, `t_{σ-ε}` is `t_σ` with one ticket taken
from each party on the border. -/
theorem ts_sub_eventually_eq (hw : ∀ i, 0 ≤ w i) {c σ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hσ : 0 ≤ σ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ts w c (σ - ε) = removeTickets (ts w c σ) (border w c σ) := by
  classical
  have := eventually_all.2 fun i =>
    floor_eventually_eq_left (a := w i) (c := c) (σ := σ) (hw i) hc0 hc1 hσ
  filter_upwards [this] with ε hε
  funext i
  simp only [ts, removeTickets, border, mem_filter, mem_univ, true_and]
  convert hε i

/-- **Existence of a locally minimal viable `s*`.** -/
theorem exists_locallyMinimal (hαw : 0 < αw) (hlt : αw < αn) (hαn : αn < 1)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≠ 0) : ∃ s, LocallyMinimal αw αn w s := by
  have hWp := sum_pos_of_sum_ne_zero hw hW
  set V : Set ℝ := {s | 0 < s ∧ Viable αw αn w (ts w αw s)}
  have hV : V.Nonempty := exists_viable hαw hlt hαn hw hW
  have hbdd : BddBelow V := ⟨0, fun s hs => hs.1.le⟩
  set σ := sInf V
  -- every viable value is at least `(1 - αw) / W`
  have hlow : (1 - αw) / ∑ i, w i ≤ σ := by
    refine le_csInf hV fun s hs => ?_
    by_contra h
    push Not at h
    rw [lt_div_iff₀ hWp] at h
    exact not_viable_of_small hαw.le hw hs.1.le h hs.2
  have hσ : 0 < σ := lt_of_lt_of_le (div_pos (by linarith) hWp) hlow
  -- the infimum is attained
  have hmem : σ ∈ V := by
    obtain ⟨s, hs, hsV⟩ :=
      ((ts_eventually_eq_right hw hαw.le hσ.le).and_frequently
        ((isGLB_csInf hV hbdd).frequently_mem hV)).exists
    exact ⟨hσ, hs ▸ hsV.2⟩
  refine ⟨σ, hσ, hmem.2, σ, hσ, fun ε hε hεσ hv => ?_⟩
  exact notMem_of_lt_csInf (by linarith : σ - ε < σ) hbdd ⟨by linarith, hv⟩

/-- `t' = t* - 1_J` is not viable at a locally minimal `s*`. -/
theorem LocallyMinimal.not_viable_removeTickets_border (hαw : 0 < αw) (hαw1 : αw < 1)
    (hw : ∀ i, 0 ≤ w i) {s : ℝ} (h : LocallyMinimal αw αn w s) :
    ¬ Viable αw αn w (removeTickets (ts w αw s) (border w αw s)) := by
  obtain ⟨hs, -, δ, hδ, hnv⟩ := h
  obtain ⟨ε, hε, hεδ⟩ := ((ts_sub_eventually_eq hw hαw hαw1 hs.le).and
    (Ioo_mem_nhdsGT hδ)).exists
  rw [← hε]
  exact hnv ε hεδ.1 hεδ.2

/-- **`J ≠ ∅`** at a locally minimal `s*`. -/
theorem LocallyMinimal.border_nonempty (hαw : 0 < αw) (hαw1 : αw < 1) (hw : ∀ i, 0 ≤ w i)
    {s : ℝ} (h : LocallyMinimal αw αn w s) : (border w αw s).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hJ
  apply h.not_viable_removeTickets_border hαw hαw1 hw
  rw [hJ]
  convert h.2.1
  funext i
  simp [removeTickets]

/-- Removing one ticket from parties on the border keeps a rounding with the same multiplier. -/
theorem rounds_removeTickets (hw : ∀ i, 0 ≤ w i) {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    {K : Finset ι} (hK : K ⊆ border w c s) : Rounds w c s (removeTickets (ts w c s) K) := by
  classical
  intro i
  by_cases hi : i ∈ K
  · obtain ⟨k, hk⟩ := (mem_filter.1 (hK hi)).2
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · have := mul_nonneg (hw i) hs; simp at hk; linarith
      · exact h
    simp only [removeTickets, hi, ite_true, ts, hk, Nat.floor_natCast]
    push_cast [hk1]
    constructor <;> linarith
  · simp only [removeTickets, hi, ite_false]
    exact ts_rounds hw hc.le hs i

theorem sum_removeTickets_insert {t : ι → ℕ} {K : Finset ι} {j : ι} (hj : j ∉ K)
    (htj : 1 ≤ t j) :
    ∑ i, removeTickets t K i = ∑ i, removeTickets t (insert j K) i + 1 := by
  classical
  rw [← Finset.add_sum_erase _ _ (mem_univ j), ← Finset.add_sum_erase _ _ (mem_univ j)]
  have : ∑ i ∈ univ.erase j, removeTickets t K i =
      ∑ i ∈ univ.erase j, removeTickets t (insert j K) i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [removeTickets, Finset.ne_of_mem_erase hi]
  rw [this]
  simp [removeTickets, hj]
  omega

/-- **The bound for Swiper's output (Appendix A.1).** If `t̂ = t* - 1_K` (`K ⊆ J`) and
`t̂̂ = t* - 1_{K ∪ {j}}` (`j ∈ J \ K`) is not viable, then
`T(t̂) ≤ ⌈αw (1 - αw) / (αn - αw) · n⌉`. -/
theorem removal_bound (hαw : 0 < αw) (hlt : αw < αn) (hαn : αn < 1) (hw : ∀ i, 0 ≤ w i)
    (hW : ∑ i, w i ≠ 0) {s : ℝ} (hs : 0 ≤ s) {K : Finset ι} (hK : K ⊆ border w αw s) {j : ι}
    (hjJ : j ∈ border w αw s) (hjK : j ∉ K)
    (hnv : ¬ Viable αw αn w (removeTickets (ts w αw s) (insert j K))) :
    ∑ i, removeTickets (ts w αw s) K i ≤ ⌈wrBound αw αn (Fintype.card ι)⌉₊ := by
  have hWp := sum_pos_of_sum_ne_zero hw hW
  have hr := rounds_removeTickets hw hαw hs (Finset.insert_subset hjJ hK)
  have hlt' : ((∑ i, removeTickets (ts w αw s) (insert j K) i : ℕ) : ℝ) <
      wrBound αw αn (Fintype.card ι) := by
    by_contra hge
    push Not at hge
    push_cast at hge
    have := isWR_of_rounds hαw (by linarith) hlt hs hr hge
    exact hnv ⟨this.sum_ne_zero hWp hαw, this⟩
  have hceil := Nat.lt_ceil.2 hlt'
  have htj : 1 ≤ ts w αw s j := by
    obtain ⟨k, hk⟩ := (mem_filter.1 hjJ).2
    simp only [ts, hk, Nat.floor_natCast]
    rcases Nat.eq_zero_or_pos k with rfl | h
    · have := mul_nonneg (hw j) hs; simp at hk; linarith
    · exact h
  rw [sum_removeTickets_insert hjK htj]
  omega

/-- **The removal process terminates as described.** At a locally minimal `s*` there is `K ⊆ J`
such that `t* - 1_K` is viable and, for some `j ∈ J \ K`, `t* - 1_{K ∪ {j}}` is not. -/
theorem LocallyMinimal.exists_removal (hαw : 0 < αw) (hαw1 : αw < 1) (hw : ∀ i, 0 ≤ w i)
    {s : ℝ} (h : LocallyMinimal αw αn w s) :
    ∃ K ⊆ border w αw s, ∃ j ∈ border w αw s, j ∉ K ∧
      Viable αw αn w (removeTickets (ts w αw s) K) ∧
      ¬ Viable αw αn w (removeTickets (ts w αw s) (insert j K)) := by
  classical
  set J := border w αw s
  set F := J.powerset.filter fun K => Viable αw αn w (removeTickets (ts w αw s) K)
  have hF : F.Nonempty := ⟨∅, by
    simp only [F, mem_filter, mem_powerset, empty_subset, true_and]
    convert h.2.1
    funext i; simp [removeTickets]⟩
  obtain ⟨K, hKmax⟩ := F.exists_maximal hF
  have hKF := hKmax.1
  simp only [F, mem_filter, mem_powerset] at hKF
  have hKJ : K ≠ J := by
    rintro rfl
    exact h.not_viable_removeTickets_border hαw hαw1 hw hKF.2
  obtain ⟨j, hjJ, hjK⟩ : ∃ j ∈ J, j ∉ K := by
    by_contra hc
    push Not at hc
    exact hKJ (Finset.Subset.antisymm hKF.1 hc)
  refine ⟨K, hKF.1, j, hjJ, hjK, hKF.2, fun hv => ?_⟩
  have hmem : insert j K ∈ F := by
    simp only [F, mem_filter, mem_powerset]
    exact ⟨Finset.insert_subset hjJ hKF.1, hv⟩
  have := hKmax.2 hmem (Finset.subset_insert j K)
  exact hjK (this (Finset.mem_insert_self j K))

/-- **Theorem 2.1 via Swiper's construction** (Appendix A.1): the output `t̂` of the construction
is viable and has `T ≤ ⌈αw (1 - αw) / (αn - αw) · n⌉`. -/
theorem wr_upper_bound_swiper (hαw : 0 < αw) (hlt : αw < αn) (hαn : αn < 1)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≠ 0) :
    ∃ s, LocallyMinimal αw αn w s ∧ ∃ K ⊆ border w αw s,
      Viable αw αn w (removeTickets (ts w αw s) K) ∧
      ∑ i, removeTickets (ts w αw s) K i ≤ ⌈αw * (1 - αw) / (αn - αw) * Fintype.card ι⌉₊ := by
  obtain ⟨s, hs⟩ := exists_locallyMinimal hαw hlt hαn hw hW
  obtain ⟨K, hK, j, hj, hjK, hv, hnv⟩ := hs.exists_removal hαw (by linarith) hw
  exact ⟨s, hs, K, hK, hv, removal_bound hαw hlt hαn hw hW hs.1.le hK hj hjK hnv⟩

end

end Papers.PODC2024.Swiper
