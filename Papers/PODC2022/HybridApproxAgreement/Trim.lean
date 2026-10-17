import Mathlib
import Cslib.Computability.Distributed.ApproxConsensus.Trim

/-!
# The technical combinatorial lemma (Lemmas 3.6 and 3.7)

For a multiset `V : Multiset ℝ` of size `m`, `kth V i` is its `i`-th smallest element (0-indexed),
`trim V d` is the multiset `T` obtained by discarding the `d` lowest and the `d` highest values, and
`midTrim V d = (min T + max T) / 2 = (kth V d + kth V (m - 1 - d)) / 2` is the new value computed in
line 7 of `Π_AA`.

* `lemma_3_7`: the ranges of the two trimmed multisets intersect (the content of Lemma 3.7; we argue
  directly with order statistics and counting instead of the paper's arrays with `⊥` entries).
* `lemma_3_6`: `|v - v'| ≤ (hi - lo) / 2` whenever `T ∪ T' ⊆ [lo, hi]`; with `lo, hi` the minimum and
  maximum of `T ∪ T'` this is the paper's `|v - v'| ≤ length(T ∪ T') / 2` (`lemma_3_6'`).
* `kth_ge_of_card_filter_lt`, `trim_validity`: if at most `d` of the values lie outside `[lo, hi]`,
  the trimmed values lie in `[lo, hi]` (the validity step of Lemmas 3.2 and 3.4).
* Bridge to CSLib's MSR trimming `Cslib.ApproxConsensus.IsTrim` (ties broken arbitrarily): for the
  values `r` on `N` and any trimming `(Low, Mid, High)` of `d` values on each side,
  `trim_eq_of_isTrim` (`trim (r(N)) d = r(Mid)`), `kth_eq_inf'_of_isTrim`, `kth_eq_sup'_of_isTrim`
  and `midTrim_eq_of_isTrim` (`midTrim (r(N)) d = (min r(Mid) + max r(Mid)) / 2`): the paper's new
  value is the midpoint of the kept values of *any* MSR trimming.
-/

open Multiset

namespace HybridApproxAgreement

/-- The `i`-th smallest element of `V` (0-indexed; `0` if out of range). -/
noncomputable def kth (V : Multiset ℝ) (i : ℕ) : ℝ := (V.sort).getD i 0

/-- `trim V d`: discard the `d` lowest and the `d` highest values of `V`. -/
noncomputable def trim (V : Multiset ℝ) (d : ℕ) : Multiset ℝ :=
  (((V.sort).drop d).take (card V - 2 * d) : List ℝ)

/-- The midpoint of the range of `trim V d`, i.e. `(min T + max T) / 2`. -/
noncomputable def midTrim (V : Multiset ℝ) (d : ℕ) : ℝ := (kth V d + kth V (card V - 1 - d)) / 2

section OrderStatistics

variable {V : Multiset ℝ}

theorem kth_eq {i : ℕ} (hi : i < card V) : kth V i = (V.sort)[i]'(by simpa using hi) := by
  have hl : i < (V.sort).length := by simpa using hi
  simp [kth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

theorem kth_mono {i j : ℕ} (hij : i ≤ j) (hj : j < card V) : kth V i ≤ kth V j := by
  rw [kth_eq (by omega), kth_eq hj]
  rcases hij.lt_or_eq with h | rfl
  · exact List.pairwise_iff_getElem.mp (pairwise_sort V (· ≤ ·)) i j _ _ h
  · exact le_rfl

theorem card_filter_eq_countP (p : ℝ → Prop) [DecidablePred p] :
    card (V.filter p) = (V.sort).countP (fun x => decide (p x)) := by
  conv_lhs => rw [← sort_eq V (· ≤ ·)]
  rw [filter_coe, coe_card, List.countP_eq_length_filter]

/-- Fewer than `i + 1` values lie strictly below the `i`-th smallest one. -/
theorem card_filter_lt_kth {i : ℕ} (hi : i < card V) :
    card (V.filter (· < kth V i)) ≤ i := by
  rw [card_filter_eq_countP]
  set l := V.sort
  have hl : l.length = card V := length_sort _
  rw [← List.take_append_drop i l, List.countP_append]
  have h1 : (l.take i).countP (fun x => decide (x < kth V i)) ≤ i :=
    (List.countP_le_length).trans (by simp)
  have h2 : (l.drop i).countP (fun x => decide (x < kth V i)) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop]
    have := kth_mono (V := V) (i := i) (j := i + j) (by omega) (by simp at hj; omega)
    rw [kth_eq (i := i + j) (by simp at hj; omega)] at this
    simpa using this
  omega

/-- Fewer than `m - i` values lie strictly above the `i`-th smallest one. -/
theorem card_filter_kth_lt {i : ℕ} (hi : i < card V) :
    card (V.filter (kth V i < ·)) ≤ card V - 1 - i := by
  rw [card_filter_eq_countP]
  set l := V.sort
  have hl : l.length = card V := length_sort _
  rw [← List.take_append_drop (i + 1) l, List.countP_append]
  have h1 : (l.take (i + 1)).countP (fun x => decide (kth V i < x)) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take]
    have := kth_mono (V := V) (i := j) (j := i) (by simp at hj; omega) hi
    rw [kth_eq (i := j) (by simp at hj; omega)] at this
    simpa using this
  have h2 : (l.drop (i + 1)).countP (fun x => decide (kth V i < x)) ≤ card V - 1 - i :=
    (List.countP_le_length).trans (by simp; omega)
  omega

/-- If at most `i` values lie strictly below `x`, then the `i`-th smallest value is `≥ x`. -/
theorem le_kth_of_card_filter_lt {i : ℕ} (hi : i < card V) {x : ℝ}
    (h : card (V.filter (· < x)) ≤ i) : x ≤ kth V i := by
  by_contra hlt
  rw [not_le] at hlt
  rw [card_filter_eq_countP] at h
  set l := V.sort
  have hl : l.length = card V := length_sort _
  rw [← List.take_append_drop (i + 1) l, List.countP_append] at h
  have : (l.take (i + 1)).countP (fun y => decide (y < x)) = i + 1 := by
    rw [List.countP_eq_length.mpr, List.length_take]
    · omega
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_take]
    have := kth_mono (V := V) (i := j) (j := i) (by simp at hj; omega) hi
    rw [kth_eq (i := j) (by simp at hj; omega)] at this
    simpa using this.trans_lt hlt
  omega

/-- If at most `m - 1 - i` values lie strictly above `x`, then the `i`-th smallest value is
`≤ x`. -/
theorem kth_le_of_card_filter_gt {i : ℕ} (hi : i < card V) {x : ℝ}
    (h : card (V.filter (x < ·)) ≤ card V - 1 - i) : kth V i ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  rw [card_filter_eq_countP] at h
  set l := V.sort
  have hl : l.length = card V := length_sort _
  rw [← List.take_append_drop i l, List.countP_append] at h
  have : (l.drop i).countP (fun y => decide (x < y)) = card V - i := by
    rw [List.countP_eq_length.mpr, List.length_drop]
    · omega
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_drop]
    have := kth_mono (V := V) (i := i) (j := i + j) (by omega) (by simp at hj; omega)
    rw [kth_eq (i := i + j) (by simp at hj; omega)] at this
    simpa using hlt.trans_le this
  omega

end OrderStatistics

section Trim

variable {V : Multiset ℝ} {d : ℕ}

theorem mem_trim {y : ℝ} (hd : 2 * d < card V) :
    y ∈ trim V d ↔ ∃ j, d ≤ j ∧ j ≤ card V - 1 - d ∧ kth V j = y := by
  have hl : (V.sort).length = card V := length_sort _
  simp only [trim, mem_coe, List.mem_iff_getElem, List.length_take, List.length_drop, hl,
    List.getElem_take, List.getElem_drop]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨d + j, by omega, by omega, kth_eq (by omega)⟩
  · rintro ⟨j, hj1, hj2, rfl⟩
    exact ⟨j - d, by omega, by rw [kth_eq (by omega)]; congr 1; omega⟩

theorem card_trim (hd : 2 * d < card V) : card (trim V d) = card V - 2 * d := by
  simp [trim]; omega

/-- The minimum and the maximum of `T = trim V d` are `kth V d` and `kth V (m - 1 - d)`. -/
theorem kth_mem_trim (hd : 2 * d < card V) : kth V d ∈ trim V d :=
  (mem_trim hd).2 ⟨d, le_rfl, by omega, rfl⟩

theorem kth_top_mem_trim (hd : 2 * d < card V) : kth V (card V - 1 - d) ∈ trim V d :=
  (mem_trim hd).2 ⟨_, by omega, le_rfl, rfl⟩

theorem trim_bounds (hd : 2 * d < card V) {y : ℝ} (hy : y ∈ trim V d) :
    kth V d ≤ y ∧ y ≤ kth V (card V - 1 - d) := by
  obtain ⟨j, h1, h2, rfl⟩ := (mem_trim hd).1 hy
  exact ⟨kth_mono h1 (by omega), kth_mono h2 (by omega)⟩

/-- **Validity step** (Lemmas 3.2, 3.4): if `V = H + C` where all values of `H` lie in `[lo, hi]` and
`C` has at most `d` values, then the trimmed values lie in `[lo, hi]`. -/
theorem trim_validity {H C : Multiset ℝ} {lo hi : ℝ} (hH : ∀ y ∈ H, lo ≤ y ∧ y ≤ hi)
    (hC : card C ≤ d) (hd : 2 * d < card (H + C)) :
    lo ≤ kth (H + C) d ∧ kth (H + C) (card (H + C) - 1 - d) ≤ hi := by
  have hfH1 : H.filter (· < lo) = 0 := filter_eq_nil.mpr fun y hy => not_lt.mpr (hH y hy).1
  have hfH2 : H.filter (hi < ·) = 0 := filter_eq_nil.mpr fun y hy => not_lt.mpr (hH y hy).2
  constructor
  · refine le_kth_of_card_filter_lt (by omega) ?_
    rw [filter_add, hfH1, zero_add]
    exact (card_le_card (filter_le _ _)).trans hC
  · refine kth_le_of_card_filter_gt (by omega) ?_
    rw [filter_add, hfH2, zero_add]
    have := card_le_card (filter_le (hi < ·) C)
    omega

theorem midTrim_mem {lo hi : ℝ} (hd : 2 * d < card V)
    (h : ∀ y ∈ trim V d, lo ≤ y ∧ y ≤ hi) : lo ≤ midTrim V d ∧ midTrim V d ≤ hi := by
  have h1 := h _ (kth_mem_trim hd)
  have h2 := h _ (kth_top_mem_trim hd)
  unfold midTrim; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Trim

section Lemma36

variable {n ts ta : ℕ} {V V' : Multiset ℝ} {k k' : ℕ}

/-- Size bookkeeping: under the hypotheses of Lemma 3.6, `T` is non-empty. -/
theorem two_mul_max_lt (hta : ta ≤ ts) (hn : 2 * ts + ta < n) (hV : card V = n - ts + k)
    (hk : k ≤ ts) : 2 * max ta k < card V := by
  have := le_max_left ta k; have := le_max_right ta k
  rcases le_total ta k with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-- One half of **Lemma 3.7**: `min T ≤ max T'`. -/
theorem lemma_3_7_half (hta : ta ≤ ts) (hn : 2 * ts + ta < n) (hV : card V = n - ts + k)
    (hV' : card V' = n - ts + k') (hk : k ≤ ts) (hk' : k' ≤ ts) (hU : card (V ∪ V') ≤ n)
    (hI : n - ts ≤ card (V ∩ V')) :
    kth V (max ta k) ≤ kth V' (card V' - 1 - max ta k') := by
  set d := max ta k with hd
  set d' := max ta k' with hd'
  have h2d := two_mul_max_lt hta hn hV hk
  have h2d' := two_mul_max_lt hta hn hV' hk'
  set x := kth V d
  by_contra hlt
  rw [not_le] at hlt
  -- few values of `V` below `x`, few values of `V'` at or above `x`
  have hA : card (V.filter (· < x)) ≤ d := card_filter_lt_kth (by omega)
  have hB : card (V'.filter (x ≤ ·)) ≤ d' := by
    have := card_filter_kth_lt (V := V') (i := card V' - 1 - d') (by omega)
    refine le_trans (card_le_card (monotone_filter_right V' fun y hy => hlt.trans_le hy)) ?_
    omega
  -- counting in the union
  have hsplit : ∀ W : Multiset ℝ,
      card (W.filter (· < x)) + card (W.filter (x ≤ ·)) = card W := by
    intro W
    have := filter_add_not (· < x) W
    have h' : W.filter (fun y => ¬ y < x) = W.filter (x ≤ ·) := filter_congr fun y _ => not_lt
    rw [h'] at this
    rw [← card_add, this]
  have hU1 : card (V.filter (x ≤ ·)) ≤ card ((V ∪ V').filter (x ≤ ·)) :=
    card_le_card (filter_le_filter _ (le_union_left))
  have hU2 : card (V'.filter (· < x)) ≤ card ((V ∪ V').filter (· < x)) :=
    card_le_card (filter_le_filter _ (le_union_right))
  have hsum : card (V ∪ V') + card (V ∩ V') = card V + card V' := by
    rw [← card_add, union_add_inter, card_add]
  have e1 := hsplit V
  have e2 := hsplit V'
  have e3 := hsplit (V ∪ V')
  have := le_max_left ta k; have := le_max_right ta k
  have := le_max_left ta k'; have := le_max_right ta k'
  rcases le_total ta k with h1 | h1 <;> rcases le_total ta k' with h2 | h2
  · rw [max_eq_right h1] at hd; rw [max_eq_right h2] at hd'; omega
  · rw [max_eq_right h1] at hd; rw [max_eq_left h2] at hd'; omega
  · rw [max_eq_left h1] at hd; rw [max_eq_right h2] at hd'; omega
  · rw [max_eq_left h1] at hd; rw [max_eq_left h2] at hd'; omega

/-- **Lemma 3.7** (multiset form): the ranges of `T = trim V (max tₐ k)` and
`T' = trim V' (max tₐ k')` intersect. -/
theorem lemma_3_7 (hta : ta ≤ ts) (hn : 2 * ts + ta < n) (hV : card V = n - ts + k)
    (hV' : card V' = n - ts + k') (hk : k ≤ ts) (hk' : k' ≤ ts) (hU : card (V ∪ V') ≤ n)
    (hI : n - ts ≤ card (V ∩ V')) :
    kth V (max ta k) ≤ kth V' (card V' - 1 - max ta k') ∧
      kth V' (max ta k') ≤ kth V (card V - 1 - max ta k) :=
  ⟨lemma_3_7_half hta hn hV hV' hk hk' hU hI,
    lemma_3_7_half hta hn hV' hV hk' hk (by rwa [union_comm]) (by rwa [inter_comm])⟩

/-- **Lemma 3.6.** Let `0 ≤ tₐ ≤ tₛ`, `2 tₛ + tₐ < n`, `|V| = n - tₛ + k`, `|V'| = n - tₛ + k'`
(`k, k' ≤ tₛ`), `|V ∪ V'| ≤ n`, `|V ∩ V'| ≥ n - tₛ`. Let `T`, `T'` be obtained by discarding the
`max(tₐ, k)` (resp. `max(tₐ, k')`) lowest and highest values, `v`, `v'` the midpoints of their ranges.
If `T ∪ T' ⊆ [lo, hi]` then `|v - v'| ≤ (hi - lo) / 2`. -/
theorem lemma_3_6 (hta : ta ≤ ts) (hn : 2 * ts + ta < n) (hV : card V = n - ts + k)
    (hV' : card V' = n - ts + k') (hk : k ≤ ts) (hk' : k' ≤ ts) (hU : card (V ∪ V') ≤ n)
    (hI : n - ts ≤ card (V ∩ V')) {lo hi : ℝ}
    (hT : ∀ y ∈ trim V (max ta k), lo ≤ y ∧ y ≤ hi)
    (hT' : ∀ y ∈ trim V' (max ta k'), lo ≤ y ∧ y ≤ hi) :
    |midTrim V (max ta k) - midTrim V' (max ta k')| ≤ (hi - lo) / 2 := by
  have h2d := two_mul_max_lt hta hn hV hk
  have h2d' := two_mul_max_lt hta hn hV' hk'
  obtain ⟨i1, i2⟩ := lemma_3_7 hta hn hV hV' hk hk' hU hI
  have a := hT _ (kth_mem_trim h2d)
  have b := hT _ (kth_top_mem_trim h2d)
  have a' := hT' _ (kth_mem_trim h2d')
  have b' := hT' _ (kth_top_mem_trim h2d')
  unfold midTrim
  rw [abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2, a'.1, a'.2, b'.1, b'.2]

/-- **Lemma 3.6**, the paper's form: `|v - v'| ≤ length(T ∪ T') / 2`, where
`length(T ∪ T') = max(T ∪ T') - min(T ∪ T')`. -/
theorem lemma_3_6' (hta : ta ≤ ts) (hn : 2 * ts + ta < n) (hV : card V = n - ts + k)
    (hV' : card V' = n - ts + k') (hk : k ≤ ts) (hk' : k' ≤ ts) (hU : card (V ∪ V') ≤ n)
    (hI : n - ts ≤ card (V ∩ V')) :
    |midTrim V (max ta k) - midTrim V' (max ta k')| ≤
      (max (kth V (card V - 1 - max ta k)) (kth V' (card V' - 1 - max ta k')) -
        min (kth V (max ta k)) (kth V' (max ta k'))) / 2 := by
  have h2d := two_mul_max_lt hta hn hV hk
  have h2d' := two_mul_max_lt hta hn hV' hk'
  refine lemma_3_6 hta hn hV hV' hk hk' hU hI (fun y hy => ?_) (fun y hy => ?_)
  · have := trim_bounds h2d hy
    exact ⟨(min_le_left _ _).trans this.1, this.2.trans (le_max_left _ _)⟩
  · have := trim_bounds h2d' hy
    exact ⟨(min_le_right _ _).trans this.1, this.2.trans (le_max_right _ _)⟩

end Lemma36

/-! ### Bridge to CSLib's MSR trimming `IsTrim` -/

section Bridge

open Cslib.ApproxConsensus

variable {ι : Type*} [DecidableEq ι] {N Low Mid High : Finset ι} {r : ι → ℝ} {d : ℕ}

omit [DecidableEq ι] in
theorem card_filter_map_val (p : ℝ → Prop) [DecidablePred p] :
    card ((N.val.map r).filter p) = (N.filter fun x => p (r x)).card := by
  rw [filter_map, card_map]; rfl

/-- The `d`-th smallest value of `r` on `N` is the minimum of the kept values of any trimming. -/
theorem kth_eq_inf'_of_isTrim (h : IsTrim N d r Low Mid High) (hd : 2 * d < N.card) :
    kth (N.val.map r) d = Mid.inf' (h.mid_nonempty hd) r := by
  obtain ⟨m, hm, hmr⟩ := Mid.exists_mem_eq_inf' (h.mid_nonempty hd) r
  have hmin : ∀ x ∈ Mid, r m ≤ r x := fun x hx => by rw [← hmr]; exact Finset.inf'_le r hx
  have hcM := h.card_mid
  have hV : card (N.val.map r) = N.card := by simp
  rw [hmr]
  apply le_antisymm
  · -- values strictly above `r m` come from `Mid.erase m` and `High`
    refine kth_le_of_card_filter_gt (by omega) ?_
    rw [card_filter_map_val, hV]
    calc (N.filter fun x => r m < r x).card ≤ (Mid.erase m ∪ High).card :=
          Finset.card_le_card fun x hx => by
            simp only [Finset.mem_filter] at hx
            rw [Finset.mem_union, Finset.mem_erase]
            by_cases hxH : x ∈ High
            · exact Or.inr hxH
            · refine Or.inl ⟨fun hxm => (lt_irrefl (r m)) (hxm ▸ hx.2), h.mem_mid.mpr
                ⟨hx.1, fun hxL => (h.low_le_mid x hxL m hm).not_gt hx.2, hxH⟩⟩
      _ ≤ (Mid.erase m).card + High.card := Finset.card_union_le _ _
      _ ≤ N.card - 1 - d := by
          rw [Finset.card_erase_of_mem hm, h.card_high]; omega
  · -- values strictly below `r m` come from `Low`
    refine le_kth_of_card_filter_lt (by omega) ?_
    rw [card_filter_map_val, ← h.card_low]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_filter] at hx
    by_contra hxL
    by_cases hxH : x ∈ High
    · exact (h.mid_le_high m hm x hxH).not_gt hx.2
    · exact (hmin x (h.mem_mid.mpr ⟨hx.1, hxL, hxH⟩)).not_gt hx.2

/-- The `d`-th largest value of `r` on `N` is the maximum of the kept values of any trimming. -/
theorem kth_eq_sup'_of_isTrim (h : IsTrim N d r Low Mid High) (hd : 2 * d < N.card) :
    kth (N.val.map r) (N.card - 1 - d) = Mid.sup' (h.mid_nonempty hd) r := by
  obtain ⟨m, hm, hmr⟩ := Mid.exists_mem_eq_sup' (h.mid_nonempty hd) r
  have hmax : ∀ x ∈ Mid, r x ≤ r m := fun x hx => by rw [← hmr]; exact Finset.le_sup' r hx
  have hcM := h.card_mid
  have hV : card (N.val.map r) = N.card := by simp
  rw [hmr]
  apply le_antisymm
  · -- values strictly above `r m` come from `High`
    refine kth_le_of_card_filter_gt (by omega) ?_
    rw [card_filter_map_val, hV]
    calc (N.filter fun x => r m < r x).card ≤ High.card :=
          Finset.card_le_card fun x hx => by
            simp only [Finset.mem_filter] at hx
            by_contra hxH
            by_cases hxL : x ∈ Low
            · exact (h.low_le_mid x hxL m hm).not_gt hx.2
            · exact (hmax x (h.mem_mid.mpr ⟨hx.1, hxL, hxH⟩)).not_gt hx.2
      _ ≤ N.card - 1 - (N.card - 1 - d) := by rw [h.card_high]; omega
  · -- values strictly below `r m` come from `Low` and `Mid.erase m`
    refine le_kth_of_card_filter_lt (by omega) ?_
    rw [card_filter_map_val]
    calc (N.filter fun x => r x < r m).card ≤ (Low ∪ Mid.erase m).card :=
          Finset.card_le_card fun x hx => by
            simp only [Finset.mem_filter] at hx
            rw [Finset.mem_union, Finset.mem_erase]
            by_cases hxL : x ∈ Low
            · exact Or.inl hxL
            · refine Or.inr ⟨fun hxm => (lt_irrefl (r m)) (hxm ▸ hx.2), h.mem_mid.mpr
                ⟨hx.1, hxL, fun hxH => (h.mid_le_high m hm x hxH).not_gt hx.2⟩⟩
      _ ≤ Low.card + (Mid.erase m).card := Finset.card_union_le _ _
      _ ≤ N.card - 1 - d := by
          rw [Finset.card_erase_of_mem hm, h.card_low]
          have := Finset.card_pos.mpr (h.mid_nonempty hd); omega

/-- The new value of `Π_AA` (line 7) is the midpoint of the kept values of *any* MSR trimming
(`IsTrim`, ties broken arbitrarily) of the received values. -/
theorem midTrim_eq_of_isTrim (h : IsTrim N d r Low Mid High) (hd : 2 * d < N.card) :
    midTrim (N.val.map r) d =
      (Mid.inf' (h.mid_nonempty hd) r + Mid.sup' (h.mid_nonempty hd) r) / 2 := by
  have hV : card (N.val.map r) = N.card := by simp
  rw [midTrim, kth_eq_inf'_of_isTrim h hd, hV, kth_eq_sup'_of_isTrim h hd]

/-- `trim` keeps exactly the values of `Mid`, for any MSR trimming `(Low, Mid, High)`. -/
theorem trim_eq_of_isTrim (h : IsTrim N d r Low Mid High) :
    trim (N.val.map r) d = Mid.val.map r := by
  have hLM : Disjoint Low Mid :=
    Finset.disjoint_left.mpr fun x hx hx' => (h.mem_mid.mp hx').2.1 hx
  have hMH : Disjoint (Low.disjUnion Mid hLM) High := by
    rw [Finset.disjUnion_eq_union]
    exact Finset.disjoint_union_left.mpr
      ⟨h.disj, Finset.disjoint_left.mpr fun x hx hx' => (h.mem_mid.mp hx).2.2 hx'⟩
  have hN : N = (Low.disjUnion Mid hLM).disjUnion High hMH := by
    ext x
    simp only [Finset.disjUnion_eq_union, Finset.mem_union, h.mem_mid]
    have := @h.low_sub x; have := @h.high_sub x
    tauto
  -- the sorted values are the sorted `Low`, `Mid`, `High` values, concatenated
  have hsort : (N.val.map r).sort =
      (Low.val.map r).sort ++ ((Mid.val.map r).sort ++ (High.val.map r).sort) := by
    refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (pairwise_sort _ _) ?_ ?_
    · simp only [List.pairwise_append, List.mem_append, mem_sort, mem_map, Finset.mem_val]
      refine ⟨pairwise_sort _ _, ⟨pairwise_sort _ _, pairwise_sort _ _, ?_⟩, ?_⟩
      · rintro _ ⟨m, hm, rfl⟩ _ ⟨k, hk, rfl⟩; exact h.mid_le_high m hm k hk
      · rintro _ ⟨l, hl, rfl⟩ _ (⟨m, hm, rfl⟩ | ⟨k, hk, rfl⟩)
        · exact h.low_le_mid l hl m hm
        · exact h.low_le_high l hl k hk
    · rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.coe_add, sort_eq, sort_eq,
        sort_eq, sort_eq, ← map_add, ← map_add, hN]
      simp only [Finset.disjUnion_val, add_assoc]
  have hcM := h.card_mid
  have hNc : 2 * d ≤ N.card := by
    rw [hN, Finset.card_disjUnion, Finset.card_disjUnion, h.card_low, h.card_high]; omega
  rw [trim, hsort, List.drop_left' (by simp [h.card_low]),
    List.take_left' (by simp; omega), sort_eq]

end Bridge

end HybridApproxAgreement
