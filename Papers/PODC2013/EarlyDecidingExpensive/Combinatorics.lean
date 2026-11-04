import Mathlib

/-!
# Combinatorial and arithmetic lemmas (Dolev–Lenzen, PODC 2013)

* `exists_flip`: the "add nodes one by one" step of Lemmas 3.4, 3.5, 3.8 and 4.2.
* `exists_subset_card_sum_ge`: the `k` heaviest elements carry at least a `k / N` fraction of the
  total weight (proof of Lemma 3.8, inequality (1)).
* `exists_light_pair`: the counting step of Lemma 3.7.
* `sum_sq_bound`, `sum_identity_false`: the sum in the proof of Theorem 4.3.
-/

namespace Podc.EarlyDecidingExpensive

open Finset

-- CSLib candidate
/-- If `g` holds at `A ⊆ B` and fails at `B`, then adding the elements of `B \ A` one by one,
`g` flips from true to false at some step. -/
theorem exists_flip {α : Type*} [DecidableEq α] (g : Finset α → Prop) {A B : Finset α}
    (hAB : A ⊆ B) (hA : g A) (hB : ¬ g B) :
    ∃ W v, A ⊆ W ∧ W ⊆ B ∧ v ∈ B ∧ v ∉ W ∧ g W ∧ ¬ g (insert v W) := by
  obtain ⟨m, hm⟩ : ∃ m, (B \ A).card = m := ⟨_, rfl⟩
  induction m generalizing A with
  | zero =>
    exfalso
    have hBA : B ⊆ A := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hm)
    exact hB (le_antisymm hAB hBA ▸ hA)
  | succ m ih =>
    obtain ⟨v, hv⟩ : (B \ A).Nonempty := card_pos.mp (by omega)
    have hv' := mem_sdiff.mp hv
    by_cases hg : g (insert v A)
    · have hc : (B \ insert v A).card = m := by
        rw [sdiff_insert, card_erase_of_mem hv, hm]; rfl
      obtain ⟨W, w, h1, h2, h3, h4, h5, h6⟩ := ih (insert_subset hv'.1 hAB) hg hc
      exact ⟨W, w, (subset_insert _ _).trans h1, h2, h3, h4, h5, h6⟩
    · exact ⟨A, v, subset_rfl, hAB, hv'.1, hv'.2, hA, hg⟩

-- CSLib candidate
/-- Averaging: for `k ≤ |S|` some `k`-subset `T ⊆ S` satisfies `k · w(S) ≤ |S| · w(T)`. -/
theorem exists_subset_card_sum_ge {α : Type*} [DecidableEq α] (S : Finset α) (w : α → ℕ)
    {k : ℕ} (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧ k * ∑ x ∈ S, w x ≤ S.card * ∑ x ∈ T, w x := by
  obtain ⟨d, hd⟩ : ∃ d, S.card = k + d := ⟨S.card - k, by omega⟩
  induction d generalizing S with
  | zero => exact ⟨S, subset_rfl, by omega, by rw [hd]; simp⟩
  | succ d ih =>
    have hne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨m, hmS, hmin⟩ := exists_min_image S w hne
    have hc : (S.erase m).card = k + d := by rw [card_erase_of_mem hmS]; omega
    obtain ⟨T, hT, hTc, hTw⟩ := ih (S.erase m) (by omega) hc
    rw [hc] at hTw
    refine ⟨T, hT.trans (erase_subset _ _), hTc, ?_⟩
    have h1 : S.card • w m ≤ ∑ x ∈ S, w x := card_nsmul_le_sum S w (w m) (fun x hx => hmin x hx)
    rw [smul_eq_mul] at h1
    have h2 : ∑ x ∈ S, w x = w m + ∑ x ∈ S.erase m, w x := (add_sum_erase S w hmS).symm
    rw [h2] at h1 ⊢
    rw [hd] at h1 ⊢
    set a := w m
    set W := ∑ x ∈ S.erase m, w x
    set wT := ∑ x ∈ T, w x
    have h1' : (k + d) * a ≤ W := by nlinarith
    rcases Nat.eq_zero_or_pos (k + d) with he | he
    · have hk0 : k = 0 := by omega
      simp [hk0]
    · apply Nat.le_of_mul_le_mul_left _ he
      nlinarith [Nat.mul_le_mul_left k h1', Nat.mul_le_mul_left (k + d + 1) hTw]

/-- The counting step of Lemma 3.7. `S₀` (the non-faulty nodes, `N ≥ n - t/2` of them) and a
set `D` of directed pairs (who sends to whom in either execution) with `11 |D| < n t`, where
`3 t < n`: there are distinct `x, y ∈ S₀`, not adjacent in `D` in either direction, whose
in-degrees from `S₀` sum to at most `t / 2`. -/
theorem exists_light_pair {α : Type*} [DecidableEq α] (S₀ : Finset α) (D : Finset (α × α))
    {n t : ℕ} (hN : 2 * n ≤ 2 * S₀.card + t) (hnt : 3 * t < n) (hD : 11 * D.card < n * t) :
    ∃ x ∈ S₀, ∃ y ∈ S₀, x ≠ y ∧ (x, y) ∉ D ∧ (y, x) ∉ D ∧
      2 * ((S₀.filter fun p => (p, x) ∈ D).card + (S₀.filter fun p => (p, y) ∈ D).card) ≤ t := by
  classical
  set indeg : α → ℕ := fun x => (S₀.filter fun p => (p, x) ∈ D).card with hindeg
  set L := S₀.filter (fun x => 4 * indeg x ≤ t) with hL
  set H := S₀.filter (fun x => ¬ 4 * indeg x ≤ t) with hH
  have hLH : L.card + H.card = S₀.card := card_filter_add_card_filter_not _
  have hsum : ∑ x ∈ S₀, indeg x ≤ D.card := by
    have : ∑ x ∈ S₀, indeg x = ((S₀ ×ˢ S₀).filter (· ∈ D)).card := by
      rw [card_filter, sum_product_right]
      simp only [hindeg, card_filter]
    rw [this]
    exact card_le_card (fun q hq => (mem_filter.mp hq).2)
  have hHt : t * H.card ≤ 4 * D.card := by
    have h1 : H.card • t ≤ ∑ x ∈ H, 4 * indeg x :=
      card_nsmul_le_sum H _ t (fun x hx => by have := (mem_filter.mp hx).2; omega)
    have h2 : ∑ x ∈ H, 4 * indeg x ≤ 4 * ∑ x ∈ S₀, indeg x := by
      rw [mul_sum]; exact sum_le_sum_of_subset (filter_subset _ _)
    simp only [smul_eq_mul] at h1
    linarith [mul_comm t H.card]
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; simp at hD
    · exact h
  have h11 : 11 * H.card < 4 * n := by
    have : t * (11 * H.card) < t * (4 * n) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hl : 31 * n < 66 * L.card := by omega
  by_contra hcon
  have hsub : L.offDiag ⊆ D ∪ D.image Prod.swap := by
    intro q hq
    obtain ⟨x, y⟩ := q
    rw [mem_offDiag] at hq
    obtain ⟨hx, hy, hxy⟩ := hq
    rw [mem_filter] at hx hy
    by_contra hq'
    rw [mem_union, not_or] at hq'
    apply hcon
    refine ⟨x, hx.1, y, hy.1, hxy, hq'.1, ?_, ?_⟩
    · intro h; exact hq'.2 (mem_image.mpr ⟨(y, x), h, rfl⟩)
    · have hx2 : 4 * (S₀.filter fun p => (p, x) ∈ D).card ≤ t := hx.2
      have hy2 : 4 * (S₀.filter fun p => (p, y) ∈ D).card ≤ t := hy.2
      omega
  have hcard := card_le_card hsub
  rw [offDiag_card] at hcard
  have h2 : L.card * L.card - L.card ≤ 2 * D.card := by
    have := card_union_le D (D.image Prod.swap)
    have := card_image_le (s := D) (f := Prod.swap)
    omega
  have h3 : L.card * L.card ≤ 2 * D.card + L.card := Nat.sub_le_iff_le_add.mp h2
  nlinarith

/-- The sum of the proof of Theorem 4.3 is at least `n f (n - f) + f³/3 - 3 n f`. -/
theorem sum_sq_bound (n f : ℕ) (hf : f + 2 ≤ n) :
    6 * (n : ℤ) ^ 2 * f - 6 * n * f ^ 2 + 2 * (f : ℤ) ^ 3 - 18 * n * f ≤
      6 * ((∑ i ∈ Icc 1 f, (n - i - 1) ^ 2 : ℕ) : ℤ) := by
  have key : ∀ f : ℕ, f + 1 ≤ n → 6 * ((∑ i ∈ Icc 1 f, (n - i - 1) ^ 2 : ℕ) : ℤ) =
      6 * (n : ℤ) ^ 2 * f - 6 * n * f ^ 2 + 2 * (f : ℤ) ^ 3 - 18 * n * f + 9 * f ^ 2 + 13 * f := by
    intro f
    induction f with
    | zero => intro _; simp
    | succ f ih =>
      intro hf
      rw [sum_Icc_succ_top (by omega), Nat.cast_add, mul_add, ih (by omega)]
      have : ((n - (f + 1) - 1 : ℕ) : ℤ) = n - f - 2 := by omega
      push_cast [this]
      ring
  rw [key f (by omega)]
  nlinarith [sq_nonneg (f : ℤ), (Nat.cast_nonneg f : (0 : ℤ) ≤ f)]

/-- The closed form written in the proof of Theorem 4.3,
`∑_{i=1}^f (n-i-1)² = (n-2)(n-1)(2n-3)/6 - (n-f-3)(n-f-2)(2(n-f)-5)/6`, is off by the term
`(n-f-2)²`: for `n = 5`, `f = 1` the left side is `9` and the right side is `13`. -/
theorem sum_identity_false :
    ¬ ∀ n f : ℕ, f + 3 ≤ n →
      ((∑ i ∈ Icc 1 f, (n - i - 1) ^ 2 : ℕ) : ℚ) =
        ((n : ℚ) - 2) * (n - 1) * (2 * n - 3) / 6 -
          ((n : ℚ) - f - 3) * (n - f - 2) * (2 * (n - f) - 5) / 6 := by
  intro h
  have := h 5 1 (by norm_num)
  norm_num at this

end Podc.EarlyDecidingExpensive
