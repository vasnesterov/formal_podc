import Papers.PODC2011.AtMostOnceEffectiveness.Algorithm

/-!
# Ranks in finite sets of natural numbers (Definition 2.3)

`below S x = #{y ∈ S | y < x}`, so the rank of `x ∈ S` is `below S x + 1`.
-/

namespace Podc.AtMostOnceEffectiveness

/-- Number of elements of `S` below `x` (the rank of `x` in `S` is `below S x + 1`). -/
def below (S : Finset ℕ) (x : ℕ) : ℕ := (S.filter (· < x)).card

lemma setOf_mem_finite (S : Finset ℕ) : (Set.ofPred (· ∈ S)).Finite := S.finite_toSet

lemma toFinset_setOf_mem (S : Finset ℕ) : (setOf_mem_finite S).toFinset = S := by
  ext x; simp [Set.ofPred]

lemma count_mem_eq_below (S : Finset ℕ) (x : ℕ) : Nat.count (· ∈ S) x = below S x := by
  rw [Nat.count_eq_card_filter_range]
  unfold below
  congr 1
  ext y; simp [and_comm]

lemma rank_mem {S : Finset ℕ} (h : S.Nonempty) (k : ℕ) : rank S k ∈ S := by
  unfold rank
  have hc : 0 < S.card := Finset.card_pos.mpr h
  have := Nat.nth_mem_of_lt_card (p := (· ∈ S)) (n := min k S.card - 1) (setOf_mem_finite S)
    (by rw [toFinset_setOf_mem]; omega)
  exact this

/-- The element of rank `k` has exactly `k − 1` smaller elements. -/
lemma below_rank {S : Finset ℕ} {k : ℕ} (hk : 1 ≤ k) (hkS : k ≤ S.card) :
    below S (rank S k) = k - 1 := by
  unfold rank
  rw [← count_mem_eq_below, min_eq_left hkS]
  exact Nat.count_nth_of_lt_card_finite (setOf_mem_finite S) (by rw [toFinset_setOf_mem]; omega)

/-- An element with `k − 1` smaller elements has rank `k`. -/
lemma rank_eq_of_below {S : Finset ℕ} {k x : ℕ} (hx : x ∈ S) (hk : 1 ≤ k)
    (hb : below S x = k - 1) : rank S k = x := by
  have hkS : k ≤ S.card := by
    have : (S.filter (· < x)) ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun e => ?_⟩
      have : x ∈ S.filter (· < x) := by rw [e]; exact hx
      simp at this
    have := Finset.card_lt_card this
    unfold below at hb; omega
  unfold rank
  rw [min_eq_left hkS, ← hb, ← count_mem_eq_below]
  exact Nat.nth_count hx

lemma below_mono {S T : Finset ℕ} (h : S ⊆ T) (x : ℕ) : below S x ≤ below T x :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma below_lt_card {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) : below S x < S.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun e => ?_⟩
  have : x ∈ S.filter (· < x) := by rw [e]; exact hx
  simp at this

lemma below_strictMono {S : Finset ℕ} {x y : ℕ} (hx : x ∈ S) (hxy : x < y) :
    below S x < below S y := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun e => ?_⟩
  · intro z hz; simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hxy⟩
  · have : x ∈ S.filter (· < y) := by simp [hx, hxy]
    rw [← e] at this; simp at this

/-- Distinct elements have distinct ranks. -/
lemma eq_of_below_eq {S : Finset ℕ} {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (h : below S x = below S y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (below_strictMono hx hxy).ne
  · exact hxy
  · exact absurd h (below_strictMono hy hxy).ne'

end Podc.AtMostOnceEffectiveness
