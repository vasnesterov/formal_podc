import Papers.PODC2020.NullMessagesByzantine.Protocol

/-!
# Counting lemmas: majorities, the Council, parities
-/

namespace Podc.NullMessagesByzantine

open Finset

variable {n : ℕ}

/-- If every entry outside a set `F` with `2 |F| < n` equals `v`, the majority is `v`. -/
lemma maj_eq_of_forall_notMem (f : Fin n → Bool) (F : Set (Fin n)) (v : Bool)
    (hF : 2 * F.ncard < n) (hv : ∀ i, i ∉ F → f i = v) : maj f = v := by
  classical
  have hcard : (F.toFinset).card = F.ncard := (Set.ncard_eq_toFinset_card' F).symm
  unfold maj
  cases v with
  | true =>
    have hsub : univ \ F.toFinset ⊆ univ.filter fun i => f i = true := by
      intro i hi; simp only [mem_sdiff, mem_univ, Set.mem_toFinset, true_and] at hi
      simp [hv i hi]
    have h1 := card_le_card hsub
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin] at h1
    simp only [decide_eq_true_eq]
    omega
  | false =>
    have hsub : (univ.filter fun i => f i = true) ⊆ F.toFinset := by
      intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
      by_contra h; rw [Set.mem_toFinset] at h; simp [hv i h] at hi
    have h1 := card_le_card hsub
    simp only [decide_eq_false_iff_not, not_lt]
    omega

/-- At most half of the entries differ from the majority. -/
lemma two_mul_card_ne_maj_le (f : Fin n → Bool) :
    2 * (univ.filter fun i => f i ≠ maj f).card ≤ n := by
  classical
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => f i = true)
  rw [card_univ, Fintype.card_fin] at hsum
  unfold maj
  by_cases hm : n < 2 * (univ.filter fun i => f i = true).card
  · have : (univ.filter fun i => f i ≠ decide (n < 2 * (univ.filter fun i => f i = true).card))
        = univ.filter fun i => ¬ f i = true := by
      ext i; simp [hm]
    rw [this]; omega
  · have : (univ.filter fun i => f i ≠ decide (n < 2 * (univ.filter fun i => f i = true).card))
        = univ.filter fun i => f i = true := by
      ext i; simp [hm]
    rw [this]; omega

/-- The Council has at most `t + 1` members. -/
lemma card_council_le (t : ℕ) : (univ.filter fun j : Fin n => council t j).card ≤ t + 1 := by
  have : (univ.filter fun j : Fin n => council t j).card ≤ (range (t + 1)).card := by
    apply card_le_card_of_injOn (fun j => j.val)
    · intro j hj
      have hj' := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).2
      simp only [council] at hj'
      simp; omega
    · intro a _ b _ h; exact Fin.ext h
  simpa using this

/-- If `t < n` and at most `t` processes are faulty, some council member is correct. -/
lemma exists_council_notMem (t : ℕ) (htn : t < n) (F : Set (Fin n)) (hF : F.ncard ≤ t) :
    ∃ j, council t j ∧ j ∉ F := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  let e : Fin (t + 1) ↪ Fin n := Fin.castLEEmb (by omega)
  have hsub : ((univ.map e : Finset (Fin n)) : Set (Fin n)) ⊆ F := by
    intro j hj
    simp only [coe_map, coe_univ, Set.image_univ, Set.mem_range] at hj
    obtain ⟨i, rfl⟩ := hj
    exact hcon _ (by simp [council, e]; omega)
  have := Set.ncard_le_ncard hsub (Set.toFinite F)
  rw [Set.ncard_coe_finset, card_map, card_univ, Fintype.card_fin] at this
  omega

lemma card_range_filter_odd (m : ℕ) : ((range m).filter fun j => j % 2 = 1).card = m / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

lemma card_range_filter_even (m : ℕ) :
    ((range m).filter fun j => ¬ j % 2 = 1).card = (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [ih]; omega
    · rw [card_insert_of_notMem (by simp), ih]; omega

/-- Council members of a given parity: at most `⌈(t + 1) / 2⌉`. -/
lemma two_mul_card_council_par_le (t : ℕ) (b : Bool) :
    2 * (univ.filter fun j : Fin n => council t j ∧ par j = b).card ≤ t + 2 := by
  have hinj : (univ.filter fun j : Fin n => council t j ∧ par j = b).card ≤
      ((range (t + 1)).filter fun j => (j % 2 == 1) = b).card := by
    apply card_le_card_of_injOn (fun j => j.val)
    · intro j hj
      have hj' := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).2
      simp only [council, par] at hj'
      simp; exact ⟨by omega, hj'.2⟩
    · intro a _ b _ h; exact Fin.ext h
  cases b with
  | true =>
    have : ((range (t + 1)).filter fun j => (j % 2 == 1) = true) =
        (range (t + 1)).filter fun j => j % 2 = 1 := by ext j; simp
    rw [this, card_range_filter_odd] at hinj; omega
  | false =>
    have : ((range (t + 1)).filter fun j => (j % 2 == 1) = false) =
        (range (t + 1)).filter fun j => ¬ j % 2 = 1 := by ext j; simp
    rw [this, card_range_filter_even] at hinj; omega

end Podc.NullMessagesByzantine
