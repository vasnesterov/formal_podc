import Papers.PODC2026.MultiKrumRobustness.Defs

/-!
# One-dimensional configurations and selection lemmas

Helpers for the lower-bound constructions of Section 3.2 and Appendix B of
Bareilles–Bouaziz–Fageot–El Mhamdi (PODC 2026):

* `block n lo hi` — the index block `{i : Fin n | lo ≤ i < hi}`, with its cardinality and sum
  splitting lemmas;
* configurations `x i = c i • e` on a line spanned by a unit vector `e`: their means, variances
  and nearest-neighbour sums reduce to real computations on `c`;
* `IsSelection.subset_of_score_lt` / `IsSelection.superset_of_score_lt`: if a group of indices has
  all its scores strictly below the scores of all other indices, every valid MultiKrum selection
  is contained in (resp. contains) the group, according to the group's size.
-/

open Finset

namespace Podc.MultiKrumRobustness

/-! ### Index blocks -/

/-- The index block `{i : Fin n | lo ≤ i < hi}`. -/
def block (n lo hi : ℕ) : Finset (Fin n) := univ.filter fun i => lo ≤ i.val ∧ i.val < hi

@[simp] lemma mem_block {n lo hi : ℕ} {i : Fin n} : i ∈ block n lo hi ↔ lo ≤ i.val ∧ i.val < hi := by
  simp [block]

lemma card_block {n lo hi : ℕ} (h : hi ≤ n) : (block n lo hi).card = hi - lo := by
  have : (block n lo hi).map Fin.valEmbedding = Ico lo hi := by
    ext k
    simp only [mem_map, mem_block, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨i, hi', rfl⟩; exact hi'
    · intro hk; exact ⟨⟨k, by omega⟩, hk, rfl⟩
  rw [← card_map, this, Nat.card_Ico]

lemma sum_block_split {M : Type*} [AddCommMonoid M] {n lo mid hi : ℕ} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) (g : Fin n → M) :
    ∑ i ∈ block n lo hi, g i = ∑ i ∈ block n lo mid, g i + ∑ i ∈ block n mid hi, g i := by
  rw [← sum_union]
  · congr 1; ext i; simp only [mem_block, mem_union]; omega
  · rw [disjoint_left]; intro i; simp only [mem_block]; omega

lemma sum_block_const {n lo hi : ℕ} (h : hi ≤ n) {g : Fin n → ℝ} {v : ℝ}
    (hg : ∀ i : Fin n, lo ≤ i.val → i.val < hi → g i = v) :
    ∑ i ∈ block n lo hi, g i = ((hi - lo : ℕ) : ℝ) * v := by
  rw [sum_congr rfl (fun i hi' => hg i (mem_block.1 hi').1 (mem_block.1 hi').2), sum_const,
    card_block h, nsmul_eq_mul]

/-! ### Constant groups -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

lemma mean_eq_of_const {x : Fin n → E} {A : Finset (Fin n)} {v : E} (hA : A.Nonempty)
    (h : ∀ i ∈ A, x i = v) : mean x A = v := by
  unfold mean
  have : (A.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.2 hA).ne'
  rw [sum_congr rfl h, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ this,
    one_smul]

lemma variance_eq_zero_of_const {x : Fin n → E} {A : Finset (Fin n)} {v : E} (hA : A.Nonempty)
    (h : ∀ i ∈ A, x i = v) : variance x A = 0 := by
  unfold variance
  rw [mean_eq_of_const hA h, sum_eq_zero (fun i hi => by rw [h i hi, sub_self, norm_zero]; ring),
    mul_zero]

/-! ### Configurations on a line -/

lemma norm_smul_sub_smul_sq {e : E} (he : ‖e‖ = 1) (a b : ℝ) :
    ‖a • e - b • e‖ ^ 2 = (a - b) ^ 2 := by
  rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]

lemma mean_line (c : Fin n → ℝ) (e : E) (A : Finset (Fin n)) :
    mean (fun i => c i • e) A = ((A.card : ℝ)⁻¹ * ∑ i ∈ A, c i) • e := by
  simp only [mean, ← sum_smul, smul_smul]

lemma variance_line {e : E} (he : ‖e‖ = 1) (c : Fin n → ℝ) (A : Finset (Fin n)) :
    variance (fun i => c i • e) A =
      (A.card : ℝ)⁻¹ * ∑ i ∈ A, (c i - (A.card : ℝ)⁻¹ * ∑ j ∈ A, c j) ^ 2 := by
  simp only [variance, mean_line, norm_smul_sub_smul_sq he]

lemma nearestSum_line_le {e : E} (he : ‖e‖ = 1) (c : Fin n → ℝ) {k : ℕ} (t : ℝ)
    {T : Finset (Fin n)} (hT : T.card = k) :
    nearestSum (fun i => c i • e) k (t • e) ≤ ∑ j ∈ T, (t - c j) ^ 2 := by
  have := nearestSum_le (fun i => c i • e) (t • e) hT
  simpa only [norm_smul_sub_smul_sq he] using this

lemma le_nearestSum_line {e : E} (he : ‖e‖ = 1) (c : Fin n → ℝ) {k r : ℕ} (hk : k ≤ n) (t : ℝ)
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hr : (univ.filter fun j => (t - c j) ^ 2 < c₀).card ≤ r) :
    ((k : ℝ) - r) * c₀ ≤ nearestSum (fun i => c i • e) k (t • e) :=
  le_nearestSum _ hk _ hc₀ (by simpa only [norm_smul_sub_smul_sq he] using hr)

/-- A unit vector exists in a nontrivial real inner product space. -/
lemma exists_unit (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] :
    ∃ e : E, ‖e‖ = 1 :=
  exists_norm_eq E zero_le_one

/-! ### Selections and strictly separated groups -/

omit [InnerProductSpace ℝ E] in
/-- If the indices of `G` have scores strictly below those of all other indices and `m ≤ |G|`,
every valid selection `S⋆_m` is contained in `G`. -/
lemma IsSelection.subset_of_score_lt {f m : ℕ} {x : Fin n → E} {S G : Finset (Fin n)}
    (hS : IsSelection f m x S) (hG : ∀ i ∈ G, ∀ j ∉ G, score f x (x i) < score f x (x j))
    (hm : m ≤ G.card) : S ⊆ G := by
  intro j hj
  by_contra hjG
  obtain ⟨i, hiG, hiS⟩ : ∃ i ∈ G, i ∉ S := by
    by_contra hcon
    push Not at hcon
    have := card_le_card (insert_subset hj hcon)
    rw [card_insert_of_notMem hjG, hS.1] at this
    omega
  exact absurd (hS.2 j hj i hiS) (not_le.2 (hG i hiG j hjG))

omit [InnerProductSpace ℝ E] in
/-- If the indices of `G` have scores strictly below those of all other indices and `|G| ≤ m`,
every valid selection `S⋆_m` contains `G`. -/
lemma IsSelection.superset_of_score_lt {f m : ℕ} {x : Fin n → E} {S G : Finset (Fin n)}
    (hS : IsSelection f m x S) (hG : ∀ i ∈ G, ∀ j ∉ G, score f x (x i) < score f x (x j))
    (hm : G.card ≤ m) : G ⊆ S := by
  intro i hiG
  by_contra hiS
  obtain ⟨j, hjS, hjG⟩ : ∃ j ∈ S, j ∉ G := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊆ G.erase i := fun j hj =>
      mem_erase.2 ⟨fun h => hiS (h ▸ hj), hcon j hj⟩
    have := card_le_card hsub
    rw [card_erase_of_mem hiG, hS.1] at this
    have : 0 < G.card := card_pos.2 ⟨i, hiG⟩
    omega
  exact absurd (hS.2 j hjS i hiS) (not_le.2 (hG i hiG j hjG))

end Podc.MultiKrumRobustness
