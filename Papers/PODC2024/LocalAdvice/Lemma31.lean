import Papers.PODC2024.LocalAdvice.Basic

/-!
# Lemma 31 (witnesses of type 23)

Near every node of a large component of `G_{2,3}` there is a node with two neighbours of colour 1,
or two adjacent nodes without a common neighbour of colour 1. We prove the statement along any
path of length `Δ` (`exists_witness_on_path`), which is what the encoding schema needs for the
second witness set `S'_v` (chosen inside a path `P_v`), and derive Lemma 31 from it.
-/

namespace Podc.LocalAdvice

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {φ : V → Fin 3}
  {Δ : ℕ}

/-- A *witness set* (the sets `S_v`, `S'_v` of the encoding schema, given by Lemma 31): either a
single node `w` of colour `≠ 1` with at least two neighbours of colour 1, or two adjacent nodes
`x, y` of `G_{2,3}` with no common neighbour of colour 1. -/
def IsWitness (G : SimpleGraph V) (φ : V → Fin 3) (S : Finset V) : Prop :=
  (∃ w, S = {w} ∧ φ w ≠ 0 ∧ 2 ≤ (nbr0 G φ w).card) ∨
  (∃ x y, S = {x, y} ∧ (H23 G φ).Adj x y ∧ Disjoint (nbr0 G φ x) (nbr0 G φ y))

lemma IsWitness.nonempty {S : Finset V} (h : IsWitness G φ S) : S.Nonempty := by
  rcases h with ⟨w, rfl, -⟩ | ⟨x, y, rfl, -⟩ <;> simp

lemma IsWitness.color_ne_zero {S : Finset V} (h : IsWitness G φ S) : ∀ z ∈ S, φ z ≠ 0 := by
  rcases h with ⟨w, rfl, hw, -⟩ | ⟨x, y, rfl, hxy, -⟩
  · simpa using hw
  · simp only [mem_insert, mem_singleton]
    rintro z (rfl | rfl)
    · exact hxy.2.1
    · exact hxy.2.2

omit [DecidableEq V] in
/-- A node of colour `≠ 1` in a greedy colouring has a neighbour of colour 1. -/
lemma IsGreedy.nbr0_nonempty (hφ : IsGreedy G φ) {v : V} (hv : φ v ≠ 0) :
    (nbr0 G φ v).Nonempty := by
  obtain ⟨w, hw, hw0⟩ := hφ.2 v 0 (Fin.pos_iff_ne_zero.2 hv)
  exact ⟨w, mem_nbr0.2 ⟨hw, hw0⟩⟩

/-- **Lemma 31 along a path.** Let `f 0, …, f Δ` be distinct nodes forming a path in `G_{2,3}`
(colours from a greedy colouring, degrees `≤ Δ`). Then some node `f i` has two neighbours of colour
1, or two consecutive nodes `f i, f (i+1)` have no common neighbour of colour 1. -/
theorem exists_witness_on_path [DecidableRel G.Adj] (hφ : IsGreedy G φ) (hΔ : ∀ v, G.degree v ≤ Δ) (f : ℕ → V)
    (h0 : φ (f 0) ≠ 0) (hadj : ∀ i < Δ, (H23 G φ).Adj (f i) (f (i + 1)))
    (hinj : ∀ i ≤ Δ, ∀ j ≤ Δ, f i = f j → i = j) :
    ∃ S, IsWitness G φ S ∧ ∀ z ∈ S, ∃ i ≤ Δ, z = f i := by
  classical
  have hcol : ∀ i ≤ Δ, φ (f i) ≠ 0 := by
    intro i hi
    rcases i with _ | i
    · exact h0
    · exact (hadj i (by omega)).2.2
  by_cases h2 : ∃ i ≤ Δ, 2 ≤ (nbr0 G φ (f i)).card
  · obtain ⟨i, hi, hcard⟩ := h2
    exact ⟨{f i}, Or.inl ⟨f i, rfl, hcol i hi, hcard⟩, fun z hz => ⟨i, hi, by simpa using hz⟩⟩
  push Not at h2
  -- every node of the path has exactly one neighbour of colour 1
  have huniq : ∀ i ≤ Δ, ∀ a ∈ nbr0 G φ (f i), ∀ b ∈ nbr0 G φ (f i), a = b := fun i hi =>
    Finset.card_le_one.1 (by have := h2 i hi; omega)
  obtain ⟨u, hu⟩ := hφ.nbr0_nonempty h0
  have hu' := mem_nbr0.1 hu
  -- some node `f j`, `1 ≤ j ≤ Δ`, is not adjacent to `u`
  have hex : ∃ j, 1 ≤ j ∧ j ≤ Δ ∧ ¬ G.Adj u (f j) := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.range (Δ + 1)).image f ⊆ G.neighborFinset u := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hz
      rw [mem_range] at hj
      rw [mem_neighborFinset]
      rcases j with _ | j
      · exact hu'.1.symm
      · exact hall (j + 1) (by omega) (by omega)
    have hcard : ((Finset.range (Δ + 1)).image f).card = Δ + 1 := by
      rw [card_image_of_injOn, card_range]
      intro a ha b hb hab
      simp only [coe_range, Set.mem_Iio] at ha hb
      exact hinj a (by omega) b (by omega) hab
    have := card_le_card hsub
    rw [hcard, card_neighborFinset_eq_degree] at this
    have := hΔ u
    omega
  let j := Nat.find hex
  have hj : 1 ≤ j ∧ j ≤ Δ ∧ ¬ G.Adj u (f j) := Nat.find_spec hex
  have hprev : G.Adj u (f (j - 1)) := by
    by_cases hj1 : j = 1
    · rw [hj1]; exact hu'.1.symm
    · by_contra hna
      exact Nat.find_min hex (show j - 1 < j by omega) ⟨by omega, by omega, hna⟩
  refine ⟨{f (j - 1), f j}, Or.inr ⟨f (j - 1), f j, rfl, ?_, ?_⟩, ?_⟩
  · have := hadj (j - 1) (by omega)
    rwa [show j - 1 + 1 = j by omega] at this
  · rw [Finset.disjoint_left]
    intro a ha hb
    have hau : a = u := huniq (j - 1) (by omega) a ha u
      (mem_nbr0.2 ⟨hprev.symm, hu'.2⟩)
    subst hau
    exact hj.2.2 (mem_nbr0.1 hb).1.symm
  · simp only [mem_insert, mem_singleton]
    rintro z (rfl | rfl)
    · exact ⟨j - 1, by omega, rfl⟩
    · exact ⟨j, hj.2.1, rfl⟩

/-- **Lemma 31** of [Balliu et al., arXiv:2405.04519]. Let `φ` be a greedy 3-colouring of a graph
of maximum degree `≤ Δ`, let `C` be a maximal connected component of `G_{2,3}` of diameter at
least `2Δ`, and let `v ∈ C`. Then (1) some `w ∈ C` with `dist_C(v, w) ≤ Δ` has at least two
neighbours of colour 1, or (2) there are two adjacent `x, y ∈ C` with `dist_C(v, x) ≤ Δ`,
`dist_C(v, y) ≤ Δ` and no common neighbour of colour 1. -/
theorem lemma_31 [DecidableRel G.Adj] (hφ : IsGreedy G φ) (hΔ : ∀ v, G.degree v ≤ Δ) {v : V} (hv : φ v ≠ 0)
    (hdiam : ∃ x y, (H23 G φ).Reachable v x ∧ (H23 G φ).Reachable v y ∧
      2 * Δ ≤ (H23 G φ).dist x y) :
    (∃ w, (H23 G φ).edist v w ≤ Δ ∧ 2 ≤ (nbr0 G φ w).card) ∨
    (∃ x y, (H23 G φ).Adj x y ∧ (H23 G φ).edist v x ≤ Δ ∧ (H23 G φ).edist v y ≤ Δ ∧
      Disjoint (nbr0 G φ x) (nbr0 G φ y)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hdiam
  have htri : (H23 G φ).dist x y ≤ (H23 G φ).dist x v + (H23 G φ).dist v y :=
    hx.symm.dist_triangle_left y
  have hc : (H23 G φ).dist x v = (H23 G φ).dist v x := dist_comm
  obtain ⟨f, hf0, hadj, hd⟩ : ∃ f : ℕ → V, f 0 = v ∧
      (∀ i < Δ, (H23 G φ).Adj (f i) (f (i + 1))) ∧ ∀ i ≤ Δ, (H23 G φ).edist v (f i) = i := by
    by_cases h1 : Δ ≤ (H23 G φ).dist v x
    · exact exists_geodesic_of_le _ hx h1
    · exact exists_geodesic_of_le _ hy (by omega)
  have hinj : ∀ i ≤ Δ, ∀ j ≤ Δ, f i = f j → i = j := by
    intro i hi j hj hij
    have := hd i hi
    rw [hij, hd j hj] at this
    exact_mod_cast this.symm
  obtain ⟨S, hS, hSf⟩ := exists_witness_on_path hφ hΔ f (hf0 ▸ hv) hadj hinj
  have hnear : ∀ z ∈ S, (H23 G φ).edist v z ≤ Δ := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := hSf z hz
    rw [hd i hi]; exact_mod_cast hi
  rcases hS with ⟨w, rfl, -, hw⟩ | ⟨a, b, rfl, hab, hdisj⟩
  · exact Or.inl ⟨w, hnear w (by simp), hw⟩
  · exact Or.inr ⟨a, b, hab, hnear a (by simp), hnear b (by simp), hdisj⟩

end Podc.LocalAdvice
