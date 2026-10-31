import Papers.PODC2012.EquivocationPrice.Defs

/-!
# Projections of a 3-uniform hypergraph (Definition 4)

Jaffe, Moscibroda, Sen, *On the Price of Equivocation in Byzantine Agreement*, PODC 2012.

The projection of a hypergraph `E` by a vertex set `C` is the graph of pairs `{u, v}` outside
`C` such that `{u, v, w} ∈ E` for some `w ∈ C` (Definition 4). We represent it as the image of
the hyperedges meeting `C` in exactly one vertex under `e ↦ e \ C`.

* `proj_subset_compl`: the projection is a graph (2-element sets) on the complement of `C`.
* `pair_mem_proj`: a hyperedge `{x, y, z}` with `x, y ∉ C`, `z ∈ C` projects to `{x, y}`.
* `sum_card_proj_le`: the overcounting bound used in the proof of Theorem 5: summing the sizes
  of the projections over all `k`-sets `C`, each hyperedge is counted at most `3 · C(n-3, k-1)`
  times.
* `card_filter_inter_card_eq_one_le`: the general counting lemma behind it (`k`-subsets of `U`
  meeting a set `s` in exactly one point).
-/

namespace Podc.EquivocationPrice

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of `k`-subsets `X` of `U` meeting `s` in exactly one point is at most
`|s| · C(|U \ s|, k - 1)` (it is equal when `s ⊆ U` and `k ≥ 1`). -/
-- CSLib candidate
theorem card_filter_inter_card_eq_one_le (U s : Finset V) (k : ℕ) :
    ((U.powersetCard k).filter (fun X => (s ∩ X).card = 1)).card ≤
      s.card * (U \ s).card.choose (k - 1) := by
  have hsub : (U.powersetCard k).filter (fun X => (s ∩ X).card = 1) ⊆
      s.biUnion (fun a => ((U \ s).powersetCard (k - 1)).image (insert a)) := by
    intro X hX
    rw [mem_filter, mem_powersetCard] at hX
    obtain ⟨⟨hXU, hXk⟩, h1⟩ := hX
    obtain ⟨a, ha⟩ := card_eq_one.mp h1
    have haX : a ∈ s ∩ X := ha ▸ mem_singleton_self a
    rw [mem_inter] at haX
    rw [mem_biUnion]
    refine ⟨a, haX.1, ?_⟩
    rw [mem_image]
    refine ⟨X.erase a, ?_, insert_erase haX.2⟩
    rw [mem_powersetCard]
    refine ⟨?_, by rw [card_erase_of_mem haX.2, hXk]⟩
    intro x hx
    rw [mem_erase] at hx
    rw [mem_sdiff]
    refine ⟨hXU hx.2, fun hxs => hx.1 ?_⟩
    have : x ∈ s ∩ X := mem_inter.mpr ⟨hxs, hx.2⟩
    rw [ha] at this
    exact mem_singleton.mp this
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ a ∈ s, (((U \ s).powersetCard (k - 1)).image (insert a)).card := card_biUnion_le
    _ ≤ ∑ _a ∈ s, (U \ s).card.choose (k - 1) := by
        gcongr with a
        exact card_image_le.trans (card_powersetCard _ _).le
    _ = _ := by rw [sum_const, smul_eq_mul]

/-- **Definition 4** of [JMS12]: the projection of `E` by `C`: the pairs `{u, v}` outside `C`
such that `{u, v, w} ∈ E` for some `w ∈ C`. -/
def proj (E : Finset (Finset V)) (C : Finset V) : Finset (Finset V) :=
  (E.filter (fun e => (e ∩ C).card = 1)).image (fun e => e \ C)

variable [Fintype V] {E : Finset (Finset V)} {C : Finset V}

/-- The projection of a 3-uniform hypergraph by `C` is a graph on the complement of `C`. -/
theorem proj_subset_compl (hE : Uniform3 E) :
    ∀ f ∈ proj E C, f.card = 2 ∧ f ⊆ Finset.univ \ C := by
  intro f hf
  simp only [proj, mem_image, mem_filter] at hf
  obtain ⟨e, ⟨he, h1⟩, rfl⟩ := hf
  refine ⟨?_, fun x hx => by simp_all⟩
  have h3 := hE e he
  have := card_sdiff_add_card_inter e C
  omega

omit [Fintype V] in
/-- A hyperedge `{x, y, z}` with `x, y ∉ C` and `z ∈ C` projects to the edge `{x, y}`. -/
theorem pair_mem_proj {x y z : V} (hx : x ∉ C) (hy : y ∉ C) (hz : z ∈ C) (hxy : x ≠ y)
    (he : ({x, y, z} : Finset V) ∈ E) : ({x, y} : Finset V) ∈ proj E C := by
  have hzx : z ≠ x := fun h => hx (h ▸ hz)
  have hzy : z ≠ y := fun h => hy (h ▸ hz)
  have hint : ({x, y, z} : Finset V) ∩ C = {z} := by
    ext w
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hw⟩
      · exact absurd hw hx
      · exact absurd hw hy
      · rfl
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), hz⟩
  have hdiff : ({x, y, z} : Finset V) \ C = {x, y} := by
    ext w
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hw⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hz hw
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hx⟩
      · exact ⟨Or.inr (Or.inl rfl), hy⟩
  simp only [proj, mem_image, mem_filter]
  exact ⟨_, ⟨he, by rw [hint, card_singleton]⟩, hdiff⟩

/-- Overcounting bound from the proof of Theorem 5 of [JMS12]: summing `|proj E C|` over all
`k`-sets `C`, each hyperedge is counted at most `3 · C(n-3, k-1)` times. -/
theorem sum_card_proj_le (hE : Uniform3 E) (k : ℕ) :
    ∑ C ∈ (Finset.univ : Finset V).powersetCard k, (proj E C).card ≤
      3 * (Fintype.card V - 3).choose (k - 1) * E.card := by
  calc ∑ C ∈ (Finset.univ : Finset V).powersetCard k, (proj E C).card
      ≤ ∑ C ∈ (Finset.univ : Finset V).powersetCard k,
          (E.bipartiteAbove (fun (C e : Finset V) => (e ∩ C).card = 1) C).card := by
        refine sum_le_sum fun C _ => ?_
        exact card_image_le
    _ = ∑ e ∈ E, (((Finset.univ : Finset V).powersetCard k).bipartiteBelow
          (fun (C e : Finset V) => (e ∩ C).card = 1) e).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
    _ ≤ ∑ _e ∈ E, 3 * (Fintype.card V - 3).choose (k - 1) := by
        gcongr with e he
        have h := card_filter_inter_card_eq_one_le (Finset.univ : Finset V) e k
        have hc : (Finset.univ \ e).card = Fintype.card V - 3 := by
          rw [card_sdiff_of_subset (subset_univ _), card_univ, hE e he]
        rw [hc, hE e he] at h
        exact h
    _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]

end Podc.EquivocationPrice
