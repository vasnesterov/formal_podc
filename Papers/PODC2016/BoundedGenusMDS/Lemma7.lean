import Papers.PODC2016.BoundedGenusMDS.Setup

/-!
# Lemmas 7 and 9 (corrected): few edges between and inside stars

The `K_{t,3}` arguments of Lemmas 7 and 9 only work for vertices outside `C`: if the covering
vertex `c ∈ C_{m_j}` is itself a leaf of the other star (Lemma 7) or a leaf of the same star
(Lemma 9), the three branch sets of the would-be `K_{t,3}` are not disjoint. We therefore count
only leaves outside `C` with a neighbour outside `C` (`Setup.X`). With this change Lemma 7 holds
with the better bounds `2c(t-1)` and `4c(t-1)`, and Lemma 9 holds with the paper's bound
`2c(t-1)`. The original Lemma 7 is false (`Counterexamples.lean`).
-/

open Finset

namespace Podc.BoundedGenusMDS

open SimpleGraph (Depth1Model IsDepth1Minor Depth1DensityLE ExcludesKt3 depth1_of_cover_two)

open Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {c t : ℕ}

omit [Fintype V] in
lemma card_le_of_subset_biUnion {s T : Finset V} (f : V → Finset V) (hcov : s ⊆ T.biUnion f)
    (k : ℕ) (hk : ∀ x ∈ T, (f x).card ≤ k) : s.card ≤ T.card * k :=
  calc s.card ≤ (T.biUnion f).card := card_le_card hcov
    _ ≤ ∑ x ∈ T, (f x).card := card_biUnion_le
    _ ≤ ∑ _x ∈ T, k := sum_le_sum hk
    _ = T.card * k := by rw [sum_const, smul_eq_mul]

namespace Setup

variable (S : Setup G c)

/-- The `K_{t,3}` argument of Lemma 7: for `c' ∈ C_b`, `c' ≠ a`, fewer than `t` leaves of `b`
(outside `C`) adjacent to `c'` have a neighbour among the leaves of `a` outside `C`. The three
branch sets are `{b}`, `{c'}` and the star of `a` without `c'`. -/
lemma card_X_filter_lt (ht : ExcludesKt3 G t) {a b c' : V} (ha : a ∈ S.M) (hb : b ∈ S.M)
    (hab : a ≠ b) (hbD : b ∉ S.D) (hc' : c' ∈ S.Cm b) (hca : c' ≠ a) :
    ((S.X a b).filter (G.Adj c')).card < t := by
  have hc'C : c' ∈ S.C := S.mem_C_of hb hbD hc'
  have hbc : b ≠ c' := fun h => (S.Cm_spec b hb hbD).1 (h ▸ hc')
  refine ht.card_lt_two_singletons (a := b) (b := c') (z := a)
    (S := insert a ((S.leaves a).erase c')) hbc ?_ ?_ (mem_insert_self _ _) ?_ _ ?_ ?_
  · simp only [mem_insert, mem_erase, mem_leaves, not_or, not_and]
    exact ⟨Ne.symm hab, fun _ h => absurd hb h⟩
  · simp only [mem_insert, mem_erase, not_or, not_and]
    exact ⟨hca, fun h => absurd rfl h⟩
  · intro x hx hxa
    simp only [mem_insert, mem_erase, mem_leaves] at hx
    rcases hx with rfl | ⟨-, hxM, hxs⟩
    · exact absurd rfl hxa
    · have := S.adj_star hxM; rw [hxs] at this; exact this.symm
  · intro u hu
    simp only [X, mem_filter, mem_sdiff, mem_leaves] at hu
    obtain ⟨⟨⟨⟨huM, hus⟩, huC⟩, -⟩, hcu⟩ := hu
    refine ⟨fun h => huM (h ▸ hb), fun h => huC (h ▸ hc'C), ?_⟩
    simp only [mem_insert, mem_erase, mem_leaves, not_or, not_and]
    exact ⟨fun h => huM (h ▸ ha), fun _ _ h => hab (h ▸ hus)⟩
  · intro u hu
    simp only [X, mem_filter, mem_sdiff, mem_leaves] at hu
    obtain ⟨⟨⟨⟨huM, hus⟩, huC⟩, v, ⟨⟨hvM, hvs⟩, hvC⟩, huv⟩, hcu⟩ := hu
    refine ⟨by have := S.adj_star huM; rwa [hus] at this, hcu.symm, v, ?_, huv⟩
    simp only [mem_insert, mem_erase, mem_leaves]
    exact Or.inr ⟨fun h => hvC (h ▸ hc'C), hvM, hvs⟩

/-- **Lemma 7, items 1 and 2 (corrected).** If `ord a < ord b` and `b ∉ D`, then at most
`2c(t-1)` leaves of `b` outside `C` have a neighbour among the leaves of `a` outside `C`
(the paper: at most `2ct` leaves of `b` have a neighbour among the leaves of `a`, which is false,
see `lemma_7_2_false`). -/
theorem lemma_7_12 (ht : ExcludesKt3 G t) {a b : V} (ha : a ∈ S.M) (hb : b ∈ S.M)
    (hbD : b ∉ S.D) (hord : S.ord a < S.ord b) : (S.X a b).card ≤ 2 * c * (t - 1) := by
  have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ hord
  have hcov : S.X a b ⊆ (S.Cm b).biUnion fun c' => (S.X a b).filter (G.Adj c') := by
    intro u hu
    have hu' := hu
    simp only [X, mem_filter, mem_sdiff] at hu'
    obtain ⟨c', hc', hcu⟩ := S.exists_Cm_adj hb hbD hu'.1.1 hu'.1.2
    exact mem_biUnion.2 ⟨c', hc', mem_filter.2 ⟨hu, hcu⟩⟩
  refine (card_le_of_subset_biUnion _ hcov (t - 1) fun c' hc' => ?_).trans ?_
  · by_cases hca : c' = a
    · subst hca
      suffices (S.X c' b).filter (G.Adj c') = ∅ by rw [this]; simp
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      simp only [X, mem_filter, mem_sdiff, mem_leaves] at hu
      have := S.ord_star_le hu.1.1.1.1 ha hu.2.symm
      rw [hu.1.1.1.2] at this; omega
    · have := S.card_X_filter_lt ht ha hb hab hbD hc' hca; omega
  · exact Nat.mul_le_mul_right _ (S.Cm_spec b hb hbD).2.1

/-- **Lemma 7, item 3 (corrected).** If `ord b < ord a` and `a, b ∉ D`, then at most `4c(t-1)`
leaves of `b` outside `C` have a neighbour among the leaves of `a` outside `C`. -/
theorem lemma_7_3 (ht : ExcludesKt3 G t) {a b : V} (ha : a ∈ S.M) (hb : b ∈ S.M)
    (haD : a ∉ S.D) (hbD : b ∉ S.D) (hord : S.ord b < S.ord a) :
    (S.X a b).card ≤ 4 * c * (t - 1) := by
  have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ hord
  set Xa := (S.X a b).filter (G.Adj a) with hXa
  have hcov : S.X a b ⊆ ((S.Cm b).erase a).biUnion (fun c' => (S.X a b).filter (G.Adj c')) ∪ Xa := by
    intro u hu
    have hu' := hu
    simp only [X, mem_filter, mem_sdiff] at hu'
    obtain ⟨c', hc', hcu⟩ := S.exists_Cm_adj hb hbD hu'.1.1 hu'.1.2
    by_cases hca : c' = a
    · subst hca; exact mem_union_right _ (mem_filter.2 ⟨hu, hcu⟩)
    · exact mem_union_left _ (mem_biUnion.2 ⟨c', mem_erase.2 ⟨hca, hc'⟩, mem_filter.2 ⟨hu, hcu⟩⟩)
  have h1 : (((S.Cm b).erase a).biUnion fun c' => (S.X a b).filter (G.Adj c')).card
      ≤ 2 * c * (t - 1) := by
    refine (card_le_of_subset_biUnion _ subset_rfl (t - 1) fun c' hc' => ?_).trans ?_
    · rw [mem_erase] at hc'
      have := S.card_X_filter_lt ht ha hb hab hbD hc'.2 hc'.1; omega
    · exact Nat.mul_le_mul_right _ ((card_erase_le).trans (S.Cm_spec b hb hbD).2.1)
  -- the leaves of `b` adjacent to `a`: use the covering set `C_a` of the other side
  have hcovA : Xa ⊆ (S.Cm a).biUnion fun c'' =>
      Xa.filter fun u => ∃ v ∈ S.leaves a \ S.C, G.Adj u v ∧ G.Adj c'' v := by
    intro u hu
    have hu' := hu
    simp only [hXa, X, mem_filter, mem_sdiff] at hu'
    obtain ⟨⟨_, v, ⟨hva, hvC⟩, huv⟩, -⟩ := hu'
    obtain ⟨c'', hc'', hcv⟩ := S.exists_Cm_adj ha haD hva hvC
    exact mem_biUnion.2 ⟨c'', hc'', mem_filter.2 ⟨hu, v, mem_sdiff.2 ⟨hva, hvC⟩, huv, hcv⟩⟩
  have h2 : Xa.card ≤ 2 * c * (t - 1) := by
    refine (card_le_of_subset_biUnion _ hcovA (t - 1) fun c'' hc'' => ?_).trans
      (Nat.mul_le_mul_right _ (S.Cm_spec a ha haD).2.1)
    have hc''C : c'' ∈ S.C := S.mem_C_of ha haD hc''
    by_cases hcb : c'' = b
    · subst hcb
      suffices (Xa.filter fun u => ∃ v ∈ S.leaves a \ S.C, G.Adj u v ∧ G.Adj c'' v) = ∅ by
        rw [this]; simp
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro u hu
      simp only [mem_filter, mem_sdiff, mem_leaves] at hu
      obtain ⟨-, v, ⟨⟨hvM, hvs⟩, -⟩, -, hcv⟩ := hu
      have := S.ord_star_le hvM hb hcv.symm
      rw [hvs] at this; omega
    · have hac : a ≠ c'' := fun h => (S.Cm_spec a ha haD).1 (h ▸ hc'')
      suffices (Xa.filter fun u => ∃ v ∈ S.leaves a \ S.C, G.Adj u v ∧ G.Adj c'' v).card < t by
        omega
      refine ht.card_lt_two_singletons (a := b) (b := a) (z := c'')
        (S := insert c'' ((S.leaves a).filter (G.Adj c''))) (Ne.symm hab) ?_ ?_
        (mem_insert_self _ _) ?_ _ ?_ ?_
      · simp only [mem_insert, mem_filter, mem_leaves, not_or, not_and]
        exact ⟨Ne.symm hcb, fun h => absurd hb h.1⟩
      · simp only [mem_insert, mem_filter, mem_leaves, not_or, not_and]
        exact ⟨hac, fun h => absurd ha h.1⟩
      · intro x hx hxc
        simp only [mem_insert, mem_filter] at hx
        rcases hx with rfl | ⟨-, h⟩
        · exact absurd rfl hxc
        · exact h
      · intro u hu
        simp only [hXa, X, mem_filter, mem_sdiff, mem_leaves] at hu
        obtain ⟨⟨⟨⟨⟨huM, hus⟩, huC⟩, -⟩, -⟩, -⟩ := hu
        refine ⟨fun h => huM (h ▸ hb), fun h => huM (h ▸ ha), ?_⟩
        simp only [mem_insert, mem_filter, mem_leaves, not_or, not_and]
        exact ⟨fun h => huC (h ▸ hc''C), fun h _ => hab (h.2 ▸ hus)⟩
      · intro u hu
        simp only [hXa, X, mem_filter, mem_sdiff, mem_leaves] at hu
        obtain ⟨⟨⟨⟨⟨huM, hus⟩, -⟩, -⟩, hau⟩, v, ⟨⟨hvM, hvs⟩, -⟩, huv, hcv⟩ := hu
        refine ⟨by have := S.adj_star huM; rwa [hus] at this, hau.symm, v, ?_, huv⟩
        simp only [mem_insert, mem_filter, mem_leaves]
        exact Or.inr ⟨⟨hvM, hvs⟩, hcv⟩
  calc (S.X a b).card ≤ _ := card_le_card hcov
    _ ≤ _ + Xa.card := card_union_le _ _
    _ ≤ 2 * c * (t - 1) + 2 * c * (t - 1) := Nat.add_le_add h1 h2
    _ = 4 * c * (t - 1) := by ring

/-- **Lemma 9 (corrected).** For `m ∈ M \ D` and a leaf `x ∉ C` of `m`, at most `2c(t-1)` leaves
of `m` outside `C` are adjacent to `x`. (The paper counts all leaves of `m`, including those in
`C_m`, which the `K_{t,3}` argument does not cover.) -/
theorem lemma_9 (ht : ExcludesKt3 G t) {m x : V} (hm : m ∈ S.M) (hmD : m ∉ S.D)
    (hx : x ∈ S.leaves m) (hxC : x ∉ S.C) :
    ((S.leaves m \ S.C).filter (G.Adj x)).card ≤ 2 * c * (t - 1) := by
  have hxM : x ∉ S.M := (S.mem_leaves.1 hx).1
  have hcov : (S.leaves m \ S.C).filter (G.Adj x) ⊆ (S.Cm m).biUnion fun c' =>
      ((S.leaves m \ S.C).filter (G.Adj x)).filter (G.Adj c') := by
    intro u hu
    have hu' := hu
    simp only [mem_filter, mem_sdiff] at hu'
    obtain ⟨c', hc', hcu⟩ := S.exists_Cm_adj hm hmD hu'.1.1 hu'.1.2
    exact mem_biUnion.2 ⟨c', hc', mem_filter.2 ⟨hu, hcu⟩⟩
  refine (card_le_of_subset_biUnion _ hcov (t - 1) fun c' hc' => ?_).trans
    (Nat.mul_le_mul_right _ (S.Cm_spec m hm hmD).2.1)
  have hc'C : c' ∈ S.C := S.mem_C_of hm hmD hc'
  have hmc : m ≠ c' := fun h => (S.Cm_spec m hm hmD).1 (h ▸ hc')
  suffices (((S.leaves m \ S.C).filter (G.Adj x)).filter (G.Adj c')).card < t by omega
  refine ht.card_lt_two_singletons (a := m) (b := c') (z := x) (S := {x}) hmc ?_ ?_
    (mem_singleton_self _) ?_ _ ?_ ?_
  · rw [mem_singleton]; exact fun h => hxM (h ▸ hm)
  · rw [mem_singleton]; exact fun h => hxC (h ▸ hc'C)
  · intro y hy hyx; exact absurd (mem_singleton.1 hy) hyx
  · intro u hu
    simp only [mem_filter, mem_sdiff, mem_leaves] at hu
    obtain ⟨⟨⟨⟨huM, -⟩, huC⟩, hxu⟩, -⟩ := hu
    exact ⟨fun h => huM (h ▸ hm), fun h => huC (h ▸ hc'C), by
      rw [mem_singleton]; rintro rfl; exact G.irrefl hxu⟩
  · intro u hu
    simp only [mem_filter, mem_sdiff, mem_leaves] at hu
    obtain ⟨⟨⟨⟨huM, hus⟩, -⟩, hxu⟩, hcu⟩ := hu
    exact ⟨by have := S.adj_star huM; rwa [hus] at this, hcu.symm, x, mem_singleton_self _,
      hxu.symm⟩

end Setup

end Podc.BoundedGenusMDS
