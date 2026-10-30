import Papers.PODC2016.BoundedGenusMDS.Lemma7

/-!
# Corollary 8, Lemmas 10–12 (corrected proofs; Lemma 12 with the paper's constant)

* `Setup.corollary_8`: `|Y| + |YD| ≤ 6c²(t-1)|M|` for the corrected `Y` (vertices outside `C`
  seeing another star outside `C`); the paper's bound `|Y| ≤ 6c²t|M|` for its own `Y` is false.
* `Setup.lemma_10`: `|Z| ≤ |M ∪ C|`.
* `Setup.lemma_11`: the sources inside stars whose dominator is a leaf of the same star outside
  `C ∪ Y ∪ Z` number at most `(2(t-1)+4)c|M|` (the paper does not exclude `C`; then the lemma is
  false).
* `lemma_12`: the modified algorithm is a `(6c²t + (2t+5)c + 4)`-approximation.
-/

open Finset

namespace Podc.BoundedGenusMDS

open SimpleGraph (Depth1Model IsDepth1Minor Depth1DensityLE ExcludesKt3 depth1_of_cover_two)

open Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {c t : ℕ}

namespace Setup

variable (S : Setup G c)

/-- The branch set of `m ∈ M` in the depth-1 minor `H` of Section 3 (the star `G_m`). -/
noncomputable def br (m : V) : Finset V := insert m (S.leaves m)

lemma br_disjoint {a b : V} (ha : a ∈ S.M) (hb : b ∈ S.M) (hab : a ≠ b) :
    Disjoint (S.br a) (S.br b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  simp only [br, mem_insert, mem_leaves] at hxa hxb
  rcases hxa with rfl | ⟨hxM, hxs⟩ <;> rcases hxb with h | ⟨hxM', hxs'⟩
  · exact hab h
  · exact hxM' ha
  · exact hxM (h ▸ hb)
  · exact hab (hxs ▸ hxs')

/-- Ordered pairs of distinct touching stars, i.e. (oriented) edges of the depth-1 minor `H`. -/
noncomputable def Pt : Finset (V × V) :=
  (S.M ×ˢ S.M).filter fun p => p.1 ≠ p.2 ∧ ∃ x ∈ S.br p.1, ∃ y ∈ S.br p.2, G.Adj x y

lemma card_Pt_le (hc : Depth1DensityLE G c) : S.Pt.card ≤ 2 * c * S.M.card := by
  refine hc.card_le_of_touch S.M id S.br (fun m _ => mem_insert_self _ _) ?_
    (fun a ha b hb hab => S.br_disjoint ha hb hab) S.Pt fun p hp => ?_
  · intro m _ x hx hxm
    simp only [br, mem_insert, mem_leaves] at hx
    rcases hx with rfl | ⟨hxM, hxs⟩
    · exact absurd rfl hxm
    · have := S.adj_star hxM; rw [hxs] at this; exact this.symm
  · simp only [Pt, mem_filter, mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩

lemma X_subset_leaves (a b : V) : S.X a b ⊆ S.leaves b := fun u hu => by
  simp only [X, mem_filter, mem_sdiff] at hu; exact hu.1.1

lemma mem_Pt_of_mem_X {a b u : V} (ha : a ∈ S.M) (hb : b ∈ S.M) (hab : a ≠ b)
    (hu : u ∈ S.X a b) : (a, b) ∈ S.Pt := by
  simp only [X, mem_filter, mem_sdiff] at hu
  obtain ⟨⟨hub, -⟩, v, ⟨hva, -⟩, huv⟩ := hu
  simp only [Pt, mem_filter, mem_product]
  exact ⟨⟨ha, hb⟩, hab, v, mem_insert_of_mem hva, u, mem_insert_of_mem hub, huv.symm⟩

/-- Weight of an oriented edge `(a, b)` of `H` in the count of `Y` and `YD`. -/
noncomputable def wt (p : V × V) : ℕ :=
  (if p.2 ∉ S.D then (S.X p.1 p.2).card else 0) +
    (if p.1 ∈ S.D ∧ p.2 ∉ S.D then (S.X p.1 p.2).card else 0)

lemma wt_pair_le (ht : ExcludesKt3 G t) {a b : V} (ha : a ∈ S.M) (hb : b ∈ S.M)
    (hord : S.ord a < S.ord b) : S.wt (a, b) + S.wt (b, a) ≤ 6 * c * (t - 1) := by
  simp only [wt]
  by_cases hbD : b ∈ S.D
  · have haD : a ∈ S.D := by
      by_contra haD; have := S.ord_D b hb a ha hbD haD; omega
    simp [hbD, haD]
  · have h1 := S.lemma_7_12 ht ha hb hbD hord
    by_cases haD : a ∈ S.D
    · simp only [hbD, not_false_eq_true, ite_true, haD, and_self, not_true_eq_false, ite_false,
        add_zero]
      nlinarith
    · have h2 := S.lemma_7_3 ht hb ha hbD haD hord
      simp only [hbD, not_false_eq_true, ite_true, haD, ite_false, add_zero, and_true]
      nlinarith

/-- **Corollary 8 (corrected).** `|Y| + |YD| ≤ 6c²(t-1)|M|`: every edge of the depth-1 minor `H`
(at most `c|M|` of them) accounts for at most `6c(t-1)` vertices. -/
theorem corollary_8 (hc : Depth1DensityLE G c) (ht : ExcludesKt3 G t) :
    S.Y.card + S.YD.card ≤ 6 * c ^ 2 * (t - 1) * S.M.card := by
  have hY : S.Y.card ≤ ∑ p ∈ S.Pt, (if p.2 ∉ S.D then (S.X p.1 p.2).card else 0) := by
    calc S.Y.card ≤ (S.Pt.biUnion fun p => if p.2 ∉ S.D then S.X p.1 p.2 else ∅).card := by
          refine card_le_card fun u hu => ?_
          simp only [Y, mem_filter, mem_univ, true_and] at hu
          obtain ⟨huM, huC, huD, v, hvM, hvC, hvu, huv⟩ := hu
          have hX : u ∈ S.X (S.star v) (S.star u) :=
            mem_filter.2 ⟨mem_sdiff.2 ⟨S.mem_leaves.2 ⟨huM, rfl⟩, huC⟩, v,
              mem_sdiff.2 ⟨S.mem_leaves.2 ⟨hvM, rfl⟩, hvC⟩, huv⟩
          refine mem_biUnion.2 ⟨(S.star v, S.star u),
            S.mem_Pt_of_mem_X (S.star_mem hvM) (S.star_mem huM) hvu hX, ?_⟩
          simp only [huD, not_false_eq_true, ite_true]; exact hX
      _ ≤ _ := by
          refine card_biUnion_le.trans (sum_le_sum fun p _ => ?_)
          split_ifs <;> simp
  have hYD : S.YD.card ≤ ∑ p ∈ S.Pt,
      (if p.1 ∈ S.D ∧ p.2 ∉ S.D then (S.X p.1 p.2).card else 0) := by
    calc S.YD.card ≤ (S.Pt.biUnion fun p =>
            if p.1 ∈ S.D ∧ p.2 ∉ S.D then S.X p.1 p.2 else ∅).card := by
          refine card_le_card fun u hu => ?_
          simp only [YD, mem_filter, mem_univ, true_and] at hu
          obtain ⟨huM, huC, huD, v, hvM, hvC, hvD, huv⟩ := hu
          have hvu : S.star v ≠ S.star u := fun h => huD (h ▸ hvD)
          have hX : u ∈ S.X (S.star v) (S.star u) :=
            mem_filter.2 ⟨mem_sdiff.2 ⟨S.mem_leaves.2 ⟨huM, rfl⟩, huC⟩, v,
              mem_sdiff.2 ⟨S.mem_leaves.2 ⟨hvM, rfl⟩, hvC⟩, huv⟩
          refine mem_biUnion.2 ⟨(S.star v, S.star u),
            S.mem_Pt_of_mem_X (S.star_mem hvM) (S.star_mem huM) hvu hX, ?_⟩
          simp only [hvD, huD, not_false_eq_true, and_self, ite_true]; exact hX
      _ ≤ _ := by
          refine card_biUnion_le.trans (sum_le_sum fun p _ => ?_)
          split_ifs <;> simp
  have hsum : S.Y.card + S.YD.card ≤ ∑ p ∈ S.Pt, S.wt p := by
    have : ∑ p ∈ S.Pt, S.wt p = (∑ p ∈ S.Pt, (if p.2 ∉ S.D then (S.X p.1 p.2).card else 0)) +
        ∑ p ∈ S.Pt, (if p.1 ∈ S.D ∧ p.2 ∉ S.D then (S.X p.1 p.2).card else 0) := by
      rw [← sum_add_distrib]; rfl
    omega
  -- split the oriented edges by the order of their endpoints
  set Plt := S.Pt.filter fun p => S.ord p.1 < S.ord p.2 with hPlt
  set Pgt := S.Pt.filter fun p => ¬ S.ord p.1 < S.ord p.2 with hPgt
  have hPt_mem : ∀ p ∈ S.Pt, p.1 ∈ S.M ∧ p.2 ∈ S.M ∧ p.1 ≠ p.2 := fun p hp => by
    simp only [Pt, mem_filter, mem_product] at hp; exact ⟨hp.1.1, hp.1.2, hp.2.1⟩
  have hswap : ∀ p ∈ S.Pt, p.swap ∈ S.Pt := by
    rintro ⟨a, b⟩ hp
    simp only [Pt, mem_filter, mem_product, Prod.swap_prod_mk] at hp ⊢
    obtain ⟨⟨ha, hb⟩, hne, x, hx, y, hy, hxy⟩ := hp
    exact ⟨⟨hb, ha⟩, Ne.symm hne, y, hy, x, hx, hxy.symm⟩
  have hgt_sum : ∑ p ∈ Pgt, S.wt p = ∑ p ∈ Plt, S.wt p.swap := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ (by simp) (by simp) (by simp)
    · intro p hp
      simp only [hPgt, hPlt, mem_filter] at hp ⊢
      refine ⟨hswap p hp.1, ?_⟩
      obtain ⟨h1, h2, hne⟩ := hPt_mem p hp.1
      have : S.ord p.1 ≠ S.ord p.2 := fun h => hne (S.ord_inj _ h1 _ h2 h)
      simp only [Prod.fst_swap, Prod.snd_swap]; omega
    · intro p hp
      simp only [hPgt, hPlt, mem_filter] at hp ⊢
      refine ⟨hswap p hp.1, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]; omega
  have hgt_card : Pgt.card = Plt.card := by
    have := hgt_sum
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ (fun p _ => Prod.swap_swap p)
      (fun p _ => Prod.swap_swap p)
    · intro p hp
      simp only [hPgt, hPlt, mem_coe, mem_filter] at hp ⊢
      refine ⟨hswap p hp.1, ?_⟩
      obtain ⟨h1, h2, hne⟩ := hPt_mem p hp.1
      have : S.ord p.1 ≠ S.ord p.2 := fun h => hne (S.ord_inj _ h1 _ h2 h)
      simp only [Prod.fst_swap, Prod.snd_swap]; omega
    · intro p hp
      simp only [hPgt, hPlt, mem_coe, mem_filter] at hp ⊢
      refine ⟨hswap p hp.1, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]; omega
  have hcard_split : Plt.card + Pgt.card = S.Pt.card := card_filter_add_card_filter_not _
  have hPt := S.card_Pt_le hc
  have hlt_card : Plt.card ≤ c * S.M.card := by nlinarith
  have hwsplit : ∑ p ∈ S.Pt, S.wt p = ∑ p ∈ Plt, (S.wt p + S.wt p.swap) := by
    rw [← sum_filter_add_sum_filter_not S.Pt (fun p => S.ord p.1 < S.ord p.2), ← hPlt, ← hPgt,
      hgt_sum, sum_add_distrib]
  have hbound : ∑ p ∈ Plt, (S.wt p + S.wt p.swap) ≤ Plt.card * (6 * c * (t - 1)) := by
    rw [← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun p hp => ?_
    simp only [hPlt, mem_filter] at hp
    obtain ⟨h1, h2, -⟩ := hPt_mem p hp.1
    exact S.wt_pair_le ht h1 h2 hp.2
  calc S.Y.card + S.YD.card ≤ Plt.card * (6 * c * (t - 1)) := hsum.trans (hwsplit ▸ hbound)
    _ ≤ c * S.M.card * (6 * c * (t - 1)) := Nat.mul_le_mul_right _ hlt_card
    _ = 6 * c ^ 2 * (t - 1) * S.M.card := by ring

/-- **Lemma 10.** Few leaves are highly connected to `M ∪ C`: `|Z| ≤ |M ∪ C|`
(the paper: `|Z| < |M ∪ C|`, which fails only for the empty graph). -/
theorem lemma_10 (hc : Depth1DensityLE G c) : S.Z.card ≤ (S.M ∪ S.C).card := by
  set T := S.M ∪ S.C
  set Q := (S.Z ×ˢ T).filter fun p => G.Adj p.1 p.2 with hQ
  have hQle : Q.card ≤ 2 * c * (S.Z ∪ T).card :=
    hc.card_le_of_adj (S.Z ∪ T) Q fun p hp => by
      simp only [hQ, mem_filter, mem_product] at hp
      exact ⟨mem_union_left _ hp.1.1, mem_union_right _ hp.1.2, hp.2⟩
  have hQge : (4 * c + 1) * S.Z.card ≤ Q.card := by
    rw [card_eq_sum_card_fiberwise (s := Q) (t := S.Z) (f := Prod.fst)
      (fun p hp => (mem_product.1 (mem_filter.1 hp).1).1), mul_comm, ← smul_eq_mul,
      ← sum_const]
    refine sum_le_sum fun z hz => ?_
    have hz' := hz
    simp only [Z, mem_filter, mem_univ, true_and] at hz'
    have : (nbhd G z ∩ (S.M ∪ S.C)).card ≤ (Q.filter fun p => p.1 = z).card := by
      refine card_le_card_of_injOn (fun y => (z, y)) ?_ (by intro _ _ _ _ h; simpa using h)
      intro y hy
      simp only [coe_inter, Set.mem_inter_iff, mem_coe, mem_nbhd] at hy
      simp only [hQ, mem_coe, mem_filter, mem_product]
      exact ⟨⟨⟨hz, hy.2⟩, hy.1⟩, trivial⟩
    omega
  have hU : (S.Z ∪ T).card ≤ S.Z.card + T.card := card_union_le _ _
  nlinarith

/-- `R = V \ N[D]`: the vertices not dominated in Phase 1. -/
noncomputable def R : Finset V := univ \ cnbhd G S.D

/-- The sources inside the star of `m` whose dominator is a leaf of `m` outside `C ∪ Y ∪ Z`. -/
noncomputable def Src (dom : V → V) (m : V) : Finset V :=
  (S.leaves m ∩ S.R).filter fun u => dom u ∈ S.leaves m \ (S.C ∪ S.Y ∪ S.Z)

lemma card_Src_le (ht : ExcludesKt3 G t) {dom : V → V} (hdom : IsDominator G S.D dom) {m : V}
    (hm : m ∈ S.M) (hmD : m ∉ S.D) : (S.Src dom m).card ≤ (2 * (t - 1) + 4) * c := by
  rcases (S.Src dom m).eq_empty_or_nonempty with h | ⟨u0, hu0⟩
  · rw [h]; simp
  simp only [Src, R, mem_filter, mem_inter, mem_sdiff, mem_univ, true_and, mem_union,
    not_or] at hu0
  obtain ⟨⟨hu0m, hu0R⟩, hxm, ⟨hxC, hxY⟩, hxZ⟩ := hu0
  set x := dom u0
  have hxM : x ∉ S.M := (S.mem_leaves.1 hxm).1
  have hxs : S.star x = m := (S.mem_leaves.1 hxm).2
  -- the degree of `x` is at most `4c + 2c(t-1)`
  have hdeg : (nbhd G x).card ≤ 4 * c + 2 * c * (t - 1) := by
    have hsub : nbhd G x ⊆ (nbhd G x ∩ (S.M ∪ S.C)) ∪ ((S.leaves m \ S.C).filter (G.Adj x)) := by
      intro y hy
      by_cases hyMC : y ∈ S.M ∪ S.C
      · exact mem_union_left _ (mem_inter.2 ⟨hy, hyMC⟩)
      · rw [mem_union, not_or] at hyMC
        rw [mem_nbhd] at hy
        refine mem_union_right _ (mem_filter.2 ⟨mem_sdiff.2 ⟨?_, hyMC.2⟩, hy⟩)
        rw [mem_leaves]
        refine ⟨hyMC.1, ?_⟩
        by_contra hys
        apply hxY
        simp only [Y, mem_filter, mem_univ, true_and]
        exact ⟨hxM, hxC, by rw [hxs]; exact hmD, y, hyMC.1, hyMC.2, by rw [hxs]; exact hys, hy⟩
    have hZ : (nbhd G x ∩ (S.M ∪ S.C)).card ≤ 4 * c := by
      by_contra h
      apply hxZ
      simp only [Z, mem_filter, mem_univ, true_and]
      exact ⟨hxM, by rw [hxs]; exact hmD, by omega⟩
    have h9 := S.lemma_9 ht hm hmD hxm hxC
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))
  -- `u0` preferred `x` over `m`
  have hres : resDeg G S.D m ≤ resDeg G S.D x := by
    refine (hdom u0 hu0R).2 m ?_
    rw [mem_cnbhd_singleton]; right
    have := S.adj_star (S.mem_leaves.1 hu0m).1; rwa [(S.mem_leaves.1 hu0m).2] at this
  have hxadj : G.Adj m x := by
    have := S.adj_star hxM; rw [hxs] at this; exact this.symm
  have hnx := card_nbhd (G := G) x
  have hsrc : (S.Src dom m).card ≤ (S.leaves m \ cnbhd G S.D).card := by
    refine card_le_card fun u hu => ?_
    simp only [Src, R, mem_filter, mem_inter, mem_sdiff, mem_univ, true_and] at hu ⊢
    exact hu.1
  have hleaf : (S.leaves m \ cnbhd G S.D).card ≤ (nbhd G x).card := by
    have hsub : S.leaves m \ cnbhd G S.D ⊆ cnbhd G {m} \ cnbhd G S.D := by
      intro u hu
      simp only [mem_sdiff, mem_leaves, mem_cnbhd_singleton] at hu ⊢
      refine ⟨Or.inr ?_, hu.2⟩
      have := S.adj_star hu.1.1; rw [hu.1.2] at this; exact this.symm
    by_cases hmN : m ∈ cnbhd G S.D
    · -- `m` is dominated by `D`, so it does not count in `resDeg x`
      have h1 : (S.leaves m \ cnbhd G S.D).card ≤ resDeg G S.D m := card_le_card hsub
      have h2 : resDeg G S.D x ≤ ((cnbhd G {x}).erase m).card := by
        refine card_le_card fun y hy => ?_
        rw [mem_sdiff] at hy
        exact mem_erase.2 ⟨fun h => hy.2 (h ▸ hmN), hy.1⟩
      have h3 : ((cnbhd G {x}).erase m).card + 1 = (cnbhd G {x}).card :=
        card_erase_add_one (by rw [mem_cnbhd_singleton]; exact Or.inr hxadj.symm)
      omega
    · have h1 : (S.leaves m \ cnbhd G S.D).card + 1 ≤ resDeg G S.D m := by
        have hmnot : m ∉ S.leaves m \ cnbhd G S.D := by simp [hm]
        rw [← card_insert_of_notMem hmnot]
        refine card_le_card (insert_subset ?_ hsub)
        simp [hmN]
      have h2 : resDeg G S.D x ≤ (cnbhd G {x}).card := card_le_card sdiff_subset
      omega
  calc (S.Src dom m).card ≤ (nbhd G x).card := hsrc.trans hleaf
    _ ≤ 4 * c + 2 * c * (t - 1) := hdeg
    _ = (2 * (t - 1) + 4) * c := by ring

/-- **Lemma 11 (corrected).** `|⋃_{m ∈ M \ D} {u ∈ N_{E'}(m) \ N[D] : dom(u) ∈ N_{E'}(m) \ (C ∪ Y ∪ Z)}|
≤ (2(t-1)+4)c|M|`. The paper's version (without excluding `C`) is false, see `lemma_11_false`. -/
theorem lemma_11 (ht : ExcludesKt3 G t) {dom : V → V} (hdom : IsDominator G S.D dom) :
    ((S.M \ S.D).biUnion (S.Src dom)).card ≤ (2 * (t - 1) + 4) * c * S.M.card := by
  calc _ ≤ (S.M \ S.D).card * ((2 * (t - 1) + 4) * c) := by
        refine card_le_of_subset_biUnion _ subset_rfl _ fun m hm => ?_
        rw [mem_sdiff] at hm
        exact S.card_Src_le ht hdom hm.1 hm.2
    _ ≤ S.M.card * ((2 * (t - 1) + 4) * c) := Nat.mul_le_mul_right _ (card_le_card sdiff_subset)
    _ = _ := by ring

/-- The image of the dominator function is covered by the sets counted in Lemmas 8, 10, 11. -/
lemma image_dom_subset {dom : V → V} (hdom : IsDominator G S.D dom) :
    S.R.image dom ⊆ (S.M ∪ S.C) ∪ S.Z ∪ S.Y ∪ S.YD.image dom ∪
      (S.R ∩ (S.M ∪ S.C)).image dom ∪ ((S.M \ S.D).biUnion (S.Src dom)).image dom := by
  intro x hx
  obtain ⟨u, huR, rfl⟩ := mem_image.1 hx
  have huR' : u ∉ cnbhd G S.D := by simpa [R] using huR
  simp only [mem_union]
  by_cases huMC : u ∈ S.M ∪ S.C
  · exact Or.inl (Or.inr (mem_image.2 ⟨u, mem_inter.2 ⟨huR, huMC⟩, rfl⟩))
  by_cases hxMC : dom u ∈ S.M ∪ S.C
  · left; left; left; left; left; exact mem_union.1 hxMC
  by_cases hxZ : dom u ∈ S.Z
  · left; left; left; left; right; exact hxZ
  by_cases hxY : dom u ∈ S.Y
  · left; left; left; right; exact hxY
  rw [mem_union, not_or] at huMC hxMC
  set m := S.star u
  have hm : m ∈ S.M := S.star_mem huMC.1
  have hmD : m ∉ S.D := by
    intro hmD; apply huR'; rw [mem_cnbhd]; exact ⟨m, hmD, Or.inr (S.adj_star huMC.1).symm⟩
  have hxN := (hdom u huR').1
  by_cases hxs : S.star (dom u) = m
  · right
    refine mem_image.2 ⟨u, mem_biUnion.2 ⟨m, mem_sdiff.2 ⟨hm, hmD⟩, ?_⟩, rfl⟩
    simp only [Src, mem_filter, mem_inter, mem_leaves, mem_sdiff, mem_union, not_or]
    exact ⟨⟨⟨huMC.1, rfl⟩, huR⟩, ⟨hxMC.1, hxs⟩, ⟨hxMC.2, hxY⟩, hxZ⟩
  · have hadj : G.Adj u (dom u) := by
      rcases mem_cnbhd_singleton.1 hxN with h | h
      · exact absurd (by rw [h]) hxs
      · exact h
    by_cases hxD : S.star (dom u) ∈ S.D
    · left; left; right
      refine mem_image.2 ⟨u, ?_, rfl⟩
      simp only [YD, mem_filter, mem_univ, true_and]
      exact ⟨huMC.1, huMC.2, hmD, dom u, hxMC.1, hxMC.2, hxD, hadj⟩
    · exfalso; apply hxY
      simp only [Y, mem_filter, mem_univ, true_and]
      exact ⟨hxMC.1, hxMC.2, hxD, u, huMC.1, huMC.2, fun h => hxs h.symm, hadj.symm⟩

end Setup

/-- A graph excluding `K_{0,3}` as a depth-1 minor has at most two vertices. -/
lemma card_le_two_of_excludesKt3_zero (ht : ExcludesKt3 G 0) : Fintype.card V ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.1 h
  have := ht.card_lt_two_singletons (a := x) (b := y) (z := z) (S := {z}) hxy (by simpa using hxz)
    (by simpa using hyz) (mem_singleton_self _) (fun w hw hwz => absurd (mem_singleton.1 hw) hwz)
    ∅ (by simp) (by simp)
  simp at this

/-- **Lemma 12.** If all depth-1 minors of `G` have edge density at most `c` and `G` excludes
`K_{t,3}` as a depth-1 minor, then the modified algorithm (with parameter `c`, for any choice of
the dominators) computes a `(6c²t + (2t+5)c + 4)`-approximation of a minimum dominating set. -/
theorem lemma_12 (hc : Depth1DensityLE G c) (ht : ExcludesKt3 G t) {dom : V → V}
    (hdom : IsDominator G (phase1 G c) dom) :
    IsApprox G (6 * c ^ 2 * t + (2 * t + 5) * c + 4) (output G c dom) := by
  refine ⟨output_isDominatingSet hdom, fun M hM => ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · -- degenerate case `t = 0`: at most two vertices
    have hV := card_le_two_of_excludesKt3_zero ht
    rcases M.eq_empty_or_nonempty with rfl | ⟨m, hm⟩
    · have : IsEmpty V := by
        refine ⟨fun v => ?_⟩
        rcases hM v with h | ⟨u, hu, -⟩ <;> simp at *
      have h0 : Fintype.card V = 0 := Fintype.card_eq_zero
      have := card_le_univ (output G c dom)
      simp only [card_empty, mul_zero]; omega
    · have h1 : 1 ≤ M.card := card_pos.2 ⟨m, hm⟩
      have h2 : (output G c dom).card ≤ 2 := (card_le_univ _).trans hV
      nlinarith
  obtain ⟨S, rfl⟩ := Setup.exists_of_dominating (c := c) hM
  have hD := lemma_5 hc S.hM
  have hsub := S.image_dom_subset hdom
  have h8 := S.corollary_8 hc ht
  have h10 := S.lemma_10 hc
  have h11 := S.lemma_11 ht hdom
  have hMC := S.card_MC_le
  have hRMC : ((S.R ∩ (S.M ∪ S.C)).image dom).card ≤ (S.M ∪ S.C).card :=
    card_image_le.trans (card_le_card inter_subset_right)
  have hYD : (S.YD.image dom).card ≤ S.YD.card := card_image_le
  have hSrc : (((S.M \ S.D).biUnion (S.Src dom)).image dom).card ≤
      ((S.M \ S.D).biUnion (S.Src dom)).card := card_image_le
  have himg : (S.R.image dom).card ≤ (S.M ∪ S.C).card + S.Z.card + S.Y.card + S.YD.card +
      (S.M ∪ S.C).card + (2 * (t - 1) + 4) * c * S.M.card := by
    refine (card_le_card hsub).trans ?_
    refine (card_union_le _ _).trans ?_
    refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (card_union_le _ _) _) _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (card_union_le _ _) _) _) _) _).trans ?_
    omega
  have hout : (output G c dom).card ≤ S.D.card + (S.R.image dom).card := card_union_le _ _
  -- arithmetic: `(c+1) + 3(2c+1) + 6c²(t-1) + (2(t-1)+4)c ≤ 6c²t + (2t+5)c + 4`
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h8 h11 himg
  have key : (output G c dom).card ≤
      ((c + 1) + 3 * (2 * c + 1) + 6 * c ^ 2 * s + (2 * s + 4) * c) * S.M.card := by
    nlinarith
  refine key.trans (Nat.mul_le_mul_right _ ?_)
  have hc2 : c ≤ c ^ 2 := Nat.le_self_pow two_ne_zero c
  nlinarith

end Podc.BoundedGenusMDS
