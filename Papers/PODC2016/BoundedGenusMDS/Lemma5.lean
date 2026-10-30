import Papers.PODC2016.BoundedGenusMDS.Defs

/-!
# Lemma 5: the Phase-1 set `D` is small

`|D| ≤ (c + 1) · |M|` for every dominating set `M` (the paper states it for a minimum one).

The paper contracts only the stars of `m ∈ M \ D`; vertices of `N(D \ M) \ (D ∪ M)` whose
unique `M`-neighbour lies in `M ∩ D` then stay uncontracted and `|V(H̃)| = |D \ M| + |M|` fails.
We contract a star around *every* `m ∈ M` (center `m`, leaves: the vertices outside `M ∪ D`
assigned to `m`), which repairs the count.
-/

open Finset

namespace Podc.BoundedGenusMDS

open SimpleGraph (Depth1Model IsDepth1Minor Depth1DensityLE ExcludesKt3 depth1_of_cover_two)

open Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
/-- Every vertex outside a dominating set `M` can be assigned to an `M`-neighbour. -/
lemma exists_assign {M : Finset V} (hM : G.IsDominatingSet (M : Set V)) :
    ∃ a : V → V, ∀ v, v ∉ M → a v ∈ M ∧ G.Adj v (a v) := by
  have : ∀ v, ∃ m, v ∉ M → m ∈ M ∧ G.Adj v m := by
    intro v
    rcases hM v with h | ⟨u, hu, h⟩
    · exact ⟨v, fun h' => absurd (by simpa using h) h'⟩
    · exact ⟨u, fun _ => ⟨by simpa using hu, h⟩⟩
  choose a ha using this
  exact ⟨a, ha⟩

/-- **Lemma 5.** If all depth-1 minors of `G` have edge density at most `c`, then the set `D`
of Phase 1 satisfies `|D| ≤ (c + 1) · |M|` for every dominating set `M` of `G`. -/
theorem lemma_5 {c : ℕ} (hc : Depth1DensityLE G c) {M : Finset V}
    (hM : G.IsDominatingSet (M : Set V)) : (phase1 G c).card ≤ (c + 1) * M.card := by
  set D := phase1 G c with hD
  obtain ⟨a, ha⟩ := exists_assign hM
  -- the star family: singletons `{w}` for `w ∈ D \ M`, stars around every `m ∈ M`
  let J : Finset (V ⊕ V) := (D \ M).map Function.Embedding.inl
  let K : Finset (V ⊕ V) := M.map Function.Embedding.inr
  let I : Finset (V ⊕ V) := J ∪ K
  let ctr : V ⊕ V → V := Sum.elim id id
  let leaves : V → Finset V := fun m => univ.filter fun v => v ∉ M ∧ v ∉ D ∧ a v = m
  let br : V ⊕ V → Finset V := Sum.elim (fun w => {w}) (fun m => insert m (leaves m))
  have hJK : Disjoint J K := by
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [J, K, mem_map, Function.Embedding.inl_apply, Function.Embedding.inr_apply] at hx hx'
    obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, h⟩ := hx'; exact Sum.inr_ne_inl h
  have hIcard : I.card = (D \ M).card + M.card := by
    simp [I, card_union_of_disjoint hJK, J, K]
  have hctr : ∀ i ∈ I, ctr i ∈ br i := by
    rintro (w | m) _ <;> simp [ctr, br]
  have hstar : ∀ i ∈ I, ∀ x ∈ br i, x ≠ ctr i → G.Adj (ctr i) x := by
    rintro (w | m) _ x hx hne
    · simp [br, ctr] at hx hne; exact absurd hx hne
    · simp only [br, ctr, Sum.elim_inr, id, mem_insert, leaves, mem_filter, mem_univ,
        true_and] at hx hne
      rcases hx with rfl | ⟨hxM, -, rfl⟩
      · exact absurd rfl hne
      · exact ((ha x hxM).2).symm
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (br i) (br j) := by
    rintro (w | m) hi (w' | m') hj hne
    · simp only [br, Sum.elim_inl, disjoint_singleton]
      intro h; exact hne (by rw [h])
    · simp only [I, J, K, mem_union, mem_map, Function.Embedding.inl_apply,
        Function.Embedding.inr_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
        exists_false, or_false, false_or, exists_eq_right, mem_sdiff] at hi hj
      simp only [br, Sum.elim_inl, Sum.elim_inr, disjoint_singleton_left, mem_insert, leaves,
        mem_filter, mem_univ, true_and, not_or, not_and]
      exact ⟨fun h => hi.2 (h ▸ hj), fun _ h => absurd hi.1 h⟩
    · simp only [I, J, K, mem_union, mem_map, Function.Embedding.inl_apply,
        Function.Embedding.inr_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
        exists_false, or_false, false_or, exists_eq_right, mem_sdiff] at hi hj
      simp only [br, Sum.elim_inl, Sum.elim_inr, disjoint_singleton_right, mem_insert, leaves,
        mem_filter, mem_univ, true_and, not_or, not_and]
      exact ⟨fun h => hj.2 (h ▸ hi), fun _ h => absurd hj.1 h⟩
    · simp only [br, Sum.elim_inr]
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [mem_insert, leaves, mem_filter, mem_univ, true_and] at hx hx'
      have hmm : m ≠ m' := fun h => hne (by rw [h])
      simp only [I, J, K, mem_union, mem_map, Function.Embedding.inl_apply,
        Function.Embedding.inr_apply, Sum.inr.injEq, reduceCtorEq, and_false,
        exists_false, false_or, exists_eq_right] at hi hj
      rcases hx with rfl | ⟨hxM, -, rfl⟩ <;> rcases hx' with h | ⟨hxM', -, h⟩
      · exact hmm h
      · exact hxM' hi
      · exact hxM (h ▸ hj)
      · exact hmm h
  let P := (I ×ˢ I).filter fun p => p.1 ≠ p.2 ∧ ∃ x ∈ br p.1, ∃ y ∈ br p.2, G.Adj x y
  have hP : P.card ≤ 2 * c * I.card :=
    hc.card_le_of_touch I ctr br hctr hstar hdisj P fun p hp => by
      simp only [P, mem_filter, mem_product] at hp; exact ⟨hp.1.1, hp.1.2, hp.2⟩
  have hJsub : J ⊆ I := subset_union_left
  have hPJ : ((J ×ˢ J).filter fun p => p.1 ≠ p.2 ∧ ∃ x ∈ br p.1, ∃ y ∈ br p.2, G.Adj x y).card
      ≤ 2 * c * J.card :=
    hc.card_le_of_touch J ctr br (fun i hi => hctr i (hJsub hi))
      (fun i hi => hstar i (hJsub hi)) (fun i hi j hj => hdisj i (hJsub hi) j (hJsub hj)) _
      fun p hp => by simp only [mem_filter, mem_product] at hp; exact ⟨hp.1.1, hp.1.2, hp.2⟩
  -- every `w ∈ D \ M` touches at least `2c + 1` other stars
  have hdeg : ∀ w ∈ D \ M, 2 * c + 1 ≤ (P.filter fun p => p.1 = Sum.inl w).card := by
    intro w hw
    rw [mem_sdiff] at hw
    by_contra hlt
    push Not at hlt
    let A := (P.filter fun p => p.1 = Sum.inl w).image fun p => ctr p.2
    have hA : A.card ≤ 2 * c := (card_image_le).trans (by omega)
    have hwA : w ∉ A := by
      simp only [A, mem_image, mem_filter, not_exists, not_and]
      rintro ⟨i, j⟩ ⟨hp, h1⟩ h2
      simp only at h1 h2
      simp only [P, mem_filter] at hp
      subst h1
      rcases j with w' | m
      · simp only [ctr, Sum.elim_inl, id] at h2; subst h2; exact hp.2.1 rfl
      · simp only [I, J, K, mem_product, mem_union, mem_map, Function.Embedding.inl_apply,
          Function.Embedding.inr_apply, reduceCtorEq, and_false, exists_false, false_or,
          Sum.inr.injEq, exists_eq_right] at hp
        simp only [ctr, Sum.elim_inr, id] at h2; subst h2; exact hw.2 hp.1.2
    have hcov : nbhd G w ⊆ cnbhd G A := by
      intro y hy
      rw [mem_nbhd] at hy
      -- the branch containing `y`
      obtain ⟨j, hjI, hyj⟩ : ∃ j ∈ I, y ∈ br j := by
        by_cases hyM : y ∈ M
        · exact ⟨Sum.inr y, by simp [I, K, hyM], by simp [br]⟩
        · by_cases hyD : y ∈ D
          · exact ⟨Sum.inl y, by simp [I, J, hyD, hyM], by simp [br]⟩
          · exact ⟨Sum.inr (a y), by simp [I, K, (ha y hyM).1],
              by simp [br, leaves, hyM, hyD]⟩
      have hwI : Sum.inl w ∈ I := by simp [I, J, hw.1, hw.2]
      have hjw : Sum.inl w ≠ j := by
        rintro rfl; simp [br] at hyj; subst hyj; exact G.irrefl hy
      have hpP : (Sum.inl w, j) ∈ P.filter fun p => p.1 = Sum.inl w := by
        exact mem_filter.2 ⟨mem_filter.2 ⟨mem_product.2 ⟨hwI, hjI⟩, hjw, w, by simp [br], y, hyj,
          hy⟩, rfl⟩
      have hcA : ctr j ∈ A := mem_image.2 ⟨_, hpP, rfl⟩
      rw [mem_cnbhd]
      refine ⟨ctr j, hcA, ?_⟩
      by_cases h : y = ctr j
      · exact Or.inl h
      · exact Or.inr (hstar j hjI y hyj h)
    exact (mem_phase1.1 hw.1) ⟨A, hwA, hA, hcov⟩
  -- double counting
  have hS : (2 * c + 1) * J.card ≤ (P.filter fun p => p.1 ∈ J).card := by
    rw [card_eq_sum_card_fiberwise (s := P.filter fun p => p.1 ∈ J) (f := Prod.fst) (t := J)
      (fun p hp => (mem_filter.1 hp).2)]
    have hJ : J.card = (D \ M).card := by simp [J]
    rw [hJ, mul_comm, ← smul_eq_mul, ← sum_const]
    rw [show J = (D \ M).map Function.Embedding.inl from rfl, sum_map]
    refine sum_le_sum fun w hw => ?_
    refine (hdeg w hw).trans (le_of_eq ?_)
    congr 1; ext p; simp only [mem_filter]
    constructor
    · rintro ⟨hp, h⟩; exact ⟨⟨hp, by rw [h]; exact mem_map_of_mem _ hw⟩, h⟩
    · rintro ⟨⟨hp, -⟩, h⟩; exact ⟨hp, h⟩
  have hsymm : ∀ p ∈ P, p.swap ∈ P := by
    rintro ⟨i, j⟩ hp
    simp only [P, mem_filter, mem_product, Prod.swap_prod_mk] at hp ⊢
    obtain ⟨⟨hi, hj⟩, hne, x, hx, y, hy, hxy⟩ := hp
    exact ⟨⟨hj, hi⟩, Ne.symm hne, y, hy, x, hx, hxy.symm⟩
  have hS' : (P.filter fun p => p.1 ∈ J).card = (P.filter fun p => p.2 ∈ J).card := by
    refine card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp; simp only [mem_filter] at hp ⊢; exact ⟨hsymm p hp.1, hp.2⟩
    · intro p _ q _ h; exact Prod.swap_injective h
    · intro q hq; simp only [mem_filter] at hq
      exact ⟨q.swap, by simp only [mem_filter, Prod.fst_swap]; exact ⟨hsymm q hq.1, hq.2⟩,
        by simp⟩
  have hunion := card_union_add_card_inter (P.filter fun p => p.1 ∈ J) (P.filter fun p => p.2 ∈ J)
  have hU : ((P.filter fun p => p.1 ∈ J) ∪ (P.filter fun p => p.2 ∈ J)).card ≤ P.card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have hInt : ((P.filter fun p => p.1 ∈ J) ∩ (P.filter fun p => p.2 ∈ J)).card ≤
      ((J ×ˢ J).filter fun p => p.1 ≠ p.2 ∧ ∃ x ∈ br p.1, ∃ y ∈ br p.2, G.Adj x y).card := by
    refine card_le_card fun p hp => ?_
    simp only [mem_inter, mem_filter, P, mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.2.2⟩, hp.1.1.2⟩
  have hJcard : J.card = (D \ M).card := by simp [J]
  have hDM : (D \ M).card ≤ c * M.card := by
    rw [hJcard] at hS hPJ
    rw [hIcard] at hP
    nlinarith
  have : D.card ≤ (D \ M).card + M.card := by
    calc D.card ≤ (D \ M ∪ M).card := card_le_card (by intro x hx; by_cases h : x ∈ M <;> simp [h, hx])
      _ ≤ _ := card_union_le _ _
  nlinarith

end Podc.BoundedGenusMDS
