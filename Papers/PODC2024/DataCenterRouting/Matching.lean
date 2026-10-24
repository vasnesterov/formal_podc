import Papers.PODC2024.DataCenterRouting.Model

/-!
# Maximum matchings and maximum-throughput allocations of the macro-switch (Lemma 3.2)

The macro-switch `MS_n` corresponds to the bipartite multigraph `G^MS` whose start nodes are the
source servers, whose end nodes are the destination servers, and whose links are the flows. A
feasible allocation of `MS_n` is exactly a *fractional matching* of `G^MS`: non-negative weights on
the flows with total weight at most `1` at every source and at every destination.

The folklore Lemma 3.2 of Ferreira–Atre–Sherry–Sobrinho (PODC 2024) states that the `0/1`
allocation of a maximum matching is a maximum-throughput allocation. The non-trivial direction is
that the fractional matching number of a bipartite multigraph equals its matching number; we prove
it (`exists_matching_sum_le`) for an arbitrary finite bipartite multigraph via König's theorem in
the deficiency form of Hall's theorem: for the set `X'` of sources maximizing the deficiency
`δ = |X'| - |N(X')|`, every flow has its source outside `X'` or its destination in `N(X')`, so the
weight is at most `|X| - δ`; and adding `δ` dummy destinations adjacent to every source, Hall's
theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`) gives a matching of size at least
`|X| - δ`.

## Main statements

* `exists_matching_sum_le`: every fractional matching of a finite bipartite multigraph is
  dominated in total weight by the size of some matching;
* `lemma_3_2`: **Lemma 3.2** — the `0/1` allocation of a maximum matching of `G^MS` is a
  maximum-throughput allocation of `MS_n`;
* `exists_isMaximumMatching`, `throughput_le_card_of_isMaximumMatching`.
-/

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

section Konig

variable {X Y F : Type*} [Fintype F]

/-- If every fibre of `g` carries total weight at most `1`, then the flows mapped into `T` carry
total weight at most `#T`. -/
theorem sum_filter_mem_le_card {Z : Type*} [DecidableEq Z] (g : F → Z) (b : F → ℝ)
    (hb : ∀ f, 0 ≤ b f) (hg : ∀ z, ∑ f ∈ univ.filter (fun f => g f = z), b f ≤ 1)
    (T : Finset Z) : ∑ f ∈ univ.filter (fun f => g f ∈ T), b f ≤ T.card := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun f => g f ∈ T)) (t := T) (g := g)
    (fun f hf => (mem_filter.1 hf).2)]
  calc ∑ z ∈ T, ∑ f ∈ (univ.filter (fun f => g f ∈ T)).filter (fun f => g f = z), b f
      ≤ ∑ _z ∈ T, (1 : ℝ) := by
        refine sum_le_sum fun z _ => le_trans ?_ (hg z)
        refine sum_le_sum_of_subset_of_nonneg ?_ fun f _ _ => hb f
        intro f hf
        simp only [mem_filter, mem_univ, true_and] at hf ⊢
        exact hf.2
    _ = T.card := by simp

variable [DecidableEq X] [DecidableEq Y]

/-- The neighbourhood `N(s)` of a set `s` of start nodes in the bipartite multigraph with links
`F`, link `f` joining `src f` and `dst f`. -/
def bipNbhd (src : F → X) (dst : F → Y) (s : Finset X) : Finset Y :=
  (univ.filter (fun f => src f ∈ s)).image dst

/-- `y ∈ N(s)` iff some link joins a node of `s` to `y`. -/
theorem mem_bipNbhd {src : F → X} {dst : F → Y} {s : Finset X} {y : Y} :
    y ∈ bipNbhd src dst s ↔ ∃ f, src f ∈ s ∧ dst f = y := by
  simp [bipNbhd]

-- CSLib candidate
/-- **Fractional matchings of bipartite multigraphs are dominated by matchings** (König). Let `F`
be the links of a finite bipartite multigraph, link `f` joining `src f` and `dst f`. If `b` is a
fractional matching (non-negative weights, total weight at most `1` at every node), then some
matching `S` (a set of links with pairwise distinct sources and pairwise distinct destinations)
has at least the total weight of `b` as its size. -/
theorem exists_matching_sum_le [Fintype X] (src : F → X) (dst : F → Y) (b : F → ℝ)
    (hb : ∀ f, 0 ≤ b f) (hsrc : ∀ x, ∑ f ∈ univ.filter (fun f => src f = x), b f ≤ 1)
    (hdst : ∀ y, ∑ f ∈ univ.filter (fun f => dst f = y), b f ≤ 1) :
    ∃ S : Finset F, Set.InjOn src S ∧ Set.InjOn dst S ∧ ∑ f, b f ≤ S.card := by
  classical
  -- a set of start nodes of maximum deficiency
  obtain ⟨X', -, hX'⟩ := Finset.exists_max_image (univ : Finset (Finset X))
    (fun s => (s.card : ℤ) - (bipNbhd src dst s).card) univ_nonempty
  have h0 : (bipNbhd src dst X').card ≤ X'.card := by
    have := hX' ∅ (mem_univ _)
    have he : bipNbhd src dst ∅ = ∅ := by simp [bipNbhd]
    rw [he] at this
    simp only [card_empty, Nat.cast_zero, sub_zero] at this
    omega
  set d := X'.card - (bipNbhd src dst X').card with hd
  -- Hall's condition holds after adding `d` dummy end nodes adjacent to every start node
  let t : X → Finset (Y ⊕ Fin d) := fun x => (bipNbhd src dst {x}).disjSum univ
  have hall : ∀ s : Finset X, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
    · simp
    have hsub : (bipNbhd src dst s).disjSum (univ : Finset (Fin d)) ⊆ s.biUnion t := by
      intro z hz
      rw [mem_biUnion]
      rcases z with y | i
      · rw [inl_mem_disjSum, mem_bipNbhd] at hz
        obtain ⟨f, hf, rfl⟩ := hz
        refine ⟨src f, hf, ?_⟩
        simp only [t, inl_mem_disjSum, mem_bipNbhd, mem_singleton]
        exact ⟨f, rfl, rfl⟩
      · exact ⟨x0, hx0, by simp [t]⟩
    have h1 := card_le_card hsub
    rw [card_disjSum, card_univ, Fintype.card_fin] at h1
    have h2 := hX' s (mem_univ _)
    omega
  obtain ⟨g, hginj, hgt⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  -- the start nodes matched to genuine end nodes
  set A := univ.filter (fun x => ∃ f, src f = x ∧ Sum.inl (dst f) = g x) with hA
  have hAc : Aᶜ.card ≤ d := by
    have hsub : Aᶜ.image g ⊆ univ.map Function.Embedding.inr := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
      have hxA : x ∉ A := mem_compl.1 hx
      have hx' := hgt x
      rcases hgx : g x with y | i
      · exfalso
        rw [hgx] at hx'
        simp only [t, inl_mem_disjSum, mem_bipNbhd, mem_singleton] at hx'
        obtain ⟨f, hf, rfl⟩ := hx'
        exact hxA (mem_filter.2 ⟨mem_univ _, f, hf, hgx.symm⟩)
      · simp
    have := card_le_card hsub
    rwa [card_image_of_injective _ hginj, card_map, card_univ, Fintype.card_fin] at this
  have hpick : ∀ x ∈ A, ∃ f, src f = x ∧ Sum.inl (dst f) = g x := fun x hx => (mem_filter.1 hx).2
  choose pick hpick using hpick
  have hpinj : Function.Injective (fun x : A => pick x.1 x.2) := by
    rintro ⟨x1, hx1⟩ ⟨x2, hx2⟩ heq
    apply Subtype.ext
    show x1 = x2
    simp only at heq
    rw [← (hpick x1 hx1).1, ← (hpick x2 hx2).1, heq]
  refine ⟨A.attach.image (fun x => pick x.1 x.2), ?_, ?_, ?_⟩
  · rintro _ h1 _ h2 heq
    simp only [coe_image, Set.mem_image, mem_coe, mem_attach, true_and] at h1 h2
    obtain ⟨⟨x1, hx1⟩, rfl⟩ := h1
    obtain ⟨⟨x2, hx2⟩, rfl⟩ := h2
    have : x1 = x2 := by rw [← (hpick x1 hx1).1, ← (hpick x2 hx2).1]; exact heq
    subst this
    rfl
  · rintro _ h1 _ h2 heq
    simp only [coe_image, Set.mem_image, mem_coe, mem_attach, true_and] at h1 h2
    obtain ⟨⟨x1, hx1⟩, rfl⟩ := h1
    obtain ⟨⟨x2, hx2⟩, rfl⟩ := h2
    have : x1 = x2 := by
      apply hginj
      rw [← (hpick x1 hx1).2, ← (hpick x2 hx2).2]
      exact congrArg Sum.inl heq
    subst this
    rfl
  · rw [card_image_of_injective _ hpinj, card_attach]
    -- every link leaves `X'ᶜ` or enters `N(X')`
    have hsplit : ∑ f, b f ≤ ∑ f ∈ univ.filter (fun f => src f ∈ X'ᶜ), b f +
        ∑ f ∈ univ.filter (fun f => dst f ∈ bipNbhd src dst X'), b f := by
      rw [← sum_filter_add_sum_filter_not univ (fun f => src f ∈ X'ᶜ)]
      refine add_le_add le_rfl ?_
      refine sum_le_sum_of_subset_of_nonneg ?_ fun f _ _ => hb f
      intro f hf
      simp only [mem_filter, mem_univ, true_and, mem_compl, not_not] at hf ⊢
      exact mem_bipNbhd.2 ⟨f, hf, rfl⟩
    have e1 := sum_filter_mem_le_card src b hb hsrc X'ᶜ
    have e2 := sum_filter_mem_le_card dst b hb hdst (bipNbhd src dst X')
    have hc1 := card_compl_add_card X'
    have hc2 := card_compl_add_card A
    have hnat : X'ᶜ.card + (bipNbhd src dst X').card ≤ A.card := by omega
    have hreal : ((X'ᶜ.card : ℕ) : ℝ) + ((bipNbhd src dst X').card : ℕ) ≤ (A.card : ℝ) := by
      exact_mod_cast hnat
    linarith

end Konig

variable {n : ℕ} {F : Type*} [Fintype F] (fl : Flows n F)

/-- Every macro-switch-feasible allocation has throughput at most the size of some matching
of `G^MS` (fractional matching number = matching number). -/
theorem exists_isMatching_throughput_le {b : F → ℝ} (hb : (macroSwitch fl).Feasible b) :
    ∃ S : Finset F, IsMatching fl S ∧ throughput b ≤ S.card := by
  obtain ⟨S, h1, h2, h3⟩ := exists_matching_sum_le fl.src fl.dst b hb.1
    (fun s => by rw [sum_filter, ← macroSwitch_load_srcLink]; exact hb.2 _)
    (fun t => by rw [sum_filter, ← macroSwitch_load_dstLink]; exact hb.2 _)
  exact ⟨S, ⟨h1, h2⟩, h3⟩

/-- `G^MS` has a maximum matching. -/
theorem exists_isMaximumMatching : ∃ S, IsMaximumMatching fl S := by
  classical
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (univ.filter (fun S : Finset F => IsMatching fl S))
    Finset.card ⟨∅, mem_filter.2 ⟨mem_univ _, by simp [IsMatching]⟩⟩
  refine ⟨S, (mem_filter.1 hS).2, fun S' hS' => hmax S' (by simpa using hS')⟩

/-- Every allocation feasible in the macro-switch has throughput at most the size of a maximum
matching of `G^MS`. -/
theorem throughput_le_card_of_isMaximumMatching {S : Finset F} (hS : IsMaximumMatching fl S)
    {b : F → ℝ} (hb : (macroSwitch fl).Feasible b) : throughput b ≤ S.card := by
  obtain ⟨S', hS', hle⟩ := exists_isMatching_throughput_le fl hb
  exact hle.trans (by exact_mod_cast hS.2 S' hS')

/-- The throughput of the `0/1` allocation of `S` is `#S`. -/
theorem throughput_indicatorAlloc (S : Finset F) : throughput (indicatorAlloc S) = S.card := by
  classical
  simp [throughput, indicatorAlloc]

/-- The `0/1` allocation of a matching is feasible in the macro-switch. -/
theorem IsMatching.feasible_indicatorAlloc {S : Finset F} (hS : IsMatching fl S) :
    (macroSwitch fl).Feasible (indicatorAlloc S) := by
  classical
  have key : ∀ {Z : Type _} [DecidableEq Z] (g : F → Z), Set.InjOn g (S : Set F) → ∀ z,
      ∑ f ∈ univ.filter (fun f => g f = z), indicatorAlloc S f ≤ 1 := by
    intro Z _ g hg z
    simp only [indicatorAlloc, sum_ite_mem, sum_const, nsmul_eq_mul, mul_one]
    have : (({f | g f = z} : Finset F) ∩ S).card ≤ 1 := by
      refine card_le_one.2 fun f hf f' hf' => ?_
      simp only [mem_inter, mem_filter, mem_univ, true_and] at hf hf'
      exact hg hf.2 hf'.2 (hf.1.trans hf'.1.symm)
    exact_mod_cast this
  refine ⟨fun f => by unfold indicatorAlloc; split_ifs <;> norm_num, fun ℓ => ?_⟩
  rw [macroSwitch_cap]
  cases ℓ with
  | srcLink s => rw [macroSwitch_load_srcLink, ← sum_filter]; exact key _ hS.1 s
  | up i m => rw [macroSwitch_load_up]; norm_num
  | down m o => rw [macroSwitch_load_down]; norm_num
  | dstLink t => rw [macroSwitch_load_dstLink, ← sum_filter]; exact key _ hS.2 t

/-- **Lemma 3.2** (Folklore) of [Ferreira–Atre–Sherry–Sobrinho, PODC 2024]. The `0/1`
allocation of a maximum matching of `G^MS` is a maximum-throughput allocation of the
macro-switch. -/
theorem lemma_3_2 {S : Finset F} (hS : IsMaximumMatching fl S) :
    (macroSwitch fl).IsMaxThroughput (indicatorAlloc S) :=
  ⟨hS.1.feasible_indicatorAlloc fl, fun b hb => by
    rw [throughput_indicatorAlloc]; exact throughput_le_card_of_isMaximumMatching fl hS hb⟩

end Podc.DataCenterRouting
