import Papers.PODC2021.LowCongestionShortcuts.DenseMinor

/-!
# Theorem 3.1 of [GH21]

> **Theorem 3.1.** Every `G` with diameter `D` and minor density `δ = δ(G)` admits tree-restricted
> `8δD`-congestion `8δ`-block partial shortcuts.

We prove it with `8δ + 1` blocks instead of `8δ` (the paper's case (I) overlooks the block
containing the root; see `differencies.md`), for every `δ ≥ δ(G)`, i.e. under the hypothesis
`G.MinorDensityLE δ`.

* `caseII_false`: case (II) of the proof (more than half of the parts have `B`-degree `> 8δ`) is
  impossible, by the averaging argument over random sets of parts.
* `theorem_3_1`: the theorem.
-/

set_option linter.unusedSectionVars false

namespace LowCongestionShortcuts

open SimpleGraph Finset

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  {G : SimpleGraph V} {T : G.RootedTree} {P : ι → Finset V}

/-- The arithmetic at the end of the proof of Theorem 3.1. Variables: `N` = number of edges of `B`
whose representative is not the edge-node itself, `m` = number of edges of `B`, `o = |O|`,
`k` = number of parts, `q₀ = (1 - p)^(D-1)` with `p = 1/(4D)`. -/
theorem final_arith {δ D N m o k q₀ : ℝ} (hD : 1 ≤ D) (hδ : 1 / 2 ≤ δ) (ho : 0 ≤ o)
    (hN : m - o ≤ N) (hc : 8 * δ * D * o ≤ m) (hk : 4 * δ * k < m)
    (hq : 1 - (D - 1) * (1 / (4 * D)) ≤ q₀) :
    δ * (k * (1 / (4 * D)) + o) < N * (1 / (4 * D)) * q₀ := by
  have hD0 : 0 < D := by linarith
  have hq' : (3 * D + 1) / (4 * D) ≤ q₀ := by
    have : 1 - (D - 1) * (1 / (4 * D)) = (3 * D + 1) / (4 * D) := by field_simp; ring
    linarith
  have hq0 : 0 ≤ q₀ := le_trans (by positivity) hq'
  -- `o (3D+1) ≤ m`
  have h1 : o * (3 * D + 1) ≤ m := by
    have h3 : 3 * D + 1 ≤ 8 * δ * D := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 ho]
  have hmo : 0 ≤ m - o := by nlinarith
  have hNq : (m - o) * ((3 * D + 1) / (4 * D)) ≤ N * q₀ :=
    mul_le_mul hN hq' (by positivity) (by linarith)
  have key : δ * k + 4 * D * δ * o < N * q₀ := by
    have h2 : m / 4 + m / 2 ≤ (m - o) * ((3 * D + 1) / (4 * D)) := by
      have e : (m - o) * ((3 * D + 1) / (4 * D)) - (m / 4 + m / 2) =
          (m - o * (3 * D + 1)) / (4 * D) := by field_simp; ring
      have : 0 ≤ (m - o * (3 * D + 1)) / (4 * D) := div_nonneg (by linarith) (by positivity)
      linarith
    nlinarith
  have : δ * (k * (1 / (4 * D)) + o) = (δ * k + 4 * D * δ * o) / (4 * D) := by
    field_simp
  rw [this, div_lt_iff₀ (by positivity)]
  calc δ * k + 4 * D * δ * o < N * q₀ := key
    _ = N * (1 / (4 * D)) * q₀ * (4 * D) := by field_simp

/-- **Case (II) of the proof of Theorem 3.1 is impossible**: if fewer than half of the parts have
`B`-degree at most `8δ`, then for some set `S` of parts the bipartite minor `B_S` has more than
`δ |V(B_S)|` edges. -/
theorem caseII_false {δ : ℝ} (hδ : G.MinorDensityLE δ) (hP : G.IsParts P) {D : ℕ}
    (hT : T.DepthLE D) {O : Finset V}
    (hO : ∀ v, v ∈ O ↔ v ≠ T.root ∧ 8 * δ * D ≤ ((parts T P O v).card : ℝ))
    (hbad : 2 * (univ.filter fun i =>
      ((O.filter fun v => i ∈ parts T P O v).card : ℝ) ≤ 8 * δ).card < Fintype.card ι) :
    False := by
  classical
  set deg : ι → ℕ := fun i => (O.filter fun v => i ∈ parts T P O v).card with hdeg
  set good := univ.filter fun i => (deg i : ℝ) ≤ 8 * δ with hgood
  set bad := univ.filter fun i => ¬ (deg i : ℝ) ≤ 8 * δ with hbad'
  have hgb : good.card + bad.card = Fintype.card ι := by
    rw [hgood, hbad', Finset.card_filter_add_card_filter_not]; rfl
  obtain ⟨i₀, hi₀⟩ : bad.Nonempty := by rw [← card_pos]; omega
  have hV : Nonempty V := by
    obtain ⟨⟨x, _⟩⟩ := (hP.connected i₀).nonempty; exact ⟨x⟩
  have hδ0 : 0 ≤ δ := hδ.nonneg
  have hdeg0 : 0 < deg i₀ := by
    have h1 : ¬ (deg i₀ : ℝ) ≤ 8 * δ := (mem_filter.1 hi₀).2
    have : (0:ℝ) < deg i₀ := by linarith
    exact_mod_cast this
  obtain ⟨v₀, hv₀⟩ : (O.filter fun v => i₀ ∈ parts T P O v).Nonempty := card_pos.1 hdeg0
  have hv₀r := ((hO v₀).1 (mem_filter.1 hv₀).1).1
  have hδ2 : 1 / 2 ≤ δ := hδ.half_le (T.adj_parent v₀ hv₀r)
  have hD : 1 ≤ D := by have := RootedTree.depth_pos hv₀r; have := hT v₀; omega
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hOr : ∀ v ∈ O, v ≠ T.root := fun v hv => ((hO v).1 hv).1
  -- the bipartite graph `B` and its edges whose representative is not the edge-node itself
  set Bp : Finset (V × ι) := (O ×ˢ univ).filter fun q => q.2 ∈ parts T P O q.1 with hBp
  set Np := Bp.filter fun q => q.1 ∉ P q.2 with hNp
  have hm1 : Bp.card = ∑ v ∈ O, (parts T P O v).card := by
    rw [hBp, card_filter, sum_product]
    refine sum_congr rfl fun v _ => ?_
    rw [← card_filter]; congr 1; ext; simp
  have hm2 : Bp.card = ∑ i, deg i := by
    rw [hBp, card_filter, sum_product_right]
    refine sum_congr rfl fun i _ => ?_
    rw [← card_filter]
  -- (F1) every edge-node has degree `≥ c = 8δD`
  have hF1 : 8 * δ * D * O.card ≤ (Bp.card : ℝ) := by
    rw [hm1, Nat.cast_sum]
    calc 8 * δ * D * O.card = ∑ _v ∈ O, 8 * δ * D := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun v hv => ((hO v).1 hv).2
  -- (F2) many parts have degree `> 8δ`
  have hF2 : 4 * δ * Fintype.card ι < (Bp.card : ℝ) := by
    have hk : (Fintype.card ι : ℝ) ≤ 2 * bad.card := by
      have : Fintype.card ι ≤ 2 * bad.card := by omega
      exact_mod_cast this
    rw [hm2, Nat.cast_sum]
    calc 4 * δ * Fintype.card ι ≤ ∑ _i ∈ bad, 8 * δ := by
          rw [sum_const, nsmul_eq_mul]; nlinarith
      _ < ∑ i ∈ bad, (deg i : ℝ) :=
          sum_lt_sum_of_nonempty ⟨i₀, hi₀⟩ fun i hi => lt_of_not_ge (mem_filter.1 hi).2
      _ ≤ ∑ i, (deg i : ℝ) := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun _ _ _ => Nat.cast_nonneg _
  -- (F3) at most `|O|` edges of `B` have the edge-node in the part itself
  have hF3 : (Bp.card : ℝ) - O.card ≤ Np.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Bp)
      (fun q : V × ι => q.1 ∉ P q.2)
    have h2 : (Bp.filter fun q => ¬ q.1 ∉ P q.2).card ≤ O.card := by
      refine card_le_card_of_injOn Prod.fst (fun q hq => ?_) (fun q hq q' hq' h => ?_)
      · exact (mem_product.1 (mem_filter.1 (mem_filter.1 hq).1).1).1
      · simp only [coe_filter, Set.mem_ofPred_eq, not_not] at hq hq'
        have h2 : q.2 = q'.2 := by
          by_contra hne
          exact Finset.disjoint_left.1 (hP.disjoint hne) hq.2 (h ▸ hq'.2)
        exact Prod.ext h h2
    have : (Bp.card : ℝ) = Np.card + (Bp.filter fun q => ¬ q.1 ∉ P q.2).card := by
      rw [hNp]; exact_mod_cast h1.symm
    have : ((Bp.filter fun q => ¬ q.1 ∉ P q.2).card : ℝ) ≤ O.card := by exact_mod_cast h2
    linarith
  -- (F4) blockers
  have hJex : ∀ q : V × ι, ∃ J : Finset ι, q ∈ Np → (q.2 ∉ J ∧ J.card ≤ D - 1 ∧
      ∀ S : Finset ι, q.2 ∈ S → Disjoint S J → Present T P O S q.2 q.1) := by
    intro q
    by_cases hq : q ∈ Np
    · have hq1 := mem_filter.1 hq
      have hq2 := mem_filter.1 hq1.1
      obtain ⟨J, h⟩ := exists_blocker hP hT (hOr _ (mem_product.1 hq2.1).1) hq2.2 hq1.2
      exact ⟨J, fun _ => h⟩
    · exact ⟨∅, fun h => absurd h hq⟩
  choose J hJ using hJex
  -- the averaging argument
  set p : ℝ := 1 / (4 * D) with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; linarith
  set q₀ : ℝ := (1 - p) ^ (D - 1) with hq₀
  let X : Finset ι → ℝ := fun S =>
    (((S ×ˢ edgeNodes P O S).filter fun q => Present T P O S q.1 q.2).card : ℝ) -
      δ * (S.card + (edgeNodes P O S).card)
  have hX : ∀ S, X S ≤ 0 := fun S => by
    have := card_present_le hδ hP hOr S
    simp only [X]; linarith
  let ind : V × ι → Finset ι → ℝ := fun q S => if {q.2} ⊆ S ∧ Disjoint S (J q) then 1 else 0
  have hpres : ∀ S : Finset ι, ∑ q ∈ Np, ind q S ≤
      (((S ×ˢ edgeNodes P O S).filter fun q => Present T P O S q.1 q.2).card : ℝ) := by
    intro S
    have : ∑ q ∈ Np, ind q S = (Np.filter fun q => {q.2} ⊆ S ∧ Disjoint S (J q)).card := by
      simp only [ind]; rw [sum_boole]
    rw [this]
    norm_cast
    refine card_le_card_of_injOn (fun q => (q.2, q.1)) (fun q hq => ?_) (fun q _ q' _ h => ?_)
    · simp only [coe_filter, Set.mem_ofPred_eq, singleton_subset_iff] at hq
      obtain ⟨hqN, hqS, hqJ⟩ := hq
      obtain ⟨-, -, hpr⟩ := hJ q hqN
      have hpres := hpr S hqS hqJ
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product]
      refine ⟨⟨hqS, ?_⟩, hpres⟩
      obtain ⟨r, -, n, hn1, hn, -, hPS⟩ := hpres
      refine mem_filter.2 ⟨(mem_product.1 (mem_filter.1 (mem_filter.1 hqN).1).1).1, ?_⟩
      intro l hl; rw [← hn]; exact hPS n hn1 le_rfl l hl
    · simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
  have hE1 : (Np.card : ℝ) * p * q₀ ≤ ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S *
      (((S ×ˢ edgeNodes P O S).filter fun q => Present T P O S q.1 q.2).card : ℝ) := by
    calc (Np.card : ℝ) * p * q₀ = ∑ _q ∈ Np, p * q₀ := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ q ∈ Np, p ^ ({q.2} : Finset ι).card * (1 - p) ^ (J q).card := by
          refine sum_le_sum fun q hq => ?_
          rw [card_singleton, pow_one]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by linarith) (by linarith)
            (hJ q hq).2.1) hp0
      _ = ∑ q ∈ Np, ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * ind q S := by
          refine sum_congr rfl fun q hq => ?_
          rw [sum_bernWeight_indicator p {q.2} (J q)
            (disjoint_singleton_left.2 (hJ q hq).1)]
      _ = ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * ∑ q ∈ Np, ind q S := by
          rw [sum_comm]; simp_rw [mul_sum]
      _ ≤ _ := sum_le_sum fun S _ =>
          mul_le_mul_of_nonneg_left (hpres S) (bernWeight_nonneg hp0 hp1 S)
  have hE2 : ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * (S.card : ℝ) =
      Fintype.card ι * p := by
    have : ∀ S : Finset ι, (S.card : ℝ) = ∑ i, if {i} ⊆ S ∧ Disjoint S ∅ then 1 else 0 := by
      intro S; simp
    simp_rw [this, mul_sum]
    rw [sum_comm]
    simp_rw [sum_bernWeight_indicator p {_} ∅ (disjoint_empty_right _)]
    simp
  have hE3 : ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S *
      ((edgeNodes P O S).card : ℝ) ≤ O.card := by
    calc _ ≤ ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * (O.card : ℝ) :=
          sum_le_sum fun S _ => mul_le_mul_of_nonneg_left
            (by exact_mod_cast card_le_card (filter_subset _ _)) (bernWeight_nonneg hp0 hp1 S)
      _ = O.card := by rw [← sum_mul, sum_bernWeight, one_mul]
  have hq : 1 - ((D : ℝ) - 1) * (1 / (4 * D)) ≤ q₀ := by
    have := one_add_mul_le_pow (a := -p) (by linarith) (D - 1)
    rw [Nat.cast_sub hD, Nat.cast_one] at this
    rw [hq₀, sub_eq_add_neg 1 p]; rw [← hp]; linarith
  have hpos : 0 < ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * X S := by
    have hsplit : ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * X S =
        ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S *
          (((S ×ˢ edgeNodes P O S).filter fun q => Present T P O S q.1 q.2).card : ℝ) -
        δ * (∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * (S.card : ℝ) +
          ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * ((edgeNodes P O S).card : ℝ)) := by
      rw [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun S _ => ?_
      simp only [X]; ring
    have hfin := final_arith (N := (Np.card : ℝ)) (m := (Bp.card : ℝ)) (o := (O.card : ℝ))
      (k := (Fintype.card ι : ℝ)) (q₀ := q₀) hDr hδ2 (Nat.cast_nonneg _) hF3 hF1 hF2 hq
    rw [hsplit, hE2]
    rw [← hp] at hfin
    nlinarith [mul_le_mul_of_nonneg_left hE3 hδ0]
  obtain ⟨S, hS⟩ := exists_pos_of_sum_bernWeight_pos hp0 hp1 X hpos
  linarith [hX S]

end LowCongestionShortcuts
