import Papers.PODC2022.DominatingSetArboricity.Basic

/-!
# Observation A.1: dominating sets in forests

Observation A.1 of the paper: "taking all non-leaf nodes" is a single-round 3-approximation of the
minimum (unweighted) dominating set on graphs of arboricity 1.

* `obsA1_proof_alg_fails_K2`: the algorithm used in the proof ("take all non-leaf nodes") fails on
  the forest consisting of a single edge (`K₂`): both nodes are leaves, so the output is empty and
  dominates nothing. (We read "non-leaf" as "degree `≠ 1`", the reading most favourable to the
  paper; with "degree `≥ 2`" isolated vertices are missed too.) The observation itself — *some*
  single-round 3-approximation exists — is true: see `observation_A_1_fixed`.
* `observation_A_1_fixed`: the repaired algorithm — take every node of degree `≠ 1`, and in every
  `K₂` component the endpoint with the larger identifier (one round: a node needs its degree, its
  neighbours' degrees and identifiers) — is a dominating set of size at most `3 · |D|` for every
  dominating set `D`. The proof (the paper's parent/grandparent charging) only needs an orientation
  with out-degree `≤ 1`, so it holds for pseudoforests as well.
-/

set_option linter.unusedSectionVars false

namespace DominatingSetArboricity

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The paper's output: all non-leaf nodes (here: all nodes of degree `≠ 1`). -/
def nonLeaves : Finset V := univ.filter fun v => G.degree v ≠ 1

/-- The repaired output: nodes of degree `≠ 1`, plus the larger endpoint of every `K₂` component. -/
def leafFix [LinearOrder V] : Finset V :=
  univ.filter fun v => G.degree v ≠ 1 ∨ ∃ u, G.Adj v u ∧ G.degree u = 1 ∧ u < v

/-- The algorithm of the proof of Observation A.1 fails on `K₂`: the single edge is a forest
(arboricity `1`) whose set of non-leaf nodes is empty, hence not dominating. -/
theorem obsA1_proof_alg_fails_K2 :
    (⊤ : SimpleGraph (Fin 2)).ArboricityLE 1 ∧ ¬ IsDominating ⊤ (nonLeaves (⊤ : SimpleGraph (Fin 2))) := by
  refine ⟨⟨fun _ => ⊤, fun _ => le_rfl, fun _ => IsAcyclic.of_card_le_two (by simp),
    fun _ _ h => ⟨0, h⟩⟩, fun h => ?_⟩
  obtain ⟨u, hu, -⟩ := h 0
  revert hu
  fin_cases u <;> decide

variable {G}

theorem leafFix_isDominating [LinearOrder V] : IsDominating G (leafFix G) := by
  intro v
  by_cases hv : G.degree v = 1
  · obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.1 hv
    by_cases hdu : G.degree u = 1
    · rcases lt_or_gt_of_ne hu.ne with h | h
      · refine ⟨u, ?_, mem_cnbr.2 (Or.inr hu)⟩
        simp only [leafFix, mem_filter, mem_univ, true_and]
        exact Or.inr ⟨v, hu.symm, hv, h⟩
      · refine ⟨v, ?_, self_mem_cnbr v⟩
        simp only [leafFix, mem_filter, mem_univ, true_and]
        exact Or.inr ⟨u, hu, hdu, h⟩
    · exact ⟨u, by simp [leafFix, hdu], mem_cnbr.2 (Or.inr hu)⟩
  · exact ⟨v, by simp [leafFix, hv], self_mem_cnbr v⟩

theorem cnbr_eq_singleton {v : V} (h : G.degree v = 0) : cnbr G v = {v} := by
  rw [cnbr_eq_insert, ← card_neighborFinset_eq_degree, card_eq_zero] at *
  rw [h]; rfl

theorem cnbr_eq_pair {v u : V} (h : G.degree v = 1) (hu : G.Adj v u) : cnbr G v = {v, u} := by
  have : G.neighborFinset v = {u} := by
    obtain ⟨a, ha⟩ := card_eq_one.1 ((card_neighborFinset_eq_degree G v).trans h)
    have : u ∈ G.neighborFinset v := (mem_neighborFinset _ _ _).2 hu
    rw [ha] at this ⊢; rw [mem_singleton.1 this]
  rw [cnbr_eq_insert, this]

/-- `w` lies in a component with at most two vertices (an isolated vertex or a `K₂`). -/
def Small (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) : Prop :=
  G.degree w = 0 ∨ (G.degree w = 1 ∧ ∀ u, G.Adj w u → G.degree u = 1)

theorem two_le_degree_of_adj_adj {u a b : V} (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b) :
    2 ≤ G.degree u := by
  rw [← card_neighborFinset_eq_degree]
  have : ({a, b} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  simpa [card_pair hab] using card_le_card this

/-- **Observation A.1** (with a repaired algorithm): for a graph with an orientation of out-degree `≤ 1` (e.g. a
forest), `leafFix G` is a dominating set with `|leafFix G| ≤ 3 |D|` for every dominating set `D`. -/
theorem observation_A_1_fixed [LinearOrder V] (o : G.OutOrientation 1) {D : Finset V}
    (hD : IsDominating G D) :
    IsDominating G (leafFix G) ∧ (leafFix G).card ≤ 3 * D.card := by
  classical
  refine ⟨leafFix_isDominating, ?_⟩
  -- the parent/grandparent cover
  let P : V → Finset V := fun w => {w} ∪ o.out w ∪ (o.out w).biUnion o.out
  have hP : ∀ w, (P w).card ≤ 3 := by
    intro w
    have h1 := o.card_out_le w
    have h2 : ((o.out w).biUnion o.out).card ≤ 1 := by
      refine (card_biUnion_le).trans ?_
      calc ∑ a ∈ o.out w, (o.out a).card ≤ ∑ _a ∈ o.out w, 1 := sum_le_sum fun a _ => o.card_out_le a
        _ ≤ 1 := by simpa using h1
    calc (P w).card ≤ ({w} ∪ o.out w).card + ((o.out w).biUnion o.out).card := card_union_le _ _
      _ ≤ ({w} : Finset V).card + (o.out w).card + 1 := by
          gcongr; exact card_union_le _ _
      _ ≤ 3 := by simp; omega
  -- parent uniqueness: out-sets have at most one element
  have huniq : ∀ {a b c : V}, b ∈ o.out a → c ∈ o.out a → b = c := fun hb hc =>
    card_le_one.1 (o.card_out_le _) _ hb _ hc
  -- every neighbour of `v` other than its parent is a child of `v`
  have hchild : ∀ {v u : V}, G.Adj v u → u ∉ o.out v → v ∈ o.out u := fun h hu =>
    (o.mem_or_mem h).resolve_left hu
  -- vertices of degree `≥ 2`
  have hD1 : (univ.filter fun v => G.degree v ≠ 1 ∧ G.degree v ≠ 0) ⊆
      (D.filter fun w => ¬ Small G w).biUnion P := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    have hv2 : 2 ≤ G.degree v := by omega
    simp only [mem_biUnion, mem_filter]
    by_cases hvD : v ∈ D
    · exact ⟨v, ⟨hvD, fun h => by unfold Small at h; omega⟩, by simp [P]⟩
    -- a child `u` of `v`
    obtain ⟨u, hu, hu'⟩ : ∃ u, G.Adj v u ∧ u ∉ o.out v := by
      by_contra hc
      push Not at hc
      have : G.neighborFinset v ⊆ o.out v := fun u hu => hc u ((mem_neighborFinset _ _ _).1 hu)
      have := (card_le_card this).trans (o.card_out_le v)
      rw [card_neighborFinset_eq_degree] at this; omega
    have hvu : v ∈ o.out u := hchild hu hu'
    have hnsmall : ∀ {w}, G.Adj w u → w ≠ v → ¬ Small G w := by
      intro w hw hwv h
      have hu2 : 2 ≤ G.degree u := two_le_degree_of_adj_adj hu.symm hw.symm hwv.symm
      rcases h with h | ⟨-, h⟩
      · have := (G.degree_pos_iff_exists_adj w).2 ⟨u, hw⟩; omega
      · have := h u hw; omega
    by_cases huD : u ∈ D
    · refine ⟨u, ⟨huD, fun h => ?_⟩, by simp [P, hvu]⟩
      rcases h with h | ⟨-, h⟩
      · have := (G.degree_pos_iff_exists_adj u).2 ⟨v, hu.symm⟩; omega
      · have := h v hu.symm; omega
    obtain ⟨w, hwD, hw⟩ := hD u
    rcases mem_cnbr.1 hw with rfl | hw
    · exact absurd hwD huD
    have hwv : w ≠ v := fun h => hvD (h ▸ hwD)
    have huw : u ∈ o.out w := (o.mem_or_mem hw).resolve_left fun h => hwv (huniq h hvu)
    refine ⟨w, ⟨hwD, hnsmall hw.symm hwv⟩, ?_⟩
    simp only [P, mem_union, mem_singleton, mem_biUnion]
    exact Or.inr ⟨u, huw, hvu⟩
  -- isolated vertices and `K₂` components
  have hD2 : (univ.filter fun v => G.degree v = 0 ∨
      ∃ u, G.Adj v u ∧ G.degree u = 1 ∧ u < v ∧ G.degree v = 1) ⊆
      (D.filter fun w => Small G w).image fun w => (cnbr G w).max' (cnbr_nonempty w) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    simp only [mem_image, mem_filter]
    rcases hv with h0 | ⟨u, hu, hdu, hlt, hdv⟩
    · -- isolated: `v ∈ D`
      obtain ⟨w, hwD, hw⟩ := hD v
      rcases mem_cnbr.1 hw with rfl | hw
      · refine ⟨w, ⟨hwD, Or.inl h0⟩, ?_⟩
        refine le_antisymm (max'_le _ _ _ fun y hy => ?_) (le_max' _ _ (self_mem_cnbr w))
        rw [cnbr_eq_singleton h0, mem_singleton] at hy; exact hy.le
      · have := (G.degree_pos_iff_exists_adj v).2 ⟨w, hw⟩; omega
    · have hcv := cnbr_eq_pair hdv hu
      have hcu := cnbr_eq_pair hdu hu.symm
      have hsmall : ∀ {a b : V}, G.degree a = 1 → G.degree b = 1 → G.Adj a b → Small G a := by
        intro a b ha hb hab
        refine Or.inr ⟨ha, fun c hc => ?_⟩
        rw [(degree_eq_one_iff_existsUnique_adj.1 ha).unique hc hab]; exact hb
      obtain ⟨w, hwD, hw⟩ := hD v
      rw [hcv] at hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · refine ⟨w, ⟨hwD, hsmall hdv hdu hu⟩, ?_⟩
        refine le_antisymm (max'_le _ _ _ fun y hy => ?_) (le_max' _ _ (self_mem_cnbr w))
        rw [hcv] at hy; simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact le_rfl
        · exact hlt.le
      · refine ⟨w, ⟨hwD, hsmall hdu hdv hu.symm⟩, ?_⟩
        refine le_antisymm (max'_le _ _ _ fun y hy => ?_)
          (le_max' _ _ (mem_cnbr.2 (Or.inr hu.symm)))
        rw [hcu] at hy; simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hlt.le
        · exact le_rfl
  have hsplit : leafFix G ⊆ (univ.filter fun v => G.degree v ≠ 1 ∧ G.degree v ≠ 0) ∪
      (univ.filter fun v => G.degree v = 0 ∨
        ∃ u, G.Adj v u ∧ G.degree u = 1 ∧ u < v ∧ G.degree v = 1) := by
    intro v hv
    simp only [leafFix, mem_filter, mem_univ, true_and] at hv
    simp only [mem_union, mem_filter, mem_univ, true_and]
    by_cases h0 : G.degree v = 0
    · exact Or.inr (Or.inl h0)
    rcases hv with h | ⟨u, hu, hdu, hlt⟩
    · exact Or.inl ⟨h, h0⟩
    · by_cases h1 : G.degree v = 1
      · exact Or.inr (Or.inr ⟨u, hu, hdu, hlt, h1⟩)
      · exact Or.inl ⟨h1, h0⟩
  calc (leafFix G).card
      ≤ ((D.filter fun w => ¬ Small G w).biUnion P).card +
          ((D.filter fun w => Small G w).image fun w => (cnbr G w).max' (cnbr_nonempty w)).card :=
        (card_le_card hsplit).trans ((card_union_le _ _).trans
          (add_le_add (card_le_card hD1) (card_le_card hD2)))
    _ ≤ 3 * (D.filter fun w => ¬ Small G w).card + (D.filter fun w => Small G w).card := by
        refine add_le_add (card_biUnion_le.trans ?_) card_image_le
        calc ∑ w ∈ D.filter (fun w => ¬ Small G w), (P w).card
            ≤ ∑ _w ∈ D.filter (fun w => ¬ Small G w), 3 := sum_le_sum fun w _ => hP w
          _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ 3 * D.card := by
        have := card_filter_add_card_filter_not (s := D) (p := fun w => Small G w)
        omega

end DominatingSetArboricity
