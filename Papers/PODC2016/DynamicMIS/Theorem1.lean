import Papers.PODC2016.DynamicMIS.Basic

/-!
# Theorem 1: the expected number of influenced nodes is at most one

For every configuration and every topology change, `E_π[|S(G_old, G_new, π)|] ≤ 1` for a uniformly
random order `π` (`theorem1`), hence also for the number of nodes whose MIS membership changes
(`adjustments_subset_infl`, `corollary_adjustments`).

Proof structure (cf. the paper's Lemmas 2–3):
1. (`flip_data`) Let `H` be the graph without the changed edge and `A_c` the union of the old and
  new
   node sets. If the invariant breaks at `v*`, then the rule of `H[A_c]` holds at `v*` for the old
   states, i.e. `v* ∈ greedyMIS(H, A_c, π)`; the old states (and the new greedy MIS) satisfy the
   greedy rule of `H[A_c]` at every other node.
2. (`infl_eq`) Hence `S` is the three-valued influenced set of `v*` in `H[A_c]`
   (`DynamicMIS.influenced_iff`).
3. (`SimpleGraph.sum_card_influenced_le`) `E[|influenced(v*)| · 1{v* ∈ greedyMIS} · 1{v** before
  v*}]
   ≤ Pr[v** before v*]`; summing over the two possible orientations of an edge gives `≤ 1`.
-/

open Finset SimpleGraph
open scoped BigOperators

namespace DynamicMIS

variable {V : Type*} [DecidableEq V]

namespace Change

/-- The base graph `H`: the graph without the changed edge (the old graph for node changes). -/
def baseGraph : Change V → Config V → SimpleGraph V
  | insertEdge a b, c | deleteEdge a b, c => c.graph.deleteEdges {s(a, b)}
  | insertNode _, c | deleteNode _, c => c.graph

/-- The base node set: the union of the old and new node sets. -/
def baseNodes (c : Change V) (cfg : Config V) : Set V := cfg.nodes ∪ (c.apply cfg).nodes

end Change

section Edge

variable {X H : SimpleGraph V} {a b : V} {r : V → ℕ}

omit [DecidableEq V] in
/-- Away from `v*` (the later endpoint), adding/removing the edge `ab` does not change predecessor
sets. -/
theorem pred_iff_of_diff (hr : Function.Injective r) (hle : H ≤ X)
    (hdiff : ∀ w u, X.Adj w u → ¬ H.Adj w u → s(w, u) = s(a, b)) :
    ∀ u, u ≠ (if r a < r b then b else a) → ∀ w,
      (X.Adj w u ∧ r w < r u) ↔ (H.Adj w u ∧ r w < r u) := by
  intro u hu w
  refine ⟨fun ⟨hX, hlt⟩ => ⟨by_contra fun hH => ?_, hlt⟩, fun ⟨hH, hlt⟩ => ⟨hle hH, hlt⟩⟩
  have := hdiff w u hX hH
  rw [Sym2.eq_iff] at this
  have hne : r a ≠ r b := by
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr.ne hX.ne
    · exact hr.ne hX.ne.symm
  split_ifs at hu with hab <;> rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | exact absurd rfl hu | omega

omit [DecidableEq V] in
/-- If the rules at `v` in `G₁` and `G₂` (both containing `H`) disagree, then the changed edge joins
`v` to an earlier node. -/
theorem exists_of_rule_ne {G₁ G₂ : SimpleGraph V} {A : Set V} {s : Set V} {v : V}
    (h₁ : H ≤ G₁) (h₂ : H ≤ G₂)
    (hd₁ : ∀ w u, G₁.Adj w u → ¬ H.Adj w u → s(w, u) = s(a, b))
    (hd₂ : ∀ w u, G₂.Adj w u → ¬ H.Adj w u → s(w, u) = s(a, b))
    (hne : ¬ ((v ∈ A ∧ ∀ w, G₁.Adj w v → r w < r v → w ∉ s) ↔
      (v ∈ A ∧ ∀ w, G₂.Adj w v → r w < r v → w ∉ s))) :
    ∃ w, r w < r v ∧ s(w, v) = s(a, b) ∧ w ≠ v := by
  by_contra hcon
  push Not at hcon
  apply hne
  have key : ∀ (X : SimpleGraph V), H ≤ X → (∀ w u, X.Adj w u → ¬ H.Adj w u → s(w, u) = s(a, b)) →
      ∀ w, X.Adj w v → r w < r v → H.Adj w v := fun X hX hd w hw hr =>
    by_contra fun hH => hw.ne (hcon w hr (hd w v hw hH))
  constructor
  · rintro ⟨hA, h⟩
    exact ⟨hA, fun w hw hr => h w (h₁ (key G₂ h₂ hd₂ w hw hr)) hr⟩
  · rintro ⟨hA, h⟩
    exact ⟨hA, fun w hw hr => h w (h₂ (key G₁ h₁ hd₁ w hw hr)) hr⟩

end Edge

/-- All the information about a single change needed for Theorem 1, for an injective order. -/
structure FlipData (c : Change V) (cfg : Config V) (r : V → ℕ) : Prop where
  /-- Off `v*`, the old graph has the predecessors of the base graph. -/
  pred_old : ∀ u, u ≠ c.vStar r → ∀ w,
    (cfg.graph.Adj w u ∧ r w < r u) ↔ ((c.baseGraph cfg).Adj w u ∧ r w < r u)
  /-- Off `v*`, the new graph has the predecessors of the base graph. -/
  pred_new : ∀ u, u ≠ c.vStar r → ∀ w,
    ((c.apply cfg).graph.Adj w u ∧ r w < r u) ↔ ((c.baseGraph cfg).Adj w u ∧ r w < r u)
  /-- Off `v*`, the old nodes are the base nodes. -/
  nodes_old : ∀ u, u ≠ c.vStar r → (u ∈ cfg.nodes ↔ u ∈ c.baseNodes cfg)
  /-- Off `v*`, the new nodes are the base nodes. -/
  nodes_new : ∀ u, u ≠ c.vStar r → (u ∈ (c.apply cfg).nodes ↔ u ∈ c.baseNodes cfg)
  /-- If the invariant breaks at `v*`, the base rule holds at `v*` for the old states. -/
  rule : ¬ InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r (cfg.graph.greedyMIS cfg.nodes r)
      (c.vStar r) →
    c.vStar r ∈ c.baseNodes cfg ∧ ∀ w, (c.baseGraph cfg).Adj w (c.vStar r) →
      r w < r (c.vStar r) → w ∉ cfg.graph.greedyMIS cfg.nodes r

theorem flipData (c : Change V) (cfg : Config V) {r : V → ℕ} (hr : Function.Injective r) :
    FlipData c cfg r := by
  obtain ⟨G, A⟩ := cfg
  cases c with
  | insertEdge a b =>
    have hle : G.deleteEdges {s(a, b)} ≤ G := deleteEdges_le _
    have hdG : ∀ w u, G.Adj w u → ¬ (G.deleteEdges {s(a, b)}).Adj w u → s(w, u) = s(a, b) :=
      fun w u h1 h2 => by_contra fun h => h2 (SimpleGraph.deleteEdges_adj.2 ⟨h1, by simpa using h⟩)
    have hdG' : ∀ w u, (G ⊔ edge a b).Adj w u → ¬ (G.deleteEdges {s(a, b)}).Adj w u →
        s(w, u) = s(a, b) := fun w u h1 h2 => by
      rcases (sup_adj _ _ _ _).1 h1 with h | h
      · exact hdG w u h h2
      · rw [edge_adj] at h
        rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
    have hle' : G.deleteEdges {s(a, b)} ≤ G ⊔ edge a b := hle.trans le_sup_left
    refine ⟨pred_iff_of_diff hr hle hdG, pred_iff_of_diff hr hle' hdG', fun u _ => ?_,
      fun u _ => ?_, fun hflip => ?_⟩
    · simp [Change.baseNodes, Change.apply]
    · simp [Change.baseNodes, Change.apply]
    · simp only [Change.baseNodes, Change.apply, Set.union_self, Change.baseGraph, Change.vStar]
        at hflip ⊢
      unfold InvariantAt at hflip
      rw [greedyMIS_iff] at hflip
      by_cases h₁ : (if r a < r b then b else a) ∈ A ∧ ∀ w, G.Adj w (if r a < r b then b else a) →
          r w < r (if r a < r b then b else a) → w ∉ G.greedyMIS A r
      · exact ⟨h₁.1, fun w hw hr' => h₁.2 w (hle hw) hr'⟩
      · have h₂ := by_contra fun h => hflip (iff_of_false h₁ h)
        exact ⟨h₂.1, fun w hw hr' => h₂.2 w (hle' hw) hr'⟩
  | deleteEdge a b =>
    have hle : G.deleteEdges {s(a, b)} ≤ G := deleteEdges_le _
    have hdG : ∀ w u, G.Adj w u → ¬ (G.deleteEdges {s(a, b)}).Adj w u → s(w, u) = s(a, b) :=
      fun w u h1 h2 => by_contra fun h => h2 (SimpleGraph.deleteEdges_adj.2 ⟨h1, by simpa using h⟩)
    have hdG' : ∀ w u, (G.deleteEdges {s(a, b)}).Adj w u →
        ¬ (G.deleteEdges {s(a, b)}).Adj w u → s(w, u) = s(a, b) :=
      fun w u h1 h2 => absurd h1 h2
    refine ⟨pred_iff_of_diff hr hle hdG, pred_iff_of_diff hr le_rfl hdG', fun u _ => ?_,
      fun u _ => ?_, fun hflip => ?_⟩
    · simp [Change.baseNodes, Change.apply]
    · simp [Change.baseNodes, Change.apply]
    · simp only [Change.baseNodes, Change.apply, Set.union_self, Change.baseGraph, Change.vStar]
        at hflip ⊢
      unfold InvariantAt at hflip
      rw [greedyMIS_iff] at hflip
      by_cases h₁ : (if r a < r b then b else a) ∈ A ∧ ∀ w, G.Adj w (if r a < r b then b else a) →
          r w < r (if r a < r b then b else a) → w ∉ G.greedyMIS A r
      · exact ⟨h₁.1, fun w hw hr' => h₁.2 w (hle hw) hr'⟩
      · have h₂ := by_contra fun h => hflip (iff_of_false h₁ h)
        exact ⟨h₂.1, h₂.2⟩
  | insertNode x =>
    refine ⟨fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun u hu => ?_, fun u hu => ?_,
      fun hflip => ?_⟩
    · simp [Change.baseNodes, Change.apply, Change.vStar] at hu ⊢; tauto
    · simp [Change.baseNodes, Change.apply, Change.vStar] at hu ⊢
    · simp only [Change.baseNodes, Change.apply, Change.baseGraph, Change.vStar] at hflip ⊢
      unfold InvariantAt at hflip
      rw [greedyMIS_iff] at hflip
      by_cases h : ∀ w, G.Adj w x → r w < r x → w ∉ G.greedyMIS A r
      · exact ⟨Or.inr (Set.mem_insert x A), h⟩
      · exact absurd (iff_of_false (fun h' => h h'.2) (fun h' => h h'.2)) hflip
  | deleteNode x =>
    refine ⟨fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun u hu => ?_, fun u hu => ?_,
      fun hflip => ?_⟩
    · simp [Change.baseNodes, Change.apply, Change.vStar] at hu ⊢; tauto
    · simp [Change.baseNodes, Change.apply, Change.vStar] at hu ⊢; tauto
    · simp only [Change.baseNodes, Change.apply, Change.baseGraph, Change.vStar] at hflip ⊢
      unfold InvariantAt at hflip
      rw [greedyMIS_iff] at hflip
      by_cases h : x ∈ A ∧ ∀ w, G.Adj w x → r w < r x → w ∉ G.greedyMIS A r
      · exact ⟨Or.inl h.1, h.2⟩
      · exact absurd (iff_of_false h (fun h' => h'.1.2 rfl)) hflip

section Reduction

variable {c : Change V} {cfg : Config V} {r : V → ℕ}

/-- The greedy rule at `u ≠ v*` in the old configuration is the rule of the base configuration. -/
theorem FlipData.rule_old_iff (hd : FlipData c cfg r) {u : V} (hu : u ≠ c.vStar r) (s : Set V) :
    (u ∈ cfg.nodes ∧ ∀ w, cfg.graph.Adj w u → r w < r u → w ∉ s) ↔
      (u ∈ c.baseNodes cfg ∧ ∀ w, (c.baseGraph cfg).Adj w u → r w < r u → w ∉ s) := by
  rw [hd.nodes_old u hu]
  refine and_congr_right fun _ => forall_congr' fun w => ?_
  have := hd.pred_old u hu w
  exact ⟨fun h hH hr => h (this.2 ⟨hH, hr⟩).1 hr, fun h hG hr => h (this.1 ⟨hG, hr⟩).1 hr⟩

/-- The greedy rule at `u ≠ v*` in the new configuration is the rule of the base configuration. -/
theorem FlipData.rule_new_iff (hd : FlipData c cfg r) {u : V} (hu : u ≠ c.vStar r) (s : Set V) :
    (u ∈ (c.apply cfg).nodes ∧ ∀ w, (c.apply cfg).graph.Adj w u → r w < r u → w ∉ s) ↔
      (u ∈ c.baseNodes cfg ∧ ∀ w, (c.baseGraph cfg).Adj w u → r w < r u → w ∉ s) := by
  rw [hd.nodes_new u hu]
  refine and_congr_right fun _ => forall_congr' fun w => ?_
  have := hd.pred_new u hu w
  exact ⟨fun h hH hr => h (this.2 ⟨hH, hr⟩).1 hr, fun h hG hr => h (this.1 ⟨hG, hr⟩).1 hr⟩

theorem FlipData.isGreedyExcept_old (hd : FlipData c cfg r) :
    (c.baseGraph cfg).IsGreedyExcept (c.baseNodes cfg) r (c.vStar r)
      (cfg.graph.greedyMIS cfg.nodes r) := fun u hu => by
  rw [greedyMIS_iff]; exact hd.rule_old_iff hu _

theorem FlipData.isGreedyExcept_new (hd : FlipData c cfg r) :
    (c.baseGraph cfg).IsGreedyExcept (c.baseNodes cfg) r (c.vStar r)
      ((c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r) := fun u hu => by
  rw [greedyMIS_iff]; exact hd.rule_new_iff hu _

theorem infl_eq_empty (h : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r
    (cfg.graph.greedyMIS cfg.nodes r) (c.vStar r)) : infl c cfg r = ∅ := by
  simp only [infl]; exact ite_eq_left h

/-- **Lemma 2 (made precise).** If the invariant breaks at `v*`, then `v*` is in the greedy MIS of
the base configuration and `S` is the influenced set of `v*` there. -/
theorem infl_eq (hr : Function.Injective r)
    (h : ¬ InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r
      (cfg.graph.greedyMIS cfg.nodes r) (c.vStar r)) :
    c.vStar r ∈ (c.baseGraph cfg).greedyMIS (c.baseNodes cfg) r ∧
      infl c cfg r = (c.baseGraph cfg).influenced (c.baseNodes cfg) r (c.vStar r) := by
  have hd := flipData c cfg hr
  refine ⟨(greedyRule_iff_mem_greedyMIS hd.isGreedyExcept_old).1 (hd.rule h), ?_⟩
  simp only [infl]
  rw [ite_eq_right h]
  have hs : (c.apply cfg).graph.IsGreedyExcept (c.baseNodes cfg) r (c.vStar r)
      (cfg.graph.greedyMIS cfg.nodes r) := fun u hu => by
    rw [hd.isGreedyExcept_old u hu, ← hd.rule_new_iff hu, hd.nodes_new u hu]
  have hcongr : (c.apply cfg).graph.partialGreedy (c.baseNodes cfg) r (c.vStar r) =
      (c.baseGraph cfg).partialGreedy (c.baseNodes cfg) r (c.vStar r) :=
    partialGreedy_congr (fun _ _ => Iff.rfl) hd.pred_new
  ext u
  change Influenced _ (cfg.nodes ∪ (c.apply cfg).nodes) _ _ _ u ↔ _
  rw [show cfg.nodes ∪ (c.apply cfg).nodes = c.baseNodes cfg from rfl, influenced_iff hs]
  simp only [influenced, hcongr]

/-- The nodes whose MIS membership differs between the old and the new greedy MIS (the
"adjustments"). -/
def adjustments (c : Change V) (cfg : Config V) (r : V → ℕ) : Set V :=
  {v | ¬ (v ∈ cfg.graph.greedyMIS cfg.nodes r ↔
    v ∈ (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r)}

/-- Every node that changes its MIS membership is influenced (and nothing changes if the invariant
still holds at `v*`). -/
theorem adjustments_subset_infl (hr : Function.Injective r) :
    adjustments c cfg r ⊆ infl c cfg r := by
  have hd := flipData c cfg hr
  by_cases h : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r
      (cfg.graph.greedyMIS cfg.nodes r) (c.vStar r)
  · have heq : cfg.graph.greedyMIS cfg.nodes r =
        (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r := by
      refine eq_greedyMIS_of_isGreedy _ _ _ fun u => ?_
      by_cases hu : u = c.vStar r
      · subst hu; exact h
      · rw [hd.isGreedyExcept_old u hu, ← hd.rule_new_iff hu]
    intro u hu
    exact absurd (by rw [heq]) hu
  · rw [(infl_eq hr h).2]
    intro u hu
    by_cases h₁ : u ∈ cfg.graph.greedyMIS cfg.nodes r
    · exact mem_influenced_of_mem_of_notMem hd.isGreedyExcept_old hd.isGreedyExcept_new h₁
        fun h₂ => hu (iff_of_true h₁ h₂)
    · exact mem_influenced_of_mem_of_notMem hd.isGreedyExcept_new hd.isGreedyExcept_old
        (by_contra fun h₂ => hu (iff_of_false h₁ h₂)) h₁

/-- For an edge change, a broken invariant forces two distinct endpoints. -/
theorem ne_of_not_invariant_edge {a b : V} (hc : c = .insertEdge a b ∨ c = .deleteEdge a b)
    (h : ¬ InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r
      (cfg.graph.greedyMIS cfg.nodes r) (c.vStar r)) : a ≠ b := by
  rintro rfl
  apply h
  have : c.apply cfg = cfg := by
    rcases hc with rfl | rfl
    · simp [Change.apply, edge_self_eq_bot]
    · simp only [Change.apply]
      congr 1
      rw [deleteEdges_eq_self, Set.disjoint_singleton_right]
      exact cfg.graph.loopless.irrefl a ∘ (mem_edgeSet _).1
  rw [this]
  exact greedyMIS_iff _ _ _

end Reduction

/-! ### Theorem 1 -/

section Main

variable [Fintype V]

open Classical in
/-- The bound used for edge changes: the contribution of the orientation "`y` before `x`". -/
noncomputable def edgeTerm (H : SimpleGraph V) (A : Set V) (π : V ≃ Fin (Fintype.card V))
    (x y : V) : ℕ :=
  if (∀ y' ∈ ({y} : Finset V), π y' < π x) ∧ x ∈ H.greedyMIS A (orderRank π) then
    (H.influenced A (orderRank π) x).toFinset.card else 0

open Classical in
theorem ncard_infl_le_node (c : Change V) (cfg : Config V) (π : V ≃ Fin (Fintype.card V)) :
    (infl c cfg (orderRank π)).ncard ≤
      if (∀ y ∈ (∅ : Finset V), π y < π (c.vStar (orderRank π))) ∧
          c.vStar (orderRank π) ∈ (c.baseGraph cfg).greedyMIS (c.baseNodes cfg) (orderRank π) then
        ((c.baseGraph cfg).influenced (c.baseNodes cfg) (orderRank π)
          (c.vStar (orderRank π))).toFinset.card else 0 := by
  by_cases h : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes (orderRank π)
      (cfg.graph.greedyMIS cfg.nodes (orderRank π)) (c.vStar (orderRank π))
  · rw [infl_eq_empty h]; simp
  · obtain ⟨h₁, h₂⟩ := infl_eq (orderRank_injective π) h
    rw [h₂, ite_eq_left ⟨by simp, h₁⟩, Set.ncard_eq_toFinset_card']

theorem sum_le_factorial_node {x : V} (c : Change V) (hc : c = .insertNode x ∨ c = .deleteNode x)
    (cfg : Config V) :
    ∑ π : V ≃ Fin (Fintype.card V), (infl c cfg (orderRank π)).ncard ≤
      (Fintype.card V).factorial := by
  have key : #(univ.filter fun π : V ≃ Fin (Fintype.card V) => ∀ y ∈ (∅ : Finset V), π y < π x)
      ≤ (Fintype.card V).factorial :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_equiv (Fintype.equivFin V))
  rcases hc with rfl | rfl
  · exact (Finset.sum_le_sum fun π _ => ncard_infl_le_node _ cfg π).trans
      ((sum_card_influenced_le x ∅).trans key)
  · exact (Finset.sum_le_sum fun π _ => ncard_infl_le_node _ cfg π).trans
      ((sum_card_influenced_le x ∅).trans key)

theorem ncard_infl_le_edge {a b : V} (c : Change V) (hc : c = .insertEdge a b ∨ c = .deleteEdge a b)
    (cfg : Config V) (π : V ≃ Fin (Fintype.card V)) :
    (infl c cfg (orderRank π)).ncard ≤
      edgeTerm (c.baseGraph cfg) (c.baseNodes cfg) π b a +
        edgeTerm (c.baseGraph cfg) (c.baseNodes cfg) π a b := by
  classical
  by_cases h : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes (orderRank π)
      (cfg.graph.greedyMIS cfg.nodes (orderRank π)) (c.vStar (orderRank π))
  · rw [infl_eq_empty h]; simp
  have hab := ne_of_not_invariant_edge hc h
  obtain ⟨h₁, h₂⟩ := infl_eq (orderRank_injective π) h
  rw [h₂, Set.ncard_eq_toFinset_card']
  have hv : c.vStar (orderRank π) = if π a < π b then b else a := by
    rcases hc with rfl | rfl <;> simp [Change.vStar, orderRank]
  by_cases hlt : π a < π b
  · rw [hv, ite_eq_left hlt] at h₁ ⊢
    refine le_trans (le_of_eq ?_) (Nat.le_add_right _ _)
    rw [edgeTerm, ite_eq_left ⟨by simpa using hlt, h₁⟩]
  · rw [hv, ite_eq_right hlt] at h₁ ⊢
    have hlt' : π b < π a :=
      lt_of_le_of_ne (not_lt.1 hlt) fun he => hab (π.injective he).symm
    refine le_trans (le_of_eq ?_) (Nat.le_add_left _ _)
    rw [edgeTerm, ite_eq_left ⟨by simpa using hlt', h₁⟩]

theorem sum_le_factorial_edge {a b : V} (c : Change V)
    (hc : c = .insertEdge a b ∨ c = .deleteEdge a b) (cfg : Config V) :
    ∑ π : V ≃ Fin (Fintype.card V), (infl c cfg (orderRank π)).ncard ≤
      (Fintype.card V).factorial := by
  classical
  refine (Finset.sum_le_sum fun π _ => ncard_infl_le_edge c hc cfg π).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 := sum_card_influenced_le (G := c.baseGraph cfg) (A := c.baseNodes cfg) b {a}
  have h2 := sum_card_influenced_le (G := c.baseGraph cfg) (A := c.baseNodes cfg) a {b}
  simp only [edgeTerm]
  refine (add_le_add h1 h2).trans ?_
  simp only [Finset.mem_singleton, forall_eq]
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (V ≃ Fin (Fintype.card V))))
    (fun π => π a < π b)
  rw [Finset.card_univ, Fintype.card_equiv (Fintype.equivFin V)] at this
  rw [← this]
  refine add_le_add le_rfl (Finset.card_le_card fun π => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  exact le_of_lt

/-- Sum form of **Theorem 1**: `∑_π |S(G_old, G_new, π)| ≤ |V|!`. -/
theorem sum_ncard_infl_le (c : Change V) (cfg : Config V) :
    ∑ π : V ≃ Fin (Fintype.card V), (infl c cfg (orderRank π)).ncard ≤
      (Fintype.card V).factorial := by
  cases c with
  | insertEdge a b => exact sum_le_factorial_edge _ (Or.inl rfl) cfg
  | deleteEdge a b => exact sum_le_factorial_edge _ (Or.inr rfl) cfg
  | insertNode x => exact sum_le_factorial_node _ (Or.inl rfl) cfg
  | deleteNode x => exact sum_le_factorial_node _ (Or.inr rfl) cfg

theorem expect_le_one_of_sum_le {f : (V ≃ Fin (Fintype.card V)) → ℕ}
    (h : ∑ π, f π ≤ (Fintype.card V).factorial) : 𝔼 π, (f π : ℚ) ≤ 1 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_equiv (Fintype.equivFin V)]
  rw [div_le_one (by positivity)]
  exact_mod_cast h

/-- **Theorem 1** (Censor-Hillel–Haramaty–Karnin, PODC 2016). For every configuration and every
single topology change (edge or node insertion or deletion), the expected size of the set
`S(G_old, G_new, π)` of influenced nodes, over a uniformly random order `π`, is at most `1`. -/
theorem theorem1 (c : Change V) (cfg : Config V) :
    𝔼 π : V ≃ Fin (Fintype.card V), ((infl c cfg (orderRank π)).ncard : ℚ) ≤ 1 :=
  expect_le_one_of_sum_le (sum_ncard_infl_le c cfg)

/-- **Adjustments** (Theorem 1 / Corollary 6): the expected number of nodes whose membership in the
(random greedy) MIS changes after one topology change is at most `1`. -/
theorem expected_adjustments_le_one (c : Change V) (cfg : Config V) :
    𝔼 π : V ≃ Fin (Fintype.card V), ((adjustments c cfg (orderRank π)).ncard : ℚ) ≤ 1 :=
  expect_le_one_of_sum_le ((Finset.sum_le_sum fun π _ =>
    Set.ncard_le_ncard (adjustments_subset_infl (orderRank_injective π))).trans
      (sum_ncard_infl_le c cfg))

end Main

end DynamicMIS
