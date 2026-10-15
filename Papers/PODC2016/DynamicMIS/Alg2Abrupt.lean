import Papers.PODC2016.DynamicMIS.Alg2Graceful

/-!
# Algorithm 2 after an abrupt node deletion (Section 4.2, Lemmas 11–13)

The node `x` disappears at once; if it was in the MIS, the nodes `v₁*, …, v_k*` of the first layer
`S_1` (the `M̄` nodes whose only earlier `M`-neighbour was `x`) change to `C` (`netAbrupt`,
`initAbrupt`). With `S = infl (deleteNode x) cfg r`:

* `abrupt_eq_of_notMem_infl`: only nodes of `S` ever change;
* `abrupt_stableFrom`, `abrupt_run_eq` (**Lemma 11**): stable from round `3|S|`, with the greedy MIS
  of the remaining nodes at every node `≠ x` (`…_add_two`: the paper's bound `3|S| + 2`);
* `abrupt_entry_spacing` (**Lemma 12**, first part): `C`-entries at times `t₁ < t₂` satisfy
  `t₂ ≥ 3 t₁ + 4`;
* `abrupt_card_entries_le` (**Lemma 12**, second part, and Lemma 13): a node enters `C` at most
  `min (log₃ (|S| + 1) + 1, deg x)` times;
* `abrupt_broadcasts_le` (**Lemma 13**): at most `3 |S| · min (log₃ (|S| + 1) + 1, deg x)`
  broadcasts in total.
-/

open Finset SimpleGraph

namespace DynamicMIS

namespace Alg2

variable {V : Type*} [DecidableEq V] {x : V} {cfg : Config V} {r : V → ℕ}

/-- The condition under which a node changes to `C` initially: it is one of the `v_i*`. -/
abbrev InitC (x : V) (cfg : Config V) (r : V → ℕ) (v : V) : Prop :=
  x ∈ cfg.graph.greedyMIS cfg.nodes r ∧ v ≠ x ∧
    v ∈ layer cfg.graph cfg.nodes r (cfg.graph.greedyMIS cfg.nodes r) x 1

theorem initAbrupt_eq_changing_iff {v : V} : initAbrupt x cfg r v = .changing 0 ↔ InitC x cfg r v := by
  unfold initAbrupt ofSet
  split_ifs <;> simp_all [InitC]

theorem initAbrupt_eq_inM_iff {v : V} :
    initAbrupt x cfg r v = .inM ↔ ¬ InitC x cfg r v ∧ v ∈ cfg.graph.greedyMIS cfg.nodes r := by
  unfold initAbrupt ofSet
  split_ifs <;> simp_all [InitC]

theorem initAbrupt_eq_outM_iff {v : V} :
    initAbrupt x cfg r v = .outM ↔ ¬ InitC x cfg r v ∧ v ∉ cfg.graph.greedyMIS cfg.nodes r := by
  unfold initAbrupt ofSet
  split_ifs <;> simp_all [InitC]

theorem initAbrupt_cases (v : V) : initAbrupt x cfg r v = .changing 0 ∨
    initAbrupt x cfg r v = .inM ∨ initAbrupt x cfg r v = .outM := by
  unfold initAbrupt ofSet
  split_ifs <;> simp

theorem initOK_initAbrupt : InitOK (netAbrupt x cfg r) (initAbrupt x cfg r) := fun v _ => by
  rcases initAbrupt_cases (x := x) (cfg := cfg) (r := r) v with h | h | h <;> simp [h]

omit [DecidableEq V] in
/-- The first layer: its nodes are present neighbours of `x` and influenced. -/
theorem mem_layer_one {G : SimpleGraph V} {A A' : Set V} {s : Set V} {v : V}
    (hAA' : A ⊆ A') (hs : s = G.greedyMIS A r) (h : v ∈ layer G A r s x 1) :
    v ∈ A ∧ G.Adj x v ∧ Influenced G A' r s x v := by
  rcases (mem_layer_succ (i := 0)).1 h with ⟨hvA, hvs, w, hw, hadj, hlt⟩ | ⟨hvA, hvs, hall⟩
  · rw [mem_layer_zero] at hw
    subst hw
    exact ⟨hvA, hadj, Influenced.inM (hAA' hvA) hvs hadj hlt Influenced.base⟩
  · have hx : ∀ w, G.Adj w v → r w < r v → w ∈ s → w = x := fun w hadj hlt hws => by
      obtain ⟨j, hj⟩ := hall w hadj hlt hws
      rw [show (j : ℕ) = 0 by omega, mem_layer_zero] at hj
      exact hj
    refine ⟨hvA, ?_, Influenced.inMbar (hAA' hvA) hvs fun w hadj hlt hws => by
      rw [hx w hadj hlt hws]; exact Influenced.base⟩
    rw [hs] at hvs hx
    obtain ⟨w, hw, hadj, hlt⟩ := greedyMIS_maximal _ _ _ hvA hvs
    rw [← hx w hadj hlt hw]
    exact hadj

/-- The invariants (J0)–(J2) hold initially. -/
theorem inv_initAbrupt : Inv (netAbrupt x cfg r) (initAbrupt x cfg r) := by
  set s := cfg.graph.greedyMIS cfg.nodes r with hs
  refine ⟨fun v hv hva _ => absurd hv hva, fun v hv hM u hu => ?_, fun v hv hva hM => ?_⟩
  · obtain ⟨-, h2⟩ := initAbrupt_eq_inM_iff.1 hM
    obtain ⟨hadj, -, hlt⟩ := hu
    by_cases hc : InitC x cfg r u
    · exact Or.inr (initAbrupt_eq_changing_iff.2 hc)
    · exact Or.inl (initAbrupt_eq_outM_iff.2 ⟨hc, ((greedyMIS_iff _ _ _).1 h2).2 u hadj hlt⟩)
  · obtain ⟨h1, h2⟩ := initAbrupt_eq_outM_iff.1 hM
    have hv' : v ∈ cfg.nodes ∧ v ≠ x := hv
    by_cases h : ∃ w, cfg.graph.Adj w v ∧ r w < r v ∧ w ∈ s ∧ w ≠ x
    · obtain ⟨w, hadj, hlt, hws, hwx⟩ := h
      refine ⟨w, ⟨hadj, ⟨greedyMIS_subset _ _ _ hws, hwx⟩, hlt⟩, ?_⟩
      by_cases hc : InitC x cfg r w
      · exact Or.inr (initAbrupt_eq_changing_iff.2 hc)
      · exact Or.inl (initAbrupt_eq_inM_iff.2 ⟨hc, hws⟩)
    · push Not at h
      exfalso
      obtain ⟨w, hw, hadj, hlt⟩ := greedyMIS_maximal _ _ _ hv'.1 h2
      have hwx := h w hadj hlt hw
      subst hwx
      refine h1 ⟨hw, hv'.2, (mem_layer_succ (i := 0)).2 (Or.inr ⟨hv'.1, h2, fun u hadj' hlt' hus =>
        ⟨0, mem_layer_zero.2 (h u hadj' hlt' hus)⟩⟩)⟩

theorem infl_deleteNode (hx : x ∈ cfg.graph.greedyMIS cfg.nodes r) :
    infl (.deleteNode x) cfg r = {u | Influenced cfg.graph (cfg.nodes ∪ cfg.nodes \ {x}) r
      (cfg.graph.greedyMIS cfg.nodes r) x u} := by
  simp only [infl, Change.apply, Change.vStar]
  exact ite_eq_right fun h => (h.1 hx).1.2 rfl

theorem infl_deleteNode_of_notMem (hx : x ∉ cfg.graph.greedyMIS cfg.nodes r) :
    infl (.deleteNode x) cfg r = ∅ := by
  simp only [infl, Change.apply, Change.vStar]
  exact ite_eq_left (iff_of_false hx fun h => h.1.2 rfl)

/-- The influenced set is closed under the rules used by `run_eq_of_notMem`. -/
theorem infl_closed_abrupt :
    (∀ v ∈ (netAbrupt x cfg r).part, initAbrupt x cfg r v = .changing 0 →
      v ∈ infl (.deleteNode x) cfg r) ∧
    (∀ v ∈ (netAbrupt x cfg r).part, initAbrupt x cfg r v = .inM → ∀ u,
      (netAbrupt x cfg r).Pred u v → u ∈ infl (.deleteNode x) cfg r →
        v ∈ infl (.deleteNode x) cfg r) ∧
    (∀ v ∈ (netAbrupt x cfg r).part, initAbrupt x cfg r v = .outM →
      (∃ u, (netAbrupt x cfg r).Pred u v ∧ u ∈ infl (.deleteNode x) cfg r) →
      (∀ u, (netAbrupt x cfg r).Pred u v → initAbrupt x cfg r u = .inM →
        u ∈ infl (.deleteNode x) cfg r) → v ∈ infl (.deleteNode x) cfg r) := by
  by_cases hx : x ∈ cfg.graph.greedyMIS cfg.nodes r
  · rw [infl_deleteNode hx]
    have hC : ∀ v, initAbrupt x cfg r v = .changing 0 →
        Influenced cfg.graph (cfg.nodes ∪ cfg.nodes \ {x}) r
          (cfg.graph.greedyMIS cfg.nodes r) x v := fun v h =>
      (mem_layer_one Set.subset_union_left rfl (initAbrupt_eq_changing_iff.1 h).2.2).2.2
    refine ⟨fun v _ h => hC v h, fun v hv h u ⟨hadj, _, hlt⟩ hu => ?_, fun v hv h _ hall => ?_⟩
    · exact Influenced.inM (Or.inl hv.1) (initAbrupt_eq_inM_iff.1 h).2 hadj hlt hu
    · refine Influenced.inMbar (Or.inl hv.1) (initAbrupt_eq_outM_iff.1 h).2 fun w hadj hlt hw => ?_
      by_cases hwx : w = x
      · rw [hwx]; exact Influenced.base
      by_cases hc : InitC x cfg r w
      · exact hC w (initAbrupt_eq_changing_iff.2 hc)
      · exact hall w ⟨hadj, ⟨greedyMIS_subset _ _ _ hw, hwx⟩, hlt⟩
          (initAbrupt_eq_inM_iff.2 ⟨hc, hw⟩)
  · rw [infl_deleteNode_of_notMem hx]
    refine ⟨fun v _ h => absurd (initAbrupt_eq_changing_iff.1 h).1 hx,
      fun _ _ _ _ _ h => h.elim, fun _ _ _ ⟨_, _, h⟩ _ => h.elim⟩

/-- **Only influenced nodes change their state** (abrupt deletion). -/
theorem abrupt_eq_of_notMem_infl :
    ∀ t v, v ∉ infl (.deleteNode x) cfg r →
      run (netAbrupt x cfg r) (initAbrupt x cfg r) t v = initAbrupt x cfg r v :=
  run_eq_of_notMem initOK_initAbrupt _ infl_closed_abrupt.1 infl_closed_abrupt.2.1
    infl_closed_abrupt.2.2

variable [Fintype V]

/-- **Lemma 11 (abrupt deletion): stabilisation.** The run is stable from round `3|S|`. -/
theorem abrupt_stableFrom :
    StableFrom (netAbrupt x cfg r) (initAbrupt x cfg r) (3 * (infl (.deleteNode x) cfg r).ncard) :=
  (correct initOK_initAbrupt inv_initAbrupt subset_rfl _ infl_closed_abrupt.1
    infl_closed_abrupt.2.1 infl_closed_abrupt.2.2).1

/-- **Correctness (abrupt deletion).** After `3|S|` rounds every node other than `x` is in the
state given by the greedy MIS of the remaining nodes. -/
theorem abrupt_run_eq {v : V} (hvx : v ≠ x) :
    run (netAbrupt x cfg r) (initAbrupt x cfg r) (3 * (infl (.deleteNode x) cfg r).ncard) v =
      ofSet (cfg.graph.greedyMIS (cfg.nodes \ {x}) r) v := by
  by_cases hv : v ∈ (netAbrupt x cfg r).part
  · exact (correct initOK_initAbrupt inv_initAbrupt subset_rfl _ infl_closed_abrupt.1
      infl_closed_abrupt.2.1 infl_closed_abrupt.2.2).2 v hv
  · have hvA : v ∉ cfg.nodes := fun h => hv ⟨h, hvx⟩
    rw [run_of_notMem hv]
    have h1 : initAbrupt x cfg r v = .outM := by
      rcases initAbrupt_cases (x := x) (cfg := cfg) (r := r) v with h | h | h
      · exact absurd (mem_layer_one subset_rfl rfl (initAbrupt_eq_changing_iff.1 h).2.2).1 hvA
      · exact absurd (greedyMIS_subset _ _ _ (initAbrupt_eq_inM_iff.1 h).2) hvA
      · exact h
    rw [h1, ofSet, ite_eq_right]
    exact fun h => hv (greedyMIS_subset _ _ _ h)

/-- The paper's bound for the abrupt deletion: stable from round `3|S| + 2`. -/
theorem abrupt_stableFrom_add_two :
    StableFrom (netAbrupt x cfg r) (initAbrupt x cfg r)
      (3 * (infl (.deleteNode x) cfg r).ncard + 2) := fun t ht =>
  (abrupt_stableFrom t (by omega)).trans (abrupt_stableFrom _ (by omega)).symm

omit [Fintype V] in
/-- **Lemma 12 (first part)**, abrupt deletion: if `v` changes to `C` at times `t₁ < t₂` (time `0`
= the initial changes of the `v_i*`), then `t₂ ≥ 3 t₁ + 4`. -/
theorem abrupt_entry_spacing {v : V} (hv : v ∈ (netAbrupt x cfg r).part) {t₁ t₂ : ℕ}
    (h₁ : run (netAbrupt x cfg r) (initAbrupt x cfg r) t₁ v = .changing 0)
    (h₂ : run (netAbrupt x cfg r) (initAbrupt x cfg r) t₂ v = .changing 0) (hlt : t₁ < t₂) :
    3 * t₁ + 4 ≤ t₂ :=
  entry_spacing hv h₁ h₂ hlt

/-- The initially-`C` nodes are neighbours of `x`. -/
theorem card_initC_initAbrupt_le :
    #(initC (netAbrupt x cfg r) (initAbrupt x cfg r)) ≤ (cfg.graph.neighborSet x).ncard := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun z hz => ?_) (Set.toFinite _)
  simp only [initC, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
  exact (mem_layer_one subset_rfl rfl (initAbrupt_eq_changing_iff.1 hz.2).2.2).2.1

/-- **Lemma 12 (second part) and Lemma 13**, abrupt deletion: a node changes to `C` at most
`min (log₃ (|S| + 1) + 1, deg x)` times. -/
theorem abrupt_card_entries_le {v : V} (hv : v ∈ (netAbrupt x cfg r).part) (T : ℕ) :
    #(entries (netAbrupt x cfg r) (initAbrupt x cfg r) v T) ≤
      min (Nat.log 3 ((infl (.deleteNode x) cfg r).ncard + 1) + 1)
        (cfg.graph.neighborSet x).ncard := by
  have hX := mem_of_not_isFinal (initOK_initAbrupt (x := x) (cfg := cfg) (r := r)) _
    infl_closed_abrupt.1 infl_closed_abrupt.2.1
    infl_closed_abrupt.2.2
  have h1 := card_entries_le_log hX hv T
  rw [← Set.ncard_eq_toFinset_card] at h1
  exact le_min h1 ((card_entries_le_initC hv T).trans card_initC_initAbrupt_le)

/-- **Lemma 13 (broadcasts)**, abrupt deletion: the total number of broadcasts is at most
`3 |S| · min (log₃ (|S| + 1) + 1, deg x)`. -/
theorem abrupt_broadcasts_le (T : ℕ) :
    ∑ t ∈ range T, broadcastsAt (netAbrupt x cfg r) (initAbrupt x cfg r) t ≤
      3 * (infl (.deleteNode x) cfg r).ncard *
        min (Nat.log 3 ((infl (.deleteNode x) cfg r).ncard + 1) + 1)
          (cfg.graph.neighborSet x).ncard := by
  have := sum_broadcastsAt_le initOK_initAbrupt (Set.toFinite (infl (.deleteNode x) cfg r)).toFinset
    (fun v hv t => abrupt_eq_of_notMem_infl t v (by simpa using hv)) _ T
    (fun v _ hvP => abrupt_card_entries_le hvP T)
  rwa [← Set.ncard_eq_toFinset_card] at this

end Alg2

end DynamicMIS
