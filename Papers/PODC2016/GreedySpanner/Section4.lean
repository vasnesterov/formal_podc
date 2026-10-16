import Papers.PODC2016.GreedySpanner.Theorem5

/-!
# Section 4: the greedy spanner in doubling metrics

A finite metric space is a weight function `w : Sym2 V → ℝ≥0` on the complete graph `⊤`
(`IsMetricW`: zero on the diagonal, positive off it, triangle inequality); the paper also views a
metric space as a complete weighted graph. For a subgraph `H`, the *induced metric* `M_H` is the
complete graph with weights `inducedW H w (xy) = δ_H(x, y)`.

* `lemma5` — `H` the greedy `t`-spanner, `H'` any `t`-spanner of `M_H`: `w(H) ≤ w_{M_H}(H')`.
* `lemma6` — for `1 ≤ t < 2` and positive weights: `|H| ≤ |H'|`.
  Both are proved for an arbitrary connected weighted graph `G` instead of a metric (the proofs do
  not use the triangle inequality of `G`), so they also hold verbatim for metrics (`G = ⊤`).
* `IsDoubling w D` — every ball of radius `r` is covered by `≤ 2^D` balls of radius `r/2`
  (doubling dimension `≤ D`). `observation7` — if `H` is a `t`-spanner of a metric of doubling
  dimension `≤ D` and `t ≤ 2`, then `M_H` is a metric of doubling dimension `≤ 2D`.
* `theorem6` — for a metric of doubling dimension `≤ D` and `1 ≤ t < 2`, the greedy `t`-spanner has
  at most `OPT_t^sparse(M(n, 2D))` edges and lightness at most `OPT_t^light(M(n, 2D))`.
* `corollary3_of_forall_exists` — Corollary 3 with the cited Theorem 4 [Got15] as a hypothesis.
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace GreedySpanner

variable {V : Type*} {G H K : SimpleGraph V} {w : Sym2 V → ℝ≥0} {t : ℝ≥0}

/-! ### Finiteness of distances -/

lemma Walk.wlength_lt_top {u v : V} (p : G.Walk u v) : p.wlength w < ⊤ := by
  induction p with
  | nil => simp
  | cons h q ih => rw [Walk.wlength_cons]; exact ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ih⟩

lemma wdist_lt_top_of_reachable {u v : V} (h : G.Reachable u v) : G.wdist w u v < ⊤ :=
  (wdist_le h.some).trans_lt (Walk.wlength_lt_top _)

lemma IsWSpanner.reachable (hH : IsWSpanner G H w t) {u v : V} (h : G.Reachable u v) :
    H.Reachable u v :=
  reachable_of_wdist_lt_top ((hH.2 u v).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (wdist_lt_top_of_reachable h)))

-- CSLib candidate
/-- Comparing distances under two weight functions along a walk. -/
lemma wdist_le_wlength_of_edges {K' : SimpleGraph V} {w₁ w₂ : Sym2 V → ℝ≥0} {u v : V}
    (p : K'.Walk u v) (h : ∀ a b, s(a, b) ∈ p.edges → K.wdist w₁ a b ≤ w₂ s(a, b)) :
    K.wdist w₁ u v ≤ p.wlength w₂ := by
  induction p with
  | nil => exact (wdist_le (Walk.nil : K.Walk _ _)).trans (by simp)
  | @cons a b c hab q ih =>
    rw [Walk.wlength_cons]
    calc K.wdist w₁ a c ≤ K.wdist w₁ a b + K.wdist w₁ b c := wdist_triangle
      _ ≤ w₂ s(a, b) + q.wlength w₂ :=
        add_le_add (h a b (by simp)) (ih fun x y hxy => h x y (by simp [hxy]))

lemma wdist_le_wdist_of_edges {K' : SimpleGraph V} {w₁ w₂ : Sym2 V → ℝ≥0} {u v : V}
    (h : ∀ a b, K'.Adj a b → K.wdist w₁ a b ≤ w₂ s(a, b)) :
    K.wdist w₁ u v ≤ K'.wdist w₂ u v :=
  le_iInf fun p => wdist_le_wlength_of_edges p fun a b hab => h a b (p.adj_of_mem_edges hab)

/-! ### The induced metric `M_H` -/

/-- The weights of the metric `M_H` induced by `H`: `xy ↦ δ_H(x, y)`. -/
noncomputable def inducedW (H : SimpleGraph V) (w : Sym2 V → ℝ≥0) : Sym2 V → ℝ≥0 :=
  fun e => (H.wdistS w e).toNNReal

lemma coe_inducedW {x y : V} (h : H.Reachable x y) :
    (inducedW H w s(x, y) : ℝ≥0∞) = H.wdist w x y :=
  ENNReal.coe_toNNReal (wdist_lt_top_of_reachable h).ne

lemma top_wdist_le {w' : Sym2 V → ℝ≥0} {x y : V} (hxy : x ≠ y) :
    (⊤ : SimpleGraph V).wdist w' x y ≤ w' s(x, y) :=
  wdist_le_of_adj (by simpa using hxy)

/-- A `t`-spanner `H'` of `M_H` satisfies `δ_{H'}^{M_H}(x, y) ≤ t · w(xy)` on the edges of `H`. -/
lemma wdist_inducedW_le_of_adj (hHc : ∀ x y, H.Reachable x y)
    {H' : SimpleGraph V} (hH' : IsWSpanner ⊤ H' (inducedW H w) t) {x y : V} (hxy : H.Adj x y) :
    H'.wdist (inducedW H w) x y ≤ t * w s(x, y) := by
  calc H'.wdist (inducedW H w) x y ≤ t * (⊤ : SimpleGraph V).wdist (inducedW H w) x y := hH'.2 x y
    _ ≤ t * inducedW H w s(x, y) := by gcongr; exact top_wdist_le hxy.ne
    _ = t * H.wdist w x y := by rw [coe_inducedW (hHc x y)]
    _ ≤ t * w s(x, y) := by gcongr; exact wdist_le_of_adj hxy

/-! ### Shortest paths in `H`, one per pair -/

section ShortestPaths

variable [Finite V] [DecidableEq V]

variable (H w) in
lemma exists_spEdges (hHc : ∀ x y, H.Reachable x y) (e : Sym2 V) :
    ∃ S : Finset (Sym2 V), ∀ x y, e = s(x, y) →
      ∃ p : H.Walk x y, p.IsPath ∧ p.edges.toFinset = S ∧ p.wlength w = H.wdist w x y := by
  induction e using Sym2.ind with
  | _ a b =>
  obtain ⟨p, hp, hpw⟩ := exists_isPath_wlength_eq (w := w) (hHc a b)
  refine ⟨p.edges.toFinset, fun x y hxy => ?_⟩
  rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨p, hp, rfl, hpw⟩
  · exact ⟨p.reverse, hp.reverse, by simp [Walk.edges_reverse],
      by rw [Walk.wlength_reverse, hpw, wdist_comm]⟩

variable (H w) in
/-- The edge set `P_e` of a fixed shortest path in `H` between the endpoints of `e`. -/
noncomputable def spEdges (hHc : ∀ x y, H.Reachable x y) (e : Sym2 V) : Finset (Sym2 V) :=
  (exists_spEdges H w hHc e).choose

lemma spEdges_spec (hHc : ∀ x y, H.Reachable x y) {x y : V} :
    ∃ p : H.Walk x y, p.IsPath ∧ p.edges.toFinset = spEdges H w hHc s(x, y) ∧
      p.wlength w = H.wdist w x y :=
  (exists_spEdges H w hHc s(x, y)).choose_spec x y rfl

lemma spEdges_subset (hHc : ∀ x y, H.Reachable x y) (e : Sym2 V) :
    ↑(spEdges H w hHc e) ⊆ H.edgeSet := by
  induction e using Sym2.ind with
  | _ x y =>
  obtain ⟨p, -, hpS, -⟩ := spEdges_spec (w := w) hHc (x := x) (y := y)
  intro f hf
  rw [Finset.mem_coe, ← hpS, List.mem_toFinset] at hf
  exact p.edges_subset_edgeSet hf

lemma sum_spEdges (hHc : ∀ x y, H.Reachable x y) (x y : V) :
    ∑ f ∈ spEdges H w hHc s(x, y), (w f : ℝ≥0∞) = H.wdist w x y := by
  obtain ⟨p, hp, hpS, hpw⟩ := spEdges_spec (w := w) hHc (x := x) (y := y)
  rw [← hpS, List.sum_toFinset _ hp.isTrail.edges_nodup, ← hpw]
  rfl

lemma sum_spEdges' (hHc : ∀ x y, H.Reachable x y) (e : Sym2 V) :
    ∑ f ∈ spEdges H w hHc e, (w f : ℝ≥0∞) = inducedW H w e := by
  induction e using Sym2.ind with
  | _ x y => rw [sum_spEdges, coe_inducedW (hHc x y)]

/-- Any graph containing `P_{xy}` has `δ(x, y) ≤ δ_H(x, y)`. -/
lemma wdist_le_of_spEdges_subset (hHc : ∀ x y, H.Reachable x y) {x y : V}
    (hK : ↑(spEdges H w hHc s(x, y)) ⊆ K.edgeSet) : K.wdist w x y ≤ H.wdist w x y := by
  obtain ⟨p, -, hpS, hpw⟩ := spEdges_spec (w := w) hHc (x := x) (y := y)
  have hsub : ∀ f ∈ p.edges, f ∈ K.edgeSet := fun f hf =>
    hK (by rw [Finset.mem_coe, ← hpS, List.mem_toFinset]; exact hf)
  calc K.wdist w x y ≤ (p.transfer K hsub).wlength w := wdist_le _
    _ = H.wdist w x y := by rw [Walk.wlength_transfer, hpw]

end ShortestPaths

lemma wt_eq_sum [Fintype V] (w : Sym2 V → ℝ≥0) (H : SimpleGraph V)
    [DecidablePred (· ∈ H.edgeSet)] :
    wt w H = ∑ e ∈ univ.filter (· ∈ H.edgeSet), (w e : ℝ≥0∞) := by
  rw [wt, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Set.indicator_apply]

lemma sum_biUnion_le' {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β)
    (g : β → ℝ≥0∞) : ∑ x ∈ s.biUnion t, g x ≤ ∑ a ∈ s, ∑ x ∈ t a, g x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    calc _ ≤ ∑ x ∈ t a, g x + ∑ x ∈ s.biUnion t, g x := by
          rw [← Finset.sum_union_inter]; exact le_self_add
      _ ≤ _ := add_le_add le_rfl ih

/-! ### Lemma 5 -/

/-- **Lemma 5** (for any connected weighted graph `G`, in particular a metric `G = ⊤`): if `H` is
the greedy `t`-spanner of `G` and `H'` is a `t`-spanner of the induced metric `M_H`, then
`w(H) ≤ w_{M_H}(H')`. -/
theorem lemma5 [Fintype V] [DecidableEq V] (hG : ∀ x y, G.Reachable x y) (ht : 1 ≤ t)
    (hH : IsGreedySpanner G w t H) {H' : SimpleGraph V} (hH' : IsWSpanner ⊤ H' (inducedW H w) t) :
    wt w H ≤ wt (inducedW H w) H' := by
  classical
  have hHc : ∀ x y, H.Reachable x y := fun x y => (hH.isWSpanner ht).reachable (hG x y)
  set E' := univ.filter (· ∈ H'.edgeSet)
  -- `H''` = union of the shortest paths `P_{e'}`, `e' ∈ H'`
  set H'' : SimpleGraph V := fromEdgeSet ↑(E'.biUnion (spEdges H w hHc)) with hH''
  have hH''H : H'' ≤ H := by
    intro x y hxy
    rw [hH'', fromEdgeSet_adj, Finset.mem_coe, Finset.mem_biUnion] at hxy
    obtain ⟨⟨e', -, hf⟩, -⟩ := hxy
    exact spEdges_subset hHc e' hf
  have hsp : ∀ a b, H'.Adj a b → ↑(spEdges H w hHc s(a, b)) ⊆ H''.edgeSet := by
    intro a b hab f hf
    rw [hH'', edgeSet_fromEdgeSet]
    refine ⟨Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
      ⟨s(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, hf⟩), ?_⟩
    exact H.not_isDiag_of_mem_edgeSet (spEdges_subset hHc _ hf)
  -- `H''` is a `t`-spanner of `H`, hence equals `H` by Lemma 3
  have hspan : IsWSpanner H H'' w t := by
    refine isWSpanner_of_adj ht hH''H fun x y hxy => ?_
    calc H''.wdist w x y ≤ H'.wdist (inducedW H w) x y :=
          wdist_le_wdist_of_edges fun a b hab => by
            rw [coe_inducedW (hHc a b)]; exact wdist_le_of_spEdges_subset hHc (hsp a b hab)
      _ ≤ t * w s(x, y) := wdist_inducedW_le_of_adj hHc hH' hxy
  have heq : H'' = H := lemma3 hH hspan
  -- weights
  calc wt w H = wt w H'' := by rw [heq]
    _ = ∑ e ∈ univ.filter (· ∈ H''.edgeSet), (w e : ℝ≥0∞) := wt_eq_sum w H''
    _ ≤ ∑ e ∈ E'.biUnion (spEdges H w hHc), (w e : ℝ≥0∞) := by
        refine Finset.sum_le_sum_of_subset fun e he => ?_
        rw [Finset.mem_filter, hH'', edgeSet_fromEdgeSet] at he
        exact he.2.1
    _ ≤ ∑ e' ∈ E', ∑ e ∈ spEdges H w hHc e', (w e : ℝ≥0∞) := sum_biUnion_le' _ _ _
    _ = ∑ e' ∈ E', (inducedW H w e' : ℝ≥0∞) :=
        Finset.sum_congr rfl fun e' _ => sum_spEdges' hHc e'
    _ = wt (inducedW H w) H' := (wt_eq_sum _ H').symm

/-! ### Lemma 6 -/

lemma Walk.single_le_wlength {u v : V} (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    (w e : ℝ≥0∞) ≤ p.wlength w :=
  List.single_le_sum (fun _ _ => zero_le) _ (List.mem_map_of_mem he)

/-- **Lemma 6** (for any connected weighted graph `G` with positive weights, in particular a metric):
if `1 ≤ t < 2`, `H` is the greedy `t`-spanner of `G` and `H'` is a `t`-spanner of the induced metric
`M_H`, then `|H| ≤ |H'|`. -/
theorem lemma6 [Fintype V] [DecidableEq V] (hG : ∀ x y, G.Reachable x y)
    (hpos : ∀ e ∈ G.edgeSet, 0 < w e) (ht : 1 ≤ t) (ht2 : t < 2)
    (hH : IsGreedySpanner G w t H) {H' : SimpleGraph V} (hH' : IsWSpanner ⊤ H' (inducedW H w) t) :
    H.edgeSet.ncard ≤ H'.edgeSet.ncard := by
  have hHG : H ≤ G := (hH.isWSpanner ht).1
  have hHc : ∀ x y, H.Reachable x y := fun x y => (hH.isWSpanner ht).reachable (hG x y)
  -- every edge `e` of `H` is covered by an edge `e'` of `H'` with `w_{M_H}(e') ≤ t · w(e)`
  have hcover : ∀ e ∈ H.edgeSet, ∃ e' ∈ H'.edgeSet, e ∈ spEdges H w hHc e' ∧
      (inducedW H w e' : ℝ≥0∞) ≤ t * w e := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : H.Adj x y := he
    have hd := wdist_inducedW_le_of_adj hHc hH' hxy
    obtain ⟨Q, -, hQw⟩ := exists_isPath_wlength_eq (w := inducedW H w)
      (reachable_of_wdist_lt_top (hd.trans_lt
        (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)))
    rw [← hQw] at hd
    suffices ∃ e' ∈ Q.edges, s(x, y) ∈ spEdges H w hHc e' by
      obtain ⟨e', he'Q, he'⟩ := this
      exact ⟨e', Q.edges_subset_edgeSet he'Q, he', (Walk.single_le_wlength Q he'Q).trans hd⟩
    by_contra hno
    push Not at hno
    -- otherwise `H - e` is a `t`-spanner of `H`, contradicting Lemma 3
    set K := H.deleteEdges {s(x, y)} with hKdef
    have hK : ∀ a b, s(a, b) ∈ Q.edges → K.wdist w a b ≤ inducedW H w s(a, b) := by
      intro a b hab
      rw [coe_inducedW (hHc a b)]
      refine wdist_le_of_spEdges_subset hHc fun f hf => ?_
      rw [edgeSet_deleteEdges]
      refine ⟨spEdges_subset hHc _ hf, fun hfe => ?_⟩
      rw [Set.mem_singleton_iff] at hfe
      exact hno _ hab (hfe ▸ hf)
    have hKxy : K.wdist w x y ≤ t * w s(x, y) := (wdist_le_wlength_of_edges Q hK).trans hd
    have hspan : IsWSpanner H K w t := by
      refine isWSpanner_of_adj ht (deleteEdges_le _) fun a b hab => ?_
      by_cases habe : s(a, b) = s(x, y)
      · rcases Sym2.eq_iff.mp habe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hKxy
        · rw [wdist_comm, Sym2.eq_swap]; exact hKxy
      · calc K.wdist w a b ≤ w s(a, b) :=
              wdist_le_of_adj (deleteEdges_adj.mpr ⟨hab, by simpa using habe⟩)
          _ ≤ t * w s(a, b) := le_mul_of_one_le_left zero_le (by exact_mod_cast ht)
    have hKH := lemma3 hH hspan
    have : K.Adj x y := hKH ▸ hxy
    exact (deleteEdges_adj.mp this).2 rfl
  choose! f hfH' hfcov hfw using hcover
  refine Set.ncard_le_ncard_of_injOn f (fun e he => hfH' e he) ?_ (Set.toFinite _)
  -- injectivity: two edges covered by the same `e'` would make `w_{M_H}(e') ≥ 2 min(w(e₁), w(e₂))`
  have key : ∀ e₁ ∈ H.edgeSet, ∀ e₂ ∈ H.edgeSet, e₁ ≠ e₂ → w e₁ ≤ w e₂ → f e₁ ≠ f e₂ := by
    intro e₁ he₁ e₂ he₂ hne hle hf
    have h1 := hfcov e₁ he₁
    have h2 := hfcov e₂ he₂
    rw [← hf] at h2
    have hsum : (w e₁ : ℝ≥0∞) + w e₂ ≤ inducedW H w (f e₁) := by
      rw [← sum_spEdges' hHc, ← Finset.sum_pair (f := fun g => (w g : ℝ≥0∞)) hne]
      exact Finset.sum_le_sum_of_subset (Finset.insert_subset h1 (Finset.singleton_subset_iff.mpr h2))
    have hpos₁ : (0 : ℝ≥0∞) < w e₁ := by exact_mod_cast hpos e₁ (edgeSet_mono hHG he₁)
    have : (2 : ℝ≥0∞) * w e₁ ≤ t * w e₁ := by
      calc (2 : ℝ≥0∞) * w e₁ = w e₁ + w e₁ := two_mul _
        _ ≤ w e₁ + w e₂ := by gcongr
        _ ≤ _ := hsum
        _ ≤ t * w e₁ := hfw e₁ he₁
    have ht2' : (t : ℝ≥0∞) < 2 := by exact_mod_cast ht2
    exact absurd this (not_le.mpr (ENNReal.mul_lt_mul_left hpos₁.ne' ENNReal.coe_ne_top ht2'))
  intro e₁ he₁ e₂ he₂ hf
  by_contra hne
  rcases le_total (w e₁) (w e₂) with h | h
  · exact key e₁ he₁ e₂ he₂ hne h hf
  · exact key e₂ he₂ e₁ he₁ (Ne.symm hne) h hf.symm

end GreedySpanner
