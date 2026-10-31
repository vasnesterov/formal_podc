import Papers.PODC2011.LocallyCheckableProofs.SpanningTree

/-!
# Problems in LogLCP: the positive results of Section 5.1

All schemes work on the family `connIdFamily c` of connected instances with identifiers in
`{1, …, n^c}` (for every `c`), use radius-1 verifiers and proof labels that are lists of a constant
number of `O(log n)`-bit numbers (`logLCP_of_check`).

* `leaderElection_logLCP`: leader election (exactly one node labelled `true`), strong scheme.
* `spanningTree_logLCP`: the marked edges `I.S` form a spanning tree, strong scheme.
* `acyclic_logLCP`: the graph is acyclic (a tree, as the graph is connected).
* `oddNodes_logLCP`: odd number of nodes (counters along a spanning tree: every node learns `n`).
* `nonBipartite_logLCP`: chromatic number `> 2`. We use a variant of the paper's scheme: a
  BFS-like tree from some root `r` and a second tree rooted at a node `g` that has a neighbour at
  the same claimed depth; the two tree paths and the edge form an odd closed walk (instead of the
  paper's counter along an odd cycle through the leader). See the comment before the theorem.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset

variable {L : Type*}

/-! ### Leader election -/

/-- Leader election: exactly one node is labelled `true`. -/
def LeaderElected : Set (Inst Bool) := {I | ∃ r ∈ I.V, ∀ v ∈ I.V, I.lab v = true ↔ v = r}

/-- **Section 5.1 (leader election).** On connected graphs, any solution of leader election can be
verified with `O(log n)`-bit proofs (spanning tree rooted at the leader); strong scheme. -/
theorem leaderElection_logLCP (c : ℕ) : LogLCP (connIdFamily c) LeaderElected := by
  refine logLCP_of_check 3 (c + 1)
    (fun I Q v => TreeOK I.G I.G (natField 0 Q) (natField 1 Q) (natField 2 Q) v ∧
      (I.lab v = true ↔ v = natField 0 Q v))
    (fun I Q I' Q' v h => and_congr (h.treeOK h.adj le_rfl 0 1 2)
      (by rw [h.lab_self, (h.field 0).2]))
    (fun I ⟨hc, hb⟩ ⟨r, hr, hlab⟩ => ?_) (fun I ⟨hc, _⟩ Q hacc => ?_)
  · obtain ⟨par, hpar⟩ := treeOK_complete le_rfl fun v hv => hc.2 v hv r hr
    refine ⟨fun v => [r, I.G.dist v r, par v], fun v hv => ⟨by simp, ?_⟩, fun v hv =>
      ⟨(hpar v hv).1, hlab v hv⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    · exact le_pow_succ_of_idBound hb hv (Or.inl hr)
    · exact le_pow_succ_of_idBound hb hv (Or.inr (hpar v hv).2.1.le)
    · exact le_pow_succ_of_idBound hb hv (Or.inl (hpar v hv).2.2)
  · obtain ⟨r, hr, hrt, -⟩ := treeOK_sound hc le_rfl fun v hv => (hacc v hv).1
    exact ⟨r, hr, fun v hv => by rw [(hacc v hv).2, hrt v hv]⟩

/-! ### Spanning trees and acyclicity -/

/-- A tree certificate for the edges of `H I` plus the check that every `H`-edge is a tree edge
verifies that `H I` is a spanning tree. -/
lemma tree_logLCP (c : ℕ) (H : Inst L → SimpleGraph ℕ) (hHG : ∀ I, H I ≤ I.G)
    (hHloc : ∀ I (Q : ℕ → List ℕ) I' Q' v, Nbr1Eq I Q I' Q' v → ∀ u, (H I).Adj v u ↔ (H I').Adj v u) :
    LogLCP (connIdFamily c)
      {I | (H I).IsAcyclic ∧ ∀ u ∈ I.V, ∀ v ∈ I.V, (H I).Reachable u v} := by
  refine logLCP_of_check 3 (c + 1)
    (fun I Q v => TreeOK I.G (H I) (natField 0 Q) (natField 1 Q) (natField 2 Q) v ∧
      TreeEdges (H I) (natField 0 Q) (natField 2 Q) v)
    (fun I Q I' Q' v h => and_congr (h.treeOK (hHloc I Q I' Q' v h) (hHG I) 0 1 2)
      (treeEdges_congr (hHloc I Q I' Q' v h) (fun u hu => (h.field 0).1 u (hHG I hu))
        (fun u hu => (h.field 2).1 u (hHG I hu)) (h.field 0).2 (h.field 2).2))
    (fun I ⟨hc, hb⟩ ⟨hac, hreach⟩ => ?_) (fun I ⟨hc, _⟩ Q hacc => ?_)
  · obtain ⟨r, hr⟩ := hc.1
    have hreach' : ∀ v ∈ I.V, (H I).Reachable v r := fun v hv => hreach v hv r hr
    obtain ⟨par, hpar⟩ := treeOK_complete (hHG I) hreach'
    have hedges := treeEdges_complete (hHG I) hac hreach' (par := par)
      fun v hv hvr => (hpar v hv).1.2.2 hvr
    refine ⟨fun v => [r, (H I).dist v r, par v], fun v hv => ⟨by simp, ?_⟩, fun v hv =>
      ⟨(hpar v hv).1, hedges v hv⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    · exact le_pow_succ_of_idBound hb hv (Or.inl hr)
    · exact le_pow_succ_of_idBound hb hv (Or.inr (hpar v hv).2.1.le)
    · exact le_pow_succ_of_idBound hb hv (Or.inl (hpar v hv).2.2)
  · obtain ⟨r, hr, hrt, hwalk⟩ := treeOK_sound hc (hHG I) fun v hv => (hacc v hv).1
    refine ⟨isAcyclic_of_treeEdges (hHG I) hrt (fun v hv => (hacc v hv).1)
      (fun v hv => (hacc v hv).2), fun u hu v hv => ?_⟩
    obtain ⟨p, -⟩ := hwalk u hu
    obtain ⟨q, -⟩ := hwalk v hv
    exact p.reachable.trans q.reachable.symm

/-- The marked edges `I.S` form a spanning tree of the nodes. -/
def MarkedSpanningTree : Set (Inst L) :=
  {I | I.S.IsAcyclic ∧ ∀ u ∈ I.V, ∀ v ∈ I.V, I.S.Reachable u v}

/-- **Section 5.1 (spanning tree).** On connected graphs, any spanning tree (marked edges) can be
verified with `O(log n)`-bit proofs (Korman–Kutten–Peleg); strong scheme. -/
theorem spanningTree_logLCP (c : ℕ) : LogLCP (connIdFamily c) (MarkedSpanningTree (L := L)) :=
  tree_logLCP c Inst.S Inst.S_le fun _ _ _ _ _ h => h.sadj

/-- **Section 5.1 (acyclic graphs).** On connected graphs, acyclicity is in LogLCP. -/
theorem acyclic_logLCP (c : ℕ) : LogLCP (connIdFamily c) {I : Inst L | I.G.IsAcyclic} :=
  logLCP_congr (P := {I | I.G.IsAcyclic ∧ ∀ u ∈ I.V, ∀ v ∈ I.V, I.G.Reachable u v})
    (fun _ hI => ⟨fun h => h.1, fun h => ⟨h, hI.1.2⟩⟩)
    (tree_logLCP c Inst.G (fun _ => le_rfl) fun _ _ _ _ _ h => h.adj)

/-! ### Odd number of nodes: counters along the tree -/

/-- **Section 5.1 (odd `n(G)`).** On connected graphs, "the number of nodes is odd" is in LogLCP:
a spanning tree with node counters along the paths towards the root (`cnt` = size of the subtree)
and the claimed value `N = n(G)`; the root checks `cnt = N`, all neighbours agree on `N`. -/
theorem oddNodes_logLCP (c : ℕ) : LogLCP (connIdFamily c) {I : Inst L | Odd I.n} := by
  refine logLCP_of_check 5 (c + 1)
    (fun I Q v => TreeOK I.G I.G (natField 0 Q) (natField 1 Q) (natField 2 Q) v ∧
      (∀ u, I.G.Adj v u → natField 4 Q u = natField 4 Q v) ∧
      natField 3 Q v = 1 + childSum I (natField 0 Q) (natField 2 Q) (natField 3 Q) v ∧
      (v = natField 0 Q v → natField 3 Q v = natField 4 Q v) ∧ Odd (natField 4 Q v))
    (fun I Q I' Q' v h => ?_) (fun I ⟨hc, hb⟩ hodd => ?_) (fun I ⟨hc, _⟩ Q hacc => ?_)
  · have hf := fun i => (h.field i)
    refine and_congr (h.treeOK h.adj le_rfl 0 1 2) (and_congr ?_ (and_congr ?_ ?_))
    · refine forall_congr' fun u => ⟨fun H hu => ?_, fun H hu => ?_⟩
      · have hu' := (h.adj u).2 hu
        rw [← (hf 4).1 u hu', ← (hf 4).2]; exact H hu'
      · rw [(hf 4).1 u hu, (hf 4).2]; exact H ((h.adj u).1 hu)
    · rw [(hf 3).2, childSum_congr h.nbrs fun u hu => by
        have hu := Inst.mem_nbrs.1 hu
        exact ⟨(hf 0).1 u hu, (hf 2).1 u hu, (hf 3).1 u hu⟩]
    · rw [(hf 0).2, (hf 3).2, (hf 4).2]
  · obtain ⟨r, hr⟩ := hc.1
    obtain ⟨par, hpar⟩ := treeOK_complete le_rfl fun v hv => hc.2 v hv r hr
    have htree : ∀ u ∈ I.V, u ≠ r → I.G.Adj u (par u) ∧ I.G.dist (par u) r + 1 = I.G.dist u r :=
      fun u hu hur => (hpar u hu).1.2.2 hur
    obtain ⟨cnt, hcnt⟩ := exists_count (rt := fun _ => r) (par := par) (fun _ _ => rfl)
      (fun u hu hur => (htree u hu hur).2) fun v hv => (hpar v hv).2.1
    have hroot := count_root hr (fun _ _ => rfl) (fun u hu hur => (htree u hu hur).1) hcnt
    have hle := count_le_root (d := fun u => I.G.dist u r) (fun _ _ => rfl) htree hcnt
    refine ⟨fun v => [r, I.G.dist v r, par v, cnt v, I.n], fun v hv => ⟨by simp, ?_⟩,
      fun v hv => ⟨(hpar v hv).1, fun _ _ => rfl, hcnt v hv, fun h => by
        simp only [natField] at h ⊢; simp; rw [h]; exact hroot, hodd⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · exact le_pow_succ_of_idBound hb hv (Or.inl hr)
    · exact le_pow_succ_of_idBound hb hv (Or.inr (hpar v hv).2.1.le)
    · exact le_pow_succ_of_idBound hb hv (Or.inl (hpar v hv).2.2)
    · exact le_pow_succ_of_idBound hb hv (Or.inr ((hle v hv).trans hroot.le))
    · exact le_pow_succ_of_idBound hb hv (Or.inr le_rfl)
  · obtain ⟨r, hr, hrt, -⟩ := treeOK_sound hc le_rfl fun v hv => (hacc v hv).1
    have hroot := count_root hr hrt
      (fun u hu hur => ((hacc u hu).1.2.2 (by rw [hrt u hu]; exact hur)).1)
      fun v hv => (hacc v hv).2.2.1
    have hN := (hacc r hr).2.2.2.1 (hrt r hr).symm
    have := (hacc r hr).2.2.2.2
    show Odd I.n
    rwa [← hN, hroot] at this

/-! ### Non-bipartite graphs -/

/-- An odd closed walk rules out a proper 2-colouring. -/
lemma not_colorable_two_of_odd_walk {G : SimpleGraph ℕ} {u : ℕ} (p : G.Walk u u)
    (hp : Odd p.length) : ¬ G.Colorable 2 := by
  intro hcol
  have h3 := p.three_le_chromaticNumber_of_odd_loop hp
  have h2 := hcol.chromaticNumber_le
  have := h3.trans h2
  norm_num at this

/-- In a graph that is not 2-colourable, some edge joins two nodes at the same distance from `r`
(otherwise the parity of the distance is a proper 2-colouring). -/
lemma exists_adj_dist_eq {I : Inst L} (hnb : ¬ I.G.Colorable 2) (r : ℕ) : ∃ u ∈ I.V, ∃ w, I.G.Adj u w ∧ I.G.dist w r = I.G.dist u r := by
  by_contra hne
  push Not at hne
  apply hnb
  have := (Coloring.mk (G := I.G) (fun x => decide (Even (I.G.dist r x))) fun {x y} hxy => by
    have hx : x ∈ I.V := I.sub hxy
    have h := hne x hx y hxy
    rw [dist_comm, dist_comm (u := x)] at h
    rcases hxy.diff_dist_adj (u := r) with h' | h' | h'
    · exact absurd h' h
    · simp only [h', Nat.even_add_one, ne_eq, decide_eq_decide]; tauto
    · have : I.G.dist r x ≠ 0 := by omega
      obtain ⟨k, hk⟩ : ∃ k, I.G.dist r x = k + 1 := ⟨I.G.dist r x - 1, by omega⟩
      rw [h', hk]; simp only [Nat.add_sub_cancel, Nat.even_add_one, ne_eq, decide_eq_decide]
      tauto).colorable
  simpa using this

/-- **Section 5.1 (chromatic number `> 2`).** On connected graphs, non-bipartiteness is in
LogLCP.

The paper's scheme: an odd cycle, a spanning tree rooted at a leader `a` on the cycle, and a
counter propagated along the cycle from `a` back to `a`, so that the leader "is convinced that it
is part of an odd cycle". (Locally, the nodes can only check that the counter increases along the
claimed cycle, so what is really certified is an odd *closed walk* through `a`; that suffices,
since an odd closed walk already rules out 2-colourings.) We formalize a variant with the same
proof size that needs no cycle: a tree `(r, d, par)` with arbitrary root `r` (in the honest proof
`d` is the BFS distance), and a second tree rooted at a node `g` that checks it has a neighbour `w`
with `d w = d g`; the tree paths from `g` and `w` to `r` and the edge `gw` form a closed walk of
odd length `2 d g + 1`. -/
theorem nonBipartite_logLCP (c : ℕ) :
    LogLCP (connIdFamily c) {I : Inst L | ¬ I.G.Colorable 2} := by
  refine logLCP_of_check 6 (c + 1)
    (fun I Q v => TreeOK I.G I.G (natField 0 Q) (natField 1 Q) (natField 2 Q) v ∧
      TreeOK I.G I.G (natField 3 Q) (natField 4 Q) (natField 5 Q) v ∧
      (v = natField 3 Q v → ∃ w, I.G.Adj v w ∧ natField 1 Q w = natField 1 Q v))
    (fun I Q I' Q' v h => ?_) (fun I ⟨hc, hb⟩ hnb => ?_) (fun I ⟨hc, _⟩ Q hacc => ?_)
  · have hf := fun i => (h.field i)
    refine and_congr (h.treeOK h.adj le_rfl 0 1 2) (and_congr (h.treeOK h.adj le_rfl 3 4 5) ?_)
    rw [(hf 3).2, (hf 1).2]
    refine imp_congr_right fun _ => ⟨fun ⟨w, hw, he⟩ => ⟨w, (h.adj w).1 hw, ?_⟩,
      fun ⟨w, hw, he⟩ => ⟨w, (h.adj w).2 hw, ?_⟩⟩
    · rw [← (hf 1).1 w hw]; exact he
    · rw [(hf 1).1 w ((h.adj w).2 hw)]; exact he
  · obtain ⟨r, hr⟩ := hc.1
    obtain ⟨par, hpar⟩ := treeOK_complete le_rfl fun v hv => hc.2 v hv r hr
    obtain ⟨g, hg, w, hgw, hdist⟩ := exists_adj_dist_eq hnb r
    obtain ⟨par', hpar'⟩ := treeOK_complete le_rfl fun v hv => hc.2 v hv g hg
    refine ⟨fun v => [r, I.G.dist v r, par v, g, I.G.dist v g, par' v],
      fun v hv => ⟨by simp, ?_⟩, fun v hv => ⟨(hpar v hv).1, (hpar' v hv).1, fun hvg => ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact le_pow_succ_of_idBound hb hv (Or.inl hr)
      · exact le_pow_succ_of_idBound hb hv (Or.inr (hpar v hv).2.1.le)
      · exact le_pow_succ_of_idBound hb hv (Or.inl (hpar v hv).2.2)
      · exact le_pow_succ_of_idBound hb hv (Or.inl hg)
      · exact le_pow_succ_of_idBound hb hv (Or.inr (hpar' v hv).2.1.le)
      · exact le_pow_succ_of_idBound hb hv (Or.inl (hpar' v hv).2.2)
    · simp only [natField] at hvg ⊢
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hvg ⊢
      subst hvg
      exact ⟨w, hgw, hdist⟩
  · obtain ⟨r, hr, hrt, hwalk⟩ := treeOK_sound hc le_rfl fun v hv => (hacc v hv).1
    obtain ⟨g, hg, hrt', -⟩ := treeOK_sound hc le_rfl fun v hv => (hacc v hv).2.1
    obtain ⟨w, hgw, hd⟩ := (hacc g hg).2.2 (hrt' g hg).symm
    obtain ⟨p, hp⟩ := hwalk g hg
    obtain ⟨q, hq⟩ := hwalk w (I.sub' hgw)
    refine not_colorable_two_of_odd_walk ((Walk.cons hgw q).append p.reverse) ?_
    simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse, hp, hq, hd]
    exact ⟨natField 1 Q g, by ring⟩

end Podc.LocallyCheckableProofs
