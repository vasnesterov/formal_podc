import Papers.PODC2021.LowCongestionShortcuts.Overcongested
import Cslib.Foundations.Combinatorics.SimpleGraph.Minor
import Mathlib

/-!
# The dense bipartite minor `B_{P'}` (proof of [GH21, Theorem 3.1], case (II))

For a set `S ⊆ ι` of parts (the random set `P'` of the paper) we build a bipartite minor of `G`:

* part-nodes `i ∈ S`, with branch set `P i`;
* edge-nodes `v ∈ O` with `v ∉ ⋃_{l ∈ S} P l` (`edgeNodes`), with branch set `branch S v`: the
  vertices below `v` in the forest `T \ O` whose path up to `v` avoids `⋃_{l ∈ S} P l` — this is
  the component of `v` in `(T \ O) \ ⋃_{l ∈ S} P l` of the paper;
* `i ~ v` iff `Present S i v`: some `r ∈ P i` lies strictly below `v` in `T \ O` and the path from
  `r` (exclusive) up to `v` avoids `⋃_{l ∈ S} P l` ("actually present").

The branch sets are proved to be connected and pairwise disjoint (the paper only asserts this), and
`card_present_le` is the resulting density bound. `exists_blocker` packages the probability
estimate for a single edge `(v, P_i)` of `B` whose representative is not `v` itself.
-/

set_option linter.unusedSectionVars false

namespace LowCongestionShortcuts

open SimpleGraph Finset

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  {G : SimpleGraph V} (T : G.RootedTree) (P : ι → Finset V) (O : Finset V)

/-- The branch set of the edge-node `v`: vertices below `v` in `T \ O` whose path up to `v`
avoids the parts in `S`. -/
def branch (S : Finset ι) (v : V) : Set V :=
  {w | ∃ n, T.parent^[n] w = v ∧ (∀ j < n, T.parent^[j] w ∉ O) ∧
    ∀ j ≤ n, ∀ l ∈ S, T.parent^[j] w ∉ P l}

/-- The edge-nodes of `B_S`: overcongested edges whose lower endpoint is not in a part of `S`. -/
def edgeNodes (S : Finset ι) : Finset V := O.filter fun v => ∀ l ∈ S, v ∉ P l

/-- The edge `(v, P_i)` is present in `B_S`. -/
def Present (S : Finset ι) (i : ι) (v : V) : Prop :=
  ∃ r ∈ P i, ∃ n, 1 ≤ n ∧ T.parent^[n] r = v ∧ (∀ j < n, T.parent^[j] r ∉ O) ∧
    ∀ j, 1 ≤ j → j ≤ n → ∀ l ∈ S, T.parent^[j] r ∉ P l

variable {T P O}

theorem branch_connected {S : Finset ι} {v : V} (hvr : v ≠ T.root)
    (hv : v ∈ edgeNodes P O S) : (G.induce (branch T P O S v)).Connected := by
  have hvb : v ∈ branch T P O S v := by
    refine ⟨0, rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj l hl => ?_⟩
    rw [Nat.le_zero.1 hj]; exact (mem_filter.1 hv).2 l hl
  have key : ∀ n w (hw : w ∈ branch T P O S v), T.parent^[n] w = v →
      (G.induce (branch T P O S v)).Reachable ⟨v, hvb⟩ ⟨w, hw⟩ := by
    intro n
    induction n with
    | zero => intro w hw hn; subst hn; exact Reachable.rfl
    | succ n ih =>
      intro w hw hn
      obtain ⟨n', hn', hO', hP'⟩ := hw
      have hnn : n' = n + 1 := by
        have a := RootedTree.depth_of_iterate_eq hn hvr
        have b := RootedTree.depth_of_iterate_eq hn' hvr
        omega
      subst hnn
      have hwr : w ≠ T.root := RootedTree.iterate_ne_root_of_lt hn hvr (Nat.succ_pos n)
      have hpw : T.parent w ∈ branch T P O S v :=
        ⟨n, by rwa [← Function.iterate_succ_apply], fun j hj => by
          rw [← Function.iterate_succ_apply]; exact hO' _ (by omega),
          fun j hj => by rw [← Function.iterate_succ_apply]; exact hP' _ (by omega)⟩
      refine (ih _ hpw (by rwa [← Function.iterate_succ_apply])).trans (Adj.reachable ?_)
      simp only [comap_adj, Function.Embedding.subtype_apply]
      exact (T.adj_parent w hwr).symm
  have : Nonempty (branch T P O S v) := ⟨⟨v, hvb⟩⟩
  refine Connected.mk fun a b => ?_
  obtain ⟨n₁, h₁, -⟩ := a.2
  obtain ⟨n₂, h₂, -⟩ := b.2
  exact (key n₁ a a.2 h₁).symm.trans (key n₂ b b.2 h₂)

theorem branch_disjoint {S : Finset ι} {v v' : V} (hv : v ∈ O) (hv' : v' ∈ O) (hne : v ≠ v') :
    Disjoint (branch T P O S v) (branch T P O S v') := by
  rw [Set.disjoint_left]
  rintro w ⟨n, hn, hO, -⟩ ⟨n', hn', hO', -⟩
  rcases lt_trichotomy n n' with h | rfl | h
  · exact hO' n h (hn ▸ hv)
  · exact hne (hn.symm.trans hn')
  · exact hO n' h (hn' ▸ hv')

theorem part_branch_disjoint {S : Finset ι} {i : ι} (hi : i ∈ S) (v : V) :
    Disjoint (P i : Set V) (branch T P O S v) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨n, -, -, hP⟩
  exact hP 0 (Nat.zero_le _) i hi hw

theorem present_adj {S : Finset ι} {i : ι} {v : V} (hvr : v ≠ T.root)
    (h : Present T P O S i v) : ∃ x ∈ (P i : Set V), ∃ y ∈ branch T P O S v, G.Adj x y := by
  obtain ⟨r, hr, n, hn1, hn, hO, hP⟩ := h
  refine ⟨r, hr, T.parent r, ⟨n - 1, ?_, fun j hj => ?_, fun j hj => ?_⟩, ?_⟩
  · rw [← Function.iterate_succ_apply]; convert hn using 2; omega
  · rw [← Function.iterate_succ_apply]; exact hO _ (by omega)
  · rw [← Function.iterate_succ_apply]; exact hP _ (by omega) (by omega)
  · exact T.adj_parent r (RootedTree.iterate_ne_root_of_lt hn hvr hn1)

/-- **Density of the minor `B_S`.** The number of present edges is at most
`δ (|S| + |edge-nodes|)`. -/
theorem card_present_le {δ : ℝ} (hδ : G.MinorDensityLE δ) (hP : G.IsParts P)
    (hOr : ∀ v ∈ O, v ≠ T.root) (S : Finset ι) [∀ i v, Decidable (Present T P O S i v)] :
    (((S ×ˢ edgeNodes P O S).filter fun q => Present T P O S q.1 q.2).card : ℝ) ≤
      δ * (S.card + (edgeNodes P O S).card) := by
  refine hδ.bipartite_card_le S (edgeNodes P O S) (fun i => (P i : Set V)) (branch T P O S)
    (Present T P O S) (fun i _ => hP.connected i) (fun v hv => ?_) ?_ ?_ ?_ ?_
  · exact branch_connected (hOr v (mem_filter.1 hv).1) hv
  · intro a _ a' _ h; exact Finset.disjoint_coe.2 (hP.disjoint h)
  · intro b hb b' hb' h; exact branch_disjoint (mem_filter.1 hb).1 (mem_filter.1 hb').1 h
  · intro a ha b _; exact part_branch_disjoint ha b
  · intro a _ b hb h; exact present_adj (hOr b (mem_filter.1 hb).1) h

/-- **Blocking parts of an edge of `B`.** For an edge `(v, P_i)` of `B` with `v ∉ P_i`, the parts
meeting the tree path from the topmost representative `r ∈ P_i` (exclusive) up to `v` (inclusive)
form a set `J` with `i ∉ J`, `|J| ≤ D - 1`, and the edge is present in `B_S` whenever `i ∈ S` and
`S ∩ J = ∅`. -/
theorem exists_blocker (hP : G.IsParts P) {D : ℕ} (hT : T.DepthLE D) {v : V} {i : ι}
    (hvr : v ≠ T.root) (hi : i ∈ parts T P O v) (hvi : v ∉ P i) :
    ∃ J : Finset ι, i ∉ J ∧ J.card ≤ D - 1 ∧
      ∀ S : Finset ι, i ∈ S → Disjoint S J → Present T P O S i v := by
  classical
  obtain ⟨r, hr, n, hn, hO, hPi⟩ := exists_rep hi
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (show v ∈ P i from hn ▸ hr) hvi
    · exact h
  let J : Finset ι := univ.filter fun l => ∃ j ∈ Icc 1 n, T.parent^[j] r ∈ P l
  refine ⟨J, ?_, ?_, ?_⟩
  · simp only [J, mem_filter, mem_univ, true_and, mem_Icc, not_exists, not_and]
    intro j hj; exact hPi j hj.1 hj.2
  · have hsub : J ⊆ (Icc 1 n).biUnion fun j => univ.filter fun l => T.parent^[j] r ∈ P l := by
      intro l hl
      simp only [J, mem_filter, mem_univ, true_and] at hl
      obtain ⟨j, hj, hl⟩ := hl
      exact mem_biUnion.2 ⟨j, hj, by simp [hl]⟩
    have hone : ∀ j, (univ.filter fun l => T.parent^[j] r ∈ P l).card ≤ 1 := by
      intro j
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [mem_filter, mem_univ, true_and] at ha hb
      by_contra hab
      exact Finset.disjoint_left.1 (hP.disjoint hab) ha hb
    have h1 := card_le_card hsub
    have h2 := card_biUnion_le (s := Icc 1 n) (t := fun j => univ.filter fun l => T.parent^[j] r ∈ P l)
    have h3 : ∑ j ∈ Icc 1 n, (univ.filter fun l => T.parent^[j] r ∈ P l).card ≤ n := by
      calc _ ≤ ∑ _j ∈ Icc 1 n, 1 := sum_le_sum fun j _ => hone j
        _ = n := by simp
    have h4 := RootedTree.depth_of_iterate_eq hn hvr
    have h5 := hT r
    have h6 := RootedTree.depth_pos hvr
    omega
  · intro S hiS hSJ
    refine ⟨r, hr, n, hn1, hn, hO, fun j hj1 hj2 l hl hjl => ?_⟩
    have : l ∈ J := by
      simp only [J, mem_filter, mem_univ, true_and]
      exact ⟨j, mem_Icc.2 ⟨hj1, hj2⟩, hjl⟩
    exact Finset.disjoint_left.1 hSJ hl this

end LowCongestionShortcuts
