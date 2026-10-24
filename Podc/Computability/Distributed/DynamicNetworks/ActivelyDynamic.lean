import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card
import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner

-- CSLib candidate: Cslib/Computability/Distributed/DynamicNetworks/ActivelyDynamic.lean

/-!
# Actively dynamic networks

Model of Michail–Skretas–Spirakis (*Distributed Computation and Reconfiguration in Actively
Dynamic Networks*, PODC 2020, §2.1): a static node set `V` and, in each synchronous round, every
node may

* **activate** an edge to a *potential neighbour*, i.e. a node at distance exactly two at the
  beginning of the round, and
* **deactivate** any of its currently active edges.

So the snapshot `E (i+1)` after round `i` is `(E i ∪ A) \ D` with `A` a set of edges between
potential neighbours of `E i` and `D ⊆ E i`. Equivalently (`validRound_iff`): every edge of
`E (i+1)` was already active or joins two nodes with a common neighbour in `E i`. We use the
latter, instance-free formulation `ValidRound` as the definition. Rounds are 0-indexed:
`E 0` is the initial network (the paper's `D(1) = G_s`).

## Main definitions

* `PotentialNbr G u v`: `u` and `v` are at distance exactly two in `G`.
* `ValidRound G G'`: `G'` is obtained from `G` by one round of activations and deactivations.
* `IsExec E`: every round of `E : ℕ → SimpleGraph V` is valid.
* `numActivated E i`: the number of edges activated in round `i` (`|E_ac(i)|`),
  `totalActivations E T`: their sum over the first `T` rounds.

## Main results

* `validRound_iff`: the definition agrees with the paper's activation/deactivation description.
* `ValidRound.edist_le_two_mul`: one round at most halves every distance.
* `ValidRound.edist_le_add`: one round shortens every distance by at most the number of edges
  activated in it (a shortest path uses each new edge once, and each new edge replaces a path of
  length two).
* `IsExec.edist_le_pow`, `IsExec.edist_le_add_total`: the iterated versions,
  `d₀(u, v) ≤ 2^T · d_T(u, v)` and `d₀(u, v) ≤ d_T(u, v) + Σ_{i<T} |E_ac(i)|`.
* `totalActivations_le_of`: `m` activations per round for `K` rounds give at most `m · K` in total.
-/

namespace Cslib.DynNet.Active

open SimpleGraph

variable {V : Type*}

/-- `v` is a *potential neighbour* of `u` in `G`: the two nodes are not adjacent but have a
common neighbour (distance exactly two). -/
def PotentialNbr (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ¬ G.Adj u v ∧ ∃ w, G.Adj u w ∧ G.Adj w v

/-- One synchronous round of an actively dynamic network turns the snapshot `G` into `G'`: every
edge of `G'` was already active in `G`, or was activated in this round between two nodes having a
common neighbour in `G`. Deactivations are unrestricted. -/
def ValidRound (G G' : SimpleGraph V) : Prop :=
  ∀ ⦃u v⦄, G'.Adj u v → G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

/-- The definition of a round agrees with the paper's: `G' = (G ∪ A) \ D` where `A` consists of
edges between potential neighbours and `D` of active edges. -/
theorem validRound_iff {G G' : SimpleGraph V} :
    ValidRound G G' ↔ ∃ A D : SimpleGraph V, (∀ u v, A.Adj u v → PotentialNbr G u v) ∧
      D ≤ G ∧ G' = (G ⊔ A) \ D := by
  constructor
  · intro h
    refine ⟨G' \ G, G \ G', ?_, sdiff_le, ?_⟩
    · rintro u v ⟨h1, h2⟩
      refine ⟨h1.ne, h2, ?_⟩
      rcases h h1 with h3 | h3
      · exact absurd h3 h2
      · exact h3
    · ext u v
      simp only [sdiff_adj, sup_adj]
      by_cases h1 : G'.Adj u v <;> by_cases h2 : G.Adj u v <;> simp [h1, h2]
  · rintro ⟨A, D, hA, -, rfl⟩ u v huv
    simp only [sdiff_adj, sup_adj] at huv
    rcases huv.1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hA u v h1).2.2

/-- An execution: a sequence of snapshots in which every round is valid. -/
def IsExec (E : ℕ → SimpleGraph V) : Prop := ∀ i, ValidRound (E i) (E (i + 1))

/-- The number of edges activated in round `i`, `|E_ac(i)| = |E(i+1) \ E(i)|`. -/
noncomputable def numActivated (E : ℕ → SimpleGraph V) (i : ℕ) : ℕ :=
  (E (i + 1) \ E i).edgeSet.ncard

/-- Total edge activations of the first `T` rounds, `Σ_{i<T} |E_ac(i)|`. -/
noncomputable def totalActivations (E : ℕ → SimpleGraph V) (T : ℕ) : ℕ :=
  ∑ i ∈ Finset.range T, numActivated E i

/-- A valid round at most halves every distance: `d_G(u, v) ≤ 2 d_{G'}(u, v)`. -/
theorem ValidRound.edist_le_two_mul {G G' : SimpleGraph V} (h : ValidRound G G') (u v : V) :
    G.edist u v ≤ 2 * G'.edist u v := by
  refine SimpleGraph.edist_le_mul_of_adj (G := G') (H := G) (by norm_num) ?_ u v
  intro x y hxy
  rcases h hxy with h1 | ⟨w, h1, h2⟩
  · rw [edist_eq_one_iff_adj.mpr h1]; norm_num
  · calc G.edist x y ≤ G.edist x w + G.edist w y := G.edist_triangle
      _ = 2 := by rw [edist_eq_one_iff_adj.mpr h1, edist_eq_one_iff_adj.mpr h2]; norm_num

open Classical in
/-- Walk version of `ValidRound.edist_le_add`: a walk of `G'` gives a walk of `G` whose length
exceeds it by the number of (occurrences of) edges of the walk that are not in `G`. -/
theorem ValidRound.edist_le_length_add {G G' : SimpleGraph V} (h : ValidRound G G') {u v : V}
    (p : G'.Walk u v) :
    G.edist u v ≤ p.length + (p.edges.filter (fun e => e ∉ G.edgeSet)).length := by
  induction p with
  | nil => simp
  | @cons x y z hxy q ih =>
    calc G.edist x z ≤ G.edist x y + G.edist y z := G.edist_triangle
      _ ≤ _ := by
        rcases _root_.em (G.Adj x y) with h1 | h1
        · have hm : s(x, y) ∈ G.edgeSet := h1
          rw [edist_eq_one_iff_adj.mpr h1]
          simp only [Walk.edges_cons, Walk.length_cons]
          rw [List.filter_cons_of_neg (by simpa using hm)]
          calc (1 : ℕ∞) + G.edist y z ≤ 1 + (q.length +
                (q.edges.filter (fun e => e ∉ G.edgeSet)).length) := by gcongr
            _ = _ := by push_cast; ring
        · have hm : s(x, y) ∉ G.edgeSet := h1
          obtain ⟨w, h2, h3⟩ := (h hxy).resolve_left h1
          have h2' : G.edist x y ≤ 2 := by
            calc G.edist x y ≤ G.edist x w + G.edist w y := G.edist_triangle
              _ = 2 := by
                rw [edist_eq_one_iff_adj.mpr h2, edist_eq_one_iff_adj.mpr h3]; norm_num
          simp only [Walk.edges_cons, Walk.length_cons]
          rw [List.filter_cons_of_pos (by simpa using hm)]
          simp only [List.length_cons]
          calc G.edist x y + G.edist y z ≤ 2 + (q.length +
                (q.edges.filter (fun e => e ∉ G.edgeSet)).length) := by gcongr
            _ = _ := by push_cast; ring

/-- A valid round shortens every distance by at most the number of activated edges:
`d_G(u, v) ≤ d_{G'}(u, v) + |E(G') \ E(G)|`. -/
theorem ValidRound.edist_le_add [Finite V] {G G' : SimpleGraph V} (h : ValidRound G G')
    (u v : V) : G.edist u v ≤ G'.edist u v + (G' \ G).edgeSet.ncard := by
  by_cases hr : G'.Reachable u v
  · obtain ⟨p, hp, hlen⟩ := hr.exists_path_of_dist
    have h1 := h.edist_le_length_add p
    generalize hl : List.filter _ p.edges = l at h1
    have hsl : l.Sublist p.edges := hl ▸ List.filter_sublist
    have hmem : ∀ e ∈ l, e ∉ G.edgeSet := by
      intro e he
      rw [← hl, List.mem_filter] at he
      simpa using he.2
    have hnd : l.Nodup := hp.isTrail.edges_nodup.sublist hsl
    classical
    have hsub : (l.toFinset : Set (Sym2 V)) ⊆ (G' \ G).edgeSet := by
      intro e he
      simp only [Finset.mem_coe, List.mem_toFinset] at he
      rw [edgeSet_sdiff]
      exact ⟨p.edges_subset_edgeSet (hsl.subset he), hmem e he⟩
    have hcard : l.length ≤ (G' \ G).edgeSet.ncard := by
      rw [← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    calc G.edist u v ≤ p.length + l.length := h1
      _ ≤ G'.edist u v + (G' \ G).edgeSet.ncard := by
        rw [← hr.coe_dist_eq_edist, ← hlen]
        gcongr
  · rw [edist_eq_top_of_not_reachable hr, top_add]
    exact le_top

/-- Over `T` rounds of an execution every distance shrinks by a factor of at most `2^T`. -/
theorem IsExec.edist_le_pow {E : ℕ → SimpleGraph V} (hE : IsExec E) (u v : V) (T : ℕ) :
    (E 0).edist u v ≤ 2 ^ T * (E T).edist u v := by
  induction T generalizing u v with
  | zero => simp
  | succ T ih =>
    calc (E 0).edist u v ≤ 2 ^ T * (E T).edist u v := ih u v
      _ ≤ 2 ^ T * (2 * (E (T + 1)).edist u v) := by gcongr; exact (hE T).edist_le_two_mul u v
      _ = 2 ^ (T + 1) * (E (T + 1)).edist u v := by rw [pow_succ, mul_assoc]

/-- Over `T` rounds of an execution every distance shrinks by at most the total number of edge
activations. -/
theorem IsExec.edist_le_add_total [Finite V] {E : ℕ → SimpleGraph V} (hE : IsExec E) (u v : V)
    (T : ℕ) : (E 0).edist u v ≤ (E T).edist u v + totalActivations E T := by
  induction T with
  | zero => simp [totalActivations]
  | succ T ih =>
    calc (E 0).edist u v ≤ (E T).edist u v + totalActivations E T := ih
      _ ≤ ((E (T + 1)).edist u v + numActivated E T) + totalActivations E T := by
        gcongr; exact (hE T).edist_le_add u v
      _ = (E (T + 1)).edist u v + totalActivations E (T + 1) := by
        simp only [totalActivations, Finset.sum_range_succ]; push_cast; ring

/-- If every round activates at most `m` edges and no round from `K` on activates any, then at
most `m · K` edges are activated over any horizon. -/
theorem totalActivations_le_of {E : ℕ → SimpleGraph V} {m K : ℕ}
    (h1 : ∀ t, numActivated E t ≤ m) (h2 : ∀ t, K ≤ t → numActivated E t = 0) (R : ℕ) :
    totalActivations E R ≤ m * K := by
  suffices h : totalActivations E R ≤ m * min R K from
    h.trans (Nat.mul_le_mul_left _ (min_le_right _ _))
  induction R with
  | zero => simp [totalActivations]
  | succ R ih =>
    have e : totalActivations E (R + 1) = totalActivations E R + numActivated E R := by
      simp [totalActivations, Finset.sum_range_succ]
    rw [e]
    by_cases hR : R < K
    · have : min (R + 1) K = min R K + 1 := by omega
      rw [this, Nat.mul_succ]
      exact add_le_add ih (h1 R)
    · rw [h2 R (by omega)]
      have : min (R + 1) K = min R K := by omega
      rw [this]; simpa using ih

end Cslib.DynNet.Active
