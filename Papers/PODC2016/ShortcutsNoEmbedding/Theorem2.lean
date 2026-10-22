import Papers.PODC2016.ShortcutsNoEmbedding.Defs
import Papers.PODC2016.ShortcutsNoEmbedding.Supersteps
import Podc.Computability.Distributed.Congest.SubtreeRouting

/-!
# Theorem 2 of [HIZ16]: routing on tree-restricted shortcuts

All algorithms of Theorem 2 run on the *supergraph* of each part: its nodes are the block
components of the part (`Blocks P H`), and two blocks are adjacent if a `G`-edge inside the part
joins them (`superGraph P H`). One superstep consists of one round of communication over the
`G`-edges between blocks and an intra-block convergecast + broadcast, which by Lemma 2 takes
`≤ 2 (D - 1 + c) + 1` rounds for all parts simultaneously.

* `blockFamily T H`: the block components of all parts as a family of subtrees of `T`
  (`(i, t)` = the block of part `i` whose top is `t`). `blockFamily_congestionLE`: every tree edge
  lies in at most `c` of them. `theorem_2_intraBlock`: by Lemma 2, a convergecast and a broadcast
  inside all block components take `≤ D - 1 + c` rounds each.
* `superGraph_connected`, `card_blocks`: the supergraph is connected and has `blockParam P H ≤ b`
  nodes, so its diameter is `≤ b - 1`.
* `theorem_2_leader` (Theorem 2.1): after `b - 1` supersteps of min-flooding (starting from the
  smallest ID in each block), every block knows the smallest ID of the part.
* `theorem_2_convergecast` (Theorem 2.2): along the BFS tree of the supergraph rooted at the
  leader's block (computed by `floodDist` in `b - 1` supersteps), `b - 1` supersteps of tree
  convergecast deliver the aggregate `∑_{v ∈ P} x_v` (any commutative monoid) to the leader's
  block. Broadcasting it back (Theorem 2.3) takes another `b - 1` supersteps down the same tree.
-/

set_option linter.unusedSectionVars false

namespace ShortcutsNoEmbedding

open SimpleGraph Finset RootedTree

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  {G : SimpleGraph V} {T : G.RootedTree}

/-! ### Block components as a family of subtrees (intra-block communication) -/

variable (T) in
/-- The block components of all parts as subtrees of `T`: `(i, t)` consists of the edges `v` of
`H i` whose block (climbing along `H i`) has top `t`. -/
noncomputable def blockFamily (H : ι → Finset (Sym2 V)) : T.SubtreeFamily (ι × V) where
  edges p := univ.filter fun v => v ≠ T.root ∧ T.edge v ∈ H p.1 ∧ T.climb (H p.1) v = p.2
  top p := p.2
  ne_root p v hv := (mem_filter.1 hv).2.1
  parent_mem p v hv := by
    obtain ⟨-, hr, he, hc⟩ := mem_filter.1 hv
    rw [climb_of_mem hr he] at hc
    by_cases h : T.parent v ≠ T.root ∧ T.edge (T.parent v) ∈ H p.1
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, h.1, h.2, hc⟩)
    · exact Or.inl (by rw [climb_of_not_mem h] at hc; exact hc)

/-- Every vertex of a block is the top of the block or the lower endpoint of an edge of it. -/
theorem mem_blockFamily_edges {H : ι → Finset (Sym2 V)} {i : ι} {v : V}
    (hv : T.climb (H i) v ≠ v) : v ∈ (blockFamily T H).edges (i, T.climb (H i) v) := by
  have h : v ≠ T.root ∧ T.edge v ∈ H i := by
    by_contra h; exact hv (climb_of_not_mem h)
  exact mem_filter.2 ⟨mem_univ _, h.1, h.2, rfl⟩

/-- The block family has congestion at most `c` if the shortcut has: a tree edge of part `i`
lies in exactly one block of part `i`. -/
theorem blockFamily_congestionLE {H : ι → Finset (Sym2 V)} {c : ℕ}
    (hc : G.CongestionLE univ H c) : (blockFamily T H).CongestionLE c := by
  classical
  intro v
  by_cases hv : v = T.root
  · have : ∀ p, v ∉ (blockFamily T H).edges p := fun p h => by simp [blockFamily, hv] at h
    simp [this]
  have hcv : (univ.filter fun i => T.edge v ∈ H i).card ≤ c := by
    exact_mod_cast hc (T.edge v) (T.adj_parent v hv)
  refine le_trans ?_ hcv
  refine card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp q hq hpq => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_filter, mem_univ, true_and,
      blockFamily] at hp ⊢
    exact hp.2.1
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_filter, mem_univ, true_and, blockFamily] at hp hq
    ext
    · exact hpq
    · rw [← hp.2.2, ← hq.2.2, hpq]

/-- **Intra-block communication (Lemma 2 applied to the blocks).** For a `T`-restricted shortcut
with congestion `≤ c` and a tree of depth `≤ D`, a convergecast and a broadcast within all block
components of all parts can be scheduled in `≤ D - 1 + c` rounds each. -/
theorem theorem_2_intraBlock [LinearOrder ι] [LinearOrder V] {H : ι → Finset (Sym2 V)}
    {c D : ℕ} (hT : T.DepthLE D) (hc : G.CongestionLE univ H c) :
    ∃ σ τ : ι × V → V → ℕ, (blockFamily T H).IsConvergecastSchedule σ (D - 1 + c) ∧
      (blockFamily T H).IsBroadcastSchedule τ (D - 1 + c) :=
  letI : LinearOrder (ι × V) := (inferInstance : LinearOrder (ι ×ₗ V))
  (blockFamily T H).exists_schedules hT (blockFamily_congestionLE hc)

/-- Rounds per superstep: an intra-block convergecast and broadcast (Lemma 2) and one round over
the `G`-edges between blocks. -/
def superstepRounds (D c : ℕ) : ℕ := 2 * (D - 1 + c) + 1

/-! ### The supergraph of a part -/

variable (P : Finset V) (H : Finset (Sym2 V))

open Classical in
/-- The block components of part `P` (Definition 5). -/
noncomputable def blocks : Finset (blockGraph H).ConnectedComponent :=
  P.image (blockGraph H).connectedComponentMk

/-- The nodes of the supergraph. -/
abbrev Blocks := {C // C ∈ blocks P H}

noncomputable instance : DecidableEq (Blocks P H) := Classical.decEq _

variable (G) in
/-- The supergraph of a part: block components, adjacent if a `G`-edge inside `P` joins them. -/
def superGraph : SimpleGraph (Blocks P H) :=
  SimpleGraph.fromRel fun C C' => ∃ u ∈ P, ∃ v ∈ P, G.Adj u v ∧
    (blockGraph H).connectedComponentMk u = C.1 ∧ (blockGraph H).connectedComponentMk v = C'.1

noncomputable instance : DecidableRel (superGraph G P H).Adj := Classical.decRel _

variable {P H}

/-- The block of a vertex of the part. -/
noncomputable def blockOf {v : V} (hv : v ∈ P) : Blocks P H :=
  ⟨(blockGraph H).connectedComponentMk v, by classical exact mem_image_of_mem _ hv⟩

/-- The supergraph has exactly `blockParam P H` nodes. -/
theorem card_blocks : Fintype.card (Blocks P H) = blockParam P H := by
  classical
  rw [Fintype.card_coe, blockParam, blocks, ← Set.ncard_coe_finset, coe_image]

/-- The supergraph of a connected part is connected. -/
theorem superGraph_connected (hP : (G.induce (P : Set V)).Connected) :
    (superGraph G P H).Connected := by
  classical
  let f : ↥(P : Set V) → Blocks P H := fun a => blockOf a.2
  have conn : ∀ a b : ↥(P : Set V), (superGraph G P H).Reachable (f a) (f b) := by
    intro a b
    obtain ⟨p⟩ := hP.preconnected a b
    induction p with
    | nil => rfl
    | @cons a c b h p ih =>
      refine Reachable.trans ?_ ih
      by_cases hac : f a = f c
      · rw [hac]
      · apply Adj.reachable
        rw [superGraph, fromRel_adj]
        exact ⟨hac, Or.inl ⟨a.1, a.2, c.1, c.2, by simpa using h, rfl, rfl⟩⟩
  have hsurj : ∀ C : Blocks P H, ∃ a, f a = C := by
    rintro ⟨C, hC⟩
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hC
    exact ⟨⟨v, hv⟩, rfl⟩
  obtain ⟨⟨v, hv⟩⟩ := hP.nonempty
  have : Nonempty (Blocks P H) := ⟨f ⟨v, hv⟩⟩
  refine Connected.mk fun C C' => ?_
  obtain ⟨a, rfl⟩ := hsurj C
  obtain ⟨a', rfl⟩ := hsurj C'
  exact conn a a'

/-! ### Leader election (Theorem 2.1) -/

open Classical in
/-- The smallest ID among the vertices of the part in block `C`. -/
noncomputable def blockMinId (id : V → ℕ) (C : Blocks P H) : ℕ :=
  (P.filter fun v => (blockGraph H).connectedComponentMk v = C.1).inf' (by
    obtain ⟨C, hC⟩ := C
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hC
    exact ⟨v, mem_filter.2 ⟨hv, rfl⟩⟩) id

omit [Fintype V] [DecidableEq V] in
theorem part_nonempty (hP : (G.induce (P : Set V)).Connected) : P.Nonempty := by
  obtain ⟨⟨v, hv⟩⟩ := hP.nonempty; exact ⟨v, hv⟩

/-- **Theorem 2.1 of [HIZ16] (leader election).** Let `P` be a connected part whose shortcut `H` has
at most `b` block components. After `b - 1` supersteps of min-flooding on the supergraph, starting
from the smallest ID in each block, every block holds the smallest ID of the part, i.e. all blocks
agree on the leader. -/
theorem theorem_2_leader (hP : (G.induce (P : Set V)).Connected) (id : V → ℕ) {b : ℕ}
    (hb : blockParam P H ≤ b) (C : Blocks P H) :
    floodMin (superGraph G P H) (blockMinId id) (b - 1) C =
      P.inf' (part_nonempty hP) id := by
  classical
  rw [floodMin_eq_inf (superGraph_connected hP) _ (by rw [card_blocks]; exact hb)]
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro v hv
    refine (inf'_le _ (mem_univ (blockOf hv))).trans ?_
    rw [blockMinId]
    exact Finset.inf'_le id (by simp [hv, blockOf])
  · rw [Finset.le_inf'_iff]
    intro C' _
    rw [blockMinId, Finset.le_inf'_iff]
    intro v hv
    exact inf'_le _ (mem_filter.1 hv).1

/-! ### Convergecast and broadcast (Theorems 2.2, 2.3) -/

/-- In the supergraph, every BFS tree has depth `≤ b - 1`. -/
theorem superGraph_dist_le (hP : (G.induce (P : Set V)).Connected) {b : ℕ}
    (hb : blockParam P H ≤ b) (C C' : Blocks P H) : (superGraph G P H).dist C C' ≤ b - 1 := by
  classical
  obtain ⟨p, hp⟩ := Connected.walkLE_card (superGraph_connected hP) C C'
  have := dist_le p
  rw [card_blocks] at hp
  omega

open Classical in
/-- **Theorem 2.2 of [HIZ16] (convergecast to the leader).** Let `L` be the leader's block and
`Tr` the BFS tree of the supergraph rooted at `L` (depth `= dist`, computed by `floodDist` in
`b - 1` supersteps). After `b - 1` supersteps of tree convergecast, starting from the
aggregate of each block (an intra-block convergecast), the leader's block holds the aggregate
`∑_{v ∈ P} x v` of the whole part. -/
theorem theorem_2_convergecast (hP : (G.induce (P : Set V)).Connected) {M : Type*} [AddCommMonoid M] (x : V → M) {b : ℕ}
    (hb : blockParam P H ≤ b) (L : Blocks P H) :
    treeAgg ((superGraph_connected hP).bfsTree L)
      (fun C => ∑ v ∈ P with (blockGraph H).connectedComponentMk v = C.1, x v) (b - 1) L =
        ∑ v ∈ P, x v := by
  classical
  have h := treeAgg_root (T := (superGraph_connected hP).bfsTree L)
    (fun C => ∑ v ∈ P with (blockGraph H).connectedComponentMk v = C.1, x v) (h := b - 1)
    (fun C => by simpa using superGraph_dist_le hP hb L C)
  simp only [Connected.bfsTree_root] at h
  rw [h]
  -- regroup the sum over the part by blocks
  rw [← sum_fiberwise_of_maps_to (g := fun v => (blockGraph H).connectedComponentMk v)
    (t := blocks P H) (fun v hv => mem_image_of_mem _ hv)]
  rw [← sum_coe_sort (blocks P H)]

/-- The supersteps of the full part-wise aggregation: leader election, BFS labelling,
convergecast and broadcast, `b - 1` each, plus the initial intra-block aggregation. -/
def aggregationRounds (b D c : ℕ) : ℕ := (4 * (b - 1) + 1) * superstepRounds D c

/-- **Theorem 2 of [HIZ16], round count:** `O(b (D + c))`. This is only the arithmetic of the
superstep accounting (`4 (b - 1) + 1` supersteps of `superstepRounds D c` rounds each); the
composition of the per-superstep message schedules into one CONGEST execution is not formalized. -/
theorem aggregationRounds_le (b D c : ℕ) :
    aggregationRounds b D c ≤ (4 * b + 1) * (2 * (D + c) + 1) := by
  unfold aggregationRounds superstepRounds
  exact Nat.mul_le_mul (by omega) (by omega)

end ShortcutsNoEmbedding
