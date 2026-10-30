import Papers.PODC2026.TreesNetworkSizeKnowledge.Model
import Cslib.Foundations.Combinatorics.SimpleGraph.Arboricity

/-!
# Rooted trees given by parent pointers, and levels from a level labelling

* `RTree`: a finite rooted tree on a set of natural numbers, given by a parent function and a rank
  that decreases towards the root. `RTree.graph` is its (undirected) tree; `RTree.toInst` the
  corresponding network (`RTree.isTree`: the graph is a tree). Surgery on trees becomes a
  pointwise change of the parent function.
* `levelSet_eq`, `inLevel_iff`: if a labelling `lev` of the nodes satisfies local conditions
  (neighbours have level `≥ lev v - 1`, at most two neighbours have level `≥ lev v`, nodes of
  level `≥ 2` have degree `≥ 3`), then the levels of the `k`-hierarchical 2½-colouring problem
  are exactly `lev`.
-/

namespace Podc.TreesNetworkSizeKnowledge

open SimpleGraph

-- CSLib candidate: rooted trees by parent pointers
/-- A finite rooted tree on natural numbers, given by parent pointers and a decreasing rank. -/
structure RTree where
  V : Finset ℕ
  root : ℕ
  par : ℕ → ℕ
  rank : ℕ → ℕ
  root_mem : root ∈ V
  par_mem : ∀ v ∈ V, v ≠ root → par v ∈ V
  rank_lt : ∀ v ∈ V, v ≠ root → rank (par v) < rank v

namespace RTree

variable (T : RTree)

lemma par_ne {v : ℕ} (hv : v ∈ T.V) (hr : v ≠ T.root) : T.par v ≠ v := by
  intro h; have := T.rank_lt v hv hr; rw [h] at this; exact lt_irrefl _ this

/-- The tree: edges between a non-root node and its parent. -/
def graph : SimpleGraph ℕ where
  Adj a b := a ≠ b ∧ ((a ∈ T.V ∧ a ≠ T.root ∧ T.par a = b) ∨ (b ∈ T.V ∧ b ≠ T.root ∧ T.par b = a))
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma adj_iff {a b : ℕ} : T.graph.Adj a b ↔
    (a ∈ T.V ∧ a ≠ T.root ∧ T.par a = b) ∨ (b ∈ T.V ∧ b ≠ T.root ∧ T.par b = a) := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨ha, hr, rfl⟩ | ⟨hb, hr, rfl⟩
    · exact (T.par_ne ha hr).symm
    · exact T.par_ne hb hr

lemma adj_mem {a b : ℕ} (h : T.graph.Adj a b) : a ∈ T.V := by
  rcases (T.adj_iff).1 h with ⟨ha, -, -⟩ | ⟨hb, hr, rfl⟩
  · exact ha
  · exact T.par_mem b hb hr

lemma adj_par {v : ℕ} (hv : v ∈ T.V) (hr : v ≠ T.root) : T.graph.Adj v (T.par v) :=
  (T.adj_iff).2 (Or.inl ⟨hv, hr, rfl⟩)

lemma isTree : (T.graph.induce (T.V : Set ℕ)).IsTree := by
  refine ⟨?_, ?_⟩
  · have : Nonempty (T.V : Set ℕ) := ⟨⟨T.root, T.root_mem⟩⟩
    refine Connected.mk fun a b => ?_
    suffices h : ∀ n, ∀ v : (T.V : Set ℕ), T.rank v.1 ≤ n →
        (T.graph.induce (T.V : Set ℕ)).Reachable v ⟨T.root, T.root_mem⟩ from
      (h _ a le_rfl).trans (h _ b le_rfl).symm
    intro n
    induction n with
    | zero =>
      intro v hv
      by_cases hr : v.1 = T.root
      · rw [show v = ⟨T.root, T.root_mem⟩ from Subtype.ext hr]
      · have := T.rank_lt v.1 v.2 hr; omega
    | succ n ih =>
      intro v hv
      by_cases hr : v.1 = T.root
      · rw [show v = ⟨T.root, T.root_mem⟩ from Subtype.ext hr]
      · have hlt := T.rank_lt v.1 v.2 hr
        have hp : T.par v.1 ∈ (T.V : Set ℕ) := T.par_mem v.1 v.2 hr
        have h1 : (T.graph.induce (T.V : Set ℕ)).Adj v ⟨T.par v.1, hp⟩ := by
          simp only [comap_adj, Function.Embedding.subtype_apply]
          exact T.adj_par v.2 hr
        exact h1.reachable.trans (ih _ (by simp only; omega))
  · refine isAcyclic_of_rank (fun v => T.rank v.1) ?_ ?_
    · intro u v h
      simp only [comap_adj, Function.Embedding.subtype_apply] at h
      rcases (T.adj_iff).1 h with ⟨ha, hr, he⟩ | ⟨hb, hr, he⟩
      · have := T.rank_lt _ ha hr; rw [he] at this; exact this.ne'
      · have := T.rank_lt _ hb hr; rw [he] at this; exact this.ne
    · intro v u u' h h' hu hu'
      simp only [comap_adj, Function.Embedding.subtype_apply] at h h'
      have key : ∀ w : (T.V : Set ℕ), T.graph.Adj v.1 w.1 → T.rank w.1 < T.rank v.1 →
          w.1 = T.par v.1 := by
        intro w hw hlt
        rcases (T.adj_iff).1 hw with ⟨-, -, he⟩ | ⟨hb, hr, he⟩
        · exact he.symm
        · have := T.rank_lt _ hb hr; rw [he] at this; omega
      exact Subtype.ext ((key u h hu).trans (key u' h' hu').symm)

/-- The network given by a rooted tree. -/
def toInst : Inst where
  V := T.V
  G := T.graph
  adj_mem := fun _ _ h => T.adj_mem h
  isTree := T.isTree

@[simp] lemma toInst_V : T.toInst.V = T.V := rfl
@[simp] lemma toInst_G : T.toInst.G = T.graph := rfl

end RTree

/-! ### Levels from a level labelling -/

-- CSLib candidate
/-- If `lev` satisfies the local conditions of a hierarchical level structure, the sets
`V⁽ⁱ⁺¹⁾` of the 2½-colouring problem are `{v | i < lev v}`. -/
theorem levelSet_eq (G : SimpleGraph ℕ) (V : Set ℕ) (lev : ℕ → ℕ)
    (hadj : ∀ a b, G.Adj a b → a ∈ V) (h1 : ∀ v ∈ V, 1 ≤ lev v)
    (ha : ∀ v ∈ V, ∀ u, G.Adj v u → lev v ≤ lev u + 1)
    (hb : ∀ v ∈ V, {u | G.Adj v u ∧ lev v ≤ lev u}.ncard ≤ 2)
    (hc : ∀ v ∈ V, 2 ≤ lev v → 3 ≤ (G.neighborSet v).ncard) :
    ∀ i, levelSet G V i = {v | v ∈ V ∧ i < lev v} := by
  intro i
  induction i with
  | zero =>
    ext v; simp only [levelSet, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h, h1 v h⟩, fun h => h.1⟩
  | succ i ih =>
    ext v
    simp only [levelSet, ih, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hv, hi⟩, hcard⟩
      refine ⟨hv, ?_⟩
      by_contra hle
      have heq : G.neighborSet v ∩ {v | v ∈ V ∧ i < lev v} = {u | G.Adj v u ∧ lev v ≤ lev u} := by
        ext u
        simp only [Set.mem_inter_iff, mem_neighborSet, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h, -, h'⟩; exact ⟨h, by omega⟩
        · rintro ⟨h, h'⟩; exact ⟨h, hadj _ _ h.symm, by omega⟩
      rw [heq] at hcard
      have := hb v hv
      omega
    · rintro ⟨hv, hi⟩
      refine ⟨⟨hv, by omega⟩, ?_⟩
      have heq : G.neighborSet v ∩ {v | v ∈ V ∧ i < lev v} = G.neighborSet v := by
        ext u
        simp only [Set.mem_inter_iff, mem_neighborSet, Set.mem_ofPred_eq, and_iff_left_iff_imp]
        intro h
        exact ⟨hadj _ _ h.symm, by have := ha v hv u h; omega⟩
      rw [heq]
      have := hc v hv (by omega)
      omega

theorem inLevel_iff (G : SimpleGraph ℕ) (V : Set ℕ) (lev : ℕ → ℕ)
    (hadj : ∀ a b, G.Adj a b → a ∈ V) (h1 : ∀ v ∈ V, 1 ≤ lev v)
    (ha : ∀ v ∈ V, ∀ u, G.Adj v u → lev v ≤ lev u + 1)
    (hb : ∀ v ∈ V, {u | G.Adj v u ∧ lev v ≤ lev u}.ncard ≤ 2)
    (hc : ∀ v ∈ V, 2 ≤ lev v → 3 ≤ (G.neighborSet v).ncard) (i v : ℕ) :
    InLevel G V i v ↔ v ∈ V ∧ lev v = i := by
  have h := levelSet_eq G V lev hadj h1 ha hb hc
  simp only [InLevel, h, Set.mem_ofPred_eq, not_and, not_lt]
  constructor
  · rintro ⟨hi, ⟨hv, hl⟩, h'⟩; exact ⟨hv, by have := h' hv; omega⟩
  · rintro ⟨hv, rfl⟩; have := h1 v hv; exact ⟨this, ⟨hv, by omega⟩, fun _ => le_rfl⟩

end Podc.TreesNetworkSizeKnowledge
