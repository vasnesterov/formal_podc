import Mathlib

/-!
# Directed graphs and vertex insertion (Section 2 of the paper)

Schett, Danezis, *Embedding a Deterministic BFT Protocol in a Block DAG*, PODC 2021
(arXiv:2102.09594v2), Section 2, "Directed Acyclic Graphs".

A directed graph is a pair `(V, E)` of a vertex set and an edge set `E ⊆ V × V`. We keep the
well-formedness condition `E ⊆ V × V` as a separate predicate `DGraph.WellFormed`.

* `DGraph.Acyclic`: `v ⇀⁺ v'` implies `v ≠ v'`.
* `DGraph.le` (`G₁ ≤ G₂`, the paper's `G₁ ⩽ G₂`): `V₁ ⊆ V₂` and `E₁ = E₂ ∩ (V₁ × V₁)`.
* `DGraph.insert` (Definition 2.1): `insert(G, v, E) = (V_G ∪ {v}, E_G ∪ E)`.
* Lemma 2.2 (1)–(3): `DGraph.insert_eq_self`, `DGraph.le_insert`, `DGraph.acyclic_insert`, and the
  two counterexamples given in the paper's text after Lemma 2.2.
-/

namespace Podc.BFTInBlockDAG

/-- A directed graph: a set of vertices and a set of edges. -/
structure DGraph (α : Type*) where
  /-- The vertices. -/
  V : Set α
  /-- The edges `(v, v')`, written `v ⇀ v'`. -/
  E : Set (α × α)

namespace DGraph

variable {α : Type*}

/-- `v ⇀ v'`. -/
def Adj (G : DGraph α) (v w : α) : Prop := (v, w) ∈ G.E

/-- The edges stay inside the vertex set: `E ⊆ V × V`. -/
def WellFormed (G : DGraph α) : Prop := ∀ e ∈ G.E, e.1 ∈ G.V ∧ e.2 ∈ G.V

/-- `G` is acyclic: `v ⇀⁺ v'` implies `v ≠ v'`. -/
def Acyclic (G : DGraph α) : Prop := ∀ v w, Relation.TransGen G.Adj v w → v ≠ w

/-- The paper's `G₁ ⩽ G₂`: `V₁ ⊆ V₂` and `E₁ = E₂ ∩ (V₁ × V₁)`. -/
instance : LE (DGraph α) where
  le G₁ G₂ := G₁.V ⊆ G₂.V ∧ G₁.E = G₂.E ∩ (G₁.V ×ˢ G₁.V)

/-- `G₁ ∪ G₂ = (V₁ ∪ V₂, E₁ ∪ E₂)`. -/
instance : Union (DGraph α) where
  union G₁ G₂ := ⟨G₁.V ∪ G₂.V, G₁.E ∪ G₂.E⟩

/-- Definition 2.1: `insert(G, v, E) = (V_G ∪ {v}, E_G ∪ E)`. -/
def insert (G : DGraph α) (v : α) (E : Set (α × α)) : DGraph α := ⟨G.V ∪ {v}, G.E ∪ E⟩

/-- The shape of the edge sets allowed in Definition 2.1: `{(vᵢ, v) | vᵢ ∈ V ⊆ G}`. -/
def InsertEdges (G : DGraph α) (v : α) (E : Set (α × α)) : Prop :=
  ∀ e ∈ E, e.1 ∈ G.V ∧ e.2 = v

/-- Lemma 2.2 (1): inserting a vertex that is already there, with edges already there, does
nothing. -/
theorem insert_eq_self (G : DGraph α) {v : α} {E : Set (α × α)} (hv : v ∈ G.V) (hE : E ⊆ G.E) :
    G.insert v E = G := by
  cases G with
  | mk V E' =>
    simp only [insert, mk.injEq]
    exact ⟨Set.union_eq_left.2 (Set.singleton_subset_iff.2 hv), Set.union_eq_left.2 hE⟩

/-- Lemma 2.2 (2): inserting a new vertex with edges into it gives a supergraph in the sense
of `⩽`. -/
theorem le_insert (G : DGraph α) {v : α} {E : Set (α × α)} (hwf : G.WellFormed)
    (hE : G.InsertEdges v E) (hv : v ∉ G.V) : G ≤ G.insert v E := by
  refine ⟨Set.subset_union_left, ?_⟩
  ext e
  simp only [insert, Set.mem_inter_iff, Set.mem_union, Set.mem_prod]
  constructor
  · intro h
    exact ⟨Or.inl h, hwf e h⟩
  · rintro ⟨h | h, -, h2⟩
    · exact h
    · exact absurd ((hE e h).2 ▸ h2) hv

/-- Lemma 2.2 (3): inserting a new vertex into an acyclic graph keeps it acyclic. -/
theorem acyclic_insert (G : DGraph α) {v : α} {E : Set (α × α)} (hwf : G.WellFormed)
    (hE : G.InsertEdges v E) (hv : v ∉ G.V) (hG : G.Acyclic) : (G.insert v E).Acyclic := by
  -- No edge of the new graph leaves `v`; so every path avoiding a final step into `v` is old.
  have key : ∀ a b, Relation.TransGen (G.insert v E).Adj a b →
      b = v ∨ (a ≠ v ∧ Relation.TransGen G.Adj a b) := by
    intro a b h
    induction h with
    | single h =>
      rcases h with h | h
      · exact Or.inr ⟨fun ha => hv (ha ▸ (hwf _ h).1), Relation.TransGen.single h⟩
      · exact Or.inl (hE _ h).2
    | tail _ h ih =>
      rename_i b c
      rcases h with h | h
      · rcases ih with rfl | ⟨ha, ih⟩
        · exact absurd (hwf _ h).1 hv
        · exact Or.inr ⟨ha, ih.tail h⟩
      · exact Or.inl (hE _ h).2
  intro a b h hab
  subst hab
  rcases key a a h with rfl | ⟨-, h'⟩
  · -- a path from `v` to `v`: its first edge leaves `v`, impossible
    obtain ⟨c, h1, -⟩ := Relation.TransGen.head'_iff.1 h
    rcases h1 with h1 | h1
    · exact hv (hwf _ h1).1
    · exact hv ((hE _ h1).1)
  · exact hG a a h' rfl

/-- The first counterexample after Lemma 2.2: re-inserting an existing vertex with a new edge
breaks `G ⩽ insert(G, v, E)`. -/
theorem not_le_insert_of_mem :
    ¬ (⟨{0, 1}, ∅⟩ : DGraph ℕ) ≤ (⟨{0, 1}, ∅⟩ : DGraph ℕ).insert 1 {(0, 1)} := by
  rintro ⟨-, h⟩
  have : ((0 : ℕ), (1 : ℕ)) ∈ (⟨{0, 1}, ∅⟩ : DGraph ℕ).E := by
    rw [h]; simp [insert]
  simp at this

/-- The second counterexample after Lemma 2.2: re-inserting an existing vertex may add a
cycle. -/
theorem not_acyclic_insert_of_mem :
    ¬ ((⟨{0, 1}, {(0, 1)}⟩ : DGraph ℕ).insert 0 {(1, 0)}).Acyclic := by
  intro h
  refine h 0 0 ((Relation.TransGen.single (b := 1) ?_).tail ?_) rfl <;> simp [insert, Adj]

end DGraph

end Podc.BFTInBlockDAG
