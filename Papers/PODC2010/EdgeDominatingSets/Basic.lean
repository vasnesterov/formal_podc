import Mathlib
import Cslib.Computability.Distributed.PortNumbering.Basic

/-!
# Edge dominating sets and outputs of port-numbering algorithms

Suomela, *Distributed algorithms for edge dominating sets*, PODC 2010, §1.1, §2.

* `IsEDS G D`: `D ⊆ E(G)` and every edge of `G` shares an endpoint with an edge of `D`
  (an edge dominates itself). -- CSLib candidate
* `edgeDomNum G`: the size of a minimum edge dominating set. -- CSLib candidate
* `card_edgeFinset_add_le`: if all degrees are `≤ Δ`, then `|E| ≤ (2Δ - 1)|D|` for every edge
  dominating set `D` (each edge dominates at most `2Δ - 1` edges). -- CSLib candidate
* `outEdges G X`: the edge set encoded by local outputs `X v ⊆ {0, …, deg v - 1}` (port `i ∈ X v`
  selects the edge behind port `i` of `v`), and `Consistent G X` (paper §2.2: both endpoints select
  the edge).
* `card_le_card_outEdges`: the covering-map counting argument of the lower bounds (§3.4, §4.4):
  if every node of a fibre of a covering map selects the same port `q`, which is not a half-loop of
  the base graph, then the selected edges are pairwise distinct.
-/

namespace Podc.EdgeDominatingSets

open Cslib.PortNumbering Finset

variable {V : Type*}

/-- `D` is an edge dominating set of `G`: `D ⊆ E(G)` and every edge of `G` shares an endpoint
with some edge of `D`. -/
def IsEDS (G : SimpleGraph V) (D : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ D, e ∈ G.edgeSet) ∧ ∀ e ∈ G.edgeSet, ∃ e' ∈ D, ∃ v, v ∈ e ∧ v ∈ e'

/-- The edge domination number: the size of a minimum edge dominating set. -/
noncomputable def edgeDomNum (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D, IsEDS G D ∧ D.card = n}

theorem edgeDomNum_le {G : SimpleGraph V} {D : Finset (Sym2 V)} (h : IsEDS G D) :
    edgeDomNum G ≤ D.card :=
  Nat.sInf_le ⟨D, h, rfl⟩

theorem isEDS_edgeFinset [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    IsEDS G G.edgeFinset := by
  refine ⟨fun e he => by simpa using he, fun e he => ⟨e, by simpa using he, ?_⟩⟩
  induction e using Sym2.ind with
  | h u v => exact ⟨u, Sym2.mem_mk_left u v, Sym2.mem_mk_left u v⟩

theorem exists_isEDS_card_eq [Fintype V] (G : SimpleGraph V) :
    ∃ D, IsEDS G D ∧ D.card = edgeDomNum G := by
  classical
  exact Nat.sInf_mem (s := {n | ∃ D, IsEDS G D ∧ D.card = n}) ⟨_, _, isEDS_edgeFinset G, rfl⟩

/-- If every edge of `G` has an endpoint covered by `D ⊆ E(G)`, then `D` is an edge dominating
set (this is just the definition, restated). -/
theorem isEDS_of_cover {G : SimpleGraph V} {D : Finset (Sym2 V)} (hD : ∀ e ∈ D, e ∈ G.edgeSet)
    (C : Set V) (hC : ∀ v ∈ C, ∃ e ∈ D, v ∈ e) (h : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) :
    IsEDS G D := by
  refine ⟨hD, fun e he => ?_⟩
  induction e using Sym2.ind with
  | h u v =>
    rcases h u v he with hu | hv
    · obtain ⟨e', he', hue'⟩ := hC u hu; exact ⟨e', he', u, Sym2.mem_mk_left u v, hue'⟩
    · obtain ⟨e', he', hve'⟩ := hC v hv; exact ⟨e', he', v, Sym2.mem_mk_right u v, hve'⟩

/-- An edge `s(u, v)` dominates at most `deg u + deg v - 1` edges. -/
theorem card_dominated_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (h : G.Adj u v) :
    (G.edgeFinset.filter fun e => ∃ w, w ∈ e ∧ w ∈ s(u, v)).card + 1 ≤ G.degree u + G.degree v := by
  have hsub : (G.edgeFinset.filter fun e => ∃ w, w ∈ e ∧ w ∈ s(u, v)) =
      G.incidenceFinset u ∪ G.incidenceFinset v := by
    ext e
    simp only [mem_filter, mem_union, SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet,
      Set.mem_ofPred_eq, Sym2.mem_iff, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨he, w, hw, rfl | rfl⟩ <;> simp_all
    · rintro (⟨he, hu⟩ | ⟨he, hv⟩)
      · exact ⟨he, u, hu, Or.inl rfl⟩
      · exact ⟨he, v, hv, Or.inr rfl⟩
  have hint : s(u, v) ∈ G.incidenceFinset u ∩ G.incidenceFinset v := by
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, h]
  rw [hsub, ← G.card_incidenceFinset_eq_degree, ← G.card_incidenceFinset_eq_degree,
    ← card_union_add_card_inter]
  have := card_pos.2 ⟨_, hint⟩
  omega

/-- **Each edge dominates at most `2Δ - 1` edges**: `|E| + |D| ≤ 2Δ|D|`, i.e.
`|E| ≤ (2Δ - 1)|D|`, for every edge dominating set `D` of a graph with maximum degree `≤ Δ`. -/
theorem card_edgeFinset_add_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {D : Finset (Sym2 V)} (hD : IsEDS G D) :
    G.edgeFinset.card + D.card ≤ 2 * Δ * D.card := by
  have hsub : G.edgeFinset ⊆
      D.biUnion fun d => G.edgeFinset.filter fun e => ∃ w, w ∈ e ∧ w ∈ d := by
    intro e he
    obtain ⟨d, hd, w, hwe, hwd⟩ := hD.2 e (by simpa using he)
    exact mem_biUnion.2 ⟨d, hd, mem_filter.2 ⟨he, w, hwe, hwd⟩⟩
  have hle : ∀ d ∈ D, (G.edgeFinset.filter fun e => ∃ w, w ∈ e ∧ w ∈ d).card + 1 ≤ 2 * Δ := by
    intro d hd
    have hdE := hD.1 d hd
    induction d using Sym2.ind with
    | h u v =>
      have := card_dominated_le G ((SimpleGraph.mem_edgeSet G).1 hdE)
      have := hΔ u; have := hΔ v
      omega
  calc G.edgeFinset.card + D.card
      ≤ (∑ d ∈ D, (G.edgeFinset.filter fun e => ∃ w, w ∈ e ∧ w ∈ d).card) + ∑ d ∈ D, 1 := by
        gcongr
        · exact (card_le_card hsub).trans card_biUnion_le
        · simp
    _ = ∑ d ∈ D, ((G.edgeFinset.filter fun e => ∃ w, w ∈ e ∧ w ∈ d).card + 1) := by
        rw [sum_add_distrib]
    _ ≤ ∑ _d ∈ D, 2 * Δ := sum_le_sum hle
    _ = 2 * Δ * D.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-! ### Outputs of algorithms -/

/-- The set of edges selected by local outputs `X`: port `i ∈ X v` (with `i < deg v`) selects the
edge behind port `i` of `v`. -/
noncomputable def outEdges [Fintype V] (G : PNGraph V) (X : V → Set ℕ) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e => ∃ v i, i < G.deg v ∧ i ∈ X v ∧ G.edge v i = e

theorem mem_outEdges [Fintype V] {G : PNGraph V} {X : V → Set ℕ} {e : Sym2 V} :
    e ∈ outEdges G X ↔ ∃ v i, i < G.deg v ∧ i ∈ X v ∧ G.edge v i = e := by
  classical
  simp [outEdges]

theorem edge_mem_outEdges [Fintype V] {G : PNGraph V} {X : V → Set ℕ} {v : V} {i : ℕ}
    (hi : i < G.deg v) (hX : i ∈ X v) : G.edge v i ∈ outEdges G X :=
  mem_outEdges.2 ⟨v, i, hi, hX, rfl⟩

theorem outEdges_subset_edgeSet [Fintype V] {G : PNGraph V} (hG : G.IsSimple) (X : V → Set ℕ) :
    ∀ e ∈ outEdges G X, e ∈ G.toSimpleGraph.edgeSet := by
  intro e he
  obtain ⟨v, i, hi, -, rfl⟩ := mem_outEdges.1 he
  exact G.edge_mem_edgeSet hG hi

/-- Consistency of the local outputs (paper, §2.2): if `v` selects the edge behind its port `i`,
then the other endpoint selects it too. -/
def Consistent (G : PNGraph V) (X : V → Set ℕ) : Prop :=
  ∀ v i, i < G.deg v → i ∈ X v → G.rport v i ∈ X (G.nbr v i)

/-- The algorithm `A`, run for `T` rounds on `G` (no local inputs), finds a factor-`α`
approximation of a minimum edge dominating set: its output is consistent, it is an edge
dominating set, and its size is at most `α` times the edge domination number. -/
def Approximates [Fintype V] (A : Algorithm Unit (Set ℕ)) (T : ℕ) (G : PNGraph V) (α : ℝ) : Prop :=
  Consistent G (A.eval G T fun _ => ()) ∧
    IsEDS G.toSimpleGraph (outEdges G (A.eval G T fun _ => ())) ∧
    ((outEdges G (A.eval G T fun _ => ())).card : ℝ) ≤ α * edgeDomNum G.toSimpleGraph

/-- `|E| ≤ (2d - 1) γ'(G)` for a simple port-numbered graph of maximum degree `≤ d`, with `|E|`
expressed through the degree sum: `Σ deg + 2γ' ≤ 4dγ'`. -/
theorem sum_deg_add_le [Fintype V] [DecidableEq V] {G : PNGraph V} (hG : G.IsSimple) {d : ℕ}
    (hd : ∀ v, G.deg v ≤ d) :
    ∑ v, G.deg v + 2 * edgeDomNum G.toSimpleGraph ≤ 4 * d * edgeDomNum G.toSimpleGraph := by
  classical
  obtain ⟨D, hD, hcard⟩ := exists_isEDS_card_eq G.toSimpleGraph
  have h1 := card_edgeFinset_add_le G.toSimpleGraph (Δ := d)
    (fun v => by rw [G.degree_eq hG]; exact hd v) hD
  have h2 := G.toSimpleGraph.sum_degrees_eq_twice_card_edges
  simp only [G.degree_eq hG] at h2
  rw [h2, ← hcard]
  nlinarith

/-- In a simple port-numbered graph, two nodes selecting the edge between them through ports `q`
and `q'` with `p v q = (w, q')`... : the key injectivity fact behind the lower bounds. If `v ≠ w`
and the edges behind port `q` of `v` and port `q` of `w` coincide, then `v` and `w` are joined by
an edge whose two ends both have port number `q`. -/
theorem rport_eq_of_edge_eq {G : PNGraph V} (hG : G.IsSimple) {v w : V} {q : ℕ}
    (hv : q < G.deg v) (hw : q < G.deg w) (hvw : v ≠ w) (h : G.edge v q = G.edge w q) :
    G.nbr v q = w ∧ G.rport v q = q := by
  have h' : s(v, G.nbr v q) = s(w, G.nbr w q) := h
  rcases Sym2.eq_iff.1 h' with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact absurd h1 hvw
  refine ⟨h2, ?_⟩
  -- `w` reaches `v` through port `q` and through port `rport v q`
  have e1 : G.nbr w (G.rport v q) = v := by have := G.nbr_nbr hv; rwa [h2] at this
  have hr : G.rport v q < G.deg w := h2 ▸ G.rport_lt hv
  exact hG.2 w _ _ hr hw (e1.trans h1)

open Classical in
/-- **Counting lemma for covering-map lower bounds.** Let `f` be a covering map from a simple
graph `G` onto `H`, let `x` be a node of `H` and `q < deg x` a port of `x` that is not a
half-loop. If every node of the fibre `f⁻¹(x)` selects port `q`, then at least `|f⁻¹(x)|`
distinct edges are selected, all of them incident to the fibre. -/
theorem card_fibre_le [Fintype V] [DecidableEq V] {W : Type*} {G : PNGraph V} (hG : G.IsSimple)
    {H : PNGraph W} {f : V → W} (hf : G.IsCovering H f) {x : W} {q : ℕ} (hq : q < H.deg x)
    (hloop : H.p x q ≠ (x, q)) (X : V → Set ℕ) (hX : ∀ v, f v = x → q ∈ X v) :
    (univ.filter fun v => f v = x).card ≤
      ((outEdges G X).filter fun e => ∃ v, f v = x ∧ v ∈ e).card := by
  classical
  rw [← card_image_of_injOn (f := fun v => G.edge v q)]
  · apply card_le_card
    intro e he
    obtain ⟨v, hv, rfl⟩ := mem_image.1 he
    have hv' : f v = x := (mem_filter.1 hv).2
    have hqv : q < G.deg v := by rw [← hf.deg_eq, hv']; exact hq
    exact mem_filter.2 ⟨edge_mem_outEdges hqv (hX v hv'), v, hv', Sym2.mem_mk_left _ _⟩
  · intro v hv w hw h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
    by_contra hvw
    have hqv : q < G.deg v := by rw [← hf.deg_eq, hv]; exact hq
    have hqw : q < G.deg w := by rw [← hf.deg_eq, hw]; exact hq
    obtain ⟨h1, h2⟩ := rport_eq_of_edge_eq hG hqv hqw hvw h
    apply hloop
    have := hf.p_eq v q hqv
    rw [h1, h2, hw, hv] at this
    exact this

end Podc.EdgeDominatingSets
