import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fintype.Card

/-!
# Neighbor assignment functions and matching covers

Dani, Gupta, Hayes, Pettie, *Wake Up and Join Me! An Energy-Efficient Algorithm for Maximal
Matching in Radio Networks*, PODC 2021 (arXiv:2104.09096v2), Section 6.

* `IsNAF G f` — Definition 6.1: `f : V → V` with `{v, f v} ∈ E` for every `v`;
* `inDeg f v = |f⁻¹(v)|`, `load f = max_v |f⁻¹(v)|`, `minNAFLoad G` (Definition 6.1);
* `IsMatchingCover G M` — `k` matchings (Mathlib `Subgraph.IsMatching`) whose vertex sets cover
  `V`; `matchingCoverNumber G = mc(G)` (Definition 6.2);
* `PMatching H` — a matching encoded by *partner variables* (as in the paper's algorithms), with
  the bridges to Mathlib matchings.

Minima are `sInf` of sets of naturals; they are only meaningful when the sets are nonempty, which
for both quantities means that `G` has no isolated vertex (see `Theorem63.lean`).
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Definition 6.1: a *neighbor assignment function* (NAF) of `G` maps every vertex to one of its
neighbours. -/
def IsNAF (G : SimpleGraph V) (f : V → V) : Prop := ∀ v, G.Adj v (f v)

/-- The load of the vertex `v` under `f`: the in-degree `|f⁻¹(v)|`. -/
def inDeg (f : V → V) (v : V) : ℕ := #{w | f w = v}

/-- Definition 6.1: the load of an assignment, `max_v |f⁻¹(v)|`. -/
def load (f : V → V) : ℕ := univ.sup (inDeg f)

/-- Definition 6.1: the minimum load among all NAFs of `G`. -/
noncomputable def minNAFLoad (G : SimpleGraph V) : ℕ := sInf {L | ∃ f, IsNAF G f ∧ load f = L}

/-- Definition 6.2: a family of `k` matchings of `G` whose union contains every vertex. -/
def IsMatchingCover (G : SimpleGraph V) {k : ℕ} (M : Fin k → G.Subgraph) : Prop :=
  (∀ i, (M i).IsMatching) ∧ ∀ v, ∃ i, v ∈ (M i).verts

/-- Definition 6.2: the matching cover number `mc(G)`. -/
noncomputable def matchingCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ M : Fin k → G.Subgraph, IsMatchingCover G M}

theorem load_le_iff {f : V → V} {L : ℕ} : load f ≤ L ↔ ∀ v, inDeg f v ≤ L := by
  simp [load, Finset.sup_le_iff]

theorem inDeg_le_load (f : V → V) (v : V) : inDeg f v ≤ load f :=
  Finset.le_sup (f := inDeg f) (mem_univ v)

/-- A matching of `H` encoded by partner variables: `p v = some w` iff `v` is matched to `w`. -/
structure PMatching (H : SimpleGraph V) where
  /-- The partner of a vertex (`none` if unmatched). -/
  p : V → Option V
  adj : ∀ v w, p v = some w → H.Adj v w
  symm : ∀ v w, p v = some w → p w = some v

namespace PMatching

variable {H : SimpleGraph V}

/-- The set of matched vertices. -/
def covered (m : PMatching H) : Finset V := {v | (m.p v).isSome}

/-- `m` is a maximal matching of `H`: every edge of `H` has a matched endpoint. -/
def IsMaximal (m : PMatching H) : Prop :=
  ∀ v w, H.Adj v w → (m.p v).isSome ∨ (m.p w).isSome

theorem mem_covered {m : PMatching H} {v : V} : v ∈ m.covered ↔ ∃ w, m.p v = some w := by
  simp [covered, Option.isSome_iff_exists]

theorem inj {m : PMatching H} {u v w : V} (hu : m.p u = some w) (hv : m.p v = some w) : u = v := by
  have h1 := m.symm _ _ hu
  have h2 := m.symm _ _ hv
  rw [h1] at h2
  exact Option.some_injective _ h2

/-- The Mathlib subgraph of a partner-variable matching. -/
def toSubgraph (m : PMatching H) : H.Subgraph where
  verts := {v | (m.p v).isSome}
  Adj v w := m.p v = some w
  adj_sub h := m.adj _ _ h
  edge_vert h := by simp [h]
  symm := ⟨fun _ _ h => m.symm _ _ h⟩

theorem toSubgraph_isMatching (m : PMatching H) : m.toSubgraph.IsMatching := by
  intro v hv
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hv
  exact ⟨w, hw, fun y hy => by
    change m.p v = some y at hy
    rw [hw] at hy; exact (Option.some_injective _ hy).symm⟩

theorem mem_toSubgraph_verts {m : PMatching H} {v : V} :
    v ∈ m.toSubgraph.verts ↔ v ∈ m.covered := by
  simp [toSubgraph, covered]

/-- The partner-variable encoding of a Mathlib matching. -/
noncomputable def ofSubgraph {M : H.Subgraph} (hM : M.IsMatching) : PMatching H where
  p v := by
    classical
    exact if h : v ∈ M.verts then some (hM h).exists.choose else none
  adj v w h := by
    classical
    by_cases hv : v ∈ M.verts
    · simp only [hv, dite_true, Option.some.injEq] at h
      subst h; exact M.adj_sub (hM hv).exists.choose_spec
    · simp [hv] at h
  symm v w h := by
    classical
    by_cases hv : v ∈ M.verts
    · simp only [hv, dite_true, Option.some.injEq] at h
      have hvw : M.Adj v w := h ▸ (hM hv).exists.choose_spec
      have hw : w ∈ M.verts := M.edge_vert hvw.symm
      simp only [hw, dite_true, Option.some.injEq]
      exact ((hM hw).unique (hM hw).exists.choose_spec hvw.symm)
    · simp [hv] at h

theorem ofSubgraph_covered {M : H.Subgraph} (hM : M.IsMatching) (v : V) :
    v ∈ (ofSubgraph hM).covered ↔ v ∈ M.verts := by
  classical
  simp only [covered, ofSubgraph]
  by_cases hv : v ∈ M.verts <;> simp [hv]

/-- Transport a matching of `H` to a supergraph `H'`. -/
def mono {H' : SimpleGraph V} (m : PMatching H) (h : H ≤ H') : PMatching H' where
  p := m.p
  adj v w hvw := h (m.adj v w hvw)
  symm := m.symm

end PMatching

/-- Definition 6.4: a *partial NAF* of `G`, `f : S → V` with `S ⊆ V`, encoded as `V → Option V`
(`S = {v | f v ≠ none}`). -/
def IsPartialNAF (G : SimpleGraph V) (f : V → Option V) : Prop := ∀ v w, f v = some w → G.Adj v w

/-- The load of `w` under a partial assignment, `|f⁻¹(w)|`. -/
def pInDeg (f : V → Option V) (w : V) : ℕ := #{v | f v = some w}

/-- Definition 6.4: the maximum load `max_v |f⁻¹(v)|` of a partial assignment. -/
def pLoad (f : V → Option V) : ℕ := univ.sup (pInDeg f)

/-- The domain `S` of a partial assignment; its coverage (Definition 6.4) is `|S| / |V|`. -/
def domain (f : V → Option V) : Finset V := {v | (f v).isSome}

theorem pLoad_le_iff {f : V → Option V} {L : ℕ} : pLoad f ≤ L ↔ ∀ v, pInDeg f v ≤ L := by
  simp [pLoad, Finset.sup_le_iff]

end Podc.WakeUpMatching
