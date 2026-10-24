import Mathlib
import Cslib.Foundations.Combinatorics.SimpleGraph.Arboricity
import Cslib.Computability.Distributed.Local.Locality

/-!
# Basic notions of Barenboim–Elkin, PODC 2010

Definitions of Section 2.1 of L. Barenboim, M. Elkin, *Deterministic Distributed Vertex Coloring
in Polylogarithmic Time*, PODC 2010 (arXiv:1003.1608), for a simple graph `G` on a finite vertex
type `V` (the vertices are their own identifiers).

* `classGraph G c`: the spanning subgraph of `G` that keeps the edges whose endpoints have the same
  `c`-value; it is the disjoint union of the subgraphs induced by the colour classes of `c`.
* `IsDefective G c d` (`d`-defective colouring), `IsArbdefective G c r` (Definition 2.1:
  `r`-arbdefective colouring, every colour class induces a subgraph of arboricity `≤ r`; we state it
  for the union `classGraph G c`, and `IsArbdefective.induce` gives the per-class form),
  `IsLegal G c` (legal = proper colouring).
* Partial orientations are given by the parent sets `par v` (the out-neighbours of `v`):
  `IsPartialOrientation`, `IsComplete`, `deficit`, `DeficitLE`, `OutDegLE`, directed paths
  `IsDirPath`, the length bound `LengthLE par ℓ` ("every directed path has at most `ℓ` edges") and
  acyclicity `IsAcyclic`.

## Main results

* `lengthLE_iff_exists_height`: an orientation has length `≤ ℓ` iff it has a height function with
  values `≤ ℓ` that strictly decreases along every oriented edge.
* `exists_height_of_isAcyclic`: an acyclic orientation of a finite graph has a height function.
* `IsAcyclic.of_height`, `LengthLE.isAcyclic`: orientations with a height function are acyclic.
-/

open Finset

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-! ### Colourings -/

/-- The spanning subgraph of `G` keeping only the edges inside the classes of `c`. -/
def classGraph {β : Type*} (G : SimpleGraph V) (c : V → β) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ c u = c v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

@[simp] lemma classGraph_adj {β : Type*} {G : SimpleGraph V} {c : V → β} {u v : V} :
    (classGraph G c).Adj u v ↔ G.Adj u v ∧ c u = c v := Iff.rfl

lemma classGraph_le {β : Type*} (G : SimpleGraph V) (c : V → β) : classGraph G c ≤ G :=
  fun _ _ h => h.1

/-- Refining a class graph: the classes of `c'` inside the class graph of `c` are the classes of
the pair `(c, c')`. -/
lemma classGraph_classGraph {β γ : Type*} (G : SimpleGraph V) (c : V → β) (c' : V → γ) :
    classGraph (classGraph G c) c' = classGraph G (fun v => (c v, c' v)) := by
  ext u v; simp [and_assoc]

/-- The number of neighbours of `v` in `G`. -/
noncomputable def deg (G : SimpleGraph V) (v : V) : ℕ := #{u | G.Adj v u}

/-- `G` has maximum degree at most `Δ`. -/
def MaxDegLE (G : SimpleGraph V) (Δ : ℕ) : Prop := ∀ v, deg G v ≤ Δ

/-- `c` is a `d`-defective colouring: every vertex has at most `d` neighbours of its own colour. -/
def IsDefective {β : Type*} (G : SimpleGraph V) (c : V → β) (d : ℕ) : Prop :=
  ∀ v, #{u | G.Adj v u ∧ c u = c v} ≤ d

/-- **Definition 2.1** (for the union of the colour classes): `c` is an `r`-arbdefective colouring
if the colour classes induce subgraphs of arboricity at most `r`. We require the arboricity bound
for the disjoint union `classGraph G c` of these subgraphs; `IsArbdefective.induce` recovers the
bound for each colour class. -/
def IsArbdefective {β : Type*} (G : SimpleGraph V) (c : V → β) (r : ℕ) : Prop :=
  (classGraph G c).ArboricityLE r

/-- A legal (proper) colouring. -/
def IsLegal {β : Type*} (G : SimpleGraph V) (c : V → β) : Prop := ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

/-- Definition 2.1 in its literal form: every colour class induces a subgraph of arboricity at
most `r`. -/
lemma IsArbdefective.induce {β : Type*} {G : SimpleGraph V} {c : V → β} {r : ℕ}
    (h : IsArbdefective G c r) (i : β) : (G.induce {v | c v = i}).ArboricityLE r := by
  obtain ⟨F, hFG, hF, hcov⟩ := h
  refine ⟨fun j => (F j).comap (Function.Embedding.subtype _), fun j u v huv => ?_,
    fun j => ?_, fun u v huv => ?_⟩
  · exact (hFG j huv).1
  · exact (hF j).comap ⟨Function.Embedding.subtype _, fun h => h⟩ Subtype.val_injective
  · obtain ⟨j, hj⟩ := hcov (show (classGraph G c).Adj u v from ⟨huv, u.2.trans v.2.symm⟩)
    exact ⟨j, hj⟩

/-- A legal colouring is `0`-defective. -/
lemma IsLegal.isDefective {β : Type*} {G : SimpleGraph V} {c : V → β} (h : IsLegal G c) :
    IsDefective G c 0 := by
  intro v
  simp only [Nat.le_zero, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies, not_and]
  exact fun u huv hc => h huv hc.symm

/-! ### Partial orientations

A (partial) orientation is given by the parent sets `par v ⊆ N(v)`: `u ∈ par v` means that the
edge `vu` is oriented from `v` towards `u` (`u` is a *parent* of `v`). -/

/-- `par` is a partial orientation of `G`: parents are neighbours, and no edge is oriented both
ways. -/
def IsPartialOrientation (G : SimpleGraph V) (par : V → Finset V) : Prop :=
  (∀ v u, u ∈ par v → G.Adj v u) ∧ (∀ v u, u ∈ par v → v ∉ par u)

/-- Every edge is oriented (a complete orientation). -/
def IsComplete (G : SimpleGraph V) (par : V → Finset V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → v ∈ par u ∨ u ∈ par v

/-- The deficit of `v`: the number of unoriented edges at `v`. -/
noncomputable def deficit (G : SimpleGraph V) (par : V → Finset V) (v : V) : ℕ :=
  #{u | G.Adj v u ∧ u ∉ par v ∧ v ∉ par u}

/-- The deficit of the orientation is at most `τ`. -/
def DeficitLE (G : SimpleGraph V) (par : V → Finset V) (τ : ℕ) : Prop := ∀ v, deficit G par v ≤ τ

/-- The out-degree of the orientation is at most `m`. -/
def OutDegLE (par : V → Finset V) (m : ℕ) : Prop := ∀ v, #(par v) ≤ m

/-- A directed path (walk) `v₀ → v₁ → ⋯`: every vertex is a parent of the previous one. -/
def IsDirPath (par : V → Finset V) (l : List V) : Prop := l.IsChain (fun v u => u ∈ par v)

/-- The orientation has length at most `ℓ`: every directed path has at most `ℓ` edges. -/
def LengthLE (par : V → Finset V) (ℓ : ℕ) : Prop := ∀ l, IsDirPath par l → l.length ≤ ℓ + 1

/-- The orientation is acyclic: no vertex reaches itself along oriented edges. -/
def IsAcyclic (par : V → Finset V) : Prop :=
  ∀ v, ¬ Relation.TransGen (fun v u => u ∈ par v) v v

/-- A complete orientation has deficit `0`. -/
lemma IsComplete.deficitLE {G : SimpleGraph V} {par : V → Finset V} (h : IsComplete G par) :
    DeficitLE G par 0 := by
  intro v
  simp only [deficit, Nat.le_zero, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies,
    not_and, not_not]
  intro u huv hu
  rcases h huv with h | h
  · exact absurd h hu
  · exact h

-- CSLib candidate: partial orientations and height functions (`SimpleGraph/Orientation.lean`)
/-! ### Height functions -/

/-- Along a directed path, a height function decreases, so the path has at most `h v₀ + 1`
vertices. -/
lemma length_le_of_height {par : V → Finset V} {h : V → ℕ}
    (hh : ∀ v u, u ∈ par v → h u < h v) :
    ∀ (v : V) (l : List V), IsDirPath par (v :: l) → l.length ≤ h v := by
  intro v l
  induction l generalizing v with
  | nil => intro _; simp
  | cons b l ih =>
    intro hp
    rw [IsDirPath, List.isChain_cons_cons] at hp
    have := ih b hp.2
    have := hh v b hp.1
    simp only [List.length_cons]
    omega

/-- A height function with values `≤ ℓ` bounds the length of the orientation by `ℓ`. -/
lemma lengthLE_of_height {par : V → Finset V} {h : V → ℕ} {ℓ : ℕ} (hle : ∀ v, h v ≤ ℓ)
    (hh : ∀ v u, u ∈ par v → h u < h v) : LengthLE par ℓ := by
  rintro (_ | ⟨v, l⟩) hp
  · simp
  · have := length_le_of_height hh v l hp
    have := hle v
    simp only [List.length_cons]
    omega

/-- An orientation of length `≤ ℓ` has a height function with values `≤ ℓ`: the length of the
longest directed path starting at the vertex. -/
lemma exists_height_of_lengthLE {par : V → Finset V} {ℓ : ℕ} (hL : LengthLE par ℓ) :
    ∃ h : V → ℕ, (∀ v, h v ≤ ℓ) ∧ ∀ v u, u ∈ par v → h u < h v := by
  let S : V → Set ℕ := fun v => {k | ∃ l, IsDirPath par (v :: l) ∧ l.length = k}
  have hbdd : ∀ v, BddAbove (S v) := fun v => ⟨ℓ, by
    rintro k ⟨l, hp, rfl⟩
    have := hL _ hp
    simp only [List.length_cons] at this
    omega⟩
  have hne : ∀ v, (S v).Nonempty := fun v => ⟨0, [], by simp [IsDirPath], rfl⟩
  refine ⟨fun v => sSup (S v), fun v => csSup_le (hne v) ?_, fun v u hu => ?_⟩
  · rintro k ⟨l, hp, rfl⟩
    have := hL _ hp
    simp only [List.length_cons] at this
    omega
  · obtain ⟨l, hp, hl⟩ := Nat.sSup_mem (hne u) (hbdd u)
    have hmem : sSup (S u) + 1 ∈ S v :=
      ⟨u :: l, by rw [IsDirPath, List.isChain_cons_cons]; exact ⟨hu, hp⟩, by simp [hl]⟩
    exact Nat.lt_of_succ_le (le_csSup (hbdd v) hmem)

/-- An orientation has length `≤ ℓ` iff it has a height function with values `≤ ℓ`. -/
theorem lengthLE_iff_exists_height {par : V → Finset V} {ℓ : ℕ} :
    LengthLE par ℓ ↔ ∃ h : V → ℕ, (∀ v, h v ≤ ℓ) ∧ ∀ v u, u ∈ par v → h u < h v :=
  ⟨exists_height_of_lengthLE, fun ⟨_, hle, hh⟩ => lengthLE_of_height hle hh⟩

/-- An orientation with a height function is acyclic. -/
lemma IsAcyclic.of_height {par : V → Finset V} {h : V → ℕ}
    (hh : ∀ v u, u ∈ par v → h u < h v) : IsAcyclic par := by
  have key : ∀ v u, Relation.TransGen (fun v u => u ∈ par v) v u → h u < h v := by
    intro v u hvu
    induction hvu with
    | single hb => exact hh _ _ hb
    | tail _ hbc ih => exact (hh _ _ hbc).trans ih
  exact fun v hv => lt_irrefl _ (key v v hv)

/-- An orientation of bounded length is acyclic. -/
lemma LengthLE.isAcyclic {par : V → Finset V} {ℓ : ℕ} (hL : LengthLE par ℓ) : IsAcyclic par := by
  obtain ⟨h, -, hh⟩ := exists_height_of_lengthLE hL
  exact IsAcyclic.of_height hh

/-- An acyclic orientation of a finite graph has a height function (the number of vertices
reachable from a vertex), with values `< |V|`. -/
lemma exists_height_of_isAcyclic {par : V → Finset V} (hA : IsAcyclic par) :
    ∃ h : V → ℕ, (∀ v, h v < Fintype.card V) ∧ ∀ v u, u ∈ par v → h u < h v := by
  let R : V → V → Prop := fun v u => u ∈ par v
  let reach : V → Finset V := fun v => {u | Relation.TransGen R v u}
  refine ⟨fun v => #(reach v), fun v => ?_, fun v u hu => ?_⟩
  · refine card_lt_univ_of_notMem (x := v) ?_
    simpa [reach] using hA v
  · refine card_lt_card ⟨fun w hw => ?_, fun hsub => ?_⟩
    · simp only [reach, mem_filter, mem_univ, true_and] at hw ⊢
      exact Relation.TransGen.head hu hw
    · have : u ∈ reach u := hsub (by simp [reach]; exact Relation.TransGen.single hu)
      simp only [reach, mem_filter, mem_univ, true_and] at this
      exact hA u this

/-- An acyclic orientation of a finite graph has finite length (`< |V|`). -/
lemma IsAcyclic.lengthLE {par : V → Finset V} (hA : IsAcyclic par) :
    LengthLE par (Fintype.card V - 1) := by
  obtain ⟨h, hlt, hh⟩ := exists_height_of_isAcyclic hA
  exact lengthLE_of_height (fun v => by have := hlt v; omega) hh

end Podc.ArbdefectiveColoring
