import Mathlib

/-!
# DAG-Rider: the DAG abstraction

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021 (arXiv:2102.08325v2),
Section 4 (Algorithm 1).

Because vertices are disseminated by reliable broadcast, two correct processes never hold different
vertices with the same round and source (non-equivocation). We therefore identify a vertex with the
pair `(round, source)` (`Vtx P = ℕ × P`) and store the contents of *all* vertices that are ever
delivered in one global `Content`: strong edges (as a set of sources: a strong edge of `(r, p)` to
`s` points to `(r - 1, s)`), weak edges and the block. A local `DAG_i` of a process is then just a
finite set of vertex identifiers.

* `SEdge C v u` / `Edge C v u`: a strong edge / any edge from `v` to a vertex `u` of round `≥ 1`
  (the pseudocode's `path` and `strong_path` only use vertices of `⋃_{r ≥ 1} DAG[r]`).
* `SPath C v u` / `Path C v u`: reflexive-transitive closures (`strong_path(v, u)`, `path(v, u)`).
* `Closed C D`: `D` contains all successors of its vertices (Claim 1 of the paper).
* `Valid f C D`: every vertex of `D` has at least `2f + 1` strong edges (line 25 of Algorithm 2).

For computations we also give a round-by-round description of strong reachability
(`sreach`, `sPath_iff`), which makes `SPath` decidable.
-/

namespace DagRider

open Finset

/-- Vertex identifiers `(round, source)`. -/
abbrev Vtx (P : Type*) := ℕ × P

/-- The global contents of all vertices (well defined thanks to non-equivocation). -/
structure Content (P : Type*) (B : Type*) where
  /-- Sources of the strong edges: a strong edge of `(r, p)` to `s` points to `(r - 1, s)`. -/
  strong : Vtx P → Finset P
  /-- Weak edges. -/
  weak : Vtx P → Finset (Vtx P)
  /-- The block of transactions. -/
  block : Vtx P → B

variable {P : Type*} {B : Type*}

/-- A strong edge from `v` to `u`, where `u` is a vertex of round `≥ 1`. -/
def SEdge (C : Content P B) (v u : Vtx P) : Prop :=
  u.1 + 1 = v.1 ∧ u.2 ∈ C.strong v ∧ 1 ≤ u.1

/-- An edge (strong or weak) from `v` to `u`, where `u` is a vertex of round `≥ 1`. -/
def Edge (C : Content P B) (v u : Vtx P) : Prop :=
  ((u.1 + 1 = v.1 ∧ u.2 ∈ C.strong v) ∨ u ∈ C.weak v) ∧ 1 ≤ u.1

/-- `strong_path(v, u)` of Algorithm 1. -/
def SPath (C : Content P B) : Vtx P → Vtx P → Prop := Relation.ReflTransGen (SEdge C)

/-- `path(v, u)` of Algorithm 1. -/
def Path (C : Content P B) : Vtx P → Vtx P → Prop := Relation.ReflTransGen (Edge C)

/-- Claim 1 of the paper: a local DAG contains the causal history of each of its vertices. -/
def Closed (C : Content P B) (D : Finset (Vtx P)) : Prop :=
  ∀ v ∈ D, ∀ u, Edge C v u → u ∈ D

/-- Line 25 of Algorithm 2: every vertex in a local DAG has at least `2f + 1` strong edges. -/
def Valid (f : ℕ) (C : Content P B) (D : Finset (Vtx P)) : Prop :=
  ∀ v ∈ D, 2 * f + 1 ≤ (C.strong v).card

/-- The vertices of round `r` of a local DAG (`DAG[r]`). -/
def layer (D : Finset (Vtx P)) (r : ℕ) : Finset (Vtx P) := D.filter (fun v => v.1 = r)

variable {C : Content P B}

lemma SEdge.edge {v u : Vtx P} (h : SEdge C v u) : Edge C v u :=
  ⟨Or.inl ⟨h.1, h.2.1⟩, h.2.2⟩

lemma SPath.path {v u : Vtx P} (h : SPath C v u) : Path C v u :=
  by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ e ih => exact Relation.ReflTransGen.tail ih e.edge

lemma SPath.refl (v : Vtx P) : SPath C v v := Relation.ReflTransGen.refl

lemma SPath.trans {a b c : Vtx P} (h₁ : SPath C a b) (h₂ : SPath C b c) : SPath C a c :=
  Relation.ReflTransGen.trans h₁ h₂

lemma Path.refl (v : Vtx P) : Path C v v := Relation.ReflTransGen.refl

lemma Path.trans {a b c : Vtx P} (h₁ : Path C a b) (h₂ : Path C b c) : Path C a c :=
  Relation.ReflTransGen.trans h₁ h₂

lemma SPath.round_le {v u : Vtx P} (h : SPath C v u) : u.1 ≤ v.1 := by
  induction h with
  | refl => exact le_rfl
  | tail _ e ih => exact le_trans (by have := e.1; omega) ih

/-- Strong paths only go down through rounds `≥ 1`. -/
lemma SPath.eq_or_one_le {v u : Vtx P} (h : SPath C v u) : u = v ∨ 1 ≤ u.1 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨_, _, e⟩
  · exact Or.inl h
  · exact Or.inr e.2.2

lemma Path.eq_or_one_le {v u : Vtx P} (h : Path C v u) : u = v ∨ 1 ≤ u.1 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨_, _, e⟩
  · exact Or.inl h
  · exact Or.inr e.2

/-- In a closed local DAG, the causal history of a member is contained in the DAG. -/
lemma Closed.mem_of_path {D : Finset (Vtx P)} (hD : Closed C D) {v u : Vtx P} (hv : v ∈ D)
    (h : Path C v u) : u ∈ D := by
  induction h with
  | refl => exact hv
  | tail _ e ih => exact hD _ ih _ e

lemma Closed.mem_of_sPath {D : Finset (Vtx P)} (hD : Closed C D) {v u : Vtx P} (hv : v ∈ D)
    (h : SPath C v u) : u ∈ D := hD.mem_of_path hv h.path

/-- The causal history `{u ∈ D | path(v, u)}` of a vertex in a local DAG. -/
noncomputable def hist (C : Content P B) (D : Finset (Vtx P)) (v : Vtx P) : Finset (Vtx P) := by
  classical exact D.filter (fun u => Path C v u)

lemma mem_hist {D : Finset (Vtx P)} {v u : Vtx P} : u ∈ hist C D v ↔ u ∈ D ∧ Path C v u := by
  classical simp [hist]

/-- Two closed local DAGs containing `v` have the same causal history of `v`: this is why all
correct processes deliver the same blocks for the same leader. -/
lemma hist_eq_of_closed {D D' : Finset (Vtx P)} (hD : Closed C D) (hD' : Closed C D') {v : Vtx P}
    (hv : v ∈ D) (hv' : v ∈ D') : hist C D v = hist C D' v := by
  ext u
  simp only [mem_hist]
  exact ⟨fun h => ⟨hD'.mem_of_path hv' h.2, h.2⟩, fun h => ⟨hD.mem_of_path hv h.2, h.2⟩⟩

/-! ### Strong reachability round by round -/

/-- Sources of the vertices of round `v.1 - k` reachable from `v` by a strong path of length `k`
(all vertices after `v` have round `≥ 1`). -/
def sreach (C : Content P B) [DecidableEq P] (v : Vtx P) : ℕ → Finset P
  | 0 => {v.2}
  | k + 1 => if v.1 - (k + 1) = 0 then ∅ else
      (sreach C v k).biUnion (fun s => C.strong (v.1 - k, s))

/-- The last edge of a nontrivial strong path. -/
lemma sPath_iff_tail {v u : Vtx P} :
    SPath C v u ↔ u = v ∨ ∃ w, SPath C v w ∧ SEdge C w u := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨w, hw, e⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, hw, e⟩
  · rintro (rfl | ⟨w, hw, e⟩)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail hw e

lemma mem_sreach_iff [DecidableEq P] (v : Vtx P) :
    ∀ k, k ≤ v.1 → ∀ s, (s ∈ sreach C v k ↔ SPath C v (v.1 - k, s)) := by
  intro k
  induction k with
  | zero =>
    intro _ s
    simp only [sreach, Finset.mem_singleton, Nat.sub_zero]
    constructor
    · rintro rfl; exact Relation.ReflTransGen.refl
    · intro h
      rcases sPath_iff_tail.1 h with h | ⟨w, hw, e⟩
      · exact (congrArg Prod.snd h)
      · have := hw.round_le; have := e.1; simp at *; omega
  | succ k ih =>
    intro hk s
    simp only [sreach]
    split_ifs with h0
    · simp only [Finset.notMem_empty, false_iff]
      intro h
      rcases sPath_iff_tail.1 h with h | ⟨w, hw, e⟩
      · have := congrArg Prod.fst h; simp at this; omega
      · have := e.2.2; simp at this; omega
    · rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨t, ht, hs⟩
        rw [ih (by omega) t] at ht
        refine Relation.ReflTransGen.tail ht ⟨?_, ?_, ?_⟩
        · simp; omega
        · simpa using hs
        · simp; omega
      · intro h
        rcases sPath_iff_tail.1 h with h | ⟨w, hw, e⟩
        · have := congrArg Prod.fst h; simp at this; omega
        · obtain ⟨e1, e2, -⟩ := e
          simp only at e1 e2
          have hw1 : w.1 = v.1 - k := by omega
          refine ⟨w.2, ?_, ?_⟩
          · rw [ih (by omega) w.2]
            have : w = (v.1 - k, w.2) := Prod.ext hw1 rfl
            rwa [← this]
          · have : w = (v.1 - k, w.2) := Prod.ext hw1 rfl
            rwa [← this]

/-- Strong reachability is decidable, round by round. -/
lemma sPath_iff_sreach [DecidableEq P] {v u : Vtx P} :
    SPath C v u ↔ u.1 ≤ v.1 ∧ u.2 ∈ sreach C v (v.1 - u.1) := by
  constructor
  · intro h
    refine ⟨h.round_le, ?_⟩
    rw [mem_sreach_iff v _ (by omega)]
    have : (v.1 - (v.1 - u.1), u.2) = u := Prod.ext (by have := h.round_le; simp; omega) rfl
    rwa [this]
  · rintro ⟨h1, h2⟩
    rw [mem_sreach_iff v _ (by omega)] at h2
    have : (v.1 - (v.1 - u.1), u.2) = u := Prod.ext (by simp; omega) rfl
    rwa [this] at h2

instance [DecidableEq P] (C : Content P B) (v u : Vtx P) : Decidable (SPath C v u) :=
  decidable_of_iff _ sPath_iff_sreach.symm

end DagRider
