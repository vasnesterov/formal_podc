import Podc.Foundations.Combinatorics.SimpleGraph.Power

/-!
# Theorem 12: a centralized 5/3-approximation for `G²`-MVC (Algorithm 2)

[BCMPP20] R. Bar-Yehuda, K. Censor-Hillel, Y. Maus, S. Pai, S. V. Pemmaraju,
*Distributed Approximation on Power Graphs*, PODC 2020 (arXiv 2006.03746), Section 4.

Algorithm 2 maintains a remaining vertex set `V'` and edge set `E'`. Since an edge of `G²` is only
removed from `E'` when one of its endpoints is taken into the cover, `E'` is always the edge set of
`G²[V']` (the paper proves this at the start of the proofs of Lemmas 13 and 14); we therefore only
store `V'` (`State.rem`), and `E' = G²[V']`.

* Part 1: while `G²[V']` has a triangle, take its three vertices into `S` (and `V1`).
* Part 2: while some vertex `x` has `deg(x) ≤ 3` in `G²[V']`:
  `deg 1`: take its neighbour; `deg 2` (no vertex of degree 1): take `y₁, y₂` and a neighbour
  `z ≠ x` of `y₁`; `deg 3` (no vertex of degree 1 or 2): take `y₁, y₂, y₃` and neighbours `z₁` of
  `y₁`, `z₂` of `y₂` with `z₁ ≠ z₂`, `z₁, z₂ ∉ {x, y₁, y₂, y₃}`. In all cases `x` is left with
  degree 0 and is removed (into `W₂`, not into `S`).
* Part 3: take any 2-approximate vertex cover of `G²[V']` into `S` (and `V3`).
* Throughout, a vertex of degree 0 may be removed from `V'` (the paper removes such vertices
  eagerly; we allow removing them at any time during parts 1 and 2, which only adds runs).

The algorithm is modelled as a nondeterministic transition system `Step` (every choice the
pseudocode leaves open is a nondeterministic choice). Main results:

* `theorem_12`: every complete run outputs a vertex cover `S` of `G²` with `3|S| ≤ 5|OPT|`.
* `exists_run`: complete runs exist (the guards of Algorithm 2 can always be met, including the
  existence claims for `z`, `z₁`, `z₂` made in lines 9 and 10, and part 3 via a maximal matching).
* `run_length_le`: every run has at most `n + 3` steps (each step is a polynomial-time check).

The approximation proof follows the paper: Lemma 13/14 (`blue_bound`: `3|V_{R'}| ≤ 2 s₁`),
Lemma 15 (the charging invariant `Inv.charge` and the 2-approximation of part 3), Lemma 16
(`Inv.covers`).
-/

namespace Podc.PowerGraphApproximation.Centralized

set_option linter.unusedSectionVars false

open SimpleGraph Finset Relation
open scoped Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Neighbours of `x` in `G²[s]`. -/
noncomputable def nbrs (s : Finset V) (x : V) : Finset V := s.filter fun y => (G.power 2).Adj x y

/-- Degree of `x` in `G²[s]`. -/
noncomputable def deg (s : Finset V) (x : V) : ℕ := (nbrs G s x).card

/-- `C` covers all edges of `G²[s]`. -/
def CoversIn (s C : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, (G.power 2).Adj u v → u ∈ C ∨ v ∈ C

/-- `C ⊆ s` is a 2-approximate vertex cover of `G²[s]`. -/
def IsTwoApprox (s C : Finset V) : Prop :=
  C ⊆ s ∧ CoversIn G s C ∧ ∀ D ⊆ s, CoversIn G s D → C.card ≤ 2 * D.card

/-- `G²[s]` has no triangle. -/
def TriangleFree (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
    ¬ ((G.power 2).Adj a b ∧ (G.power 2).Adj b c ∧ (G.power 2).Adj a c)

/-- The parts of Algorithm 2. -/
inductive Phase
  | one
  | two
  | three
  | done
  deriving DecidableEq

/-- State of Algorithm 2: the phase, the remaining vertices `V'` and the sets `V1, V2, V3` of
vertices taken into the cover in parts 1, 2, 3. -/
structure State (V : Type*) where
  phase : Phase
  rem : Finset V
  V1 : Finset V
  V2 : Finset V
  V3 : Finset V

/-- The cover `S = V1 ∪ V2 ∪ V3`. -/
noncomputable def State.cover (s : State V) : Finset V := s.V1 ∪ s.V2 ∪ s.V3

/-- Initial state on the instance `G²[U₀]`: `V' = U₀`, `S = ∅`. Algorithm 2 on `G²` is
`init univ`; `init U` runs Algorithm 2 on the induced subgraph `G²[U]` (as in Corollary 17). -/
def init (U₀ : Finset V) : State V := ⟨.one, U₀, ∅, ∅, ∅⟩

/-- One step of Algorithm 2 (see the module docstring). -/
inductive Step : State V → State V → Prop
  /-- Part 1 (lines 4–5): take a triangle of `G²[V']`. -/
  | tri {s : State V} {a b c : V} (hp : s.phase = .one) (ha : a ∈ s.rem) (hb : b ∈ s.rem)
      (hc : c ∈ s.rem) (hab : (G.power 2).Adj a b) (hbc : (G.power 2).Adj b c)
      (hac : (G.power 2).Adj a c) :
      Step s { s with rem := s.rem \ {a, b, c}, V1 := s.V1 ∪ {a, b, c} }
  /-- Remove a vertex of degree 0 (parts 1 and 2). -/
  | iso {s : State V} {v : V} (hp : s.phase = .one ∨ s.phase = .two) (hv : v ∈ s.rem)
      (hd : deg G s.rem v = 0) :
      Step s { s with rem := s.rem \ {v} }
  /-- End of part 1: no triangle left. -/
  | endOne {s : State V} (hp : s.phase = .one) (h : TriangleFree G s.rem) :
      Step s { s with phase := .two }
  /-- Part 2, line 8: `deg(x) = 1`, take its neighbour `y`; `x` becomes isolated. -/
  | deg1 {s : State V} {x y : V} (hp : s.phase = .two) (hx : x ∈ s.rem)
      (hn : nbrs G s.rem x = {y}) :
      Step s { s with rem := s.rem \ {x, y}, V2 := s.V2 ∪ {y} }
  /-- Part 2, line 9: no vertex of degree 1, `deg(x) = 2` with neighbours `y₁, y₂`, and `z ≠ x`
  a neighbour of `y₁`; take `z, y₁, y₂`; `x` becomes isolated. -/
  | deg2 {s : State V} {x y₁ y₂ z : V} (hp : s.phase = .two)
      (hno : ∀ u ∈ s.rem, deg G s.rem u ≠ 1) (hx : x ∈ s.rem)
      (hn : nbrs G s.rem x = {y₁, y₂}) (hy : y₁ ≠ y₂) (hz : z ∈ s.rem)
      (hyz : (G.power 2).Adj y₁ z) (hzx : z ≠ x) :
      Step s { s with rem := s.rem \ {x, y₁, y₂, z}, V2 := s.V2 ∪ {z, y₁, y₂} }
  /-- Part 2, line 10: no vertex of degree 1 or 2, `deg(x) = 3` with neighbours `y₁, y₂, y₃`, and
  `z₁ ≠ z₂` neighbours of `y₁`, `y₂` outside `{x, y₁, y₂, y₃}`; take `y₁, y₂, y₃, z₁, z₂`. -/
  | deg3 {s : State V} {x y₁ y₂ y₃ z₁ z₂ : V} (hp : s.phase = .two)
      (hno : ∀ u ∈ s.rem, deg G s.rem u ≠ 1 ∧ deg G s.rem u ≠ 2) (hx : x ∈ s.rem)
      (hn : nbrs G s.rem x = {y₁, y₂, y₃}) (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃)
      (hz₁ : z₁ ∈ s.rem) (hz₂ : z₂ ∈ s.rem) (hyz₁ : (G.power 2).Adj y₁ z₁)
      (hyz₂ : (G.power 2).Adj y₂ z₂) (hzz : z₁ ≠ z₂) (hz₁' : z₁ ∉ ({x, y₁, y₂, y₃} : Finset V))
      (hz₂' : z₂ ∉ ({x, y₁, y₂, y₃} : Finset V)) :
      Step s { s with rem := s.rem \ {x, y₁, y₂, y₃, z₁, z₂},
                      V2 := s.V2 ∪ {y₁, y₂, y₃, z₁, z₂} }
  /-- End of part 2: every remaining vertex has degree at least 4. -/
  | endTwo {s : State V} (hp : s.phase = .two) (h : ∀ u ∈ s.rem, 4 ≤ deg G s.rem u) :
      Step s { s with phase := .three }
  /-- Part 3 (line 13): take a 2-approximate vertex cover of `G²[V']`. -/
  | final {s : State V} {C : Finset V} (hp : s.phase = .three) (hC : IsTwoApprox G s.rem C) :
      Step s { s with phase := .done, rem := ∅, V3 := C }

/-! ### Basic facts -/

variable {G}

lemma mem_nbrs {s : Finset V} {x y : V} : y ∈ nbrs G s x ↔ y ∈ s ∧ (G.power 2).Adj x y := by
  simp [nbrs]

lemma adj_ne {u v : V} (h : (G.power 2).Adj u v) : u ≠ v := h.ne

/-- From an edge of `G²[U₀]` and a cover of `G²[U₀]`, an endpoint in the cover. -/
lemma exists_mem_of_adj {U₀ O : Finset V} (hO : CoversIn G U₀ O) {a b : V} (ha : a ∈ U₀)
    (hb : b ∈ U₀) (h : (G.power 2).Adj a b) : ∃ e ∈ O, e = a ∨ e = b := by
  rcases hO a ha b hb h with h | h
  · exact ⟨a, h, Or.inl rfl⟩
  · exact ⟨b, h, Or.inr rfl⟩

lemma two_le_card_of {s : Finset V} {e₁ e₂ : V} (h₁ : e₁ ∈ s) (h₂ : e₂ ∈ s) (h : e₁ ≠ e₂) :
    2 ≤ s.card := by
  have : ({e₁, e₂} : Finset V) ⊆ s := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
  have := card_le_card this
  rwa [card_pair h] at this

lemma three_le_card_of {s : Finset V} {e₁ e₂ e₃ : V} (h₁ : e₁ ∈ s) (h₂ : e₂ ∈ s) (h₃ : e₃ ∈ s)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) : 3 ≤ s.card := by
  have : ({e₁, e₂, e₃} : Finset V) ⊆ s := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := card_le_card this
  rwa [card_eq_three.2 ⟨e₁, e₂, e₃, h12, h13, h23, rfl⟩] at this

/-- Removing `P ⊆ rem` adds `O ∩ P` to the removed part of `O`. -/
lemma card_filter_not_mem_sdiff {O rem P : Finset V} (hP : P ⊆ rem) :
    (O.filter (· ∉ rem \ P)).card = (O.filter (· ∉ rem)).card + (O ∩ P).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext v
    simp only [mem_filter, mem_sdiff, not_and, not_not, mem_union, mem_inter]
    constructor
    · rintro ⟨hv, h⟩
      by_cases hr : v ∈ rem
      · exact Or.inr ⟨hv, h hr⟩
      · exact Or.inl ⟨hv, hr⟩
    · rintro (⟨hv, h⟩ | ⟨hv, h⟩)
      · exact ⟨hv, fun h' => absurd h' h⟩
      · exact ⟨hv, fun _ => h⟩
  · rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [mem_filter, mem_inter] at h1 h2
    exact h1.2 (hP h2.2)

/-- A triangle forces two cover vertices. -/
lemma tri_lb {U₀ O : Finset V} (hO : CoversIn G U₀ O) {a b c : V} (ha₀ : a ∈ U₀)
    (hb₀ : b ∈ U₀) (hc₀ : c ∈ U₀) (hab : (G.power 2).Adj a b) (hbc : (G.power 2).Adj b c) (hac : (G.power 2).Adj a c) :
    2 ≤ (O ∩ {a, b, c}).card := by
  have hm : ∀ v, v ∈ O → (v = a ∨ v = b ∨ v = c) → v ∈ O ∩ {a, b, c} := by
    intro v hv h; simp only [mem_inter, mem_insert, mem_singleton]; exact ⟨hv, h⟩
  rcases hO a ha₀ b hb₀ hab with ha | hb
  · rcases hO b hb₀ c hc₀ hbc with hb | hc
    · exact two_le_card_of (hm a ha (by simp)) (hm b hb (by simp)) hab.ne
    · exact two_le_card_of (hm a ha (by simp)) (hm c hc (by simp)) hac.ne
  · rcases hO a ha₀ c hc₀ hac with ha | hc
    · exact two_le_card_of (hm a ha (by simp)) (hm b hb (by simp)) hab.ne
    · exact two_le_card_of (hm b hb (by simp)) (hm c hc (by simp)) hbc.ne

/-! ### The invariant -/

/-- The invariant of Algorithm 2 (Lemmas 13–16). -/
structure Inv (G : SimpleGraph V) (U₀ : Finset V) (s : State V) : Prop where
  remSub : s.rem ⊆ U₀
  /-- Lemma 16: every edge of `G²[U₀]` is covered or lies in `G²[V']`. -/
  covers : ∀ u ∈ U₀, ∀ v ∈ U₀, (G.power 2).Adj u v →
    (u ∈ s.rem ∧ v ∈ s.rem) ∨ u ∈ s.cover ∨ v ∈ s.cover
  /-- A removed vertex not in `V1` forms no triangle with two remaining vertices. -/
  triClosed : s.phase ≠ .done → ∀ v ∈ U₀, v ∉ s.rem → v ∉ s.V1 → ∀ x ∈ s.rem, ∀ y ∈ s.rem,
    ¬ ((G.power 2).Adj v x ∧ (G.power 2).Adj v y ∧ (G.power 2).Adj x y)
  /-- Lemma 13 (1) / 14 (1): no triangles after part 1. -/
  noTri : s.phase = .two ∨ s.phase = .three → TriangleFree G s.rem
  /-- After part 2 every remaining vertex has degree at least 4. -/
  deg4 : s.phase = .three → ∀ u ∈ s.rem, 4 ≤ deg G s.rem u
  v3 : s.phase ≠ .done → s.V3 = ∅
  doneRem : s.phase = .done → s.rem = ∅
  /-- Lemma 15 (parts 1, 2): `opt₁ ≥ (2/3) s₁`, `opt₂ ≥ (3/5) s₂`, combined. -/
  charge : s.phase ≠ .done → ∀ O : Finset V, CoversIn G U₀ O →
    10 * s.V1.card + 9 * s.V2.card ≤ 15 * ((O ∩ U₀).filter (· ∉ s.rem)).card
  /-- The final bound (Theorem 12; the term `2 |V \ U₀|` accounts for midpoints of `G`-paths
  outside the instance, it vanishes for `U₀ = V`). -/
  approx : s.phase = .done → ∀ O : Finset V, CoversIn G U₀ O →
    18 * s.cover.card ≤ 30 * (O ∩ U₀).card + 2 * (univ \ U₀).card

lemma inv_init (U₀ : Finset V) : Inv G U₀ (init U₀) where
  remSub := subset_rfl
  covers := fun u hu v hv _ => Or.inl ⟨hu, hv⟩
  triClosed := fun _ v hv hv' => absurd hv hv'
  noTri := by simp [init]
  deg4 := by simp [init]
  v3 := by simp [init]
  doneRem := by simp [init]
  charge := by simp [init]
  approx := by simp [init]

/-- Removing vertices from a triangle-free remaining set keeps `triClosed`. -/
lemma triClosed_sdiff {U₀ : Finset V} {s : State V} (hI : Inv G U₀ s) (hp : s.phase = .two)
    {P V1' : Finset V} (hV1 : s.V1 ⊆ V1') :
    ∀ v ∈ U₀, v ∉ s.rem \ P → v ∉ V1' → ∀ x ∈ s.rem \ P, ∀ y ∈ s.rem \ P,
      ¬ ((G.power 2).Adj v x ∧ (G.power 2).Adj v y ∧ (G.power 2).Adj x y) := by
  intro v hv0 hv hv1 x hx y hy h
  simp only [mem_sdiff] at hx hy
  by_cases hvr : v ∈ s.rem
  · exact hI.noTri (Or.inl hp) v hvr x hx.1 y hy.1 ⟨h.1, h.2.2, h.2.1⟩
  · exact hI.triClosed (by simp [hp]) v hv0 hvr (fun h' => hv1 (hV1 h')) x hx.1 y hy.1 h

lemma triangleFree_mono {s t : Finset V} (h : TriangleFree G s) (hts : t ⊆ s) :
    TriangleFree G t := fun a ha b hb c hc => h a (hts ha) b (hts hb) c (hts hc)

/-- Removing `P` from `V'`: the covering invariant is kept if every vertex of `P` is taken into the
cover or has all its remaining neighbours in the cover. -/
lemma covers_remove {U₀ : Finset V} {s t : State V} (hI : Inv G U₀ s) {P : Finset V}
    (hrem : t.rem = s.rem \ P) (hcov : s.cover ⊆ t.cover)
    (hP : ∀ v ∈ P, v ∈ t.cover ∨ ∀ w ∈ s.rem, (G.power 2).Adj v w → w ∈ t.cover) :
    ∀ u ∈ U₀, ∀ v ∈ U₀, (G.power 2).Adj u v →
      (u ∈ t.rem ∧ v ∈ t.rem) ∨ u ∈ t.cover ∨ v ∈ t.cover := by
  intro u hu0 v hv0 huv
  rcases hI.covers u hu0 v hv0 huv with ⟨hu, hv⟩ | h | h
  · by_cases huP : u ∈ P
    · rcases hP u huP with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (h v hv huv))
    by_cases hvP : v ∈ P
    · rcases hP v hvP with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (h u hu huv.symm))
    exact Or.inl ⟨by rw [hrem]; exact mem_sdiff.2 ⟨hu, huP⟩, by rw [hrem]; exact mem_sdiff.2 ⟨hv, hvP⟩⟩
  · exact Or.inr (Or.inl (hcov h))
  · exact Or.inr (Or.inr (hcov h))

/-- Removing `P ⊆ V'`: the charging invariant is kept if the new cover vertices are paid for by
`15 |O ∩ P|`. -/
lemma charge_remove {U₀ : Finset V} {s t : State V} (hI : Inv G U₀ s) (hp : s.phase ≠ .done)
    {P : Finset V} (hrem : t.rem = s.rem \ P) (hPs : P ⊆ s.rem)
    (h : ∀ O : Finset V, CoversIn G U₀ O →
      10 * t.V1.card + 9 * t.V2.card ≤ 10 * s.V1.card + 9 * s.V2.card + 15 * (O ∩ P).card) :
    ∀ O : Finset V, CoversIn G U₀ O →
      10 * t.V1.card + 9 * t.V2.card ≤ 15 * ((O ∩ U₀).filter (· ∉ t.rem)).card := by
  intro O hO
  rw [hrem, card_filter_not_mem_sdiff hPs, inter_assoc,
    inter_eq_right.2 (hPs.trans hI.remSub)]
  have := hI.charge hp O hO
  have := h O hO
  omega

lemma card_union_le_add {A B : Finset V} {k : ℕ} (hB : B.card ≤ k) : (A ∪ B).card ≤ A.card + k :=
  (card_union_le _ _).trans (by omega)

/-- Lemmas 13 (2), (3) and 14 (4): after part 2, `s₁ ≥ |E^blue_{R'}| ≥ (3/2)|V_{R'}|`. -/
lemma blue_bound {U₀ : Finset V} {s : State V} (hI : Inv G U₀ s) (hph : s.phase = .three) :
    3 * s.rem.card ≤ 2 * s.V1.card + 2 * (univ \ U₀).card := by
  have hnt := hI.noTri (Or.inr hph)
  set R := s.rem with hR
  set Pairs := (R ×ˢ R).filter (fun p => (G.power 2).Adj p.1 p.2 ∧ ¬ G.Adj p.1 p.2) with hPairs
  have memP : ∀ p, p ∈ Pairs ↔ (p.1 ∈ R ∧ p.2 ∈ R) ∧ (G.power 2).Adj p.1 p.2 ∧ ¬ G.Adj p.1 p.2 := by
    intro p; simp [Pairs]
  have hmid : ∀ p ∈ Pairs, ∃ w, G.Adj p.1 w ∧ G.Adj w p.2 := by
    intro p hp
    obtain ⟨-, h, hn⟩ := (memP p).1 hp
    rcases (power_two_adj.1 h).2 with h' | h'
    · exact absurd h' hn
    · exact h'
  let mid : V × V → V := fun p =>
    if h : ∃ w, G.Adj p.1 w ∧ G.Adj w p.2 then h.choose else p.1
  have hmid' : ∀ p ∈ Pairs, G.Adj p.1 (mid p) ∧ G.Adj (mid p) p.2 := by
    intro p hp; simp only [mid, hmid p hp, ↓reduceDIte]; exact (hmid p hp).choose_spec
  -- a vertex has at most two `G`-neighbours in `R` (else a triangle in `G²[R]`)
  have hnb : ∀ v, (R.filter fun x => G.Adj v x).card ≤ 2 := by
    intro v
    by_contra hc
    rw [not_le] at hc
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.1 hc
    simp only [mem_filter] at ha hb hc
    exact hnt a ha.1 b hb.1 c hc.1 ⟨power_two_adj_of_adj_adj ha.2.symm hb.2 hab,
      power_two_adj_of_adj_adj hb.2.symm hc.2 hbc, power_two_adj_of_adj_adj ha.2.symm hc.2 hac⟩
  have hmaps : ∀ p ∈ Pairs, mid p ∈ s.V1 ∪ (univ \ U₀) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hmid' p hp
    obtain ⟨hpR, hadj, -⟩ := (memP p).1 hp
    have htri : (G.power 2).Adj (mid p) p.1 ∧ (G.power 2).Adj (mid p) p.2 ∧
        (G.power 2).Adj p.1 p.2 := ⟨h1.symm.power_two, h2.power_two, hadj⟩
    by_contra hv1
    simp only [mem_union, mem_sdiff, mem_univ, true_and, not_or, not_not] at hv1
    by_cases hvr : mid p ∈ R
    · exact hnt _ hvr _ hpR.1 _ hpR.2 ⟨htri.1, htri.2.2, htri.2.1⟩
    · exact hI.triClosed (by simp [hph]) _ hv1.2 hvr hv1.1 _ hpR.1 _ hpR.2 htri
  have hup : Pairs.card ≤ 2 * (s.V1 ∪ (univ \ U₀)).card := by
    apply card_le_mul_card_image_of_maps_to hmaps
    intro v _
    set N := R.filter fun x => G.Adj v x
    have hsub : Pairs.filter (fun p => mid p = v) ⊆ N.offDiag := by
      intro p hp
      rw [mem_filter] at hp
      obtain ⟨h1, h2⟩ := hmid' p hp.1
      obtain ⟨hpR, hadj, -⟩ := (memP p).1 hp.1
      rw [hp.2] at h1 h2
      simp only [N, mem_offDiag, mem_filter]
      exact ⟨⟨hpR.1, h1.symm⟩, ⟨hpR.2, h2⟩, hadj.ne⟩
    calc _ ≤ N.offDiag.card := card_le_card hsub
      _ = N.card * N.card - N.card := offDiag_card N
      _ ≤ 2 := by
        have := hnb v
        interval_cases N.card <;> simp
  have hlow : 3 * R.card ≤ Pairs.card := by
    apply mul_card_image_le_card_of_maps_to (f := Prod.fst)
      (fun p hp => ((memP p).1 hp).1.1)
    intro x hx
    have hd : 4 ≤ deg G R x := hI.deg4 hph x hx
    set Nr := (nbrs G R x).filter (fun y => G.Adj x y)
    set Nb := (nbrs G R x).filter (fun y => ¬ G.Adj x y)
    have hred : Nr.card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      by_contra hab
      simp only [Nr, mem_filter, mem_nbrs] at ha hb
      exact hnt x hx a ha.1.1 b hb.1.1
        ⟨ha.1.2, power_two_adj_of_adj_adj ha.2.symm hb.2 hab, hb.1.2⟩
    have hsplit : Nr.card + Nb.card = deg G R x := card_filter_add_card_filter_not _
    have hsub : Nb.image (fun y => (x, y)) ⊆ Pairs.filter (fun p => p.1 = x) := by
      intro p hp
      simp only [mem_image, Nb, mem_filter, mem_nbrs] at hp
      obtain ⟨y, ⟨⟨hy, hxy⟩, hn⟩, rfl⟩ := hp
      rw [mem_filter, memP]
      exact ⟨⟨⟨hx, hy⟩, hxy, hn⟩, rfl⟩
    calc 3 ≤ Nb.card := by omega
      _ = (Nb.image fun y => (x, y)).card :=
        (card_image_of_injective _ (fun a b h => by simpa using h)).symm
      _ ≤ _ := card_le_card hsub
  have := card_union_le s.V1 (univ \ U₀)
  omega

/-- Part 3 is well defined: `G²[s]` has a 2-approximate vertex cover, e.g. both endpoints of a
maximal matching. -/
lemma exists_twoApprox (s : Finset V) : ∃ C, IsTwoApprox G s C := by
  let IsM : Finset (V × V) → Prop := fun M =>
    (∀ p ∈ M, p.1 ∈ s ∧ p.2 ∈ s ∧ (G.power 2).Adj p.1 p.2) ∧
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2
  obtain ⟨M, hM, hmax⟩ := exists_max_image ((univ : Finset (Finset (V × V))).filter IsM) card
    ⟨∅, by simp [IsM]⟩
  rw [mem_filter] at hM
  obtain ⟨-, hM1, hM2⟩ := hM
  refine ⟨M.image Prod.fst ∪ M.image Prod.snd, ?_, ?_, ?_⟩
  · intro v hv
    simp only [mem_union, mem_image] at hv
    rcases hv with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (hM1 p hp).1
    · exact (hM1 p hp).2.1
  · intro u hu v hv huv
    by_contra hc
    simp only [mem_union, mem_image, not_or, not_exists, not_and] at hc
    obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ := hc
    have hnot : (u, v) ∉ M := fun h => hu1 _ h rfl
    have hIns : IsM (insert (u, v) M) := by
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases mem_insert.1 hp with rfl | hp
        · exact ⟨hu, hv, huv⟩
        · exact hM1 p hp
      · intro p hp q hq hpq
        rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
        · exact absurd rfl hpq
        · exact ⟨fun h => hu1 q hq h.symm, fun h => hu2 q hq h.symm,
            fun h => hv1 q hq h.symm, fun h => hv2 q hq h.symm⟩
        · exact ⟨hu1 p hp, hv1 p hp, hu2 p hp, hv2 p hp⟩
        · exact hM2 p hp q hq hpq
    have := hmax _ (mem_filter.2 ⟨mem_univ _, hIns⟩)
    rw [card_insert_of_notMem hnot] at this
    omega
  · intro D _ hD
    have hMD : M.card ≤ D.card := by
      let f : V × V → V := fun p => if p.1 ∈ D then p.1 else p.2
      apply card_le_card_of_injOn f
      · intro p hp
        obtain ⟨h1, h2, h3⟩ := hM1 p hp
        simp only [f]
        split_ifs with h
        · exact h
        · exact (hD _ h1 _ h2 h3).resolve_left h
      · intro p hp q hq hfpq
        by_contra hpq
        have := hM2 p hp q hq hpq
        simp only [f] at hfpq
        split_ifs at hfpq <;> tauto
    calc (M.image Prod.fst ∪ M.image Prod.snd).card
        ≤ (M.image Prod.fst).card + (M.image Prod.snd).card := card_union_le _ _
      _ ≤ M.card + M.card := add_le_add card_image_le card_image_le
      _ ≤ 2 * D.card := by omega

/-! ### Preservation of the invariant -/

section Preservation

variable {U₀ : Finset V} {s : State V}

lemma inv_tri {a b c : V} (hI : Inv G U₀ s) (hp : s.phase = .one) (ha : a ∈ s.rem)
    (hb : b ∈ s.rem) (hc : c ∈ s.rem) (hab : (G.power 2).Adj a b) (hbc : (G.power 2).Adj b c)
    (hac : (G.power 2).Adj a c) :
    Inv G U₀ { s with rem := s.rem \ {a, b, c}, V1 := s.V1 ∪ {a, b, c} } where
  remSub := sdiff_subset.trans hI.remSub
  covers := covers_remove hI rfl
    (by intro v hv; simp only [State.cover, mem_union] at hv ⊢; tauto)
    (fun v hv => Or.inl (by
      simp only [State.cover, mem_union, mem_insert, mem_singleton] at hv ⊢; tauto))
  triClosed := fun _ v hv0 hv hv1 x hx y hy => by
    simp only [mem_sdiff, mem_union, mem_insert, mem_singleton, not_and, not_or] at hv hv1 hx hy
    exact hI.triClosed (by simp [hp]) v hv0 (fun h => by have := hv h; tauto) hv1.1 x hx.1 y hy.1
  noTri := by simp [hp]
  deg4 := by simp [hp]
  v3 := fun h => hI.v3 h
  doneRem := by simp [hp]
  charge := fun _ => charge_remove hI (by simp [hp]) rfl
    (by intro v hv; simp only [mem_insert, mem_singleton] at hv; rcases hv with rfl | rfl | rfl <;>
          assumption)
    (fun O hO => by
      have h1 := tri_lb hO (hI.remSub ha) (hI.remSub hb) (hI.remSub hc) hab hbc hac
      have h2 : (s.V1 ∪ {a, b, c}).card ≤ s.V1.card + 3 := card_union_le_add card_le_three
      dsimp only
      omega)
  approx := by simp [hp]

lemma inv_iso {v : V} (hI : Inv G U₀ s) (hp : s.phase = .one ∨ s.phase = .two) (hv : v ∈ s.rem)
    (hd : deg G s.rem v = 0) : Inv G U₀ { s with rem := s.rem \ {v} } := by
  have hnb : ∀ w ∈ s.rem, ¬ (G.power 2).Adj v w := by
    intro w hw hadj
    have : w ∈ nbrs G s.rem v := mem_nbrs.2 ⟨hw, hadj⟩
    rw [deg, card_eq_zero] at hd
    simp [hd] at this
  have hnd : s.phase ≠ .done := by rcases hp with h | h <;> simp [h]
  exact {
    remSub := sdiff_subset.trans hI.remSub
    covers := covers_remove hI rfl subset_rfl (fun w hw => Or.inr (by
      intro u hu hadj
      rw [mem_singleton] at hw
      subst hw
      exact absurd hadj (hnb u hu)))
    triClosed := fun _ w hw0 hw hw1 x hx y hy h => by
      simp only [mem_sdiff, mem_singleton, not_and, not_not] at hw hx hy
      by_cases hwv : w = v
      · subst hwv; exact hnb x hx.1 h.1
      · exact hI.triClosed hnd w hw0 (fun h' => hwv (hw h')) hw1 x hx.1 y hy.1 h
    noTri := fun h => triangleFree_mono (hI.noTri h) sdiff_subset
    deg4 := fun h => by rcases hp with hp | hp <;> simp [hp] at h
    v3 := fun _ => hI.v3 hnd
    doneRem := fun h => absurd h hnd
    charge := fun _ => charge_remove hI hnd rfl (by simpa using hv) (fun O _ => by dsimp only; omega)
    approx := fun h => absurd h hnd }

lemma inv_endOne (hI : Inv G U₀ s) (hp : s.phase = .one) (h : TriangleFree G s.rem) :
    Inv G U₀ { s with phase := .two } where
  remSub := hI.remSub
  covers := hI.covers
  triClosed := fun _ => hI.triClosed (by simp [hp])
  noTri := fun _ => h
  deg4 := by simp
  v3 := fun _ => hI.v3 (by simp [hp])
  doneRem := by simp
  charge := fun _ => hI.charge (by simp [hp])
  approx := by simp

lemma inv_deg1 {x y : V} (hI : Inv G U₀ s) (hp : s.phase = .two) (hx : x ∈ s.rem)
    (hn : nbrs G s.rem x = {y}) :
    Inv G U₀ { s with rem := s.rem \ {x, y}, V2 := s.V2 ∪ {y} } := by
  have hy : y ∈ s.rem ∧ (G.power 2).Adj x y := mem_nbrs.1 (by rw [hn]; exact mem_singleton_self y)
  have hnd : s.phase ≠ .done := by simp [hp]
  exact {
    remSub := sdiff_subset.trans hI.remSub
    covers := covers_remove hI rfl
      (by intro v hv; simp only [State.cover, mem_union] at hv ⊢; tauto)
      (fun v hv => by
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · refine Or.inr fun w hw hadj => ?_
          have : w ∈ nbrs G s.rem v := mem_nbrs.2 ⟨hw, hadj⟩
          rw [hn, mem_singleton] at this
          subst this
          simp [State.cover]
        · exact Or.inl (by simp [State.cover]))
    triClosed := fun _ => triClosed_sdiff hI hp subset_rfl
    noTri := fun h => triangleFree_mono (hI.noTri h) sdiff_subset
    deg4 := by simp [hp]
    v3 := fun _ => hI.v3 hnd
    doneRem := by simp [hp]
    charge := fun _ => charge_remove hI hnd rfl
      (by intro v hv; simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact hx
          · exact hy.1)
      (fun O hO => by
        obtain ⟨e, he, he'⟩ := exists_mem_of_adj hO (hI.remSub hx) (hI.remSub hy.1) hy.2
        have h1 : 1 ≤ (O ∩ {x, y}).card :=
          card_pos.2 ⟨e, mem_inter.2 ⟨he, by rcases he' with rfl | rfl <;> simp⟩⟩
        have h2 : (s.V2 ∪ {y}).card ≤ s.V2.card + 1 := card_union_le_add (card_singleton y).le
        dsimp only
        omega)
    approx := by simp [hp] }

lemma inv_deg2 {x y₁ y₂ z : V} (hI : Inv G U₀ s) (hp : s.phase = .two) (hx : x ∈ s.rem)
    (hn : nbrs G s.rem x = {y₁, y₂}) (hy : y₁ ≠ y₂) (hz : z ∈ s.rem)
    (hyz : (G.power 2).Adj y₁ z) (hzx : z ≠ x) :
    Inv G U₀ { s with rem := s.rem \ {x, y₁, y₂, z}, V2 := s.V2 ∪ {z, y₁, y₂} } := by
  have hy₁ : y₁ ∈ s.rem ∧ (G.power 2).Adj x y₁ := mem_nbrs.1 (by rw [hn]; simp)
  have hy₂ : y₂ ∈ s.rem ∧ (G.power 2).Adj x y₂ := mem_nbrs.1 (by rw [hn]; simp)
  have hnd : s.phase ≠ .done := by simp [hp]
  have hnt := hI.noTri (Or.inl hp)
  have hzy₂ : z ≠ y₂ := by
    rintro rfl
    exact hnt x hx y₁ hy₁.1 z hz ⟨hy₁.2, hyz, hy₂.2⟩
  exact {
    remSub := sdiff_subset.trans hI.remSub
    covers := covers_remove hI rfl
      (by intro v hv; simp only [State.cover, mem_union] at hv ⊢; tauto)
      (fun v hv => by
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · refine Or.inr fun w hw hadj => ?_
          have : w ∈ nbrs G s.rem v := mem_nbrs.2 ⟨hw, hadj⟩
          rw [hn] at this
          simp only [mem_insert, mem_singleton] at this
          rcases this with rfl | rfl <;> simp [State.cover]
        all_goals exact Or.inl (by simp [State.cover]))
    triClosed := fun _ => triClosed_sdiff hI hp subset_rfl
    noTri := fun h => triangleFree_mono (hI.noTri h) sdiff_subset
    deg4 := by simp [hp]
    v3 := fun _ => hI.v3 hnd
    doneRem := by simp [hp]
    charge := fun _ => charge_remove hI hnd rfl
      (by intro v hv; simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl
          · exact hx
          · exact hy₁.1
          · exact hy₂.1
          · exact hz)
      (fun O hO => by
        obtain ⟨e₁, he₁, he₁'⟩ := exists_mem_of_adj hO (hI.remSub hx) (hI.remSub hy₂.1) hy₂.2
        obtain ⟨e₂, he₂, he₂'⟩ := exists_mem_of_adj hO (hI.remSub hy₁.1) (hI.remSub hz) hyz
        have hne : e₁ ≠ e₂ := by
          rcases he₁' with rfl | rfl <;> rcases he₂' with rfl | rfl
          · exact hy₁.2.ne
          · exact hzx.symm
          · exact hy.symm
          · exact hzy₂.symm
        have h1 : 2 ≤ (O ∩ {x, y₁, y₂, z}).card :=
          two_le_card_of (mem_inter.2 ⟨he₁, by rcases he₁' with rfl | rfl <;> simp⟩)
            (mem_inter.2 ⟨he₂, by rcases he₂' with rfl | rfl <;> simp⟩) hne
        have h2 : (s.V2 ∪ {z, y₁, y₂}).card ≤ s.V2.card + 3 := card_union_le_add card_le_three
        dsimp only
        omega)
    approx := by simp [hp] }

lemma inv_deg3 {x y₁ y₂ y₃ z₁ z₂ : V} (hI : Inv G U₀ s) (hp : s.phase = .two) (hx : x ∈ s.rem)
    (hn : nbrs G s.rem x = {y₁, y₂, y₃}) (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃)
    (hz₁ : z₁ ∈ s.rem) (hz₂ : z₂ ∈ s.rem) (hyz₁ : (G.power 2).Adj y₁ z₁)
    (hyz₂ : (G.power 2).Adj y₂ z₂) (hzz : z₁ ≠ z₂) (hz₁' : z₁ ∉ ({x, y₁, y₂, y₃} : Finset V))
    (hz₂' : z₂ ∉ ({x, y₁, y₂, y₃} : Finset V)) :
    Inv G U₀ { s with rem := s.rem \ {x, y₁, y₂, y₃, z₁, z₂},
                      V2 := s.V2 ∪ {y₁, y₂, y₃, z₁, z₂} } := by
  have hy₁ : y₁ ∈ s.rem ∧ (G.power 2).Adj x y₁ := mem_nbrs.1 (by rw [hn]; simp)
  have hy₂ : y₂ ∈ s.rem ∧ (G.power 2).Adj x y₂ := mem_nbrs.1 (by rw [hn]; simp)
  have hy₃ : y₃ ∈ s.rem ∧ (G.power 2).Adj x y₃ := mem_nbrs.1 (by rw [hn]; simp)
  have hnd : s.phase ≠ .done := by simp [hp]
  simp only [mem_insert, mem_singleton, not_or] at hz₁' hz₂'
  exact {
    remSub := sdiff_subset.trans hI.remSub
    covers := covers_remove hI rfl
      (by intro v hv; simp only [State.cover, mem_union] at hv ⊢; tauto)
      (fun v hv => by
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
        · refine Or.inr fun w hw hadj => ?_
          have : w ∈ nbrs G s.rem v := mem_nbrs.2 ⟨hw, hadj⟩
          rw [hn] at this
          simp only [mem_insert, mem_singleton] at this
          rcases this with rfl | rfl | rfl <;> simp [State.cover]
        all_goals exact Or.inl (by simp [State.cover]))
    triClosed := fun _ => triClosed_sdiff hI hp subset_rfl
    noTri := fun h => triangleFree_mono (hI.noTri h) sdiff_subset
    deg4 := by simp [hp]
    v3 := fun _ => hI.v3 hnd
    doneRem := by simp [hp]
    charge := fun _ => charge_remove hI hnd rfl
      (by intro v hv; simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hx
          · exact hy₁.1
          · exact hy₂.1
          · exact hy₃.1
          · exact hz₁
          · exact hz₂)
      (fun O hO => by
        obtain ⟨e₁, he₁, he₁'⟩ := exists_mem_of_adj hO (hI.remSub hx) (hI.remSub hy₃.1) hy₃.2
        obtain ⟨e₂, he₂, he₂'⟩ :=
          exists_mem_of_adj hO (hI.remSub hy₁.1) (hI.remSub hz₁) hyz₁
        obtain ⟨e₃, he₃, he₃'⟩ :=
          exists_mem_of_adj hO (hI.remSub hy₂.1) (hI.remSub hz₂) hyz₂
        have hxy₁ := hy₁.2.ne
        have hxy₂ := hy₂.2.ne
        have n12 : e₁ ≠ e₂ := by
          rcases he₁' with rfl | rfl <;> rcases he₂' with rfl | rfl <;> tauto
        have n13 : e₁ ≠ e₃ := by
          rcases he₁' with rfl | rfl <;> rcases he₃' with rfl | rfl <;> tauto
        have n23 : e₂ ≠ e₃ := by
          rcases he₂' with rfl | rfl <;> rcases he₃' with rfl | rfl <;> tauto
        have h1 : 3 ≤ (O ∩ {x, y₁, y₂, y₃, z₁, z₂}).card :=
          three_le_card_of (mem_inter.2 ⟨he₁, by rcases he₁' with rfl | rfl <;> simp⟩)
            (mem_inter.2 ⟨he₂, by rcases he₂' with rfl | rfl <;> simp⟩)
            (mem_inter.2 ⟨he₃, by rcases he₃' with rfl | rfl <;> simp⟩) n12 n13 n23
        have h2 : (s.V2 ∪ {y₁, y₂, y₃, z₁, z₂}).card ≤ s.V2.card + 5 :=
          card_union_le_add (by
            have a1 := card_insert_le y₁ ({y₂, y₃, z₁, z₂} : Finset V)
            have a2 := card_insert_le y₂ ({y₃, z₁, z₂} : Finset V)
            have a3 := card_insert_le y₃ ({z₁, z₂} : Finset V)
            have a4 := card_le_two (a := z₁) (b := z₂)
            omega)
        dsimp only
        omega)
    approx := by simp [hp] }

lemma inv_endTwo (hI : Inv G U₀ s) (hp : s.phase = .two) (h : ∀ u ∈ s.rem, 4 ≤ deg G s.rem u) :
    Inv G U₀ { s with phase := .three } where
  remSub := hI.remSub
  covers := hI.covers
  triClosed := fun _ => hI.triClosed (by simp [hp])
  noTri := fun _ => hI.noTri (Or.inl hp)
  deg4 := fun _ => h
  v3 := fun _ => hI.v3 (by simp [hp])
  doneRem := by simp
  charge := fun _ => hI.charge (by simp [hp])
  approx := by simp

lemma inv_final {C : Finset V} (hI : Inv G U₀ s) (hp : s.phase = .three)
    (hC : IsTwoApprox G s.rem C) : Inv G U₀ { s with phase := .done, rem := ∅, V3 := C } := by
  have hv3 := hI.v3 (by simp [hp])
  exact {
    remSub := empty_subset _
    covers := fun u hu0 v hv0 huv => by
      rcases hI.covers u hu0 v hv0 huv with ⟨hu, hv⟩ | h | h
      · rcases hC.2.1 u hu v hv huv with h | h
        · exact Or.inr (Or.inl (by simp [State.cover, h]))
        · exact Or.inr (Or.inr (by simp [State.cover, h]))
      · simp only [State.cover, hv3, mem_union] at h
        exact Or.inr (Or.inl (by simp only [State.cover, mem_union]; tauto))
      · simp only [State.cover, hv3, mem_union] at h
        exact Or.inr (Or.inr (by simp only [State.cover, mem_union]; tauto))
    triClosed := fun h => absurd rfl h
    noTri := by simp
    deg4 := by simp
    v3 := fun h => absurd rfl h
    doneRem := fun _ => rfl
    charge := fun h => absurd rfl h
    approx := fun _ O hO => by
      have hb := blue_bound hI hp
      have hch := hI.charge (by simp [hp]) O hO
      set D := (O ∩ U₀).filter (· ∈ s.rem)
      have hD : C.card ≤ 2 * D.card := hC.2.2 D (fun v hv => (mem_filter.1 hv).2) (by
        intro u hu v hv huv
        rcases hO u (hI.remSub hu) v (hI.remSub hv) huv with h | h
        · exact Or.inl (mem_filter.2 ⟨mem_inter.2 ⟨h, hI.remSub hu⟩, hu⟩)
        · exact Or.inr (mem_filter.2 ⟨mem_inter.2 ⟨h, hI.remSub hv⟩, hv⟩))
      have hCr : C.card ≤ s.rem.card := card_le_card hC.1
      have hsplit : ((O ∩ U₀).filter (· ∉ s.rem)).card + D.card = (O ∩ U₀).card := by
        rw [add_comm]; exact card_filter_add_card_filter_not _
      have hcov : (s.V1 ∪ s.V2 ∪ C).card ≤ s.V1.card + s.V2.card + C.card :=
        (card_union_le _ _).trans (by have := card_union_le s.V1 s.V2; omega)
      simp only [State.cover]
      omega }

/-- The invariant is preserved by every step. -/
theorem inv_step {s t : State V} (hI : Inv G U₀ s) (hst : Step G s t) : Inv G U₀ t := by
  cases hst with
  | tri hp ha hb hc hab hbc hac => exact inv_tri hI hp ha hb hc hab hbc hac
  | iso hp hv hd => exact inv_iso hI hp hv hd
  | endOne hp h => exact inv_endOne hI hp h
  | deg1 hp hx hn => exact inv_deg1 hI hp hx hn
  | deg2 hp _ hx hn hy hz hyz hzx => exact inv_deg2 hI hp hx hn hy hz hyz hzx
  | deg3 hp _ hx hn h12 h13 h23 hz₁ hz₂ hyz₁ hyz₂ hzz hz₁' hz₂' =>
    exact inv_deg3 hI hp hx hn h12 h13 h23 hz₁ hz₂ hyz₁ hyz₂ hzz hz₁' hz₂'
  | endTwo hp h => exact inv_endTwo hI hp h
  | final hp hC => exact inv_final hI hp hC

theorem inv_of_reach {s : State V} (h : ReflTransGen (Step G) (init U₀) s) : Inv G U₀ s := by
  induction h with
  | refl => exact inv_init U₀
  | tail _ hst ih => exact inv_step ih hst

end Preservation

/-! ### Main results -/

/-- **Theorem 12 of [BCMPP20]** (Algorithm 2, with `α = 5/3` as in the abstract and in the proof).
Every complete run of Algorithm 2 on `G` outputs a vertex cover `S` of `G²` with
`|S| ≤ (5/3) |OPT|` for every vertex cover `OPT` of `G²`. -/
theorem theorem_12 {s : State V} (h : ReflTransGen (Step G) (init univ) s)
    (hs : s.phase = .done) :
    (G.power 2).IsVertexCover (s.cover : Set V) ∧
      ∀ O : Finset V, (G.power 2).IsVertexCover (O : Set V) → 3 * s.cover.card ≤ 5 * O.card := by
  have hI := inv_of_reach h
  refine ⟨fun u v huv => ?_, fun O hO => ?_⟩
  · rcases hI.covers u (mem_univ _) v (mem_univ _) huv with ⟨hu, -⟩ | h | h
    · simp [hI.doneRem hs] at hu
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  · have := hI.approx hs O (fun u _ v _ huv => hO huv)
    simp only [inter_univ, sdiff_self, bot_eq_empty, card_empty, mul_zero, add_zero] at this
    omega

/-- Lemma 16 of [BCMPP20]: the output is a vertex cover of `G²`. -/
theorem lemma_16 {s : State V} (h : ReflTransGen (Step G) (init univ) s)
    (hs : s.phase = .done) :
    (G.power 2).IsVertexCover (s.cover : Set V) := (theorem_12 h hs).1

/-- Algorithm 2 run on an induced subgraph `G²[U₀]` (needed for Corollary 17): the output covers
`G²[U₀]`, and `18 |S| ≤ 30 |O ∩ U₀| + 2 |V \ U₀|` for every cover `O` of `G²[U₀]`. The extra
term comes from Lemma 13 (3): a blue edge of the remaining graph may have its `G`-midpoint
outside `U₀` instead of in `V1`. -/
theorem induced_bound {U₀ : Finset V} {s : State V} (h : ReflTransGen (Step G) (init U₀) s)
    (hs : s.phase = .done) :
    CoversIn G U₀ s.cover ∧ ∀ O : Finset V, CoversIn G U₀ O →
      18 * s.cover.card ≤ 30 * (O ∩ U₀).card + 2 * (univ \ U₀).card := by
  have hI := inv_of_reach h
  refine ⟨fun u hu v hv huv => ?_, hI.approx hs⟩
  rcases hI.covers u hu v hv huv with ⟨hu', -⟩ | h | h
  · simp [hI.doneRem hs] at hu'
  · exact Or.inl h
  · exact Or.inr h

/-- The guards of Algorithm 2 can always be met: every reachable state that is not final has a
successor. In particular the existence claims of lines 9 and 10 (a neighbour `z ≠ x` of `y₁`;
`z₁ ≠ z₂`, outside `{x, y₁, y₂, y₃}`) hold, using that `G²[V']` is triangle-free in part 2. -/
theorem exists_step {U₀ : Finset V} {s : State V} (h : ReflTransGen (Step G) (init U₀) s) (hs : s.phase ≠ .done) :
    ∃ t, Step G s t := by
  have hI := inv_of_reach h
  cases hph : s.phase with
  | done => exact absurd hph hs
  | three => exact ⟨_, .final hph (exists_twoApprox s.rem).choose_spec⟩
  | one =>
    by_cases ht : TriangleFree G s.rem
    · exact ⟨_, .endOne hph ht⟩
    · simp only [TriangleFree, not_forall, not_not] at ht
      obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac⟩ := ht
      exact ⟨_, .tri hph ha hb hc hab hbc hac⟩
  | two =>
    have hnt := hI.noTri (Or.inl hph)
    have hdeg_pos : ∀ x ∈ s.rem, ∀ y ∈ nbrs G s.rem x, 1 ≤ deg G s.rem y := by
      intro x hx y hy
      exact card_pos.2 ⟨x, mem_nbrs.2 ⟨hx, (mem_nbrs.1 hy).2.symm⟩⟩
    by_cases h4 : ∀ u ∈ s.rem, 4 ≤ deg G s.rem u
    · exact ⟨_, .endTwo hph h4⟩
    simp only [not_forall, not_le] at h4
    obtain ⟨x, hx, hx3⟩ := h4
    by_cases h0 : ∃ u ∈ s.rem, deg G s.rem u = 0
    · obtain ⟨u, hu, hu0⟩ := h0
      exact ⟨_, .iso (Or.inr hph) hu hu0⟩
    by_cases h1 : ∃ u ∈ s.rem, deg G s.rem u = 1
    · obtain ⟨u, hu, hu1⟩ := h1
      obtain ⟨y, hy⟩ := card_eq_one.1 hu1
      exact ⟨_, .deg1 hph hu hy⟩
    simp only [not_exists, not_and] at h0 h1
    by_cases h2 : ∃ u ∈ s.rem, deg G s.rem u = 2
    · obtain ⟨u, hu, hu2⟩ := h2
      obtain ⟨y₁, y₂, hy, hn⟩ := card_eq_two.1 hu2
      have hy₁ : y₁ ∈ nbrs G s.rem u := by rw [hn]; simp
      have hd : 2 ≤ deg G s.rem y₁ := by
        have := hdeg_pos u hu y₁ hy₁
        have := h1 y₁ (mem_nbrs.1 hy₁).1
        omega
      obtain ⟨z, hz⟩ : ((nbrs G s.rem y₁).erase u).Nonempty := by
        rw [← card_pos]
        have := pred_card_le_card_erase (s := nbrs G s.rem y₁) (a := u)
        unfold deg at hd
        omega
      rw [mem_erase, mem_nbrs] at hz
      exact ⟨_, .deg2 hph h1 hu hn hy hz.2.1 hz.2.2 hz.1⟩
    simp only [not_exists, not_and] at h2
    have hx3' : deg G s.rem x = 3 := by
      have := h0 x hx; have := h1 x hx; have := h2 x hx; omega
    obtain ⟨y₁, y₂, y₃, h12, h13, h23, hn⟩ := card_eq_three.1 hx3'
    have hy₁ : y₁ ∈ nbrs G s.rem x := by rw [hn]; simp
    have hy₂ : y₂ ∈ nbrs G s.rem x := by rw [hn]; simp
    have hy₃ : y₃ ∈ nbrs G s.rem x := by rw [hn]; simp
    have hd : ∀ y ∈ nbrs G s.rem x, 3 ≤ deg G s.rem y := by
      intro y hy
      have := hdeg_pos x hx y hy
      have := h1 y (mem_nbrs.1 hy).1
      have := h2 y (mem_nbrs.1 hy).1
      omega
    obtain ⟨z₁, hz₁⟩ : ((nbrs G s.rem y₁).erase x).Nonempty := by
      rw [← card_pos]
      have := pred_card_le_card_erase (s := nbrs G s.rem y₁) (a := x)
      have := hd y₁ hy₁
      unfold deg at this
      omega
    obtain ⟨z₂, hz₂⟩ : (((nbrs G s.rem y₂).erase x).erase z₁).Nonempty := by
      rw [← card_pos]
      have := pred_card_le_card_erase (s := (nbrs G s.rem y₂).erase x) (a := z₁)
      have := pred_card_le_card_erase (s := nbrs G s.rem y₂) (a := x)
      have := hd y₂ hy₂
      unfold deg at this
      omega
    rw [mem_erase, mem_nbrs] at hz₁
    rw [mem_erase, mem_erase, mem_nbrs] at hz₂
    rw [mem_nbrs] at hy₁ hy₂ hy₃
    -- triangle-freeness excludes `zᵢ = yⱼ`
    have t12 : ¬ (G.power 2).Adj y₁ y₂ := fun h =>
      hnt x hx y₁ hy₁.1 y₂ hy₂.1 ⟨hy₁.2, h, hy₂.2⟩
    have t13 : ¬ (G.power 2).Adj y₁ y₃ := fun h =>
      hnt x hx y₁ hy₁.1 y₃ hy₃.1 ⟨hy₁.2, h, hy₃.2⟩
    have t23 : ¬ (G.power 2).Adj y₂ y₃ := fun h =>
      hnt x hx y₂ hy₂.1 y₃ hy₃.1 ⟨hy₂.2, h, hy₃.2⟩
    have hz₁' : z₁ ∉ ({x, y₁, y₂, y₃} : Finset V) := by
      simp only [mem_insert, mem_singleton, not_or]
      refine ⟨hz₁.1, fun h => hz₁.2.2.ne h.symm, fun h => t12 (h ▸ hz₁.2.2),
        fun h => t13 (h ▸ hz₁.2.2)⟩
    have hz₂' : z₂ ∉ ({x, y₁, y₂, y₃} : Finset V) := by
      simp only [mem_insert, mem_singleton, not_or]
      refine ⟨hz₂.2.1, fun h => t12 (h ▸ hz₂.2.2.2).symm, fun h => hz₂.2.2.2.ne h.symm,
        fun h => t23 (h ▸ hz₂.2.2.2)⟩
    exact ⟨_, .deg3 hph (fun u hu => ⟨h1 u hu, h2 u hu⟩) hx hn h12 h13 h23 hz₁.2.1
      hz₂.2.2.1 hz₁.2.2 hz₂.2.2.2 (Ne.symm hz₂.1) hz₁' hz₂'⟩

/-- Rank of a phase (number of phase changes left). -/
def Phase.rank : Phase → ℕ
  | .one => 3
  | .two => 2
  | .three => 1
  | .done => 0

/-- Termination measure: remaining vertices plus phase changes left. -/
def measure (s : State V) : ℕ := s.rem.card + s.phase.rank

lemma card_sdiff_lt {rem P : Finset V} {x : V} (hx : x ∈ rem) (hxP : x ∈ P) :
    (rem \ P).card < rem.card :=
  card_lt_card (Finset.ssubset_of_subset_of_ssubset (fun v hv => by
    rw [mem_sdiff] at hv; exact mem_erase.2 ⟨fun h => hv.2 (h ▸ hxP), hv.1⟩) (erase_ssubset hx))

/-- Every step decreases the measure. -/
lemma measure_lt {s t : State V} (h : Step G s t) : measure t < measure s := by
  cases h with
  | tri hp ha => dsimp only [measure]; exact Nat.add_lt_add_right (card_sdiff_lt ha (by simp)) _
  | iso hp hv => dsimp only [measure]; exact Nat.add_lt_add_right (card_sdiff_lt hv (by simp)) _
  | endOne hp => simp [measure, Phase.rank, hp]
  | deg1 hp hx => dsimp only [measure]; exact Nat.add_lt_add_right (card_sdiff_lt hx (by simp)) _
  | deg2 hp _ hx => dsimp only [measure]; exact Nat.add_lt_add_right (card_sdiff_lt hx (by simp)) _
  | deg3 hp _ hx => dsimp only [measure]; exact Nat.add_lt_add_right (card_sdiff_lt hx (by simp)) _
  | endTwo hp => simp [measure, Phase.rank, hp]
  | final hp => simp [measure, Phase.rank, hp]

/-- Polynomial running time (step count): every run of Algorithm 2 has at most `n + 3` steps
(each step removes a vertex or ends a part). -/
theorem run_length_le {U₀ : Finset V} (f : ℕ → State V) (m : ℕ) (h0 : f 0 = init U₀)
    (hf : ∀ i < m, Step G (f i) (f (i + 1))) : m ≤ U₀.card + 3 := by
  have : ∀ i ≤ m, measure (f i) + i ≤ U₀.card + 3 := by
    intro i hi
    induction i with
    | zero => simp [h0, measure, init, Phase.rank]
    | succ i ih =>
      have := measure_lt (hf i (by omega))
      have := ih (by omega)
      omega
  have := this m le_rfl
  omega

/-- Algorithm 2 always terminates with an output: a complete run exists. -/
theorem exists_run (U₀ : Finset V) :
    ∃ s, ReflTransGen (Step G) (init U₀) s ∧ s.phase = .done := by
  suffices H : ∀ k, ∀ s, ReflTransGen (Step G) (init U₀) s → measure s ≤ k →
      ∃ t, ReflTransGen (Step G) (init U₀) t ∧ t.phase = .done from
    H _ (init U₀) .refl le_rfl
  intro k
  induction k with
  | zero =>
    intro s hs hk
    refine ⟨s, hs, ?_⟩
    cases hph : s.phase <;> simp_all [measure, Phase.rank]
  | succ k ih =>
    intro s hs hk
    by_cases hd : s.phase = .done
    · exact ⟨s, hs, hd⟩
    obtain ⟨t, ht⟩ := exists_step hs hd
    exact ih t (hs.tail ht) (by have := measure_lt ht; omega)

end Podc.PowerGraphApproximation.Centralized
