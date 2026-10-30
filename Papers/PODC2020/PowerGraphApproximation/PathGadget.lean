import Podc.Foundations.Combinatorics.SimpleGraph.Power
import Mathlib

/-!
# Attaching path gadgets to a graph, and the square of the result

This file contains the graph-theoretic core of Lemmas 21, 23 and 24 of
Bar-Yehuda, Censor-Hillel, Maus, Pai, Pemmaraju, *Distributed Approximation on Power Graphs*,
PODC 2020 (arXiv:2006.03746), in a form independent of the concrete lower-bound graphs.

Given a "core" graph `core` on `V` (the edges that are kept, e.g. the clique edges), a set `E` of
gadgets and an attachment relation `att e v` (the vertices to which the first vertex of gadget `e`
is joined), `attach core att m` is the graph on `V ⊕ E × Fin m` in which
* `inl u ~ inl v` iff `core.Adj u v`,
* gadget `e` is a path `(e,0) – (e,1) – ⋯ – (e,m-1)`,
* `(e,0) ~ inl v` iff `att e v`.

For `m = 1` this is the weighted construction of Section 5.2 (the single vertex `p_e` of weight
`0`), for `m = 3` the dangling/shared path gadgets of Section 5.3 (`DP_e[1], DP_e[2], DP_e[3]`).

If `G` is a graph on `V` with `G.Adj u v ↔ u ≠ v ∧ (core-edge ∨ core-2-path ∨ common gadget)`
(`IsSquareTrace`), then the square of `attach core att m` restricted to `V` is `G`
(`attach_sq_inl_iff`), and:
* `weighted_iff` (Lemma 21): the square has a vertex cover of weight `≤ W` (weight `1` on `V`,
  `0` on gadget vertices) iff `G` has a vertex cover of size `≤ W`;
* `normalize` (Lemma 23, `m = 3`): every vertex cover of the square can be turned into one, not
  larger, that contains `(e,0), (e,1)` and not `(e,2)` for every gadget;
* `unweighted_iff`, `vertexCoverNum_sq` (Lemma 24, `m = 3`):
  `τ(H²) = τ(G) + 2 |E|`.
-/

namespace Podc.PowerGraphApproximation.LowerBound

open SimpleGraph Finset

variable {V E : Type*}

/-- Attach to every gadget `e : E` a path of `m` new vertices `(e,0), …, (e,m-1)`, the first of
which is joined to all `v` with `att e v`; the vertices of `V` keep only the `core` edges. -/
def attach (core : SimpleGraph V) (att : E → V → Bool) (m : ℕ) [NeZero m] :
    SimpleGraph (V ⊕ E × Fin m) where
  Adj a b := match a, b with
    | .inl u, .inl v => core.Adj u v
    | .inl u, .inr (e, p) => p = 0 ∧ att e u = true
    | .inr (e, p), .inl u => p = 0 ∧ att e u = true
    | .inr (e, p), .inr (e', q) => e = e' ∧ (p.val + 1 = q.val ∨ q.val + 1 = p.val)
  symm := ⟨fun a b h => by
    rcases a with u | ⟨e, p⟩ <;> rcases b with v | ⟨e', q⟩
    · exact h.symm
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => by
    rcases a with u | ⟨e, p⟩
    · exact core.loopless.irrefl _ h
    · rcases h.2 with h | h <;> omega⟩

variable {core : SimpleGraph V} {att : E → V → Bool} {m : ℕ} [NeZero m]

instance [DecidableRel core.Adj] [DecidableEq E] : DecidableRel (attach core att m).Adj :=
  fun a b => match a, b with
    | .inl u, .inl v => inferInstanceAs (Decidable (core.Adj u v))
    | .inl u, .inr (e, p) => inferInstanceAs (Decidable (p = 0 ∧ att e u = true))
    | .inr (e, p), .inl u => inferInstanceAs (Decidable (p = 0 ∧ att e u = true))
    | .inr (e, p), .inr (e', q) =>
      inferInstanceAs (Decidable (e = e' ∧ (p.val + 1 = q.val ∨ q.val + 1 = p.val)))

@[simp] lemma attach_inl_inl {u v : V} : (attach core att m).Adj (.inl u) (.inl v) ↔ core.Adj u v :=
  Iff.rfl

@[simp] lemma attach_inl_inr {u : V} {e : E} {p : Fin m} :
    (attach core att m).Adj (.inl u) (.inr (e, p)) ↔ p = 0 ∧ att e u = true := Iff.rfl

@[simp] lemma attach_inr_inl {u : V} {e : E} {p : Fin m} :
    (attach core att m).Adj (.inr (e, p)) (.inl u) ↔ p = 0 ∧ att e u = true := Iff.rfl

@[simp] lemma attach_inr_inr {e e' : E} {p q : Fin m} :
    (attach core att m).Adj (.inr (e, p)) (.inr (e', q)) ↔
      e = e' ∧ (p.val + 1 = q.val ∨ q.val + 1 = p.val) := Iff.rfl

/-- Adjacency in the square between two vertices of `V`: a core edge, a core path of length two,
or a common gadget. -/
lemma attach_sq_inl_inl {u v : V} :
    ((attach core att m).power 2).Adj (.inl u) (.inl v) ↔
      u ≠ v ∧ (core.Adj u v ∨ (∃ w, core.Adj u w ∧ core.Adj w v) ∨
        ∃ e, att e u = true ∧ att e v = true) := by
  rw [power_two_adj]
  refine and_congr (by simp) ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | ⟨w, h1, h2⟩
    · exact Or.inl h
    · rcases w with w | ⟨e, p⟩
      · exact Or.inr (Or.inl ⟨w, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨e, h1.2, h2.2⟩)
  · rcases h with h | ⟨w, h1, h2⟩ | ⟨e, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨.inl w, h1, h2⟩
    · exact Or.inr ⟨.inr (e, 0), ⟨rfl, h1⟩, ⟨rfl, h2⟩⟩

/-- `G` is the trace of the square of `attach core att m` on `V`: two distinct vertices are
adjacent in `G` iff they are joined by a core edge, a core path of length two, or a common
gadget. -/
def IsSquareTrace (G : SimpleGraph V) (core : SimpleGraph V) (att : E → V → Bool) : Prop :=
  ∀ u v, G.Adj u v ↔ u ≠ v ∧ (core.Adj u v ∨ (∃ w, core.Adj u w ∧ core.Adj w v) ∨
    ∃ e, att e u = true ∧ att e v = true)

variable {G : SimpleGraph V}

/-- `H²[V] = G`. -/
lemma attach_sq_inl_iff (hG : IsSquareTrace G core att) {u v : V} :
    ((attach core att m).power 2).Adj (.inl u) (.inl v) ↔ G.Adj u v := by
  rw [attach_sq_inl_inl, hG]

/-- The `V`-part of a vertex cover of the square is a vertex cover of `G`. -/
lemma isVertexCover_toLeft (hG : IsSquareTrace G core att) [DecidableEq V] [DecidableEq E]
    {C : Finset (V ⊕ E × Fin m)} (hC : ((attach core att m).power 2).IsVertexCover ↑C) :
    G.IsVertexCover ↑C.toLeft := by
  intro u v huv
  have := hC ((attach_sq_inl_iff (m := m) hG).2 huv)
  simpa using this

/-- A vertex cover of `G` together with all gadget vertices (`inr`) whose position is in `P` is a
vertex cover of the square, provided every square edge between gadget vertices outside `P` is
covered by `P`. Used with `P = univ` (Lemma 21) and `P = {0, 1}` (Lemma 24). -/
lemma isVertexCover_disjSum (hG : IsSquareTrace G core att) {C : Finset V}
    (hC : G.IsVertexCover ↑C) (D : Finset (E × Fin m))
    (hD : ∀ e p b, (e, p) ∉ D →
      ((attach core att m).power 2).Adj (.inr (e, p)) b → b ∈ C.disjSum D) :
    ((attach core att m).power 2).IsVertexCover ↑(C.disjSum D) := by
  intro a b hab
  rcases a with u | ⟨e, p⟩
  · rcases b with v | ⟨e', q⟩
    · have := hC ((attach_sq_inl_iff hG).1 hab)
      simpa using this
    · by_cases hq : (e', q) ∈ D
      · right; simpa using hq
      · left; exact hD e' q _ hq hab.symm
  · by_cases hp : (e, p) ∈ D
    · left; simpa using hp
    · right; exact hD e p _ hp hab

section Weighted

/-- Vertex weights of the weighted construction: `1` on the vertices of `V`, `0` on gadget
vertices. -/
def wt : V ⊕ E × Fin m → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

omit [NeZero m] in
lemma sum_wt (C : Finset (V ⊕ E × Fin m)) : ∑ v ∈ C, (wt v : ℕ) = C.toLeft.card := by
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := C)]
  rw [Finset.sum_disjSum]
  simp [wt]

variable [Fintype E] [DecidableEq V] [DecidableEq E]

/-- **Lemma 21 (abstract form).** The square of `attach core att m` has a vertex cover of weight
at most `W` (weights `wt`) iff `G` has a vertex cover with at most `W` vertices. -/
theorem weighted_iff (hG : IsSquareTrace G core att) (W : ℕ) :
    (∃ C : Finset (V ⊕ E × Fin m), ((attach core att m).power 2).IsVertexCover ↑C ∧
        ∑ v ∈ C, wt v ≤ W) ↔
      ∃ C : Finset V, G.IsVertexCover ↑C ∧ C.card ≤ W := by
  constructor
  · rintro ⟨C, hC, hW⟩
    exact ⟨C.toLeft, isVertexCover_toLeft hG hC, by rwa [sum_wt] at hW⟩
  · rintro ⟨C, hC, hW⟩
    refine ⟨C.disjSum univ, isVertexCover_disjSum hG hC univ ?_, ?_⟩
    · intro e p b h
      simp at h
    · rw [sum_wt, Finset.toLeft_disjSum]; exact hW

end Weighted

section Unweighted

/-! ### Dangling paths of length three (`m = 3`) -/

variable {core : SimpleGraph V} {att : E → V → Bool}

/-- The leaf `(e,2)` of a dangling path is adjacent in the square only to `(e,0)` and `(e,1)`. -/
lemma sq_leaf_adj {e : E} {b : V ⊕ E × Fin 3}
    (h : ((attach core att 3).power 2).Adj (.inr (e, 2)) b) :
    b = .inr (e, 0) ∨ b = .inr (e, 1) := by
  rw [power_two_adj] at h
  obtain ⟨hne, h | ⟨w, h1, h2⟩⟩ := h
  · rcases b with v | ⟨e', q⟩
    · exact absurd h.1 (by decide)
    · obtain ⟨rfl, h⟩ := h
      right; congr; ext; simp at h; omega
  · rcases w with w | ⟨e', q⟩
    · exact absurd h1.1 (by decide)
    · obtain ⟨rfl, hq⟩ := h1
      have hq1 : q = 1 := by ext; simp at hq; omega
      subst hq1
      rcases b with v | ⟨e'', r⟩
      · obtain ⟨h, -⟩ := h2; exact absurd h (by decide)
      · obtain ⟨rfl, hr⟩ := h2
        simp at hr
        have : r.val = 0 ∨ r.val = 2 := by omega
        rcases this with hr | hr
        · left; congr; ext; exact hr
        · exact absurd (by congr; ext; exact hr.symm) hne

/-- `(e,0), (e,1), (e,2)` form a triangle in the square. -/
lemma sq_triangle (e : E) :
    ((attach core att 3).power 2).Adj (.inr (e, 0)) (.inr (e, 1)) ∧
    ((attach core att 3).power 2).Adj (.inr (e, 1)) (.inr (e, 2)) ∧
    ((attach core att 3).power 2).Adj (.inr (e, 0)) (.inr (e, 2)) := by
  refine ⟨Adj.power_two ⟨rfl, by simp⟩, Adj.power_two ⟨rfl, by simp⟩,
    power_two_adj_of_adj_adj (w := .inr (e, 1)) ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ (by simp)⟩

variable [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] in
/-- Every vertex cover of the square contains at least two vertices of every gadget, hence at
least `2 |E|` gadget vertices. -/
lemma two_mul_card_le_toRight {C : Finset (V ⊕ E × Fin 3)}
    (hC : ((attach core att 3).power 2).IsVertexCover ↑C) :
    2 * Fintype.card E ≤ C.toRight.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (by simp)]
  rw [← Finset.card_univ, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun e _ => ?_
  obtain ⟨t01, t12, t02⟩ := sq_triangle (core := core) (att := att) e
  have h01 := hC t01
  have h12 := hC t12
  have h02 := hC t02
  simp only [Finset.mem_coe] at h01 h12 h02
  have key : ∀ p q : Fin 3, p ≠ q → Sum.inr (e, p) ∈ C → Sum.inr (e, q) ∈ C →
      2 ≤ (C.toRight.filter fun x => x.1 = e).card := by
    intro p q hpq hp hq
    calc 2 = ({(e, p), (e, q)} : Finset (E × Fin 3)).card := by
          rw [Finset.card_pair]; simpa using hpq
      _ ≤ _ := Finset.card_le_card (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> simpa)
  rcases h01 with h0 | h1 <;> rcases h12 with h1' | h2 <;> rcases h02 with h0' | h2'
  all_goals first
    | exact key 0 1 (by decide) ‹_› ‹_›
    | exact key 0 2 (by decide) ‹_› ‹_›
    | exact key 1 2 (by decide) ‹_› ‹_›

/-- The gadget vertices with positions `0` and `1`. -/
def firstTwo (E : Type*) [Fintype E] : Finset (E × Fin 3) := univ ×ˢ {0, 1}

omit [DecidableEq E] in
lemma card_firstTwo : (firstTwo E).card = 2 * Fintype.card E := by
  simp [firstTwo, Finset.card_product, mul_comm]

omit [DecidableEq V] [DecidableEq E] in
/-- A vertex cover of `G` plus the first two vertices of every gadget is a vertex cover of the
square. -/
lemma isVertexCover_firstTwo (hG : IsSquareTrace G core att) {C : Finset V}
    (hC : G.IsVertexCover ↑C) :
    ((attach core att 3).power 2).IsVertexCover ↑(C.disjSum (firstTwo E)) := by
  refine isVertexCover_disjSum hG hC _ fun e p b hp hb => ?_
  have hp : p = 2 := by
    simp only [firstTwo, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hp
    revert hp; fin_cases p <;> simp
  subst hp
  rcases sq_leaf_adj hb with rfl | rfl <;> simp [firstTwo]

/-- **Lemma 23 (abstract form).** Every vertex cover `C` of the square can be replaced by a
vertex cover `C'` with `|C'| ≤ |C|`, the same `V`-part, containing `(e,0)` and `(e,1)` and not the
leaf `(e,2)` for every gadget `e`. -/
theorem normalize (hG : IsSquareTrace G core att) {C : Finset (V ⊕ E × Fin 3)}
    (hC : ((attach core att 3).power 2).IsVertexCover ↑C) :
    ∃ C' : Finset (V ⊕ E × Fin 3), ((attach core att 3).power 2).IsVertexCover ↑C' ∧
      C'.card ≤ C.card ∧ C'.toLeft = C.toLeft ∧
      ∀ e, Sum.inr (e, 0) ∈ C' ∧ Sum.inr (e, 1) ∈ C' ∧ Sum.inr (e, 2) ∉ C' := by
  refine ⟨C.toLeft.disjSum (firstTwo E), isVertexCover_firstTwo hG (isVertexCover_toLeft hG hC),
    ?_, by simp, fun e => ?_⟩
  · rw [Finset.card_disjSum, card_firstTwo, ← Finset.card_toLeft_add_card_toRight (u := C)]
    exact Nat.add_le_add_left (two_mul_card_le_toRight hC) _
  · simp [firstTwo]

/-- **Lemma 24 (abstract form, threshold version).** The square has a vertex cover with at most
`W + 2 |E|` vertices iff `G` has a vertex cover with at most `W` vertices. -/
theorem unweighted_iff (hG : IsSquareTrace G core att) (W : ℕ) :
    (∃ C : Finset (V ⊕ E × Fin 3), ((attach core att 3).power 2).IsVertexCover ↑C ∧
        C.card ≤ W + 2 * Fintype.card E) ↔
      ∃ C : Finset V, G.IsVertexCover ↑C ∧ C.card ≤ W := by
  constructor
  · rintro ⟨C, hC, hW⟩
    refine ⟨C.toLeft, isVertexCover_toLeft hG hC, ?_⟩
    have h1 := two_mul_card_le_toRight hC
    have h2 := Finset.card_toLeft_add_card_toRight (u := C)
    omega
  · rintro ⟨C, hC, hW⟩
    refine ⟨C.disjSum (firstTwo E), isVertexCover_firstTwo hG hC, ?_⟩
    rw [Finset.card_disjSum, card_firstTwo]
    omega

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- On a finite vertex type, `τ(G) ≤ n` iff `G` has a vertex cover (a finset) of size `≤ n`. -/
lemma vertexCoverNum_le_iff_finset [Fintype V] {G : SimpleGraph V} (n : ℕ) :
    G.vertexCoverNum ≤ n ↔ ∃ C : Finset V, G.IsVertexCover ↑C ∧ C.card ≤ n := by
  constructor
  · intro h
    obtain ⟨s, hs, hvc⟩ := vertexCoverNum_exists G
    refine ⟨s.toFinite.toFinset, by simpa using hvc, ?_⟩
    have : (s.toFinite.toFinset.card : ℕ∞) ≤ n := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, hs]; exact h
    exact_mod_cast this
  · rintro ⟨C, hC, hn⟩
    refine hC.vertexCoverNum_le.trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hn

/-- **Lemma 24 (abstract form).** `τ(H²) = τ(G) + 2 |E|` for `H = attach core att 3`. -/
theorem vertexCoverNum_sq [Fintype V] (hG : IsSquareTrace G core att) :
    ((attach core att 3).power 2).vertexCoverNum = G.vertexCoverNum + 2 * Fintype.card E := by
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1
    (vertexCoverNum_ne_top_of_finite (G := (attach core att 3).power 2))
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (vertexCoverNum_ne_top_of_finite (G := G))
  rw [← ha, ← hb]
  apply le_antisymm
  · obtain ⟨C, hC, hcard⟩ := (vertexCoverNum_le_iff_finset b).1 hb.symm.le
    have := (vertexCoverNum_le_iff_finset (b + 2 * Fintype.card E)).2
      ((unweighted_iff hG b).2 ⟨C, hC, hcard⟩)
    rw [← ha] at this
    exact_mod_cast this
  · obtain ⟨C, hC, hcard⟩ := (vertexCoverNum_le_iff_finset a).1 ha.symm.le
    have h1 := two_mul_card_le_toRight hC
    have h2 := Finset.card_toLeft_add_card_toRight (u := C)
    have := (vertexCoverNum_le_iff_finset (a - 2 * Fintype.card E)).2
      ⟨C.toLeft, isVertexCover_toLeft hG hC, by omega⟩
    rw [← hb] at this
    have : b ≤ a - 2 * Fintype.card E := by exact_mod_cast this
    have : b + 2 * Fintype.card E ≤ a := by omega
    exact_mod_cast this

end Unweighted

end Podc.PowerGraphApproximation.LowerBound
