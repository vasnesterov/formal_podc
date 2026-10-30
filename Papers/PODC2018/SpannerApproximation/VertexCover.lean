import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner

/-!
# Weighted 2-spanner versus minimum vertex cover (Claim 3.1 of [CD18])

[CD18] K. Censor-Hillel, M. Dory, *Distributed Spanner Approximation*, PODC 2018.

Given a graph `G` on `V` (vertex names are the IDs, compared by a linear order), the graph
`GS G` lives on `V × Fin 3`; the copies `0, 1, 2` of `v` are the paper's `v₁, v₂, v₃`.

* the triangle `{v₁, v₂}` (weight 1), `{v₁, v₃}`, `{v₂, v₃}` (weight 0) for every `v`;
* for every edge `{v, u}` of `G`: `{v₁, u₁}`, `{v₂, u₂}` (weight 0) and the *cross edge*
  `{v₁, u₂}` for `v < u` (weight 2) — the paper chooses one of `{v₁,u₂}`, `{u₁,v₂}` "according to
  the order of the IDs"; we fix this convention.

A 2-spanner of `GS G` is a subgraph `H ≤ GS G` such that every edge of `GS G` is joined in `H` by a
walk of length at most 2 (`IsTwoSpanner`, equivalent to CSLib's `SimpleGraph.IsSpanner _ H 2`);
its cost is the sum of the weights of its edges (`wcost`).

Main results:
* `isTwoSpanner_HC`, `cost_HC`: for every vertex cover `C`, `HC G C` is a 2-spanner of cost `|C|`;
* `isVertexCover_CH`, `ncard_CH_le_cost`: for every 2-spanner `H`, the explicit set
  `CH H = {v | {v₁,v₂} ∈ H or a cross edge at v₁ or at v₂ is in H}` is a vertex cover with
  `|CH H| ≤ cost H`;
* `claim_3_1`: the minimum 2-spanner cost equals the vertex cover number;
* `approx_transfer`: an `α`-approximate 2-spanner `H` yields the `α`-approximate vertex cover
  `CH H`.
-/

namespace Podc.SpannerApproximation

open Finset

section General

variable {W : Type*}

/-- `H` is a 2-spanner of `Gs`: a subgraph in which every edge of `Gs` is covered by a path of
length at most 2 (Section 1.5 of [CD18], `k = 2`). -/
def IsTwoSpanner (Gs H : SimpleGraph W) : Prop :=
  H ≤ Gs ∧ ∀ ⦃a b : W⦄, Gs.Adj a b → H.Adj a b ∨ ∃ c, H.Adj a c ∧ H.Adj c b

/-- The edge-covering definition of a 2-spanner agrees with CSLib's distance-stretch definition
`SimpleGraph.IsSpanner Gs H 2`. -/
theorem isTwoSpanner_iff_isSpanner {Gs H : SimpleGraph W} :
    IsTwoSpanner Gs H ↔ Gs.IsSpanner H 2 := by
  constructor
  · rintro ⟨hle, hcov⟩
    refine ⟨hle, SimpleGraph.edist_le_mul_of_adj (by norm_num) fun x y hxy => ?_⟩
    rw [SimpleGraph.edist_le_coe_iff]
    rcases hcov hxy with h | ⟨c, h1, h2⟩
    · exact ⟨h.toWalk, by simp⟩
    · exact ⟨.cons h1 (.cons h2 .nil), by simp⟩
  · rintro ⟨hle, hd⟩
    refine ⟨hle, fun a b hab => ?_⟩
    have h := hd a b
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hab, mul_one] at h
    obtain ⟨p, hp⟩ := SimpleGraph.edist_le_coe_iff.mp (by exact_mod_cast h)
    cases p with
    | nil => exact absurd hab Gs.irrefl
    | cons h1 q =>
      cases q with
      | nil => exact Or.inl h1
      | cons h2 r =>
        cases r with
        | nil => exact Or.inr ⟨_, h1, h2⟩
        | cons _ _ => simp at hp

variable [Fintype W]

/-- Cost `w(H) = ∑_{e ∈ H} w(e)` of a subgraph `H` for edge weights `w`. -/
noncomputable def wcost (w : Sym2 W → ℕ) (H : SimpleGraph W) : ℕ := by
  classical exact ∑ e ∈ H.edgeFinset, w e

lemma wcost_eq (w : Sym2 W → ℕ) (H : SimpleGraph W) [Fintype H.edgeSet] :
    wcost w H = ∑ e ∈ H.edgeFinset, w e := by
  unfold wcost
  congr 1
  ext e
  simp

end General

variable {V : Type*} [LinearOrder V]

/-- Adjacency of `G_S` in terms of the adjacency `r` of `G` (copies `0, 1, 2` = `v₁, v₂, v₃`). -/
def SAdj (r : V → V → Prop) (a b : V × Fin 3) : Prop :=
  (a.1 = b.1 ∧ a.2 ≠ b.2) ∨
  (r a.1 b.1 ∧ ((a.2 = 0 ∧ b.2 = 0) ∨ (a.2 = 1 ∧ b.2 = 1) ∨
    (a.1 < b.1 ∧ a.2 = 0 ∧ b.2 = 1) ∨ (b.1 < a.1 ∧ a.2 = 1 ∧ b.2 = 0)))

instance (r : V → V → Prop) [DecidableRel r] : DecidableRel (SAdj r) := fun _ _ => by
  unfold SAdj; infer_instance

/-- The graph `G_S` of Section 3 of [CD18] (Figure 3). -/
def GS (G : SimpleGraph V) : SimpleGraph (V × Fin 3) where
  Adj := SAdj G.Adj
  symm := ⟨fun a b h => by
    unfold SAdj at *
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
    · refine Or.inr ⟨h1.symm, ?_⟩
      rcases h2 with h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2.2, h.2.1⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.2, h.2.1⟩))⟩
  loopless := ⟨fun a h => by
    unfold SAdj at h
    rcases h with ⟨_, h⟩ | ⟨h, _⟩
    · exact h rfl
    · exact G.irrefl h⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (GS G).Adj :=
  inferInstanceAs (DecidableRel (SAdj G.Adj))

lemma GS_adj {G : SimpleGraph V} {a b : V × Fin 3} : (GS G).Adj a b ↔ SAdj G.Adj a b := Iff.rfl

@[simp] lemma GS_adj_same {G : SimpleGraph V} {v : V} {i j : Fin 3} :
    (GS G).Adj (v, i) (v, j) ↔ i ≠ j := by
  simp [GS_adj, SAdj]

lemma GS_adj_of_ne {G : SimpleGraph V} {v u : V} (h : v ≠ u) {i j : Fin 3} :
    (GS G).Adj (v, i) (u, j) ↔ G.Adj v u ∧ ((i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 1) ∨
      (v < u ∧ i = 0 ∧ j = 1) ∨ (u < v ∧ i = 1 ∧ j = 0)) := by
  simp [GS_adj, SAdj, h]

lemma GS_adj_fst {G : SimpleGraph V} {a b : V × Fin 3} (h : (GS G).Adj a b) :
    a.1 = b.1 ∨ G.Adj a.1 b.1 := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Weights of `G_S` on ordered pairs: `1` on `{v₁,v₂}`, `0` on `{v₁,v₃}, {v₂,v₃}, {v₁,u₁},
{v₂,u₂}`, `2` on the cross edges `{v₁,u₂}`. (Only the values on edges of `G_S` matter.) -/
def wtPair (a b : V × Fin 3) : ℕ :=
  if a.1 = b.1 then (if a.2 = 2 ∨ b.2 = 2 then 0 else 1) else if a.2 = b.2 then 0 else 2

lemma wtPair_comm (a b : V × Fin 3) : wtPair a b = wtPair b a := by
  unfold wtPair
  by_cases h : a.1 = b.1
  · simp [h, or_comm]
  · simp [h, Ne.symm h, eq_comm]

/-- The edge weights of `G_S`. -/
def wt : Sym2 (V × Fin 3) → ℕ := Sym2.lift ⟨wtPair, wtPair_comm⟩

@[simp] lemma wt_mk (a b : V × Fin 3) : wt s(a, b) = wtPair a b := rfl

variable [Fintype V]

/-- The cost of a subgraph of `G_S`. -/
noncomputable abbrev cost (H : SimpleGraph (V × Fin 3)) : ℕ := wcost wt H

/-! ### From vertex covers to 2-spanners -/

/-- The spanner `H_C` of the proof of Claim 3.1: all weight-0 edges of `G_S` and the triangle
edges `{v₁, v₂}` for `v ∈ C`. (We add the whole triangle of `v ∈ C`; its other edges have weight
0 anyway.) -/
def HC (G : SimpleGraph V) (C : Set V) : SimpleGraph (V × Fin 3) where
  Adj a b := (GS G).Adj a b ∧ (wtPair a b = 0 ∨ (a.1 = b.1 ∧ a.1 ∈ C))
  symm := ⟨fun a b h => ⟨h.1.symm, by
    rcases h.2 with h2 | ⟨h2, h3⟩
    · exact Or.inl (by rw [wtPair_comm]; exact h2)
    · exact Or.inr ⟨h2.symm, h2 ▸ h3⟩⟩⟩
  loopless := ⟨fun _ h => (GS G).irrefl h.1⟩

omit [Fintype V] in
lemma HC_le (G : SimpleGraph V) (C : Set V) : HC G C ≤ GS G := fun _ _ h => h.1

omit [Fintype V] in
/-- First half of the proof of Claim 3.1: `H_C` is a 2-spanner if `C` is a vertex cover. -/
theorem isTwoSpanner_HC {G : SimpleGraph V} {C : Set V} (hC : G.IsVertexCover C) :
    IsTwoSpanner (GS G) (HC G C) := by
  refine ⟨HC_le G C, ?_⟩
  rintro ⟨v, i⟩ ⟨u, j⟩ hab
  by_cases hvu : v = u
  · subst hvu
    -- triangle edge: covered directly, or by the path through the third copy
    have hij : i ≠ j := GS_adj_same.mp hab
    by_cases hw : wtPair (v, i) (v, j) = 0
    · exact Or.inl ⟨hab, Or.inl hw⟩
    · right
      have h2 : i ≠ 2 ∧ j ≠ 2 := by simp only [wtPair, ite_true] at hw; split_ifs at hw <;> tauto
      refine ⟨(v, 2), ⟨GS_adj_same.mpr h2.1, Or.inl ?_⟩, ⟨GS_adj_same.mpr (Ne.symm h2.2),
        Or.inl ?_⟩⟩ <;> simp [wtPair]
  · rw [GS_adj_of_ne hvu] at hab
    obtain ⟨hG, hk⟩ := hab
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩
    · exact Or.inl ⟨(GS_adj_of_ne hvu).mpr ⟨hG, by simp⟩, Or.inl (by simp [wtPair, hvu])⟩
    · exact Or.inl ⟨(GS_adj_of_ne hvu).mpr ⟨hG, by simp⟩, Or.inl (by simp [wtPair, hvu])⟩
    · -- cross edge `{v₁, u₂}`, `v < u`
      right
      rcases hC hG with hv | hu
      · refine ⟨(v, 1), ⟨GS_adj_same.mpr (by decide), Or.inr ⟨rfl, hv⟩⟩, ?_⟩
        exact ⟨(GS_adj_of_ne hvu).mpr ⟨hG, by simp⟩, Or.inl (by simp [wtPair, hvu])⟩
      · refine ⟨(u, 0), ⟨(GS_adj_of_ne hvu).mpr ⟨hG, by simp⟩, Or.inl (by simp [wtPair, hvu])⟩,
          ⟨GS_adj_same.mpr (by decide), Or.inr ⟨rfl, hu⟩⟩⟩
    · -- cross edge `{v₂, u₁}`, `u < v`
      right
      rcases hC hG with hv | hu
      · refine ⟨(v, 0), ⟨GS_adj_same.mpr (by decide), Or.inr ⟨rfl, hv⟩⟩, ?_⟩
        exact ⟨(GS_adj_of_ne hvu).mpr ⟨hG, by simp⟩, Or.inl (by simp [wtPair, hvu])⟩
      · refine ⟨(u, 1), ⟨(GS_adj_of_ne hvu).mpr ⟨hG, by simp⟩, Or.inl (by simp [wtPair, hvu])⟩,
          ⟨GS_adj_same.mpr (by decide), Or.inr ⟨rfl, hu⟩⟩⟩

/-- The edge `{v₁, v₂}`. -/
def diag (v : V) : Sym2 (V × Fin 3) := s((v, 0), (v, 1))

omit [LinearOrder V] [Fintype V] in
lemma diag_injective : Function.Injective (diag (V := V)) := by
  intro v u h
  simp only [diag, Sym2.eq_iff, Prod.mk.injEq] at h
  rcases h with ⟨⟨h, _⟩, _⟩ | ⟨⟨_, h⟩, _⟩
  · exact h
  · exact absurd h (by decide)

open Classical in
lemma wtPair_HC {G : SimpleGraph V} {C : Set V} {a b : V × Fin 3} (h : (HC G C).Adj a b) :
    wtPair a b = if ∃ v ∈ C, diag v = s(a, b) then 1 else 0 := by
  by_cases hw : wtPair a b = 0
  · rw [hw, eq_comm, ite_eq_right_iff]
    rintro ⟨w, _, hd⟩
    simp only [diag, Sym2.eq_iff] at hd
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [wtPair] at hw
  · obtain ⟨hadj, h2⟩ := h
    rcases h2 with h2 | ⟨h2, hC⟩
    · exact absurd h2 hw
    obtain ⟨v, i⟩ := a
    obtain ⟨u, j⟩ := b
    simp only at h2 hC
    subst h2
    have hij : i ≠ j := GS_adj_same.mp hadj
    clear hadj
    simp only [wtPair, ite_true] at hw ⊢
    have h2 : i ≠ 2 ∧ j ≠ 2 := by split_ifs at hw <;> tauto
    have hd : diag v = s((v, i), (v, j)) := by
      simp only [diag, Sym2.eq_iff, Prod.mk.injEq, true_and]
      clear hw; revert h2 hij; revert i j; decide
    have hex : ∃ w ∈ C, diag w = s((v, i), (v, j)) := ⟨v, hC, hd⟩
    simp only [hex, ite_true]
    simp [h2.1, h2.2]

/-- First half of the proof of Claim 3.1: the cost of `H_C` is exactly `|C|`. -/
theorem cost_HC (G : SimpleGraph V) (C : Set V) : cost (HC G C) = C.ncard := by
  classical
  rw [cost, wcost_eq, Set.ncard_eq_toFinset_card', ← card_image_of_injective _ diag_injective]
  have hsub : C.toFinset.image diag ⊆ (HC G C).edgeFinset := by
    intro e he
    simp only [mem_image, Set.mem_toFinset] at he
    obtain ⟨v, hv, rfl⟩ := he
    simp only [diag, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨GS_adj_same.mpr (by decide), Or.inr ⟨rfl, hv⟩⟩
  rw [sum_congr rfl (g := fun e => if e ∈ C.toFinset.image diag then 1 else 0), sum_boole,
    filter_mem_eq_inter, inter_eq_right.mpr hsub, Nat.cast_id]
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rw [wt_mk, wtPair_HC he]
    simp

/-! ### From 2-spanners to vertex covers -/

/-- The vertex cover `C_H` of the proof of Claim 3.1, read off directly from `H`: `v ∈ C_H` iff
`{v₁, v₂} ∈ H` (the case `u = v`) or some cross edge `{v₁, u₂}` or `{u₁, v₂}` is in `H`.
This is the paper's `C_{H'} = {v | {v₁,v₂} ∈ H'}`, where `H'` replaces each cross edge
`{v₁, u₂} ∈ H` by `{v₁, v₂}, {u₁, u₂}`. -/
def CH (H : SimpleGraph (V × Fin 3)) : Set V :=
  {v | ∃ u, H.Adj (v, 0) (u, 1) ∨ H.Adj (u, 0) (v, 1)}

/-- `v` is the name of an endpoint of the edge `e`, which joins a first copy to a second copy. -/
def Touches (v : V) (e : Sym2 (V × Fin 3)) : Prop :=
  ∃ u, e = s((v, 0), (u, 1)) ∨ e = s((u, 0), (v, 1))

omit [LinearOrder V] [Fintype V] in
lemma touches_mk {v : V} {a b : V × Fin 3} : Touches v s(a, b) ↔
    ((a.2 = 0 ∧ b.2 = 1) ∨ (a.2 = 1 ∧ b.2 = 0)) ∧ (v = a.1 ∨ v = b.1) := by
  obtain ⟨x, i⟩ := a
  obtain ⟨y, j⟩ := b
  simp only [Touches, Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨u, h⟩
    rcases h with (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) | (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩)
    all_goals subst_vars; simp
  · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), (rfl | rfl)⟩
    · exact ⟨y, Or.inl (Or.inl ⟨⟨rfl, rfl⟩, rfl, rfl⟩)⟩
    · exact ⟨x, Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl, rfl⟩)⟩
    · exact ⟨y, Or.inr (Or.inr ⟨⟨rfl, rfl⟩, rfl, rfl⟩)⟩
    · exact ⟨x, Or.inl (Or.inr ⟨⟨rfl, rfl⟩, rfl, rfl⟩)⟩

open Classical in
/-- An edge `e` touches at most `wt e` names: the triangle edge `{v₁, v₂}` (weight 1) one name,
a cross edge (weight 2) two names, every other edge none. -/
lemma card_touches_le (a b : V × Fin 3) :
    (univ.filter (fun v => Touches v s(a, b))).card ≤ wtPair a b := by
  classical
  by_cases h01 : (a.2 = 0 ∧ b.2 = 1) ∨ (a.2 = 1 ∧ b.2 = 0)
  · have hsub : univ.filter (fun v => Touches v s(a, b)) ⊆ {a.1, b.1} := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, touches_mk] at hv
      simp [hv.2]
    refine (card_le_card hsub).trans ?_
    have h2 : a.2 ≠ 2 ∧ b.2 ≠ 2 := by rcases h01 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [h, h']
    have hne : a.2 ≠ b.2 := by rcases h01 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [h, h']
    by_cases h : a.1 = b.1
    · simp [h, wtPair, h2.1, h2.2]
    · simp only [wtPair, h, hne, ite_false]
      exact card_le_two
  · have : univ.filter (fun v => Touches v s(a, b)) = ∅ := by
      ext v; simp [touches_mk, h01]
    simp [this]

/-- Second half of the proof of Claim 3.1: `|C_H| ≤ w(H)` (for every subgraph `H`). -/
theorem ncard_CH_le_cost (H : SimpleGraph (V × Fin 3)) : (CH H).ncard ≤ cost H := by
  classical
  rw [cost, wcost_eq, Set.ncard_eq_toFinset_card']
  have hsub : (CH H).toFinset ⊆
      H.edgeFinset.biUnion (fun e => univ.filter (fun v => Touches v e)) := by
    intro v hv
    obtain ⟨u, h | h⟩ := Set.mem_toFinset.mp hv
    · exact mem_biUnion.mpr ⟨s((v, 0), (u, 1)), by simpa using h,
        by simpa using ⟨u, Or.inl rfl⟩⟩
    · exact mem_biUnion.mpr ⟨s((u, 0), (v, 1)), by simpa using h,
        by simpa using ⟨u, Or.inr rfl⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun e _ => ?_))
  induction e using Sym2.ind with
  | _ a b => exact card_touches_le a b

omit [Fintype V] in
lemma GS_adj_two {G : SimpleGraph V} {a : V × Fin 3} {y : V} (h : (GS G).Adj a (y, 2)) :
    a.1 = y := by
  rcases h with h | ⟨_, h⟩
  · exact h.1
  · simp at h

omit [Fintype V] in
/-- Second half of the proof of Claim 3.1: `C_H` is a vertex cover of `G` for every 2-spanner `H`
of `G_S`. -/
theorem isVertexCover_CH {G : SimpleGraph V} {H : SimpleGraph (V × Fin 3)}
    (hH : IsTwoSpanner (GS G) H) : G.IsVertexCover (CH H) := by
  have key : ∀ v u, v < u → G.Adj v u → v ∈ CH H ∨ u ∈ CH H := by
    intro v u hlt hG
    have he : (GS G).Adj (v, 0) (u, 1) :=
      (GS_adj_of_ne hlt.ne).mpr ⟨hG, Or.inr (Or.inr (Or.inl ⟨hlt, rfl, rfl⟩))⟩
    rcases hH.2 he with h | ⟨⟨w, k⟩, h1, h2⟩
    · exact Or.inl ⟨u, Or.inl h⟩
    · fin_cases k
      · -- the middle vertex is `w₁`: the edge `{w₁, u₂}` is in `H`
        exact Or.inr ⟨w, Or.inr h2⟩
      · -- the middle vertex is `w₂`: the edge `{v₁, w₂}` is in `H`
        exact Or.inl ⟨w, Or.inl h1⟩
      · -- the middle vertex is `w₃`: impossible, it would force `v = w = u`
        have e1 := GS_adj_two (hH.1 h1)
        have e2 := GS_adj_two ((hH.1 h2).symm)
        simp only at e1 e2
        exact absurd (e1.trans e2.symm) hlt.ne
  intro v u hG
  rcases lt_or_gt_of_ne (G.ne_of_adj hG) with hlt | hlt
  · exact key v u hlt hG
  · exact (key u v hlt hG.symm).symm

/-! ### Claim 3.1 and approximation transfer -/

/-- The minimum cost of a 2-spanner of `G_S`. -/
noncomputable def minSpannerCost (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (H : SimpleGraph (V × Fin 3)) (_ : IsTwoSpanner (GS G) H), (cost H : ℕ∞)

/-- **Claim 3.1 of [CD18].** The cost of the minimum 2-spanner in `G_S` is exactly the size of the
minimum vertex cover in `G`. -/
theorem claim_3_1 (G : SimpleGraph V) : minSpannerCost G = G.vertexCoverNum := by
  apply le_antisymm
  · refine le_iInf₂ fun C hC => ?_
    refine (iInf₂_le (HC G C) (isTwoSpanner_HC hC)).trans ?_
    rw [cost_HC, Set.Finite.cast_ncard_eq C.toFinite]
  · refine le_iInf₂ fun H hH => ?_
    refine (isVertexCover_CH hH).vertexCoverNum_le.trans ?_
    rw [← Set.Finite.cast_ncard_eq (CH H).toFinite]
    exact_mod_cast ncard_CH_le_cost H

/-- `H` is an `α`-approximate minimum-cost 2-spanner of `Gs` for the weights `w`. -/
def IsApproxMinSpanner {W : Type*} [Fintype W] (w : Sym2 W → ℕ) (α : ℝ)
    (Gs H : SimpleGraph W) : Prop :=
  IsTwoSpanner Gs H ∧ ∀ H', IsTwoSpanner Gs H' → (wcost w H : ℝ) ≤ α * wcost w H'

/-- `C` is an `α`-approximate minimum vertex cover of `G`. -/
def IsApproxMinVC {U : Type*} (α : ℝ) (G : SimpleGraph U) (C : Set U) : Prop :=
  G.IsVertexCover C ∧ ∀ C', G.IsVertexCover C' → (C.ncard : ℝ) ≤ α * C'.ncard

/-- Approximation transfer (used in Lemma 3.2 of [CD18]): if `H` is an `α`-approximate minimum
2-spanner of `G_S`, then `C_H` is an `α`-approximate minimum vertex cover of `G`. -/
theorem approx_transfer {G : SimpleGraph V} {H : SimpleGraph (V × Fin 3)} {α : ℝ}
    (hH : IsApproxMinSpanner wt α (GS G) H) : IsApproxMinVC α G (CH H) := by
  refine ⟨isVertexCover_CH hH.1, fun C hC => ?_⟩
  calc ((CH H).ncard : ℝ) ≤ cost H := by exact_mod_cast ncard_CH_le_cost H
    _ ≤ α * cost (HC G C) := hH.2 _ (isTwoSpanner_HC hC)
    _ = α * C.ncard := by rw [cost_HC]

end Podc.SpannerApproximation
