import Mathlib

/-!
# Cuts of a vertex set and the parity identity behind `TestOut` (Section 2.1)

For a simple graph `G` and a vertex set `T` (the tree `T_x` maintained by the network), an edge
*leaves* `T` if exactly one of its endpoints is in `T`.

* `crosses T e` — the edge `e` has exactly one endpoint in `T`.
* `cut G T` — the edges leaving `T` (the paper's `Cut(T, V \ T)`); `inside G T` — the edges with
  both endpoints in `T`.
* `sum_incidence_eq` — `∑_{v ∈ T} ∑_{e ∋ v} f e = ∑_{e ∈ cut} f e + 2 • ∑_{e ∈ inside} f e`
  in any commutative monoid.
* `sum_incidence_eq_sum_cut` — **the identity behind `TestOut`**: in characteristic 2 (parities,
  XOR of bit vectors) the edges inside `T` cancel, so aggregating the local sums over the tree
  gives the sum over the cut.
* `Eup`, `Edown`, `exists_cut_iff_Eup_ne_Edown` — **Observation 1**: `E↑(T) ≠ E↓(T)` iff some edge
  leaves `T` (darts, i.e. ordered pairs). All notions are relative to an edge predicate `P`
  (`weight e ∈ [j, k]` for `TestOut(x, j, k)` / `HP-TestOut(x, j, k)`).
-/

namespace Podc.MSTImpromptuRepair

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `crosses T e`: the edge `e` has exactly one endpoint in `T`. -/
def crosses (T : Finset V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun a b => (a ∈ T ↔ b ∉ T), fun a b => propext (by tauto)⟩

@[simp] theorem crosses_mk (T : Finset V) (a b : V) :
    crosses T s(a, b) ↔ (a ∈ T ↔ b ∉ T) := Iff.rfl

instance (T : Finset V) : DecidablePred (crosses T) := fun e =>
  Sym2.recOnSubsingleton e fun a b => decidable_of_iff _ (crosses_mk T a b).symm

/-- `bothIn T e`: both endpoints of `e` lie in `T`. -/
def bothIn (T : Finset V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun a b => a ∈ T ∧ b ∈ T, fun a b => propext (by tauto)⟩

@[simp] theorem bothIn_mk (T : Finset V) (a b : V) :
    bothIn T s(a, b) ↔ (a ∈ T ∧ b ∈ T) := Iff.rfl

instance (T : Finset V) : DecidablePred (bothIn T) := fun e =>
  Sym2.recOnSubsingleton e fun a b => decidable_of_iff _ (bothIn_mk T a b).symm

-- CSLib candidate: `Cslib/Foundations/Combinatorics/SimpleGraph/` (cut, `sum_incidence_eq`, Observation 1)
/-- The cut `Cut(T, V \ T)`: edges of `G` with exactly one endpoint in `T`. -/
def cut (T : Finset V) : Finset (Sym2 V) := G.edgeFinset.filter (crosses T)

/-- Edges of `G` with both endpoints in `T`. -/
def inside (T : Finset V) : Finset (Sym2 V) := G.edgeFinset.filter (bothIn T)

theorem mem_cut {T : Finset V} {e : Sym2 V} : e ∈ cut G T ↔ e ∈ G.edgeSet ∧ crosses T e := by
  simp [cut]

/-- Number of endpoints of an edge `s(a, b)` (`a ≠ b`) lying in `T`. -/
private theorem card_filter_mem_mk (T : Finset V) {a b : V} (hab : a ≠ b) :
    #(T.filter (· ∈ s(a, b))) =
      (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) := by
  have : T.filter (· ∈ s(a, b)) = (T.filter (· = a)) ∪ (T.filter (· = b)) := by
    ext v; simp [Sym2.mem_iff, or_and_right, and_or_left]
  rw [this, card_union_of_disjoint]
  · congr 1 <;> split_ifs with h <;> simp_all [filter_eq']
  · rw [disjoint_filter]; intro v _ h1 h2; exact hab (h1 ▸ h2)

/-- Each edge is counted once per endpoint in `T`: `∑_{v ∈ T} ∑_{e ∋ v} f e` equals
`∑_{e ∈ cut} f e + 2 • ∑_{e ∈ inside} f e`. -/
theorem sum_incidence_eq {M : Type*} [AddCommMonoid M] (T : Finset V) (f : Sym2 V → M) :
    ∑ v ∈ T, ∑ e ∈ G.incidenceFinset v, f e =
      ∑ e ∈ cut G T, f e + 2 • ∑ e ∈ inside G T, f e := by
  classical
  have h1 : ∑ v ∈ T, ∑ e ∈ G.incidenceFinset v, f e =
      ∑ e ∈ G.edgeFinset, #(T.filter (· ∈ e)) • f e := by
    have : ∀ v, G.incidenceFinset v = G.edgeFinset.filter (v ∈ ·) := by
      intro v; ext e
      simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet]
    simp_rw [this, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun e _ => ?_
    rw [card_eq_sum_ones, sum_smul, sum_filter]
    simp
  rw [h1, cut, inside, sum_filter, sum_filter, smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := G.ne_of_adj (by simpa using he)
    rw [card_filter_mem_mk T hab]
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> simp [ha, hb, two_smul]

/-- **The identity behind `TestOut`** (Section 2.1, displayed formula): in characteristic 2,
`∑_{v ∈ V(T)} ∑_{e ∈ E(v)} h(e) = ∑_{e ∈ Cut(T, V \ T)} h(e)`. -/
theorem sum_incidence_eq_sum_cut {M : Type*} [AddCommMonoid M] (h2 : ∀ x : M, x + x = 0)
    (T : Finset V) (f : Sym2 V → M) :
    ∑ v ∈ T, ∑ e ∈ G.incidenceFinset v, f e = ∑ e ∈ cut G T, f e := by
  rw [sum_incidence_eq, two_smul, h2, add_zero]

/-- The interval version used by `TestOut(x, j, k)`: only edges satisfying `P`
(`weight e ∈ [j, k]`) contribute. -/
theorem sum_incidence_filter_eq_sum_cut {M : Type*} [AddCommMonoid M] (h2 : ∀ x : M, x + x = 0)
    (T : Finset V) (P : Sym2 V → Prop) [DecidablePred P] (f : Sym2 V → M) :
    ∑ v ∈ T, ∑ e ∈ (G.incidenceFinset v).filter P, f e = ∑ e ∈ (cut G T).filter P, f e := by
  simp_rw [sum_filter]
  exact sum_incidence_eq_sum_cut G h2 T _

/-! ### Observation 1: darts out of `T` and darts into `T` -/

/-- `E↑(u)`, restricted to edges satisfying `P`: the darts `(u, v)` of `G`. -/
def EupV (P : Sym2 V → Prop) [DecidablePred P] (u : V) : Finset (V × V) :=
  univ.filter fun d => G.Adj d.1 d.2 ∧ P s(d.1, d.2) ∧ d.1 = u

/-- `E↓(u)`, restricted to edges satisfying `P`: the darts `(v, u)` of `G`. -/
def EdownV (P : Sym2 V → Prop) [DecidablePred P] (u : V) : Finset (V × V) :=
  univ.filter fun d => G.Adj d.1 d.2 ∧ P s(d.1, d.2) ∧ d.2 = u

/-- `E↑(T) = ⋃_{u ∈ T} E↑(u)`: darts of `G` (satisfying `P`) leaving a vertex of `T`. -/
def Eup (P : Sym2 V → Prop) [DecidablePred P] (T : Finset V) : Finset (V × V) :=
  univ.filter fun d => G.Adj d.1 d.2 ∧ P s(d.1, d.2) ∧ d.1 ∈ T

/-- `E↓(T) = ⋃_{u ∈ T} E↓(u)`: darts of `G` (satisfying `P`) entering a vertex of `T`. -/
def Edown (P : Sym2 V → Prop) [DecidablePred P] (T : Finset V) : Finset (V × V) :=
  univ.filter fun d => G.Adj d.1 d.2 ∧ P s(d.1, d.2) ∧ d.2 ∈ T

variable (P : Sym2 V → Prop) [DecidablePred P]

theorem Eup_eq_biUnion (T : Finset V) : Eup G P T = T.biUnion (EupV G P) := by
  ext d; simp [Eup, EupV]; tauto

theorem Edown_eq_biUnion (T : Finset V) : Edown G P T = T.biUnion (EdownV G P) := by
  ext d; simp [Edown, EdownV]; tauto

theorem pairwiseDisjoint_EupV (T : Finset V) : (T : Set V).PairwiseDisjoint (EupV G P) := by
  intro u _ v _ huv
  simp only [Function.onFun, disjoint_left, EupV, mem_filter, mem_univ, true_and]
  rintro d ⟨-, -, rfl⟩ ⟨-, -, h⟩; exact huv h

theorem pairwiseDisjoint_EdownV (T : Finset V) : (T : Set V).PairwiseDisjoint (EdownV G P) := by
  intro u _ v _ huv
  simp only [Function.onFun, disjoint_left, EdownV, mem_filter, mem_univ, true_and]
  rintro d ⟨-, -, rfl⟩ ⟨-, -, h⟩; exact huv h

/-- Reversing darts maps `E↑(T)` onto `E↓(T)`; in particular both have the same size (the sum of
the (`P`-restricted) degrees of the vertices of `T`). -/
theorem card_Edown_eq_card_Eup (T : Finset V) : #(Edown G P T) = #(Eup G P T) := by
  refine card_bij (fun d _ => d.swap) ?_ ?_ ?_
  · intro d hd
    simp only [Edown, Eup, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hd ⊢
    exact ⟨hd.1.symm, by rw [Sym2.eq_swap]; exact hd.2.1, hd.2.2⟩
  · intro a _ b _ h; simpa using h
  · intro d hd
    refine ⟨d.swap, ?_, by simp⟩
    simp only [Edown, Eup, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hd ⊢
    exact ⟨hd.1.symm, by rw [Sym2.eq_swap]; exact hd.2.1, hd.2.2⟩

/-- **Observation 1.** There is an edge (satisfying `P`) with exactly one endpoint in `T` iff
`E↑(T) ≠ E↓(T)`. -/
theorem exists_cut_iff_Eup_ne_Edown (T : Finset V) :
    (∃ e ∈ cut G T, P e) ↔ Eup G P T ≠ Edown G P T := by
  constructor
  · rintro ⟨e, he, hP⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [mem_cut] at he
      obtain ⟨hab, hc⟩ := he
      simp only [SimpleGraph.mem_edgeSet, crosses_mk] at hab hc
      intro heq
      by_cases ha : a ∈ T
      · have hb : b ∉ T := hc.1 ha
        have : (a, b) ∈ Eup G P T := by simp [Eup, hab, hP, ha]
        rw [heq] at this; simp [Edown] at this; exact hb this.2.2
      · have hb : b ∈ T := by by_contra hb; exact ha (hc.2 hb)
        have : (b, a) ∈ Eup G P T := by
          simp [Eup, hab.symm, hb]; rwa [Sym2.eq_swap]
        rw [heq] at this; simp [Edown] at this; exact ha this.2.2
  · intro hne
    by_contra hno
    push_neg at hno
    apply hne
    ext d
    simp only [Eup, Edown, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hadj, hP, h1⟩
      refine ⟨hadj, hP, ?_⟩
      by_contra h2
      exact hno s(d.1, d.2) ((mem_cut G).2 ⟨hadj, by simp [h1, h2]⟩) hP
    · rintro ⟨hadj, hP, h2⟩
      refine ⟨hadj, hP, ?_⟩
      by_contra h1
      exact hno s(d.1, d.2) ((mem_cut G).2 ⟨hadj, by simp [h1, h2]⟩) hP

end Podc.MSTImpromptuRepair
