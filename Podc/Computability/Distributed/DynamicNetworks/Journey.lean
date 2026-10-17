import Cslib.Computability.Distributed.DynamicNetworks.Journey
import Podc.Foundations.Data.Nat.Growth
import Podc.Foundations.Combinatorics.Digraph.Walk

-- CSLib candidate: Cslib/Computability/Distributed/DynamicNetworks/Journey.lean (append to the
-- existing file); `prod_of_inv` to `DynamicNetworks/Product.lean`.

/-!
# Journeys: forward invariants and the growth of the causal past

Additions to `Cslib/Computability/Distributed/DynamicNetworks/Journey.lean`.

* `isRoot_iff`: rooted rounds are rooted digraphs (`Digraph.IsRoot`).
* `Journey.of_inv`, `prod_of_inv`: a property of (time, vertex) pairs preserved by every step of
  a journey (of a product of rounds) holds at its end ("speed of information" arguments).
* `DynNet.past E V u t s`: the causal past of `(u, t)` at time `s` among the vertices `V`, i.e.
  the vertices `v ∈ V` with a journey from `(v, s)` to `(u, t)`. `V` is a `Finset`, so that the
  vertex set may vary (e.g. the vertices of one execution among natural-number identifiers).
* **Flooding.** If every round is connected towards `u` (`hconn`), the past grows by at least one
  vertex per round until it is all of `V`: `past_ssubset`, `min_card_le_card_past`
  (`|past(u, t)(t - j)| ≥ min(|V|, j + 1)`), `past_eq_of_card_le` (after `|V| - 1` rounds, `u` has
  heard from every vertex). The counting step is `Nat.min_add_le`.
-/

namespace Cslib.DynNet

open Relation

/-- `Cslib.DynNet.IsRoot E r` is rootedness in the digraph with arcs `E`. -/
theorem isRoot_iff {α : Type*} {E : α → α → Prop} {r : α} : IsRoot E r ↔ (Digraph.mk E).IsRoot r :=
  Iff.rfl

variable {α : Type*} {E : ℕ → α → α → Prop}

/-! ### Forward invariants -/

/-- **Forward invariant along a journey.** If `P s x` holds and every step of round `τ` (staying
put or following an edge of round `τ`, for `s ≤ τ < t`) preserves `P`, then `P t y` holds at the
end of every journey from `(x, s)` to `(y, t)`. -/
theorem Journey.of_inv {P : ℕ → α → Prop} {s t : ℕ} {x y : α} (h : Journey E s x t y)
    (h0 : P s x) (hstep : ∀ τ a b, s ≤ τ → τ < t → P τ a → (a = b ∨ E τ a b) → P (τ + 1) b) :
    P t y := by
  induction h with
  | refl => exact h0
  | @step w u t hr hwu ih =>
    exact hstep t w u hr.le (by omega) (ih fun τ a b h1 h2 => hstep τ a b h1 (by omega)) hwu

/-- **Forward invariant along a product of rounds.** If `S 0 x` holds and every edge of round
`a + k` maps `S k` into `S (k + 1)`, then every vertex reached from `x` by the product of the `k`
rounds starting at round `a` satisfies `S k`. -/
theorem prod_of_inv (S : ℕ → α → Prop) {a : ℕ} {x : α} (h0 : S 0 x)
    (hstep : ∀ k z y, S k z → E (a + k) z y → S (k + 1) y) :
    ∀ k y, prod E a k x y → S k y := by
  intro k
  induction k with
  | zero => rintro y rfl; exact h0
  | succ k ih =>
    intro y hy
    obtain ⟨z, hz, hzy⟩ := prod_succ_apply.1 hy
    exact hstep k z y (ih z hz) hzy

/-! ### The causal past -/

open Classical in
/-- The causal past of `(u, t)` at time `s` among the vertices `V`: the vertices `v ∈ V` with a
journey from `(v, s)` to `(u, t)` (`past_{(u, t)}(s)` of Kuhn–Moses–Oshman). -/
noncomputable def past (E : ℕ → α → α → Prop) (V : Finset α) (u : α) (t s : ℕ) : Finset α :=
  V.filter fun v => Journey E s v t u

variable {V : Finset α} {u v : α} {t s : ℕ}

/-- Membership in the causal past. -/
theorem mem_past : v ∈ past E V u t s ↔ v ∈ V ∧ Journey E s v t u := by
  classical
  simp [past]

/-- The causal past consists of vertices of `V`. -/
theorem past_subset (u : α) (t s : ℕ) : past E V u t s ⊆ V := fun _ hv => (mem_past.1 hv).1

/-- A vertex of `V` is in its own causal past at any earlier time. -/
theorem self_mem_past (hu : u ∈ V) (h : s ≤ t) : u ∈ past E V u t s :=
  mem_past.2 ⟨hu, Journey.self h⟩

/-- The past at a later time `s'` is contained in the past at time `s ≤ s'`. -/
theorem past_anti {s s' : ℕ} (h : s ≤ s') : past E V u t s' ⊆ past E V u t s := fun _ hv =>
  mem_past.2 ⟨(mem_past.1 hv).1, (mem_past.1 hv).2.mono_left h⟩

/-- The past of `(u, t)` grows with `t`. -/
theorem past_mono {t t' : ℕ} (h : t ≤ t') : past E V u t s ⊆ past E V u t' s := fun _ hv =>
  mem_past.2 ⟨(mem_past.1 hv).1, (mem_past.1 hv).2.trans (Journey.self h)⟩

/-- **The past grows across a round.** If the edges of round `s` start in `V` and some vertex
outside the past at time `s + 1` reaches the past at time `s + 1` along edges of round `s`, then
the past at time `s` is strictly larger. -/
theorem past_ssubset_of_reflTransGen (hE : ∀ x y, E s x y → x ∈ V) {y x : α}
    (hy' : y ∉ past E V u t (s + 1)) (hx : x ∈ past E V u t (s + 1))
    (h : ReflTransGen (E s) y x) : past E V u t (s + 1) ⊂ past E V u t s := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨past_anti s.le_succ, fun heq => ?_⟩
  obtain ⟨z, w, hzw, hz, hw⟩ :=
    exists_edge_cross (S := fun x => x ∈ past E V u t (s + 1)) h hy' hx
  exact hz (heq ▸ mem_past.2 ⟨hE _ _ hzw, Journey.cons (Or.inr hzw) (mem_past.1 hw).2⟩)

/-- **The past grows in a connected round.** If the edges of round `s < t` start in `V`, every
vertex of `V` reaches `u ∈ V` along edges of round `s`, and the past at time `s + 1` is not yet
all of `V`, then the past at time `s` is strictly larger. -/
theorem past_ssubset (hE : ∀ x y, E s x y → x ∈ V) (hconn : ∀ y ∈ V, ReflTransGen (E s) y u)
    (hu : u ∈ V) (hst : s < t) (hne : past E V u t (s + 1) ≠ V) :
    past E V u t (s + 1) ⊂ past E V u t s := by
  obtain ⟨y, hy, hy'⟩ : ∃ y ∈ V, y ∉ past E V u t (s + 1) := by
    by_contra! h
    exact hne (Finset.Subset.antisymm (past_subset u t _) h)
  exact past_ssubset_of_reflTransGen hE hy' (self_mem_past hu hst) (hconn y hy)

/-- **Flooding lemma.** If the edges of every round start in `V` and every vertex of `V` reaches
`u ∈ V` in every round before `t`, then `|past(u, t)(t - j)| ≥ min(|V|, j + 1)` for `j ≤ t`. -/
theorem min_card_le_card_past (hE : ∀ r x y, E r x y → x ∈ V)
    (hconn : ∀ r < t, ∀ y ∈ V, ReflTransGen (E r) y u) (hu : u ∈ V) {j : ℕ} (hj : j ≤ t) :
    min V.card (j + 1) ≤ (past E V u t (t - j)).card := by
  have h0 : 1 ≤ (past E V u t (t - 0)).card := Finset.card_pos.2 ⟨u, self_mem_past hu (by omega)⟩
  have := Nat.min_add_le (f := fun i => (past E V u t (t - i)).card) (n := V.card) (K := j)
    (fun i hi => Finset.card_le_card (past_anti (by omega)))
    (fun i hi hlt => by
      have e : t - i = t - (i + 1) + 1 := by omega
      simp only [e] at hlt ⊢
      refine Finset.card_lt_card (past_ssubset (hE _) (hconn _ (by omega)) hu (by omega) ?_)
      rintro h; rw [h] at hlt; exact lt_irrefl _ hlt)
  omega

/-- **Flooding.** Under the hypotheses of `min_card_le_card_past`, the past of `(u, t)` at any
time `s` with `s + |V| ≤ t + 1` is all of `V`. -/
theorem past_eq_of_card_le (hE : ∀ r x y, E r x y → x ∈ V)
    (hconn : ∀ r < t, ∀ y ∈ V, ReflTransGen (E r) y u) (hu : u ∈ V) (h : s + V.card ≤ t + 1) :
    past E V u t s = V := by
  have hn : 0 < V.card := Finset.card_pos.2 ⟨u, hu⟩
  have := min_card_le_card_past hE hconn hu (j := t - s) (by omega)
  rw [show t - (t - s) = s by omega] at this
  exact Finset.eq_of_subset_of_card_le (past_subset _ _ _) (by omega)

end Cslib.DynNet
