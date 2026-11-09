/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Podc.Foundations.GameTheory.NeverBestResponse

/-!
# BGP games (Section 3.3 of Nisan–Schapira–Valiant–Zohar, *Best-Response Mechanisms*)

The network is an undirected graph `G` on a finite vertex set `V` with a destination `d`; the other
vertices are the *source nodes*. Each source node `i` has a private strict ranking of all simple
routes from `i` to `d` (`Rankings`: a positive number for each route, injective on the simple
routes of `i`; larger is better). In the *BGP game*

* the players are the source nodes (`Player d`),
* the strategies of `i` are its outgoing edges, i.e. its neighbours (`Strategy G d i`),
* given a forwarding profile `f`, the utility of `i` is the rank of the simple route from `i` to
  `d` obtained by following the next hops of `f` (`route f i`), or `0` if there is no such route.

## Main statements

* `theorem_3_6` (**Theorem 3.6**): if `G` is connected and has *No Dispute Wheel*
  (`NoDisputeWheel`, an assumption used but not stated in the paper), then for every tie-breaking
  rule the BGP game is NBR-solvable in at most `n` steps (`n` = number of source nodes) with a
  clear outcome `s`; `s` is a stable routing tree, and it is the unique pure Nash equilibrium.
  All eliminations are *strict* (the eliminated strategy is strictly worse), so tie-breaking plays
  no role.
* `exists_guarantee`: the dispute-wheel argument of the proof sketch. We take as `a₁` the *last*
  non-fixed node on `a₀`'s best existing route `R₀` (not the paper's "closest to `d` that prefers
  another route": when no such node exists, it is this node, not `a₀`, that can guarantee its
  route). The chain `aⱼ₊₁ := last non-fixed node on R(aⱼ)` is eventually periodic, and its cycle
  is a dispute wheel with spokes = suffixes of `R(aⱼ)` and rims = prefixes of `R(aⱼ₊₁)`.
* `badGadget_noNash`, `badGadget_not_NBRSolvable`: without No Dispute Wheel, Theorem 3.6 fails —
  the BAD GADGET has no pure Nash equilibrium, hence is not NBR-solvable under any strict total
  tie-breaking rule; `badGadget_disputeWheel` shows (via Theorem 3.6) that it has a dispute wheel.
-/

open Function Set Cslib.GameTheory

namespace Podc.BestResponseMechanisms.BGP

/-! ### Generic list lemmas -/

section ListLemmas

variable {α : Type*}

-- CSLib candidate
/-- `IsChain` is monotone in the relation, where the implication may use membership of the
first element. -/
lemma isChain_imp_of_mem {R S : α → α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y, R x y → S x y) → l.IsChain R → l.IsChain S
  | [], _, _ => .nil
  | [a], _, _ => .singleton a
  | a :: b :: l, h, .cons_cons hr hc =>
      .cons_cons (h a (by simp) b hr)
        (isChain_imp_of_mem (fun x hx => h x (List.mem_cons_of_mem _ hx)) hc)

-- CSLib candidate
/-- If some element of `l` satisfies `P`, then `l` splits at the *last* such element. -/
lemma exists_split_last {P : α → Prop} :
    ∀ l : List α, (∃ x ∈ l, P x) →
      ∃ pre c post, l = pre ++ c :: post ∧ P c ∧ ∀ x ∈ post, ¬ P x
  | [], h => by simp at h
  | a :: l, h => by
    by_cases hl : ∃ x ∈ l, P x
    · obtain ⟨pre, c, post, rfl, hc, hpost⟩ := exists_split_last l hl
      exact ⟨a :: pre, c, post, rfl, hc, hpost⟩
    · push Not at hl
      have ha : P a := by
        obtain ⟨x, hx, hPx⟩ := h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hPx
        · exact absurd hPx (hl x hx)
      exact ⟨[], a, l, rfl, ha, hl⟩

end ListLemmas

variable {V : Type*} [DecidableEq V]

/-! ### Routes, rankings, and the BGP game -/

section Model

variable (G : SimpleGraph V) (d : V)

/-- `p` is a *simple route* from `u` to `v` in `G`: a loop-free path, given by its vertex list. -/
def IsSimpleRoute (p : List V) (u v : V) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain G.Adj ∧ p.Nodup

/-- The source nodes (all vertices except the destination `d`): the players of the BGP game. -/
abbrev Player := {v : V // v ≠ d}

/-- The strategies of a source node `i`: its outgoing edges, i.e. its neighbours. -/
abbrev Strategy (i : Player d) := {w : V // G.Adj i.1 w}

/-- A forwarding profile: every source node chooses a next hop. -/
abbrev Profile := ∀ i : Player d, Strategy G d i

/-- The private rankings of the source nodes: `rank i p` is `i`'s rank of the simple route `p`
from `i` to `d` (larger is better). The paper uses ranks `1, …, N` (the least desired route has
rank `1`); we only need that ranks of simple routes are positive and distinct. -/
structure Rankings where
  /-- `rank i p`: the rank of the route `p` for the source node `i`. -/
  rank : V → List V → ℕ
  /-- Every simple route has positive rank (rank `0` is reserved for "no route"). -/
  rank_pos : ∀ i, i ≠ d → ∀ p, IsSimpleRoute G p i d → 0 < rank i p
  /-- The ranking is strict: distinct simple routes have distinct ranks. -/
  rank_inj : ∀ i, i ≠ d → ∀ p q, IsSimpleRoute G p i d → IsSimpleRoute G q i d →
    rank i p = rank i q → p = q

variable {G d}

/-- The next hop of a vertex under a forwarding profile (`d` stays at `d`). -/
def nextHop (f : Profile G d) (v : V) : V :=
  if h : v = d then d else (f ⟨v, h⟩).1

/-- Follow next hops from `v` for at most `n` steps; `some p` if `d` is reached (the list `p` of
visited vertices ends at the first visit of `d`). -/
def walkTo (f : Profile G d) : ℕ → V → Option (List V)
  | 0, v => if v = d then some [v] else none
  | n + 1, v => if v = d then some [v] else (walkTo f n (nextHop f v)).map (v :: ·)

/-- `p` is the route from `v` to `d` under `f`, as a predicate: `p` starts at `v`, ends at `d`, is
loop-free, and each vertex of `p` forwards to the next one. -/
def Follows (f : Profile G d) (v : V) (p : List V) : Prop :=
  p.head? = some v ∧ p.getLast? = some d ∧ p.Nodup ∧
    p.IsChain (fun x y => x ≠ d ∧ nextHop f x = y)

/-! #### Basic facts about routes -/

lemma nextHop_player (f : Profile G d) (i : Player d) : nextHop f i.1 = (f i).1 := by
  simp [nextHop, i.2]

lemma nextHop_update_of_ne (f : Profile G d) (i : Player d) (y : Strategy G d i) {x : V}
    (hx : x ≠ i.1) : nextHop (update f i y) x = nextHop f x := by
  unfold nextHop
  split_ifs with h
  · rfl
  · rw [update_of_ne]
    intro hc
    exact hx (congrArg Subtype.val hc)

lemma nextHop_adj (f : Profile G d) {x : V} (hx : x ≠ d) : G.Adj x (nextHop f x) := by
  simpa [nextHop, hx] using (f ⟨x, hx⟩).2

lemma walkTo_spec (f : Profile G d) :
    ∀ (n : ℕ) (v : V) (p : List V), walkTo f n v = some p →
      p.head? = some v ∧ p.getLast? = some d ∧ p.IsChain (fun x y => x ≠ d ∧ nextHop f x = y)
  | 0, v, p, h => by
    simp only [walkTo] at h
    split_ifs at h with hv
    cases h
    simp [hv]
  | n + 1, v, p, h => by
    simp only [walkTo] at h
    split_ifs at h with hv
    · cases h; simp [hv]
    · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨h1, h2, h3⟩ := walkTo_spec f n _ q hq
      refine ⟨rfl, ?_, ?_⟩
      · cases q with
        | nil => simp at h1
        | cons a q => simpa [List.getLast?_cons] using h2
      · cases q with
        | nil => simp at h1
        | cons a q =>
          simp only [List.head?_cons, Option.some.injEq] at h1
          subst h1
          exact .cons_cons ⟨hv, rfl⟩ h3

lemma walkTo_of_follows (f : Profile G d) :
    ∀ (n : ℕ) (v : V) (p : List V), Follows f v p → p.length ≤ n + 1 → walkTo f n v = some p := by
  intro n v p hp hlen
  obtain ⟨h1, h2, h3, h4⟩ := hp
  induction p generalizing n v with
  | nil => simp at h1
  | cons a q ih =>
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    cases q with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h2
      subst h2
      cases n <;> simp [walkTo]
    | cons b q =>
      obtain ⟨⟨ha, hb⟩, h4'⟩ := List.isChain_cons_cons.1 h4
      cases n with
      | zero => simp at hlen
      | succ n =>
        have := ih n b (by simpa using hlen) rfl (by simpa [List.getLast?_cons] using h2)
          (List.nodup_cons.1 h3).2 h4'
        simp [walkTo, ha, hb, this]

variable [Fintype V]

/-- The route from `v` to `d` under the forwarding profile `f`: follow the next hops (at most
`|V|` steps); `none` if `d` is not reached by a simple (loop-free) route. -/
def route (f : Profile G d) (v : V) : Option (List V) :=
  (walkTo f (Fintype.card V) v).filter (fun p => decide p.Nodup)

/-- The route function computes exactly the `Follows` relation. -/
lemma route_eq_some_iff (f : Profile G d) (v : V) (p : List V) :
    route f v = some p ↔ Follows f v p := by
  constructor
  · intro h
    simp only [route, Option.filter_eq_some_iff, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := walkTo_spec f _ v p h.1
    exact ⟨h1, h2, h.2, h3⟩
  · intro h
    have hlen : p.length ≤ Fintype.card V + 1 := (h.2.2.1.length_le_card).trans (by omega)
    simp only [route, walkTo_of_follows f _ v p h hlen, Option.filter_some, decide_eq_true_eq,
      h.2.2.1, ite_true]

lemma Follows.unique {f : Profile G d} {v : V} {p q : List V} (hp : Follows f v p)
    (hq : Follows f v q) : p = q := by
  rw [← route_eq_some_iff] at hp hq
  rw [hp] at hq
  exact Option.some.inj hq

omit [Fintype V] in
lemma Follows.isSimpleRoute {f : Profile G d} {v : V} {p : List V} (h : Follows f v p) :
    IsSimpleRoute G p v d :=
  ⟨h.1, h.2.1, h.2.2.2.imp (fun _ _ ⟨hx, hxy⟩ => hxy ▸ nextHop_adj f hx), h.2.2.1⟩

/-- The utility of the source node `i` under `f`: the rank of its route to `d`, or `0` if there
is no route. -/
def utility (ρ : Rankings G d) (f : Profile G d) (i : Player d) : ℕ :=
  match route f i.1 with
  | some p => ρ.rank i.1 p
  | none => 0

variable (G d) in
/-- **The BGP game** of Section 3.3 with rankings `ρ` and tie-breaking rule `prec`. -/
def bgpGame (ρ : Rankings G d) (prec : ∀ i : Player d, Strategy G d i → Strategy G d i → Prop) :
    TieBreakGame (Player d) (Strategy G d) ℕ where
  utility i f := utility ρ f i
  prec := prec

/-- A *routing tree*: every vertex has a route to `d` under `f` (the next hops then form a tree
rooted at `d`). A *stable* routing tree is one which is moreover a pure Nash equilibrium. -/
def IsRoutingTree (f : Profile G d) : Prop :=
  ∀ v, (route f v).isSome

lemma utility_eq_of_follows (ρ : Rankings G d) {f : Profile G d} {i : Player d} {p : List V}
    (h : Follows f i.1 p) : utility ρ f i = ρ.rank i.1 p := by
  rw [← route_eq_some_iff] at h
  simp [utility, h]

lemma utility_eq_zero (ρ : Rankings G d) {f : Profile G d} {i : Player d}
    (h : ∀ p, ¬ Follows f i.1 p) : utility ρ f i = 0 := by
  unfold utility
  split
  · next p hp => exact absurd ((route_eq_some_iff _ _ _).1 hp) (h p)
  · rfl

omit [Fintype V] in
lemma Follows.of_agree {f f' : Profile G d} {v : V} {p : List V} (h : Follows f v p)
    (hag : ∀ x ∈ p, x ≠ d → nextHop f' x = nextHop f x) : Follows f' v p :=
  ⟨h.1, h.2.1, h.2.2.1, isChain_imp_of_mem
    (fun x hx _ hxy => ⟨hxy.1, (hag x hx hxy.1).trans hxy.2⟩) h.2.2.2⟩

omit [Fintype V] in
lemma follows_dest (f : Profile G d) : Follows f d [d] := by
  simp [Follows]

end Model

/-! ### Dispute wheels -/

section DisputeWheel

variable (G : SimpleGraph V) (d : V)

/-- A **Dispute Wheel** `(U, R, Q)` (Section 3.3, after Griffin–Shepherd–Wilfong): pivot nodes
`u 0, …, u (k-1)` (source nodes), *spokes* `Q i`, a simple route from `u i` to `d`, and *rims*
`R i`, a simple route from `u i` to `u (i+1)` (indices modulo `k`), such that `u i` ranks the
route `R i Q (i+1)` more highly than `Q i`. The concatenation `R i Q (i+1)` is written
`R i ++ (Q (i+1)).tail` (`Q (i+1)` starts at the last vertex of `R i`); since rankings are only
defined on simple routes, it is required to be a simple route from `u i` to `d`. -/
structure DisputeWheel (rank : V → List V → ℕ) where
  /-- The number of pivots. -/
  k : ℕ
  k_pos : 0 < k
  /-- The pivot nodes `u i`. -/
  pivot : ℕ → V
  /-- The spokes `Q i`. -/
  spoke : ℕ → List V
  /-- The rims `R i`. -/
  rim : ℕ → List V
  pivot_ne : ∀ i < k, pivot i ≠ d
  spoke_route : ∀ i < k, IsSimpleRoute G (spoke i) (pivot i) d
  rim_route : ∀ i < k, IsSimpleRoute G (rim i) (pivot i) (pivot ((i + 1) % k))
  rimSpoke_route : ∀ i < k, IsSimpleRoute G (rim i ++ (spoke ((i + 1) % k)).tail) (pivot i) d
  prefers : ∀ i < k,
    rank (pivot i) (spoke i) < rank (pivot i) (rim i ++ (spoke ((i + 1) % k)).tail)

/-- **No Dispute Wheel** (NDW): the network has no dispute wheel. -/
def NoDisputeWheel (rank : V → List V → ℕ) : Prop :=
  IsEmpty (DisputeWheel G d rank)

end DisputeWheel

/-! ### Subgames with fixed nodes -/

section Elimination

variable {G : SimpleGraph V} {d : V}

/-- The subgame in which the nodes of `F` are fixed to their next hops in `g` and all other
nodes are free. -/
def fixSubgame (F : Finset V) (g : Profile G d) : Subgame (Strategy G d) :=
  fun i => if i.1 ∈ F then {g i} else univ

/-- In the subgame `fixSubgame F g`, the node `x` can forward to `y`. -/
def CanFwd (F : Finset V) (g : Profile G d) (x y : V) : Prop :=
  x ≠ d ∧ G.Adj x y ∧ (x ∈ F → nextHop g x = y)

/-- `p` is a route from `v` to `d` that *exists* in the subgame `fixSubgame F g` (in the paper:
"a route is said to exist if all nodes along it can route accordingly in the current
subgame"). -/
def IsAvailable (F : Finset V) (g : Profile G d) (v : V) (p : List V) : Prop :=
  p.head? = some v ∧ p.getLast? = some d ∧ p.Nodup ∧ p.IsChain (CanFwd F g)

/-- Invariant of the elimination: `d` is not fixed, and every fixed node has a route to `d` under
`g` through fixed nodes. -/
def Inv (F : Finset V) (g : Profile G d) : Prop :=
  d ∉ F ∧ ∀ v ∈ F, ∃ p, Follows g v p ∧ ∀ x ∈ p, x = d ∨ x ∈ F

variable {F : Finset V} {g : Profile G d}

lemma mem_fixSubgame {j : Player d} {y : Strategy G d j} :
    y ∈ fixSubgame F g j ↔ (j.1 ∈ F → y = g j) := by
  unfold fixSubgame
  split_ifs with h <;> simp [h]

lemma IsAvailable.isSimpleRoute {v : V} {p : List V} (h : IsAvailable F g v p) :
    IsSimpleRoute G p v d :=
  ⟨h.1, h.2.1, h.2.2.2.imp (fun _ _ h => h.2.1), h.2.2.1⟩

lemma IsAvailable.suffix {v c : V} {pre post : List V} (h : IsAvailable F g v (pre ++ c :: post)) :
    IsAvailable F g c (c :: post) := by
  refine ⟨rfl, ?_, (List.nodup_append.1 h.2.2.1).2.1, h.2.2.2.right_of_append⟩
  have := h.2.1
  rw [List.getLast?_append] at this
  simpa [List.getLast?_cons] using this

lemma nextHop_eq_of_agree {f : Profile G d} (hdF : d ∉ F)
    (hf : ∀ j : Player d, j.1 ∈ F → f j = g j) {x : V} (hx : x ∈ F) :
    nextHop f x = nextHop g x := by
  have hxd : x ≠ d := fun h => hdF (h ▸ hx)
  simp [nextHop, hxd, hf ⟨x, hxd⟩ hx]

/-- A route followed by a profile of the subgame exists in the subgame. -/
lemma Follows.isAvailable {f : Profile G d} {v : V} {p : List V} (hdF : d ∉ F)
    (hf : ∀ j : Player d, j.1 ∈ F → f j = g j) (h : Follows f v p) : IsAvailable F g v p :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.imp fun _ _ ⟨hx, hxy⟩ =>
    ⟨hx, hxy ▸ nextHop_adj f hx, fun hxF => (nextHop_eq_of_agree hdF hf hxF).symm.trans hxy⟩⟩

lemma isAvailable_of_fixed (hinv : Inv F g) {v : V} (hv : v = d ∨ v ∈ F) :
    ∃ p, IsAvailable F g v p := by
  rcases hv with rfl | hv
  · exact ⟨[v], by simp [IsAvailable]⟩
  · obtain ⟨p, hp, -⟩ := hinv.2 v hv
    exact ⟨p, hp.isAvailable hinv.1 (fun _ _ => rfl)⟩

lemma exists_isAvailable_aux (hinv : Inv F g) :
    ∀ {u v : V} (_ : G.Walk u v), v = d → ∃ p, IsAvailable F g u p := by
  intro u v w
  induction w with
  | nil => intro h; exact isAvailable_of_fixed hinv (Or.inl h)
  | @cons x y _ hadj _ ih =>
    intro hv
    obtain ⟨q, hq⟩ := ih hv
    by_cases hxq : x ∈ q
    · obtain ⟨pre, post, rfl⟩ := List.append_of_mem hxq
      exact ⟨_, hq.suffix⟩
    by_cases hx : x = d ∨ x ∈ F
    · exact isAvailable_of_fixed hinv hx
    push Not at hx
    cases q with
    | nil => simp [IsAvailable] at hq
    | cons a q =>
      have hay : a = y := by simpa using hq.1
      subst hay
      refine ⟨x :: a :: q, rfl, ?_, List.nodup_cons.2 ⟨hxq, hq.2.2.1⟩, ?_⟩
      · simpa [List.getLast?_cons] using hq.2.1
      · exact .cons_cons ⟨hx.1, hadj, fun h => absurd h hx.2⟩ hq.2.2.2

/-- In a connected graph every node has a route that exists in the subgame. -/
lemma exists_isAvailable (hconn : G.Connected) (hinv : Inv F g) (v : V) :
    ∃ p, IsAvailable F g v p := by
  obtain ⟨w⟩ := hconn.preconnected v d
  exact exists_isAvailable_aux hinv w rfl

variable [Fintype V]

/-- Every node has a best route among those that exist in the subgame. -/
lemma exists_best (ρ : Rankings G d) (hconn : G.Connected) (hinv : Inv F g) (v : V) :
    ∃ R, IsAvailable F g v R ∧ ∀ q, IsAvailable F g v q → ρ.rank v q ≤ ρ.rank v R := by
  have hfin : {q | IsAvailable F g v q}.Finite :=
    (List.finite_length_le V (Fintype.card V)).subset (fun q hq => hq.2.2.1.length_le_card)
  obtain ⟨q0, hq0⟩ := exists_isAvailable hconn hinv v
  obtain ⟨R, hR, hmax⟩ := Set.exists_max_image _ (ρ.rank v) hfin ⟨q0, hq0⟩
  exact ⟨R, hR, fun q hq => hmax q hq⟩

/-- **Key lemma of the proof of Theorem 3.6** (dispute-wheel argument): under No Dispute Wheel, if
some source node is not fixed, then some non-fixed node `b` can *guarantee* its most preferred
route existing in the subgame: that route has the form `b :: post` with all nodes of `post` fixed
(or `d`). -/
theorem exists_guarantee (ρ : Rankings G d) (hconn : G.Connected)
    (hndw : NoDisputeWheel G d ρ.rank) (hinv : Inv F g) (hex : ∃ v, v ≠ d ∧ v ∉ F) :
    ∃ b post, b ≠ d ∧ b ∉ F ∧ IsAvailable F g b (b :: post) ∧ (∀ x ∈ post, x = d ∨ x ∈ F) ∧
      ∀ q, IsAvailable F g b q → ρ.rank b q ≤ ρ.rank b (b :: post) := by
  by_contra hcon
  push Not at hcon
  let U := {v : V // v ≠ d ∧ v ∉ F}
  have hbest : ∀ a : U, ∃ R, IsAvailable F g a.1 R ∧
      ∀ q, IsAvailable F g a.1 q → ρ.rank a.1 q ≤ ρ.rank a.1 R :=
    fun a => exists_best ρ hconn hinv a.1
  choose R hRa hRb using hbest
  -- the last non-fixed node on the best route of `a`
  have hdec : ∀ a : U, ∃ pre, ∃ c : U, ∃ post,
      R a = pre ++ c.1 :: post ∧ ∀ x ∈ post, x = d ∨ x ∈ F := by
    intro a
    have hmem : a.1 ∈ R a := List.mem_of_mem_head? (by rw [(hRa a).1]; rfl)
    obtain ⟨pre, c, post, he, hc, hpost⟩ :=
      exists_split_last (P := fun x => x ≠ d ∧ x ∉ F) (R a) ⟨a.1, hmem, a.2⟩
    exact ⟨pre, ⟨c, hc⟩, post, he, fun x hx => by have := hpost x hx; tauto⟩
  choose pre c post hRdec hpost using hdec
  have hsuf : ∀ a : U, IsAvailable F g (c a).1 ((c a).1 :: post a) := fun a => by
    have := hRa a
    rw [hRdec a] at this
    exact this.suffix
  have hlt : ∀ a : U, ρ.rank (c a).1 ((c a).1 :: post a) < ρ.rank (c a).1 (R (c a)) := by
    intro a
    obtain ⟨q, hq, hlt⟩ := hcon (c a).1 (post a) (c a).2.1 (c a).2.2 (hsuf a) (hpost a)
    exact hlt.trans_le (hRb (c a) q hq)
  -- the sequence `a₀, a₁, …` of the paper
  obtain ⟨v0, hv0, hv0F⟩ := hex
  let s : ℕ → U := fun j => c^[j] ⟨v0, hv0, hv0F⟩
  have hs : ∀ j, c (s j) = s (j + 1) := fun j => (Function.iterate_succ_apply' c j _).symm
  obtain ⟨p1, p2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite s
  obtain ⟨p, q, hpq, hpq'⟩ : ∃ p q, p < q ∧ s p = s q := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨p1, p2, h, heq⟩
    · exact ⟨p2, p1, h, heq.symm⟩
  set k := q - p with hk
  have hadd : ∀ m, s (p + m) = c^[m] (s p) := fun m => by
    simp only [s]
    rw [add_comm, Function.iterate_add_apply]
  have hper : IsPeriodicPt c k (s p) := by
    show c^[k] (s p) = s p
    rw [← hadd, show p + k = q by omega, hpq']
  have hmod : ∀ m, s (p + m % k) = s (p + m) := fun m => by
    rw [hadd, hadd, hper.iterate_mod_apply]
  have hmod1 : ∀ m, s (p + m % k + 1) = s (p + m + 1) := fun m => by
    rw [← hs, hmod, hs]
  -- the dispute wheel
  have hRS : ∀ i, (pre (s (p + i + 1)) ++ [(s (p + i + 2)).1]) ++
      ((s (p + (i + 1) % k + 1)).1 :: post (s (p + (i + 1) % k))).tail = R (s (p + i + 1)) := by
    intro i
    rw [hRdec, hs, hmod]
    simp [show p + i + 1 + 1 = p + i + 2 by omega, show p + (i + 1) = p + i + 1 by omega]
  have hwheel : DisputeWheel G d ρ.rank :=
    { k := k
      k_pos := by omega
      pivot := fun i => (s (p + i + 1)).1
      spoke := fun i => (s (p + i + 1)).1 :: post (s (p + i))
      rim := fun i => pre (s (p + i + 1)) ++ [(s (p + i + 2)).1]
      pivot_ne := fun i _ => (s (p + i + 1)).2.1
      spoke_route := fun i _ => by
        have := (hsuf (s (p + i))).isSimpleRoute
        rwa [hs] at this
      rim_route := fun i _ => by
        have hR := hRa (s (p + i + 1))
        rw [hRdec, hs, show p + i + 1 + 1 = p + i + 2 by omega] at hR
        obtain ⟨h1, -, h3, h4⟩ := hR
        rw [← List.singleton_append, ← List.append_assoc] at h3 h4
        refine ⟨?_, ?_, h4.left_of_append.imp (fun _ _ h => h.2.1), h3.of_append_left⟩
        · rw [← h1]
          cases pre (s (p + i + 1)) <;> simp
        · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
          rw [hmod1, show p + (i + 1) + 1 = p + i + 2 by omega]
      rimSpoke_route := fun i _ => by
        rw [hRS]
        exact (hRa _).isSimpleRoute
      prefers := fun i _ => by
        rw [hRS]
        have := hlt (s (p + i))
        rwa [hs] at this }
  exact hndw.false hwheel

end Elimination

/-! ### One elimination stage -/

section Stage

variable {G : SimpleGraph V} {d : V} [Fintype V]

/-- One stage of the elimination of the proof of Theorem 3.6: the non-fixed node `i` can guarantee
its most preferred existing route `i :: u :: rest` (all of whose other nodes are fixed or `d`); it
gets fixed to the next hop `u`, i.e. all its other actions are eliminated. -/
def Step (ρ : Rankings G d) (F : Finset V) (g : Profile G d) (F' : Finset V) (g' : Profile G d) :
    Prop :=
  ∃ (i : Player d) (u : V) (rest : List V), i.1 ∉ F ∧ IsAvailable F g i.1 (i.1 :: u :: rest) ∧
    (∀ x ∈ u :: rest, x = d ∨ x ∈ F) ∧
    (∀ q, IsAvailable F g i.1 q → ρ.rank i.1 q ≤ ρ.rank i.1 (i.1 :: u :: rest)) ∧
    F' = insert i.1 F ∧ (g' i).1 = u ∧ ∀ j, j ≠ i → g' j = g j

variable {F F' : Finset V} {g g' : Profile G d}

omit [Fintype V] in
/-- Under every profile of the subgame in which `i` forwards to `u`, the route of `i` is
`i :: u :: rest`. -/
lemma follows_chosen {i : Player d} {u : V} {rest : List V} (hdF : d ∉ F)
    (hav : IsAvailable F g i.1 (i.1 :: u :: rest)) (hfix : ∀ x ∈ u :: rest, x = d ∨ x ∈ F)
    {f : Profile G d} (hf : ∀ j : Player d, j.1 ∈ F → f j = g j) (hfi : (f i).1 = u) :
    Follows f i.1 (i.1 :: u :: rest) := by
  refine ⟨rfl, hav.2.1, hav.2.2.1, List.isChain_cons_cons.2 ⟨⟨i.2, by rw [nextHop_player, hfi]⟩,
    isChain_imp_of_mem (fun x hx y hxy => ⟨hxy.1, ?_⟩) (List.isChain_cons_cons.1 hav.2.2.2).2⟩⟩
  have hxF : x ∈ F := (hfix x hx).resolve_left hxy.1
  rw [nextHop_eq_of_agree hdF hf hxF]
  exact hxy.2.2 hxF

/-- **Strictness**: against every profile of the subgame, each action of `i` other than `u` gives
`i` strictly less utility than `u`. -/
lemma utility_lt_of_ne {ρ : Rankings G d} {i : Player d} {u : V} {rest : List V} (hdF : d ∉ F)
    (hiF : i.1 ∉ F) (hav : IsAvailable F g i.1 (i.1 :: u :: rest))
    (hfix : ∀ x ∈ u :: rest, x = d ∨ x ∈ F)
    (hbest : ∀ q, IsAvailable F g i.1 q → ρ.rank i.1 q ≤ ρ.rank i.1 (i.1 :: u :: rest))
    {f : Profile G d} (hf : ∀ j : Player d, j.1 ∈ F → f j = g j) {y y' : Strategy G d i}
    (hy : y.1 ≠ u) (hy' : y'.1 = u) :
    utility ρ (update f i y) i < utility ρ (update f i y') i := by
  have hupd : ∀ z : Strategy G d i, ∀ j : Player d, j.1 ∈ F → update f i z j = g j := by
    intro z j hj
    rw [update_of_ne (by rintro rfl; exact hiF hj)]
    exact hf j hj
  rw [utility_eq_of_follows ρ (follows_chosen hdF hav hfix (hupd y') (by simpa using hy'))]
  by_cases h : ∃ p, Follows (update f i y) i.1 p
  · obtain ⟨p, hp⟩ := h
    rw [utility_eq_of_follows ρ hp]
    have hpav := hp.isAvailable hdF (hupd y)
    refine lt_of_le_of_ne (hbest p hpav) (fun heq => ?_)
    have hpeq := ρ.rank_inj i.1 i.2 _ _ hpav.isSimpleRoute hav.isSimpleRoute heq
    subst hpeq
    have := (List.isChain_cons_cons.1 hp.2.2.2).1.2
    rw [nextHop_player, update_self] at this
    exact hy this
  · push Not at h
    rw [utility_eq_zero ρ h]
    exact ρ.rank_pos i.1 i.2 _ hav.isSimpleRoute

/-- At the stage where `i` is fixed, `i`'s guaranteed route is globally optimal for `i` in the
subgame. -/
lemma utility_le_of_stage {ρ : Rankings G d} {i : Player d} {u : V} {rest : List V}
    (hdF : d ∉ F)
    (hbest : ∀ q, IsAvailable F g i.1 q → ρ.rank i.1 q ≤ ρ.rank i.1 (i.1 :: u :: rest))
    {t : Profile G d} (ht : ∀ j : Player d, j.1 ∈ F → t j = g j) :
    utility ρ t i ≤ ρ.rank i.1 (i.1 :: u :: rest) := by
  by_cases h : ∃ p, Follows t i.1 p
  · obtain ⟨p, hp⟩ := h
    rw [utility_eq_of_follows ρ hp]
    exact hbest p (hp.isAvailable hdF ht)
  · push Not at h
    rw [utility_eq_zero ρ h]
    exact Nat.zero_le _

namespace Step

variable {ρ : Rankings G d}

omit [Fintype V] in
lemma agree (hst : Step ρ F g F' g') : ∀ j : Player d, j.1 ∈ F → g' j = g j := by
  obtain ⟨i, u, rest, hiF, -, -, -, -, -, hg'⟩ := hst
  exact fun j hj => hg' j (fun h => hiF (h ▸ hj))

omit [Fintype V] in
lemma card (hst : Step ρ F g F' g') : F'.card = F.card + 1 := by
  obtain ⟨i, u, rest, hiF, -, -, -, hF', -, -⟩ := hst
  rw [hF', Finset.card_insert_of_notMem hiF]

omit [Fintype V] in
/-- Routes of fixed nodes persist. -/
lemma persist (hinv : Inv F g) (hst : Step ρ F g F' g') {v : V} {p : List V}
    (hp : Follows g v p) (hpF : ∀ x ∈ p, x = d ∨ x ∈ F) :
    Follows g' v p ∧ ∀ x ∈ p, x = d ∨ x ∈ F' := by
  have hag := hst.agree
  obtain ⟨i, u, rest, hiF, -, -, -, hF', -, -⟩ := hst
  refine ⟨hp.of_agree fun x hx hxd => nextHop_eq_of_agree hinv.1 hag ((hpF x hx).resolve_left hxd),
    fun x hx => ?_⟩
  rw [hF']
  rcases hpF x hx with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_insert_of_mem h)

omit [Fintype V] in
lemma inv (hinv : Inv F g) (hst : Step ρ F g F' g') : Inv F' g' := by
  have hst' := hst
  obtain ⟨i, u, rest, hiF, hav, hfix, -, hF', hg'i, -⟩ := hst'
  refine ⟨by rw [hF']; simp [Finset.mem_insert, hinv.1, Ne.symm i.2], fun v hv => ?_⟩
  rw [hF'] at hv ⊢
  rcases Finset.mem_insert.1 hv with rfl | hv
  · refine ⟨_, follows_chosen hinv.1 hav hfix hst.agree hg'i, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr (Finset.mem_insert_self _ _)
    · rcases hfix x hx with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_insert_of_mem h)
  · obtain ⟨p, hp, hpF⟩ := hinv.2 v hv
    have := hst.persist hinv hp hpF
    rw [hF'] at this
    exact ⟨p, this⟩

/-- Each stage is a (strict) NBR-elimination step, for every tie-breaking rule. -/
lemma elimStep (prec : ∀ i : Player d, Strategy G d i → Strategy G d i → Prop)
    (hinv : Inv F g) (hst : Step ρ F g F' g') :
    (bgpGame G d ρ prec).ElimStep (fixSubgame F g) (fixSubgame F' g') := by
  have hag := hst.agree
  obtain ⟨i, u, rest, hiF, hav, hfix, hbest, hF', hg'i, hg'o⟩ := hst
  refine ⟨fun j y hy => ?_, fun j y hy hy' => ?_⟩
  · rw [mem_fixSubgame] at hy ⊢
    intro hj
    by_cases hji : j = i
    · subst hji; exact absurd hj hiF
    · rw [hy (by rw [hF']; exact Finset.mem_insert_of_mem hj), hg'o j hji]
  · rw [mem_fixSubgame] at hy hy'
    push Not at hy'
    obtain ⟨hj', hne⟩ := hy'
    have hji : j = i := by
      by_contra hji
      rw [hF'] at hj'
      have hjF : j.1 ∈ F := (Finset.mem_insert.1 hj').resolve_left
        (fun h => hji (Subtype.ext h))
      exact hne (by rw [hy hjF, hg'o j hji])
    subst hji
    intro f hf
    refine ⟨g' j, by rw [mem_fixSubgame]; intro h; exact absurd h hiF, Or.inl ?_⟩
    have hfF : ∀ l : Player d, l.1 ∈ F → f l = g l := by
      intro l hl
      have hlj : l ≠ j := fun h => hiF (h ▸ hl)
      exact (mem_fixSubgame.1 (hf l hlj)) hl
    refine utility_lt_of_ne hinv.1 hiF hav hfix hbest hfF (fun h => hne ?_) hg'i
    exact Subtype.ext (h.trans hg'i.symm)

/-- Strict eliminations preserve every pure Nash equilibrium. -/
lemma nash_mem (prec : ∀ i : Player d, Strategy G d i → Strategy G d i → Prop)
    (hinv : Inv F g) (hst : Step ρ F g F' g') {t : Profile G d}
    (ht : (bgpGame G d ρ prec).IsNash t) (htF : ∀ j, t j ∈ fixSubgame F g j) :
    ∀ j, t j ∈ fixSubgame F' g' j := by
  obtain ⟨i, u, rest, hiF, hav, hfix, hbest, hF', hg'i, hg'o⟩ := hst
  have htg : ∀ l : Player d, l.1 ∈ F → t l = g l := fun l => mem_fixSubgame.1 (htF l)
  intro j
  rw [mem_fixSubgame]
  intro hj
  by_cases hji : j = i
  · subst hji
    by_contra hne
    have hlt := utility_lt_of_ne (ρ := ρ) hinv.1 hiF hav hfix hbest htg (y := t j) (y' := g' j)
      (fun h => hne (Subtype.ext (h.trans hg'i.symm))) hg'i
    rw [update_eq_self] at hlt
    exact absurd (ht j (g' j)) (not_le.2 hlt)
  · rw [hF'] at hj
    have hjF : j.1 ∈ F := (Finset.mem_insert.1 hj).resolve_left (fun h => hji (Subtype.ext h))
    rw [htg j hjF, hg'o j hji]

end Step

/-- Existence of a stage (from the key lemma `exists_guarantee`). -/
lemma exists_step (ρ : Rankings G d) (hconn : G.Connected) (hndw : NoDisputeWheel G d ρ.rank)
    (hinv : Inv F g) (hex : ∃ v, v ≠ d ∧ v ∉ F) : ∃ F' g', Step ρ F g F' g' := by
  obtain ⟨b, post, hb, hbF, hav, hfix, hbest⟩ := exists_guarantee ρ hconn hndw hinv hex
  cases post with
  | nil =>
    have := hav.2.1
    simp only [List.getLast?_singleton, Option.some.injEq] at this
    exact absurd this hb
  | cons u rest =>
    have hadj : G.Adj b u := (List.isChain_cons_cons.1 hav.2.2.2).1.2.1
    let i : Player d := ⟨b, hb⟩
    refine ⟨insert b F, update g i ⟨u, hadj⟩, i, u, rest, hbF, hav, hfix, hbest, rfl,
      by simp, fun j hj => update_of_ne hj _ _⟩

end Stage

/-! ### Theorem 3.6 -/

section Main

variable {G : SimpleGraph V} {d : V} [Fintype V]

/-- **Theorem 3.6 of [NSVZ].** For a BGP game on a connected network satisfying No Dispute Wheel
(an assumption used, but not stated, in the paper) and for *every* tie-breaking rule `prec`:
there is an NBR-elimination sequence `E 0, …, E r` with `r ≤ n` (`n` = number of source nodes)
ending in a single profile `s` (so the game is NBR-solvable and `e_G ≤ n`); `s` is a stable
routing tree (every node has a route to `d`, and `s` is a pure Nash equilibrium); `s` is the
*unique* pure Nash equilibrium; and the same sequence witnesses that `s` is a clear outcome for
every player. -/
theorem theorem_3_6 (ρ : Rankings G d) (hconn : G.Connected) (hndw : NoDisputeWheel G d ρ.rank)
    (prec : ∀ i : Player d, Strategy G d i → Strategy G d i → Prop) :
    ∃ (E : ℕ → Subgame (Strategy G d)) (r : ℕ) (s : Profile G d),
      (bgpGame G d ρ prec).Solves E r s ∧ r ≤ Fintype.card (Player d) ∧
      IsRoutingTree s ∧ (bgpGame G d ρ prec).IsNash s ∧
      (∀ t, (bgpGame G d ρ prec).IsNash t → t = s) ∧
      ∀ i, ∃ k ≤ r, (bgpGame G d ρ prec).ClearWitness s i E r k := by
  -- an initial profile
  have aux : ∀ {u v : V} (w : G.Walk u v), u ≠ v → ∃ x, G.Adj u x := by
    intro u v w h
    cases w with
    | nil => exact absurd rfl h
    | cons h' _ => exact ⟨_, h'⟩
  have hnb : ∀ i : Player d, ∃ w, G.Adj i.1 w := by
    intro i
    obtain ⟨w⟩ := hconn.preconnected i.1 d
    exact aux w i.2
  choose w0 hw0 using hnb
  let g0 : Profile G d := fun i => ⟨w0 i, hw0 i⟩
  -- the stages
  have hstep : ∀ σ : Finset V × Profile G d, ∃ σ' : Finset V × Profile G d,
      Inv σ.1 σ.2 → (∃ v, v ≠ d ∧ v ∉ σ.1) → Step ρ σ.1 σ.2 σ'.1 σ'.2 := by
    intro σ
    by_cases h : Inv σ.1 σ.2 ∧ ∃ v, v ≠ d ∧ v ∉ σ.1
    · obtain ⟨F', g', h'⟩ := exists_step ρ hconn hndw h.1 h.2
      exact ⟨(F', g'), fun _ _ => h'⟩
    · exact ⟨σ, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose nxt hnxt using hstep
  let σ : ℕ → Finset V × Profile G d := fun k => nxt^[k] (∅, g0)
  have hσ : ∀ k, σ (k + 1) = nxt (σ k) := fun k => Function.iterate_succ_apply' nxt k _
  have hσ0 : σ 0 = (∅, g0) := rfl
  set n := Fintype.card (Player d) with hn
  have hncard : n = (Finset.univ.erase d).card := by simp [hn]
  have hsub : ∀ {F : Finset V} {g : Profile G d}, Inv F g → F ⊆ Finset.univ.erase d :=
    fun hinv x hx => Finset.mem_erase.2 ⟨fun h => hinv.1 (h ▸ hx), Finset.mem_univ _⟩
  have hI : ∀ k ≤ n, Inv (σ k).1 (σ k).2 ∧ (σ k).1.card = k ∧
      (k < n → Step ρ (σ k).1 (σ k).2 (σ (k + 1)).1 (σ (k + 1)).2) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hinv0 : Inv (σ 0).1 (σ 0).2 := by simp [hσ0, Inv]
      refine ⟨hinv0, by simp [hσ0], fun hk => ?_⟩
      rw [hσ]
      refine hnxt _ hinv0 ?_
      obtain ⟨v, hv, -⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := (σ 0).1) (t := Finset.univ.erase d) (by rw [hσ0, Finset.card_empty, ← hncard]; omega)
      exact ⟨v, (Finset.mem_erase.1 hv).1, by simp [hσ0]⟩
    | succ k ih =>
      intro hk
      obtain ⟨hinv, hcard, hst⟩ := ih (by omega)
      have hst := hst (by omega)
      have hinv' := hst.inv hinv
      refine ⟨hinv', by rw [hst.card, hcard], fun hk' => ?_⟩
      rw [hσ (k + 1)]
      refine hnxt _ hinv' ?_
      obtain ⟨v, hv, hvF⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := (σ (k + 1)).1) (t := Finset.univ.erase d) (by rw [hst.card, hcard]; omega)
      exact ⟨v, (Finset.mem_erase.1 hv).1, hvF⟩
  have hInv : ∀ k ≤ n, Inv (σ k).1 (σ k).2 := fun k hk => (hI k hk).1
  have hS : ∀ k < n, Step ρ (σ k).1 (σ k).2 (σ (k + 1)).1 (σ (k + 1)).2 :=
    fun k hk => (hI k hk.le).2.2 hk
  -- at the end, every source node is fixed
  have hall : ∀ v, v ≠ d → v ∈ (σ n).1 := by
    have heq : (σ n).1 = Finset.univ.erase d :=
      Finset.eq_of_subset_of_card_le (hsub (hInv n le_rfl)) (by rw [(hI n le_rfl).2.1, hncard])
    intro v hv
    rw [heq]
    exact Finset.mem_erase.2 ⟨hv, Finset.mem_univ _⟩
  let E : ℕ → Subgame (Strategy G d) := fun k => fixSubgame (σ k).1 (σ k).2
  let s : Profile G d := (σ n).2
  set Γ := bgpGame G d ρ prec with hΓ
  have hsolves : Γ.Solves E n s := by
    refine ⟨⟨?_, fun k hk => (hS k hk).elimStep prec (hInv k hk.le)⟩, ?_⟩
    · funext i
      simp [E, hσ0, fixSubgame, TieBreakGame.full]
    · funext i
      simp [E, s, fixSubgame, hall i.1 i.2]
  -- persistence of routes
  have hpersist : ∀ k ≤ n, ∀ v p, Follows (σ k).2 v p → (∀ x ∈ p, x = d ∨ x ∈ (σ k).1) →
      ∀ m, k ≤ m → m ≤ n → Follows (σ m).2 v p ∧ ∀ x ∈ p, x = d ∨ x ∈ (σ m).1 := by
    intro k _ v p hp hpF m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact fun _ => ⟨hp, hpF⟩
    | succ m hkm ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact (hS m (by omega)).persist (hInv m (by omega)) h1 h2
  -- the stage at which each player is fixed: clear witnesses
  have hclear : ∀ i, ∃ k ≤ n, Γ.ClearWitness s i E n k := by
    intro i
    have hex : ∃ m, i.1 ∈ (σ m).1 := ⟨n, hall i.1 i.2⟩
    classical
    set m0 := Nat.find hex with hm0
    have hm0n : m0 ≤ n := Nat.find_min' hex (hall i.1 i.2)
    have hm0pos : m0 ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [← hm0, h, hσ0] at this
      simp at this
    obtain ⟨k, hk⟩ : ∃ k, m0 = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0pos
    have hiF : i.1 ∉ (σ k).1 := Nat.find_min hex (by omega)
    have hiF' : i.1 ∈ (σ (k + 1)).1 := hk ▸ Nat.find_spec hex
    have hst := hS k (by omega)
    have hag := hst.agree
    obtain ⟨j, u, rest, hjF, hav, hfix, hbest, hF', hg'j, -⟩ := hst
    have hij : i = j := by
      rw [hF'] at hiF'
      exact Subtype.ext ((Finset.mem_insert.1 hiF').resolve_right hiF)
    subst hij
    have hdF := (hInv k (by omega)).1
    have hfol := follows_chosen hdF hav hfix hag hg'j
    have hfolF : ∀ x ∈ i.1 :: u :: rest, x = d ∨ x ∈ (σ (k + 1)).1 := by
      intro x hx
      rw [hF']
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr (Finset.mem_insert_self _ _)
      · rcases hfix x hx with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_insert_of_mem h)
    have hfs := (hpersist (k + 1) (by omega) _ _ hfol hfolF n (by omega) le_rfl).1
    refine ⟨k, by omega, hsolves, by omega, ?_, fun t ht => ?_⟩
    · funext x
      simp [E, fixSubgame, hiF]
    · change utility ρ t i ≤ utility ρ s i
      rw [utility_eq_of_follows ρ hfs]
      exact utility_le_of_stage hdF hbest (fun l hl => mem_fixSubgame.1 (ht l) hl)
  -- `s` is a pure Nash equilibrium
  have hnash : Γ.IsNash s := by
    intro i x
    obtain ⟨k, hk, -, -, hEi, hopt⟩ := hclear i
    apply hopt
    intro j
    by_cases hji : j = i
    · subst hji
      rw [update_self, hEi]
      trivial
    · rw [update_of_ne hji]
      exact hsolves.mem hk j
  refine ⟨E, n, s, hsolves, le_rfl, ?_, hnash, ?_, hclear⟩
  · -- routing tree
    intro v
    by_cases hv : v = d
    · subst hv
      rw [route_eq_some_iff _ _ _ |>.2 (follows_dest _)]
      rfl
    · obtain ⟨p, hp, -⟩ := (hInv n le_rfl).2 v (hall v hv)
      rw [route_eq_some_iff _ _ _ |>.2 hp]
      rfl
  · -- uniqueness of the pure Nash equilibrium
    intro t ht
    have hmem : ∀ k ≤ n, ∀ j, t j ∈ E k j := by
      intro k
      induction k with
      | zero => intro _ j; rw [hsolves.1.1]; trivial
      | succ k ih =>
        intro hk
        exact (hS k (by omega)).nash_mem prec (hInv k (by omega)) ht (ih (by omega))
    funext j
    have := hmem n le_rfl j
    rw [hsolves.2] at this
    exact this

/-- Theorem 3.6, first item: the BGP game is NBR-solvable (for every tie-breaking rule). -/
theorem nbrSolvable (ρ : Rankings G d) (hconn : G.Connected) (hndw : NoDisputeWheel G d ρ.rank)
    (prec : ∀ i : Player d, Strategy G d i → Strategy G d i → Prop) :
    (bgpGame G d ρ prec).NBRSolvable := by
  obtain ⟨E, r, s, h, -⟩ := theorem_3_6 ρ hconn hndw prec
  exact ⟨E, r, s, h⟩

/-- Theorem 3.6, third item: `e_G ≤ n`. -/
theorem elimParam_le (ρ : Rankings G d) (hconn : G.Connected)
    (hndw : NoDisputeWheel G d ρ.rank)
    (prec : ∀ i : Player d, Strategy G d i → Strategy G d i → Prop) :
    (bgpGame G d ρ prec).elimParam ≤ Fintype.card (Player d) := by
  obtain ⟨E, r, s, h, hr, -⟩ := theorem_3_6 ρ hconn hndw prec
  have hmem : r ∈ {r | ∃ (E : ℕ → Subgame (Strategy G d)) (s : Profile G d),
      (bgpGame G d ρ prec).Solves E r s} := ⟨E, s, h⟩
  exact (Nat.sInf_le hmem).trans hr

/-- Theorem 3.6 (with the paper's Section 2 framework): the BGP game has a clear outcome, which is
a stable routing tree and the unique pure Nash equilibrium. -/
theorem hasClearOutcome (ρ : Rankings G d) (hconn : G.Connected)
    (hndw : NoDisputeWheel G d ρ.rank)
    (prec : ∀ i : Player d, Strategy G d i → Strategy G d i → Prop) :
    ∃ s, (bgpGame G d ρ prec).HasClearOutcome s ∧ IsRoutingTree s ∧
      (bgpGame G d ρ prec).IsNash s ∧ ∀ t, (bgpGame G d ρ prec).IsNash t → t = s := by
  obtain ⟨E, r, s, h, -, htree, hnash, huniq, hclear⟩ := theorem_3_6 ρ hconn hndw prec
  refine ⟨s, ⟨⟨E, r, h⟩, fun i => ?_⟩, htree, hnash, huniq⟩
  obtain ⟨k, -, hk⟩ := hclear i
  exact ⟨E, r, k, hk⟩

end Main

/-! ### BAD GADGET: without No Dispute Wheel, Theorem 3.6 fails -/

section BadGadget

/-- The clockwise neighbour in the BAD GADGET wheel `1 → 2 → 3 → 1` around the destination `0`. -/
def cw : Fin 4 → Fin 4 := ![0, 2, 3, 1]

/-- **BAD GADGET** (Griffin–Shepherd–Wilfong): the complete graph on `{0, 1, 2, 3}` with
destination `0`, where each source node `i` ranks the route `[i, cw i, 0]` through its clockwise
neighbour highest, its direct route `[i, 0]` second, and all other routes lower. Then there is no
pure Nash equilibrium (no stable routing tree), whatever the tie-breaking rule. -/
theorem badGadget_noNash (ρ : Rankings (⊤ : SimpleGraph (Fin 4)) 0)
    (h1 : ∀ i : Fin 4, i ≠ 0 → ρ.rank i [i, 0] < ρ.rank i [i, cw i, 0])
    (h2 : ∀ i : Fin 4, i ≠ 0 → ∀ p, IsSimpleRoute ⊤ p i 0 → p ≠ [i, cw i, 0] → p ≠ [i, 0] →
      ρ.rank i p < ρ.rank i [i, 0])
    (prec : ∀ i : Player (0 : Fin 4), Strategy ⊤ 0 i → Strategy ⊤ 0 i → Prop)
    (t : Profile (⊤ : SimpleGraph (Fin 4)) 0) : ¬ (bgpGame ⊤ 0 ρ prec).IsNash t := by
  intro ht
  have key : ∀ a : Fin 4, a ≠ 0 → (nextHop t (cw a) = 0 ↔ nextHop t a ≠ 0) := by
    intro a ha
    let i : Player (0 : Fin 4) := ⟨a, ha⟩
    have hcw : cw a ≠ 0 ∧ cw a ≠ a := by revert ha; revert a; decide
    let xd : Strategy ⊤ 0 i := ⟨0, by simpa using ha⟩
    let xc : Strategy ⊤ 0 i := ⟨cw a, by simpa using hcw.2.symm⟩
    have hfd : Follows (update t i xd) a [a, 0] := by
      refine ⟨rfl, rfl, by simp [ha], ?_⟩
      simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
      exact ⟨ha, by rw [nextHop_player (update t i xd) i, update_self]⟩
    have hNd : ρ.rank a [a, 0] ≤ utility ρ t i := by
      have := ht i xd
      change utility ρ (update t i xd) i ≤ utility ρ t i at this
      rwa [utility_eq_of_follows ρ hfd] at this
    obtain ⟨p, hp⟩ : ∃ p, Follows t a p := by
      by_contra hno
      push Not at hno
      rw [utility_eq_zero ρ hno] at hNd
      exact absurd hNd (not_le.2 (ρ.rank_pos a ha _ hfd.isSimpleRoute))
    have hu : utility ρ t i = ρ.rank a p := utility_eq_of_follows ρ hp
    rw [hu] at hNd
    have hp2 : p = [a, cw a, 0] ∨ p = [a, 0] := by
      by_contra hc
      push Not at hc
      exact absurd hNd (not_le.2 (h2 a ha p hp.isSimpleRoute hc.1 hc.2))
    constructor
    · intro hc0
      have hfc : Follows (update t i xc) a [a, cw a, 0] := by
        refine ⟨rfl, rfl, by simp [ha, hcw.1, Ne.symm hcw.2], ?_⟩
        simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
        refine ⟨⟨ha, by rw [nextHop_player (update t i xc) i, update_self]⟩, hcw.1, ?_⟩
        rw [nextHop_update_of_ne t i xc hcw.2, hc0]
      have hNc := ht i xc
      change utility ρ (update t i xc) i ≤ utility ρ t i at hNc
      rw [utility_eq_of_follows ρ hfc, hu] at hNc
      rcases hp2 with rfl | rfl
      · have := (List.isChain_cons_cons.1 hp.2.2.2).1.2
        rw [this]
        exact hcw.1
      · exact absurd hNc (not_le.2 (h1 a ha))
    · intro hne
      rcases hp2 with rfl | rfl
      · exact (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hp.2.2.2).2).1.2
      · exact absurd (List.isChain_cons_cons.1 hp.2.2.2).1.2 hne
  have k1 := key 1 (by decide)
  have k2 := key 2 (by decide)
  have k3 := key 3 (by decide)
  simp only [cw] at k1 k2 k3
  change nextHop t 2 = 0 ↔ ¬nextHop t 1 = 0 at k1
  change nextHop t 3 = 0 ↔ ¬nextHop t 2 = 0 at k2
  change nextHop t 1 = 0 ↔ ¬nextHop t 3 = 0 at k3
  tauto

/-- An injective encoding of lists over `Fin 4` (base `5`). -/
def enc : List (Fin 4) → ℕ
  | [] => 0
  | a :: l => a.val + 1 + 5 * enc l

lemma enc_lt : ∀ l : List (Fin 4), enc l < 5 ^ l.length
  | [] => by simp [enc]
  | a :: l => by
    have := enc_lt l
    have ha := a.isLt
    simp only [enc, List.length_cons, pow_succ]
    omega

lemma enc_injective : ∀ l l' : List (Fin 4), enc l = enc l' → l = l'
  | [], [], _ => rfl
  | [], b :: l', h => by simp only [enc] at h; omega
  | a :: l, [], h => by simp only [enc] at h; omega
  | a :: l, b :: l', h => by
    simp only [enc] at h
    have ha := a.isLt
    have hb := b.isLt
    have hab : a = b := Fin.ext (by omega)
    have hll : enc l = enc l' := by omega
    rw [hab, enc_injective l l' hll]

lemma enc_lt_of_isSimpleRoute {p : List (Fin 4)} {i : Fin 4}
    (h : IsSimpleRoute ⊤ p i 0) : enc p < 625 := by
  have hlen : p.length ≤ 4 := by simpa using h.2.2.2.length_le_card
  calc enc p < 5 ^ p.length := enc_lt p
    _ ≤ 5 ^ 4 := Nat.pow_le_pow_right (by norm_num) hlen
    _ = 625 := by norm_num

/-- A concrete BAD GADGET ranking: `[i, cw i, 0]` has rank `627`, `[i, 0]` rank `626`, all other
routes ranks below `626`. -/
def badGadgetRanking : Rankings (⊤ : SimpleGraph (Fin 4)) 0 where
  rank i p := if p = [i, cw i, 0] then 627 else if p = [i, 0] then 626 else enc p + 1
  rank_pos i _ p _ := by split_ifs <;> omega
  rank_inj i _ p q hp hq h := by
    have bp := enc_lt_of_isSimpleRoute hp
    have bq := enc_lt_of_isSimpleRoute hq
    split_ifs at h <;>
      first | omega | (subst_vars; rfl) | exact enc_injective p q (by omega)

lemma badGadgetRanking_h1 (i : Fin 4) (_ : i ≠ 0) :
    badGadgetRanking.rank i [i, 0] < badGadgetRanking.rank i [i, cw i, 0] := by
  simp [badGadgetRanking]

lemma badGadgetRanking_h2 (i : Fin 4) (_ : i ≠ 0) (p : List (Fin 4))
    (hp : IsSimpleRoute ⊤ p i 0) (h1 : p ≠ [i, cw i, 0]) (h2 : p ≠ [i, 0]) :
    badGadgetRanking.rank i p < badGadgetRanking.rank i [i, 0] := by
  have := enc_lt_of_isSimpleRoute hp
  simp only [badGadgetRanking, h1, h2, ite_false]
  simp
  omega

/-- The concrete BAD GADGET game has no pure Nash equilibrium (for every tie-breaking rule). -/
theorem badGadget_noNash' (prec : ∀ i : Player (0 : Fin 4), Strategy ⊤ 0 i → Strategy ⊤ 0 i → Prop)
    (t : Profile (⊤ : SimpleGraph (Fin 4)) 0) :
    ¬ (bgpGame ⊤ 0 badGadgetRanking prec).IsNash t :=
  badGadget_noNash badGadgetRanking badGadgetRanking_h1 badGadgetRanking_h2 prec t

/-- **Theorem 3.6 fails without No Dispute Wheel.** The BAD GADGET game (on a connected network)
is not NBR-solvable under any strict total tie-breaking rule: the outcome of NBR elimination
would be a pure Nash equilibrium (`Solves.isNash`), and there is none. -/
theorem badGadget_not_NBRSolvable
    (prec : ∀ i : Player (0 : Fin 4), Strategy ⊤ 0 i → Strategy ⊤ 0 i → Prop)
    [hprec : ∀ i, IsStrictTotalOrder _ (prec i)] :
    ¬ (bgpGame ⊤ 0 badGadgetRanking prec).NBRSolvable := by
  rintro ⟨E, r, s, h⟩
  have : ∀ i, IsStrictTotalOrder _ ((bgpGame ⊤ 0 badGadgetRanking prec).prec i) := hprec
  exact badGadget_noNash' prec s (h.isNash TieBreakGame.hasBR_of_finite)

/-- The hypothesis of `badGadget_not_NBRSolvable` is satisfiable (tie-breaking by vertex
order). -/
example : ¬ (bgpGame ⊤ 0 badGadgetRanking (fun _ x y => x < y)).NBRSolvable :=
  badGadget_not_NBRSolvable _

/-- The BAD GADGET network is connected; by Theorem 3.6 it therefore must contain a dispute
wheel (it does: the three nodes `1, 2, 3` with spokes `[i, 0]` and rims `[i, cw i]`). -/
theorem badGadget_disputeWheel :
    Nonempty (DisputeWheel (⊤ : SimpleGraph (Fin 4)) 0 badGadgetRanking.rank) := by
  by_contra h
  have hndw : NoDisputeWheel (⊤ : SimpleGraph (Fin 4)) 0 badGadgetRanking.rank :=
    not_nonempty_iff.1 h
  obtain ⟨E, r, s, -, -, -, hnash, -⟩ :=
    theorem_3_6 badGadgetRanking SimpleGraph.connected_top hndw (fun _ _ _ => False)
  exact badGadget_noNash' _ s hnash

end BadGadget

/-! ### Non-vacuity of the hypotheses of Theorem 3.6 -/

section NonVacuity

lemma fin2_route {p : List (Fin 2)} (h : IsSimpleRoute (⊤ : SimpleGraph (Fin 2)) p 1 0) :
    p = [1, 0] := by
  obtain ⟨h1, h2, -, h4⟩ := h
  have hlen : p.length ≤ 2 := by simpa using h4.length_le_card
  rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all

/-- The one-edge network `1 — 0` with its unique ranking. -/
def fin2Ranking : Rankings (⊤ : SimpleGraph (Fin 2)) 0 where
  rank _ _ := 1
  rank_pos _ _ _ _ := Nat.one_pos
  rank_inj i hi p q hp hq _ := by
    have hi1 : i = 1 := by omega
    subst hi1
    rw [fin2_route hp, fin2_route hq]

/-- No Dispute Wheel is satisfiable (so `theorem_3_6` is not vacuous). -/
lemma fin2_noDisputeWheel :
    NoDisputeWheel (⊤ : SimpleGraph (Fin 2)) 0 fin2Ranking.rank :=
  ⟨fun w => absurd (w.prefers 0 w.k_pos) (lt_irrefl 1)⟩

example (prec : ∀ i : Player (0 : Fin 2), Strategy ⊤ 0 i → Strategy ⊤ 0 i → Prop) :
    (bgpGame ⊤ 0 fin2Ranking prec).NBRSolvable :=
  nbrSolvable fin2Ranking SimpleGraph.connected_top fin2_noDisputeWheel prec

end NonVacuity

end Podc.BestResponseMechanisms.BGP
