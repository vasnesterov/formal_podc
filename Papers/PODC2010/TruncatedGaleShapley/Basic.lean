import Mathlib

-- CSLib candidate: Cslib/Algorithms/Lean/StableMatching/ (incomplete preferences on a graph,
-- unstable edges, ε-stability; synchronous Gale–Shapley with blue/red turns)

/-!
# Bicoloured graphs with preferences, unstable edges, and truncated Gale–Shapley

Floréen, Kaski, Polishchuk, Suomela, *Almost Stable Matchings in Constant Time*
(arXiv 0812.4893; brief announcement at PODC 2010), Sections 1.1 and 4.

* `PrefGraph V`: a finite simple graph given by neighbour sets `N v`, and for every node `v` a
  strict preference order on its neighbours, encoded by a rank `rank v u` (smaller = more
  preferred, injective on the neighbours of `v`).
* `PrefGraph.IsUnstable p u v` (§1.1): the edge `{u, v}` is unstable relative to the partner
  function `p` (each endpoint is unmatched or prefers the other one to its partner).
* `unstableEdges`, `matchingEdges`, `IsEpsStable` (Definition 1: at most `ε |M|` unstable edges).
* `Bicoloured V`: a `PrefGraph` whose nodes are red or blue, every edge joining a red and a blue
  node.
* The distributed variant of the Gale–Shapley algorithm of §4 as a global synchronous
  transition: `blueTurn`, `redTurn`, `round`, and `run I i` = the state at the end of round `i`.
  Nodes read the post-blue-turn states of their neighbours instead of explicit messages; the
  messages of §4 are recovered as follows (see `redStep1`, `redStep2`):
  'propose' to `b` ↔ `c r = some b`; 'accept' ↔ `b` now points to `r`; 'reject' (to a proposer)
  and 'break' (to the old partner) ↔ `b` now points elsewhere.
-/

namespace Podc.TruncatedGaleShapley

open Finset

set_option linter.unusedSectionVars false

/-- A finite simple graph (neighbour sets `N`) with a strict preference order of every node on its
neighbours: `v` prefers `x` over `y` iff `rank v x < rank v y`. -/
structure PrefGraph (V : Type*) where
  /-- The neighbours (acceptable partners) of a node. -/
  N : V → Finset V
  /-- Acceptability is symmetric. -/
  symm : ∀ {u v}, v ∈ N u → u ∈ N v
  /-- Preference rank (smaller = more preferred). -/
  rank : V → V → ℕ
  /-- Preferences are strict on the neighbours. -/
  rank_inj : ∀ {v u u'}, u ∈ N v → u' ∈ N v → rank v u = rank v u' → u = u'

variable {V : Type*}

namespace PrefGraph

variable (P : PrefGraph V)

/-- `v` is an acceptable partner that `u` prefers to its current partner `m` (`none` = unmatched:
then every neighbour is preferred). -/
def Prefers (u v : V) : Option V → Prop
  | none => True
  | some x => P.rank u v < P.rank u x

instance (u v : V) (m : Option V) : Decidable (P.Prefers u v m) := by
  cases m <;> unfold Prefers <;> infer_instance

/-- §1.1: the edge `{u, v}` is *unstable* relative to the matching given by the partner function
`p`: it is an edge, `u` is unmatched or prefers `v` to its partner, and `v` is unmatched or
prefers `u` to its partner. (Such an edge is automatically not in the matching.) -/
def IsUnstable (p : V → Option V) (u v : V) : Prop :=
  v ∈ P.N u ∧ P.Prefers u v (p u) ∧ P.Prefers v u (p v)

instance [DecidableEq V] (p : V → Option V) (u v : V) : Decidable (P.IsUnstable p u v) := by
  unfold IsUnstable; infer_instance

lemma isUnstable_comm {p : V → Option V} {u v : V} :
    P.IsUnstable p u v ↔ P.IsUnstable p v u :=
  ⟨fun ⟨h, a, b⟩ => ⟨P.symm h, b, a⟩, fun ⟨h, a, b⟩ => ⟨P.symm h, b, a⟩⟩

/-- A partner function `p` describes a matching of the graph: partners are neighbours and the
relation is symmetric. -/
structure IsMatching (p : V → Option V) : Prop where
  mem_N : ∀ u v, p u = some v → v ∈ P.N u
  symm : ∀ u v, p u = some v → p v = some u

/-- The matching is *stable* if there are no unstable edges. -/
def IsStable (p : V → Option V) : Prop := ∀ u v, ¬ P.IsUnstable p u v

variable [Fintype V] [DecidableEq V]

/-- The set of unstable edges `{u, v}`. -/
def unstableEdges (p : V → Option V) : Finset (Sym2 V) :=
  (univ.filter fun x : V × V => P.IsUnstable p x.1 x.2).image (fun x => s(x.1, x.2))

/-- Definition 1: a matching `p` is `ε`-stable if it has at most `ε |M|` unstable edges. -/
def IsEpsStable (ε : ℝ) (p : V → Option V) : Prop :=
  ((P.unstableEdges p).card : ℝ) ≤ ε * (((univ.filter fun x : V × V => p x.1 = some x.2).image
    (fun x => s(x.1, x.2))).card : ℝ)

end PrefGraph

/-- The edges `{u, v}` of the matching described by the partner function `p`. -/
def matchingEdges [Fintype V] [DecidableEq V] (p : V → Option V) : Finset (Sym2 V) :=
  (univ.filter fun x : V × V => p x.1 = some x.2).image (fun x => s(x.1, x.2))

lemma PrefGraph.isEpsStable_iff [Fintype V] [DecidableEq V] (P : PrefGraph V) (ε : ℝ)
    (p : V → Option V) :
    P.IsEpsStable ε p ↔ ((P.unstableEdges p).card : ℝ) ≤ ε * (matchingEdges p).card := Iff.rfl

/-- A bicoloured graph (§1.1): a `PrefGraph` whose nodes are red (`red v = true`) or blue, every
edge joining a red and a blue node. -/
structure Bicoloured (V : Type*) extends PrefGraph V where
  /-- The colour of a node: `true` = red (proposing side), `false` = blue. -/
  red : V → Bool
  /-- Every edge joins nodes of different colours. -/
  red_ne : ∀ {u v}, v ∈ N u → red v ≠ red u

/-- The state of the algorithm of §4: `C r` (candidate list of a red node, kept as a set ordered by
`rank r`), `c r` (the blue node to which `r` has an outstanding proposal) and the partner `p v`. -/
@[ext] structure State (V : Type*) where
  /-- Candidates of a red node. -/
  C : V → Finset V
  /-- Outstanding proposal of a red node. -/
  c : V → Option V
  /-- Current partner. -/
  p : V → Option V

namespace Bicoloured

variable [DecidableEq V] (I : Bicoloured V)

/-- The most preferred element of `S` for `v` (`none` iff `S = ∅`). -/
noncomputable def best (v : V) (S : Finset V) : Option V :=
  if h : S.Nonempty then some (S.exists_min_image (I.rank v) h).choose else none

/-- Initial state: every red node has all neighbours as candidates; nothing is matched or
proposed. -/
def init : State V where
  C v := if I.red v then I.N v else ∅
  c _ := none
  p _ := none

/-- The neighbours of `b` with an outstanding proposal to `b` (the set `P` of the blue turn). -/
def proposers (s : State V) (b : V) : Finset V := (I.N b).filter fun r => s.c r = some b

/-- Blue turn (§4): a blue node `b` with a nonempty set `P` of proposers keeps the most preferred
node of `P ∪ {p(b)}` as its partner (sending 'accept' to it if it is new, 'break' to the old
partner if replaced, 'reject' to the other proposers); otherwise nothing changes. -/
noncomputable def blueTurn (s : State V) : State V where
  C := s.C
  c := s.c
  p v := if I.red v = false ∧ (I.proposers s v).Nonempty then
      I.best v (I.proposers s v ∪ (s.p v).toFinset) else s.p v

/-- Step 1 of the red turn (state `s` after the blue turn): the response to the outstanding
proposal `c r = some b` is 'accept' iff `b` now points to `r` (then `p(r) ← b`); otherwise it is
'reject' and `b` is removed from `C(r)`. Returns the new `(C(r), p(r))`. -/
def redStep1 (s : State V) (r : V) : Finset V × Option V :=
  match s.c r with
  | none => (s.C r, s.p r)
  | some b => if s.p b = some r then (s.C r, some b) else ((s.C r).erase b, s.p r)

/-- Step 2 of the red turn: if `r` is matched to `b` and `b` now points elsewhere, `r` has
received 'break': `b` is removed from `C(r)` and `r` becomes unmatched. -/
def redStep2 (s : State V) (r : V) : Finset V × Option V → Finset V × Option V
  | (C, none) => (C, none)
  | (C, some b) => if s.p b = some r then (C, some b) else (C.erase b, none)

/-- Red turn (§4), steps 1–3; step 3 proposes to the first element of `C(r)` if `r` is unmatched
(`best r ∅ = none`: no proposal). -/
noncomputable def redTurn (s : State V) : State V where
  C v := if I.red v then (redStep2 s v (redStep1 s v)).1 else s.C v
  p v := if I.red v then (redStep2 s v (redStep1 s v)).2 else s.p v
  c v := if I.red v then
      (if (redStep2 s v (redStep1 s v)).2 = none then
        I.best v (redStep2 s v (redStep1 s v)).1 else none)
    else s.c v

/-- One round: a blue turn followed by a red turn. -/
noncomputable def round (s : State V) : State V := I.redTurn (I.blueTurn s)

/-- The state at the end of round `i` (`run I 0 = init I`). -/
noncomputable def run (i : ℕ) : State V := (I.round)^[i] I.init

lemma run_succ (i : ℕ) : I.run (i + 1) = I.round (I.run i) :=
  Function.iterate_succ_apply' _ _ _

/-! ### `best` -/

lemma best_eq_none {v : V} {S : Finset V} : I.best v S = none ↔ S = ∅ := by
  unfold best; split_ifs with h <;> simp_all [Finset.nonempty_iff_ne_empty]

lemma best_spec {v x : V} {S : Finset V} (h : I.best v S = some x) :
    x ∈ S ∧ ∀ y ∈ S, I.rank v x ≤ I.rank v y := by
  unfold best at h
  split_ifs at h with hS
  cases h; exact (S.exists_min_image (I.rank v) hS).choose_spec

lemma best_mem {v x : V} {S : Finset V} (h : I.best v S = some x) : x ∈ S := (I.best_spec h).1

lemma best_isSome {v : V} {S : Finset V} (h : S.Nonempty) : ∃ x, I.best v S = some x := by
  unfold best; simp [h]

lemma best_eq_some_iff {v x : V} {S : Finset V} (hS : S ⊆ I.N v) :
    I.best v S = some x ↔ x ∈ S ∧ ∀ y ∈ S, I.rank v x ≤ I.rank v y := by
  refine ⟨I.best_spec, fun ⟨hx, hmin⟩ => ?_⟩
  obtain ⟨y, hy⟩ := I.best_isSome (v := v) ⟨x, hx⟩
  obtain ⟨hyS, hymin⟩ := I.best_spec hy
  rw [hy, I.rank_inj (hS hyS) (hS hx) (le_antisymm (hymin x hx) (hmin y hyS))]

end Bicoloured

end Podc.TruncatedGaleShapley
