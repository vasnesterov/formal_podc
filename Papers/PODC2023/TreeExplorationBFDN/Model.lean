import Mathlib
import Cslib.Foundations.Combinatorics.SimpleGraph.RootedTree

/-!
# Collaborative tree exploration and the BFDN algorithm (model)

Cosson, Massoulié, Viennot, *Efficient Collaborative Tree Exploration with Breadth-First
Depth-Next*, PODC 2023 (Brief Announcement), Section 2 and Algorithm 1; full version
arXiv:2301.13307, Section 2 and Algorithm 1.

## Model

* The unknown tree is a `G.RootedTree` `T` (CSLib: root, parent pointers, depths) of a finite
  graph `G`; robots move along tree edges. Edges are identified with their lower endpoint `w ≠ root`
  (the edge `{parent w, w}`), so "the edge to `w` has been traversed" is the same as "`w` has been
  visited". A *dangling* edge is an edge to an unvisited child of a visited node; a visited node
  with a dangling edge is *open*.
* `k` robots start at the root; time is divided into synchronous rounds. In round `t` the robots
  take their decisions sequentially (`for i = 1 to k`, line 5 of Algorithm 1), then all move at
  once (`MOVE`). The paper's complete-communication model is reflected by the fact that the
  decisions may depend on the whole configuration (positions, anchors, explored subtree); the
  decisions of BFDN only use explored information (visited nodes and their children).
* A configuration stores the positions, the anchors `v_i`, the visited set, and a flag `bf i`
  saying whether the stack `S_i` of breadth-first moves of robot `i` is nonempty. The stack itself
  is determined by the position and the anchor (it is the path from the position down to the
  anchor), so it is not stored.
* Ties (which anchor of minimum load, which dangling edge) are resolved arbitrarily: the round
  is a *relation* `Round`, and all results hold for every resolution of ties.
* To also cover the adversarial break-downs of Section 4.2 (Proposition 4.2), a round is
  parametrized by the set `act` of robots allowed to move; blocked robots neither decide nor
  move ("for `i ∈ {i : M^i_t = 1}`"). The model of Theorem 2.1 is `act = univ` in every round.

## Algorithm 1 (BFDN), as formalized in `Round`

For each robot `i` (allowed to move), in the order of indices:
1. if `i` is at the root, `Reanchor`: let `A` be the set of open nodes of minimum depth; if `A`
   is nonempty, the new anchor is a node of `A` minimizing the number of robots `j` whose current
   anchor `v_j` is that node (robots `j < i` already updated in this round), otherwise the root;
   the stack is filled with the path to the anchor (`bf` = anchor is not the root);
2. if the stack is nonempty (`bf`), `BF`: move to the next node on the path to the anchor;
3. otherwise `DN`: move through a dangling edge at the current position that is not selected by
   a robot `j < i`, if any; otherwise move up (stay if at the root).
Then all robots move and the visited set is updated.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (T : G.RootedTree)

/-- `InSub T v w`: `w` lies in the subtree `T(v)` of `v`, i.e. `v` is an ancestor of `w`
(or `w = v`). -/
def InSub (v w : V) : Prop := ∃ n, T.parent^[n] w = v

/-- The next node on the path from `v` down to its descendant `a` (Algorithm 1, procedure `BF`). -/
def towards (v a : V) : V := T.parent^[T.depth a - T.depth v - 1] a

/-- A robot configuration (the state of Algorithm 1 at the start of a round). -/
@[ext]
structure Config (V : Type*) (k : ℕ) where
  /-- Positions `p_i`. -/
  pos : Fin k → V
  /-- Anchors `v_i`. -/
  anchor : Fin k → V
  /-- `bf i`: the stack `S_i` of breadth-first moves is nonempty. -/
  bf : Fin k → Bool
  /-- The visited (explored) nodes. -/
  vis : Finset V

variable {k : ℕ}

/-- The initial configuration: all robots at the root, anchored at the root, empty stacks. -/
def init (k : ℕ) : Config V k where
  pos := fun _ => T.root
  anchor := fun _ => T.root
  bf := fun _ => false
  vis := {T.root}

section Defs

variable [DecidableEq V]

/-- `x` is open in `c`: a visited node with an unvisited child (adjacent to a dangling edge). -/
def IsOpen (c : Config V k) (x : V) : Prop :=
  x ∈ c.vis ∧ ∃ w, w ≠ T.root ∧ T.parent w = x ∧ w ∉ c.vis

/-- `x` is a candidate anchor (the set `A` of procedure `Reanchor`): an open node of minimum
depth. -/
def IsCand (c : Config V k) (x : V) : Prop :=
  IsOpen T c x ∧ ∀ y, IsOpen T c y → T.depth x ≤ T.depth y

/-- The anchor of robot `j` as seen by robot `i` during the sequential decisions of a round:
robots `j < i` have already been re-anchored (to `na j`). -/
def curAnchor (c : Config V k) (na : Fin k → V) (i j : Fin k) : V :=
  if j < i then na j else c.anchor j

/-- The load `#{j : v_j = v}` of a node `v` as seen by robot `i` (line 28 of Algorithm 1). -/
def load (c : Config V k) (na : Fin k → V) (i : Fin k) (v : V) : ℕ :=
  (univ.filter fun j => curAnchor c na i j = v).card

/-- Procedure `Reanchor` for robot `i` (if it is allowed to move and at the root), with result
`na i`; other robots keep their anchor. -/
def ReanchorOK (act : Finset (Fin k)) (c : Config V k) (na : Fin k → V) (i : Fin k) : Prop :=
  if i ∈ act ∧ c.pos i = T.root then
    ((∃ v, IsCand T c v) → IsCand T c (na i) ∧ ∀ v, IsCand T c v → load c na i (na i) ≤ load c na i v)
    ∧ ((¬ ∃ v, IsCand T c v) → na i = T.root)
  else na i = c.anchor i

/-- The stack flag after the (possible) re-anchoring of robot `i` in this round. -/
def bf0 (act : Finset (Fin k)) (c : Config V k) (na : Fin k → V) (i : Fin k) : Bool :=
  if i ∈ act ∧ c.pos i = T.root then decide (na i ≠ T.root) else c.bf i

/-- `w` is a dangling edge at the position of robot `i` not selected by any robot `j < i`. -/
def FreeDangling (c : Config V k) (tgt : Fin k → V) (i : Fin k) (w : V) : Prop :=
  w ≠ T.root ∧ T.parent w = c.pos i ∧ w ∉ c.vis ∧ ∀ j < i, tgt j ≠ w

/-- The move selected by robot `i` (procedures `BF` and `DN`); `tgt i` is its next position. -/
def MoveOK (act : Finset (Fin k)) (c : Config V k) (na tgt : Fin k → V) (i : Fin k) : Prop :=
  if i ∈ act then
    if bf0 T act c na i = true then tgt i = towards T (c.pos i) (na i)
    else
      ((∃ w, FreeDangling T c tgt i w) → FreeDangling T c tgt i (tgt i)) ∧
      ((¬ ∃ w, FreeDangling T c tgt i w) → tgt i = T.parent (c.pos i))
  else tgt i = c.pos i

/-- The configuration after the synchronous `MOVE`. -/
def after (act : Finset (Fin k)) (c : Config V k) (na tgt : Fin k → V) : Config V k where
  pos := tgt
  anchor := na
  bf := fun i => if i ∈ act then (bf0 T act c na i && decide (tgt i ≠ na i)) else c.bf i
  vis := c.vis ∪ univ.image tgt

/-- One round of BFDN with the set `act` of robots allowed to move (all robots in the model of
Theorem 2.1). -/
def Round (act : Finset (Fin k)) (c c' : Config V k) : Prop :=
  ∃ na tgt : Fin k → V, (∀ i, ReanchorOK T act c na i) ∧ (∀ i, MoveOK T act c na tgt i) ∧
    c' = after T act c na tgt

/-- An execution of BFDN: a sequence of configurations starting from `init`, where round `t`
is played with the set `act t` of robots allowed to move. -/
def IsExec (act : ℕ → Finset (Fin k)) (e : ℕ → Config V k) : Prop :=
  e 0 = init T k ∧ ∀ t, Round T (act t) (e t) (e (t + 1))

/-- An execution of BFDN in the synchronous model of Theorem 2.1 (all robots move every
round). -/
def IsSyncExec (e : ℕ → Config V k) : Prop := IsExec T (fun _ => univ) e

/-- Terminal configuration: the tree is fully explored and all robots are back at the root.
This is exactly the configuration at which the main loop of Algorithm 1 (full version:
"while some robot changes position") stops. -/
def Terminal [Fintype V] (c : Config V k) : Prop := c.vis = univ ∧ ∀ i, c.pos i = T.root

end Defs

end Podc.TreeExplorationBFDN
