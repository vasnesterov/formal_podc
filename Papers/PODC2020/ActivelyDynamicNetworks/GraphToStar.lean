import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Fin.Basic

/-!
# GraphToStar (Section 3): the committee rules as printed break on a 4-node line

Michail–Skretas–Spirakis, PODC 2020, §3, Algorithm GraphToStar and Lemma 3.1 ("Algorithm
GraphToStar solves Depth-1 Tree").

We model the algorithm at the level of committees and phases, rule by rule as printed:

* every node `x` has a leader `lead x`; committees are the classes `{x | lead x = u}` of leaders
  `u` (`lead u = u`), and IDs are the node names (comparison based, `Fin n` order);
* a leader stores the leader `tgt u` it last activated an edge with (`act u`: it did so in the
  previous phase) and `recv u`: some committee activated an edge with `u` in the previous phase;
* **Selection**: among the neighbouring committees not in pulling mode, if one has a larger ID,
  select the largest one `v` (activate `uv`); enter *merging* if `v` did not select in this phase,
  *pulling* if it did. Otherwise: *termination* if there are no neighbouring committees, *waiting*
  if selected, else stay in selection;
* **Merging**: all nodes of `C(u)` take `tgt u` as their leader (`C(u)` ceases to exist);
* **Pulling**: with `v = tgt u`: if `v` activated an edge with `w = tgt v` in the previous phase,
  jump to `w` (stay pulling); otherwise enter merging;
* **Waiting**: termination if no neighbouring committees; selection if nobody activated an edge
  with `u` in the previous phase; otherwise keep waiting.

Two committees are neighbours if an edge of the initial graph `G_s` joins their members or one
leader activated an edge with the other (`tgt`). Phases are synchronous; all decisions of a phase
are taken on the state at its beginning (`phase`).

**Counterexample** (`lemma_3_1_breaks`): on the line `0 - 1 - 2 - 3` (IDs increasing), in phase 1
every committee selects its right neighbour; `C(2)` pairs with `C(3)` (merging) and `C(0)`, `C(1)`
enter pulling. In phase 2, `C(1)` jumps to `3`, `C(0)` jumps to `2` — but `C(2)` merges into
`C(3)` in the same phase, so `C(0)` now points to node `2`, which is no longer a leader. In phase 3
`C(0)`'s target "did not activate", so `C(0)` enters merging, and in phase 4 it merges into node
`2`, a follower of `3`: node `0`'s leader is `2` and `2`'s leader is `3`. The committees are no
longer stars, the pulling forest is not "TreeToStar on committees" (Lemma 3.1's proof), and the
final network cannot be a spanning star with `0` attached to the centre: GraphToStar as printed
does not solve Depth-1 Tree. On the 3-node line the same rules work (`line3_ok`).
-/

namespace Podc.ActivelyDynamicNetworks.GraphToStar

/-- The modes of a committee. -/
inductive Mode
  | sel | merge | pull | wait | term
  deriving DecidableEq, Repr

/-- Committee-level state of GraphToStar on `n` nodes. -/
structure St (n : ℕ) where
  /-- leader of each node -/
  lead : Fin n → Fin n
  /-- mode of each committee (meaningful for leaders) -/
  mode : Fin n → Mode
  /-- the leader that this leader last activated an edge with -/
  tgt : Fin n → Fin n
  /-- this leader activated an edge with another leader in the previous phase -/
  act : Fin n → Bool
  /-- some committee activated an edge with this leader in the previous phase -/
  recv : Fin n → Bool
  deriving DecidableEq

variable {n : ℕ} (adj : Fin n → Fin n → Bool) (s : St n)

/-- Leaders of committees. -/
def isLeader (u : Fin n) : Bool := s.lead u = u

/-- The leaders of the committees neighbouring the committee of `u`. -/
def nbrs (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun c => isLeader s c ∧ c ≠ u ∧
    ((∃ x y, s.lead x = u ∧ s.lead y = c ∧ adj x y = true) ∨ s.tgt u = c ∨ s.tgt c = u)

/-- The committee that the leader `u` selects in this phase (if it is in selection mode). -/
def selOf (u : Fin n) : Option (Fin n) :=
  if isLeader s u ∧ s.mode u = .sel then
    let cand := (nbrs adj s u).filter fun z => s.mode z ≠ .pull
    if ∃ z ∈ cand, u < z then some (cand.max.getD u) else none
  else none

/-- `u` is selected by some committee in this phase. -/
def selected (u : Fin n) : Bool := decide (∃ c, selOf adj s c = some u)

/-- One synchronous phase of GraphToStar (rules of §3 as printed). -/
def phase : St n where
  lead x :=
    let u := s.lead x
    if isLeader s u ∧ s.mode u = .merge then s.tgt u else u
  mode u :=
    match s.mode u with
    | .sel =>
      match selOf adj s u with
      | some v => if (selOf adj s v).isSome then .pull else .merge
      | none => if nbrs adj s u = ∅ then .term else if selected adj s u = true then .wait else .sel
    | .merge => .merge
    | .pull => if s.act (s.tgt u) then .pull else .merge
    | .wait => if nbrs adj s u = ∅ then .term else if s.recv u = false then .sel else .wait
    | .term => .term
  tgt u :=
    match s.mode u with
    | .sel => (selOf adj s u).getD (s.tgt u)
    | .pull => if s.act (s.tgt u) then s.tgt (s.tgt u) else s.tgt u
    | _ => s.tgt u
  act u :=
    match s.mode u with
    | .sel => (selOf adj s u).isSome
    | .pull => s.act (s.tgt u)
    | _ => false
  recv u := decide (selected adj s u = true ∨
    (∃ c, isLeader s c ∧ s.mode c = .pull ∧ s.act (s.tgt c) = true ∧ s.tgt (s.tgt c) = u) ∨
    (∃ c, isLeader s c ∧ s.mode c = .merge ∧ s.tgt c = u ∧ c ≠ u))

/-- Initially every node is the leader of its own committee, in selection mode. -/
def init (n : ℕ) : St n where
  lead := id
  mode _ := .sel
  tgt := id
  act _ := false
  recv _ := false

/-- The line `0 - 1 - ⋯ - (n-1)` with IDs increasing along the line. -/
def line (n : ℕ) (i j : Fin n) : Bool := i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- Committees are stars centred at their leaders: the leader of a node is a leader. -/
def StarInv (s : St n) : Prop := ∀ x, s.lead (s.lead x) = s.lead x

instance (s : St n) : Decidable (StarInv s) := by unfold StarInv; infer_instance

/-- After phase 2 on the 4-node line, committee `C(0)` points to node `2` (it jumped there), but
`C(2)` has merged into `C(3)` in the same phase: node `2` is no longer a leader. -/
theorem line4_phase2 :
    let s := (phase (line 4))^[2] (init 4)
    s.lead 0 = 0 ∧ s.mode 0 = .pull ∧ s.tgt 0 = 2 ∧ s.lead 2 = 3 := by
  decide

/-- **Lemma 3.1 as printed fails**: after 4 phases on the 4-node line with increasing IDs, node
`0` has joined the "committee" of node `2`, which is itself a follower of `3`. The committees are
no longer stars, and node `0` is at distance two from the only leader `3`. -/
theorem lemma_3_1_breaks :
    let s := (phase (line 4))^[4] (init 4)
    s.lead 0 = 2 ∧ s.lead 2 = 3 ∧ s.lead 3 = 3 ∧ ¬ StarInv s := by
  decide +kernel

/-- **The run terminates with a wrong committee.** After 5 phases on the 4-node line, `3` is the
only leader and `C(3)` has entered the termination mode, but node `0` still has the follower `2`
as its leader and its only link to the committee is `2` (`tgt 0 = 2`): no rule ever connects `0`
to `3`, so the termination phase cannot leave a spanning star centred at `3`. Leaders and modes
no longer change. -/
theorem line4_terminates_wrong :
    let s := (phase (line 4))^[5] (init 4)
    s.mode 3 = .term ∧ (∀ c, s.lead c = c → c = 3) ∧ s.lead 0 = 2 ∧ s.tgt 0 = 2 ∧
      (phase (line 4) s).lead = s.lead ∧ (phase (line 4) s).mode = s.mode := by
  decide +kernel

/-- The star invariant holds throughout phases 0–3 and is first broken in phase 4. -/
theorem line4_inv_before : ∀ k < 4, StarInv ((phase (line 4))^[k] (init 4)) := by
  decide

/-- Sanity check of the model: on the 3-node line the rules work, every node ends in the
committee of `2` and that committee terminates. -/
theorem line3_ok :
    let s := (phase (line 3))^[6] (init 3)
    (∀ x, s.lead x = 2) ∧ s.mode 2 = .term := by
  decide +kernel

end Podc.ActivelyDynamicNetworks.GraphToStar
