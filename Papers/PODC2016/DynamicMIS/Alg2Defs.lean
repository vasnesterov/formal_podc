import Papers.PODC2016.DynamicMIS.Theorem1

/-!
# Algorithm 2 (Section 4): the constant-broadcast implementation — model

Synchronous broadcast model. Every node knows the ranks (random IDs) of its neighbours and their
current states (a node broadcasts its new state whenever it changes, and neighbours receive it
before the next round). One round: every participating node computes its new state from its own
state and its neighbours' states at the end of the previous round.

States (`St`): `inM` (`M`), `outM` (`M̄`), `changing a` (`C`, entered `a` rounds ago: `a = 0` means
"changed to `C` in the previous round", which is what neighbours react to), `ready` (`R`).

Rules of Algorithm 2 for node `v` (`I(v)` = participating neighbours with smaller rank):
1. `v ∈ M`: if some `u ∈ I(v)` changed to `C`, change to `C`.
2. `v ∈ M̄`: if some `u ∈ I(v)` changed to `C` and no `w ∈ I(v)` is in `M`, change to `C`.
3. `v ∈ C`: if no higher-ranked neighbour is in `C` and `v` changed to `C` at least 2 rounds ago,
   change to `R`.
4. `v ∈ R`: if all `u ∈ I(v)` are in `M` or `M̄`, change to `M` if all of them are in `M̄` (and `v`
   is an active node), to `M̄` otherwise.

A `Net` fixes the graph, the participating nodes (the communication network), the *active* nodes
(nodes that may join the MIS: a gracefully deleted node still participates until stabilisation but
must end in `M̄`) and the ranks.
-/

open Finset SimpleGraph

namespace DynamicMIS

namespace Alg2

/-- Node states of Algorithm 2. -/
inductive St
  /-- `M`: in the MIS. -/
  | inM
  /-- `M̄`: not in the MIS. -/
  | outM
  /-- `C`, entered `age` rounds ago. -/
  | changing (age : ℕ)
  /-- `R`: ready to change. -/
  | ready
  deriving DecidableEq

/-- The broadcast-visible class of a state (the age of `C` is local). -/
def St.cls : St → Fin 4
  | .inM => 0
  | .outM => 1
  | .changing _ => 2
  | .ready => 3

/-- `s` is a `C` state. -/
def St.IsChanging : St → Prop
  | .changing _ => True
  | _ => False

/-- `s` is `M` or `M̄`. -/
def St.IsFinal : St → Prop
  | .inM | .outM => True
  | _ => False

variable {V : Type*}

/-- The network on which Algorithm 2 runs. -/
structure Net (V : Type*) where
  /-- The communication graph. -/
  graph : SimpleGraph V
  /-- Participating nodes. -/
  part : Set V
  /-- Active nodes (allowed to be in the MIS). -/
  active : Set V
  /-- Ranks (the random order). -/
  rank : V → ℕ

namespace Net

/-- `w ∈ I(v)`: a participating neighbour with smaller rank. -/
def Pred (N : Net V) (w v : V) : Prop := N.graph.Adj w v ∧ w ∈ N.part ∧ N.rank w < N.rank v

/-- A participating neighbour with larger rank. -/
def Higher (N : Net V) (w v : V) : Prop := N.graph.Adj w v ∧ w ∈ N.part ∧ N.rank v < N.rank w

end Net

open Classical in
/-- One synchronous round of Algorithm 2 (non-participating nodes keep their state). -/
noncomputable def step (N : Net V) (c : V → St) (v : V) : St :=
  if v ∉ N.part then c v else
  match c v with
  | .inM => if ∃ u, N.Pred u v ∧ c u = .changing 0 then .changing 0 else .inM
  | .outM =>
    if (∃ u, N.Pred u v ∧ c u = .changing 0) ∧ (∀ u, N.Pred u v → c u ≠ .inM) then .changing 0
    else .outM
  | .changing a =>
    if 1 ≤ a ∧ ∀ u, N.Higher u v → ¬ (c u).IsChanging then .ready else .changing (a + 1)
  | .ready =>
    if ∀ u, N.Pred u v → (c u).IsFinal then
      (if v ∈ N.active ∧ ∀ u, N.Pred u v → c u = .outM then .inM else .outM)
    else .ready

/-- The configuration after `t` rounds. -/
noncomputable def run (N : Net V) (c₀ : V → St) : ℕ → V → St
  | 0 => c₀
  | t + 1 => step N (run N c₀ t)

/-- Number of broadcasts in round `t + 1` (nodes whose visible state changes). -/
noncomputable def broadcastsAt [Fintype V] (N : Net V) (c₀ : V → St) (t : ℕ) : ℕ :=
  open Classical in
  #{v | (run N c₀ (t + 1) v).cls ≠ (run N c₀ t v).cls}

/-- The configuration has stabilised at round `T`: nothing changes from then on. -/
def StableFrom (N : Net V) (c₀ : V → St) (T : ℕ) : Prop := ∀ t, T ≤ t → run N c₀ t = run N c₀ T

/-- States encoding a set `s` of MIS nodes. -/
noncomputable def ofSet (s : Set V) : V → St := open Classical in fun v => if v ∈ s then .inM else .outM

/-! ### The two kinds of initial configurations -/

variable [DecidableEq V]

/-- The network after a non-abrupt change `c` (edge insertion/deletion, graceful node deletion,
node unmuting): the new graph, all nodes of the old or new network participate, the new nodes are
active. -/
def netOf (c : Change V) (cfg : Config V) (r : V → ℕ) : Net V :=
  ⟨(c.apply cfg).graph, c.baseNodes cfg, (c.apply cfg).nodes, r⟩

open Classical in
/-- Initial configuration after a non-abrupt change: the old (greedy) states, except that `v*`
changes to `C` if the MIS invariant fails at `v*`. -/
noncomputable def initOf (c : Change V) (cfg : Config V) (r : V → ℕ) : V → St :=
  fun v =>
    if v = c.vStar r ∧ ¬ InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r
        (cfg.graph.greedyMIS cfg.nodes r) (c.vStar r) then .changing 0
    else ofSet (cfg.graph.greedyMIS cfg.nodes r) v

/-- The network after the abrupt deletion of `x`: `x` disappears immediately. -/
def netAbrupt (x : V) (cfg : Config V) (r : V → ℕ) : Net V :=
  ⟨cfg.graph, cfg.nodes \ {x}, cfg.nodes \ {x}, r⟩

open Classical in
/-- Initial configuration after the abrupt deletion of `x` (Section 4.2): the old states, except
that the nodes `v₁*, …, v_k*` of the first layer `S_1` (computed in the old graph from `S_0 = {x}`)
change to `C` — if `x` was in the MIS (otherwise nothing has to change). -/
noncomputable def initAbrupt (x : V) (cfg : Config V) (r : V → ℕ) : V → St :=
  fun v =>
    if x ∈ cfg.graph.greedyMIS cfg.nodes r ∧ v ≠ x ∧
        v ∈ layer cfg.graph cfg.nodes r (cfg.graph.greedyMIS cfg.nodes r) x 1 then .changing 0
    else ofSet (cfg.graph.greedyMIS cfg.nodes r) v

end Alg2

end DynamicMIS
