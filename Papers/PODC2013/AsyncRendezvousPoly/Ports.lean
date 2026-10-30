import Mathlib
import Cslib.Computability.Distributed.PortNumbering.Basic

/-!
# Port-labelled graphs and deterministic exploration procedures

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), Section 2.

The network is a simple connected port-labelled graph (CSLib `PNGraph` with `IsSimple`): node `v`
has ports `0, …, deg v - 1`, and `G.nbr v q` is the neighbour behind port `q` (the paper's
`succ(v, q)`), `G.rport v q` the port number of that edge at the other end.

An agent moving in the graph sees, at each node it reaches, the degree of the node and the port by
which it entered. A deterministic exploration procedure (such as Reingold's procedure based on a
universal exploration sequence, `R(k, ·)` in the paper) is therefore a function `A` from the
*history of observations* (list of pairs `(degree, entry port)`, the first pair being
`(deg v, 0)` at the start node `v`) to the next exit port (taken modulo the current degree). This is
the most general deterministic agent with unbounded memory that only uses what it sees. A
procedure is run for a fixed number of steps.

* `obsRun G A v t`: node and observation history after `t` steps from `v`.
* `walk G A v t`: the node reached after `t` steps (the trajectory `(u₁, u₂, …)` of the paper,
  shifted to start at index `0`).
* `Explores A L`: from any node of any simple connected port-labelled graph with at most `k` nodes
  the first `L` steps visit every node (stated for a given size bound in `ExploresUpTo`).
-/

namespace Podc.AsyncRendezvousPoly

open Cslib.PortNumbering

/-- A deterministic exploration procedure: next exit port as a function of the history of
observations `(degree, entry port)` (oldest first). The port is taken modulo the current degree. -/
abbrev Proc := List (ℕ × ℕ) → ℕ

variable {V : Type*}

/-- Node and observation history after `t` steps of procedure `A` started at `v`. -/
def obsRun (G : PNGraph V) (A : Proc) (v : V) : ℕ → V × List (ℕ × ℕ)
  | 0 => (v, [(G.deg v, 0)])
  | t + 1 =>
    let s := obsRun G A v t
    let q := A s.2 % G.deg s.1
    (G.nbr s.1 q, s.2 ++ [(G.deg (G.nbr s.1 q), G.rport s.1 q)])

/-- The node visited after `t` steps of procedure `A` started at `v`. -/
def walk (G : PNGraph V) (A : Proc) (v : V) (t : ℕ) : V := (obsRun G A v t).1

/-- The exit port used in step `t + 1`. -/
def exitPort (G : PNGraph V) (A : Proc) (v : V) (t : ℕ) : ℕ :=
  A (obsRun G A v t).2 % G.deg (walk G A v t)

theorem walk_zero (G : PNGraph V) (A : Proc) (v : V) : walk G A v 0 = v := rfl

theorem walk_succ (G : PNGraph V) (A : Proc) (v : V) (t : ℕ) :
    walk G A v (t + 1) = G.nbr (walk G A v t) (exitPort G A v t) := rfl

/-- Procedure `A`, run for `L` steps, visits all nodes of every simple connected port-labelled
graph with at most `k` nodes, from every starting node. -/
def ExploresUpTo (A : Proc) (L k : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] (H : PNGraph W), H.IsSimple → H.toSimpleGraph.Connected →
    Fintype.card W ≤ k → ∀ w x : W, ∃ t ≤ L, walk H A w t = x

end Podc.AsyncRendezvousPoly
