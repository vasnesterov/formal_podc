import Papers.PODC2026.ForgetIT.Defs

/-!
# Forget-IT as an asynchronous transition system

The global state records the local states of the processes, the set of messages ever broadcast
by correct processes (`sent`, as `(sender, message)` pairs) and all decision events
(`(process, view, value)`). A step is one of:

* `act`: a correct process executes an enabled rule of Algorithms 1–3 (`En`, `exec`);
* `vol`: a correct process changes its *volatile* state: it receives any message broadcast by a
  correct process or any message from a faulty process, and it may forget received messages and
  accepted `vote-2` messages (this covers message delivery, and the loss of volatile state in a
  crash; a crash is `vol` with empty volatile state followed by the `recover` rule);
* `aux`: a correct process changes the bookkeeping fields used only by the timed implementation
  (`clk`, `entered`, `active`, `out`).

There are no timing constraints at all, and timers may fire at any time, so every execution of
the paper's model (partial synchrony, unreliable channels, crash–recovery of correct processes
before GST, constant persistent memory) is an execution of this system, as far as the actions
of correct processes are concerned. Safety proved here therefore holds in the paper's model.

Persistent memory is modelled with unbounded arrays indexed by views instead of the paper's
window of three views (line 18); every rule only reads views in the window
(`view_i − 2 ≤ V ≤ view_i`) or sets the guard of the view it enters, and views only grow, so
forgotten entries would never be read again.
-/

namespace Podc.ForgetIT

variable {P Val : Type} [Fintype P] [DecidableEq P] [DecidableEq Val]

/-- Global state. -/
structure GS (P Val : Type) where
  loc : P → LS P Val
  sent : Set (P × Msg Val)
  dec : Set (P × ℕ × Val)

/-- Decision events produced by a rule. -/
def decEv (p : P) (s : LS P Val) : Act P Val → Set (P × ℕ × Val)
  | .decide v => {(p, s.view, v)}
  | _ => ∅

/-- Correct process `p` executes rule `a`. -/
def GS.act (prm : Params P) (g : GS P Val) (p : P) (a : Act P Val) : GS P Val where
  loc := Function.update g.loc p (exec prm p a (g.loc p)).1
  sent := g.sent ∪ {e | e.1 = p ∧ e.2 ∈ (exec prm p a (g.loc p)).2}
  dec := g.dec ∪ decEv p (g.loc p) a

/-- Replace the local state of `p`. -/
def GS.setLoc (g : GS P Val) (p : P) (s : LS P Val) : GS P Val :=
  { g with loc := Function.update g.loc p s }

/-- Steps of the system, with faulty set `F`. -/
inductive Step (prm : Params P) (F : Finset P) : GS P Val → GS P Val → Prop
  | act {g : GS P Val} (p : P) (a : Act P Val) (hp : p ∉ F) (hen : En prm p a (g.loc p)) :
      Step prm F g (g.act prm p a)
  | vol {g : GS P Val} (p : P) (hp : p ∉ F) (rcv : List (P × Msg Val))
      (acc : ℕ → P → Option (Option Val × Option (GV Val)))
      (hrcv : ∀ e ∈ rcv, e ∈ (g.loc p).rcv ∨ e.1 ∈ F ∨ e ∈ g.sent)
      (hacc : ∀ V q, acc V q = none ∨ acc V q = (g.loc p).acc V q) :
      Step prm F g (g.setLoc p { g.loc p with rcv := rcv, acc := acc })
  | aux {g : GS P Val} (p : P) (hp : p ∉ F) (clk entered : ℕ) (active : Bool)
      (out : List (Msg Val)) :
      Step prm F g (g.setLoc p { g.loc p with clk := clk, entered := entered, active := active,
                                              out := out })

/-- Initial global state for proposals `inp`. -/
def initGS (prm : Params P) (F : Finset P) (inp : P → Val) : GS P Val where
  loc p := initLS prm p (inp p)
  sent := {e | e.1 ∉ F ∧ e.2 ∈ (initR prm e.1 (inp e.1)).2}
  dec := ∅

/-- Reachable global states. -/
def Reach (prm : Params P) (F : Finset P) (inp : P → Val) : GS P Val → Prop :=
  Relation.ReflTransGen (Step prm F) (initGS prm F inp)

end Podc.ForgetIT
