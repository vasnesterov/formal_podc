import Mathlib

/-!
# The abortable lock of Jayanti and Jayanti (PODC 2019): model

Prasad Jayanti, Siddhartha Jayanti. *Constant Amortized RMR Abortable Mutex for CC and DSM.*
PODC 2019 (full version: arXiv 1809.04561v1, "Constant Amortized RMR Complexity Deterministic
Abortable Mutual Exclusion Algorithm for CC and DSM Models"), Algorithm 1.

```
Shared: sentinel (init token); tail (init &sentinel);
        per process p: node_p (init nil), go_p (init false; in DSM, in p's partition)
Local:  mynode_p (init &node_p), pred_p (init &node_p), v_p
Try(p):   1  if FAS(*mynode_p, nil) ≠ pred_p then
          2      pred_p ← FAS(tail, mynode_p)
          3  v_p ← FAS(*pred_p, &go_p)
             while v_p ≠ token do
                 if v_p ∉ {nil, &go_p} then pred_p ← v_p
          4      else wait till go_p = true
          5           go_p ← false
          6      v_p ← FAS(*pred_p, &go_p)
Exit(p):  7  v_p ← FAS(*mynode_p, token); mynode_p ← pred_p
             if v_p ≠ nil then
          8      *v_p ← true
Abort(p): 9  v_p ← FAS(*pred_p, nil)
             if v_p = token then goto Exit (line 7)
             else if v_p ∉ {nil, &go_p} then pred_p ← v_p
         10  if (v_p ← FAS(*mynode_p, pred_p)) ≠ nil then
         11      *v_p ← true
```

## Model

* `n` processes `Fin n` (the paper allows processes to join at any time; a process that has not
  joined yet is a process that stays in the Remainder section). Asynchronous shared memory, no
  crashes, deterministic algorithm; the scheduler (adversary) is arbitrary.
* Node addresses `Node n = Option (Fin n)`: `none` is `&sentinel`, `some p` is `&node_p`.
  The contents of a node are `Val n`: `nil`, `token`, a node address, or the address `&go_q` of a
  busy-wait flag.
* A step of a process performs one shared-memory operation (the numbered line `pc p`) together with
  all local actions that follow it, as in the paper ("in a single step of the execution, a process
  performs an operation on a single shared variable, but can perform any number of local actions").
  Being at line 1 is being in the Remainder section; being at line 7 is being in the CS (the paper's
  convention in `I10` and Corollary 4.1.1).
* A step is labelled by the process and a Boolean *abort* flag (the environment's abort signal).
  The flag only matters at lines 4, 5, 6 (the paper allows the jump to the Abort section "only after
  performing Line 3, or Line 4, or Line 5, or Line 6"): there an aborting step jumps to the Abort
  section and performs line 9 in the same step (the jump is a local action, merged into the next
  shared-memory operation). Everywhere else the flag is ignored.
* Values that the invariant shows impossible (e.g. `*v_p ← true` with `v_p` not the address of a
  go-flag, or `v_p = &go_q` with `q ≠ p` at line 3) are given some harmless semantics.
-/

namespace Podc.AbortableMutexAmortized

/-- Node addresses: `none` is `&sentinel`, `some p` is `&node_p`. -/
abbrev Node (n : ℕ) := Option (Fin n)

/-- Contents of a node (and values of the local variable `v_p`). -/
inductive Val (n : ℕ) where
  /-- `nil` -/
  | nil
  /-- `token` -/
  | token
  /-- the address of a node -/
  | addr (a : Node n)
  /-- the address `&go_q` of process `q`'s busy-wait flag -/
  | go (q : Fin n)
  deriving DecidableEq

/-- Program counters: the next line (shared-memory operation) to execute. -/
inductive PC where
  | l1 | l2 | l3 | l4 | l5 | l6 | l7 | l8 | l9 | l10 | l11
  deriving DecidableEq, Repr

/-- Configurations: shared variables and local variables of all processes. -/
structure State (n : ℕ) where
  /-- program counters -/
  pc : Fin n → PC
  /-- local `mynode_p` -/
  mynode : Fin n → Node n
  /-- local `pred_p` -/
  pred : Fin n → Node n
  /-- local `v_p` -/
  v : Fin n → Val n
  /-- contents of the nodes (`sentinel` and `node_p`) -/
  node : Node n → Val n
  /-- busy-wait flags `go_p` -/
  go : Fin n → Bool
  /-- shared variable `tail` -/
  tail : Node n

variable {n : ℕ}

/-- The initial configuration. (`v_p` is "arbitrarily initialized"; we pick `nil`, it is never read
before being written.) -/
def init : State n where
  pc _ := .l1
  mynode p := some p
  pred p := some p
  v _ := .nil
  node a := if a = none then .token else .nil
  go _ := false
  tail := none

/-- `pred_p ← v_p` if `v_p` is a node address (the paper's "if `v_p ∉ {nil, &go_p}` then
`pred_p ← v_p`"; the invariant shows that `v_p` is then a node address). -/
def newPred (x : Val n) (a : Node n) : Node n :=
  match x with
  | .addr b => b
  | _ => a

/-- Where the `while` loop goes after reading `v_p` at line 3 or 6. -/
def loopPC (x : Val n) : PC :=
  match x with
  | .token => .l7
  | .addr _ => .l6
  | _ => .l4

/-- Lines 3 and 6: `v_p ← FAS(*pred_p, &go_p)` and the local loop control. -/
def fasPred (s : State n) (p : Fin n) : State n :=
  { s with
    node := Function.update s.node (s.pred p) (.go p)
    v := Function.update s.v p (s.node (s.pred p))
    pred := Function.update s.pred p (newPred (s.node (s.pred p)) (s.pred p))
    pc := Function.update s.pc p (loopPC (s.node (s.pred p))) }

/-- Line 9: `v_p ← FAS(*pred_p, nil)` and the local actions that follow it. -/
def line9 (s : State n) (p : Fin n) : State n :=
  { s with
    node := Function.update s.node (s.pred p) .nil
    v := Function.update s.v p (s.node (s.pred p))
    pred := Function.update s.pred p (newPred (s.node (s.pred p)) (s.pred p))
    pc := Function.update s.pc p (if s.node (s.pred p) = .token then .l7 else .l10) }

/-- Lines 8 and 11: `*v_p ← true`, then return to the Remainder section. -/
def wake (s : State n) (p : Fin n) : State n :=
  { s with
    go := match s.v p with
      | .go q => Function.update s.go q true
      | _ => s.go
    pc := Function.update s.pc p .l1 }

/-- One step of process `p`; `ab` is the abort signal (only used at lines 4, 5, 6). -/
def step (s : State n) (p : Fin n) (ab : Bool) : State n :=
  match s.pc p with
  | .l1 =>
    { s with
      node := Function.update s.node (s.mynode p) .nil
      pc := Function.update s.pc p
        (if s.node (s.mynode p) = .addr (s.pred p) then .l3 else .l2) }
  | .l2 =>
    { s with
      pred := Function.update s.pred p s.tail
      tail := s.mynode p
      pc := Function.update s.pc p .l3 }
  | .l3 => fasPred s p
  | .l4 =>
    if ab then line9 s p
    else if s.go p then { s with pc := Function.update s.pc p .l5 } else s
  | .l5 =>
    if ab then line9 s p
    else { s with go := Function.update s.go p false, pc := Function.update s.pc p .l6 }
  | .l6 => if ab then line9 s p else fasPred s p
  | .l7 =>
    { s with
      node := Function.update s.node (s.mynode p) .token
      v := Function.update s.v p (s.node (s.mynode p))
      mynode := Function.update s.mynode p (s.pred p)
      pc := Function.update s.pc p (if s.node (s.mynode p) = .nil then .l1 else .l8) }
  | .l8 => wake s p
  | .l9 => line9 s p
  | .l10 =>
    { s with
      node := Function.update s.node (s.mynode p) (.addr (s.pred p))
      v := Function.update s.v p (s.node (s.mynode p))
      pc := Function.update s.pc p (if s.node (s.mynode p) = .nil then .l1 else .l11) }
  | .l11 => wake s p

/-- Reachable configurations. -/
inductive Reachable : State n → Prop
  | init : Reachable init
  | step {s : State n} (p : Fin n) (ab : Bool) : Reachable s → Reachable (step s p ab)

/-- The execution determined by a schedule `σ` (every schedule is admissible: `step` is total).
`σ t = (p, ab)`: process `p` takes the `t`-th step, `ab` is the abort signal. -/
def exec (σ : ℕ → Fin n × Bool) : ℕ → State n
  | 0 => init
  | t + 1 => step (exec σ t) (σ t).1 (σ t).2

theorem reachable_exec (σ : ℕ → Fin n × Bool) (t : ℕ) : Reachable (exec σ t) := by
  induction t with
  | zero => exact .init
  | succ t ih => exact .step _ _ ih

/-- The execution of a finite schedule (a list of steps) from a configuration. -/
def run (s : State n) : List (Fin n × Bool) → State n
  | [] => s
  | l :: ls => run (step s l.1 l.2) ls

theorem reachable_run {s : State n} (h : Reachable s) (ls : List (Fin n × Bool)) :
    Reachable (run s ls) := by
  induction ls generalizing s with
  | nil => exact h
  | cons l ls ih => exact ih (.step _ _ h)

/-- The line a step executes (an aborting step at lines 4–6 executes line 9). -/
def lineOf (s : State n) (p : Fin n) (ab : Bool) : PC :=
  match s.pc p with
  | .l4 | .l5 | .l6 => if ab then .l9 else s.pc p
  | l => l

end Podc.AbortableMutexAmortized
