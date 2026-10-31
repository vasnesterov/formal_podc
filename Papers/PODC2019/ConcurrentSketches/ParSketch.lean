import Papers.PODC2019.ConcurrentSketches.Objects

/-!
# Fast Concurrent Data Sketches (PODC 2019): the algorithm `ParSketch`

The unoptimised generic concurrent algorithm `ParSketch` (Algorithm 2 of the PODC version
without the gray lines; left column of Algorithm 3 of the full version):

```
variables: composable sketch globalS (init empty); constant b;
  for each update thread t_i: sketch localS_i (init empty), counter_i (init 0),
  hint_i (init 1), atomic prop_i (init 1)

propagator (t₀):  while true: for all t_i with prop_i = 0:
    globalS.merge(localS_i); localS_i ← empty sketch; prop_i ← globalS.calcHint()
query(arg):       localCopy ← globalS.snapshot(); return localCopy.query(arg)
update_i(a):      if ¬shouldAdd(hint_i, a) then return
                  counter_i ← counter_i + 1; localS_i.update(a)
                  if counter_i = b then
                    prop_i ← 0; wait until prop_i ≠ 0; hint_i ← prop_i; counter_i ← 0
```

Modelling choices (see `differencies.md`):
* the paper's initial value `1` of `hint_i` and `prop_i` is a parameter `hint₀ : S.Hint`;
* the propagator scans the threads round-robin (`pCheck j` reads `prop_j`; "for all `t_i` with
  `prop_i = 0`"); it is started by the (never-returning) operation `propagate`;
* `globalS.merge(localS_i)` is split into reading `localS_i` and merging the value read into
  `globalS` (only `t₀` accesses `localS_i` at that time);
* `hint_i ← prop_i` uses the value read by the last iteration of the wait loop;
* `shouldAdd(hint_i, a)` (a local computation) is evaluated when `update_i(a)` is invoked.
-/

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

variable (S : Composable) (N : ℕ) (Q : Type)

/-- Base objects of `ParSketch`. -/
inductive PObj (N : ℕ) where
  | glob
  | loc (i : Fin N)
  | prop (i : Fin N)
  deriving DecidableEq

/-- Specifications of the base objects of `ParSketch`. -/
abbrev pobjs : PObj N → ObjSpec
  | .glob => globObj S
  | .loc _ => locObj S
  | .prop _ => regObj (Option S.Hint) none

/-- Local states (program counters with local variables) of all processes of `ParSketch`. -/
inductive PLoc where
  /-- Update thread, idle (`counter = c`, `hint = h`). -/
  | uIdle (c : ℕ) (h : S.Hint)
  /-- Update thread, about to execute `localS_i.update(a)` (counter already `c + 1`). -/
  | uApply (a : S.Elem) (c : ℕ) (h : S.Hint)
  /-- Update thread, about to signal `prop_i ← 0`. -/
  | uSignal (h : S.Hint)
  /-- Update thread, waiting until `prop_i ≠ 0`. -/
  | uWait (h : S.Hint)
  /-- Update thread, about to return. -/
  | uRet (c : ℕ) (h : S.Hint)
  /-- Propagator, not started. -/
  | pIdle
  /-- Propagator, about to read `prop_j`. -/
  | pCheck (j : Fin N)
  /-- Propagator, about to read `localS_j`. -/
  | pRead (j : Fin N)
  /-- Propagator, about to merge the value `s` read from `localS_j` into `globalS`. -/
  | pMerge (j : Fin N) (s : S.State)
  /-- Propagator, about to reset `localS_j`. -/
  | pReset (j : Fin N)
  /-- Propagator, about to compute `globalS.calcHint()`. -/
  | pHint (j : Fin N)
  /-- Propagator, about to write the hint `h` to `prop_j`. -/
  | pSignal (j : Fin N) (h : S.Hint)
  /-- Query thread, idle. -/
  | qIdle
  /-- Query thread, about to take a snapshot of `globalS` for `query(q)`. -/
  | qSnap (q : S.Arg)
  /-- Query thread, about to return `v`. -/
  | qRet (v : S.Val)

variable {S N Q}

/-- The initial local states. -/
def PLoc.init (hint₀ : S.Hint) : Proc N Q → PLoc S N
  | .upd _ => .uIdle 0 hint₀
  | .prop => .pIdle
  | .qry _ => .qIdle

variable [NeZero N]

/-- Invocations. -/
def PLoc.invoke : Proc N Q → PLoc S N → SkOp S.toSketch → PLoc S N
  | .upd _, .uIdle c h, .update a => if S.shouldAdd h a then .uApply a c h else .uRet c h
  | .prop, .pIdle, .propagate => .pCheck 0
  | .qry _, .qIdle, .query q => .qSnap q
  | _, l, _ => l

/-- The next action of a process. -/
def PLoc.act (b : ℕ) : Proc N Q → PLoc S N → Action (seqObj S.toSketch) (pobjs S N) (PLoc S N)
  | .upd i, .uApply a c h =>
      .access (.loc i) (LOp.update a) fun _ => if c + 1 = b then .uSignal h else .uRet (c + 1) h
  | .upd i, .uSignal h => .access (.prop i) (ROp.write none) fun _ => .uWait h
  | .upd i, .uWait h => .access (.prop i) ROp.read fun r =>
      match r with
      | none => .uWait h
      | some h' => .uRet 0 h'
  | .upd _, .uRet c h => .ret .ack (.uIdle c h)
  | .prop, .pCheck j => .access (.prop j) ROp.read fun r =>
      match r with
      | none => .pRead j
      | some _ => .pCheck (j + 1)
  | .prop, .pRead j => .access (.loc j) LOp.read fun r =>
      match r with
      | .state s => .pMerge j s
      | .unit => .pCheck j
  | .prop, .pMerge j s => .access .glob (GOp.merge s) fun _ => .pReset j
  | .prop, .pReset j => .access (.loc j) LOp.reset fun _ => .pHint j
  | .prop, .pHint j => .access .glob GOp.calcHint fun r =>
      match r with
      | .hint h => .pSignal j h
      | _ => .pCheck j
  | .prop, .pSignal j h => .access (.prop j) (ROp.write (some h)) fun _ => .pCheck (j + 1)
  | .qry _, .qSnap q => .access .glob GOp.snapshot fun r =>
      match r with
      | .snap x => .qRet (S.snapQuery x q)
      | _ => .qIdle
  | .qry _, .qRet v => .ret (.val v) .qIdle
  | _, l => .ret .ack l

variable (S N Q) in
/-- **`ParSketch`** with buffer size `b` and initial hint `hint₀` (the paper's `1`). -/
def parSketch (b : ℕ) (hint₀ : S.Hint) :
    Impl (seqObj S.toSketch) (pobjs S N) (Proc N Q) (PLoc S N) where
  memInit
    | .glob => S.init
    | .loc _ => S.init
    | .prop _ => some hint₀
  locInit := PLoc.init hint₀
  invoke := PLoc.invoke
  act := PLoc.act b
  allowed := Proc.allowed

end Podc.ConcurrentSketches
