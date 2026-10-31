import Papers.PODC2019.ConcurrentSketches.Objects

/-!
# Fast Concurrent Data Sketches (PODC 2019): the algorithm `OptParSketch`

The optimised generic concurrent algorithm `OptParSketch` (Algorithm 2 of the PODC version with
the gray lines and without line 124; right column of Algorithm 3 of the full version), which uses
two local sketches per update thread (double buffering):

```
variables: composable sketch globalS (init empty); constant b;
  for each update thread t_i: sketch localS_i[2] (init empty), cur_i (init 0),
  counter_i (init 0), hint_i (init 1), atomic prop_i (init 1)

propagator (t₀):  while true: for all t_i with prop_i = 0:
    globalS.merge(localS_i[1 - cur_i]); localS_i[1 - cur_i] ← empty sketch;
    prop_i ← globalS.calcHint()
query(arg):       localCopy ← globalS.snapshot(); return localCopy.query(arg)
update_i(a):      if ¬shouldAdd(hint_i, a) then return
                  counter_i ← counter_i + 1; localS_i[cur_i].update(a)
                  if counter_i = b then
                    wait until prop_i ≠ 0; cur_i ← 1 - cur_i; hint_i ← prop_i;
                    counter_i ← 0; prop_i ← 0
```

Modelling choices (in addition to those of `ParSketch`): `cur_i` is a shared register (`cur i`),
written only by `t_i` (which keeps a local copy) and read by the propagator; the indices `0, 1`
are `false, true` (`1 - cur` is `!cur`); lines `cur_i ← 1 - cur_i; hint_i ← prop_i;
counter_i ← 0` are one step (the write to `cur_i`; the other two are local, and `prop_i`
cannot change while it is non-zero).
-/

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

variable (S : Composable) (N : ℕ) (Q : Type)

/-- Base objects of `OptParSketch`. -/
inductive OObj (N : ℕ) where
  | glob
  | loc (i : Fin N) (k : Bool)
  | prop (i : Fin N)
  | cur (i : Fin N)
  deriving DecidableEq

/-- Specifications of the base objects of `OptParSketch`. -/
abbrev oobjs : OObj N → ObjSpec
  | .glob => globObj S
  | .loc _ _ => locObj S
  | .prop _ => regObj (Option S.Hint) none
  | .cur _ => regObj Bool false

/-- Local states of all processes of `OptParSketch`. -/
inductive OLoc where
  /-- Update thread, idle (`cur_i = cur`, `counter = c`, `hint = h`). -/
  | oIdle (cur : Bool) (c : ℕ) (h : S.Hint)
  /-- Update thread, about to execute `localS_i[cur].update(a)` (counter already `c + 1`). -/
  | oApply (a : S.Elem) (cur : Bool) (c : ℕ) (h : S.Hint)
  /-- Update thread, waiting until `prop_i ≠ 0`. -/
  | oWait (cur : Bool) (h : S.Hint)
  /-- Update thread, about to flip `cur_i` (it read the hint `h` from `prop_i`). -/
  | oFlip (cur : Bool) (h : S.Hint)
  /-- Update thread, about to signal `prop_i ← 0` (`cur` is the new value of `cur_i`). -/
  | oSignal (cur : Bool) (h : S.Hint)
  /-- Update thread, about to return. -/
  | oRet (cur : Bool) (c : ℕ) (h : S.Hint)
  /-- Propagator, not started. -/
  | pIdle
  /-- Propagator, about to read `prop_j`. -/
  | pCheck (j : Fin N)
  /-- Propagator, about to read `cur_j`. -/
  | pCur (j : Fin N)
  /-- Propagator, about to read `localS_j[k]`. -/
  | pRead (j : Fin N) (k : Bool)
  /-- Propagator, about to merge the value `s` read from `localS_j[k]` into `globalS`. -/
  | pMerge (j : Fin N) (k : Bool) (s : S.State)
  /-- Propagator, about to reset `localS_j[k]`. -/
  | pReset (j : Fin N) (k : Bool)
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
def OLoc.init (hint₀ : S.Hint) : Proc N Q → OLoc S N
  | .upd _ => .oIdle false 0 hint₀
  | .prop => .pIdle
  | .qry _ => .qIdle

variable [NeZero N]

/-- Invocations. -/
def OLoc.invoke : Proc N Q → OLoc S N → SkOp S.toSketch → OLoc S N
  | .upd _, .oIdle cur c h, .update a => if S.shouldAdd h a then .oApply a cur c h else .oRet cur c h
  | .prop, .pIdle, .propagate => .pCheck 0
  | .qry _, .qIdle, .query q => .qSnap q
  | _, l, _ => l

/-- The next action of a process. -/
def OLoc.act (b : ℕ) : Proc N Q → OLoc S N → Action (seqObj S.toSketch) (oobjs S N) (OLoc S N)
  | .upd i, .oApply a cur c h =>
      .access (.loc i cur) (LOp.update a) fun _ =>
        if c + 1 = b then .oWait cur h else .oRet cur (c + 1) h
  | .upd i, .oWait cur h => .access (.prop i) ROp.read fun r =>
      match r with
      | none => .oWait cur h
      | some h' => .oFlip cur h'
  | .upd i, .oFlip cur h => .access (.cur i) (ROp.write (!cur)) fun _ => .oSignal (!cur) h
  | .upd i, .oSignal cur h => .access (.prop i) (ROp.write none) fun _ => .oRet cur 0 h
  | .upd _, .oRet cur c h => .ret .ack (.oIdle cur c h)
  | .prop, .pCheck j => .access (.prop j) ROp.read fun r =>
      match r with
      | none => .pCur j
      | some _ => .pCheck (j + 1)
  | .prop, .pCur j => .access (.cur j) ROp.read fun v => .pRead j (!v)
  | .prop, .pRead j k => .access (.loc j k) LOp.read fun r =>
      match r with
      | .state s => .pMerge j k s
      | .unit => .pCheck j
  | .prop, .pMerge j k s => .access .glob (GOp.merge s) fun _ => .pReset j k
  | .prop, .pReset j k => .access (.loc j k) LOp.reset fun _ => .pHint j
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
/-- **`OptParSketch`** with buffer size `b` and initial hint `hint₀` (the paper's `1`). -/
def optParSketch (b : ℕ) (hint₀ : S.Hint) :
    Impl (seqObj S.toSketch) (oobjs S N) (Proc N Q) (OLoc S N) where
  memInit
    | .glob => S.init
    | .loc _ _ => S.init
    | .prop _ => some hint₀
    | .cur _ => false
  locInit := OLoc.init hint₀
  invoke := OLoc.invoke
  act := OLoc.act b
  allowed := Proc.allowed

end Podc.ConcurrentSketches
