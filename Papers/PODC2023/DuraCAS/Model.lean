import Mathlib

/-!
# DuraCAS over DurEC over hardware CAS: the concrete model

Prasad Jayanti, Siddhartha Jayanti, Sucharita Jayanti. *Brief Announcement: Efficient Recoverable
Writable-CAS.* PODC 2023 (Algorithms 1 and 2); full version *Durable Algorithms for Writable LL/SC
and CAS with Dynamic Joining*, arXiv:2302.00135v1 (Algorithms 1 and 4, Appendix A).

```
DurEC (handle h = record {DetVal, Val};  object = hardware CAS words X = (hndl, seq), Y = (seq, val))
  ECLL(h):        4  return Y
  ECSC(h, s, v):  6  if Y.seq ≠ s then return false      7  h.Val ← v      8  ĥ ← X.hndl
                  9  ŝ ← max(h.DetVal, s) + 1           10  r ← CAS(X, (ĥ, s), (h, ŝ))
                 11  FORWARD(h)                         12  return r
  FORWARD(h):    13  x ← X     14  ŝ ← x.hndl.DetVal     15  if ŝ < x.seq then CAS(x.hndl.DetVal, ŝ, x.seq)
                 16  v̂ ← x.hndl.Val     17  y ← Y        18  if y.seq < x.seq then CAS(Y, y, (x.seq, v̂))
  RECOVER(h):    20  FORWARD(h)                         DETECT(h): 22 return (h.DetVal, true)

DuraCAS (handle h = {Critical, Casual : DurEC handles};  object = DurEC objects W, Z holding (val, bit))
  READ(h):        4  z ← Z.ECLL(h.Casual)   5  return z.val
  CAS(h,old,new): 6  for i ← 1 to 2
                  7    z ← Z.ECLL(h.Casual)
                  8    if z.val ≠ old then return false else if old = new then return true
                  9    TRANSFER-WRITE(h)
                 10    if Z.ECSC(h.Critical, z.seq, (new, z.bit)) then return true
                 11  return false
  WRITE(h, v):   12  w ← W.ECLL(h.Casual)   13  z ← Z.ECLL(h.Casual)   14 if z.val = v then return ack
                 15  if z.bit = w.bit then W.ECSC(h.Critical, w.seq, (v, 1 − w.bit))
                 16  TRANSFER-WRITE(h)      17  TRANSFER-WRITE(h)      18 return ack
  TRANSFER-WRITE(h): 19 ẑ ← Z.ECLL(h.Casual)   20 ŵ ← W.ECLL(h.Casual)
                     21 if ẑ.bit ≠ ŵ.bit then Z.ECSC(h.Casual, ẑ.seq, (ŵ.val, ŵ.bit))
  RECOVER(h):    22 W.RECOVER(h.Critical) 23 Z.RECOVER(h.Critical) 24 W.RECOVER(h.Casual)
                 25 Z.RECOVER(h.Casual)   26 TRANSFER-WRITE(h)     27 TRANSFER-WRITE(h)
  DETECT(h):     28 return DurEC.DETECT(h.Critical)
```
(Line numbers of DuraCAS are those of the brief announcement; the full version numbers the lines of
`WRITE` 12, 13, 13*, 14–17, of `TRANSFER-WRITE` 18–20 and of `RECOVER` 21–26.)

## Model

* Asynchronous shared memory (NVM) with individual crash–restart failures: any process may crash at
  any time, any number of times; a crash erases the process's local state (program counter and
  local variables), shared memory is unaffected.
* Processes form an arbitrary type `P` (dynamic joining: no bound on the number of processes; the
  handles `(p, crit)`, `(p, cas)` of process `p` exist from the start with `DetVal = 0` — creating
  a handle is pure allocation). DuraCAS objects form an arbitrary type `K` (each with its two DurEC
  objects `(k, W)` and `(k, Z)`), values an arbitrary type `V`.
* **The DurEC code is inlined**: every step of a process executes exactly one hardware operation
  (read or CAS of `X`, `Y`, a `DetVal` or a `Val` field) of the DurEC algorithm, together with
  the local computation that follows it (DuraCAS-level bookkeeping included). A call of `ECLL` is a
  single read of `Y`; a call of `ECSC` starts with line 6 and a call of `RECOVER` with line 13.
* The `Val` fields are arbitrarily initialised (`hv0`), as in the paper.
* `x.hndl = null` (no install yet) in `FORWARD`: the paper dereferences the null pointer at
  lines 14 and 16. We use the evident fix "if `x.hndl = null` then return" (then `x.seq = 0` and
  the `if` at line 18 is false anyway).
* Every process runs a *most general client*: when idle it may invoke any operation on any object.
  A crash of a busy process restarts it at line 22 of `RECOVER` of the object of its pending
  operation; the operation ends (event `rdone`) when `RECOVER` completes. This is the
  **per-process** recovery discipline (the process recovers before invoking anything else). The
  brief announcement allows the weaker **per-object** discipline (recover `O` before the next
  operation on `O`); it is modelled by `StepPO` and refuted in `Counterexample.lean`.
* The history records invocations (with the value `d₁` returned by `DETECT` just before),
  responses and recovery completions (with `d₂` returned by `DETECT` just after) and crashes.
-/

namespace Podc.DuraCAS

/-- The two DurEC handles of a DuraCAS handle. -/
inductive Kind where
  | crit
  | cas
  deriving DecidableEq, Repr

/-- The two DurEC objects of a DuraCAS object. -/
inductive WZ where
  | W
  | Z
  deriving DecidableEq, Repr

/-- DuraCAS operations. -/
inductive Op (V : Type) where
  | read
  | cas (old new : V)
  | write (v : V)
  deriving DecidableEq, Repr

/-- Responses (`WRITE` returns `ack`, written `ok true`). -/
inductive Resp (V : Type) where
  | val (v : V)
  | ok (b : Bool)
  deriving DecidableEq, Repr

variable (P K V : Type)

/-- DurEC handles. -/
abbrev Hd := P × Kind
/-- DurEC objects. -/
abbrev Obj := K × WZ
/-- Content of a DurEC object: `(seq, (val, bit))`. -/
abbrev Cell := ℕ × (V × Bool)

/-- Shared memory (NVM). -/
structure Mem where
  /-- hardware word `X = (hndl, seq)` of each DurEC object (`none` = null) -/
  X : Obj K → Option (Hd P) × ℕ
  /-- hardware word `Y = (seq, val)` of each DurEC object -/
  Y : Obj K → Cell V
  /-- `DetVal` field of each DurEC handle -/
  det : Hd P → ℕ
  /-- `Val` field of each DurEC handle -/
  hval : Hd P → V × Bool

/-- Program counter inside a DurEC procedure (with local variables). -/
inductive FPc where
  /-- line 7 (`h.Val ← v`) -/
  | l7
  /-- line 8 (`ĥ ← X.hndl`) -/
  | l8
  /-- line 9 (`ŝ ← max(h.DetVal, s) + 1`) -/
  | l9 (hh : Option (Hd P))
  /-- line 10 (`CAS(X, (ĥ, s), (h, ŝ))`) -/
  | l10 (hh : Option (Hd P))
  /-- line 13 (`x ← X`) -/
  | f13
  /-- line 14 (`ŝ ← x.hndl.DetVal`) -/
  | f14 (x : Option (Hd P) × ℕ)
  /-- line 15, with `x = (g, e)` (non-null) and `ŝ = d` -/
  | f15 (g : Hd P) (e d : ℕ)
  /-- line 16 -/
  | f16 (g : Hd P) (e : ℕ)
  /-- line 17 -/
  | f17 (g : Hd P) (e : ℕ) (vh : V × Bool)
  /-- line 18 -/
  | f18 (g : Hd P) (e : ℕ) (vh : V × Bool) (y : Cell V)
  deriving DecidableEq

/-- Kind of an active DurEC call. -/
inductive FKind where
  | sc
  | recov
  deriving DecidableEq, Repr

/-- An active DurEC call (`ECSC` after line 6, or `RECOVER`). -/
structure Frame where
  kind : FKind
  o : Obj K
  h : Hd P
  /-- the context argument `s` of `ECSC` -/
  s : ℕ
  /-- the value argument `v` of `ECSC` -/
  v : V × Bool
  /-- the local `ŝ` computed at line 9 -/
  sh : ℕ
  /-- the result `r` of the CAS at line 10 -/
  r : Bool
  pc : FPc P V
  deriving DecidableEq

/-- Return addresses of `TRANSFER-WRITE`. -/
inductive Ret where
  /-- line 9 of `CAS` in iteration `i` (`false` = first), with `z` read at line 7 -/
  | casT (i : Bool) (z : Cell V)
  /-- line 16 of `WRITE` -/
  | wr1
  /-- line 17 of `WRITE` -/
  | wr2
  /-- line 26 of `RECOVER` -/
  | rec1
  /-- line 27 of `RECOVER` -/
  | rec2
  deriving DecidableEq

/-- DuraCAS program counters (the next DuraCAS-level line, with local variables). -/
inductive Pc where
  | idle
  /-- line 4 -/
  | read
  /-- line 7, iteration `i` (`false` = first) -/
  | cas7 (i : Bool)
  /-- line 10, iteration `i`, with `z` read at line 7 -/
  | cas10 (i : Bool) (z : Cell V)
  /-- line 12 -/
  | wr12
  /-- line 13, with `w` read at line 12 -/
  | wr13 (w : Cell V)
  /-- line 15 (the `ECSC` on `W`), with `w` -/
  | wr15 (w : Cell V)
  /-- line 19 of `TRANSFER-WRITE` -/
  | tw19 (ret : Ret V)
  /-- line 20, with `ẑ` -/
  | tw20 (ret : Ret V) (zh : Cell V)
  /-- line 21 (the `ECSC` on `Z`), with `ẑ`, `ŵ` -/
  | tw21 (ret : Ret V) (zh wh : Cell V)
  /-- lines 22–25 of `RECOVER` (`j = 0, 1, 2, 3`) -/
  | recv (j : Fin 4)
  deriving DecidableEq

/-- The operation a process is executing (or recovering). `id` and `d1` are bookkeeping for the
history; the algorithm uses only `k` and `op`. -/
structure OpRec where
  id : ℕ
  k : K
  op : Op V
  d1 : ℕ
  deriving DecidableEq

/-- Local state of a process. -/
structure PState where
  pc : Pc V
  fr : Option (Frame P K V)
  op : Option (OpRec K V)

/-- History events. `d` is the value returned by `DETECT` at that moment. -/
inductive Ev where
  | inv (id : ℕ) (p : P) (k : K) (op : Op V) (d : ℕ)
  | ret (id : ℕ) (r : Resp V) (d : ℕ)
  | crash (p : P)
  | rdone (id : ℕ) (d : ℕ)
  deriving DecidableEq

/-- Global state. -/
structure St where
  m : Mem P K V
  ps : P → PState P K V
  hist : List (Ev P K V)
  nid : ℕ

variable {P K V}
variable [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- Result of one step of a DurEC call. -/
inductive FRes (P K V : Type) where
  | cont (f : Frame P K V)
  | done (r : Bool)

/-- One atomic step of an active DurEC call (lines 7–10 and 13–18). -/
def fstep (m : Mem P K V) (f : Frame P K V) : Mem P K V × FRes P K V :=
  match f.pc with
  | .l7 => ({ m with hval := Function.update m.hval f.h f.v }, .cont { f with pc := .l8 })
  | .l8 => (m, .cont { f with pc := .l9 (m.X f.o).1 })
  | .l9 hh => (m, .cont { f with sh := max (m.det f.h) f.s + 1, pc := .l10 hh })
  | .l10 hh =>
    if m.X f.o = (hh, f.s) then
      ({ m with X := Function.update m.X f.o (some f.h, f.sh) }, .cont { f with r := true, pc := .f13 })
    else (m, .cont { f with r := false, pc := .f13 })
  | .f13 => (m, .cont { f with pc := .f14 (m.X f.o) })
  | .f14 x =>
    match x.1 with
    | none => (m, .done f.r)
    | some g => (m, .cont { f with pc := .f15 g x.2 (m.det g) })
  | .f15 g e d =>
    if d < e ∧ m.det g = d then
      ({ m with det := Function.update m.det g e }, .cont { f with pc := .f16 g e })
    else (m, .cont { f with pc := .f16 g e })
  | .f16 g e => (m, .cont { f with pc := .f17 g e (m.hval g) })
  | .f17 g e vh => (m, .cont { f with pc := .f18 g e vh (m.Y f.o) })
  | .f18 g e vh y =>
    if y.1 < e ∧ m.Y f.o = y then
      ({ m with Y := Function.update m.Y f.o (e, vh) }, .done f.r)
    else (m, .done f.r)

/-- The DuraCAS-level continuation of a process after a `TRANSFER-WRITE` returns. -/
inductive Next (V : Type) where
  | go (pc : Pc V)
  | ret (r : Resp V)
  | rdone

/-- Continuation after `TRANSFER-WRITE` with return address `ret`. -/
def afterTW : Ret V → Next V
  | .casT i z => .go (.cas10 i z)
  | .wr1 => .go (.tw19 .wr2)
  | .wr2 => .ret (.ok true)
  | .rec1 => .go (.tw19 .rec2)
  | .rec2 => .rdone

/-- Continuation after an `ECSC`/`RECOVER` call issued at `pc` returns `r`. -/
def afterCall : Pc V → Bool → Next V
  | .cas10 i _, r => if r then .ret (.ok true) else if i then .ret (.ok false) else .go (.cas7 true)
  | .wr15 _, _ => .go (.tw19 .wr1)
  | .tw21 ret _ _, _ => afterTW ret
  | .recv j, _ => if h : j.val < 3 then .go (.recv ⟨j.val + 1, by omega⟩) else .go (.tw19 .rec1)
  | _, _ => .go .idle

/-- The DurEC object and handle of the call issued at `pc` (for an object `k` and process `p`). -/
def callObj (k : K) : Pc V → Obj K
  | .wr12 => (k, .W)
  | .wr15 _ => (k, .W)
  | .tw20 _ _ => (k, .W)
  | .recv j => (k, if j.val % 2 = 0 then .W else .Z)
  | _ => (k, .Z)

/-- Apply a continuation to process `p` whose memory is `m`. -/
def applyNext (s : St P K V) (p : P) (m : Mem P K V) (n : Next V) : St P K V :=
  let st := s.ps p
  match n with
  | .go pc => { s with m := m, ps := Function.update s.ps p { st with pc := pc, fr := none } }
  | .ret r =>
    { s with m := m, ps := Function.update s.ps p ⟨.idle, none, none⟩,
             hist := s.hist ++ [.ret ((st.op.map OpRec.id).getD 0) r (m.det (p, .crit))] }
  | .rdone =>
    { s with m := m, ps := Function.update s.ps p ⟨.idle, none, none⟩,
             hist := s.hist ++ [.rdone ((st.op.map OpRec.id).getD 0) (m.det (p, .crit))] }

/-- Set the active DurEC frame of `p`. -/
def setFrame (s : St P K V) (p : P) (m : Mem P K V) (f : Frame P K V) : St P K V :=
  { s with m := m, ps := Function.update s.ps p { s.ps p with fr := some f } }

/-- Start an `ECSC(h, s, v)` call on `o` at `pc` (line 6). -/
def startSC (s : St P K V) (p : P) (o : Obj K) (h : Hd P) (sq : ℕ) (v : V × Bool) : St P K V :=
  if (s.m.Y o).1 ≠ sq then applyNext s p s.m (afterCall (s.ps p).pc false)
  else setFrame s p s.m ⟨.sc, o, h, sq, v, 0, false, .l7⟩

/-- The next step of a busy process `p` (deterministic). -/
def pstep (s : St P K V) (p : P) : St P K V :=
  let st := s.ps p
  match st.fr with
  | some f =>
    match fstep s.m f with
    | (m', .cont f') => setFrame s p m' f'
    | (m', .done r) => applyNext s p m' (afterCall st.pc r)
  | none =>
    match st.op with
    | none => s
    | some r =>
      let k := r.k
      let Wk := s.m.Y (k, .W)
      let Zk := s.m.Y (k, .Z)
      match st.pc with
      | .idle => s
      | .read => applyNext s p s.m (.ret (.val Zk.2.1))
      | .cas7 i =>
        match r.op with
        | .cas old new =>
          if Zk.2.1 ≠ old then applyNext s p s.m (.ret (.ok false))
          else if old = new then applyNext s p s.m (.ret (.ok true))
          else applyNext s p s.m (.go (.tw19 (.casT i Zk)))
        | _ => s
      | .cas10 _ z =>
        match r.op with
        | .cas _ new => startSC s p (k, .Z) (p, .crit) z.1 (new, z.2.2)
        | _ => s
      | .wr12 => applyNext s p s.m (.go (.wr13 Wk))
      | .wr13 w =>
        match r.op with
        | .write v =>
          if Zk.2.1 = v then applyNext s p s.m (.ret (.ok true))
          else if Zk.2.2 = w.2.2 then applyNext s p s.m (.go (.wr15 w))
          else applyNext s p s.m (.go (.tw19 .wr1))
        | _ => s
      | .wr15 w =>
        match r.op with
        | .write v => startSC s p (k, .W) (p, .crit) w.1 (v, !w.2.2)
        | _ => s
      | .tw19 ret => applyNext s p s.m (.go (.tw20 ret Zk))
      | .tw20 ret zh =>
        if zh.2.2 ≠ Wk.2.2 then applyNext s p s.m (.go (.tw21 ret zh Wk))
        else applyNext s p s.m (afterTW ret)
      | .tw21 _ zh wh => startSC s p (k, .Z) (p, .cas) zh.1 wh.2
      | .recv j =>
        setFrame s p s.m ⟨.recov, (k, if j.val % 2 = 0 then .W else .Z),
          (p, if j.val < 2 then .crit else .cas), 0, (s.m.hval (p, .crit)), 0, false,
          .f14 (s.m.X (k, if j.val % 2 = 0 then .W else .Z))⟩

/-- The first program counter of an operation. -/
def firstPc : Op V → Pc V
  | .read => .read
  | .cas _ _ => .cas7 false
  | .write _ => .wr12

/-- Invocation of `op` on object `k` by `p` (no idleness check). -/
def doInvoke (s : St P K V) (p : P) (k : K) (op : Op V) : St P K V :=
  { s with ps := Function.update s.ps p ⟨firstPc op, none, some ⟨s.nid, k, op, s.m.det (p, .crit)⟩⟩,
           hist := s.hist ++ [.inv s.nid p k op (s.m.det (p, .crit))],
           nid := s.nid + 1 }

/-- Crash of `p`: the local state is lost; a busy process restarts at line 22 of `RECOVER`. -/
def doCrash (s : St P K V) (p : P) : St P K V :=
  { s with ps := Function.update s.ps p ⟨.recv 0, none, (s.ps p).op⟩,
           hist := s.hist ++ [.crash p] }

/-- A process is busy iff it executes (or recovers) an operation. -/
def Busy (s : St P K V) (p : P) : Prop := (s.ps p).op.isSome

/-- Transitions labels. -/
inductive Lbl (P K V : Type) where
  | step (p : P)
  | invoke (p : P) (k : K) (op : Op V)
  | crash (p : P)
  deriving DecidableEq

/-- Enabledness of a transition (per-process discipline). -/
def Lbl.En (s : St P K V) : Lbl P K V → Prop
  | .step p => (s.ps p).op.isSome
  | .invoke p _ _ => (s.ps p).op = none
  | .crash p => (s.ps p).op.isSome

instance (s : St P K V) : (ℓ : Lbl P K V) → Decidable (ℓ.En s)
  | .step p => inferInstanceAs (Decidable ((s.ps p).op.isSome))
  | .invoke p _ _ => inferInstanceAs (Decidable ((s.ps p).op = none))
  | .crash p => inferInstanceAs (Decidable ((s.ps p).op.isSome))

/-- Effect of a transition. -/
def Lbl.apply (s : St P K V) : Lbl P K V → St P K V
  | .step p => pstep s p
  | .invoke p k op => doInvoke s p k op
  | .crash p => doCrash s p

/-- Initial state; `init k` is the initial value of object `k`, `hv0` the arbitrary initial
content of the `Val` fields. The `W` object of `k` is initialised with value `init k` (the paper:
`0`; its initial value is never used). -/
def initSt (init : K → V) (hv0 : Hd P → V × Bool) : St P K V where
  m := { X := fun _ => (none, 0)
         Y := fun o => (0, (init o.1, false))
         det := fun _ => 0
         hval := hv0 }
  ps := fun _ => ⟨.idle, none, none⟩
  hist := []
  nid := 0

/-- One step of the system (per-process recovery discipline). -/
def Step (s s' : St P K V) : Prop := ∃ ℓ : Lbl P K V, ℓ.En s ∧ s' = ℓ.apply s

/-- Reachable states. -/
def Reach (init : K → V) (hv0 : Hd P → V × Bool) : St P K V → Prop :=
  Relation.ReflTransGen Step (initSt init hv0)

end Podc.DuraCAS
