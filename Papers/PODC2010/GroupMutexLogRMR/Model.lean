import Mathlib

/-!
# Group mutual exclusion in O(log n) RMR (Bhatt–Huang, PODC 2010): the model

Vibhor Bhatt, Chien-Chung Huang. *Group mutual exclusion in O(log n) RMR.* PODC 2010,
Figure 3 ("The final algorithm"):

```
Gmutex-Lock(s)                       Inc-Get-dir(s)               Promote-Exit(s)
  REMAINDER SECTION                  1.1 inc(C[s,0],1)            16.1  LL(Ex)
1  d ← Inc-Get-Dir(s)                1.2 inc(C[s,1],1)            16.2  SC(Ex,false)
2  inc(G,1)                          1.3 d ← In[s]                16.3  LL(Ex)
3  tm ← Read(G)                      1.4 if Min(Q) ∈ {(s,−),(⊥,⊥)} 16.4  LL(S)
4  Enqueue(Q,[p,s,d,tm])             1.5   if LL(S) = (s,d̄,−)      16.5  Exclear[s] ← false
5  Promote-Try(s)                    1.6     d ← d̄                16.6  inc(C[s,d],−1)
6  if LL(S) = (s,d,s)                1.7 inc(C[s,d̄],−1)           16.7  (sh,dh) ← Min(Q)
7    Out[s] ← d                      1.8 return d                 16.8  if C[s,d] = 0 ∧ sh ≠ ⊥
8  wait till Out[s] = d                                           16.9    if SC(Ex,s)
9  if ¬LL(Ex)                        Promote-Try(s)               16.10     if SC(S,(sh,dh,s))
10   SC(Ex,false)                    5.1 (sc,dc,−) ← LL(S)        16.11       Out[sh] = dh
11 if false ≠ se = LL(Ex)            5.2 (sh,dh) ← Min(Q)         16.12     if S = (s',d',s'') ∧ s' = s''
12   wait till Exclear[se]           5.3 if C[sc,dc] = 0 ∧ sh ≠ sc 16.13       Out[s'] ← d'
   CRITICAL SECTION                  5.4   if SC(S,(sh,dh,s))     16.14     Exclear[s] ← true
13 Dequeue(Q,[p,s,d,tm])             5.5     Out[sh] ← dh
14 if Min(Q) ≠ (s,−)
15   In[s] ← d̄
16 Promote-Exit(s)
```

Initially `Q = ∅`, `S = (s₀,0,s₀)`, `Ex = false`, `G = 0`, `In[s] = 1`, `Out[s] = 0`,
`Exclear[s] = true`, `C[s,d] = 0`.

## Model

* Asynchronous shared memory, `n` processes `Fin n`, sessions of an arbitrary type `J`
  (`s₀ : J` is the initial session recorded in `S`). Sides are `Bool` (`false` = 0,
  `true` = 1, `d̄ = !d`).
* Every numbered line is one atomic step (it performs one access to a shared object, plus
  local computation). Line 1.8 (`return d`) is merged with line 1.7, and the critical section is
  a single step `cs`. A process in the remainder section that takes a step starts a new attempt
  with a session chosen by the adversary (the event carries it).
* `G`, `C[s,d]` and `Q` are atomic (linearizable) objects, as in Theorems 2–3 of the paper. The
  priority process-queue is modelled by one slot per process (the paper's restrictions (i)–(ii):
  only `p` dequeues its element, and `p` dequeues before enqueuing again); `Min(Q)` returns the
  `(s,d)` of the element with the least `(tm, p)`.
* LL/SC (`S` and `Ex`): a per-process link bit, set by `LL`, cleared for everybody by every
  successful `SC`; `SC` by `p` succeeds iff `p`'s bit is set ("no successful SC since `p`'s latest
  LL"). Line 16.12 is a plain read of `S`.
* `Ex = false` is `none`. Wait loops (lines 8, 12) are a read that leaves the program counter
  unchanged when the condition fails.
-/

namespace Podc.GroupMutexLogRMR

/-- Program counters: the line a process executes next. -/
inductive PC where
  | rem
  | l1_1 | l1_2 | l1_3 | l1_4 | l1_5 | l1_6 | l1_7
  | l2 | l3 | l4
  | l5_1 | l5_2 | l5_3 | l5_4 | l5_5
  | l6 | l7 | l8 | l9 | l10 | l11 | l12
  | cs
  | l13 | l14 | l15
  | l16_1 | l16_2 | l16_3 | l16_4 | l16_5 | l16_6 | l16_7 | l16_8 | l16_9 | l16_10 | l16_11
  | l16_12 | l16_13 | l16_14
  deriving DecidableEq, Repr

/-- The local state of a process: program counter and private variables. -/
structure Loc (J : Type) where
  /-- program counter -/
  pc : PC
  /-- requested session `s` -/
  s : J
  /-- side `d` -/
  d : Bool
  /-- time-stamp `tm` -/
  tm : ℕ
  /-- `(sc, dc)` read at line 5.1, `se` read at line 11 (first component), or `(s', d')` read at
  line 16.12 -/
  a : J × Bool
  /-- `Min(Q)` read at line 5.2 or 16.7 (`none` = `(⊥,⊥)`) -/
  b : Option (J × Bool)
  deriving DecidableEq

/-- Configurations: shared variables and local states. -/
structure Cfg (n : ℕ) (J : Type) where
  /-- `S = (session, side, session of the last successful SC)` -/
  S : J × Bool × J
  /-- `Ex` (`none` = `false`) -/
  Ex : Option J
  /-- global counter `G` -/
  G : ℕ
  /-- `In[s]` -/
  In : J → Bool
  /-- `Out[s]` -/
  Out : J → Bool
  /-- `Exclear[s]` -/
  Exclear : J → Bool
  /-- counters `C[s,d]` -/
  C : J → Bool → ℕ
  /-- the element `(s, d, tm)` of `p` in the priority queue `Q`, if any -/
  Q : Fin n → Option (J × Bool × ℕ)
  /-- LL/SC link of `p` on `S` -/
  linkS : Fin n → Bool
  /-- LL/SC link of `p` on `Ex` -/
  linkEx : Fin n → Bool
  /-- local states -/
  loc : Fin n → Loc J

variable {n : ℕ} {J : Type}

/-- One step of the scan for the smallest element of `Q`: keep the accumulator unless `q`'s
element has a strictly smaller time-stamp (so ties go to the smaller process id). -/
def qstep (Q : Fin n → Option (J × Bool × ℕ)) (acc : Option (Fin n)) (q : Fin n) : Option (Fin n) :=
  match Q q, acc with
  | none, _ => acc
  | some _, none => some q
  | some (_, _, t), some r =>
    match Q r with
    | some (_, _, t') => if t < t' then some q else acc
    | none => some q

/-- The process whose element is the smallest in `Q` (least `(tm, p)`). -/
def qminProc (Q : Fin n → Option (J × Bool × ℕ)) : Option (Fin n) :=
  (List.finRange n).foldl (qstep Q) none

/-- `Min(Q)`: the pair `(s, d)` of the smallest element, `none` (= `(⊥,⊥)`) if `Q` is empty. -/
def minQ (Q : Fin n → Option (J × Bool × ℕ)) : Option (J × Bool) :=
  (qminProc Q).bind fun q => (Q q).map fun e => (e.1, e.2.1)

variable [DecidableEq J]

/-- The initial configuration (`S = (s₀, 0, s₀)`). -/
def Cfg.init (n : ℕ) (s₀ : J) : Cfg n J where
  S := (s₀, false, s₀)
  Ex := none
  G := 0
  In _ := true
  Out _ := false
  Exclear _ := true
  C _ _ := 0
  Q _ := none
  linkS _ := false
  linkEx _ := false
  loc _ := ⟨.rem, s₀, false, 0, (s₀, false), none⟩

namespace Cfg

/-- Replace the local state of `p`. -/
def setLoc (c : Cfg n J) (p : Fin n) (l : Loc J) : Cfg n J :=
  { c with loc := Function.update c.loc p l }

/-- Move `p` to program counter `pc` (other locals unchanged). -/
def go (c : Cfg n J) (p : Fin n) (pc : PC) : Cfg n J :=
  c.setLoc p { c.loc p with pc := pc }

/-- `C[s,d] ← C[s,d] + 1`. -/
def incC (c : Cfg n J) (s : J) (d : Bool) : Cfg n J :=
  { c with C := Function.update c.C s (Function.update (c.C s) d (c.C s d + 1)) }

/-- `C[s,d] ← C[s,d] - 1`. -/
def decC (c : Cfg n J) (s : J) (d : Bool) : Cfg n J :=
  { c with C := Function.update c.C s (Function.update (c.C s) d (c.C s d - 1)) }

/-- Set `p`'s link on `S` (`LL(S)`). -/
def llS (c : Cfg n J) (p : Fin n) : Cfg n J :=
  { c with linkS := Function.update c.linkS p true }

/-- Set `p`'s link on `Ex` (`LL(Ex)`). -/
def llEx (c : Cfg n J) (p : Fin n) : Cfg n J :=
  { c with linkEx := Function.update c.linkEx p true }

/-- A successful `SC(S, v)`. -/
def scS (c : Cfg n J) (v : J × Bool × J) : Cfg n J :=
  { c with S := v, linkS := fun _ => false }

/-- A successful `SC(Ex, v)`. -/
def scEx (c : Cfg n J) (v : Option J) : Cfg n J :=
  { c with Ex := v, linkEx := fun _ => false }

/-- `Out[s] ← d`. -/
def setOut (c : Cfg n J) (s : J) (d : Bool) : Cfg n J :=
  { c with Out := Function.update c.Out s d }

/-- `Exclear[s] ← v`. -/
def setExclear (c : Cfg n J) (s : J) (v : Bool) : Cfg n J :=
  { c with Exclear := Function.update c.Exclear s v }

/-- One step of process `p`; `σ` is the session requested if `p` starts a new attempt. -/
def step (c : Cfg n J) (p : Fin n) (σ : J) : Cfg n J :=
  let l := c.loc p
  let s := l.s
  let d := l.d
  match l.pc with
  | .rem => c.setLoc p { l with pc := .l1_1, s := σ }
  | .l1_1 => (c.incC s false).go p .l1_2
  | .l1_2 => (c.incC s true).go p .l1_3
  | .l1_3 => c.setLoc p { l with pc := .l1_4, d := c.In s }
  | .l1_4 =>
    if minQ c.Q = none ∨ (minQ c.Q).map Prod.fst = some s then c.go p .l1_5 else c.go p .l1_7
  | .l1_5 =>
    if c.S.1 = s ∧ c.S.2.1 = !d then (c.llS p).go p .l1_6 else (c.llS p).go p .l1_7
  | .l1_6 => c.setLoc p { l with pc := .l1_7, d := !d }
  | .l1_7 => (c.decC s (!d)).go p .l2
  | .l2 => ({ c with G := c.G + 1 }).go p .l3
  | .l3 => c.setLoc p { l with pc := .l4, tm := c.G }
  | .l4 => ({ c with Q := Function.update c.Q p (some (s, d, l.tm)) }).go p .l5_1
  | .l5_1 => (c.llS p).setLoc p { l with pc := .l5_2, a := (c.S.1, c.S.2.1) }
  | .l5_2 => c.setLoc p { l with pc := .l5_3, b := minQ c.Q }
  | .l5_3 =>
    match l.b with
    | some (sh, _) => if c.C l.a.1 l.a.2 = 0 ∧ sh ≠ l.a.1 then c.go p .l5_4 else c.go p .l6
    | none => c.go p .l6
  | .l5_4 =>
    match l.b with
    | some (sh, dh) => if c.linkS p then (c.scS (sh, dh, s)).go p .l5_5 else c.go p .l6
    | none => c.go p .l6
  | .l5_5 =>
    match l.b with
    | some (sh, dh) => (c.setOut sh dh).go p .l6
    | none => c.go p .l6
  | .l6 => if c.S = (s, d, s) then (c.llS p).go p .l7 else (c.llS p).go p .l8
  | .l7 => (c.setOut s d).go p .l8
  | .l8 => if c.Out s = d then c.go p .l9 else c
  | .l9 => if c.Ex = none then (c.llEx p).go p .l10 else (c.llEx p).go p .l11
  | .l10 => if c.linkEx p then (c.scEx none).go p .l11 else c.go p .l11
  | .l11 =>
    match c.Ex with
    | some se => (c.llEx p).setLoc p { l with pc := .l12, a := (se, l.a.2) }
    | none => (c.llEx p).go p .cs
  | .l12 => if c.Exclear l.a.1 then c.go p .cs else c
  | .cs => c.go p .l13
  | .l13 => ({ c with Q := Function.update c.Q p none }).go p .l14
  | .l14 =>
    if minQ c.Q = none ∨ (minQ c.Q).map Prod.fst ≠ some s then c.go p .l15 else c.go p .l16_1
  | .l15 => ({ c with In := Function.update c.In s (!d) }).go p .l16_1
  | .l16_1 => (c.llEx p).go p .l16_2
  | .l16_2 => if c.linkEx p then (c.scEx none).go p .l16_3 else c.go p .l16_3
  | .l16_3 => (c.llEx p).go p .l16_4
  | .l16_4 => (c.llS p).go p .l16_5
  | .l16_5 => (c.setExclear s false).go p .l16_6
  | .l16_6 => (c.decC s d).go p .l16_7
  | .l16_7 => c.setLoc p { l with pc := .l16_8, b := minQ c.Q }
  | .l16_8 => if c.C s d = 0 ∧ l.b ≠ none then c.go p .l16_9 else c.go p .rem
  | .l16_9 => if c.linkEx p then (c.scEx (some s)).go p .l16_10 else c.go p .rem
  | .l16_10 =>
    match l.b with
    | some (sh, dh) => if c.linkS p then (c.scS (sh, dh, s)).go p .l16_11 else c.go p .l16_12
    | none => c.go p .l16_12
  | .l16_11 =>
    match l.b with
    | some (sh, dh) => (c.setOut sh dh).go p .l16_12
    | none => c.go p .l16_12
  | .l16_12 =>
    if c.S.1 = c.S.2.2 then c.setLoc p { l with pc := .l16_13, a := (c.S.1, c.S.2.1) }
    else c.go p .l16_14
  | .l16_13 => (c.setOut l.a.1 l.a.2).go p .l16_14
  | .l16_14 => (c.setExclear s true).go p .rem

end Cfg

/-- An event: process `p` takes a step (requesting session `σ` if it starts an attempt). -/
abbrev Ev (n : ℕ) (J : Type) := Fin n × J

/-- The configuration after a finite sequence of events. -/
def run (c : Cfg n J) (es : List (Ev n J)) : Cfg n J :=
  es.foldl (fun c e => c.step e.1 e.2) c

/-- Reachable configurations. -/
def Reachable (s₀ : J) (c : Cfg n J) : Prop :=
  ∃ es : List (Ev n J), run (Cfg.init n s₀) es = c

/-- A schedule: the event at every time. -/
abbrev Sched (n : ℕ) (J : Type) := ℕ → Ev n J

/-- The configuration at time `t` of a schedule. -/
def Sched.cfg (s₀ : J) (σ : Sched n J) (t : ℕ) : Cfg n J :=
  run (Cfg.init n s₀) ((List.range t).map σ)

/-- Trying section: lines 1.1–12. -/
def PC.trying : PC → Prop
  | .rem | .cs | .l13 | .l14 | .l15 | .l16_1 | .l16_2 | .l16_3 | .l16_4 | .l16_5 | .l16_6
  | .l16_7 | .l16_8 | .l16_9 | .l16_10 | .l16_11 | .l16_12 | .l16_13 | .l16_14 => False
  | _ => True

instance : DecidablePred PC.trying := fun pc => by cases pc <;> simp [PC.trying] <;> infer_instance

/-- A process is active if it is not in the remainder section. -/
def Loc.active (l : Loc J) : Prop := l.pc ≠ .rem

end Podc.GroupMutexLogRMR
