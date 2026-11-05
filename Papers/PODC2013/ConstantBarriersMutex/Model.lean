import Mathlib

/-!
# Attiya, Hendler, Levy (PODC 2013): Algorithm 1 under Total Store Ordering — the model

Hagit Attiya, Danny Hendler, Smadar Levy. *An O(1)-Barriers Optimal RMRs Mutual Exclusion
Algorithm.* PODC 2013 (extended abstract).

```
 1 shared T : binary tree with leaves L_0 … L_{n−1}, nodes init −1
 3 shared promQ : queue of int, init ∅
 5 shared apply  : array [0..n−1] of boolean init false
 7 shared signal : array [0..n−1] of boolean
 9 shared inPromQ: array [0..n−1] of boolean init false
11 shared lock : int init −1
13 shared exits : int init 0
16 Entry():
17   signal[p] ← false
18   apply[p] ← true
19   foreach node n on the path from L_p to the root do n ← p
22   Barrier
23   if CAS(lock, −1, p) ≠ −1 then
24     e ← exits
25     await (exits − e ≥ 2) ∨ lock ∈ {p, −1}
26     if CAS(lock, −1, p) ≠ −1 then
27       await signal[p]
30 Exit():
31   apply[p] ← false
32   exits ← exits + 1
33   foreach node n on the path from the root to L_p's parent do
34     q1 ← n, q2 ← n.left, q3 ← n.right
35     foreach q ∈ {q1, q2, q3} \ {−1, p} do
36       if apply[q] ∧ ¬inPromQ[q] then
37         promQ.enqueue(q)
38         inPromQ[q] ← true
42   if promQ.isEmpty() then
43     lock ← −1
44   else
45     next ← promQ.dequeue()
46     inPromQ[next] ← false
47     lock ← next
48     signal[next] ← true
50   Barrier
```

## Model (Section 3 of the paper)

* `n = 2^h` processes `Fin (2^h)`; the tree is the complete binary tree in heap numbering (root `1`,
  children of `v` are `2v`, `2v+1`, leaf of `p` is `2^h + p`); `anc p l` is the node at level `l`
  (root = level 0, leaves = level `h`) on the path of `p`. A node holds `none` (= `−1`) or a
  process id; only process `p` ever writes `p`.
* **TSO** (the paper's Section 3, after Park and Dill): every process has a FIFO store buffer
  `buf p`. A write is *issued* by appending it to the buffer and *performed* when it leaves the
  buffer (event `flush p`, chosen by the adversary at any time). A read returns the value of the
  most recent write to that variable in the reader's own buffer, if any, and the memory value
  otherwise (`Mem.view`). A barrier step with a non-empty buffer performs the oldest buffered
  write (so a barrier completes after the buffer is drained). A CAS first performs all buffered
  writes and then compares-and-swaps atomically on memory.
* Each step of a process performs one shared-memory access (or a local step). The `foreach` of
  statement 35 visits the distinct values among `q1, q2, q3` (other than `−1, p`) in this order.
  The queue `promQ` is a single shared variable holding a list; `enqueue`/`dequeue` read it (in
  the process's view) and issue a write of the new list in one step, and `exits ← exits + 1` reads
  and issues the write in one step (in all three cases only the lock holder accesses the
  variable, so this does not restrict the behaviour of the algorithm; see `README.md`).
* The critical section is one local step (`cs → x31`). The remainder section is `rem`; a step
  of a process in `rem` starts a passage by issuing statement 17.
* `ent` is a ghost counter of critical-section entries (never read by the algorithm).
-/

namespace Podc.ConstantBarriersMutex

/-- Processes `0, …, 2^h − 1`. -/
abbrev Proc (h : ℕ) := Fin (2 ^ h)

variable {h : ℕ}

/-- The leaf of process `p` (heap numbering). -/
def leaf (p : Proc h) : ℕ := 2 ^ h + p.val

/-- The node at level `l` on the path from `p`'s leaf to the root (root: level `0`). -/
def anc (p : Proc h) (l : ℕ) : ℕ := leaf p / 2 ^ (h - l)

/-- Shared memory. -/
structure Mem (h : ℕ) where
  /-- tree nodes (`none` = `−1`) -/
  node : ℕ → Option (Proc h)
  /-- the promotion queue -/
  promQ : List (Proc h)
  /-- `apply` array -/
  apply : Proc h → Bool
  /-- `signal` array -/
  signal : Proc h → Bool
  /-- `inPromQ` array -/
  inPromQ : Proc h → Bool
  /-- the lock (`none` = `−1`) -/
  lock : Option (Proc h)
  /-- number of exits -/
  exits : ℕ

/-- A buffered write. -/
inductive W (h : ℕ) where
  | node (i : ℕ) (v : Proc h)
  | promQ (l : List (Proc h))
  | apply (q : Proc h) (b : Bool)
  | signal (q : Proc h) (b : Bool)
  | inPromQ (q : Proc h) (b : Bool)
  | lock (v : Option (Proc h))
  | exits (v : ℕ)
  deriving DecidableEq

/-- Performing a write on memory. -/
def Mem.write (m : Mem h) : W h → Mem h
  | .node i v => { m with node := Function.update m.node i (some v) }
  | .promQ l => { m with promQ := l }
  | .apply q b => { m with apply := Function.update m.apply q b }
  | .signal q b => { m with signal := Function.update m.signal q b }
  | .inPromQ q b => { m with inPromQ := Function.update m.inPromQ q b }
  | .lock v => { m with lock := v }
  | .exits v => { m with exits := v }

/-- The memory as seen by a process with store buffer `b` (oldest write first). -/
def Mem.view (m : Mem h) (b : List (W h)) : Mem h := b.foldl Mem.write m

/-- Program counters (with the local variables). -/
inductive PC (h : ℕ) where
  /-- remainder section -/
  | rem
  /-- statement 18 -/
  | e18
  /-- statement 20 for the node at level `l` -/
  | e19 (l : ℕ)
  /-- statement 22 (barrier) -/
  | e22
  /-- statement 23 (CAS) -/
  | e23
  /-- statement 24 (`e ← exits`) -/
  | e24
  /-- statement 25, reading `exits` -/
  | e25a (e : ℕ)
  /-- statement 25, reading `lock` -/
  | e25b (e : ℕ)
  /-- statement 26 (CAS) -/
  | e26
  /-- statement 27 (`await signal[p]`) -/
  | e27
  /-- critical section -/
  | cs
  /-- statement 31 -/
  | x31
  /-- statement 32 -/
  | x32
  /-- statement 34 at level `l`: read node `j` of `(n, n.left, n.right)`; `acc` = candidates so far -/
  | x34 (l j : ℕ) (acc : List (Proc h))
  /-- statement 35 at level `l`: candidates still to examine -/
  | x35 (l : ℕ) (cands : List (Proc h))
  /-- statement 36, second conjunct (`inPromQ[q]`), for candidate `q` -/
  | x36 (l : ℕ) (q : Proc h) (rest : List (Proc h))
  /-- statement 37 (enqueue `q`) -/
  | x37 (l : ℕ) (q : Proc h) (rest : List (Proc h))
  /-- statement 38 (`inPromQ[q] ← true`) -/
  | x38 (l : ℕ) (q : Proc h) (rest : List (Proc h))
  /-- statement 42 -/
  | x42
  /-- statement 43 -/
  | x43
  /-- statement 45 (dequeue) -/
  | x45
  /-- statement 46 -/
  | x46 (nx : Proc h)
  /-- statement 47 -/
  | x47 (nx : Proc h)
  /-- statement 48 -/
  | x48 (nx : Proc h)
  /-- statement 50 (barrier); `o` = the process the lock was handed to (`none` after 43) -/
  | x50 (o : Option (Proc h))
  deriving DecidableEq

/-- Configurations. -/
structure Cfg (h : ℕ) where
  /-- shared memory -/
  mem : Mem h
  /-- store buffers (oldest write first) -/
  buf : Proc h → List (W h)
  /-- program counters with local variables -/
  pc : Proc h → PC h
  /-- ghost: number of critical-section entries so far -/
  ent : ℕ

/-- The initial memory. -/
def Mem.init : Mem h where
  node _ := none
  promQ := []
  apply _ := false
  signal _ := false
  inPromQ _ := false
  lock := none
  exits := 0

/-- The initial configuration. -/
def Cfg.init : Cfg h where
  mem := Mem.init
  buf _ := []
  pc _ := .rem
  ent := 0

/-- The view of process `p`. -/
def Cfg.view (s : Cfg h) (p : Proc h) : Mem h := s.mem.view (s.buf p)

/-- Set the program counter of `p`. -/
def Cfg.goto (s : Cfg h) (p : Proc h) (c : PC h) : Cfg h :=
  { s with pc := Function.update s.pc p c }

/-- Issue a write `w` of `p` (append to its store buffer) and go to `c`. -/
def Cfg.issue (s : Cfg h) (p : Proc h) (w : W h) (c : PC h) : Cfg h :=
  { s with buf := Function.update s.buf p (s.buf p ++ [w]), pc := Function.update s.pc p c }

/-- Perform the oldest buffered write of `p` (no effect on an empty buffer). -/
def Cfg.flush (s : Cfg h) (p : Proc h) : Cfg h :=
  match s.buf p with
  | [] => s
  | w :: b => { s with mem := s.mem.write w, buf := Function.update s.buf p b }

/-- `CAS(lock, −1, p)` by `p` after performing all its buffered writes; on success go to `cs`
(and count the entry), otherwise to `c`. -/
def Cfg.cas (s : Cfg h) (p : Proc h) (c : PC h) : Cfg h :=
  let m := s.mem.view (s.buf p)
  if m.lock = none then
    { mem := { m with lock := some p }, buf := Function.update s.buf p [],
      pc := Function.update s.pc p .cs, ent := s.ent + 1 }
  else
    { s with mem := m, buf := Function.update s.buf p [], pc := Function.update s.pc p c }

/-- A barrier step of `p`: perform the oldest buffered write, or go to `c` if the buffer is empty. -/
def Cfg.barrier (s : Cfg h) (p : Proc h) (c : PC h) : Cfg h :=
  if s.buf p = [] then s.goto p c else s.flush p

/-- The target of the read number `j` at statement 34 on the node `v`: `v`, `v.left`, `v.right`. -/
def target (v j : ℕ) : ℕ := if j = 0 then v else if j = 1 then 2 * v else 2 * v + 1

/-- Add a value read at statement 34 to the candidate list (statement 35: drop `−1`, `p` and
duplicates). -/
def addCand (p : Proc h) (acc : List (Proc h)) : Option (Proc h) → List (Proc h)
  | none => acc
  | some q => if q ≠ p ∧ q ∉ acc then acc ++ [q] else acc

/-- One step of process `p` (one shared-memory access or local step). -/
def Cfg.stepProc (s : Cfg h) (p : Proc h) : Cfg h :=
  let v := s.view p
  match s.pc p with
  | .rem => s.issue p (.signal p false) .e18
  | .e18 => s.issue p (.apply p true) (.e19 h)
  | .e19 l => s.issue p (.node (anc p l) p) (if l = 0 then .e22 else .e19 (l - 1))
  | .e22 => s.barrier p .e23
  | .e23 => s.cas p .e24
  | .e24 => s.goto p (.e25a v.exits)
  | .e25a e => s.goto p (if e + 2 ≤ v.exits then .e26 else .e25b e)
  | .e25b e => s.goto p (if v.lock = some p ∨ v.lock = none then .e26 else .e25a e)
  | .e26 => s.cas p .e27
  | .e27 => if v.signal p then { s.goto p .cs with ent := s.ent + 1 } else s
  | .cs => s.goto p .x31
  | .x31 => s.issue p (.apply p false) .x32
  | .x32 => s.issue p (.exits (v.exits + 1)) (if 0 < h then .x34 0 0 [] else .x42)
  | .x34 l j acc =>
    let acc' := addCand p acc (v.node (target (anc p l) j))
    s.goto p (if j < 2 then .x34 l (j + 1) acc' else .x35 l acc')
  | .x35 l [] => s.goto p (if l + 1 < h then .x34 (l + 1) 0 [] else .x42)
  | .x35 l (q :: rest) => s.goto p (if v.apply q then .x36 l q rest else .x35 l rest)
  | .x36 l q rest => s.goto p (if v.inPromQ q then .x35 l rest else .x37 l q rest)
  | .x37 l q rest => s.issue p (.promQ (v.promQ ++ [q])) (.x38 l q rest)
  | .x38 l q rest => s.issue p (.inPromQ q true) (.x35 l rest)
  | .x42 => s.goto p (if v.promQ = [] then .x43 else .x45)
  | .x43 => s.issue p (.lock none) (.x50 none)
  | .x45 =>
    match v.promQ with
    | [] => s.goto p .x42
    | nx :: rest => s.issue p (.promQ rest) (.x46 nx)
  | .x46 nx => s.issue p (.inPromQ nx false) (.x47 nx)
  | .x47 nx => s.issue p (.lock (some nx)) (.x48 nx)
  | .x48 nx => s.issue p (.signal nx true) (.x50 (some nx))
  | .x50 _ => s.barrier p .rem

/-- Scheduling events: a step of a process, or the adversary performing the oldest write in the
store buffer of a process. -/
inductive Ev (h : ℕ) where
  | step (p : Proc h)
  | flush (p : Proc h)
  deriving DecidableEq

/-- The effect of an event. -/
def Cfg.next (s : Cfg h) : Ev h → Cfg h
  | .step p => s.stepProc p
  | .flush p => s.flush p

/-- Reachable configurations. -/
inductive Reachable : Cfg h → Prop
  | init : Reachable Cfg.init
  | next {s : Cfg h} (e : Ev h) : Reachable s → Reachable (s.next e)

/-- Executions: an infinite schedule of events and the resulting configurations. -/
structure Run (h : ℕ) where
  /-- the event at time `t` -/
  ev : ℕ → Ev h
  /-- the configuration at time `t` -/
  s : ℕ → Cfg h
  init : s 0 = Cfg.init
  step : ∀ t, s (t + 1) = (s t).next (ev t)

/-- Fairness: a process outside the remainder section eventually takes a step. (Processes may
stay in the remainder section forever; buffered writes need no fairness: a process that keeps
stepping drains its buffer at the next barrier.) -/
def Run.Fair (r : Run h) : Prop :=
  ∀ p T, (r.s T).pc p ≠ .rem → ∃ t ≥ T, r.ev t = .step p

/-! ### Sections of the algorithm -/

/-- The entry section (statements 18–27, after statement 17 was issued). -/
def PC.Entry : PC h → Prop
  | .e18 | .e19 _ | .e22 | .e23 | .e24 | .e25a _ | .e25b _ | .e26 | .e27 => True
  | _ => False

/-- The waiting section (after the CAS of statement 23 failed). -/
def PC.Waiting : PC h → Prop
  | .e24 | .e25a _ | .e25b _ | .e26 | .e27 => True
  | _ => False

/-- The exit section, statements 31–48 (statement 50 is not part of it, as in the paper). -/
def PC.Exit : PC h → Prop
  | .x31 | .x32 | .x34 _ _ _ | .x35 _ _ | .x36 _ _ _ | .x37 _ _ _ | .x38 _ _ _ | .x42 | .x43
  | .x45 | .x46 _ | .x47 _ | .x48 _ => True
  | _ => False

instance (c : PC h) : Decidable c.Entry := by unfold PC.Entry; split <;> infer_instance
instance (c : PC h) : Decidable c.Waiting := by unfold PC.Waiting; split <;> infer_instance
instance (c : PC h) : Decidable c.Exit := by unfold PC.Exit; split <;> infer_instance

/-- `p` is in the critical section. -/
def Cfg.InCS (s : Cfg h) (p : Proc h) : Prop := s.pc p = .cs

/-- `p` is in the critical section or in its exit section in the sense of Definition 1 of the
paper: the exit section is completed when the write of statement 43 or 48 is *performed*, i.e.
when the buffer is drained at statement 50. -/
def Cfg.InCSX (s : Cfg h) (p : Proc h) : Prop :=
  s.pc p = .cs ∨ (s.pc p).Exit ∨ (∃ o, s.pc p = .x50 o) ∧ s.buf p ≠ []

end Podc.ConstantBarriersMutex
