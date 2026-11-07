import Mathlib.Data.List.Basic

/-!
# The almost-wait-free test-and-set bit (Section 3.1) is not safe: a counterexample to
# Theorem 3.2

Taubenfeld, *A closer look at fault tolerance*, PODC 2012 (full version of 22 Feb 2017),
Section 3. Process `p`'s program (`n` processes, registers `turn`, `winner`, `lock[1..n-1]`):

```
function test-and-set (b:bit) return:value in {0, 1};
1  if b.turn ≠ 0 then return(0) fi;                         /* lost */
2  b.turn := p;
3  repeat
4    for j := 1 to n − 1 do                                 /* get locks */
5      if b.lock[j] = 0 then b.lock[j] := p fi od
6    locked := 1;
7    for j := 1 to n − 1 do                                 /* have all locks? */
8      if b.lock[j] ≠ p then locked := 0 fi od;
9  until b.turn ≠ p or locked = 1 or b.winner = 1;
10 if b.turn ≠ p or b.winner = 1 then
11   for j := 1 to n − 1 do                                 /* lost, release locks */
12     if b.lock[j] = p then b.lock[j] := 0 fi od
13   return(0) fi;
14 b.winner := 1; return(1).                                /* wins */

function reset (b:bit);
1  b.winner := 0; b.turn := 0;
2  for j := 1 to n − 1 do
3    if b.lock[j] = p then b.lock[j] := 0 fi od.
```

Theorem 3.2 (safety) claims: in every *well-structured* run (a reset is only invoked by a process
whose last operation was a winning test-and-set) there is at most one *winner* (a process whose
last completed operation is a winning test-and-set).

**The claim is false.** A process `q` may leave the `repeat` loop because it reads
`winner = 1` (some `p` is the current winner), then read `turn = q` at line 10 while `p` is
resetting the bit (`winner := 0` already written, `turn := 0` not yet), and then read
`winner = 0` and win — without holding any lock. If meanwhile `p` completes its reset and wins
again (it gets all locks, since `q` holds none), both `p` and `q` are winners
(`two_winners_n2`, `two_winners_n3`: explicit schedules of 35 and 39 steps for `n = 2, 3`). The
history is not linearizable either: `q`'s winning operation overlaps `p`'s reset and `p`'s second
winning operation, and no linearization point for it is legal. The paper's proof of Theorem 3.2
overlooks this path: "any other process has to set all the n−1 locks and see turn set to its value
for it to become a winner" is wrong because line 10 does not test `locked`.

A one-condition fix — losing at line 10 also when `locked = 0` — removes the counterexample
(`fixed := true` below; proved safe for every `n ≥ 2` in `TestAndSetFix.lean`).

Model: every line accesses at most one register atomically; the local variable `locked` is part
of the program counter; a process with no pending operation may invoke `test-and-set` (from
`idle`) or, if it is a winner, `reset` (from `won`), so every schedule is well-structured.
Identifiers are `1..n`; `0` is the empty value.
-/

namespace Podc.CloserLookFT.TAS

/-- Shared registers: `turn`, `winner`, and `lock[1..n-1]` (as a list, `lock[j]` at index
`j - 1`). -/
structure TMem where
  /-- `b.turn` -/
  turn : ℕ
  /-- `b.winner` -/
  winner : ℕ
  /-- `b.lock[1..n-1]` -/
  lock : List ℕ
  deriving DecidableEq

/-- Program counters. -/
inductive TLoc where
  /-- no pending operation, not a winner -/
  | idle
  /-- no pending operation, last operation was a winning test-and-set (a *winner*) -/
  | won
  /-- line 1 -/
  | l1
  /-- line 2 -/
  | l2
  /-- line 5, read `lock[j]` -/
  | get (j : ℕ)
  /-- line 5, write `lock[j] := p` -/
  | getw (j : ℕ)
  /-- line 8, read `lock[j]` (with the current value of `locked`) -/
  | chk (j : ℕ) (locked : Bool)
  /-- line 9, read `turn` -/
  | u9a (locked : Bool)
  /-- line 9, read `winner` -/
  | u9b
  /-- line 10, read `turn` -/
  | x10a (locked : Bool)
  /-- line 10, read `winner` -/
  | x10b
  /-- lines 11–12, read `lock[j]` -/
  | rel (j : ℕ)
  /-- line 12, write `lock[j] := 0` -/
  | relw (j : ℕ)
  /-- line 14, write `winner := 1` -/
  | w14
  /-- reset line 1, write `winner := 0` -/
  | r1a
  /-- reset line 1, write `turn := 0` -/
  | r1b
  /-- reset lines 2–3, read `lock[j]` -/
  | rrel (j : ℕ)
  /-- reset line 3, write `lock[j] := 0` -/
  | rrelw (j : ℕ)
  deriving DecidableEq

/-- `lock[j]`. -/
def TMem.lk (m : TMem) (j : ℕ) : ℕ := m.lock.getD (j - 1) 0

/-- `lock[j] := v`. -/
def TMem.setLk (m : TMem) (j v : ℕ) : TMem := { m with lock := m.lock.set (j - 1) v }

variable (n : ℕ) (fixed : Bool)

/-- After line 5 for index `j`. -/
def nextGet (j : ℕ) : TLoc := if j < n - 1 then .get (j + 1) else .chk 1 true

/-- One atomic step of process `p` (`fixed = true`: line 10 also loses when `locked = 0`). -/
def tstep (p : ℕ) (m : TMem) : TLoc → TMem × TLoc
  | .idle => (m, .l1)
  | .won => (m, .r1a)
  | .l1 => (m, if m.turn ≠ 0 then .idle else .l2)
  | .l2 => ({ m with turn := p }, .get 1)
  | .get j => (m, if m.lk j = 0 then .getw j else nextGet n j)
  | .getw j => (m.setLk j p, nextGet n j)
  | .chk j lo =>
    let lo' := lo && decide (m.lk j = p)
    (m, if j < n - 1 then .chk (j + 1) lo' else .u9a lo')
  | .u9a lo => (m, if m.turn ≠ p ∨ lo then .x10a lo else .u9b)
  | .u9b => (m, if m.winner = 1 then .x10a false else .get 1)
  | .x10a lo => (m, if m.turn ≠ p ∨ (fixed ∧ lo = false) then .rel 1 else .x10b)
  | .x10b => (m, if m.winner = 1 then .rel 1 else .w14)
  | .rel j => (m, if m.lk j = p then .relw j else if j < n - 1 then .rel (j + 1) else .idle)
  | .relw j => (m.setLk j 0, if j < n - 1 then .rel (j + 1) else .idle)
  | .w14 => ({ m with winner := 1 }, .won)
  | .r1a => ({ m with winner := 0 }, .r1b)
  | .r1b => ({ m with turn := 0 }, .rrel 1)
  | .rrel j => (m, if m.lk j = p then .rrelw j else if j < n - 1 then .rrel (j + 1) else .idle)
  | .rrelw j => (m.setLk j 0, if j < n - 1 then .rrel (j + 1) else .idle)

/-- A global state: memory and the program counters of processes `1..n` (as a list). -/
abbrev TSys := TMem × List TLoc

/-- Initial state: all registers `0`, all processes idle. -/
def tinit : TSys := (⟨0, 0, List.replicate (n - 1) 0⟩, List.replicate n .idle)

/-- Process `p ∈ {1..n}` takes a step; other identifiers (in particular `0`, the empty value of
the registers) are not processes and leave the state unchanged. -/
def tsysStep (s : TSys) (p : ℕ) : TSys :=
  if 1 ≤ p ∧ p ≤ n then
    let r := tstep n fixed p s.1 (s.2.getD (p - 1) .idle)
    (r.1, s.2.set (p - 1) r.2)
  else s

/-- Run a schedule (a list of process identifiers). -/
def trun (σ : List ℕ) : TSys := σ.foldl (tsysStep n fixed) (tinit n)

/-- Number of winners (processes whose last completed operation is a winning test-and-set). -/
def winners (s : TSys) : ℕ := s.2.count .won

/-- The statement of **Theorem 3.2** for `n` processes: every (well-structured) run has at most
one winner. -/
def Theorem32 (n : ℕ) (fixed : Bool) : Prop := ∀ σ : List ℕ, winners (trun n fixed σ) ≤ 1

/-- The schedule for `n = 2`. -/
def σ₂ : List ℕ :=
  [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    2, 1, 2]

/-- The schedule for `n = 3`. -/
def σ₃ : List ℕ :=
  [1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3,
    3, 1, 2, 3, 3, 2, 3]

/-- With two processes, the printed algorithm reaches a state with two winners. -/
theorem two_winners_n2 : winners (trun 2 false σ₂) = 2 := by decide

/-- With three processes, the printed algorithm reaches a state with two winners. -/
theorem two_winners_n3 : winners (trun 3 false σ₃) = 2 := by decide

/-- **Theorem 3.2 is false** (for `n = 2` and `n = 3`): the test-and-set algorithm of
Section 3.1 has well-structured runs with two winners. -/
theorem theorem_3_2_false : ¬ Theorem32 2 false ∧ ¬ Theorem32 3 false :=
  ⟨fun h => by have := h σ₂; rw [two_winners_n2] at this; omega,
   fun h => by have := h σ₃; rw [two_winners_n3] at this; omega⟩

/-- The same schedule does not produce two winners for the fixed algorithm (the second
"winner" `2` loses at line 10). -/
theorem fixed_σ₂ : winners (trun 2 true σ₂) ≤ 1 := by decide

end Podc.CloserLookFT.TAS
