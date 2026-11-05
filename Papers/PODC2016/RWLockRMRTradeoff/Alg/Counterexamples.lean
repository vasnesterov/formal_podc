import Papers.PODC2016.RWLockRMRTradeoff.Alg.Model

/-!
# Two bugs in Algorithm 1 of Hendler (PODC 2016), with explicit executions

1. **Mutual exclusion fails for the literal line 51.** If `C[i].read() = W[i].read()` (line 51)
   is evaluated left to right (`C` first), a helping reader can read `C[i]` while a reader that
   entered the CS without waiting is still counted, and then read a `W[i]` that has meanwhile
   caught up because *other* readers started waiting. With `f(n) = 1` and three readers the writer
   then enters its CS together with a reader (`mutex_violation_literal_order`). This holds for
   either version of line 47.
2. **Deadlock freedom fails for the literal line 47.** Line 47 tests `op` (the opcode read on
   entry, line 32) instead of `op'` (read on exit, line 41). A reader that entered the CS while
   `RSIG = <seq, PREENTRY>` then never calls `HelpWCS` on exit, although the writer waits for it in
   line 21. With one reader the writer waits in line 21 forever while the reader stays in the
   remainder section (`deadlock_literal_line47`). This holds for either order in line 51.
-/

namespace Podc.RWLockRMRTradeoff.Alg

open Who

/-! ### Mutual exclusion violation -/

/-- Three readers in a single group (`f(n) = 1`), literal order in line 51. -/
def cfgME (l47 : Line47) : Cfg 3 1 := ⟨.cw, l47, fun _ => 0⟩

/-- The schedule: the writer runs lines 6–16 (reading `C[0] = 0`); reader 0 starts and reads
`RSIG = <0, PREENTRY>` in line 32, so it enters the CS; the writer writes `<0, WAIT>` to `RSIG`
(line 18), reads `C[0] = 1` (line 20) and waits in line 21; reader 1 starts, reads `WAIT`,
increments `W[0]` and reads `C[0] = 2` in line 51; reader 2 starts, reads `WAIT` and increments
`W[0]` to 2; reader 1 reads `W[0] = 2 = C`-value and CASes `WSIG[0]` to `<0, CS>` (line 52); the
writer enters the CS. -/
def schedME : List (Who 3) :=
  [writer, writer, writer, writer, writer,
   reader 0, reader 0, reader 0,
   writer, writer,
   reader 1, reader 1, reader 1, reader 1, reader 1,
   reader 2, reader 2, reader 2, reader 2,
   reader 1, reader 1,
   writer]

/-- **Line 51 as written violates Mutual Exclusion (Lemma 8 / Lemma 9 fail).** With the literal
left-to-right evaluation of `C[i].read() = W[i].read()`, there is a reachable configuration
in which the writer and reader 0 are both in the critical section (for either version of
line 47). -/
theorem mutex_violation_literal_order (l47 : Line47) :
    ∃ s, Reachable (cfgME l47) s ∧ s.writerInCS ∧ s.readerInCS 0 := by
  refine ⟨run (cfgME l47) schedME init, reachable_run _ .init _, ?_⟩
  cases l47 <;> (unfold State.writerInCS State.readerInCS; decide)

/-- Hence the literal algorithm does not satisfy Mutual Exclusion. -/
theorem not_mutualExclusion_literal_order (l47 : Line47) :
    ¬ MutualExclusion (cfgME l47) := by
  intro h
  obtain ⟨s, hs, hw, hr⟩ := mutex_violation_literal_order l47
  exact h s hs hw 0 hr

/-! ### Mutual exclusion violation caused by line 47 -/

/-- One reader, one group, literal line 47, either order in line 51. -/
def cfgME47 (order : ReadOrder) : Cfg 1 1 := ⟨order, .op, fun _ => 0⟩

/-- The schedule: writer passage 0 runs to its exit (line 26 pending); the reader starts, reads
`RSIG = <0, WAIT>` and is about to wait (line 34); the writer completes passage 0 and starts passage
1 up to line 11 (`WSIG[0] = <1, ⊥>`, `RSIG = <1, NOP>`); the reader helps in vain, stops waiting,
passes through the CS and in its exit section reads `RSIG = <1, NOP>` in line 41; since its *entry*
opcode `op` is `WAIT`, line 47 (literal) calls `HelpWCS(1)`; it reads `W[0] = 0` and is about to
read `C[0]`; the writer runs lines 11–16 of passage 1 (`C[0] = 0`, `WSIG[0] := <1, WAIT>`); the
reader reads `C[0] = 0` and CASes `WSIG[0]` from `<1, WAIT>` to `<1, CS>` (line 52) although no
reader waits for passage 1; it then starts a new passage, reads `RSIG = <1, PREENTRY>` and enters
the CS; the writer writes `<1, WAIT>` (line 18), reads `C[0] = 1` (line 20), finds
`WSIG[0] = <1, CS>` (line 21) and enters the CS. -/
def schedME47 : List (Who 1) :=
  [writer, writer, writer, writer, writer, writer, writer, writer,
   reader 0, reader 0, reader 0,
   writer, writer, writer,
   reader 0, reader 0, reader 0, reader 0, reader 0, reader 0, reader 0, reader 0,
   writer, writer, writer,
   reader 0, reader 0, reader 0, reader 0, reader 0, reader 0,
   writer, writer, writer]

/-- **Line 47 as written also violates Mutual Exclusion**, even with a single reader and for
either order of the reads in line 51: a stale `HelpWCS(seq')` call (made because the *entry*
opcode `op` was `WAIT`, while `RSIG` holds `<seq', NOP>`) signals `<seq', CS>` to the next writer
passage before it has published `WAIT`. -/
theorem mutex_violation_literal_line47 (order : ReadOrder) :
    ∃ s, Reachable (cfgME47 order) s ∧ s.writerInCS ∧ s.readerInCS 0 := by
  refine ⟨run (cfgME47 order) schedME47 init, reachable_run _ .init _, ?_⟩
  cases order <;> (unfold State.writerInCS State.readerInCS; decide)

theorem not_mutualExclusion_literal_line47 (order : ReadOrder) :
    ¬ MutualExclusion (cfgME47 order) := by
  intro h
  obtain ⟨s, hs, hw, hr⟩ := mutex_violation_literal_line47 order
  exact h s hs hw 0 hr

/-! ### Deadlock -/

/-- One reader, one group, literal line 47. -/
def cfgDL (order : ReadOrder) : Cfg 1 1 := ⟨order, .op, fun _ => 0⟩

/-- The schedule: the writer runs lines 6–16 (reading `C[0] = 0` in line 13); the reader starts,
reads `RSIG = <0, PREENTRY>` in line 32 and enters the CS; the writer writes `<0, WAIT>` to `RSIG`
(line 18), reads `C[0] = 1` (line 20) and starts waiting in line 21 for `WSIG[0] = <0, CS>`; the
reader exits: it decrements `C[0]`, reads `<0, WAIT>` in line 41, and since its entry opcode `op`
is `PREENTRY` it skips `HelpWCS` (line 47) and returns to the remainder section. -/
def schedDL : List (Who 1) :=
  [writer, writer, writer, writer, writer,
   reader 0, reader 0, reader 0,
   writer, writer,
   reader 0, reader 0]

/-- The deadlocked configuration. -/
def stuckDL (order : ReadOrder) : State 1 1 := run (cfgDL order) schedDL init

theorem stuckDL_spec (order : ReadOrder) :
    (stuckDL order).w.pc = .l21 0 ∧ (stuckDL order).wsig 0 ≠ ((stuckDL order).w.wseq, .cs) ∧
      ∀ p, ((stuckDL order).r p).pc = .rem := by
  cases order <;> decide

/-- A writer waiting in line 21 for a signal that is not there does not change the state. -/
theorem wstep_l21_stuck {s : State n G} {i : Fin G} (hpc : s.w.pc = .l21 i)
    (hsig : s.wsig i ≠ (s.w.wseq, .cs)) : wstep s = s := by
  simp [wstep, hpc, hsig]

/-- **Line 47 as written violates Deadlock Freedom (Lemma 15 fails).** There is a reachable
configuration in which the only reader is in the remainder section and the writer is in its entry
section (waiting in line 21), such that in the infinite execution in which only the writer takes
steps (the reader may stay in the remainder section forever) the configuration never changes; in
particular no process ever enters the critical section and no passage is ever completed. This holds
for either order of the reads in line 51. -/
theorem deadlock_literal_line47 (order : ReadOrder) :
    ∃ s, Reachable (cfgDL order) s ∧ (∀ p, (s.r p).pc = .rem) ∧ (∃ i, s.w.pc = .l21 i) ∧
      ∀ k, exec (cfgDL order) (fun _ => writer) s k = s := by
  obtain ⟨hpc, hsig, hr⟩ := stuckDL_spec order
  refine ⟨stuckDL order, reachable_run _ .init _, hr, ⟨0, hpc⟩, fun k => ?_⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [exec, ih, step]
    exact wstep_l21_stuck hpc hsig

/-- Consequently, in that execution no process is ever in the critical section. -/
theorem deadlock_literal_line47_noCS (order : ReadOrder) :
    ∃ s, Reachable (cfgDL order) s ∧ ∀ k, ¬ (exec (cfgDL order) (fun _ => writer) s k).writerInCS ∧
      ∀ p, ¬ (exec (cfgDL order) (fun _ => writer) s k).readerInCS p ∧
        ((exec (cfgDL order) (fun _ => writer) s k).r p).pc = .rem := by
  obtain ⟨s, hs, hr, ⟨i, hpc⟩, hk⟩ := deadlock_literal_line47 order
  refine ⟨s, hs, fun k => ?_⟩
  rw [hk k]
  refine ⟨by simp [State.writerInCS, hpc], fun p => ⟨by simp [State.readerInCS, hr p], hr p⟩⟩

end Podc.RWLockRMRTradeoff.Alg
