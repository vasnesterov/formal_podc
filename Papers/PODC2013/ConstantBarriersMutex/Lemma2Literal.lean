import Papers.PODC2013.ConstantBarriersMutex.Model

/-!
# Lemma 2 (b) and (c) of the paper fail under TSO as stated

Lemma 2 claims, for every reachable configuration `C`:

* (b) "If `pc(C, p) = 48`, then the lock owner is some process `q`, where `q`'s identifier was
  dequeued by `p` in statement 45 of its current passage."
* (c) "`|{r | C.signal[r] = true ∧ 17 < pc(C, r) < 49}| ≤ 1`. If there is such a process `r`,
  then `r` owns the lock in `C` …"

Here `C.v` is the value of the shared variable `v` in the configuration, i.e. the *memory* value
(Section 3: a configuration contains the local states, the store buffers and the value of each
shared variable), and `pc(C, p)` is the next statement `p` will *issue*. The proof of Lemma 2
treats every write as performed when it is issued (sequential consistency). Under TSO:

* (b) fails when `lock ← next` (statement 47) is still in `p`'s store buffer at `pc = 48`
  (`lemma2b_false`, 2 processes, 31 events).
* (c) fails because a process that was signalled in an earlier passage keeps `signal[r] = true` in
  memory after issuing `signal[r] ← false` (statement 17) until that write is performed
  (`lemma2c_false`, 2 processes, 80 events: both processes have `signal = true` in memory and
  `17 < pc < 49`).

The corrected invariants (with "performed" in place of "issued") are proved in `Invariant.lean`.
-/

namespace Podc.ConstantBarriersMutex

/-- The configuration reached by a finite list of events. -/
def exec {h : ℕ} (l : List (Ev h)) : Cfg h := l.foldl Cfg.next Cfg.init

lemma reachable_exec {h : ℕ} (l : List (Ev h)) : Reachable (exec l) := by
  unfold exec
  induction l using List.reverseRecOn with
  | nil => exact Reachable.init
  | append_singleton l e ih => rw [List.foldl_append]; exact Reachable.next e ih

/-- The statement numbers `18, …, 48` as program counters (`17 < pc < 49`). -/
def PC.Between17And49 {h : ℕ} (c : PC h) : Prop := c.Entry ∨ c = .cs ∨ c.Exit

instance {h : ℕ} (c : PC h) : Decidable c.Between17And49 := by
  unfold PC.Between17And49; infer_instance

/-- The execution refuting Lemma 2(b). -/
def evB : List (Ev 1) :=
  [.step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .step 0,
   .step 0, .step 0, .step 0, .step 0, .step 0, .step 1, .flush 1, .step 1, .flush 1, .step 1,
   .flush 1, .step 0, .step 0, .step 0, .step 0, .step 0, .step 0, .step 0, .step 0, .step 0,
   .step 0]

/-- **Lemma 2(b) is false under TSO**: process `0` is at statement 48 after dequeuing `1`, but
the lock (in memory) is still `0`, because the write of statement 47 is still buffered. -/
theorem lemma2b_false :
    ∃ s : Cfg 1, Reachable s ∧ ∃ p nx, s.pc p = .x48 nx ∧ s.mem.lock ≠ some nx := by
  refine ⟨exec evB, reachable_exec _, 0, 1, ?_, ?_⟩ <;> decide

/-- The execution refuting Lemma 2(c). -/
def evC : List (Ev 1) :=
  [.step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .step 0,
   .step 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .step 0, .step 1, .flush 1, .step 1,
   .flush 1, .step 1, .flush 1, .step 0, .step 0, .step 0, .step 0, .flush 0, .step 0, .flush 0,
   .step 0, .step 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0,
   .step 0, .step 0, .flush 0, .step 0, .flush 0, .step 1, .flush 1, .step 1, .step 1, .step 1,
   .step 1, .step 1, .step 1, .step 1, .step 1, .step 1, .flush 1, .step 1, .flush 1, .step 1,
   .step 1, .step 1, .step 1, .step 1, .step 1, .flush 1, .step 1, .flush 1, .step 1, .step 1,
   .step 1, .flush 1, .step 1, .flush 1, .step 1, .flush 1, .step 1, .flush 1, .step 1, .step 1]

/-- **Lemma 2(c) is false under TSO**: both processes have `signal = true` in memory and are
between statements 17 and 49 (process `1` has issued `signal[1] ← false`, which is still in its
store buffer; process `0` was handed the lock and signalled). -/
theorem lemma2c_false :
    ∃ s : Cfg 1, Reachable s ∧ ∃ p q, p ≠ q ∧ s.mem.signal p = true ∧ s.mem.signal q = true ∧
      (s.pc p).Between17And49 ∧ (s.pc q).Between17And49 := by
  refine ⟨exec evC, reachable_exec _, 0, 1, by decide, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### Lemma 2(c) fails even under sequential consistency -/

/-- The schedule is sequentially consistent: every issued write is performed by the very next
event (before the event, at most one buffer is non-empty and the event performs its write). -/
def SCSched {h : ℕ} : Cfg h → List (Ev h) → Prop
  | _, [] => True
  | s, e :: l => (∀ q, s.buf q = [] ∨ e = .flush q) ∧ SCSched (s.next e) l

instance {h : ℕ} (s : Cfg h) (l : List (Ev h)) : Decidable (SCSched s l) := by
  induction l generalizing s with
  | nil => exact isTrue trivial
  | cons e l ih =>
    have := ih (s.next e)
    unfold SCSched; infer_instance

/-- A sequentially consistent execution refuting Lemma 2(c): process `1` was promoted and
signalled in its previous passage (`signal[1] = true`), and in its current exit section it has
dequeued process `0` and performed `lock ← 0` (statement 47); now `pc(1) = 48`, so `1` is in the
set `{r | signal[r] ∧ 17 < pc(r) < 49}` but does not own the lock. -/
def evC2 : List (Ev 1) :=
  [.step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .step 0,
   .step 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .step 0, .step 1, .flush 1, .step 1,
   .flush 1, .step 1, .flush 1, .step 0, .step 0, .step 0, .step 0, .flush 0, .step 0, .flush 0,
   .step 0, .step 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0, .step 0, .flush 0,
   .step 0, .step 0, .flush 0, .step 0, .flush 0, .step 1, .flush 1, .step 1, .step 1, .step 1,
   .step 1, .step 1, .step 1, .step 1, .step 1, .step 1, .flush 1, .step 1, .flush 1, .step 1,
   .step 1, .step 1, .step 1, .step 1, .step 1, .flush 1, .step 1, .flush 1, .step 1, .step 1,
   .step 1, .flush 1, .step 1, .flush 1, .step 1, .flush 1]

/-- **Lemma 2(c) is false, even under sequential consistency.** In a sequentially consistent
execution with 2 processes, process `1` has `signal[1] = true` and `pc(1) = 48` (between 17 and
49), but the lock is owned by process `0`. -/
theorem lemma2c_false_sc :
    SCSched Cfg.init evC2 ∧ (∀ q, (exec evC2).buf q = []) ∧
      (exec evC2).mem.signal 1 = true ∧ (exec evC2).pc 1 = .x48 0 ∧
      (exec evC2).mem.lock = some 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · intro q; revert q; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end Podc.ConstantBarriersMutex
