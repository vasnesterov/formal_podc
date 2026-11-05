# Differences between the formalization and the paper

Paper: Jayanti, Jayanti, Joshi, *A Recoverable Mutex Algorithm with Sub-logarithmic RMR on Both CC
and DSM*, PODC 2019, arXiv 1904.02124v2.

## Statement-level issues (verdict rules from `verdicts.md`)

1. **Lemma 9 is false as stated (❌, rule R1).** It is a numbered lemma, and three conditions of
   its invariant fail in reachable configurations of crash-free runs with `k = 2`:
   - Condition 5, `qnode.CS_Signal = 0 ⇒ qnode.Pred ∈ {NIL, &Crash, &InCS}`: false after line 14
     (`PaperInv.cond5_csSignal_false`); also false at line 28 (`Pred = &Exit`, signal 0).
   - Condition 5, `qnode.NonNil_Signal = 0 ⇒ qnode.Pred = NIL`: false between lines 14 and 15
     (`PaperInv.cond5_nonNil_false`) and between lines 18 and 23.
   - Condition 4, third conjunct (`Pred` iterated at most `k` times reaches a distinguished value):
     false with two queued processes (`PaperInv.cond4_false`); `k + 1` would be needed.
   - Condition 18 uses `PC_π'` instead of `\hat{PC}_π'` (fails in the initial configuration);
     this one alone would be a typo with evident intent (Condition 19(g) has the hat).

   *Borderline call (R3).* The Condition 4 off-by-one and Condition 18 typo would be excusable,
   but the two Condition 5 conjuncts have no evident local fix in the paper (adding all node values
   and `&Exit` to the right-hand side would make them nearly vacuous). The proof in Appendix E
   claims the whole conjunction is inductive. We therefore classify Lemma 9 as ❌. It is not a
   headline (R5): the headline correctness claims (Theorem 2's RME properties) are true and proved
   here.

   *Reviewer check (rendered Figures 8–9).* Condition 5 is quantified over all `qnode ∈ 𝒩` with no
   PC guard and no restriction to a role; `𝒩` contains every node created at line 11, and
   `CS_Signal = 0` / `NonNil_Signal = 0` mean that no `set()` has been applied (a fresh node's
   signals have `State = 0`, Section 3.1). Condition 4's bound is the `k` of the `k`-ported
   algorithm. Reversing the two `= 0` implications would give true statements, but they are just
   contrapositives of Condition 5's `= 1` conjuncts, so that reading is not evidently intended; the
   printed conjuncts express the belief that the signals track `Pred` exactly ("`NonNil_Signal = 0`
   iff `Pred = NIL`"), which ignores the windows 14–15, 18–23 and 27–28. The `= 0` conjuncts are
   never used in Appendix E (only the `= 1` conjuncts are cited), and the step for line 14 does not
   re-check Condition 5. For Condition 4 the proof does reason with the wrong bound (step of line 14:
   "`b1 + b2 ≤ k`", which forgets that a fragment's head may be `SpecialNode` or an exited node that
   is nobody's `node_π`); it is only used for acyclicity (Condition 23's proof), where any finite
   bound suffices. So R3 does not excuse Condition 5, and R1 makes the false numbered Lemma 9 ❌
   even though Lemmas 4–8 are true (same treatment as Lemma 2(c) of ConstantBarriersMutex, PODC 2013).
   The paper's corrected invariant (Conditions 4, 5, 18 patched, all others as printed) was not
   checked; we prove our own invariant instead.
2. **Lemmas 4 and 5: proofs not established (🛠️).** Both proofs cite conditions of the false
   invariant (Conditions 15, 19), and Lemma 5's case "the queue is broken" is an informal induction
   over fragments. Statements proved with a new invariant and liveness argument.
3. **Theorem 2, RMR part (not formalized, not counted).** "O(1) for a process that does not crash
   during its passage" is literally false for a passage that starts with recovery (it runs `RLock`
   and scans all of `Node[]`); the intent is crash-free super-passages. "O(fk)" should be
   "O(1 + fk)".

## Modelling choices

- **Processes = ports.** One process per port `Fin k`. The paper has `n` processes and at most one
  per port per super-passage. A process only touches `Node[p]` of its port and loses its local
  state at every crash, so the projection onto ports is faithful for ME, SF, CSR, wait-free exit and
  wait-free CSR. RMR accounting per process (CC caches) is not modelled.
- **Granularity.** One shared access per step. Merged: lines 11–12 (allocation is local, so a crash
  between them only leaks a node); lines 16–17 into 10 (both read `Node[p]`, written only by `p`);
  local lines 20–21, 34, 37–38, 39–41 (as one nondeterministic step), 48 (with the read of
  line 46). Each read in lines 43, 44 and 46 is its own step.
- **Pseudo-nodes.** `&Crash`, `&InCS`, `&Exit`, `NIL` are constructors of `PV`. `SpecialNode` is
  node `0`, with `Pred = &Exit` and both signals set. `new QNode` returns the next fresh address.
- **Nondeterminism of lines 39–42.** `mypath`, `tailpath` may be any maximal path containing
  `mynode`, `tail`, and the loop of line 42 visits maximal paths in any order (`done` list). The
  paper says "the unique path"; we prove the invariant for every choice, and `step_total` shows a
  choice always exists (the scanned graph is acyclic).
- **Line 37 with `curpred = NIL`.** It cannot happen (`NonNil_Signal` was awaited at line 35); we
  treat it like the distinguished values (vertex only).
- **Signals.** Atomic bits inside the main algorithm. Theorem 1 is proved separately for the
  implementation of Figure 2, crash-free. The composition (Figure 2's non-atomic `set()`/`wait()`
  inside Figures 3–4, with crashes in the middle of a `set()` or `wait()`) is not verified; the
  paper does not prove it either beyond the remark that interrupted `set()`s are re-executed.
- **RLock.** Abstract lock variable `holder`: acquire if free or held by the caller (CSR), else
  busy-wait; release in its exit. Any acquisition order is allowed (covers every mutual exclusion
  lock with re-entry for safety). For starvation freedom the paper assumes a starvation-free RLock;
  with our abstract lock no assumption is needed because after the last crash only finitely many
  acquisitions happen. A concrete RLock with its own steps is not modelled.
- **Crash.** Sets the program counter to line 10 (non-idle) from any line, including the remainder
  section. This only adds obligations; it does not weaken the results.
- **Sections.** CS = `PC.cs` (the paper's `PC = 27`); its step executes line 27. Exit section =
  lines 28–29 (`b = 2` in Lemma 6). Try = everything else except the remainder section; the
  recovery code (including lines 22's execution of 28–29) is in Try, as in the paper.
- **Fairness.** `Fair`: a process not in the remainder section later takes a step or crashes
  (conditions (i)–(ii) of Section 1.2). `FinCrash`: finitely many crashes overall.
- **Lemma 7/8 formulations.** Lemma 7: after a crash in the CS, `p` is back in the CS within 3 own
  steps if it does not crash again. Lemma 8: from the crash until `p` re-enters the CS, no other
  process is in the CS (also with further crashes of `p`).

## Theorem 1 (Signal)

- Crash-free model, arbitrary invocations of `set()`/`wait()` by any processes, hypothesis that
  `wait()` executions never overlap. Linearization point of the first effective `set()`: the first
  completion of a `set()` or the first `wait()` reading `Bit = 1` (as in Appendix D). (iii): `set()`
  takes ≤ 3 steps (lines 2–3 merged). (iv): ≤ 4 more steps of a `wait()` once `State = 1`.
  (v): RMR counts on DSM and CC (ghost cache).
- With crashes and strict linearizability, (iv) can fail (`Signal.crash_spin`,
  `Signal.crash_rewait`): a `set()` crashing after line 1 leaves a waiter spinning with `Bit = 1`.
  The paper does not state Theorem 1 for crashes, and the main algorithm re-executes every
  interrupted `set()`; not counted as a mistake.

## Not formalized

- The RMR complexity bounds of Theorem 2 and all of Theorem 3 (arbitration tree via Golab–Hendler
  Section 5).
- Appendix A's two scenarios against Golab–Hendler's PODC'17 algorithm.
