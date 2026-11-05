# Recoverable Mutex with Sub-logarithmic RMR on CC and DSM — PODC 2019

Prasad Jayanti, Siddhartha Jayanti, Anup Joshi. *A Recoverable Mutex Algorithm with Sub-logarithmic
RMR on Both CC and DSM.* PODC 2019. DOI
[10.1145/3293611.3331634](https://doi.org/10.1145/3293611.3331634). Formalized version: arXiv
[1904.02124](https://arxiv.org/abs/1904.02124) v2 (full version, proofs in Appendices C–E);
numbering follows it.

**Verdict: ❌ False claim.** The `k`-ported algorithm of Figures 3–4 is correct. We prove mutual
exclusion, starvation freedom (finitely many crashes), wait-free exit, wait-free critical-section
re-entry and critical-section re-entry (Lemmas 4–8), and Theorem 1 on the Signal object. But Lemma 9,
the 39-condition invariant on which all the correctness proofs rest, is false as stated: several of
its conditions fail in crash-free runs with two processes. We replace it with our own invariant.

## Mistakes in the paper

### ❌ Lemma 9 (the invariant of Figures 8–14)
Lemma 9 claims that all 39 conditions hold in every configuration, but Condition 5 fails as soon as
one process has executed line 14 in a crash-free run (`PaperInv.cond5_csSignal_false`,
`PaperInv.cond5_nonNil_false`), and Condition 4 fails once two processes are queued
(`PaperInv.cond4_false`).

**Impact.** The proofs of Lemmas 4 and 5 (mutual exclusion and starvation freedom) cite conditions
of this invariant, so they are not established by the paper. The algorithm itself is correct: we
prove Lemmas 4–8 from a new invariant (`inv_reach`).

**Details.**
- Condition 5 says `qnode.CS_Signal = 0 ⇒ qnode.Pred ∈ {NIL, &Crash, &InCS}`. Every waiting node
  (lines 15 and 25) has `CS_Signal = 0` and `Pred` pointing to its predecessor. So does an exiting
  node at line 28, with `Pred = &Exit`.
- Condition 5 also says `qnode.NonNil_Signal = 0 ⇒ qnode.Pred = NIL`. Between lines 14 and 15 (and
  between lines 18 and 23 after a crash) `Pred` is already set while `NonNil_Signal` is still `0`.
- Condition 4 asks that `Pred` be iterated at most `k` times from a node to reach
  `{NIL, &Crash, &InCS, &Exit}`. With `k = 2` and both processes queued behind `SpecialNode`, the
  second node needs 3 hops (node → first node → `SpecialNode` → `&Exit`). The bound should be
  `k + 1`.
- The fixes are not evident from the paper: for Condition 5 one would have to add node values and
  `&Exit` to the right-hand side, which makes the conjunct nearly empty. Reversing the
  implications gives true statements, but they merely restate Condition 5's `= 1` conjuncts. The
  proof of Lemma 9 (Appendix E) claims that the conjunction of all conditions is preserved by every
  step, but never re-checks Condition 5 at line 14. Its Condition 4 case counts `b1 + b2 ≤ k` and
  forgets the fragment's head (`SpecialNode` or an exited node).

**Repair.** Our invariant (`Inv`, `InvDefs.lean`) is preserved by every step and crash
(`inv_reach`); Lemmas 4–8 follow from it.

### Typos and slips
- Condition 18 quantifies over the real program counter `PC_π'` where `\hat{PC}_π'` is meant (as
  in Condition 19(g)). Read literally it fails in the initial configuration, where every `PC_π = 10`.
- Theorem 2 claims `O(1)` RMRs "for a process that does not crash during its passage". A passage
  that starts after a crash runs `RLock` and the repair scan of all `k` entries of `Node[]`, even
  if no crash happens during it. The intended statement is about crash-free super-passages, and
  `O(fk)` should read `O(1 + fk)`. Not formalized.

## Proof gaps (statements true)

### 🛠️ Lemma 4 (Mutual Exclusion)
The proof is one line from Condition 19 of the (false) Lemma 9 invariant.

**Impact.** Statement true; proved from our invariant (`mutual_exclusion`).

**Details.** The new invariant's core: every node has at most one successor, nobody is behind
`Tail`, and at most one node "holds the right to the CS" (`InH`). A node holds it if it is in the
CS, is behind a released node, or is exiting with a successor. The hard part is the repair code
(lines 30–49). We characterise what the non-atomic scan of `Node[]` still says when the decision
at line 46 is taken. It uses a ghost set of nodes that had already done their `FAS` when `Tail`
was read (line 31): every later node hangs behind that `Tail` value. Then the `FAS` branch never
creates a cycle. In the attach branch, the chosen predecessor has no successor and is not `Tail`.
If `headpath = NIL`, nobody holds the right to the CS (`ScanInv.fas_facts`,
`ScanInv.attach_facts`, `ScanInv.none_noH`).

### 🛠️ Lemma 5 (Starvation Freedom)
The proof uses Conditions 15 and 19 of the false invariant, and an informal argument ("applying
the above argument inductively on these fragments …") for the case where the queue is broken.

**Impact.** Statement true under finitely many crashes and the paper's fairness conditions;
proved (`starvation_freedom`).

**Details.** After the last crash, every recovering process gets through `RLock`. The repair
terminates: the waits at line 35 end, and the loop over maximal paths is finite. Eventually nobody
is in the recovery code or in `RLock` (`eventually_no_rec`). From then on, the unique holder of
the right to the CS is an ancestor of every waiting node. A rank (10 × number of unreleased
ancestors + stage of the holder) never increases and drops at every step of the holder
(`token_step`, `phase2_cs`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory with NVRAM and individual crash–recovery failures. A crash resets the
  program counter to line 10 and erases all local variables. Shared memory is unaffected.
  Deterministic algorithm; executions are arbitrary interleavings of steps and crashes (an
  adversarial scheduler).
- One process per port (`Fin k`). The paper's `n ≥ k` processes are allowed one super-passage per
  port at a time. A process accesses only `Node[p]` of its own port, and its local state is wiped
  at every crash. So identifying processes with ports loses nothing for the properties proved.
- One shared-memory access per step. Lines 11–12 form one step (allocation and `Node[p] ← mynode`),
  and lines 16–17 are merged into line 10. Lines 39–41 and the order of the loop at line 42 are
  nondeterministic (any maximal path, any order), and all results hold for every resolution.
- Signal objects are atomic bits (`set` = one write, `wait` = busy-wait reads). Theorem 1 treats
  the implementation of Figure 2 separately.
- `RLock` is an abstract lock variable: line 24 acquires it if it is free or already held by the
  caller (re-entry after a crash), and otherwise busy-waits. Any order of acquisition is allowed, so
  the safety results hold for every mutual exclusion lock with re-entry. Starvation freedom needs no
  fairness assumption on `RLock`: after the last crash only finitely many acquisitions remain.
- Liveness: runs are infinite sequences of events. Fairness (`Fair`) is the paper's run condition:
  a process outside the remainder section later takes a step or crashes. `FinCrash` says that
  only finitely many crashes occur.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 4 (Mutual Exclusion) | `mutual_exclusion` | `Safety.lean` |
| Lemma 5 (Starvation Freedom) | `starvation_freedom` | `Liveness.lean` |
| Lemma 6 (Wait-free Exit, `b = 2`) | `wait_free_exit` | `Safety.lean` |
| Lemma 7 (Wait-free CSR, `b = 3`) | `wait_free_csr` | `Safety.lean` |
| Lemma 8 (Critical Section Reentry) | `cs_reentry` | `Safety.lean` |
| Lemma 9 (false as stated) | `PaperInv.cond5_csSignal_false`, `PaperInv.cond5_nonNil_false`, `PaperInv.cond4_false` | `PaperInv.lean` |
| Replacement invariant | `Inv`, `inv_reach` | `InvDefs.lean`, `Invariant.lean` |
| Theorem 1 (i)–(v) (Signal, crash-free) | `Signal.theorem1_i_linearization_point`, `Signal.theorem1_i_set_completes`, `Signal.theorem1_ii`, `Signal.theorem1_iii`, `Signal.theorem1_iv`, `Signal.theorem1_v_set`, `Signal.theorem1_v_wait_dsm`, `Signal.theorem1_v_wait_cc` | `Signal.lean` |
| Non-vacuity (every process can step; fair runs exist) | `step_total`, `exists_run`, `exists_fair_run` | `NonVacuity.lean` |

**Remark on Theorem 1.** It is proved for crash-free executions (Section 2 does not mention crashes)
with linearization point "first completed `set()` or first `wait()` that reads `Bit = 1`".
With crashes, a `set()` that crashes after line 1 leaves a spinning waiter with `Bit = 1`
(`Signal.crash_spin`, `Signal.crash_rewait`), so (iv) needs the interrupted `set()` to be
re-executed. The algorithm of Figures 3–4 always does this (lines 22–23).

**Not formalized.** The RMR bounds of Theorem 2, Theorem 3 (arbitration tree), and the two
scenarios of Appendix A against Golab–Hendler's algorithm.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Before the Lean proof, explicit-state model checking (`modelcheck/`) confirmed
mutual exclusion for `k = 3` with up to 2 crashes and 5 passages (12.4M states), and starvation
freedom for `k = 2` with up to 2 crashes. The candidate invariant was checked on all reachable
states for `k ≤ 4` with bounded crashes and passages. These Python scripts (no dependencies;
`python3 mc.py K MAXCRASHES [live]`, `python3 inv.py ...`) are a sanity check only and use a FIFO
`RLock`. Paper-local model; no CSLib dependency.
