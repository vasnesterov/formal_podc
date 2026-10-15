# Two-Bit Messages are Sufficient to Implement Atomic Read/Write Registers in Crash-prone Systems (PODC 2016)

Achour Mostéfaoui, Michel Raynal. PODC 2016, pp. 381–389, DOI 10.1145/2933057.2933095.
- Formalized version: **arXiv:1602.02695v1** (the only arXiv version). The local copy
  `papers/2016/2933057.2933095_Two_Bit_Messages_are_Sufficient_to_Implement_Atomic_Read_Write_Registe.pdf`
  is that arXiv version.
- Numbering below follows it.

## Status

**Complete. No `sorry`, no axioms.**
- `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for the theorems
  checked: `linearizable`, `live`, `lemma1`, `lemma4`, `lemma5`, `lemma5_sent`, `lemma10`,
  `write_messages`,
  `read_messages`, `Sanity.run_spec` and `Sanity.fair_exec_exists`.
- Build with `lake build Papers.PODC2016.TwoBitRegisters.Sanity Papers.PODC2016.TwoBitRegisters.Messages`.
- The lean-lsp MCP was unavailable during this work; everything was checked with
  `lake env lean` and single-module builds.

**Verdict: the paper is correct.** Figure 1 implements an atomic SWMR register in
`CAMP_{n,t}[t < n/2]`. Messages carry only a two-bit type (plus a value for two of the four
types), and every operation of a correct process terminates.
- **FIFO channels are not needed.** This was flagged during screening.
  - Channels are modelled as unordered multisets.
  - The parity bit plus the `wait` of line 11 form an alternating-bit protocol. The invariant
    `InvW` shows that at most two unprocessed `WRITE`s per channel exist, with different parities.
  - The non-FIFO `READ()`/`PROCEED()` counting is sound by the pipeline invariant `InvP`.
- **One implicit but necessary convention** (standard for Raynal-style pseudo-code, not an
  error): each block of code between two `wait`s executes atomically.
  - Suppose a `WRITE` handler could run between lines 1 and 2 of `write()`.
  - The writer can then send the same `WRITE(b, v)` twice to a process.
  - The stale copy is later accepted as a newer value.
  - Our model checker found a 14-step counterexample: `n = 3`, no crashes, 3 writes.
  - See `differencies.md` §1.
- **A gap in the proof of Lemma 5:** a `WRITE` from a third process `p_k` is not considered
  (see `differencies.md` §3). The statement is true.
- **Two harmless imprecisions in the proof of Lemma 10:**
  - Claim 2 has "`= x`" where "`≥ x`" is meant.
  - Claim 3 claims a *correct* process in the intersection of two quorums, which does not follow
    and is not needed.
- **The informal "alternating bit" arguments are replaced by invariants.** The paper argues
  Lemmas 4 and 5 and the `PROCEED` counting informally.

See `differencies.md` for the complete list.

## Model (explicit)

Model `CAMP_{n,t}[t < n/2]`: `Cslib/Computability/Distributed/MessagePassing/Async.lean` (generic) and `Algorithm.lean`
(the algorithm).
- **Processes:**
  - finitely many: `[Fintype P]`, `n = Fintype.card P`;
  - asynchronous and deterministic;
  - `w` is the writer;
  - every process `p ≠ w` may read; the writer does not read (see `differencies.md`).
- **Communication:**
  - complete network of reliable, **unordered** (non-FIFO), asynchronous channels;
  - `net` is the multiset of in-transit `(sender, receiver, message)`.
- **Crash failures:**
  - a crashed process takes no further step;
  - messages *of crashed senders* may be lost (`drop`). This models a crash in the middle of a
    broadcast and is never forced.
  - Safety holds for any number of crashes. Liveness assumes at most `t` crashes
    (`Exec.Resilient t`) and `2t < n`.
- **Atomicity of local code:** each block of code between two `wait`s is one transition.
  - A message whose handler would block at line 11 stays in the channel.
  - A `READ()` handler waiting at line 20 is a pending task.
- **Fairness** (`Exec.Fair`), for liveness only. Weak fairness for internal actions and
  receptions of correct processes: a step that stays enabled forever is eventually taken. For
  receptions this is channel reliability.
  - Correct = never crashes.
  - Fair executions with completed operations exist: `Sanity.fair_exec_exists`.
- **Histories:**
  - CSLib `Label`s (`inv`/`ret`);
  - atomicity is `Cslib.SharedMemory.IsLinearization` for `register V v₀` (the amended
    Herlihy–Wing linearizability);
  - pending operations may or may not be linearized.
- **No randomness, no adversary beyond the scheduler, no time bounds.**

## Main results ↔ Lean

| Paper | Lean | File |
|---|---|---|
| Figure 1 (algorithm) | `alg w t v₀ : Protocol P (register V v₀) (Loc P V) (Msg V) (Act P)` | `Algorithm.lean` |
| Theorem 2 (two control bits) | `Msg.ext_ctrl_payload` | `Algorithm.lean` |
| Lemma 1 | `lemma1` | `LivenessSteps.lean` |
| Lemma 2 | `lemma2` | `Safety.lean` |
| Lemma 3 | `lemma3` | `Safety.lean` |
| Lemma 4 | `lemma4` | `Safety.lean` |
| Lemma 5, R1/R2 on messages actually sent | `lemma5_sent` | `Messages.lean` |
| Lemma 5, channel contents (exact form; Properties P1/P2) | `lemma5`, `InvW` | `Safety.lean`, `InvWrite.lean` |
| Lemma 6 | `Liveness.lemma6` | `Liveness.lean` |
| Lemma 7 | `Liveness.recv_progress` | `Liveness.lean` |
| Lemma 8 | `Liveness.write_terminates` | `Liveness.lean` |
| Lemma 9 | `Liveness.read_terminates` (`READ()` pipeline: `Liveness.pipeline`, `InvP`) | `Liveness.lean`, `InvRead.lean` |
| Lemma 10 (Claims 1–3) | `lemma10` | `Safety.lean` |
| Theorem 1, safety | `linearizable : (alg w t v₀).Linearizable` (assumes `2 * t < n`) | `Safety.lean` |
| Theorem 1, liveness | `live : (alg w t v₀).Live t` (assumes `2 * t < n`) | `Liveness.lean` |
| Theorem 2 (message complexity, amortized) | `write_messages` (`≤ n(n−1)` per write), `read_messages` (`≤ 2(n−1)` per read) | `Messages.lean` |
| (sanity) | `Sanity.run_spec`, `Sanity.fair_exec_exists`, examples applying `live` and `linearizable` | `Sanity.lean` |

Not formalized: the time complexity (`2Δ`/`4Δ`, Table 1), since the model is untimed.

## Files

- `Algorithm.lean`: messages (4 types), local states, transitions, `alg`.
- `Steps.lean`: characterization lemmas of the individual transitions.
- `InvWrite.lean`: `InvW`, the alternating-bit invariant (Lemmas 1–5); `invW_of_reach`.
- `InvRead.lean`: `InvP`, the `READ()`/`PROCEED()` pipeline invariant; `invP_of_reach`.
- `InvHist.lean`: `InvH`, the history invariant with a ghost state; `invH_of_reach`.
  - The ghost state holds the read snapshots `snap` and the reads-from map `rf`.
  - The quorum intersection at line 8 is `InvH.of_r8`.
- `Safety.lean`: Lemmas 2–5, 10, Theorem 1 (safety).
- `LivenessSteps.lean`, `Liveness.lean`: Lemmas 6–9, Theorem 1 (liveness).
- `Messages.lean`: Theorem 2 message counts (invariant `InvM` on the ghost log `C.sent`).
- `Sanity.lean`: a concrete 17-step run with `n = 3` (write 5, then read 5); its extension to
  an infinite fair execution; the main theorems applied to it.
- `scripts/twobit_mc.py`: explicit-state model checker. It checks safety via the three claims
  and checks for liveness deadlocks. Variants:
  - `paper`: no violation;
  - `noparity`: violation (sanity check of the checker);
  - `split12`: non-atomic lines 1–2, violation.

## Infrastructure (CSLib candidates)

- `Cslib/Computability/Distributed/MessagePassing/Async.lean` (now in CSLib): a generic asynchronous crash-prone
  message-passing model implementing a CSLib `ObjSpec`.
  - `Protocol`, `Config` (with a `sent` log), `Step`, `step`, `Reach`, `Linearizable`;
  - infinite executions `Exec`, `Correct`, `Fair`, `Resilient`, `OpsTerminate`, `Live`;
  - progress lemmas `Exec.eventually_gt`/`eventually_ge`/`eventually_lt`/`eventually_zero`;
  - `card_faulty_le`, `crashed_mono`, `hist_prefix`.
- `Cslib/Computability/Distributed/MessagePassing/FairExec.lean` (now in CSLib): finite runs `runFrom`.
  `exists_fair_exec_of_quiescent` extends a run that ends quiescent to a fair execution.
- `Cslib/Computability/Distributed/SharedMemory/SWMRRegister.lean` (now in CSLib): the SWMR reads-from linearizability
  criterion `SWMRReadsFrom.isLinearization`, which generalizes CSLib's SWSR criterion to many
  readers. It also has:
  - invocation order `invIds`;
  - `WellFormed.append_inv`/`append_ret`;
  - `precedes_append_inv_iff`, `Precedes.not_of_invoked`.
