# Two-Bit Messages Suffice for Atomic Registers — PODC 2016

Achour Mostéfaoui, Michel Raynal. *Two-Bit Messages are Sufficient to Implement Atomic Read/Write
Registers in Crash-prone Systems.* PODC 2016. DOI
[10.1145/2933057.2933095](https://doi.org/10.1145/2933057.2933095). Formalized version: arXiv
[1602.02695](https://arxiv.org/abs/1602.02695) v1 (the only version); numbering follows it.

**Verdict: ✅ Correct.** The algorithm of Figure 1 implements a linearizable SWMR register in
`CAMP_{n,t}[t < n/2]`, and every operation of a correct process terminates. Messages carry a two-bit
type, plus a value for two of the four types. **FIFO channels are not needed**: the parity bit and the
`wait` at line 11 form an alternating-bit protocol. Correctness relies on the implicit (standard)
convention that code between two `wait`s runs atomically. The proofs have one gap and a few slips, none
affecting the result.

## Mistakes in the paper

* **Implicit convention, necessary for correctness.** The paper never says how an operation's code
  interleaves with the message handlers. We use the standard convention for this pseudo-code: each
  block between two `wait`s is atomic. Without it the algorithm is wrong. Suppose a `WRITE` handler
  runs between lines 1 and 2 of `write()`. Then the writer can send the same `WRITE(b, v_x)` twice
  to one process: once at line 16, while it handles a late echo of `v_{x−1}`, and again at line 2.
  The stale copy later passes the parity test as message `x + 2`, and the receiver appends a wrong
  value to its history. Our model checker found a 14-step execution with `n = 3`, `t = 1`, no crashes,
  no reads and three writes, in which `p2` accepts the stale `WRITE(0, v2)` as its 4th value.
  Recorded as a convention, not an error.
* **Gap in the proof of Lemma 5; statement true.** The case analysis for a pair `(i, j)` considers
  `p_i` invoking `write` and `p_i` receiving a `WRITE` from `p_j`. It omits `p_i` receiving a `WRITE`
  from a third process `p_k`. That reception may raise `w_sync_i[i]` (line 14) and send a `WRITE` to
  `p_j` (line 15), changing the premises of R1/R2. The induction also needs the hypothesis "at most
  two unprocessed `WRITE`s per channel, with different parities". This is what makes the parity test
  of line 11 pick the right message. We prove an exact invariant covering both points (`lemma5`,
  `lemma5_sent`).
* **Unargued step in Lemma 9.** Channels are not FIFO and `READ()`/`PROCEED()` carry no sequence
  number, so "`r_sync_i[j] = rsn` means `p_j` answered the *current* request" needs proof; the paper
  only asserts it. It holds: each `READ()` is at all times in exactly one place (in transit, a pending
  handler, a `PROCEED()` in transit, or already counted).
* **Lemma 10, two harmless imprecisions.**
  * Claim 2 says `w_sync_k[k] = x` when the read starts; only `≥ x` is true, and only `≥ x` is used.
  * Claim 3 asserts a *correct* process in the intersection of two `(n − t)`-quorums. This does not
    follow: with `n = 3`, `t = 1`, quorums `{1,2}` and `{2,3}`, `p_2` may be faulty. Correctness of
    that process is never used.
* **Theorem 2's message complexity** (`O(n)` per read, `O(n²)` per write) holds only amortized.
  Catch-up messages for old values (line 16) may be sent long after the write returned. We prove the
  amortized bounds.
* **Index slips.**
  * Claim 3: "computed by `p_i`" should be `p_j`.
  * Claim 2: `i` and `j` are mixed in the quorum `Q_w`.
  * Lemma 8: `w_sync_i[i] ≥ w_sync_w[i]` should be `w_sync_w[i] ≥ wsn`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Finitely many asynchronous deterministic processes; the writer `w` and readers `p ≠ w`. The writer
  does not read; the paper only remarks that its reads are local.
* A complete network of reliable, **unordered** channels (a multiset of in-transit messages).
* Crash failures. Messages of crashed senders may be dropped (a crash mid-broadcast), but dropping is
  never forced.
* Safety is proved for *any* number of crashes. Liveness assumes at most `t` crashes, `2t < n`, and
  weak fairness for steps of correct processes (this includes reliable delivery).
* Each block of code between `wait`s is one atomic transition. A `WRITE` that fails the parity test
  of line 11 stays in the channel.
* Atomicity is CSLib's linearizability (amended Herlihy–Wing) for a register. Pending operations may
  or may not be linearized. No randomness, no timing.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Figure 1 | `alg` | `Algorithm.lean` |
| Theorem 1, safety (atomicity) | `linearizable` | `Safety.lean` |
| Theorem 1, liveness | `live` | `Liveness.lean` |
| Lemma 1 | `lemma1` | `LivenessSteps.lean` |
| Lemmas 4, 5, 10 | `lemma4`, `lemma5`, `lemma10` (alternating-bit invariant `InvW`) | `Safety.lean`, `InvWrite.lean` |
| Lemma 5 on messages actually sent | `lemma5_sent` | `Messages.lean` |
| Lemmas 8, 9 (termination) | `write_terminates`, `read_terminates` (read pipeline invariant `InvP`) | `Liveness.lean`, `InvRead.lean` |
| Theorem 2: two control bits | `Msg.ext_ctrl_payload` | `Algorithm.lean` |
| Theorem 2: amortized message counts | `write_messages` (`≤ n(n−1)` per write), `read_messages` (`≤ 2(n−1)` per read) | `Messages.lean` |

**Not formalized.** The time complexity (`2Δ` per write, `4Δ` per read, Table 1); the model is untimed.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `Sanity.lean` gives a concrete 17-step run (`n = 3`, write 5 then read 5),
extends it to a fair 1-resilient infinite execution (`fair_exec_exists`), and applies `live` and
`linearizable` to it. The explicit-state model checker [`scripts/twobit_mc.py`](scripts/twobit_mc.py)
finds no violation for the paper's algorithm and reproduces the counterexample above for non-atomic
lines 1–2. The message-passing model and the SWMR reads-from linearizability criterion are in CSLib
(`Cslib/Computability/Distributed/MessagePassing/{Async,FairExec}.lean`,
`Cslib/Computability/Distributed/SharedMemory/SWMRRegister.lean`).
