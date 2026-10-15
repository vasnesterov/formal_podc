# Differences between the formalization and the paper

Paper: A. Mostéfaoui, M. Raynal, *Two-Bit Messages are Sufficient to Implement Atomic Read/Write
Registers in Crash-prone Systems*, PODC 2016 (arXiv:1602.02695v1; the arXiv version has a single
version, identical in content to the local copy). Numbering follows the arXiv version.

**Verdict.** The main result is correct. The algorithm of Figure 1 implements an atomic
(linearizable) SWMR register in `CAMP_{n,t}[t < n/2]` with four message types, and every
operation of a correct process terminates. **FIFO channels are not needed.** Screening asked
whether the paper silently relies on FIFO channels. It does not. Channels are modelled as
unordered multisets, and the parity bit plus the `wait` at line 11 (an alternating-bit protocol)
handle reordering. The pairwise invariant behind this (our `InvW`, Lemma 5 in exact form) shows
that at most two `WRITE` messages are unprocessed per channel, with different parities.

The algorithm relies on an **implicit convention**: code between two `wait`s executes atomically
(§1). This is the standard convention of Raynal's pseudo-code, not an error, but we record it
because the algorithm is incorrect without it. The other items are proof imprecisions or gaps that
the formal proof closes, small slips, harmless generalizations and modelling choices.

## 1. Implicit convention: code blocks between `wait`s are atomic (necessary)

The paper does not say explicitly how the code of an operation interleaves with the message
handlers (`when ... is received do`). We follow the standard convention of this style of
pseudo-code: each block of code between two `wait` statements runs atomically. So lines 1–2, lines 5–6, lines 8, 10, lines 11–18, line 19,
lines 20–21 and line 22 are each one transition (`Algorithm.lean`).

**This convention is necessary.** Suppose a `WRITE` handler may run between lines 1 and 2 of
`write()`. Then the writer can send the same `WRITE(b, v_x)` twice to the same process: once at
line 16, while it handles a late echo of `v_{x-1}`, and once more at line 2. The stale copy later
passes the parity test as message number `x + 2`, and the receiver appends a wrong value to its
history.

Our explicit-state model checker (`scripts/twobit_mc.py`, variant `split12`) finds this
14-step counterexample with `n = 3`, `t = 1`, no crashes and no reads:

1. The writer completes `write(v1)`.
2. It starts `write(v2)`: line 1 sets `w_sync_w[w] = 2`.
3. It processes `p2`'s echo `WRITE(1, v1)`. Since `wsn = 1 < 2`, line 16 sends `WRITE(0, v2)` to
   `p2`.
4. Line 2 sends `WRITE(0, v2)` to `p2` again, because `w_sync_w[2] = 1`.
5. `p2` processes one copy of `WRITE(0, v2)`.
6. After `write(v3)`, `p2` accepts the stale `WRITE(0, v2)` as its 4th value, before `write(v4)`
   is even invoked.

With atomic blocks (variant `paper`), the checker finds no violation of safety or liveness on all
instances we tried:
- `n = 3`: up to 3 writes; 1–2 readers; up to 2 reads per reader; 0–1 crashes.
- `n = 4`: 1 write and 1 read.

The theorems in Lean prove correctness in general.

## 2. Model choices (generalizations or equivalent reformulations)

- **Channels.** A channel is the multiset `net` of in-transit messages `(sender, receiver, msg)`.
  It is unordered, does not lose messages and does not create them.
  - Messages *of a crashed sender* may be dropped (step `drop`). This models a crash in the
    middle of a broadcast, which the paper mentions for line 6. It is a generalization:
    dropping is never forced.
- **Handlers blocked at a `wait`.** A received `WRITE(b, v)` whose parity test (line 11) fails
  stays in the channel. This cannot be distinguished from a handler blocked at line 11, because
  the handler has done nothing yet.
  - A `READ()` handler blocked at line 20 is an explicit pending task `(j, sn)`. Its `sn` is
    saved at reception (line 19), as in the paper.
- **Crashes.** A crash step stops a process forever. Safety holds for *any* number of crashes;
  only the quorum size `n - t > n/2` is used. Liveness assumes that at most `t` processes crash
  (`Exec.Resilient t`).
- **Fairness / reliable delivery** (`Exec.Fair`). Weak fairness for the steps of correct
  processes: an internal action (the end of a `wait`), or the reception of a message by a correct
  process, that stays enabled forever is eventually taken. For receptions this is exactly
  channel reliability; for internal actions it is "processes are not infinitely slow".
- **Correct processes.** A correct process is one that never crashes in the execution. The
  paper's Lemmas 8 and 9 say "if the process does not crash during the operation". In an
  infinite execution this is equivalent: an operation that never returns of a process that does
  not crash during it belongs to a process that never crashes.
- **The writer does not read.** Read operations are allowed for all processes except the writer
  `w`. The paper only remarks that "the writer can directly return `history_w[w_sync_w[w]]`"
  (Figure 1, comment of `read()`).
  - Any process `p ≠ w` may read; this is the paper's SWMR setting minus the writer's own reads.
  - Supporting the writer's reads would only need a slightly more general reads-from criterion
    (writes would have to be identified among the writer's operations).
- **Values.** The value type `V` must have decidable equality (`[DecidableEq V]`). This is a
  technical requirement: messages live in a `Multiset`, where membership and `erase` need
  decidable equality.
- **Histories and atomicity.** Atomicity is CSLib's `Cslib.SharedMemory.IsLinearization` on the
  history of invocations and responses. The paper's definition (§2.2) allows dropping the last
  operation of each faulty process; pending operations may or may not be linearized, which is the
  same thing. CSLib's notion is the amended Herlihy–Wing definition, see the LinearizabilityTypo
  paper (PODC 2021).

## 3. Lemma by lemma

- **Lemma 1** (increments by 1). Holds: `lemma1` (`LivenessSteps.lean`; every step changes each
  `w_sync_i[j]` by `0` or `1`).
- **Lemma 2.** Holds: `lemma2`.
- **Lemma 3.** Holds: `lemma3`. The paper's induction is fine.
- **Lemma 4.** Holds: `lemma4`. The paper's proof is an informal appeal to the "alternating bit"
  properties P1/P2. We replace it by an inductive invariant, `InvW` in `InvWrite.lean`:
  - the `k`-th `WRITE` message from `i` to `j` is `WRITE(k mod 2, v_k)`;
  - it is sent exactly once;
  - the unprocessed ones are exactly the numbers in `(w_sync_j[i], sent(i,j)]`, where
    `sent(i,j) = min(w_sync_i[i], w_sync_i[j] + 1)`;
  - there are at most two of them (`sent ≤ w_sync_j[i] + 2`).
- **Lemma 5.** Holds.
  - R1/R2 about the messages *actually sent*: `lemma5_sent` (`Messages.lean`). The number of
    `WRITE`s `p_i` has sent to `p_j`, counted on the ghost log `C.sent`, equals
    `sent C i j = min(w_sync_i[i], w_sync_i[j] + 1)`. Note that `sent` in `InvWrite.lean` and
    `lemma5` (`Safety.lean`) is this *formula* on local variables, not a count; `lemma5_sent`
    shows the two agree.
  - Channel part (stronger "exact" form): `lemma5`. The unprocessed messages are exactly the
    numbers in `(w_sync_j[i], sent C i j]`, at most two, and only crashed senders' messages can be
    lost.
  - The paper states it for `i ∈ C`, but it holds for every process.
  - **Gap in the paper's proof.** The case analysis considers only a `write` invocation by
    `p_i` and the reception by `p_i` of a `WRITE` from `p_j`. It ignores the reception by `p_i`
    of a `WRITE` from a third process `p_k ≠ p_j`. Such a reception may increase `w_sync_i[i]`
    (line 14) and send a `WRITE` to `p_j` (line 15), changing the premises of R1/R2 for the pair
    `(i, j)`. The statement remains true. Our invariant proof handles this case: in
    `InvW.of_recv_adopt` every `ℓ` with `w_sync_i[ℓ] = wsn − 1` gets exactly one new message.
  - The paper's case analysis also needs, as an induction hypothesis, the property "at most two
    unprocessed messages, of different parities". That property is what makes the parity test
    of line 11 select the right message. We include it in the invariant.
- **Lemma 6** (pairwise progress) and **Lemma 7** (no process blocks forever at line 11): see
  `Liveness.lean`. The paper's proof of Lemma 6 forward-references Lemma 7. In our proof both
  follow from one "progress" argument: the next unprocessed `WRITE` of a channel passes the
  parity test, stays enabled, and fairness delivers it.
  - Our Lemma 7 (`Liveness.recv_progress`) assumes that the *sender* is also correct. The
    paper states it for every sender. This is harmless: it is only used for pairs of correct
    processes. Moreover, messages of crashed senders may be lost in our model (`drop`), so a
    receiver may legitimately wait forever at line 11 for a lost message; such a blocked
    handler does not block the process.
- **Lemmas 8 and 9** (termination): see `Liveness.lean`.
- **Lemma 9 (the `PROCEED` counting).** Channels are not FIFO and `READ()`/`PROCEED()` carry no
  sequence number, so "`r_sync_i[j] = rsn` means `p_j` answered the current request" needs an
  argument; the paper only asserts it. Our invariant `InvP.pipe`: every `READ()` from `i` to
  `j` is, at any time, in exactly one place:
  - in transit;
  - a pending handler at `j`;
  - a `PROCEED()` in transit;
  - already counted in `r_sync_i[j]`.

  Messages can only be lost when their sender crashed. So `r_sync_i[j] = rsn` implies that the
  current request has been answered (`InvH.of_r8`).
- **Lemma 10.** Holds: `lemma10` (the three claims) and `linearizable`. Two harmless
  imprecisions in the paper's proof:
  - **Claim 2** says "we have `w_sync_k[k] = x` when `read[i,y]` starts". Only `≥ x` is true:
    later writes may have started. Only `≥ x` is used.
  - **Claim 3** says that "as each of `Q_ri` and `Q_rj` contains at least `n − t` processes, and
    there is a majority of correct processes, there is at least one correct process in their
    intersection". This is a non sequitur: two quorums of size `n − t` intersect, but not
    necessarily in a correct process. For example, `n = 3`, `t = 1`, quorums `{1,2}` and
    `{2,3}`, and `p_2` faulty. Correctness of the common process is never used, so the proof
    goes through with "a process in the intersection".
  - Small slips:
    - At the end of the proof of Claim 3, "the index `sn` computed by `p_i`" should be `p_j`.
    - In the proof of Claim 2, "a quorum `Q_w` of at least `(n−t)` processes `p_i` such that
      `w_sync_w[j] = x`" mixes the indices `i` and `j`.
    - In the proof of Lemma 8, "`w_sync_i[i] ≥ w_sync_w[i] = wsn` at each correct process
      `p_i`" has the indices swapped. What is needed (and true by Lemma 6) is
      `w_sync_w[i] ≥ wsn`.
  - Our proof makes the ghost information explicit (`InvH` in `InvHist.lean`):
    - the snapshot of all `w_sync_j[j]` at the invocation of each read (`snap`);
    - the reads-from map (`rf`).

    The linearization comes from a general SWMR reads-from criterion
    (`Cslib/Computability/Distributed/SharedMemory/SWMRRegister.lean`).
- **Theorem 1.** Safety part: `linearizable`. Liveness part: `live` (`Liveness.lean`).
- **Theorem 2** (message content). The control information is two bits:
  `Msg.ext_ctrl_payload` (a message is determined by `Msg.ctrl : Bool × Bool` and its optional
  data value). Two of the four types carry a value.
  - Message complexity, "`O(n)` messages per read, `O(n²)` per write", only holds in the
    amortized sense.
    - A single write may trigger fewer messages.
    - Catch-up messages (line 16) for old values may be sent long after the write returned.
  - We prove the amortized bounds on the ghost log of all sent messages (`Messages.lean`):
    - `write_messages`: at most `n(n−1)` `WRITE` messages per invoked write. Process `i` sends
      at most `w_sync_i[i]` `WRITE`s to each `j`.
    - `read_messages`: at most `2(n−1)` `READ`/`PROCEED` messages per invoked read.
- **Time complexity** (`2Δ` per write, `4Δ` per read in failure-free runs with delays `≤ Δ`;
  §1 and Table 1) is not formalized: our model is untimed.
