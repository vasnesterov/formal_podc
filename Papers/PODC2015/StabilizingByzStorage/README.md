# Stabilizing Byzantine Server-Based Storage — PODC 2015

Silvia Bonomi, Shlomi Dolev, Maria Potop-Butucaru, Michel Raynal. *Stabilizing Server-Based Storage in
Byzantine Asynchronous Message-Passing Systems.* PODC 2015. DOI
[10.1145/2767386.2767441](https://doi.org/10.1145/2767386.2767441). Formalized version: arXiv
[1503.00140](https://arxiv.org/abs/1503.00140) v1 (full version with Figs. 2–5 and the proofs); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ Intent lost.** The paper's noteworthy claim, the first *atomic* storage on top of asynchronous
servers with transient failures and Byzantine servers, fails: the practically stabilizing SWSR atomic register
(Fig. 3, Theorem 3) has new/old inversions forever in a fair execution with `n = 9`, `t = 1`, and the SWMR/MWMR
registers of Theorem 4 are built on it. The stabilizing *regular* register (Fig. 2, Theorem 1) is correct: we
proved it (liveness for `n > 6t`, regularity after the first write for every `n`), repairing gaps in the
proofs of Lemmas 2 and 3.

## Mistakes in the paper

### ❌ Theorem 3 and Lemma 13 (Fig. 3, practically stabilizing atomic register)
The register of Fig. 3 never stabilizes to atomicity: with `n = 9` servers, `t = 1` Byzantine, sequence
numbers modulo `2^64 + 1`, there is a fair infinite execution in which, in every 158-step period, a read
returns the value of a write `W4` and the next read returns the value of the earlier write `W3`, both values
regular, each read overlapping at most four writes (`Atomic.theorem3_false`).

**Impact.** The atomic SWSR register, the paper's main contribution, is refuted, and with it the
foundation of the SWMR and MWMR registers of Section 5 (Theorem 4), which are built from it (Fig. 4 itself
was not checked). The regular register of Fig. 2 is not
affected.

**Details.** The culprit is the sanity check N2–N7, which *lowers* the reader's `pwsn` to the sequence number
of any helping pair reported by `2t + 1` servers. Lemma 13's proof claims this "happens iff the writer
sequence number wrapped around". But helping pairs are refreshed only when a read has reset them, so they
normally lag behind `last_val`. One period (`Atomic.Cex.cycle`):

1. Read `R1` starts; writes `W1`–`W3` run while its `READ(true)` reaches the servers two at a time, so its
   first iteration sees four different `last_val`s and loops. `W3` refreshes the helping values to `(3, 3)`.
2. `W4` starts; `WRITE(4, 4)` reaches two correct servers. `R1`'s second iteration sees `(4, 4)` three times
   (with the Byzantine server) and `(3, 3)` five times. It takes `(4, 4)`, since `4 >cd pwsn`, and returns
   `4`.
3. Read `R2` starts while `W4` is still running. Its sanity check sees `(3, 3)` at seven servers; since
   `pwsn = 4 >cd 3` it sets `pwsn ← 3`, `pv ← 3` (`Atomic.Cex.sanity_check_lowers_pwsn`). Its loop sees
   `(4, 4)` once and `(3, 3)` seven times, and `3 >cd 3` is false, so it returns `pv = 3`.
4. `W4` completes and a solo read `R3` brings the system back to the initial configuration shifted by 4.

`W3` completed before `W4` started, `R1` completed before `R2` started: a new/old inversion. Without N6, line
13M3 would have returned `pv = 4`. When two values pass the `2t + 1` test of line 12 the pseudo-code does not
say which one is taken. In our execution every choice is the freshest candidate (largest sequence number,
`Atomic.Cex.cycle_allFresh`). In a variant where one correct server lags on the writer's link, every choice
is both the freshest and the strictly most frequent candidate, with the same inversion
(`Atomic.Cex.variant_labels`, `Atomic.Cex.variant_allMostFrequent`), so the counterexample does not exploit
that ambiguity. It also respects the paper's "system-life-span" bound: between two successive reads that
are not concurrent with any write (`R3` of consecutive periods) there are only four writes.

**Repair.** None proved. N6 cannot simply be dropped: it is how the reader recovers from a corrupted `pwsn`
that is "ahead" of the writer, which otherwise makes reads return a stale `pv` for up to `2^63` writes.

### ✏️ Slips
- Lemma 9 claims that `4t + 1` *correct* servers share a helping pair when a write returns. When the test of
  line 03 fails because `4t + 1` acks agree, up to `t` of them are Byzantine, so only `3t + 1` correct servers
  are guaranteed (`Atomic.Cex.lemma9_false`). Claim C(b) of Lemma 2 states the right bound `3t + 1`, which
  suffices for the later uses.

## Proof gaps (statements true)

### 🔧 Lemma 2 (Fig. 2, termination of `read()`)
The case "more than one write concurrent with `R`" claims that the first write after `R`'s `READ(true)`
sees `4t + 1` acks with `⊥` and refreshes the helping values; this is not so, because `NEW_HELP_VAL`s of
writes concurrent with the reset can be delivered after it.

**Impact.** Statement true (even for `n > 6t` instead of `n > 8t`); repaired
(`Regular.lemma2_read_terminates`).

**Details.** The proof also starts "consider an execution of the loop body after `τ_stab`", where
`τ_stab` is only defined in Lemma 3, and in the one-concurrent-write case it concludes from "`2t + 1`
replies carry `x` or `y`" that `2t + 1` replies carry the *same* value (true by pigeonhole, since in fact
`n − 3t ≥ 4t + 1` replies carry `x` or `y`).

**Repair.** Wait until *every* correct server has delivered `R`'s `READ(true)`. If some later write
refreshes the helping values to `z`, every following write sees `≥ n − 2t ≥ 4t + 1` acks `z` and never
refreshes again. So there are finitely many refreshes; then the helping values are frozen, and a write
that does not refresh has `4t + 1` acks with the same `w`, so `≥ 3t + 1` correct servers hold `w` and an
iteration of `R` sees `≥ 2t + 1` of them. If the writer stops, all correct servers end with the same
`last_val`.

### 🔧 Lemma 3 (Fig. 2, eventual regularity)
The proof only argues about `last_val` quorums and leaves "`2t + 1` messages `ACK_READ(−, z)`" (a return at
line 15 through the helping values) unexplained; "and so on and so forth" stands for an induction over
concurrent writes that is not given.

**Impact.** Statement true, with `τ_stab` = the return of the first write and no bound on `n`; repaired
(`Regular.lemma3_regular_exec`).

**Repair.** Take the `≥ n − 2t` correct servers that delivered the `WRITE` of the last write `W` completed
before `R` (synchronized delivery). By FIFO order every later `last_val` of such a server, and every
helping value it adopts after `R`'s `READ(true)`, comes from `W` or a later write, which is concurrent with
`R`. A value with `2t + 1` copies among `n − t` replies has a copy from one of them, since at most `2t`
servers are outside this set.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing, interleaving semantics: one writer, one reader, `n` servers, a set `B` of at
  most `t` Byzantine servers whose replies are arbitrary in every collection (they may answer writer and reader
  differently). No randomness.
* Each server has a FIFO link from the writer and one from the reader. Their initial contents are arbitrary
  (transient failures end at `τ_no_tr = 0`), and so are the servers' variables.
* `ss-broadcast` is axiomatised as in the paper. A broadcast appends to all links, so no duplication, validity
  and FIFO order hold by construction. Synchronized delivery (`n − 2t` correct servers deliver during the call)
  guards the step that ends the broadcast; termination and eventual delivery are fairness assumptions.
* Acknowledgments are matched to the client's current broadcast through ghost reply slots, which never use
  stale replies. This is a favourable reading of the paper's remark that FIFO order makes sequence numbers
  unnecessary.
* A client collection picks any `n − t` servers. At lines N4, 12, 14 any value with `2t + 1` copies may be
  taken.
* Fig. 3 uses sequence numbers in `Fin (2^64 + 1)` with the clockwise-distance order `>cd`. The counterexample
  starts from a clean configuration, which only makes it stronger.
* Fig. 2 (Theorem 1): the clients start between operations; arbitrary initial servers and links. Liveness is
  proved for fair infinite executions (`Regular.Fair`: weak fairness of every correct server's deliveries and
  of each client's enabled steps; stutters allowed). Regularity is proved through ghost variables recording
  the write history, which the algorithm never reads; the theorem itself is stated on invocation and
  response events.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3 / Lemma 13 (Fig. 3 practically atomic): **false** | `Atomic.theorem3_false` | `Theorem3.lean` |
| Lemma 13, "N6 lowers `pwsn` only after wrap-around": **false** | `Atomic.Cex.sanity_check_lowers_pwsn` | `Theorem3.lean` |
| Counterexample uses the freshest candidate at every threshold test | `Atomic.Cex.cycle_allFresh` | `Cycle.lean` |
| Inversion also when line 12 takes the most frequent candidate | `Atomic.Cex.variant_labels`, `Atomic.Cex.variant_allMostFrequent` | `Robust.lean` |
| Lemma 9: **false** as stated (`3t + 1`, not `4t + 1`) | `Atomic.Cex.lemma9_false` | `Lemma9.lean` |
| Theorem 1 (Fig. 2 stabilizing regular; with `n > 6t`) | `Regular.theorem1` | `Theorem1.lean` |
| Lemma 1 (writes terminate) | `Regular.lemma1_write_terminates` | `RegularLiveness.lean` |
| Lemma 2 (reads terminate; `n > 6t`, at least one write) | `Regular.lemma2_read_terminates` | `RegularLiveness.lean` |
| Lemma 3 (regularity after the first write; any `n`) | `Regular.lemma3_regular_exec`, `Regular.lemma3_regular` | `RegularSafety.lean` |

The paper assumes `n ≥ 8t + 1` throughout. For Fig. 2 regularity needs no bound and termination needs only
`n ≥ 6t + 1`.

**Not formalized.** Theorem 2 and Fig. 5 (synchronous links, `t < n/3`). The liveness and eventual
regularity lemmas of Fig. 3 (Lemmas 7, 8, 10–12). Section 5: the one-paragraph SWMR construction from SWSR
registers (5.1) and the MWMR construction of Fig. 4 with bounded epochs (Lemmas 14–18); their premise, the
atomic SWSR register, fails. Mobile Byzantine faults (footnote 1).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The counterexample cycle is checked by kernel evaluation (`decide`) of an executable step function proved sound
for the step relation (`Atomic.apply_sound`, `Atomic.run_spec`). It is repeated forever through a
shift-equivariance lemma (`Atomic.Step.shift`). The fairness assumption of Theorem 1 is satisfiable (an
`example` in `RegularLiveness.lean`). The model is paper-local (`Server.lean`, `Atomic.lean`,
`Regular.lean`).
