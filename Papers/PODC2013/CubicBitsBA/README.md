# Nearly cubic synchronous Byzantine agreement — PODC 2013

Dariusz R. Kowalski, Achour Mostéfaoui. *Synchronous Byzantine Agreement with Nearly a Cubic Number of
Communication Bits.* PODC 2013. DOI [10.1145/2484239.2484271](https://doi.org/10.1145/2484239.2484271).
Formalized version: the authors' final version on HAL ([hal-01151136](https://hal.science/hal-01151136v1),
16 pp.); there is no arXiv version. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** The protocol of Section 4 does not solve Byzantine agreement:
with `n = 7`, `t = 2` (so `t < n/3`) and binary values, two Byzantine processes make the correct
processes decide differently, whatever the default value `v0`. Theorem 2 (agreement) and Lemma 5
are false. Lemmas 1–4 and Theorem 1 (validity) hold.

## Mistakes in the paper

### 🚨 Theorem 2 (agreement of the protocol of Section 4)
The protocol violates agreement for `n = 7`, `t = 2`: Byzantine `b₁` sends `0` to three correct
processes and `1` to the other two, Byzantine `b₂` reports `b₁`'s value in round 2 as `0` to the
first group and as `1` to the second, and then the first group decides `0` while the second decides
the default `v0 = 1` (`not_solves_BA`, `theorem_2_false`).

**Impact.** The paper's algorithm, the contribution named in the title and abstract, is not a
Byzantine agreement protocol, so its `O(n³ log n)` bound is not established. The incremental
variant of Section 6 uses the same information and fails on the same run. Validity holds
(`theorem_1`).

**Details.**
- Run (correct `0..4`, Byzantine `b₁ = 5`, `b₂ = 6`, inputs `0,0,0,1,1`). Round 1: `b₁` sends `0`
  to `A = {0,1,2}` and `1` to `{3,4}`; `b₂` sends `1` to all. Round 2: both Byzantine processes
  echo the correct inputs truthfully and report `b₁`'s value to each receiver as that receiver got
  it. Round 3: they report no suspicion and echo the round-2 arrays as each receiver saw them.
- At the node `b₁` every correct process sees the same top set: `{0,…,4, b₂}`. The correct
  children echo `0,0,0,1,1`. `b₂`'s echo is `0` in `A` (strict majority `4/6`: `newval(b₁) = 0`)
  and `1` at `3, 4` (tie `3/6`: `newval(b₁) = ⊥`) (`newval1_b1`).
- At the root, `A` sees four `0`s among seven children and decides `0`. Processes `3, 4` see three
  and fall back to `v0 = 1` (`decide_exec`). With `v0 = 0` the same run with all values flipped
  works.
- `b₂`'s round-2 equivocation is detected only at the end of round 3 = `t + 1` and is never
  reported. `b₁`'s round-1 equivocation is detected by `3, 4` after round 2 and reported in
  round 3. But `newval(b₁ k)` reads `k`'s reports about `b₁` only through the echoes of round
  `t + 1 = 3`, which carry round-2 arrays, not suspicion sets. So the masks that should remove
  `3, 4` from the top set of `b₁` are all `⊤`.
- Other readings of §4. The run also violates agreement if a process discards, at decision time,
  all messages of every process it ever suspected. It does not if a process also drops from a top
  set the children whose last id it suspects itself, or takes the majority among non-`⊥` echoes
  only. A different attack with `n = 10`, `t = 3` breaks agreement under all eight combinations
  of these readings (Python simulation in [`simulation/`](simulation/), not formalized).

### ❌ Lemma 5 (common path coverings propagate to the root)
In the run above the whole tree has a common path covering (Lemma 4), but the root is not common
(`lemma_5_false`).

**Impact.** Lemma 5 is the only route from Lemma 4 to agreement, so Theorem 2 has no proof; the
run above shows it is false.

**Details.** The proof fails at the level-1 node `b₁`, all of whose children are common
(`children_b1_common`, `node_b1_not_common`). It claims that the correct processes in the top set
"do not suspect `p_j`" and hence "reported the same value `cval(xk)`". But membership of `xk` in
the top set only says that `k` reported no suspicion of `j` *by round `t`*. A suspicion created by
a round-`l` equivocation is reported in round `l + 2`, outside that window when `l = t − 1`. So
correct members of the top set can echo different values, and a Byzantine member of the top set
then decides the strict majority differently at different processes.

### Typos and slips
- §4.1, decoration example: "when `val(x)` of some node `x = yjk` is set to `⊤`, this means that
  `p_k` reported that it suspects `p_j`": `⊤` means "does not suspect" (as the bullets say).
- §4.2, intuition paragraph: "for the nodes of level 1 and level 2, `val(x)` is a proposed value";
  by the bullets of §4.1, level-2 `val` is a suspicion bit. This is harmless: `val` of an internal
  node is never used in the evaluation.
- Proof of Lemma 5: "`n − 2t > t + 1`" should be "`n − 2t > t`" (`n − 2t ≥ t + 1`).
- §6: "each process … relays `(n − 1)t` suspicions" ignores that Byzantine processes may report
  up to `n − 1` suspicions each. The relayed amount is still `O(nt)` (at most about `2nt`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous rounds; `n` processes `Fin n`; static Byzantine set of size `≤ t`. Reliable
  point-to-point channels, where the receiver knows the sender; no signatures. Each process also
  receives its own message. The protocol is deterministic, and the adversary chooses every
  Byzantine message per receiver and per round, knowing everything.
* The protocol (`Protocol.lean`) follows §4.1–4.2 literally. It has one message record (`Msg`):
  proposal, round-2 echo array, suspicion set, round-3 echo of arrays, echo of suspicion sets.
  The echo confirmation uses threshold `n − t`, counting the receiver's own echo and Byzantine
  echoes. A process suspected in an earlier round is treated as `⊥`. Suspicion sets are
  cumulative.
* The EIG decoration (`val1`, `cval2`, `valB`, `leafVal`, `cvalB`) and the bottom-up evaluation
  (`nvB`, `newval1`, `decision`) follow the bullets of §4.1–4.2. Labels are lists of distinct ids
  in reverse order.
* Executions (`Exec`): families of views in which correct senders send `out` of their own view.
  `Bridge.lean` defines the protocol as a CSLib `LockStep.Protocol` on the complete graph. It
  shows that every reliable lock-step run is an `Exec` with the same decisions (`execOf`,
  `decides_iff`). The counterexample is replayed as a lock-step scenario (`not_solves_BA`), so
  the refutation is stated in CSLib's standard model.
* Values: arbitrary `V` with decidable equality for the positive results; `Bool` for the
  counterexample, which covers both choices of `v0`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (correct processes never suspect each other) | `lemma_1`, `susp_correct` | `Correctness.lean` |
| Lemma 2 (decorations at labels ending in a correct id agree) | `lemma_2` | `Correctness.lean` |
| Lemma 3 (`newval = val` at labels ending in a correct id) | `lemma_3`, `lemma_3_level1` | `Correctness.lean` |
| Theorem 1 (validity) | `theorem_1`; in CSLib's model `validity_termination` | `Correctness.lean`, `Bridge.lean` |
| Lemma 4 (common path covering) | `lemma_4` | `Correctness.lean` |
| Lemma 5: **false** | `Counterexample.lemma_5_false` | `Counterexample.lean` |
| Theorem 2 (agreement): **false** | `Counterexample.theorem_2_false`, `Counterexample.not_solves_BA` | `Counterexample.lean`, `Bridge.lean` |
| §6, basic protocol: `O(n³ + n² log k)` bits per process | `totalBits_le`, `allBits_le` | `Complexity.lean` |

Lemma 1 needs only `|byz| ≤ t`, not `n > 3t`. Lemma 3, Theorem 1 and Lemma 4 use `n > 3t`. For
`t = 0` the level-1 nodes are leaves and `newval = val` (`newval1`).

**Not formalized.** The incremental protocol of §6 (`O(n³ log n)` total bits) is only sketched
in the paper. The `t = 3` attack is simulated only.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The counterexample is checked by kernel evaluation (`decide +kernel`, no
`native_decide`) on the actual protocol functions. The scenario is a CSLib lock-step run, so the
hypotheses are satisfiable. The lock-step model is CSLib's
`Cslib/Computability/Distributed/Byzantine/LockStep/` (`Solves`, `atMost`, `BA`). The Python
simulator in [`simulation/`](simulation/) is not part of the Lean development.
