# Read-Write Wait-Free Coverings in the Fully-Anonymous Model — PODC 2024

Giuliano Losa, Eli Gafni. *Understanding Read-Write Wait-Free Coverings in the Fully-Anonymous
Shared-Memory Model.* PODC 2024 (brief announcement). DOI
[10.1145/3662158.3662786](https://doi.org/10.1145/3662158.3662786). Formalized version: arXiv
[2405.03573](https://arxiv.org/abs/2405.03573) v2, the full version with proofs. Numbering follows it.

**Verdict: ❌ False claim.** Lemmas 4.6–4.7 and Theorem 4.8 are false when there are fewer
registers than processors. Section 4 never bounds the number of registers. With at least `N`
registers everything checked holds:

* Lemmas 4.5–4.7 as printed.
* Theorem 4.8: stable views form a DAG with a unique source.
* The snapshot algorithm of Figure 3 is safe and wait-free. Level `N − 1` (footnote 4) already
  suffices.
* The renaming reduction of Section 6 is correct.

The proofs of Theorem 4.8 and of snapshot safety (§5.3.2) do not go through. We prove both with
repaired or new arguments.

## Mistakes in the paper

* **Lemmas 4.6–4.7 and Theorem 4.8 need at least `N` registers.** Take two registers and four
  processors with inputs `0, 0, 1, 1`. The two groups take turns: both members of a group write,
  one register each, and then both scan. Each processor only ever reads its own group's value, so
  the stable views `{0}` and `{1}` are incomparable and the stable-view graph has two sources.
  * With one register, two processors that alternate *write; scan* behave the same way. This
    execution also refutes Lemma 4.6 with `A = {0}`: `Ā = {1}` is live and covers at most one
    register, yet never reads from `A`.
  * Exhaustive search finds no such execution with 3 processors and 2 registers. In general, the
    two groups with minimal views must together have more members than there are registers.
  * Section 2 allows any number `M > 0` of registers, and Theorem 4.8 states no bound.
  * Section 4 stresses that its pathology arises "regardless of the number of registers". Its
    running example (§4.1, reused in §5.1) has 5 processors and 3 registers.
  * The proof of Lemma 4.6 does count `N` registers ("`|R_t^Ā| + |Ā| < N` registers"). Section 5
    uses `N` registers.

  So the missing hypothesis `M ≥ N` is borderline between an implied assumption (⚠️) and a false
  claim (❌). We count it as ❌ because the paper itself works with fewer registers than processors
  in Section 4. Section 4 is a warm-up for the snapshot algorithm, which uses `N` registers, so the
  headline results are unaffected. We prove Lemmas 4.5–4.7 and Theorem 4.8 with
  `N ≤ |R|`. (`theorem_4_8_needs_registers'`, `theorem_4_8_needs_registers`,
  `lemma_4_6_needs_registers`; `Exec.lemma_4_5`,
  `Exec.lemma_4_6`, `Exec.lemma_4_7`, `theorem_4_8`)
* **Theorem 4.8: the proof is wrong; the statement holds with `N ≤ |R|`.**
  * The proof claims, by Lemma 4.4, that live processors with a stable view in `X` read only from
    `P_X`. Here `X` is the set of views reachable from a source `S`. Lemma 4.4 gives the opposite
    inclusion: processors with a view in `X̄` read only from `P_X̄`. A processor with a view in `X`
    may read from a smaller view in `X̄`.
  * Applying Lemma 4.7 to the closed set `P_X̄` yields no contradiction.
  * The GST of Definition 4.1 does not ensure that registers hold the writers' *stable* views,
    which Lemma 4.4 needs.

  Our proof:
  * Take two distinct minimal stable views. After a strengthened GST, the processors holding each
    of them read only from each other.
  * By Lemma 4.5, each group leaves at most its own size of registers to the others. With at least
    `N` registers, this pins the partition exactly.
  * The next round-robin write of a group member into the other group's registers then breaks the
    count.

  (`theorem_4_8`, `theorem_4_8_unique_source`, `Exec.false_of_two_closed`, `Exec.exists_gst`)
* **Snapshot safety (§5.3.2): the statement is true; the proof does not go through.**
  * Lemma 5.2 is false as printed. Take `N = 2`: `q` runs solo to level 2 with view `{1}`. Then
    `p` writes `{1,2}` into both registers, so `W = {1,2}` is durable. Afterwards `q` executes its
    output step, "takes a step and terminates", with `W ⊄ view[q]`. The intended statement covers
    scans that *start* after `t`. Without the printed version, the derivation of safety from
    Lemmas 5.2 and 5.3 misses two final scans that overlap in time. This counterexample is not in
    Lean: our model merges the output step into the last read.
  * Lemma 5.8 assumes that "durably stored" is preserved over time. It is not: a write of a value
    containing `W` can turn several harmless scanners into threats.

  We give a new proof (details in [differencies.md](differencies.md), item 8). Call `W` *durable*
  when the registers containing `W` plus the processors containing `W` number more than `N`.
  * Persistence: every scan that starts after a durable time ends with a view containing `W`.
  * Chain: below a terminated view `W` there is a chain of nested scans with view `W`. Each scan
    in the chain is performed by a new processor with view `W`, so the chain must reach a scan at
    whose start `W` is durable.
  * For two incomparable outputs, the two durable starts would each have to precede the other.

  This proof needs only level `N − 1`, so it also proves footnote 4, which the paper states
  without proof. (`snapshot_safety_paper`, `snapshot_safety`, `Exec.durable_scan`, `Exec.chain`)
* **Smaller points.**
  * The wait-freedom proof only needs a minimal stable view, not Theorem 4.8. It also tacitly uses
    fresh register contents after stabilization.
  * Lemma 4.6's proof ignores registers that still hold their initial value. Its case "|R_t^Ā| <
    |A|" needs a scan that starts after every register has been written.
  * Figure 1 has a typo: `written ∪ {r} = P` should be `= R`. Figure 3 has the same typo.
  * The "saving grace" argument of Section 6 is correct, but a simpler argument suffices. Two
    groups with equal-size snapshots appear together in some output sample, so their snapshots
    are equal and their ranks differ.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous read/write shared memory: `N` processors (`P`) and `|R|` multi-writer atomic
  registers. There are no failures besides stopping, and the schedule is arbitrary (adversarial).
  The model is deterministic and has no randomness.
* **Processor anonymity:** all processors run the same program and differ only in their input.
* **Memory anonymity:** each write or read names a *physical* register, chosen
  nondeterministically. Writes follow the round-robin `written` set, and each scan reads every
  register once, in any order. This over-approximates every wiring permutation, so the positive
  results hold for all wirings. The concrete counterexample schedules are realizable with suitable
  wirings.
* Registers carry a ghost "last writer" field, which the algorithm never reads.
* Executions are infinite. A terminated processor only takes idle steps. *Live* means taking
  infinitely many non-idle steps.
* Atomicity follows the PlusCal code. The end-of-scan computation and the output step are merged
  into the last read of the scan.
* Sections 3 and 6 are formalized on outcomes: participants, groups (= inputs), and outputs.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 4.5 | `Exec.lemma_4_5` (strengthened: `Exec.card_notWrittenBy_le`) | `Lemmas.lean`, `Covering.lean` |
| Lemma 4.6 (needs `N ≤ |R|`) | `Exec.lemma_4_6` | `Lemmas.lean` |
| Lemma 4.6 fails with `|R| < N` | `lemma_4_6_needs_registers` | `Counterexamples.lean` |
| Lemma 4.7 (needs `N ≤ |R|`) | `Exec.lemma_4_7` | `Lemmas.lean` |
| Two closed live groups cannot coexist (used for Thm 4.8) | `Exec.false_of_two_closed` | `Covering.lean` |
| Lemma 4.4 + GST (Def. 4.1, corrected) | `Exec.readsOnlyFrom_minimal`, `Exec.exists_gst` | `Stable.lean` |
| Theorem 4.8 (needs `N ≤ |R|`) | `theorem_4_8`, `theorem_4_8_unique_source` | `WriteScan.lean` |
| Theorem 4.8 fails with `|R| < N` (`N = 4, |R| = 2`; `N = 2, |R| = 1`) | `theorem_4_8_needs_registers'`, `theorem_4_8_needs_registers` | `Counterexamples.lean` |
| Figure 2 execution | `figure_2` | `Examples.lean` |
| Safety of Figure 3 (§5.3.2) | `snapshot_safety_paper`, `snapshot_safety_outputs` | `Safety.lean` |
| Footnote 4 (level `N − 1` suffices; also any `|R| ≥ N`) | `snapshot_safety` | `Safety.lean` |
| Validity of outputs | `snapshot_view_valid` | `Safety.lean` |
| Wait-freedom (§5.3.3; any level, any `|R|`) | `snapshot_waitFree`, `snapshot_live_false` | `WaitFree.lean` |
| Section 3.2 example (group snapshot) | `example_3_2` | `Groups.lean` |
| Section 6 (renaming with `n(n+1)/2` names) | `renaming_of_groupSnapshot` | `Groups.lean` |
| Chain outputs group-solve snapshot | `groupSnapshot_of_chain` | `Groups.lean` |

**Not formalized.**
* Section 2.1, an informal lower bound.
* Section 7, long-lived snapshot and obstruction-free consensus, which the paper only sketches.
* The paper's own induction for safety (Lemmas 5.2–5.8), which our new proof replaces.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Concrete executions are checked by kernel computation (`decide +kernel`, `Periodic.lean`).
* Non-vacuity: `snapSolo_spec` exhibits an execution of Figure 3. `figure_2` exhibits an
  execution of Figure 1 with `|R| = N = 3` to which Theorem 4.8 applies.
* The model is self-contained in this folder: `Model.lean`, `Scan.lean`, `Covering.lean`,
  `Stable.lean`, `Periodic.lean`. These modules are CSLib candidates: a generic write–scan loop
  over anonymous registers, fair writes, the first-completing-scan counting argument, and GST.
