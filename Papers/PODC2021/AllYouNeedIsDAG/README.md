# All You Need is DAG (DAG-Rider) — PODC 2021

Idit Keidar, Eleftherios Kokoris-Kogias, Oded Naor, Alexander Spiegelman. *All You Need is DAG.*
PODC 2021. DOI [10.1145/3465084.3467905](https://doi.org/10.1145/3465084.3467905). Formalized
version: arXiv [2102.08325](https://arxiv.org/abs/2102.08325) v2. Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** DAG-Rider satisfies Integrity, Total order, Agreement and Validity (the last two given infinitely many good waves, which occur with probability 1; robust Lemma 2 and the `≤ 3/2` expected-waves bound are proved). But Lemma 1 is false as stated (for indirectly committed leaders) and the total-order proof relies on it; chain quality holds only for round-major delivery orders; several proofs (Lemma 2 → Claim 6, Claim 2, Validity) have gaps, all closed here.

## Mistakes in the paper

* **Lemma 1 is false for indirectly committed leaders, so the proof of Proposition 2 (total order)
  has a gap.**
  - Section 6.1 says a process *commits* a leader when it pops it from the stack. Leaders reached
    in lines 39–43 count too. Lemma 1 says every later leader in anyone's DAG has a strong path to
    every committed leader.
  - The proof assumes the commit rule of line 36 was met, which is true only for *direct* commits.
  - Section 5 introduces Lemma 1 right after the commit rule, so it can be read as speaking of
    direct commits only. Under that reading Lemma 1 is true (`lemma1_direct`), and the gap moves to
    Proposition 2, whose proof applies it to every committed leader.
  - Counterexample with `n = 4`, `f = 1`, observed by correct process `3`, whose DAG at
    `wave_ready(w)` holds all vertices of rounds `1..4w` except its own `(4w, 3)` (a realizable view):
    - Waves 1 and 2 fail the commit rule (only one round-4/round-8 vertex reaches the leader).
    - The wave-2 leader `v₂ = (5,0)` points only to round-4 vertices that avoid `v₁ = (1,0)`.
    - Wave 3 commits `v₃ = (9,0)` directly. `v₃` reaches `v₁` (via `(5,1) → (4,0)`) but not `v₂`.
    - So the process commits `v₁` and then `v₃`, while the later leader `v₂` sits in its DAG with
      no strong path to `v₁`.
  - Total order still holds. Lemma 1 for *direct* commits is enough: the output of a process is
    always the delivery of the full greedy chain of its last directly committed leader, and that
    chain depends only on the global DAG. (`Lemma1Counterexample.lemma1_false`; repaired:
    `lemma1_direct`, `orun_inv`, `delivered_prefix`, `total_order`)
* **Chain quality (Section 3, stated without proof) depends on the unspecified delivery order.**
  - `order_vertices` delivers a causal history "in some deterministic order". If that order lists
    vertices by source first, the claim is false. In a lock-step run with `n = 4` and Byzantine
    process `0` that behaves correctly:
    - wave 1 delivers the leader `(1,1)`;
    - wave 2 then delivers `(1,0), (2,0), …`.
    - The prefix of size `2f + 1 = 3` therefore has only one correct block.
  - For any round-major order (rounds non-decreasing, any order within a round, even Byzantine
    first) the claim is true. Every prefix of the output has `≥ 2f + 1` vertices in each round below
    its top round, and at most `f` Byzantine vertices per round.

  Classification: under-specified definition. (`ChainQualityCounterexample.chain_quality_false`;
  `chain_quality`)
* **The probability argument (Lemma 2 → Claim 6) needs a stronger Lemma 2; the statement is true.**
  - Lemma 2 gives each process a set `V` from its *own* DAG at the time it completes the wave.
  - The coin is revealed as soon as `f + 1` processes have called it, so the adversary may know
    the leader before slower correct processes complete the wave.
  - We prove the needed *robust* version. Take any `2f + 1` round-3 vertices that exist; this
    already holds when the first correct process completes the wave, i.e. before the reveal.
    Let the core be the round-1 sources reached by `≥ f + 1` of them. Then:
    - the core has `≥ 2f + 1` members (double counting; this replaces the informal appeal to the
      common-core protocol);
    - every round-4 vertex ever created, Byzantine or not, strongly reaches the whole core;
    - the core is determined by the past of those vertices.
  - With a perfect coin the expected number of waves until a commit is `≤ (3f+1)/(2f+1) ≤ 3/2`.
    The paper's "`≤ 3/2 + ε`" is slightly off for `ε > 0`: `1/(2/3 − ε) > 3/2 + ε`.
  (`core_card`, `sPath_of_mem_core`, `core_congr`, `lemma2`, `goodWave_of_core`,
  `Coin.dagRider_expected_waves`)
* **Claim 2's "induction on rounds" is unsound as written; the statement is true.**
  - Line 25 checks only the strong edges, so a Byzantine vertex may have weak edges to vertices
    of the same or a higher round.
  - The proof also assumes every correct process eventually reaches the vertex's round. That
    progress claim is never proved and itself needs Claim 2.

  We prove progress and Claim 2 jointly: induction on rounds, with an inner induction on the time
  at which the vertex was added. (`round_liveness`, `claim2`, `claim7`)
* **Proposition 4 (Validity) skips a step; the statement is true.**
  - Weak edges only guarantee that vertices created *later by correct processes* reach `v`. The
    committed leader may be Byzantine.
  - Missing step: a vertex of a late enough round has `2f + 1` strong edges, so at least one of
    them goes to a correct vertex, which reaches `v`.

  The proof also needs RBC *authenticity*: a correct sender's message is delivered only if it was
  sent. This is standard, but absent from the paper's RBC specification. (`run_validity`)
* **Typos and slips.**
  - Line 7 requires predecessors in `⋃_{k≥1} DAG[k]`, which excludes the genesis round, so
    literally no round-1 vertex is ever added.
  - Algorithm 2 calls `wave_ready(0)` with `round(0,1) = −3` (harmless).
  - Line 25 does not check that strong edges point to round `r − 1`. The prose requires it, and
    without it a Byzantine leader could skip a committed leader and break total order (described
    in words only).
  - Claim 7's proof ignores the buffer conditions.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `n = 3f + 1` processes, at most `f` Byzantine (a static set chosen by the adversary).
  Asynchronous network.
* Reliable broadcast is abstract. A run gives each correct process an arbitrary sequence of
  batches of delivered vertex ids. RBC Validity, Agreement and Authenticity are hypotheses
  (`Run.Valid`).
* Non-equivocation is built in: vertices are identified by `(round, source)` and have one global
  content.
* Correct processes run Algorithm 2 step by step (one main-loop iteration per step). When a
  process advances from round `4w`, the ordering layer runs on its current DAG. Algorithm 3 is
  implemented literally (`waveReady`, `orun`); "some deterministic order" is an arbitrary function
  `sortV`.
* The global perfect coin is a function `coin : ℕ → P` (agreement).
* Safety theorems hold for **arbitrary** closed, valid local DAGs, with no assumption on schedules
  (only `n ≤ 4f + 1` is used: two sets of `2f + 1` sources intersect. The bound on Byzantine
  processes enters only through the RBC abstraction, i.e. non-equivocation).
* Agreement and Validity assume infinitely many *good* waves: every correct process's round-4
  vertices reach the leader.
  - Such a wave occurs whenever the coin hits the robust core.
  - In an abstract adaptive-adversary coin game (perfect coin, `ε = 0`), `k` consecutive misses
    have probability `≤ (f/(3f+1))^k`, and the expected waiting time is `≤ 3/2`.
  - The identification of the execution's probability space with this game is informal (see
    differencies.md).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Prop. 1 (Integrity) | `run_integrity`, `integrity` | `Liveness.lean`, `Safety.lean` |
| Prop. 2 (Total order) | `run_total_order`, `total_order`, `delivered_prefix` | `Liveness.lean`, `Safety.lean` |
| Prop. 3 (Agreement) | `run_agreement` | `Liveness.lean` |
| Prop. 4 (Validity) | `run_validity` | `Liveness.lean` |
| Lemma 1 (direct commits) | `lemma1_direct` | `Safety.lean` |
| Lemma 1 as stated: false | `Lemma1Counterexample.lemma1_false` | `Lemma1Counterexample.lean` |
| Lemma 2 | `lemma2`; robust core: `core_card`, `sPath_of_mem_core`, `core_congr`, `commit_of_mem_core` | `CommonCore.lean` |
| Claim 6 | `Coin.dagRider_expected_waves`, `Cslib.Probability.CoinGame.prob_missesWindow_le`; link: `goodWave_of_core` | `Coin.lean`, `Podc/Probability/CoinGame.lean`, `Liveness.lean` |
| Claims 1, 2, 7 | `st_dag_closed`, `claim2`, `claim7`, `round_liveness` | `DagLayerProofs.lean` |
| Claims 4, 5 | built into `orun_inv` (one leader per wave; increasing waves) | `Safety.lean` |
| Chain quality (round-major) | `chain_quality` | `ChainQuality.lean` |
| Chain quality (source-major): false | `ChainQualityCounterexample.chain_quality_false` | `ChainQualityCounterexample.lean` |
| Non-vacuity | `nonVacuity`, `NonVacuity.valid` | `Main.lean`, `NonVacuity.lean` |

**Not formalized.**
- Communication and time complexity (Section 6.2, Table 1), post-quantum safety, and the
  threshold-signature coin.
- The measure-theoretic link between executions and the coin game.

**Trust.**
- No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
- The counterexamples are checked by `decide +kernel`.
- Non-vacuity: a lock-step run with `n = 4`, `f = 1` satisfies all hypotheses of `Run.Valid`, and
  all of its waves are good, so the Agreement and Validity hypotheses are satisfiable.
- The coin game (`Podc/Probability/CoinGame.lean`, shared with VABA) and quorum intersection
  (`Podc/Foundations/Quorum.lean`) are shared infrastructure.
- No CSLib model was reused. The Byzantine models in CSLib are
  round/time-based state machines, whereas DAG-Rider needs an abstract RBC.
