# Fast Concurrent Data Sketches — PODC 2019

Arik Rinberg, Alexander Spiegelman, Edward Bortnikov, Eshcar Hillel, Idit Keidar, Lee Rhodes, Hadar
Serviansky. *Fast Concurrent Data Sketches.* PODC 2019 (brief announcement). DOI
[10.1145/3293611.3331567](https://doi.org/10.1145/3293611.3331567). Formalized version: arXiv
[1902.10995](https://arxiv.org/abs/1902.10995) v2 (Dec. 2019; the PPoPP 2020 text). The PODC 2019
publication itself is a two-page brief announcement; Lemma 1 and Theorem 1 are stated identically in
v1 (Feb. 2019, proofs in its Appendix A), v2 and the journal version. v2 defers its proofs to "the
full paper"; the proofs we checked are those of the journal version (ACM TOPC 9(2), 2022), Sections
6–7. See `differencies.md` for version differences. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** Lemma 1 and Theorem 1 hold: the generic algorithms are strongly linearisable with respect
to `SeqSketch_{Nb}` and `SeqSketch_{2Nb}`, for every composable sketch, provided the threads' initial hint is the
empty sketch's hint (Algorithm 2 hard-codes `1`, which is right for the Θ sketch but not in general). The simulation
behind Theorem 1, the paper's main correctness result, does not preserve histories, so Theorem 1 took a new direct
invariant proof; we prove both results in a stronger form, which is the one the error analysis needs. The error bounds
of Section 6 check out algebraically, with the order-statistic moments of §6.1 taken as hypotheses.

## Mistakes in the paper

### 🔧 Lemma 1 and Theorem 1 (Algorithm 2's initial hint `1`)
Algorithm 2 starts with `hint_i = prop_i = 1`, which breaks Lemma 1 and Theorem 1 for general
composable sketches: an exact counter whose `calcHint` always returns `2` and with
`shouldAdd(h, a) = (h ≠ 1)` meets all requirements, but drops every update forever
(`parSketch_hint_one_not_stronglyLinearizable`).

**Impact.** For the paper's Θ sketch, `1` is exactly the empty sketch's Θ, so only the generic claim is affected. With
"initial hint = hint of the empty sketch" both results hold (`lemma1`, `theorem1`).

**Details.** The pre-filtering requirement of Section 5.1 only constrains `shouldAdd(h, ·)` for hints
`h` produced by `calcHint()`. So the first batch of every thread is filtered with a hint about which
nothing is assumed. With the counter above and `N = b = 1`, two completed updates followed by two
queries returning `0` is an execution with no linearization in `SeqSketch_{Nb}`.

**Repair.** We prove both results with "initial hint = hint of the empty sketch" (more generally, any
hint that filters harmlessly on every stream). (`lemma1`, `theorem1`)

### 🔧 Section 5.3 (exactness of the sequential Θ sketch, off by one)
"The sequential Θ sketch answers queries with perfect accuracy in streams with up to `k` unique
elements" holds for Algorithm 1 only up to `k − 1` distinct hashes: with exactly `k`, the initial `1` is
evicted and the estimate becomes `(k−1)/Θ`, for every `k` (`thetaSketch_query_exact`,
`thetaSketch_query_of_le`; smallest instance `thetaSketch_not_exact_k`).

**Impact.** A remark motivating eager propagation; nothing depends on it. The same off-by-one appears in "Θ is
1 during the first `k` updates".

### Typos
- Update threads are indexed `0 ≤ i ≤ N` (`t₀` is the propagator).
- `hint_i` and `prop_i` are declared `int` but carry real Θ values.
- Section 6.1 has a broken reference, "the RSE bound of Lemma ??".

## Proof gaps (statements true)

### 🛠️ Theorem 1 (simulation by `ParSketch`)
Section 5.2 announces a proof of Theorem 1 by simulating `N` `OptParSketch` threads with `2N` `ParSketch` threads, and
the full version carries it out, but the mapping does not preserve histories.

**Impact.** Statement true; the simulation is not repaired, and we prove Theorem 1 directly instead, by a separate
invariant argument (`theorem1`).

**Details.** An update that fills a buffer returns in `OptParSketch` while the simulating `ParSketch`
update still waits at line 125, and in the first round line 225 is mapped to line 125 of a thread with
no pending operation.

### 🔧 Definition 2 vs. Section 6 (what "strongly linearisable w.r.t. `SeqSketch_r`" gives)
Definition 2 is weaker than what Section 6 uses: an `r`-relaxation may drop queries and may place an
operation after arbitrarily many operations that follow it (`isRelaxation_drop`,
`isRelaxation_future`).

**Impact.** The algorithms satisfy the stronger property Section 6 needs; we prove Lemma 1 and Theorem 1
in this form (`lemma1_pastOnly`, `theorem1_pastOnly`).

**Details.** An `r`-relaxation may drop up to `r` operations altogether, including queries, which may
then return anything. It may also put an operation after arbitrarily many operations that follow it in
`H'`: `U, q` is a `1`-relaxation of `q, U` for every list of updates `U`. So "strongly linearisable
w.r.t. `SeqSketch_r`" does not by itself give the model of Section 6 ("a query misses up to `r` of the
updates preceding it"), on which the error bounds rest.

**Repair.** In the witnessing relaxation no query is dropped, and a query is preceded only by operations
that precede it in the linearization. (`lemma1_pastOnly`, `theorem1_pastOnly`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared memory: an interleaving of atomic accesses to base objects. The paper
  assumes a weaker memory with fences, but its proofs also reason with atomic steps. No failures.
  The scheduler is arbitrary; we prove safety only.
* Processes: `N ≥ 1` update threads, the propagator `t₀` (started by a never-returning `propagate`
  operation), and any number of query threads. The propagator scans the threads round-robin.
* Base objects: the composable global sketch is atomic (`merge`, `snapshot`, `calcHint`). The paper
  requires its `snapshot`/`merge` to be strongly linearisable and treats them as atomic steps. There
  are also local sketches (`update`, `read`, `reset`), atomic registers `prop_i : Option Hint`
  (`none` = 0), and for `OptParSketch` registers `cur_i`.
* Sketches are derandomised, as in Section 4 (coins fixed by an oracle). A `Composable` sketch carries
  the paper's requirements as hypotheses: merge of summaries summarises the concatenation; snapshots
  answer like the sketch; `shouldAdd(calcHint(S), a) = false` ⇒ `a` can be removed from any
  extension of the stream summarised by `S`. Everything is generic in the sketch.
* `SeqSketch` is the set of histories of the sequential sketch. `SeqSketch_r` is Definition 2, taken
  literally. Strong linearisability w.r.t. a set of histories (Definition 1) is a prefix-preserving
  map from executions to linearizations in that set (`Impl.HStronglyLinearizable`). The witness is
  the paper's `l` (updates at invocation, queries at their snapshot). The relaxed history is the
  paper's `f` (visibility points), computed by a ghost run.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (`ParSketch` strongly lin. w.r.t. `SeqSketch_{Nb}`) | `lemma1` | `ParSketchMain.lean` |
| Lemma 1, form used by Section 6 (no query dropped, queries see only the past) | `lemma1_pastOnly` | `ParSketchMain.lean` |
| Theorem 1 (`OptParSketch` strongly lin. w.r.t. `SeqSketch_{2Nb}`) | `theorem1` | `OptParSketchMain.lean` |
| Theorem 1, form used by Section 6 | `theorem1_pastOnly` | `OptParSketchMain.lean` |
| Initial hint `1` fails in general | `parSketch_hint_one_not_stronglyLinearizable` | `Counterexample.lean` |
| Definition 2 drops / reorders | `isRelaxation_drop`, `isRelaxation_future` | `Relaxation.lean` |
| Composable Θ sketch (Alg. 1 + API meets Section 5.1) | `thetaComposable` | `ThetaSketch.lean` |
| Lemma 1 / Theorem 1 for the Θ sketch with hint `1` | `lemma1_theta`, `theorem1_theta` | `Examples.lean` |
| §6.2 / full Lemma 10 (quantiles, `ε_r = ε − rε/n + r/n`) | `quantile_relaxed_rank`, `quantile_relaxed_prob` | `ErrorBounds.lean` |
| Full Claim 1 (`j ∈ {0, r}` maximises the error) | `abs_est_sub_le_max` | `ErrorBounds.lean` |
| Full Lemma 9 (RSE ≤ σ/n + bias/n) | `sqrt_expect_sq_sub_le` | `ErrorBounds.lean` |
| §6.1 weak adversary (eqs. (3), (4); `≤ 2/√(k−2)` for `r ≤ √(k−2)`) | `rse_weak_lt`, `weak_rse_bound_le_two` | `ErrorBounds.lean` |

**Not formalized.** The order-statistic moments of uniform samples used in §6.1 are hypotheses of
`rse_weak_lt`. Also not formalized: the strong adversary (numerical in the paper), Tables 1–2, the
experiments, the adaptive eager phase (§5.3), and Quantiles/HLL instances.

**Full version.** These remarks concern the journal version only and are not findings about the formalized text:
- Lemma 6 overlooks updates that are invoked but have not yet run `shouldAdd`: they have no visibility point and are
  not in `up_suff_i`. The statement is true: the bound `Nb` survives because such an update can only be pending while
  `counter_i < b`.
- Lemma 1 is stated with `r = 2Nb` but proved with `Nb` (the PODC version says `Nb`).
- The extreme order statistics of Claim 1 are written `M(0)`, `M(j)`, and Claims 4–6 write `i, j > 0` for `i, j ≥ 0`.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `thetaComposable` instantiates all hypotheses with the paper's Θ sketch,
and `lemma1_theta`, `theorem1_theta` apply Lemma 1 and Theorem 1 to it with the paper's literal
initial hint. The model is built on
CSLib's `Cslib.SharedMemory` (`Impl`, executions, linearizations). The new generic notion of
strong linearisability w.r.t. a set of histories is staged in
`Podc/Computability/Distributed/SharedMemory/HistorySpecLin.lean` (CSLib candidate). The step
lemmas in `ExecLemmas.lean` and `kSmallest` in `ThetaSketch.lean` are also CSLib candidates.
