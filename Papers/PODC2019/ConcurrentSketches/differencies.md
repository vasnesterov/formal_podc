# Differences between the formalization and the paper

Paper: Rinberg, Spiegelman, Bortnikov, Hillel, Keidar, Rhodes, Serviansky. *Fast Concurrent Data
Sketches.* PODC 2019 (brief announcement; we use the arXiv version 1902.10995v2, whose numbering is
that of the PODC paper). The PODC version defers all proofs to "the full paper [24]"; the proofs we
checked are those of the journal version (ACM TOPC 9(2), 2022, author copy
`iditkeidar.com/wp-content/uploads/2021/12/ConcurrentSketches.pdf`): Section 6 (Lemmas 2–8,
Invariants 1–3) and Section 7 (Claims 1–6, Lemmas 9–10).

## Statement-level issues

1. **The initial hint `1` (Algorithm 2, lines 108–109; Lemma 1, Theorem 1).** `hint_i` and `prop_i`
   start at the constant `1`, but `shouldAdd(h, a)` is only required to be safe for hints `h`
   returned by `calcHint()` of a sketch that summarises a prefix of the stream. For a composable
   sketch whose empty-sketch hint is not `1`, the first batch of every thread is filtered with an
   unconstrained hint and Lemma 1 / Theorem 1 fail: `cntSketch` (an exact counter, hints always `2`,
   `shouldAdd h a = (h ≠ 1)`) satisfies every requirement of Section 5.1, yet with `N = b = 1`
   two completed updates followed by two queries returning `0` is an execution of `ParSketch` with
   no linearization in `SeqSketch_{Nb}` (`parSketch_hint_one_not_relaxed`,
   `parSketch_hint_one_not_stronglyLinearizable`, `Counterexample.lean`). We prove Lemma 1 and
   Theorem 1 under the hypothesis `S.Safe hint₀ []` (filtering by `hint₀` is harmless on every
   stream), which holds for `hint₀ = calcHint(empty sketch)` (`safe_init_hint`). 🔧 The intended
   reading ("the hint of the empty sketch") is recoverable from the paper (hints
   are otherwise always produced by `calcHint`; for the only instantiation, the Θ sketch, `Θ = 1`
   initially — `theta_calcHint_init`; the "trivial" implementation `shouldAdd ≡ true` does not care),
   and the fix is local (an initial value). The full version explicitly claims
   the algorithm works for "any composable sketch adhering to the API" (arXiv v2 only calls the
   algorithm "generic" and states Lemma 1 / Theorem 1 for "`ParSketch` instantiated with" the
   sketch). This is a wrong initial value, not a gap in the design: the repair (initialise `hint_i`,
   `prop_i` with `globalS.calcHint()` of the empty `globalS`) keeps the claim for every composable
   sketch, with no extra assumption on the sketch. The
   journal proof (Invariant 3, case `shouldAdd` false: "let `H` be the last hint returned to
   `t_i`") already reasons with hints produced by `calcHint`, i.e. with the intended version.
   Note that in `OptParSketch` the initial `prop_i = 1` is also copied into `hint_i` at the first
   buffer switch (line 125 passes at once), so both initial values need the fix; the
   formalization uses `hint₀` for both.
2. **Section 5.3: "the sequential Θ sketch answers queries with perfect accuracy in streams with up
   to k unique elements"** (and Section 3: "Θ is 1 during the first k updates"). For Algorithm 1
   (read with set semantics, the only reading under which the claim can hold) the query is exact
   only for at most `k − 1` distinct hash values; with exactly `k` the initial `1` is evicted and the
   estimate is `(k − 1)/Θ` (`thetaSketch_query_exact`, `thetaSketch_query_of_le`,
   `thetaSketch_not_exact_k`). If "init k 1's" is read as a multiset, the estimate is `(k−1)/Θ`
   from the first update on and never exact. A remark motivating eager propagation, off by one;
   🔧 The fix changes the number, but the intended meaning ("exact until the
   sample set is full", Section 3) is recoverable, it is an index-level slip caused by the sentinel
   `1` occupying a slot of Algorithm 1's sample set, and nothing in the paper depends on it. (For
   the library sketch of Section 7, whose exact mode is not tied to a sentinel, the sentence may well
   be true; it is false for the paper's own Algorithm 1.) The failure holds for every `k`
   (`thetaSketch_query_of_le`: estimate `(k − 1)/Θ` with `Θ < 1`); `thetaSketch_not_exact_k` is
   only the smallest instance (`k = 1`).
3. **Definition 2 is weaker than what Section 6 uses** (not a false statement; it makes Lemma 1 and
   Theorem 1 *weaker* than the paper's use of them). (a) An `r`-relaxation may drop up to `r`
   entries, including queries, so up to `r` queries of a history in `SeqSketch_r` may return
   arbitrary values (`isRelaxation_drop`). (b) An entry of the relaxation may be preceded by
   arbitrarily many entries that *follow* it in `H'`: `U ++ [q]` is a `1`-relaxation of `q :: U` for
   every `U` (`isRelaxation_future`), so a query may reflect any number of later updates. Section 6
   ("By Theorem 1, a query can miss up to r updates"; "Given Theorem 1, the optimised concurrent
   sketch's error is bounded by the relaxation's error bound") models only queries that see all but
   at most `r` of the *preceding* updates. This does not follow from Theorem 1 as stated, but it does
   follow from the paper's proof: we prove the stronger property `SeqSketchRPast` (no query dropped;
   a query is preceded in the relaxed history only by operations that precede it in the
   linearization), `lemma1_pastOnly`, `theorem1_pastOnly`. Proof gap in the step from Section 5 to
   Section 6, statements true. 🔧

## Versions

The PODC 2019 publication (DOI 10.1145/3293611.3331567, pp. 207–208) is a two-page brief
announcement. The file `papers/2019/3293611.3331567_…pdf` and our `paper.pdf` are arXiv
1902.10995**v2** (Dec. 2019), which is the PPoPP 2020 text (it even cites the PODC brief
announcement as "the full paper [24]"). Differences that matter for the checked claims:
* Lemma 1 (`Nb`) and Theorem 1 (`2Nb`) and Algorithm 2 (including `hint_i`, `prop_i` init `1`) are
  identical in v1 (Feb. 2019, contemporaneous with the brief announcement; proofs in its Appendix A),
  v2 and the journal version (which states Lemma 1 with `2Nb`, item 6).
* The Section 5.3 sentence "perfect accuracy … up to `k` unique elements" is in v2 / PPoPP / journal,
  not in v1; "Θ is 1 during the first `k` updates" (Section 3) is in v1 and v2.
* The quantiles bound `ε_r = ε − rε/n + r/n` (Section 6.2) is from v2; v1 has a different
  quantiles analysis (its Lemma 3), which we did not check.
* The phrase "any composable sketch adhering to the API" is only in the journal version.
Our findings concern Lemma 1 and Theorem 1 (common to all versions) and the v2 claims listed above.

## Proof-level issues (statements true)

4. **Lemma 6 of the full version** says "the only updates without a visibility point are those in
   `up_suff_i(σ)`". An update that has been invoked but has not yet executed line 120 (`shouldAdd`)
   has no visibility point either and is not in `up_suff_i`. The bound `|f(σ)| ≥ |l(σ)| − Nb` still
   holds, because such an update can only be pending while `counter_i < b`, i.e. while
   `|up_suff_i| ≤ b − 1`. In our model `shouldAdd(hint_i, a)` is evaluated at the invocation (it is a
   local computation on the thread's own variable), so the issue disappears; the count is
   `Inv.allButAtMost` (from `TI.length_le`). This is a claim inside a proof of a true lemma, in the
   journal version only.
5. **Theorem 1's proof (full version, Section 6.3)** simulates one `OptParSketch` thread by two
   `ParSketch` threads and appeals to "forward simulation ⇒ strong linearisability". The mapping
   does not preserve histories: the update that fills a buffer returns in `OptParSketch` right after
   line 229, while in the simulating `ParSketch` execution the corresponding update of `t_i^cur` is
   still waiting at line 125 (its response comes one batch later); in the first round the inactive
   simulated thread `t_i^1` has no pending update at all when line 225 is mapped to its line 125.
   So the simulated execution is not an execution of `ParSketch` with the same history, and the
   generic simulation theorem does not apply as stated; the conclusion holds because the specific
   linearization (updates at invocation) ignores update responses. We do not formalize the
   simulation; we prove Theorem 1 directly with the same invariant method as Lemma 1
   (`OptParSketchInv.lean`, `OptParSketchStep.lean`, `OptParSketchMain.lean`). 🛠️.
6. **Full version, Lemma 1 states `r = 2Nb`** for `ParSketch` but proves `Nb`; the PODC version
   states `Nb`. We prove `Nb`.
7. **Error analysis (Section 6 / full version Section 7).** Checked algebraically
   (`ErrorBounds.lean`): the quantiles bound `ε_r = ε − rε/n + r/n` (Lemma 10; the PODC version has
   no assumption on `ε`, the full version assumes `ε < 1/2`; the computation needs only `ε ≤ 1`, and
   with genuine ranks `0 ≤ ρ ≤ n − m` and `r ≤ n` it holds for every `ε`:
   `quantile_relaxed_rank_of_rank_le`; the failure for `ε > 1` in `quantile_relaxed_rank_fails` uses
   a "rank" larger than the stream, so it is outside the paper's model); Claim 1 (extremes at
   `j = 0` or `j = r`; the full version writes `M(0)`, `M(j)` for the extreme order statistics);
   Lemma 9 (an equality written as `≤`, harmless); the weak-adversary bounds (eqs. (3), (4)) and
   the corollary "RSE ≤ 2/√(k−2) when r ≤ √(k−2)". All correct. Claims 4–6 of the full version write
   `i, j > 0` where `i, j ≥ 0` is meant (typo).

## Modelling choices

* **Memory model.** The paper assumes a non-sequentially-consistent memory with fences on atomic
  variables; its proofs reason about atomic steps in an interleaving semantics. We use CSLib's
  asynchronous shared-memory model (sequentially consistent interleaving of atomic accesses to base
  objects), as the proofs do.
* **Global sketch.** The paper requires concurrent `snapshot`/`merge` executions of the composable
  sketch to be strongly linearisable and then treats them as atomic steps; we model the global
  sketch as one atomic base object (`globObj`). `snapshot` returns an element of an abstract type
  `Snap` with `snapQuery (snapshot s) = query s` (the paper's requirement on `snapshot`).
* **Derandomised sketch.** As in Section 4, the sketch is deterministic (coins fixed by an oracle):
  `Sketch` with `init/update/query`; a state *summarises* a stream iff it equals `run` of the stream
  (the paper's definition). `Composable` adds `merge` with `merge (run A) (run B) = run (A ++ B)`,
  `snapshot`, `calcHint`, `shouldAdd` with the paper's filtering requirement (`shouldAdd_spec`).
  The requirement `calcHint() ≠ 0` is built in: `prop_i : Option Hint`, `none` = 0.
* **Propagator.** "for all `t_i` with `prop_i = 0`" is a deterministic round-robin scan (`pCheck j`
  reads `prop_j`, then moves to `j + 1`); any other scan order would be a special case of
  nondeterminism the proof does not use. Since CSLib processes act only while they have a pending
  operation, the propagator is started by a never-returning operation `propagate` that only `t₀`
  may invoke (it never appears in linearizations). `globalS.merge(localS_i)` is split into reading
  `localS_i` and merging the value read (`localS_i` is accessed only by `t₀` at that time).
  `prop_i ← globalS.calcHint()` reads the hint, then writes it.
* **Update threads.** `shouldAdd(hint_i, a)` is evaluated at the invocation; `wait until
  prop_i ≠ 0; hint_i ← prop_i` uses the value read by the last iteration of the wait loop (`prop_i`
  cannot change while it is non-zero). In `OptParSketch`, `cur_i` is a shared register written only
  by `t_i` and read by `t₀`; lines 226–228 are one step (the write of `cur_i`).
* **Processes.** `N ≥ 1` update threads `upd i`, the propagator, and any type `Q` of query threads,
  each of which may invoke only its kind of operation. The paper's "`0 ≤ i ≤ N`" for update threads
  is read as `1 ≤ i ≤ N` (typo: `t₀` is the propagator).
* **Hints and counters** are of arbitrary types (the paper declares `int hint_i`, `int atomic
  prop_i`, although the Θ sketch's hints are reals in `(0, 1]`).
* **`b ≥ 1`** is assumed (with `b = 0` no thread ever propagates; degenerate).
* **Strong linearisability w.r.t. a set of histories** (Definition 1 with `SeqSketch_r` in place of
  `SeqSpec`) is `Impl.HStronglyLinearizable` (staged in
  `Podc/Computability/Distributed/SharedMemory/HistorySpecLin.lean`): a prefix-preserving map from
  executions to linearizations (entries carry responses; completed operations included, real-time
  order respected, pending operations may be included) whose histories lie in the set.
  `SeqSketch` is the set of histories legal for the derandomised sketch.
* **Definition 2** is formalized literally on lists of entries (`IsRelaxation`): "all but at most
  `r`" is "up to a list `D` of at most `r` exceptions"; "`y` precedes `x` in `H`" is `[y, x] <+ H`.
* **Not formalized:** the Θ sketch's order-statistic moments (taken as hypotheses in
  `rse_weak_lt`), the strong adversary (numerical only in the paper), Table 1, the experiments
  (Section 7), the adaptive eager phase of Section 5.3 (a variable `b`), and Quantiles/HLL sketches
  as instances.
