# Sinkless orientation made trivial — PODC 2026

Alexandre Nolin. *Brief Announcement: Sinkless Orientation Made Trivial.* PODC 2026. DOI
[10.1145/3796701.3815953](https://doi.org/10.1145/3796701.3815953). Formalized version: the 4-page brief
announcement (HAL `hal-05678283`); no full version was found.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct (deterministic part).** The paper's proofs are sketches; filled in, they hold. This covers
the min-ID orientation (Theorem 2.1), the ball-growth Lemma 2.2, the repair procedure (Lemma 2.3) and the
deterministic `O(log_δ n)` sinkless orientation of Theorem 1.1. We also prove the "obvious" tightness remark
after Theorem 2.1. We found only typos and imprecisions. The randomized part relies on external reductions and is
not formalized.

## Mistakes in the paper

No error affects the results. Minor slips and remarks:

- **Lemma 2.2, "in particular" (typo).** The ball of radius `⌈log_{δ−1} n⌉` contains "a node of degree `δ` or a
  cycle". It should read "degree `< δ`", which is what the main statement (item (i)) gives and Algorithm 2 uses
  (`lemma_2_2_clog`). The paper gives no proof of Lemma 2.2 ("the argument is standard").
- **Definition of `k`-sinksparse.** The definition asks for sinks at distance `≥ k`, but the proof of
  Theorem 2.1 gives `> k`; we use the stronger `> k`.
- **Redundant hypothesis.** The hypothesis `r ≥ 1` of Lemma 2.2 is redundant: for `r = 0` the bound is 1.
- **Section 3 phrasing (remark, not an error).** "At least `max(ε deg(v), 1)` outgoing and incoming edges" is
  meant for minimum degree `δ ≥ 3`. Read literally for arbitrary graphs, it is impossible at degree-1 nodes: a
  single edge has no such orientation (`no_orientation_in_and_out_single_edge`).
- **Constants.** Algorithm 1's `k = 4⌈log_{δ−1} n⌉` is twice what is needed; we keep the paper's value. The
  tightness of Theorem 2.1 is only asserted ("obviously tight, even in LOCAL").

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Deterministic, synchronous, fault-free LOCAL with unique identifiers; every node knows `n`. No randomness.
- Round complexity is *locality*. An orientation algorithm `A : ∀ G, Orientation G` is `R`-local if the
  direction of each edge `uv` is the same in any two graphs that agree on all edges incident to nodes at distance
  `< R` from `u`, i.e. on what `u` learns in `R` rounds. Since `A` sees the node set `V`, a rule may depend on
  the global identifier set, slightly more than standard LOCAL. This is harmless for the explicit algorithms and
  makes the lower bound stronger.
- Theorem 2.1 is also implemented as an explicit flooding algorithm in CSLib's synchronous SET-LOCAL model, with
  `O(log n)`-bit states. CONGEST message sizes are otherwise not modelled.
- Graphs: Theorem 2.1 and Lemma 2.3 hold for any (even infinite) simple graph; Lemma 2.2 and Theorem 1.1 assume
  a finite node set.
- Tie-breaking in Algorithm 2 uses a fixed choice function. The proofs use only the specifications of the
  choices, so ID-based tie-breaking is covered as well.

**Main results in Lean** (namespace `SinklessOrientation`).

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1: correctness, `k+1` rounds | `minIdOrientation_isSinkSparse`, `minIdOrientation_isLocal` | `MinId.lean` |
| Theorem 2.1 as an explicit flooding algorithm | `theorem_2_1` | `MinIdRun.lean` |
| Tightness remark after Theorem 2.1 | `sinkSparse_lower_bound` | `LowerBound.lean` |
| Lemma 2.2 (+ "in particular") | `lemma_2_2`, `lemma_2_2_clog` | `Lemma22.lean` |
| Lemma 2.3 (correctness; `2⌊k/2⌋+1` rounds) | `lemma_2_3`, `repairOrientation_isLocal` | `Main.lean`, `Reorient.lean` |
| Theorem 1.1, deterministic: no `δ`-sinks in `16⌈log_δ n⌉ + 2` rounds | `theorem_1_1` | `Main.lean` |

The tightness proof is the classical reflection argument. A `T`-local algorithm with `2T + 2 ≤ k` (given
`2T + 2 + 3k` identifiers) puts two sinks on some `(k+1)`-node path. So `k`-sinksparse orientations need about
`k/2` rounds, while `k + 1` suffice.

**Not formalized.** The randomized part of Theorem 1.1 and Corollary 1.2 (they rely on the shattering and
reduction results of Ghaffari–Su and Ghaffari et al.), the CONGEST implementation of Algorithm 2, and the cited
`Ω(log_δ n)` / `Ω(log_δ log n)` lower bounds.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
SET-LOCAL round model of `theorem_2_1` is CSLib's `Cslib.LocallyIterative`.
