# Tight Bounds on Channel Reliability via Generalized Quorum Systems — PODC 2025

Alejandro Naser-Pastoriza, Gregory Chockler, Alexey Gotsman, Fedor Ryabinin. *Tight Bounds on Channel Reliability via
Generalized Quorum Systems.* PODC 2025. DOI [10.1145/3732772.3733529](https://doi.org/10.1145/3732772.3733529).
Formalized version: arXiv [2505.02646](https://arxiv.org/abs/2505.02646) v1 (proceedings text plus appendices);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The lower bounds hold: Lemma 2, Theorem 2 (lattice agreement, MWMR registers,
SWMR snapshots, and also consensus) and Theorem 6 (partial synchrony) are proved for arbitrary deterministic
algorithms, together with Proposition 1. Two fixes are needed: the value domain must be non-trivial (otherwise
Theorem 2 is false), and "strongly connected" must be read as mutual reachability in `G \ f` (otherwise Proposition 1
is false). The upper bounds (Theorems 1, 4, 5) are not formalized; for the quorum access functions of Figure 3 we
formalize the protocol and its safety (see the table).

## Mistakes in the paper

* **Theorem 2 needs a non-trivial object (false in a degenerate case).** The proof picks two incomparable elements
  `x₁, x₂` of the semi-lattice, but the theorem is stated for lattice agreement over any semi-lattice. Over a chain
  (e.g. `ℕ`), returning one's own proposal immediately is a safe, wait-free lattice agreement algorithm that never
  communicates. Under the fail-prone system "one of two processes may crash" (`τ(f)` = the correct process), no
  generalized quorum system exists. The same algorithm shows that registers, snapshots and consensus need at least two
  values. We add these hypotheses; with them, everything holds. (`theorem_2_false_of_chain`)
* **Ambiguous phrase "strongly connected in `G \ f`" (Proposition 1; not an error under the natural reading).** If it
  meant that the induced subgraph is strongly connected, Proposition 1 would be false. Take processes `0, 1, 2`, with only the channels `0 ↔ 1` failing, and
  write quorums `{0}`, `{1}` reachable from the read quorum `{0, 1}`. Then `U = {0, 1}`, but `0` and `1` reach each
  other only through `2`. The proof of Proposition 1 and the definition of `U_f` as a strongly connected component use
  mutual reachability in `G \ f`; with that reading everything is correct, and this is the reading we formalize.
  (`proposition_1_false_induced`, `proposition_1`)
* **`U_f` is not determined by `F`.** The remark after Theorem 2 calls `U_f` "the largest set of processes for which
  termination can be guaranteed". But `U_f` depends on the quorum system. With two processes and only the channel
  `0 → 1` reliable, both `({0},{0})` and `({0,1},{1})` are generalized quorum systems, with `U_f = {0}` and
  `U_f = {1}`. Termination can be guaranteed at `{0}` or at `{1}`, but not at both (Lemma 2). The theorems themselves
  are unaffected. (`Uf_not_unique`)
* **Proof gaps, statements true.** Theorem 2 for registers and snapshots is derived from the constructions of [2, 11],
  and Theorem 6 from "consensus implements an MWMR register". Neither reduction is checked in this failure model with
  obstruction-freedom at `τ(f)` only, and a single-shot consensus object needs infinitely many instances. For
  Theorem 6 the paper only argues that `σ` is finite; one also needs the executions `α₁, β₁` to be partially
  synchronous. We avoid the reductions: one gluing argument proves the bound for every object with two conflicting
  operations, and it uses liveness only through one canonical continuation, which is both fair and partially
  synchronous. (`theorem_2_register`, `theorem_2_snapshot`, `theorem_6`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (staged shared library `Podc/Computability/Distributed/MessagePassing/ChannelFailures/`, namespace
`Cslib.ChannelFailures`).
* Asynchronous message passing among finitely many processes, deterministic event-driven algorithms (invocations,
  spontaneous steps reading a local clock, receptions), FIFO channels (a restriction of the adversary, which only
  strengthens lower bounds). Determinism is without loss of generality: the paper's liveness is "returns in every fair
  execution", so a nondeterministic algorithm can be replaced by a deterministic refinement; probabilistic
  termination is not considered by the paper. Histories are CSLib `Label`s; registers and snapshots use CSLib linearizability.
* A failure pattern `(procs, chans)` enters only fairness: crashed processes stop taking steps, disconnected channels
  stop delivering (a suffix of their messages is lost); all other processes take infinitely many steps and all other
  channels between them deliver every message. This is exactly the paper's `f`-compliant fair execution. Finite
  executions are failure free; safety is required for all of them.
* `(f, T)`-obstruction-freedom and wait-freedom as in §2. Partial synchrony (§7): discrete time with GST and `Δ`,
  non-drifting clocks after GST, and a step of every correct process per time unit.
* The lower bounds quantify over all algorithms, message types and local states.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 2 (GQS), Definition 1, their equivalence without channel failures | `IsGQS`, `IsQS`, `isGQS_iff_isQS` | `Defs.lean` |
| Proposition 1 (`U` strongly connected); `U_f` | `proposition_1`, `Uf`, `Uf_stronglyConnected` | `Defs.lean` |
| Lemma 2 (obstruction-freedom set is strongly connected) | `lemma_2_lattice_agreement`; generic `lemma_2` | `Main.lean`, `LowerBound.lean` |
| Theorem 2 (GQS necessary, `τ(f) ⊆ U_f`) | `theorem_2_lattice_agreement`, `theorem_2_register`, `theorem_2_snapshot` (+ `theorem_2_consensus`); generic `theorem_2_generic` | `Main.lean`, `LowerBound.lean` |
| Claims 1–2 (closed sets in `G \ f`) | `closed_reachTo`, `closed_reachTo_not` | `LowerBound.lean` |
| Theorem 6 (consensus, partial synchrony) | `theorem_6` (+ `theorem_6_lattice_agreement`) | `Main.lean` |
| Partitioning core (`σ` is an execution, indistinguishability) | `Cslib.ChannelFailures.glue`, `agree_run_filter` | `Podc/…/ChannelFailures/{Glue,Restrict}.lean` |
| Examples 2, 7, 8 (Figure 1 is a GQS; `R₁` not strongly connected) | `figure_1_isGQS`, `figure_1_R1_not_stronglyConnected` | `Examples.lean` |
| Example 9 (`F'` admits no GQS) | `example_9` | `Examples.lean` |
| Proposition 2 (views overlap for ≥ `d` eventually), abstract real-time form | `proposition_2` | `ViewSync.lean` |
| Degenerate value domains | `theorem_2_false_of_chain` | `Counterexamples.lean` |
| Figure 3: Validity, Lemma 1 + Theorem 3 (real-time ordering) | `QA.validity`, `QA.realtime_ordering` (protocol `QA.qaAlg`) | `QuorumAccess.lean`, `QuorumAccessProof.lean` |

**Not formalized.** The upper bounds: Theorem 1, the liveness of Figure 3 (Theorem 4), the register protocol of
Figure 4 with Appendix B, and Theorem 5 with the protocol of Figure 6. Also not formalized: the
reductions [2, 11], which our direct proofs make unnecessary.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: fair and partially synchronous executions exist from every finite prefix (`fair_extend_canon`,
`ps_extend_canon`). `echoAlg` is a safe, wait-free algorithm that meets the hypotheses of Theorem 2 except
non-triviality. The model is staged in `Podc/` as a CSLib candidate. It reuses CSLib's
`Digraph.ReachableAvoiding`, `Label`, `IsLinearization` and `register`.
