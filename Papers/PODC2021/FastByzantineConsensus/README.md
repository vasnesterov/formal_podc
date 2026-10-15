# Optimal Resilience of Fast Byzantine Consensus — PODC 2021

Petr Kuznetsov, Andrei Tonkikh, Yan X Zhang. *Revisiting Optimal Resilience of Fast Byzantine Consensus.* PODC 2021,
pp. 343–353. DOI [10.1145/3465084.3467924](https://doi.org/10.1145/3465084.3467924). Formalized version: extended
version arXiv:2102.12825v3 (numbering follows it).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** The tight bound holds: for `1 ≤ t ≤ f`, an `f`-resilient `t`-two-step consensus protocol
exists iff `n ≥ 3f + 2t − 1` (`5f − 1` for `t = f`). We proved both directions in one formal model: the lower bound
(Theorem 4.5), and the safety, liveness and two-step property of a concrete implementation of the protocol. The
paper's safety proof has one gap, which we repaired with a harmless extra check.

## Mistakes in the paper

- **Proof gap in protocol safety: votes from "future" views (Sections 3.2–3.3, Appendix A).** A vote
  `(x, u, σ, τ)` sent to the leader of view `v` is valid if its certificates check out. Nothing requires `u < v`.
  During asynchrony, other processes may already be in higher views, so a Byzantine voter can attach a correctly
  certified proposal from some view `u ≥ v`. The highest view `w` among the valid votes can then be `≥ v`. The
  proof's induction on views ("every certified value of an earlier view is safe") cannot be applied to `w`. The
  commit certificate carried in a vote has the same problem. This is a gap in the proof, not a known protocol bug:
  safety of the unmodified protocol is plausibly provable by a different induction, for example on certificate
  creation time. We add the check that a vote for view `v` may only carry a proposal and a commit certificate
  from views `< v`. Correct processes only send such votes, so liveness is unaffected. (`Protocol.ValidBallot`,
  `Protocol.ValidCC`, `Protocol.consistency`)
- **Imprecision: commit certificates in case (3) of the Appendix A.3 safety induction (used for Theorem A.4).** The
  proof argues that a slow-path decision for `x` in view `w` would leave a commit certificate for `x` in view `w` in
  votes′. This needs two things. First, a correct process
  commits only for its current view; this follows from the paper's rule behind Lemma 3.1. Second, "the latest
  commit certificate" must mean the one with the highest view rather than the most recent in time. The two
  coincide once the first point holds. We make both explicit.
- **Theorem 4.5 is false in the degenerate case `f = 1, t = 0`.** Then `3f + 2t − 2 = 1`, and with a single process
  "decide your own input at once" is an `f`-resilient `t`-two-step protocol. This is outside the paper's intended
  scope, since §4.1 assumes `n ≥ 3f + 1` and the protocol assumes `t ≥ 1`. We prove the lower bound for every
  `2 ≤ n ≤ 3f + 2t − 2`, not just `n = 3f + 2t − 2`. (`theorem_4_5_fails_f1_t0`, `no_fastConsensus_of_le`)
- **Unstated hypotheses (not errors).** Lemma 4.4 uses `n ≥ 2t + 2`, which follows from `n ≥ 3f + 1`, and at
  least two input values.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** We use a shared partially synchronous model with Byzantine faults
(`Cslib.Byzantine.PartialSync`).
- `n` deterministic processes, at most `f` of them statically Byzantine. Point-to-point links with **ideal
  unforgeable signatures**; the unauthenticated case is a special case (`theorem_4_5_noAuth`).
- Discrete time with an unknown GST and a known `δ > 0`. Correct processes step at every tick from time 0
  (synchronized, drift-free clocks), as in the paper's §4.1.
- Consensus means weak validity, agreement and termination in every valid run. `t`-two-step (`TwoStep`): in the
  `T`-faulty two-step execution `tsRun` with `|T| = t`, every correct process decides by time `2δ`.
- **Differences from the paper.**
  - Simultaneous deliveries are processed atomically, so the two-step execution is unique rather than "some
    ordering of simultaneous events". The lower bound therefore covers a slightly smaller class of protocols.
  - A reply leaves one tick after its trigger, so the two-step notion matches the paper's only for `δ ≥ 2`. The
    headline theorem assumes `δ ≥ 2`.
- **Positive side.** It is proved twice.
  - First, for an asynchronous interleaving transition system over all emitted signed tokens, with arbitrary
    leaders and view changes. This over-approximates any implementation, so safety transfers.
  - Second, for a concrete algorithm in the model above: gossip of signed tokens, clock-driven views of length
    `6δ + 12`, a rotating leader. Synchronized clocks make a view synchronizer unnecessary, which is friendlier
    than the paper's setting.

**Main results in Lean** (namespace `FastByzantineConsensus`).

| Paper | Lean | File |
|---|---|---|
| Lemma 4.3, Lemma 4.4 (influential process) | `lemma_4_3`, `exists_influential` | `Influential.lean` |
| Executions ρ₁–ρ₅ and their indistinguishability | `rho4_st_eq_rho5_P3`, `rho4_st_eq_rho3` | `Executions.lean` |
| **Theorem 4.5** (no protocol for `n ≤ 3f + 2t − 2`) | `theorem_4_5`, `no_fastConsensus_of_le`, `theorem_4_5_tight` | `LowerBound.lean` |
| Case `n ≤ 3f` (classic bound) | `not_solves_of_le_three_mul` | `SmallCases.lean` |
| Lemmas 3.1–3.5, A.1–A.2, Corollary A.3 | `Protocol.safe_of_certified`, `Protocol.decidedIn_unique`, … | `ProtocolSafety.lean` |
| **Theorem A.4 / Theorem 3.6** (consistency) | `Protocol.consistency`, `Protocol.consistency_five_f` | `ProtocolSafety.lean` |
| Protocol refines the transition system; agreement | `Impl.reachable_absState`, `Impl.algo_agreement` | `ImplSafety.lean` |
| Weak validity; the protocol is `t`-two-step (§4.1) | `Impl.algo_validity`, `Impl.algo_twoStep` | `ImplTwoStep.lean` |
| Termination after GST (§3.3, A.3) | `Impl.algo_termination` | `ImplLiveness.lean` |
| **Tightness: protocol exists iff `n ≥ 3f + 2t − 1`** | `Impl.algo_fastConsensus`, `Impl.tight_bound` | `ImplMain.lean` |

The case `n ≤ 3f` reuses Theorem 1 of the PODC 2023 *Validity of Consensus* formalization.

**Not formalized.** Section 4.3 (suspect sets), Section 4.4 (disjoint proposers and acceptors, `3f + 2t + 1`),
extended validity, and bounded certificate size. The reduction of the vanilla protocol (Theorem 3.6) to the
generalized one with `t = f` is argued on paper, not formalized.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
`leaderEcho_fastConsensus` (`NonVacuity.lean`) shows that `FastConsensus` is satisfiable, and `Impl.algo_fastConsensus`
exhibits a nontrivial instance. The model comes from CSLib, `Cslib/Computability/Distributed/Byzantine/PartialSync/`.
