# Pareto-optimal (unbeatable) consensus — PODC 2013

Armando Castañeda, Yannai A. Gonczarowski, Yoram Moses. *Brief announcement: Pareto optimal solutions to
consensus and set consensus.* PODC 2013, pp. 113–115. Formalized version: the full version, arXiv
[1311.6902](https://arxiv.org/abs/1311.6902) v1, *Good, Better, Best! — Unbeatable Protocols for Consensus and
Set Consensus*; numbering follows it.

**Verdict: ❌ False claim.** The main results hold: `Opt0` is an unbeatable consensus protocol (Thm. 2), `OptMaj`
is unbeatable for `t > 0` (Thm. 3), `Opt_min-k` is unbeatable (Thm. 4), and `U-Opt0` is an unbeatable uniform
consensus protocol deciding by `f + 1` / `f + 2` (Thm. 5). But Lemma 10, the core of the `k`-set part, is false as
stated (the same lemma as Lemma 1 of the authors' PODC 2016 paper). Lemma 6 is false when `i` knows of `t`
failures, Corollary 1 (HMW's `P0opt` is beatable) needs `t ≥ 2`, and the proof of Lemma 15 needs a different
inner induction.

## Mistakes in the paper

* **Lemma 10 is false as stated (false numbered lemma; Theorem 4 survives).** This is Lemma 1 of the authors' PODC
  2016 paper, with the same five conditions. With `n = 6`, `k = 2`, `t = 1`, `V = {0, 1, 2}`, a 2-set consensus
  protocol in which low processes decide at once can make process `0` decide `2` at time 1 even though all five
  conditions hold for it with `v = 0`. The "changes" in the proof suppress messages carrying `v` to `j_b`, which
  may need more than `t` crashes. Theorem 4 itself is true: the proof goes through with an extra hypothesis that
  holds wherever Lemma 10 is used. The counterexample and the repair are in
  [`UnbeatableSetConsensus`](../../PODC2016/UnbeatableSetConsensus/README.md). (`lemma10_false`, `theorem4`)
* **Lemma 6 is false when `d = t` (missing hypothesis; recoverable from its proof).** Condition (b), "`K_i(K_j ∃v
  held at m − 1)` for at least `t − d` processes `j`", holds vacuously when `i` knows of `d = t` failures, even if
  `v` occurs nowhere. Example: `n = 3`, `t = 1`, all inputs `1`, process `2` crashes in round 1 sending nothing.
  At time 1, process `0` knows of one failure, so (b) holds for `v = 0`, but `K_0 ∃correct(0)` is false. The proof
  sketch counts "processes knowing `∃0`, including `i` itself", so it assumes `K_i ∃v`. We prove Lemma 6 with
  "`K_i ∃v` and ((a) or (b))". All uses in the paper are consistent with this version. (`lemma6_literal_false`;
  repaired: `lemma6`)
* **Corollary 1 ("`P0opt` of [HMW] is not unbeatable") holds only for `t ≥ 2` (or `t = n − 1`).** We read `P0opt`
  as the paper describes it: decide `0` on `K_i ∃0`; decide `1` after a round in which no new failure became
  known. For `t ≤ 1` (and `n ≥ 3`), `P0opt` makes exactly the same decisions as `Opt0`, so it is unbeatable by
  Theorem 2. The paper's own example ("one failure seen in each of the first two rounds") needs `t ≥ 2`. As a
  refutation of HMW's general claim, the corollary is correct. (`corollary1`; for `t ≤ 1`:
  `p0opt_sameDecisions`, `p0opt_unbeatable`)
* **Lemma 15, proof (statement true; proof repaired).** The inner induction on `|C_i \ Z_i|` does not decrease in
  Case II: the new process `j` does not see `⟨k, m⟩` and may consider more processes possibly alive, so `C_j` can
  be larger than `C_i`. The induction hypothesis is also applied to `j` without checking that `j` knows `∃0` for
  the first time at `m` and does not know `∃correct(0)` at `m`. The counting argument for Part 1 ("fewer Case II
  than Case I invocations") is not needed. We prove Lemma 15 by an induction on `n − |Z_i|`. Case II followed by
  Case I becomes one step `x ~_i x' ~_j x''`: in `x''`, `k` has received `z`'s message, `Z_i` has grown by `k`,
  and the induction hypothesis is applied to `i` itself. The number of failures in these runs never exceeds
  `F⟨i, m+1⟩ + 1 ≤ t`. The base case becomes "`⟨z, m⟩` hidden" (Case C). (`lemma15_part1`, `lemma15_part2`,
  `ic`, `ic_caseII`)
* **Smaller slips.**
  - Theorem 2: the paper says a process deciding `1` must know `never-known(∃0)`. By Agreement this is only a
    precondition for *correct* deciders. The proof works by making `i` correct in the run that contains the
    hidden path.
  - Lemma 2 needs `P0` to decide at the first time `K_i ∃0` holds. This holds because first knowledge happens by
    time `f + 1 ≤ t + 1`.
  - Lemma 17, case `F⟨i, m⟩ = t`: it suffices that only `z` carries `0`. The paper makes every hidden process at
    `m − 1` carry it.
  - Two different results are numbered "Corollary 1" (§3 and Appendix C).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous message passing, crash failures, at most `t` crashes. Theorem 5 and the uniform lemmas assume
  `t < n`, as in the paper's model. A run (adversary) is CSLib's `SyncCrash.Run`: inputs, crash round, and the set
  reached in the crashing round. The model, views and hidden nodes are those of the companion formalization
  `Papers/PODC2016/UnbeatableSetConsensus` (same authors, same model), which this folder imports.
* Full-information protocols: a protocol is a decision rule that depends only on the view (`SameView`, i.e. CSLib's
  `FIIndist`). A process decides at the first time its rule fires while it is alive. The companion's
  `theorem1_lockStep` shows that this covers all deterministic protocols (Coan).
* Consensus is nonuniform `1`-set consensus with inputs `{0, 1}`. Uniform consensus requires that all deciders,
  faulty ones included, agree. Unbeatability (Def. 1): `P` solves the problem, and every solution `Q` with
  `Q ⪰ P` satisfies `P ⪰ Q`. Domination compares decision times per process and per adversary.
* Knowledge `K_i φ` (Def. 2) is truth in all admissible runs where `i` is alive at `m` with the same view.
  `K_i ∃v` is "`v` has been seen" (`Lemma 1`/KoP via `decided_mem_vals`). `K_i(Maj = v)` is characterized
  explicitly (`knows_maj_iff`). `∃correct(v)` means "some correct process knows `∃v` at time `m`".
* No randomness.

**Main results in Lean.** Namespace `Podc.ParetoOptimalConsensus`.

| Paper | Lean | File |
|---|---|---|
| Protocols `P0`, `Opt0`, `Opt1` (`P_a`, `Opt_a`) | `pA`, `optA`, `p0`, `opt0`, `opt1` | `Defs.lean` |
| `Opt_a` solves consensus, decides by `f + 1` | `optA_solves`, `optA_decidesBy_faulty` | `Defs.lean` |
| Lemma 2 | `lemma2` | `Consensus.lean` |
| Lemma 3 | `lemma3` | `Consensus.lean` |
| Lemma 9 for one hidden path | `exists_run_of_hiddenPath` | `Consensus.lean` |
| Theorem 2 (`Opt0` unbeatable; also `Opt1`) | `theorem2`, `opt1_unbeatable`, `theorem2_optA` | `Consensus.lean` |
| Corollary 1 (§3) | `corollary1`, `opt0_dominates_p0opt`, `p0opt_solves` | `P0opt.lean` |
| Corollary 1 needs `t ≥ 2` | `p0opt_sameDecisions`, `p0opt_unbeatable` | `P0opt.lean` |
| `OptMaj`, `K_i(Maj = v)` | `optMaj`, `knows_maj_iff` | `Majority.lean` |
| `OptMaj` solves consensus; Majority Validity | `optMaj_solves`, `optMaj_majorityValidity` | `Majority.lean` |
| Lemma 7 | `lemma7` (core: `time1_forcing`) | `MajorityUnbeatable.lean`, `Time1.lean` |
| Lemma 8 | `lemma8` | `MajorityUnbeatable.lean` |
| Theorem 3 | `theorem3` | `MajorityUnbeatable.lean` |
| Lemma 4, Lemma 11, Theorem 4 | `lemma4`, `lemma11`, `theorem4` | `SetConsensus.lean` |
| Lemma 10, as stated: **false** | `lemma10_false` | `SetConsensus.lean` |
| Lemma 5 | `lemma5` | `UniformDefs.lean` |
| Lemma 6 (with `K_i ∃v`); as stated: **false** | `lemma6`, `lemma6_literal_false` | `UniformDefs.lean` |
| Lemma 13 | `lemma13` | `UniformDefs.lean` |
| Protocols `U-P0`, `U-Opt0` | `uP0`, `uOpt0` | `UOpt0.lean` |
| Theorem 8 (`U-Opt0` solves uniform consensus, `f + 1` / `f + 2`) | `theorem8` | `UOpt0.lean` |
| Lemma 18 | `lemma18` | `UOpt0.lean` |
| Lemma 14, Parts 1 and 2 | `lemma14_part1`, `lemma14_part2` | `UniformForcing.lean` |
| Lemma 15, Parts 1 and 2 | `lemma15_part1`, `lemma15_part2` | `Lemma15.lean` |
| Lemma 16 | `lemma16` | `Lemma16.lean` |
| Lemma 17 | `lemma17` | `Lemma17.lean`, `Lemma17Runs.lean` |
| Corollary 1 (Appendix C) | `corollaryC1` | `Theorem5.lean` |
| Theorem 5 (`U-Opt0` unbeatable, `f + 1` / `f + 2`) | `theorem5` | `Theorem5.lean` |

**Not formalized.** Theorem 1 (KoP) in general; we use its instance for Validity. Also: the topological proof of
Lemma 10 (B.1, B.2), `U-PROT_min-k` and Theorem 6, Theorem 7 and Lemma 19 (last-decider unbeatability), and
Lemma 20 (`O(n log n)` bits).

**Trust.** No `sorry`. All theorems in the table use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The protocols whose unbeatability is proved are proved to solve their problems (`optA_solves`,
`optMaj_solves`, `theorem8`), so the unbeatability statements are not vacuous. Likewise `P0opt` is proved
to solve consensus (`p0opt_solves`), so Corollary 1 is about a genuine solution that `Opt0` strictly dominates.
The hypotheses of Lemmas 14–17 are established inside the proof of Theorem 5. The model comes from CSLib (`SyncCrash.Run`, `DynNet.Journey`,
`HeardOf.FIIndist`) through the companion folder `Papers/PODC2016/UnbeatableSetConsensus`.

**CSLib candidates** (marked `-- CSLib candidate`): the hidden-path and "no hidden path ⇒ sees everything correct
processes see" lemmas (`Defs.lean`); known failures `knownSet` with `guarCrashed_now_iff` and
`le_known_of_hiddenPath` (`UniformDefs.lean`); and the run-surgery tools `deliv_congr`, `sameView_succ_of`,
`seen_succ_self_iff` and `not_seen_of_inv` (`UniformForcing.lean`, `Lemma15.lean`). Together with the companion's
`Views.lean`, these would form a `SyncCrash/FullInfo` module.
