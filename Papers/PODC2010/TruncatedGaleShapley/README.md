# Almost Stable Matchings in Constant Time — PODC 2010

Patrik Floréen, Petteri Kaski, Valentin Polishchuk, Jukka Suomela. *Brief announcement: Almost stable
matchings in constant time.* PODC 2010, pp. 281–282. DOI
[10.1145/1835698.1835765](https://doi.org/10.1145/1835698.1835765). Formalized version: the full paper
*Almost Stable Matchings in Constant Time*, arXiv [0812.4893](https://arxiv.org/abs/0812.4893) v1;
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** All three theorems hold with the paper's constants:
truncated Gale–Shapley gives an `ε`-stable matching in `T ≤ 4 + 2Δ²/ε` rounds (also with ties), a
`(2+ε)`-approximate maximum-weight matching in `T ≤ 4 + 2Δ/ε` rounds, and a constant-query
estimator of the size of a stable matching. Lemmas 1–5 are true. Lemma 6 is false as stated in the
degenerate case `Δ = 1`, `i = 1`; it needs `i ≥ 2`, as in Lemmas 4 and 5, which its proof uses.

## Mistakes in the paper

* **Lemma 6 is false for `Δ = 1` (degenerate case; statement repaired).** Lemma 6 claims
  `f_i(R) ≤ γ w_i(B)` for all `γ > 0` and `i ≥ 1 + (Δ-1)/γ`. For `Δ = 1` this allows `i = 1`. But
  after round 1 nothing is matched (`w_1(B) = 0`), while every red node has a pending proposal
  (`f_1(R) > 0`). The smallest counterexample is a single edge `K₂`, which has maximum degree 1
  and no isolated nodes. The proof combines Lemmas 4 and 5, which are stated only for
  `i ≥ 2`. With the extra hypothesis `i ≥ 2` the lemma holds. The proofs of Theorems 1 and 2
  inherit the slip: for `Δ = 1` they allow `i = 1`, and `M_1 = ∅` is neither `ε`-stable nor an
  approximation. Both theorems are still true: choosing `i = max(2, ⌈…⌉)` keeps `T = 2i` within
  the claimed bounds. (`lemma_6_false_at_one`; repaired: `Bicoloured.lemma_6`, `theorem_1`,
  `theorem_2`)
* **Small slips in proofs** (statements true):
  - Proof of Lemma 5: "`w({r,b}) < w_j(b)`" should be `≤`. The weights respect the preferences only
    weakly, and with `w ≡ 1` equality holds. Only `≤` is needed.
  - Proof of Theorem 1 with ties: "analogous" hides nothing. The ports refine the weak
    preferences, and every edge unstable for the weak preferences is unstable for the refinement.
    (`theorem_1_ties`)
  - §6.3 treats `Y` (the matched nodes among the first `N` red samples) as a binomial variable
    without saying that the analysis conditions on the sample containing `N` red nodes. The bound
    is correct. We prove it with a martingale (exponential-moment) argument over the sequential
    sampling. (`card_firstHits_abs_sub_ge_le` in `Podc/Probability/Finite/MultiplicativeChernoff.lean`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Distributed model (Theorems 1, 2):** CSLib's anonymous port-numbering model
  (`Cslib.PortNumbering`). It is synchronous and deterministic, with no failures and no identifiers.
  A node knows its degree, its colour (red/blue input) and `T` (built into the algorithm). Its ports
  are numbered by preference (port `0` = favourite). The graph is any simple port-numbered graph
  whose input colouring is proper; isolated nodes are allowed. One GS round is two communication
  rounds (blue turn, red turn), so `T = 2i`. Messages are full local states (`Algorithm.ofLocal`),
  but each node only uses the information the 'propose', 'accept', 'reject' and 'break' messages
  of §4 carry. The output is the port of the partner.
* **Centralised analysis:** `Bicoloured V` is a finite bicoloured graph with strict
  preferences, given as ranks that are injective on the neighbours. `run I i` is the state at the
  end of round `i`, a global synchronous transition. `dec_localRun` proves that after `2i`
  communication rounds the port-level run decodes exactly to `run I i`.
* **Theorem 2:** each node's input is its colour and the weights (nonnegative reals) of its
  edges, given per port. The node ranks its ports by decreasing weight, breaking ties by port
  number, and then runs the Theorem 1 algorithm. `M*` ranges over all matchings.
* **Theorem 3:** randomness is uniform on `(Fin N → V) × (Fin K → V)` (sampling with replacement,
  probability by counting), and the algorithm knows `n`. The oracle is not modelled interactively.
  Instead we prove the three facts the query count rests on: locality (whether `r` is matched in
  `M_j` depends only on the local data within distance `2j`), the bound `< 3(Δ-1)^{2j}` on the
  size of such a ball, and the arithmetic bound on `N + K + N·3(Δ-1)^{2j}`. `M` is the stable
  matching `M_∞` reached by Gale–Shapley, as in the paper's proof.

**Main results in Lean.** Namespace `Podc.TruncatedGaleShapley`.

| Paper | Lean | File |
|---|---|---|
| Definition 1 (`ε`-stable), unstable edges | `PrefGraph.IsUnstable`, `PrefGraph.unstableEdges`, `PrefGraph.IsEpsStable` | `Basic.lean` |
| §4 algorithm (blue/red turns) | `Bicoloured.blueTurn`, `redTurn`, `round`, `run` | `Basic.lean` |
| §4 algorithm, port-numbering model | `rule`, `gsAlg`, simulation `dec_localRun`, `gsAlg_partner` | `Distributed.lean` |
| Invariants (matching, monotonicity) | `Bicoloured.Inv`, `inv_run`, `Inv.red_outcome` | `Invariants.lean` |
| Lemma 1 | `Bicoloured.lemma_1` | `Analysis.lean` |
| Lemma 2, Lemma 3 | `Bicoloured.lemma_2`, `Bicoloured.lemma_3` | `Analysis.lean` |
| Lemma 4, Lemma 5 (for `i ≥ 1`) | `Bicoloured.lemma_4`, `Bicoloured.lemma_5` | `Analysis.lean` |
| Lemma 6 (with `i ≥ 2`) | `Bicoloured.lemma_6` | `Analysis.lean` |
| Lemma 6 as stated is false (`Δ = 1`) | `lemma_6_false_at_one` | `Counterexample.lean` |
| §5.1: convergence, `M_z` stable | `Bicoloured.exists_stable` | `Stable.lean` |
| Theorem 1 (centralised core) | `Bicoloured.theorem_1_rounds` | `Theorems.lean` |
| Theorem 1 (distributed; with ties) | `theorem_1`, `theorem_1_ties` | `Main.lean` |
| Theorem 2 (centralised core) | `Bicoloured.theorem_2_rounds` | `Theorems.lean` |
| Theorem 2 (distributed) | `theorem_2` | `Main.lean` |
| §6.3 (3)–(5), (9) | `Bicoloured.size_Minf_le`, `card_reds_le`, `card_blues_le`, `estimate_error` | `Theorem3Det.lean` |
| §6.3 locality ("information travels 2 hops per round") | `Bicoloured.run_congr_of_agree` | `Locality.lean` |
| Theorem 3 (probability `≥ 1 - δ`) | `Bicoloured.theorem_3_prob` | `Theorem3.lean` |
| Theorem 3 (query count) | `Bicoloured.theorem_3_queries`, `queries_le`, `N3_le` | `Theorem3.lean` |
| Chernoff bound (1) [Janson et al.] | `card_filter_abs_card_filter_mem_sub_ge_le`, `card_firstHits_abs_sub_ge_le` | `Podc/Probability/Finite/MultiplicativeChernoff.lean` |
| Ball size `1 + Δ ∑ (Δ-1)^i < 3(Δ-1)^ρ` | `SimpleGraph.ncard_closedBall_le`, `ncard_closedBall_lt` | `Podc/Foundations/Combinatorics/SimpleGraph/BallCard.lean` |
| §2.2 example (unique stable matchings, edge-disjoint) | `pathPG_unique_stable`, `stable_matchings_disjoint` | `PathExample.lean` |
| §2.4 triangle has no `ε`-stable matching, `ε < 1` | `triangle_not_epsStable` | `Examples.lean` |
| §2.5 no order-based `(2-ε)`-approximation | `no_order_based_two_sub_eps` | `Examples.lean` |

**Not formalized.** The informal interpretations of §2.1 (robustness, Boolean circuits). The
cited impossibility results of §2.5 (Linial; Czygrinow et al.). Equality of the sizes of all stable
matchings (rural hospitals theorem): Theorem 3 is stated for `M_∞`, which is what its proof uses.

**Trust.** No `sorry`; all listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The distributed model is CSLib's `Cslib.PortNumbering`. Hypotheses are
non-vacuous: `k2` (Counterexample.lean) and the path and triangle examples are concrete instances.
New shared code, all CSLib candidates: `Podc/Probability/Finite/MultiplicativeChernoff.lean`, a
multiplicative Chernoff bound by counting with a "first `N` hits" variant, and
`Podc/Foundations/Combinatorics/SimpleGraph/BallCard.lean`, the ball size in bounded-degree
graphs. Paper-local CSLib candidates: the incomplete-preference stable-matching notions
(`PrefGraph`, `PrefGraph.forced`), and `card_filter_fst`/`card_filter_snd` (Theorem3.lean).
