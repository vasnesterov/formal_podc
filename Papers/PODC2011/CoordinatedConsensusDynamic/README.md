# Coordinated Consensus in Dynamic Networks — PODC 2011

Fabian Kuhn, Yoram Moses, Rotem Oshman. *Coordinated Consensus in Dynamic Networks.* PODC 2011.
DOI [10.1145/1993806.1993808](https://doi.org/10.1145/1993806.1993808). Formalized version: the
10-page proceedings version (no full version exists); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The paper's core results hold, and we proved them:

- Lemma 3.1, the knowledge test for "I have heard from everybody".
- Theorem 5.1: nothing non-trivial is common knowledge before time `n − 1` (known `n`) or `n`
  (unknown `n`). So simultaneous consensus needs exactly `n − 1`, resp. `n`, rounds.
- Theorem 6.1, Lemmas 6.2–6.4, and Theorem 6.7 (the static-line lower bound
  `n − O(Δ^{0.28} n^{0.72})`).

Several statements need fixing:

- Theorem 4.1 is false as stated (quantifier order); the per-`n` version holds.
- Definition 3 (dynamic diameter) is vacuous as written.
- The precise running-time claim for the dynamic-diameter protocol is false, although its final
  bound `nD/(D+Δ) + Δ` holds.
- Lemma 6.5 names the wrong node.
- Theorem 6.8 is only a sketch that never specifies its graph `H`. We supply `H` and the walk,
  and the bound `Ω(nD/Δ)` then holds.

## Mistakes in the paper

* **Theorem 4.1 is false as stated.** It claims one bit `i` such that, in *every* execution with
  all inputs `i` and the upper bound `2n`, no node decides before hearing from everybody. But the
  bound `2n` reveals `n`, so the algorithm may favour `0` for some sizes and `1` for others.
  Counterexample: decide `b = [⌊N/2⌋ odd]` as soon as an input `b` is heard, else decide `¬b` at
  time `N − 1`. This is a correct comparison-based consensus algorithm for every valid bound
  `N ≥ n`. It decides at time 0 in the all-`0` execution with `n = 2` and in the all-`1` execution
  with `n = 3`. The stitching proof tacitly assumes that both bad executions have the same size.
  With "for every `n` there is an `i`" the theorem and its proof are correct. *False statement;
  the intended per-`n` statement holds.* (`theorem_4_1_literal_false`; repaired: `theorem_4_1`)
* **The running time of the dynamic-diameter protocol is overstated.** The paper says nodes can stop
  at `n − kmax·Δ − 1` once `kmax ≥ ⌊n/(D+Δ)⌋`, with the side condition `(k−1)D < n − kΔ − 1`. But
  to know that the diameter was `≤ D` up to time `(k−1)D`, a node must hear every node's state at
  that time, which takes until `kD`. So level `k` fires only when `k(D+Δ) ≤ n − 1`.
  The paper is inconsistent about the side condition: the rule says `(k−1)D ≤ n − kΔ − 1`, and the
  later remark says `<`. With `≤`, the 4-clique with `D = Δ = 1`, `kmax = 2` is a counterexample:
  nobody decides at time 1, because a node cannot exclude that round 1 was a star centred at
  itself. With the strict `<` and `D = 1`, the paper's condition coincides with the correct one, so
  a counterexample needs `D ≥ 2`. One exists: `n = 6`, `D = 2`, `Δ = 1`, `kmax = 2`, and the static
  graph with edges `01, 02, 03, 14, 24, 35, 45` (diameter 2). Node 3 cannot decide at time 3: it
  cannot exclude an execution in which node 2 has not heard from node 5 by time 3. The final bound
  `t < nD/(D+Δ) + Δ` is still true. The abstract's `min{O(nD/Δ), …}` drops this additive `Δ`, which
  matters when `Δ` is large. *False intermediate claim; final bound true.*
  (`diamProtocol_counterexample`, `diamProtocol_counterexample_strict`; proved: `diamProtocol_decides`,
  `diamProtocol_time`)
* **Definition 3 (dynamic diameter) is vacuous.** "`(u, max{0, t'−D}) ↝ (v, t')` for all `t' ≤ t`"
  fails at `t' = 0`, so no graph with two or more nodes has a dynamic diameter. Read literally, the
  dynamic-diameter protocol never decides early. Fix: quantify only over `t' ≥ D`. *Under-specified
  definition.* (`not_diamLit`, `DiamUpTo`)
* **Lemma 6.5 picks the wrong node.** The node that cannot distinguish the cycle-prefix from the
  path-prefix execution is `u_{k+s+1}` (the start of `P_{k+s}`), not `u_{k+s−1}`. In the instance
  `n = 6, k = 0, s = 2, a = 1, b = 2, t = 3`, `u_1` does distinguish. For `s < 0` the hypothesis
  must be `a + b < n − |s|`. Only `s ≥ 0` is used later. *Typo, plus a false unused case.*
  (`lemma_6_5_paper_node_false`, `lemma_6_5_neg_false`; repaired: `lemma_6_5`)
* Minor:
  - Lemma 6.6 omits its base case and needs `n ≥ 3`.
  - Theorem 6.7's proof writes `log₂ e` for `log₂ 3`.
  - Lemma 6.2's proof drops a factor `Δ`, and its two conditions on `Δ` differ.
  - Lemma 6.3 never states the level-0 rule.
  - Lemma 3.1 holds only for unknown `n` (implicit in the text).
  - Theorem 6.8 leaves `H` and the `O(t/D)`-step walk unspecified. We reconstructed them: the
    path `0 — ⋯ — (n−1)` plus a star at `a` covering everything left of `a`, and a star at
    `b = n/2 − 1` covering everything right of `b`, with `b − a = D − 2`. The walk deletes the left
    and right stars alternately in staggered blocks of `D − 1` rounds, observed by the far ends of
    the path. It needs `D ≥ 2`, and `D = O(Δ)` is unnecessary. (`Diameter68.theorem_6_8`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**

* **Rounds and adversary.** Synchronous rounds. In round `r ≥ 1` an adversary picks an arbitrary
  undirected, loopless, *connected* graph on the node set `V`, and nodes broadcast to their
  neighbours. There are no failures and the protocols are deterministic.
* **Nodes and a-priori knowledge.** Nodes are their UIDs (`V : Finset ℕ`, which may differ between
  executions). There are three systems:
  - `KnownN n`: every node is given `N = n`.
  - `UnknownN`: no information.
  - `BoundN`: a valid upper bound `N ≥ n`.
* **Views.** `Indist G H u t` is the full-information view relation, defined recursively.
  `Protocol.state_eq_of_indist` shows that every protocol's state is a function of it. Lower
  bounds therefore quantify over all *local decision rules*, which covers all protocols.
  Indistinguishability is always obtained from one locality lemma, `indist_of_agree`.
* **Knowledge.** Knowledge, the similarity graph and common knowledge are defined semantically,
  as in §2.1 (`Knows`, `Sim`, `CK`).
* **Problems.**
  - Consensus is binary, with irrevocable decisions.
  - `Δ`-coordination: every node has decided within `Δ` rounds of the first decision.
    Simultaneous consensus is the case `Δ = 0`.
  - "Comparison-based" means invariant under order-preserving renaming of UIDs.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Flooding (`n − s − 1` rounds ⇒ all but `s` heard) | `min_card_le_card_past`, `past_eq_V` | `Model.lean` |
| Lemma 3.1 | `lemma_3_1` | `Knowledge.lean` |
| Remark after Lemma 3.1 (no bound on `n`, `f` not known) | `not_knows_bound`, `not_knows_value` | `Knowledge.lean` |
| Theorem 4.1 as stated: **false** | `theorem_4_1_literal_false` | `CountBound.lean` |
| Theorem 4.1, per `n` | `theorem_4_1` | `CountBound.lean` |
| Remark after 4.1 (bound `N < 2(n−1)` allows early decisions) | `majority_remark` | `MajorityRemark.lean` |
| Theorem 5.1 (1), (2) | `theorem_5_1_known`, `theorem_5_1_unknown` | `Hiding.lean` |
| Simultaneous consensus: `≥ n−1` / `≥ n` rounds, tight | `simultaneous_lb_known`, `simKnown_spec`, `simultaneous_lb_unknown`, `simUnknown_spec` | `Simultaneous.lean` |
| Theorem 6.1 | `theorem_6_1` | `Simultaneous.lean` |
| Lemma 6.2 (clear majority) | `clearMajority_solves`, `clearMajority_decides`, `clearMajority_decides_eps` | `UpperBounds.lean` |
| Lemma 6.3 (approximate Δ-ladder) | `ladder_solves` | `UpperBounds.lean` |
| Dynamic-diameter protocol | `diamProtocol_solves`, `diamProtocol_decides`, `diamProtocol_time`, `diamProtocol_counterexample`, `diamProtocol_counterexample_strict`, `not_diamLit` | `UpperBoundsDiameter.lean` |
| Lemma 6.4 (as stated / simplified) | `lemma_6_4_general`, `lemma_6_4` | `Coordination.lean` |
| Lemma 6.5 (corrected) and counterexamples | `lemma_6_5`, `lemma_6_5_paper_node_false`, `lemma_6_5_neg_false` | `StaticPathLemma65.lean` |
| Lemma 6.6 | `lemma_6_6`, `lemma_6_6_clog` | `StaticPathLemma66.lean` |
| Theorem 6.7 (explicit / asymptotic) | `theorem_6_7`, `theorem_6_7_clog`, `theorem_6_7_asymptotic` | `StaticPathMain.lean`, `StaticPathAsymptotic.lean` |
| Theorem 6.8 (reconstructed `H`: path + two stars) | `Diameter68.theorem_6_8`, `Diameter68.theorem_6_8'` | `Diameter68.lean` |

The two forms of Theorem 6.7:
- Explicit: if `n ≤ 2^m β`, no node of the static line decides by any time `t` with
  `t + ⌈n/β⌉·3^{m+1}·Δ ≤ n − 1 − β`, for every input.
- Asymptotic: no node decides by `t` whenever `t + 57·Δ^{1/(2+log₂3)}·n^{1−1/(2+log₂3)} ≤ n`.

Theorem 5.1 is proved in a stronger form:
- Known `n`: all size-`n` executions are similar at every `t ≤ n−2`, even with different UID sets.
- Unknown `n`: all executions with at least `t+1` nodes are similar at time `t`.

Theorem 6.8 (`theorem_6_8'`): for `2 ≤ D ≤ n/2 + 1` there is a graph `H` on `{0, …, n−1}` of
diameter `≤ D` such that no `Δ`-coordinated consensus protocol decides by any time `t` with
`t(D−1+Δ) + 4Δ(D−1) ≤ (D−1)(n/2−1)`, in any execution that follows `H` up to time `t`. This is
`Ω(nD/Δ)` for `D ≤ Δ + 1`.

**Not formalized.** The extension of Section 5 to facts about arbitrary times and the
exact (non-approximate) `Δ`-ladder with nested `E^{@t}` operators are not formalized either.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity:
- The hypotheses of the lower bounds are satisfiable. The rules `simKnown`, `simUnknown`,
  `clearMajority`, `ladder`, `diamProtocol` and `majRule` are proved to solve the respective
  problems.
- The lower bounds are tight where the paper says so (`simKnown_spec`, `simUnknown_spec`).
- The model is paper-local (`Model.lean`) and imports only `Cslib.DynNet.exists_edge_cross` from
  CSLib. CSLib candidates: the model with views, the locality lemma and the hiding lemma
  (`Model.lean`, `Hiding.lean`), and the generic first-firing/ladder combinator (`UpperBounds.lean`).
