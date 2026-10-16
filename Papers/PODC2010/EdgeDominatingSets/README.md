# Edge Dominating Sets in Port-Numbered Networks — PODC 2010

Jukka Suomela. *Distributed Algorithms for Edge Dominating Sets.* PODC 2010. DOI
[10.1145/1835698.1835783](https://doi.org/10.1145/1835698.1835783). Formalized version: the author's version
(http://users.ics.aalto.fi/suomela/doc/eds.pdf, 10 pages, same numbering as the proceedings; there is no arXiv
version).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** All results are formalized and hold as stated: the lower bounds `4 - 2/d` (even `d`) and
`4 - 6/(d+1)` (odd `d`) for `d`-regular graphs (Theorems 1, 2), their bounded-degree consequence `4 - 1/k`
(Corollary 1), and the matching algorithms (Theorems 3, 4, 5). The lower bounds are proved in a slightly stronger
form than stated. The paper has only typos and trivially fillable gaps.

## Mistakes in the paper

No mistakes that affect a statement. Minor points:

* **§7.7, case `c(v) = 3/2`.** "`d_G(v) − 2` other nodes `x1, x2` in addition to `v`" should read "in addition to
  `s` and `t`". (Typo.)
* **§7.7, unstated facts.** In case `c(v) = 1`, the weight `2 − d(v) ≤ 0` needs `d(v) ≥ 2`. In case `c(v) = 2`,
  the `D*`-partner of `v` must differ from `s, t`. Both are immediate. (Trivial proof gap, true statement.)
* **§7.8 divides by `|D*|`.** This is `0` for an edgeless graph. We prove the integer form
  `2k·|D| ≤ (8k − 2)·|D*|` instead. (Degenerate case.)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Deterministic synchronous message passing in anonymous port-numbered networks
  (`Cslib/Computability/Distributed/PortNumbering/Basic.lean`). A `PNGraph` has degrees and an involution `p` on ports
  (`0 … deg v − 1`); loops and multi-edges are allowed, so the quotient graphs of the covering arguments are
  `PNGraph`s too.
* Initially a node knows only its degree. Each round it sends one message per port and receives one per port,
  indexed by its own port numbers. Messages and local computation are unbounded.
* An algorithm runs for `T` rounds, and then every node outputs a set of its ports. The selected edge set is
  `outEdges`; `Consistent` is the paper's requirement that both endpoints select the edge.
* The problem is posed on simple graphs (`IsSimple`, underlying `SimpleGraph` `toSimpleGraph`). `IsEDS` is an
  edge dominating set, `edgeDomNum` the minimum size. `Approximates A T G α` means: consistent, an EDS, and
  `|D| ≤ α·γ'(G)`.
* **Lower bounds are stronger than in the paper.** They hold for every algorithm and every running time `T`
  that outputs an EDS on the one graph `G`. Consistency is not assumed.
* Upper-bound algorithms are written as local processes. Each round, a node updates its data from its
  neighbours' data and the remote port numbers. `Algorithm.ofLocal` turns such a process into a genuine
  message-passing algorithm, and `eval_ofLocal` is the bridge.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (even `d`: ratio `≥ 4 − 2/d`, here `d = 2k`; also `γ'(G) = k`) | `theorem_1` | `LowerBound.lean` |
| Theorem 2 (odd `d`: ratio `≥ 4 − 6/(d+1)`, here `d = 2k+1`; also `γ'(G) = (k+1)d`) | `theorem_2` | `LowerBound.lean` |
| Corollary 1 (`α ≥ 4 − 1/k` whenever `Δ ≥ 2k`) | `corollary_1` | `LowerBound.lean` |
| Theorem 3 (`d`-regular, `4 − 2/d`, 1 round) | `theorem_3` (algorithm `alg3`) | `Theorem3.lean` |
| Theorem 4 (odd `d`-regular, `4 − 6/(d+1)`, `2 + 2d²` rounds) | `theorem_4` (algorithm `alg4`) | `Theorem4.lean` |
| Theorem 5 (`Δ = 2k+1`, `4 − 1/k`, `3Δ² + 4Δ + 2` rounds) | `theorem_5_odd` (algorithm `alg5`) | `Theorem5.lean` |
| Theorem 5 (`Δ = 2k`, `A(2k) = A(2k+1)`) | `theorem_5_even` | `Theorem5.lean` |
| Theorem 5 (`Δ = 1`, ratio `1`) | `theorem_5_one` | `Theorem5.lean` |
| §7.3–7.8 analysis (properties (a)(b)(c) ⇒ ratio) | `card_le_of_props`, `card_le_edgeDomNum_of_props` | `Analysis5.lean` |
| Lemma 1 (odd degree ⇒ distinguishable neighbour) | `PNGraph.dn_isSome_of_odd` | `Distinguishable.lean` |
| Lemma 2 (`M_G(i, j)` is a matching) | `M_matching` | `Distinguishable.lean` |
| covering maps preserve outputs (§2.3) | `Algorithm.eval_covering` | `Cslib/Computability/Distributed/PortNumbering/Basic.lean` |
| each edge dominates `≤ 2Δ − 1` edges | `card_edgeFinset_add_le` | `Basic.lean` |

Supporting files:
* `Gadget.lean`: an explicit closed-form 2-factorisation of the lower-bound graphs, which replaces Petersen's
  theorem.
* `Phases.lean`, `Phase5.lean`: the phases as global processes on edge sets.
* `Theorem5Alg.lean`: the round-by-round simulation of `alg5`.

**Not formalized.**
* The equivalence "minimum maximal matching = minimum EDS" (§1.1). It is not needed: the §7 analysis works for
  any EDS `D*`.
* The NP-hardness and related-work claims of §1.

**Trust.** No `sorry`. The theorems in the table use only `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity (`NonVacuity.lean`): on the lower-bound graphs of Theorems 1 and 2, the algorithms of Theorems 3 and 4
output edge dominating sets (`nonvacuous_theorem_1/2`), so the lower-bound hypothesis is satisfiable; combining
both bounds, their outputs there have size exactly `(4 − 2/d)γ'` resp. `(4 − 6/(d+1))γ'` (`tight_theorem_1/2`).
`d`-regular simple inputs exist for every `d ≥ 1` (`graph1`, `graph2`). The port-numbering model (the model, covering maps,
sequential composition, local processes) is in CSLib, `Cslib/Computability/Distributed/PortNumbering/Basic.lean`.

**CSLib candidates.**
* `IsEDS`, `edgeDomNum`, `card_edgeFinset_add_le` (`Basic.lean`).
* `card_fibre_le` / `card_le_of_fibre`: covering-map counting.
* `card_mul_le`: the star-forest count `(d+1)|D| ≤ d|V|`.
* `firstPort`, `IsMatching`.
