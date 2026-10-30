# Space-Time Tradeoffs for Distributed Verification — PODC 2016

Rafail Ostrovsky, Mor Perry, Will Rosenbaum. *Space-Time Tradeoffs for Distributed Verification.*
PODC 2016 brief announcement by Mor Baruch, Rafail Ostrovsky, Will Rosenbaum. Formalized version: arXiv
[1605.06814](https://arxiv.org/abs/1605.06814) v2 (full version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The acyclicity results hold: every `t`-round scheme needs labels of
`Ω(log n / t)` bits (Theorem 7), and `O(log n / t)` bits suffice for every `t ≥ 2` (Theorem 8). The
universal `t`-PLS (Theorem 1) holds; the paper's scheme covers `t ∈ O(D)` (printed: `t ∈ Ω(D)`). The general crossing
tool, Proposition 4 and Theorem 5, is false in the model with identifiers, where the paper says it holds:
two-round verifiers can detect short cycles. It is true without identifiers.

## Mistakes in the paper

* **Proposition 4 and Theorem 5 fail for `t ≥ 2` in the identifier model.** The paper claims (Sections 1.1
  and 4) that its lower-bound tool holds when nodes have unique identifiers, with outputs independent of
  them. Take `r` disjoint triangles, `e_i` an edge of triangle `i`, `t = 2`, `q = 3`, and the predicate
  "every node lies on a triangle". All hypotheses hold, and the crossing of two triangles is a 6-cycle
  violating the predicate. But a 2-round verifier with *empty* labels decides the predicate: a node checks
  whether two of its neighbours are adjacent. So the label size is 0, not `Ω(log r)`, and Proposition 4's
  conclusion fails for every pair. The broken step is "every node of `N_t(e_i) ∪ N_t(e_j)` has the same
  `t`-neighbourhood in `G` and in `C(e_i, e_j, G)`", which fails when `e_i` lies on a cycle of length
  `≤ 2t+1`. In anonymous networks, where a node only learns its view tree, a triangle and a 6-cycle look
  alike and Proposition 4 is true; we prove it there. The paper's application, Theorem 7, uses a path and
  is unaffected; we prove it directly in the identifier model. Counterexamples: (`theorem_5_false`,
  `proposition_4_false`); anonymous-model version: (`proposition_4_view`, `theorem_5_anon`).
* **Proposition 16 is false as printed: off-by-one in condition 4 of correct block labels.** Condition 4
  asks for a head at the start of an oriented path `w_0, …, w_{k-1} = v` with `k < t` vertices. A tail is
  `t` vertices below its head, so it can never satisfy this. For `t = 2` no graph with an edge has a
  correct labelling, e.g. the acyclic path on two nodes. With `k ≤ t`, as the proof of Lemma 17 and Fig. 1
  intend, Proposition 16 holds for all `t ≥ 2`. Typo with evident intent. (`not_correctLiteral_path`,
  `prop16`)
* **Proposition 16 fails for `t = 1`.** Every node would have to be both head and tail, so no nonempty
  graph has a correct labelling. This is a degenerate case; Theorem 8 is then the classical 1-round scheme.
  (`correct_one_isEmpty`)
* **Theorem 1 says "`t ∈ Ω(D)`", but its scheme needs `t ∈ O(D)`.** The shares are spread over BFS
  distances `0, …, t/4` from one node, so that node needs eccentricity about `t/4`. The introduction
  indeed says `t ∈ O(diam)`, so `Ω` is most likely a typo. The statement itself survives for large `t`:
  when the diameter is below `t`, every node sees the whole configuration in `t` rounds and empty labels
  suffice (not formalized; we formalize the paper's scheme for `t ≤ 2·diam + 2`). The scheme also tacitly needs `P` to be invariant under isomorphism and connected
  configurations. Its soundness proof skips why a representation consistent with all local views is the
  actual configuration; we fill this gap. (`theorem1`)
* **Smaller slips.**
  * Proposition 4's counting "`|ℓ| < log r / q` ⇒ fewer than `r` concatenations" is wrong for
    variable-length labels. Counting label tuples gives `log₂ r < q(|ℓ|+1)`. Same asymptotics.
  * Algorithm 1 (not formalized): `HEAD_CHECK` starts `false` and only ancestors can set it, so a root
    always rejects at line 35. The relay loop runs `t-1` times while the text uses the message of the
    `t`-th round.
  * Typos: "`d(v) = mid` otherwise" should be `b(v) = mid` (proof of Proposition 16), and
    "`d(w) = b(v) + 1`" should be `d(w) = d(v) + 1` (before Definition 10).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Configurations.** A configuration is a graph on any vertex type `V : Type`, with states `I : V → ι`.
  A `t`-PLS (`TPLS`) has a prover and a verifier, and must be complete and sound on all finite
  configurations of the family. Deterministic, synchronous, no failures. The verifier does not know `n`.
- **Locality.** The output of a node is a function of its labelled radius-`t` ball up to isomorphism
  (`BallIso`): the nodes at distance `≤ t` with states and labels, and the edges at nodes at distance `< t`.
  This is what `t` rounds reveal when identifiers may be used but the output must not depend on them. This
  is the paper's rule in Section 2.1 and its model for the lower bounds.
- **Identifiers.** For Theorem 1, identifiers are part of the states, so the verifier may use them.
- **Anonymous model.** For the positive version of Proposition 4, views are anonymous broadcast view trees
  (`Anonymous.lean`).
- **Not modelled.** Labels are bit strings (or finite data with an explicit bit size). Message size, memory
  and run time are not modelled.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Model (Section 2), `t`-PLS | `TPLS`, `BallIso`, `TPLS.CostLE` | `Basic.lean` |
| Theorem 1 (universal `t`-PLS) | `theorem1`, `theorem1_ids`, `universal` | `UniversalCodes.lean`, `Universal.lean` |
| Definitions 2–3; Proposition 4, Theorem 5 refuted (`t = 2`) | `crossing`, `edgeNbhd`, `theorem_5_false`, `proposition_4_false` | `Crossing.lean` |
| Proposition 4, Theorem 5 in the anonymous model | `proposition_4_view`, `proposition_4_anon`, `theorem_5_anon_length` | `Anonymous.lean` |
| Theorem 7 | `theorem_7`, `lowerBound_card` | `LowerBound.lean` |
| Definitions 13–14, Proposition 16 (corrected; as printed refuted) | `Correct`, `prop16`, `not_correctLiteral_path` | `AcyclicLabels.lean` |
| Lemma 17 (for a radius-`t` check), Theorem 8 | `lemma17`, `check_isLocal`, `theorem8`, `theorem8_bits` | `AcyclicUpper.lean` |
| Theorems 7 + 8: tight tradeoff | `acyclic_tradeoff` | `Tightness.lean` |

Explicit bounds:
- **Theorem 7.** `⌊n/(2t+2)⌋ - 1 ≤ (2^{L+1} - 1)^{2t+2}` for labels of length `≤ L`.
- **Theorem 8.** Labels of `5 + ⌈⌈log₂ n⌉/t⌉` bits, radius `t`.
- **Theorem 1.** Labels of `2R/t + ⌊log₂ t⌋ + 2` bits with
  `R = n(2s+3) + 2 + min{n(2n+1), m(4⌈log₂(n+1)⌉+1)}`, radius `t`, for `t ≤ 2·diam + 2`.

**Not formalized.**
- Algorithm 1 itself: Lemma 17 is proved for the radius-`t` predicate it is meant to compute.
- Lemma 12.
- Section 4.3: the recursive `O(log* n)` scheme, Theorem 18.
- Appendix A.
- Space and message-size claims.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
- *Theorem 7 is not vacuous.* `acyclic_tradeoff` applies it to the scheme of Theorem 8.
- *Theorem 1's hypotheses can be met.* An `example` and `pathGraph_le_diam` exhibit families satisfying
  them.
- *The counterexample meets the paper's hypotheses.* It satisfies every hypothesis of Theorem 5
  (`triangles_hyp`).
- *Sources.* Locality uses CSLib's `Cslib.Local.GAgree`. Graph facts come from CSLib (`isAcyclic_of_rank`,
  BFS trees, `le_add_edist_of_lipschitz`).

**CSLib candidates.**
- The `t`-PLS model over all vertex types with ball-isomorphism locality (`Basic.lean`).
- `TPLS.recode`.
- `bitsW`, `exists_dist_between`, `eq_of_adj_eq` (`Universal.lean`).
