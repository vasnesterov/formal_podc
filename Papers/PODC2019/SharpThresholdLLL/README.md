# Sharp threshold for the distributed Lovász Local Lemma — PODC 2019

Sebastian Brandt, Yannic Maus, Jara Uitto. *A Sharp Threshold Phenomenon for the Distributed Complexity of the
Lovász Local Lemma.* PODC 2019. DOI [10.1145/3293611.3331636](https://doi.org/10.1145/3293611.3331636).
Formalized version: arXiv [1908.06270](https://arxiv.org/abs/1908.06270) v2; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Both main theorems hold. Theorem 1.1 covers variables affecting `≤ 2` events
and Theorem 1.3 variables affecting `≤ 3` events. In both, `p · 2^d < 1` and the deterministic variable-fixing
process works for any adaptive order of the variables. Lemmas 3.2, 3.6, 3.7 and 3.9 hold, and so does Lemma 3.5
once a parenthesis typo is fixed. Two things needed repair: the proof of Theorem 1.3 reduces "w.l.o.g." to variables
of rank exactly 3 by a step that does not work as written, and Lemma 3.5 is false as printed. We also give a shorter
proof of the key geometric fact (Lemma 3.7): no Hessians, two weighted AM–GM inequalities.

## Mistakes in the paper

* **The reduction to rank exactly 3 (Section 3) does not work as written (proof gap; the statement is true).**
  A rank-2 variable on `{u, v}` is made rank 3 by adding a "virtual third bad event" `w`. The bookkeeping of
  Lemma 3.2 needs the dependency-graph edges `{u,w}` and `{v,w}`.
  * A new node `w` gives `u` and `v` an extra incident edge, whose value (up to 2) enters the final bound
    `p · ∏ φ ≤ p · 2^{deg}`, which then exceeds `p · 2^d`.
  * An existing `w` need not be adjacent to `u` and `v`.
  * Rank-1 variables are not addressed.

  The repair is easy. For hyperedges of size 1 or 2, the set of representable values is a half-space, and the
  linearity argument of Section 2 (in the weighted form sketched in §3.1) gives the fixing step directly. We prove
  one fixing property for every hyperedge of size `≤ 3` and Lemma 3.2 for every variable of rank `≤ 3`, with no
  virtual events (`fixingProperty_of_card_le_three`, `variable_fixing_lemma`).
* **Lemma 3.5 is false as printed (typo).** The statement writes `f(a,b) = 4 + ½·ab − 2a − 2b − √(ab(4−a)(4−b))`,
  without the parentheses of Lemma 3.6. With this reading `(0, 1, 3)` is representable but `3 > f(0,1) = 2`. With
  the parentheses the lemma holds. Equivalently, and more simply,
  `S_rep = {(a,b,c) ≥ 0 | a + b + c + √(abc) ≤ 4}`. (`lemma_3_5_as_printed_false`; repaired: `srep_eq_f`,
  `representable_iff`)
* **Degenerate cases glossed over (proof gaps; statements true).**
  * Theorem 1.1's proof claims that variables other than those on edges at `v` do not change `Pr[E_v]`. This
    overlooks variables that affect only `E_v`.
  * The same proof divides by `Pr[E_u | θ]`, which may be 0.
  * In Lemma 3.9, the identity `Σ pᵢ sᵢ = (a,b,c)` fails when some conditional probability is 0. Only `≤` holds,
    so downward-closedness of `S_rep` is needed. It is true but not stated.

  All are handled in the formalization (`exists_inc_add_inc_le_two`, `exists_hval_le_four`,
  `Representable.mono`).
* **Typos and remarks.**
  * In the proof of Lemma 3.5, case `a = b = 0`, `b₂` should be `b₁`.
  * The Applications remark "the degree of the dependency graph must be at least 7" (three orientations of a rank-3
    hypergraph, no node a sink in two of them) could not be reproduced. On `k`-regular linear hypergraphs (`d = 2k`)
    the criterion already holds for `k = 2` (`p·2^d = 400/729`) and fails only for `k = 1`. This was checked by
    exact arithmetic, not in Lean.
  * We checked the appendix's Hessian formulas numerically; they are right.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **LLL instances in the variable setting** (`Basic.lean`). There are finitely many independent variables, each
  with a finite range and an arbitrary distribution, and finitely many bad events, each a predicate determined by
  its variable set `vbl v`. The dependency graph joins events that share a variable. Hypotheses:
  `Pr[E_v] ≤ p`, `#N(v) ≤ d`, `p · 2^d < 1`, and the rank (`#` events per variable) `≤ 2` or `≤ 3`.
* **Conditional probabilities** are exact finite sums. `condProb σ v` is the probability of `E_v` under the product
  distribution in which the fixed variables (partial assignment `σ`) are point masses (`Cslib.Probability.piExpect`
  of the shared library `Cslib/Probability/Finite/Product.lean`). There is no measure theory. The four facts used
  (total probability, independence, locality, value at full assignments) are proved; the first, second and fourth
  are instances of the library's `sum_mul_piExpect_update_single`, `piExpect_update_single_of_forall_update` and
  `piExpect_single`.
* **The process** is a transition relation `Step p j s s'` on states `(σ, φ)`, where `φ t u` is the bookkeeping
  value of edge `{t,u}` at `t` (Definition 3.1). A step fixes an unfixed variable `X_j` to a value of positive
  probability. It changes `φ` only on edges inside the hyperedge of `X_j`, and must restore `P*` at the events of
  `X_j`, a condition that only involves `X_j`'s events and their incident edges.
  * Adversarial or adaptive order: every unfixed variable can be stepped in every reachable state.
  * Determinism: fix one step by a choice function.
  * Locality: a step remains valid from any state that agrees on the variables of its events and on their
    bookkeeping rows (`Step.transport`).
* **Distributed corollaries**: only the parallel semantics. A phase is a set of groups with pairwise disjoint
  regions, each running a sequential run from the phase's start state. The colourings are hypotheses, and LOCAL
  rounds are not modelled.

**Main results in Lean** (namespace `SharpThresholdLLL`).

| Paper | Lean | File |
|---|---|---|
| Theorem 1.1 (rank ≤ 2) | `Instance.theorem_1_1` | `Process.lean` |
| Theorem 1.1, key claim `Inc(u,y) + Inc(v,y) ≤ 2` | `Instance.exists_inc_add_inc_le_two` | `Process.lean` |
| Theorem 1.3 (rank ≤ 3) | `Instance.theorem_1_3` | `Process.lean` |
| Definition 3.1 (`P*`), Lemma 3.2 | `Instance.PStar`, `Instance.variable_fixing_lemma` (general: `exists_step`, `step_pstar`) | `Process.lean` |
| Any rank, given the fixing property (Conjecture 1.5 reduced to it) | `Instance.process_correct`, `FixingProperty` | `Process.lean` |
| Definitions 3.3, 3.4 | `Representable`, `Srep`, `Incurved` | `Representable.lean` |
| Lemma 3.5 (corrected; symmetric form) | `srep_eq_f`, `representable_iff` | `Representable.lean` |
| Lemma 3.5 as printed is false | `lemma_3_5_as_printed_false` | `Representable.lean` |
| Lemma 3.6 | `f_convexOn` | `Representable.lean` |
| Lemma 3.7 | `srep_incurved` | `Representable.lean` |
| Lemma 3.9 (any incurved set) | `lemma_3_9` | `Representable.lean` |
| New: tangent-plane inequality / averaging step | `hval_le_of_tangent`, `exists_hval_le_four` | `Representable.lean` |
| Corollaries 1.2, 1.4: correctness of the colour-class schedules (K phases) | `Instance.corollary_1_2_core`, `Instance.corollary_1_4_core` | `Corollaries.lean` |
| Parallel phases are sequential runs | `Instance.phase_run`, `Instance.valid_schedule_correct` | `Parallel.lean` |
| Sinkless orientation sits exactly at `p = 2^{-d}` | `sinkless_at_threshold`, `sinklessInstance_good_iff` | `Sinkless.lean` |
| `p · 2^d = 1` is not enough | `sharp_no_good_assignment` | `Examples.lean` |

The proof of Lemma 3.7 is new. Write `h(a,b,c) = a + b + c + √(abc)`, so `S_rep = {h ≤ 4}`. For `m > 0`, every
`s ≥ 0` below the tangent plane of `h` at `m` satisfies `h(s) ≤ h(m)`. In the coordinates `uᵢ = sᵢ/mᵢ` this is
`2√(u₁u₂u₃) ≤ (Σ(1−βᵢ)uᵢ)·√(Σβᵢuᵢ)` for weights `β` in the simplex: one weighted AM–GM with weights `(1−βᵢ)/2`
and one with weights `βᵢ`. The averaging step of Lemma 3.2 then follows directly, Lemma 3.7 is the two-point
case, and Lemma 3.6 follows from Lemma 3.7.

**Not formalized.**
* The round bounds `O(d + log* n)` and `O(d² + log* n)`. They need the cited colouring algorithms ([PR01],
  [FHK16]) and a LOCAL implementation of a phase.
* The cited `Ω(log n)` / `Ω(log log n)` lower bounds above the threshold. Only the instance-level reduction from
  sinkless orientation is formalized.
* The fixing property for hyperedges of size `≥ 4` (Conjecture 1.5) and the Applications section.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity:
* `ex3_theorem_1_3` applies Theorem 1.3 to a concrete rank-3 instance (one variable uniform on 8 values, three
  events, `d = 2`, `p = 1/8`).
* `sharp_no_good_assignment` shows that the strict inequality is necessary.

The development builds on Mathlib and the shared finite probability library `Cslib/Probability/Finite/` (product
distributions, averaging `exists_le_of_sum_mul_le`). CSLib candidates (`-- CSLib candidate`): the LLL instance in
`Basic.lean`, and the tangent-plane / AM–GM lemmas in `Representable.lean`.
