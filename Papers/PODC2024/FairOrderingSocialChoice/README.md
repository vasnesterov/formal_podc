# Fair Ordering via Streaming Social Choice — PODC 2024

Geoffrey Ramseyer, Ashish Goel. *Brief Announcement: Fair Ordering via Streaming Social Choice Theory.* PODC 2024.
DOI [10.1145/3662158.3662772](https://doi.org/10.1145/3662158.3662772). Formalized version: the full version, arXiv
[2304.02730](https://arxiv.org/abs/2304.02730) v4 ("Fair Ordering in Replicated Systems via Streaming Social
Choice"), which has the proofs (Appendices A–E, K); numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** The headline results hold: Ranked Pairs is `(γ, f/n)`-minimally-batch-order-fair for
every `γ` at once (Theorem 4.1), and the streaming Algorithm 3 is consistent with Ranked Pairs and monotonic
(Lemma 5.8, Theorem 5.10, Corollary 5.9), once its output rule is repaired: as printed, it always outputs nothing.
Two supporting results of Section 3 have problems. Lemma 3.6 is false: the strongly connected components it builds
are not output one after another, so its "recovered batches" claim fails. The impossibility Lemma 3.4 is true, but
its proof is wrong; we prove it with a new argument. The liveness part (Section 6, Algorithm 1) was not checked.

## Mistakes in the paper

### ❌ Lemma 3.6 (recovering minimal batches)
Both bullets are false, even with `δ = 0` and no faulty replicas. Take 6 replicas, 4 transactions, `γ = 2/3`.
The pairs with at least 4 votes are `a→b`, `b→c`, `c→a`, `a→d`, so the components are `{a,b,c}` and `{d}`.
The output `a, d, b, c` is exactly `2/3`-minimal, yet `d` comes before `b` (`lemma_3_6_false`).

**Impact.** Definition 3.5 does not yield "approximately minimal batches" output in order: an output can
interleave a component with one it must precede. The claim after Theorem 4.1 that Ranked Pairs' output can be cut
into such batches rests on this lemma. Theorem 4.1 itself is unaffected.

**Details.** The six votes are `abcd`, `adbc`, `bcad`, `dbca`, `cabd`, `dcab`. They give `a≺b`, `b≺c`, `c≺a`,
`a≺d` 4 votes each, `b≺d` and `c≺d` 3 votes each, and `d≺a` 2 votes. The output `a, d, b, c` reverses only `c→a`,
and `a→b→c` is output in order, so Definition 3.5 holds with `(2/3, 0)` (`Lemma36.minimalBatchFair`). Bullet 1
fails because `a→d` crosses components while `b` (in `a`'s component) comes after `d`. Bullet 2 fails because `d`
has no out-edge of weight `2/3` at all. Bullet 1 also fails for every `0 ≤ δ < 1/6`
(`lemma_3_6_part1_false`).

The proof's last step ("if there is an edge from one component to another, all transactions in the first must be
output before any in the second, or else a violation of Definition 3.5") is wrong. Definition 3.5 constrains only
the pairs with `γn` votes, not every pair across the two components. By hand (not in Lean), Ranked Pairs itself
produces `a, d, b, c` when the weight-`4/6` ties are processed as `a→b, b→c, a→d, c→a` and the weight-`3/6` ties
as `d→b, b→d, d→c, c→d`. So the remark after Theorem 4.1
fails for Ranked Pairs too.

**Repair.** Only the pairwise statement survives. If `γn` replicas received `a ≺ b` and `a, b` lie in different
components of the `(γ − 2δ)`-graph, then `a` is output before `b` (`lemma_3_6_pairwise`). This drops the batch
structure that the lemma was meant to provide.

### 🔧 Algorithms 3 and 1 (output rule)
Read literally, the output is always empty. The output stops at "the first transaction bordering an indeterminate
edge", and initialization marks the edge `(τ, v̂)` indeterminate for *every* transaction `τ`.

**Impact.** Theorem 5.10 and Corollary 5.9 hold trivially for the printed rule, and the liveness claims of Section 6
(Theorems 6.5, 6.9) fail for it. With the evident fix, Theorem 5.10 and Corollary 5.9 hold and the output is not
trivial: once all votes cover the same set, everything is output (`output_complete`).

**Repair.** Ignore the edges `(τ, v̂)`: a transaction is *clean* if it is not the target of `(v̂, τ)` and all its edges
to other transactions are determinate. Output the clean transactions that precede every non-clean one in the
determinate order (`Streaming.output`).

### ✏️ Slips
- After Definition 3.3 the text says the condition of Lemma 3.4 "admits `f = 1`" for `n = 7`, `γ = 2/3`. But
  `7 mod (7 − 5 + 1) = 1`, so the stated condition `f > 1` excludes `f = 1` (`lemma_3_4_n7_f1_not_covered`). The
  impossibility does hold for `f = 1` there, by a different construction (`lemma_3_4_n7_f1`).

### Typos
- Definition 3.1 (§3.1) has `τ` and `τ'` swapped ("never outputs `τ'` in a later batch than `τ`"). The abstract and
  §1.1 state it correctly.

## Proof gaps (statements true)

### 🛠️ Lemma 3.4 (impossibility of exact `γ`-minimality with faulty replicas)
The proof's construction forces nothing. With groups of size `n − m + 1` (`m = ⌈γn⌉`) receiving the `k` rotations,
*no* pair gets `m` votes (`lemma_3_4_paper_construction_vacuous`). The claim "pairs `τᵢ, τⱼ` with `i < j` receive at
least `m` votes" is false; for `n = 7`, `γ = 2/3` it gives `τ₁ ≺ τ₂` 4 votes and `τ₂ ≺ τ₁` 3
(`lemma_3_4_paper_construction_n7`).

**Impact.** Statement true; proved with a new argument (`lemma_3_4`). It holds even in the weak form where the true
`γ`-graph is acyclic.

**Repair.** Keep the paper's reported profile, with the remainder put into one group, and use `k` scenarios instead
of two. In scenario `i`, enough members of group `i` (one, or `r + 1` for the enlarged group, `r = n mod (n−m+1)`)
are faulty and truly received the order of group `i+1`. Then the single `γ`-edge is `τᵢ → τᵢ₊₁`. Since the reported
profile is the same in all scenarios, the protocol would have to output the cycle `τ₁ → … → τₖ → τ₁`. The case
`k = ⌊n/(n−m+1)⌋ = 1`, which the paper does not cover (e.g. `n = 3`, `γ = 2/3`), uses two transactions and `m`
faulty replicas. The core is `Impossibility.cyclic_fails`.

### 🔧 Corollary 5.9 (monotonicity of Algorithm 3)
The proof only argues consistency: determinate decisions agree with Ranked Pairs on every completion. It does not
show that a transaction once output stays output when the votes are extended, which is what "extends" requires.

**Impact.** Statement true (for the repaired output rule); proved (`corollary_5_9`).

**Repair.** Determinate decisions are stable under extension (`dec_mono`, the Lemma 5.8 argument run against a
streaming extension instead of a completion), and clean transactions stay clean (`clean_mono`).

### 🔧 Lemma 3.8 (Themis example)
The bound `(1 − γ) + (f+1)/n ≤ (1 − γ) + 2f/n` used in the proof fails for `f = 0`, the case of the lemma
(`paper_step_false`). With `f = 0` the tied cycle is a valid set of Themis dependencies only when
`γ ≥ 1/2 + 1/n` (`Themis.cycleDeps_iff`; it fails for `n = 4`, `γ = 3/5`: `cycleDeps_fails_small_n`).

**Impact.** Statement true: `n` is ours to choose, and for every `γ > 1/2` a large enough even `n` works
(`lemma_3_8_exists`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- `n` replicas (`Fintype ι`), deterministic aggregation, no communication layer: the input is one ordering vote
  per replica, as in the paper. Faulty replicas (any number `f = |F|`, unknown) report arbitrary orders; honest ones
  report their true order (`Agree T P F`).
- Static setting (Sections 3–4): votes are strict total orders `Cslib.SocialChoice.Pref X`, and a protocol is a
  `Cslib.SocialChoice.Aggregation`. Definitions 3.3 and 3.5 are stated with the *true* profile `T` ("at least `γn`
  replicas received"), the output being the protocol's result on the reported profile.
- Ranked Pairs (`RP.accepted`, by well-founded recursion on the processing order): edges in decreasing weight, ties
  broken by any fixed injective rule `tb`, which covers "ties broken arbitrarily". Output = transitive closure of
  the accepted edges, a strict total order (`rpPref`).
- Streaming (Section 5): votes are finite lists, an extension appends to each list, and transactions form a
  countable type (`tb : α × α → ℕ` injective, one global tie-breaking rule for all invocations and completions).
  Algorithm 3 iterates over the edges between transactions voted on by all replicas. `v̂` is `none : Option α`.
  Decisions are `acc/rej/ind` (`Streaming.dec`). The counterfactual of Lemma 5.8 is any completion `σc` in which
  every replica's vote extends its current vote and all votes cover the same finite set (`Complete`). The output is
  a set ordered by the determinate edges (`output`, `detLt`). "`A(σ')` extends `A(σ)`" is stated as containment,
  down-closure and agreement of orders.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 3.2, 3.3, 3.5 | `count`, `ExactlyMinimal`, `MinimalBatchFair` | `Defs.lean` |
| Lemma 3.4 | `lemma_3_4` (+ `lemma_3_4_n7_f1`, `lemma_3_4_paper_construction_vacuous`) | `Impossibility.lean` |
| Lemma 3.6 (false) | `lemma_3_6_false`, `lemma_3_6_part1_false`; repair `lemma_3_6_pairwise` | `Batches.lean` |
| Lemma 3.8 | `lemma_3_8`, `lemma_3_8_exists` | `Themis.lean` |
| Algorithm 2, Lemma 5.3 | `RP.accepted`, `RP.rejected_path`, `RP.rpLt_irrefl`, `RP.rpLt_total` | `RankedPairs.lean` |
| Theorem 4.1 | `theorem_4_1` (from `minimalBatchFair_of_approx`) | `Theorem41.lean` |
| Lemma 6.11 (fairness, non-streaming) | `lemma_6_11` | `Theorem41.lean` |
| Observation 5.4, Lemma 5.6 | `Streaming.observation_5_4`, `Streaming.lemma_5_6` | `Streaming.lean` |
| Algorithm 3 | `Streaming.dec`, `Streaming.output` | `Streaming.lean` |
| Lemma 5.8 | `Streaming.lemma_5_8` (core: `dec_mono`, `dec_complete`) | `Streaming.lean` |
| Theorem 5.10 | `Streaming.theorem_5_10` | `Streaming.lean` |
| Corollary 5.9 | `Streaming.corollary_5_9` | `Streaming.lean` |

All names are in the namespace `Podc.FairOrderingSocialChoice`.

**Remarks.** Theorem 4.1 holds for every real `γ`, not only `γ > 1/2`. It follows from a general fact: if the
weights used to order the edges are within `ε` of the true weights, Ranked Pairs is `(γ, ε)`-fair. Faulty replicas
give `ε = f/n`, and rounding to `1/k` adds `1/(2k)` (Lemma 6.11). Algorithm 3 accepts every weight-1 edge and
rejects every weight-0 edge determinately (`dec_of_cnt_full`, `dec_of_cnt_zero`).

**Not formalized.** Lemma 3.7 (Aequitas), Section 6 except the fairness part of Lemma 6.11 (Algorithm 1, its
deferral tie-breaking and oracle, Lemmas 6.1–6.10, Theorems 6.5 and 6.9: liveness is unchecked), Lemma E.1, the
examples of Appendices F–I, and the protocol instantiation of §L.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `output_complete` (the streaming output is everything once votes are complete), an explicit
tie-breaking rule for `α = ℕ`, and concrete profiles in `Impossibility.lean`, `Batches.lean`, `Themis.lean`.
Votes and aggregation maps come from CSLib's `Cslib.Foundations.SocialChoice.Aggregation`.

CSLib candidates: the generic Ranked Pairs / greedy acyclic edge selection in `RankedPairs.lean` (marked
`-- CSLib candidate`).
