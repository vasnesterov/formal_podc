# Wake Up and Join Me! (energy-efficient maximal matching in radio networks) — PODC 2021

Varsha Dani, Aayush Gupta, Thomas P. Hayes, Seth Pettie. *Brief Announcement: Wake Up and Join Me!
An Energy-Efficient Algorithm for Maximal Matching in Radio Networks.* PODC 2021. DOI
[10.1145/3465084.3467950](https://doi.org/10.1145/3465084.3467950). Formalized version: arXiv
[2104.09096](https://arxiv.org/abs/2104.09096) v2 (full version); numbering follows it.

**Verdict: ❌ False claim.** Theorem 6.5 (the neighbour-assignment application, a secondary result)
claims that Algorithm 4 with parameter `k` outputs a
neighbor assignment of maximum load at most `k`. This is false: the true bound is `k + 1`, and it is
attained on disjoint copies of `P₃` whenever the matching subroutine succeeds. The other checked
results are true. These are Theorem 6.3 (minimum NAF load = matching cover number unless it is 1),
the coverage bounds of Theorem 6.5, Lemmas 5.1, 5.2, 5.6 and Lemma 5.4 (Algorithm 1 outputs a
maximal matching w.h.p.). The proofs of Theorems 6.3 and 6.5 needed repairs. The headline energy
bound of Theorem 1.1 fails literally for `Δ = 1`, a degenerate corner. Its energy part is not
formalized otherwise.

## Mistakes in the paper

* **Theorem 6.5: "maximum load at most `k`" is false; it should be `k + 1`.** Algorithm 4 calls
  the maximal matching subroutine `k + 1` times: once in line 1 and once in each of the `k` loop
  iterations. Each call gives a vertex at most one new partner, so it adds at most one vertex
  pointing to it. Hence the load is at most `k + 1`, and this is attained. Take a path
  `ℓ — c — ℓ'` and `k = 1`. The first call matches `c` with one leaf `ℓ`. In the iteration, `ℓ'`
  is the only unassigned vertex and `c` its only neighbour, so every maximal matching of the cross
  graph matches them. Then `c` is re-assigned to `ℓ'`, while `ℓ` still points to `c`, so `c` has
  load `2`. With `c` disjoint copies (`n = 3c`) this happens in every execution where both calls
  succeed. By the paper's own Theorem 1.1 that has probability `1 − O(1/n²)`, so the claimed
  property fails with high probability. This is not a typo with evident intent: the proof never
  discusses the load, and the bound `k` is part of the claim. The polylog-factor claim of the
  abstract survives. (`theorem_6_5_load_false`, `exists_run`; corrected bound `theorem_6_5_load`)
* **Proof of Theorem 6.5: a false intermediate claim (statement true).** The proof claims that
  after `k` iterations at most `(1 − 1/(2L+2))^k (1 − ε) n` vertices of `S ∪ R` remain unassigned.
  This can fail because the cross-graph matchings may keep picking unassigned vertices outside
  `S ∪ R`. Example: the star `K_{1,9}` with a partial NAF on 3 vertices of load `2`. After 7
  iterations a vertex of `S` is still unassigned, although the bound is `(5/6)^7 · 3 < 1`. The
  repair counts *all* assigned vertices. Each call assigns at least `|S \ A|/(2L+2)` new vertices,
  and this gives the stated coverage `(1 − ε)(1 − e^{−k/(2L+2)})` and the "in particular" claim
  for `k ≥ (2L+2) ln n`. (`proof_6_5_step_false`; `theorem_6_5_coverage_exp`,
  `theorem_6_5_full_coverage`)
* **Proof of Theorem 6.3: the normalisation does not terminate as described (statement true).**
  The proof redirects `f(f(v))` to a load-0 vertex `v`, "repeated … to all leaves in turn". At a
  leaf of a star with a bidirected edge `r ↔ x₁`, this just moves the leaf to `x₁` and cycles
  forever. The claimed final shape also contains leaves and misses "double stars". Repair: apply
  the move only where `f(v)` is not on a 2-cycle and `v` has load `< L`. Each move strictly
  decreases `|{v : f³(v) ≠ f(v)}|`. When no move applies and `L ≥ 2`, a counting argument gives
  `f³ = f`, so every component is a 2-cycle with leaves. Labelling in-neighbours injectively by
  `1..L` then yields `L` matchings. (`theorem_6_3`, `exists_cover_of_naf`)
* **Theorem 1.1 is literally false for `Δ = 1` (degenerate).** For `Δ = 1` the energy bound
  `2C (log n)(log Δ)` is `0`. But a node is matched only in a round in which it sends or listens,
  so on any graph with an edge the event of Theorem 1.1 is empty. With the usual convention
  `log Δ ≥ 1` this disappears. (`theorem_1_1_delta_one`)
* **Typos and slips.** In the proof of Lemma 5.4, "first bad round: `Δ(t) ≥ 1/(2r(t))`" should
  read `Δ(t − 1)`. The proof of Lemma 5.6 switches from `d(v, t−1)` to `d(v, t)` inside an
  expectation conditioned on `M(t−1)`; a case split on `d(v, t−1)` is intended. The energy
  computation of Theorem 1.1 has `r(T)` for `3r(T)`. `T = CΔ log n` need not be an integer.

Full list of differences (including modelling choices and minor imprecisions):
[differencies.md](differencies.md).

## The formalization

**Model.**
* *Graph theory (Section 6).* `G` is a finite simple graph. A NAF is `f : V → V` with
  `G.Adj v (f v)`. A matching cover is `k` Mathlib matchings (`Subgraph.IsMatching`) whose vertex
  sets cover `V`. Theorem 6.3 assumes no isolated vertices; otherwise neither NAFs nor covers
  exist.
* *Radio model (Sections 2.3, 4, 5).* Synchronous rounds of three timesteps, no collision
  detection: a listener receives iff exactly one neighbour sends. IDs are unique (they are the
  vertices). Algorithms 2–3 are implemented message by message (`Radio.lean`). In each round a
  node draws a role: recruit with probability `r(t)/2`, accept with probability `r(t)/2`, sleep
  otherwise. Matched nodes ignore their role. All draws are independent.
* *Probability.* Executions of `T` rounds are paths `Fin T → V → Role` with the product law
  (`Chain.lean`). One-round statements (Lemmas 5.2, 5.6) condition on the current matching
  `M(t−1)`. Lemma 5.1 holds for *every* role sequence, which is stronger than "with probability
  one".
* *Algorithm 4.* The maximal matching subroutine is a black box. An execution is a sequence of
  maximal matchings: the first of `G`, the later ones of the assigned–unassigned cross graph.
  Theorem 6.5 is proved for every execution in which all calls succeed; the probability wrapper
  `1 − O(k/n²)` is Theorem 1.1's. `log` is `ln`.

**Main results in Lean.** (namespace `Podc.WakeUpMatching`)

| Paper | Lean | File |
|---|---|---|
| Theorem 6.3 (`L ≠ 1`: min NAF load = `mc(G)`) | `theorem_6_3` | `Theorem63.lean` |
| Theorem 6.3 (`L = 1`: `mc ∈ {1, 2}`) | `theorem_6_3_load_one` | `Theorem63.lean` |
| Theorem 6.3, threshold form (`k ≥ 2`) | `exists_naf_iff_exists_cover` | `Theorem63.lean` |
| Theorem 6.3: both values occur (`K₂`, `K₃`) | `k2`, `k3` | `Examples.lean` |
| Theorem 6.5: output is a partial NAF | `out_isPartialNAF` | `Algorithm4.lean` |
| Theorem 6.5: load `≤ k` — **false** | `theorem_6_5_load_false`, `exists_run` | `Algorithm4.lean` |
| Theorem 6.5: load `≤ k + 1` (corrected) | `theorem_6_5_load` | `Algorithm4.lean` |
| Theorem 6.5: coverage `(1−ε)(1−e^{−k/(2L+2)})` | `theorem_6_5_coverage_exp` (sharp: `theorem_6_5_coverage`) | `Algorithm4.lean` |
| Theorem 6.5: `k ≥ (2L+2) ln n` ⇒ coverage `1 − ε` | `theorem_6_5_full_coverage` | `Algorithm4.lean` |
| Proof of Thm 6.5: false intermediate claim | `proof_6_5_step_false` | `Algorithm4Gap.lean` |
| Proposition 2.2 (`β ≥ ν/2`) | `proposition_2_2` | `Algorithm4.lean` |
| Lemma 5.1 | `lemma_5_1` | `Radio.lean` |
| Lemma 5.2 | `lemma_5_2` | `Lemma52.lean` |
| Lemma 5.6 | `lemma_5_6` | `Lemma56.lean` |
| Lemma 5.4 (maximal w.h.p.) | `lemma_5_4`, `lemma_5_4_whp` | `Lemma54.lean` |
| Theorem 1.1, `Δ = 1` corner — **false** | `theorem_1_1_delta_one` | `Theorem11Degenerate.lean` |

**Not formalized.** The w.h.p. energy bound of Theorem 1.1 for `Δ ≥ 2` (Chernoff) and its running
time; the energy claim of Theorem 6.5; Propositions 2.3–2.4 (cited facts about random graphs).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `exists_run` gives successful executions for the Theorem 6.5
counterexample, and `k2`/`k3` instantiate Theorem 6.3. `roundLaw_sum` and `prob_true` show the
role laws are probability distributions. Everything is built on Mathlib only. CSLib candidates:
the NAF/matching-cover theorem (`exists_naf_of_cover`, `exists_cover_of_naf`) and the
path-space chain rule `pathProb_forall_le` (`Chain.lean`).
