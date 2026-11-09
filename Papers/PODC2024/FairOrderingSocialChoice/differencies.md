# Differences between the formalization and the paper

Paper: Ramseyer, Goel, *Fair Ordering in Replicated Systems via Streaming Social Choice*, arXiv 2304.02730v4 (full
version of the PODC 2024 brief announcement). Labels follow `mistakes-labeling.md`.

## Mistakes and proof gaps

1. ❌ **Lemma 3.6 is false** (both bullets), already for `δ = 0`: `lemma_3_6_false`. Bullet 1 also fails for
   every `0 ≤ δ < 1/6`: `lemma_3_6_part1_false`. The proof wrongly assumes that Definition 3.5 forces every pair
   across two components joined by an edge to be ordered. The counterexample does not depend on reading "`γn`
   replicas" as `≥ γn` (our `AtLeast`): the thresholded graph is the same for every threshold in `(1/2, 2/3]`
   (`Lemma36.atLeast_iff`), so under a strict `> γn` reading any `γ ∈ (1/2, 2/3)` gives the same counterexample.
   Only the pairwise version holds: `lemma_3_6_pairwise`,
   with components of the `(γ − 2δ)`-graph. The `(γ − δ)` threshold of the paper is not enough even pairwise when
   `δ > 0`: two transactions, `n = 10`, `f = 1`, `γ = 0.6`, `δ = 0.1` (by hand, not in Lean). By hand, Ranked Pairs
   produces the interleaved output of the counterexample with a suitable tie-break, so the remark after Theorem 4.1
   ("Ranked Pairs' output can be divided into batches") fails as well.
2. 🛠️ **Lemma 3.4: the proof is wrong; the statement is true.** In the paper's profile no pair reaches `m = ⌈γn⌉`
   votes (`lemma_3_4_paper_construction_vacuous`, `lemma_3_4_paper_construction_n7`). We prove the statement with `k`
   scenarios forming a forced cycle (`lemma_3_4`, core `Impossibility.cyclic_fails`), plus a separate 2-transaction
   argument when `⌊n/(n−m+1)⌋ = 1`, a case the paper's construction does not cover.
3. 🔧 **Output rule of Algorithms 3 and 1.** Literally every transaction borders the indeterminate edge `(τ, v̂)`, so
   the output is always empty. We ignore the edges `(τ, v̂)` (`Streaming.Clean`, `Streaming.output`). For the printed
   rule, Theorem 5.10 and Corollary 5.9 are trivial and liveness (Theorems 6.5, 6.9) fails.
4. 🔧 **Corollary 5.9: proof gap.** The proof gives only consistency with Ranked Pairs, not that earlier outputs are
   kept. Repaired by `dec_mono` (stability of determinate decisions under extension) and `clean_mono`; the result is
   `corollary_5_9`.
5. 🔧 **Lemma 3.8: proof gap.** The step `(f+1)/n ≤ 2f/n` fails for `f = 0` (`paper_step_false`). The example needs
   `γ ≥ 1/2 + 1/n` (`Themis.cycleDeps_iff`, `cycleDeps_fails_small_n`); `n` can be chosen large
   (`lemma_3_8_exists`).
6. ✏️ **Remark after Definition 3.3** ("the condition admits `f = 1`" for `n = 7`, `γ = 2/3`): the stated condition
   `f > n mod (n − ⌈γn⌉ + 1) = 1` excludes `f = 1` (`lemma_3_4_n7_f1_not_covered`). Impossibility at `f = 1` is
   nevertheless true (`lemma_3_4_n7_f1`, groups of sizes 3, 3, 1 on three transactions).
7. Typo: Definition 3.1 in §3.1 swaps `τ` and `τ'`; we follow the abstract and §1.1 (not formalized: batches).

## Modelling choices

- **Votes.** In Sections 3–4, a vote is a strict total order on the transactions (`Cslib.SocialChoice.Pref X`);
  every replica votes on every transaction. In Section 5, a vote is a `List α`, and "before" is the comparison of
  first occurrences (`List.idxOf`). We do not need votes to be duplicate-free.
- **Faulty replicas.** We use a true profile `T`, a reported profile `P`, and a faulty set `F` with `P i = T i` for
  `i ∉ F`. Faulty votes are arbitrary total orders. Theorem 4.1 is stated for `δ = |F|/n`.
- **Definitions 3.3/3.5** count *true* receptions ("at least `γn` replicas received"). The sequence
  `τ' = τ₁, …, τₖ = τ` is a `ReflTransGen` path. Definition 3.1 (batches) is not formalized. Lemma 3.4 is proved for
  the weaker requirement (exact minimality when the true `γ`-graph is acyclic), which implies the paper's version.
- **Lemma 3.4** is stated as: for `0 < n`, `1/2 < γ ≤ 1` and `f > n mod (n − ⌈γn⌉ + 1)`, there is a number `k` of
  transactions such that every deterministic aggregation `(Fin n → Pref (Fin k)) → Pref (Fin k)` fails in some
  scenario with at most `f` faulty replicas. `n > 0` is needed: with no replicas every pair is a `γ`-edge and any
  order is exactly minimal.
- **Ranked Pairs.** Edges are processed in increasing `key`, where `key` is injective (a fixed tie-breaking rule)
  and weight-antitone. "Ties broken arbitrarily" means quantifying over all injective `tb`. The output is the
  transitive closure of the accepted edges (equal to the unique topological sort). Theorem 4.1 is proved for every
  real `γ`, via `minimalBatchFair_of_approx` (any weights within `ε` of the truth).
- **Lemma 6.11** is proved for non-streaming Ranked Pairs on rounded weights (any injective order compatible with
  the rounded weights). The paper's statement is about Algorithm 1, whose equivalence to Ranked Pairs with an
  induced tie-break (Lemma 6.1) we did not formalize.
- **Streaming (Section 5).**
  - Transactions form a type `α` with an injective global tie-breaking rule `tb : α × α → ℕ` (so `α` is
    countable, as in the paper). The same rule is used by every invocation and by the counterfactual Ranked Pairs.
  - Algorithm 3's loop ranges over edges between transactions voted on by all replicas. Edges incident to `v̂` are
    the initial indeterminate edges; their weights play no role.
  - `R_τ` and `P_τ` exclude `τ` itself (otherwise `τᵢ ∉ U_{τᵢ,τⱼ}` and every edge would be accepted).
  - Algorithm 3 is defined by well-founded recursion on the processing order, with `H` at each step consisting of
    the earlier accepted and indeterminate edges plus the initial `v̂` edges.
  - The counterfactual of Lemma 5.8 is any `σc` such that each `σ i` is a prefix of `σc i` and all `σc i` contain
    the same transactions (`Complete`). One always exists (`exists_completion`).
  - Output: a set with the order `detLt`. "Extends" (Def. 5.1) and "initial segment" (Thm. 5.10) are stated as
    containment, down-closure and agreement of the orders.
  - `[Nonempty ι]`: at least one replica.
- **Lemma 3.8** formalizes only the arithmetic of the example: the profile, Themis's dependency rule as
  paraphrased in the proof (weak majority and at least `n(1−γ)+f+1` votes, ties broken by choice), and the walk
  along the Hamiltonian cycle. Themis itself is not modelled.

## Not formalized

Lemma 3.7 (Aequitas); Lemmas 6.1–6.10 and Theorems 6.5, 6.9 (Algorithm 1, liveness, delay bounds); Lemma E.1
(truncation); the examples in Appendices F, G, H, I; the protocol instantiation in §L.
