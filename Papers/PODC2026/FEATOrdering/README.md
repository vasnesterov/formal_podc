# FEAT: Fair and Efficient Adversarial Transaction Ordering — PODC 2026

Tien Tuan Anh Dinh, Dakai Kang, Mohammad Sadoghi. *FEAT: Fair and Efficient Adversarial Transaction Ordering.*
PODC 2026. DOI [10.1145/3796701.3815905](https://doi.org/10.1145/3796701.3815905). Formalized version: the
11-page PODC version (no arXiv version). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** The protocol as defined does not achieve what Theorem 6.6 claims (FEAT
achieves comparator-based γ-Batch-Order-Fairness), and Theorem 6.4 and Lemma 6.3 fail with it. The cause is the
transaction score: the paper counts only **honest** replicas, and a 7-replica run with `f = 2` makes FEAT output
`[z, m]` although `cmp_T(z, m) = False`. If the score counts **all** replicas, Lemma 6.3 and Theorems 6.4 and 6.6
hold, and we prove them. Theorem 4.4 (ACC suffices) and the `Ω(|T| log |T|)` lower bound (Theorem 4.5, Corollary
4.6) are correct, and we prove the lower bound in a stronger form. The fix is one word in a definition, so this
verdict is borderline: if "honest" is read as a slip, the verdict would be ⚠️ (see [differencies.md](differencies.md)).

## Mistakes in the paper

* **Lemma 6.3 is false, and with it Theorems 6.4 and 6.6.** §5.1 defines `score(T)` as the number of *honest*
  replicas whose committed local orderings include `T`. Case 2 of the proof of Lemma 6.3 reasons as follows: `z` is
  solid and `m` is blank, so `W(z, m) > τ_dec = τ_shaded > W(m, z)`. The second inequality needs
  `W(m, z) ≤ score(m)`. But `W(m, z)` counts *all* committed orderings, including the Byzantine ones. Here is a
  counterexample with `n = 7`, `f = 2`, `γ = 1` (so `n > (2γ+1)f/(2γ−1) = 6`), `τ_dec = 5/2` and `τ_solid = 5`:
  * Honest replicas 0 and 1 receive `m, z`, and honest replicas 2, 3 and 4 receive `z, m`.
  * In round 1, replicas 0 and 1 and both Byzantine replicas commit `[m, z]`, and replicas 2, 3, 4 commit `[z]`.
    So `z` is solid (honest score 5) and `m` is blank (honest score 2). Also `W₁(m, z) = 4 > W₁(z, m) = 3 ≥ τ_dec`,
    so the pair is decided in round 1: `cmp_T(z, m) = False`. FEAT finalizes `FO₁ = [z]`.
  * In round 2, replicas 2, 3 and 4 commit `m`. Now `m` is newly solid, so `RO₂ = [m]` and FEAT outputs
    `FO₂ = [z, m]`.

  FEAT never compares this pair. The output violates ACC and the linear-batch-partition clause of Definition 4.1:
  the batches are `{z}` and `{m}`, `z` comes first, but `cmp_T(z, m) = False`. All system-model assumptions hold.
  Rounds after 2 commit nothing new (empty fragments), so `FO₂` is the final ordering. The γ-precedence clause is not
  violated in this run. What fails is the claim that FO is consistent with FEAT's own comparator, and that claim
  is exactly what Theorems 6.4 and 6.6 state. If the score counts all replicas, the proof goes through:
  `W(m, z) ≤ score(m) < τ_shaded`. On the same run, FEAT then inserts both transactions in round 1 and outputs
  `[m, z]`. (`lemma_6_3_false`, `theorem_6_4_false`, `theorem_6_6_false`; repaired: `Setup.lemma_6_3`,
  `Setup.theorem_6_4`, `Setup.theorem_6_6`, contrast run `cex_scoreAll_FO1`)
* **The repair needs the "loose" reading of `W`.** In the proof of Lemma 6.3, `W(z, m)` counts orderings that
  contain `z` but not yet `m` ("committed `z` but not `m`"). We use this reading. Under the stricter reading (both
  transactions present, `z` first), Case 2 fails even with the all-replica score. An example: two honest replicas
  that have committed nothing yet later commit `[m, z]`. This is a sketch and is not formalized.
* **Lemma 6.3, Case 1 has a gap (the statement is true).** It says that the head of `TailList_{r−1}` immediately
  followed `z` in `Merged_{r−1}`. This fails when round `r−1` finalized nothing (`ℓ = 0`): then `z` was finalized
  earlier. An invariant over rounds closes the gap: `FO ++ TailList` satisfies ACC and the last finalized
  transaction is solid. (`Setup.inv_step`)
* **Algorithm 3 drops a suffix.** After the loop `while i ≤ |TailList| and j ≤ |RO_r|`, the tests
  `if i = |TailList|` and `else if j = |RO_r|` are both false (the exhausted index is one past the end). So the
  remaining suffix is never appended. The prose (steps (1) and (2)) is correct, and we model the prose
  (`List.merge`).
* **The Theorem 4.5 proof needs the positional comparison model.** "Fix `cmp★`, then `A` sorts the random
  permutation" works only if the algorithm sees the transactions through their input positions. The theorem
  itself holds more generally. If the algorithm also sees the transaction identities, averaging over the `|T|!`
  linear comparators gives the same bound. (`theorem_4_5_of_linear`, `theorem_4_5_identityAware`)
* **Corollary 4.6 holds more broadly than stated.** For a linear comparator, Definition 4.1 already forces the
  sorted order. So the `Ω(|T| log |T|)` bound holds for every algorithm guaranteeing comparator-based γ-BOF, not
  only those "relying on ACC". (`corollary_4_6`)
* Minor slips:
  * Algorithm 1 inserts the transactions that are "newly solid" or "newly shaded". Read literally, a transaction
    that turns from shaded to solid would be inserted twice. The prose says "newly non-blank".
  * Rule (4) of `pcmp` says "both weights exceed the threshold". It should be `≥`, as in rules (2) and (3).
  * Replicas cannot know which replicas are honest, so an honest-replica score cannot be computed by the protocol.
  * The bound `W(T_j, T_i) ≤ (1−γ)(n−f) + f` in Lemma 6.5 implicitly takes exactly `n − f` honest replicas. It
    remains true with more honest replicas: `n − γ|H| ≤ n − γ(n − f)`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `n = |R|` replicas: the honest set `H` and at most `f` Byzantine replicas. Every round has its own "committed
  local ordering up to round `r`" `L r i`, which only grows. Honest committed orderings are prefixes of the receive
  orders (consensus property (3)). Every transaction received by an honest replica is eventually committed by all
  honest replicas (property (4)). Byzantine orderings are arbitrary, and fragments may be empty. Synchrony and
  the consensus layer are abstracted into this round-indexed data, as the paper does.
* `W_r(a, b)` counts orderings that contain `a` and do not have `b` before it. `pcmp^(r)` implements rules
  (1)–(4) with `W ≥ τ_dec` written as `n − f ≤ 2W`. `cmp_T` takes the value of `pcmp` at the first round where it
  is defined. A pair that is never decided defaults to the tie-break hash; under the assumptions this never
  happens for pairs that matter.
* FEAT (`Setup.run`) answers every comparison with `cmp_T`. In the protocol, `⊥` only delays an action (deferral or
  waiting), and every defined answer equals `cmp_T`. So the only effect of timing is the order in which insertions
  succeed. We therefore quantify over every insertion order of the newly non-blank transactions (`InsOK`), and over
  every in-order-preserving rebalancing (AVL rotations). The score is a parameter: `scoreHonest` is the paper's,
  `scoreAll` is the repair.
* Definition 4.1 is stated for a finite list `FO`, with batches the strongly connected components of the comparator
  graph on its elements. "At least a `γ`-fraction of honest replicas receive `a` before `b`" is `GammaPrec γ`.
  Theorem 6.6 is proved for every round's `FO_r`.
* Lower bound: a deterministic comparison-based algorithm is a binary decision tree (`Cslib.DecisionTree`) over
  queries `(i, j)` of input positions. We count queries, and the expectation is over a uniformly random arrival order.

**Main results in Lean.** (namespace `Podc.FEATOrdering`)

| Paper | Lean | File |
|---|---|---|
| Def. 4.1–4.3 | `BatchOrderFair`, `GammaInduced`, `AdjConsistent` | `Fairness.lean` |
| Theorem 4.4 | `theorem_4_4` | `Fairness.lean` |
| Theorem 4.5 (paper's proof, any linear `cmp★`) | `theorem_4_5_of_linear` | `LowerBound.lean` |
| Theorem 4.5 (`max_cmp E_π ≥ log₂ n! ≥ n log₂ n / 2`) | `theorem_4_5`; identity-aware: `theorem_4_5_identityAware` | `LowerBound.lean` |
| Corollary 4.6 (strengthened to Def. 4.1 algorithms) | `corollary_4_6` | `LowerBound.lean` |
| Lemma 6.1 | `lemma_6_1` | `Tree.lean` |
| Lemma 6.2 | `lemma_6_2` | `Tree.lean` |
| Lemma 6.3: **false** as stated / repaired | `lemma_6_3_false` / `Setup.lemma_6_3` | `Counterexample.lean` / `FEAT.lean` |
| Theorem 6.4: **false** as stated / repaired | `theorem_6_4_false` / `Setup.theorem_6_4` | `Counterexample.lean` / `FEAT.lean` |
| Lemma 6.5 | `Setup.lemma_6_5` | `FEAT.lean` |
| Theorem 6.6: **false** as stated / repaired | `theorem_6_6_false` / `Setup.theorem_6_6` | `Counterexample.lean` / `FEAT.lean` |

**Not formalized.** Theorem 6.7 and Corollary 6.8 (the per-round `O(|T| log |T|)` upper bound: AVL heights and
retry counts), Theorem 6.9 (safety: replicas agree), and the query count in Figure 4.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
counterexample `cex` instantiates every field of `Setup` (the system-model assumptions), and `theorem_6_6_false`
checks every other hypothesis of `Setup.theorem_6_6`. Shared infrastructure: `Podc/Computability/QueryComplexity/
DecisionTree.lean` (decision trees, the average-case `log₂ |S|` bound, `log n!` bounds; CSLib candidate).
