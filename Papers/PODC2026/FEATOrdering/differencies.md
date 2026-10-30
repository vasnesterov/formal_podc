# Differences between the formalization and the paper

Paper: Dinh, Kang, Sadoghi, *FEAT: Fair and Efficient Adversarial Transaction Ordering*, PODC 2026 (11-page version).

## Statement-level issues (decide the verdict)

1. **Lemma 6.3, Theorem 6.4 and Theorem 6.6 are false with the paper's score.** The score `score(T)` in §5.1 counts
   honest replicas only. Lean counterexample: `lemma_6_3_false`, `theorem_6_4_false`, `theorem_6_6_false`
   (`Counterexample.lean`), with `n = 7`, `f = 2`, `γ = 1` and two transactions. The failing step is Case 2 of the
   proof of Lemma 6.3: `τ_shaded > W_{r−1}(m, z)` does not follow from `score(m) < τ_shaded`, because Byzantine
   replicas add to `W(m, z)`. The counterexample satisfies all of the paper's model assumptions:
   - committed orderings are append-only;
   - honest orderings are committed in receive order;
   - every honest-received transaction is eventually committed by all honest replicas, within `c = 2` rounds;
   - `n > (2γ+1)f/(2γ−1)`;
   - authenticated, Byzantine-arbitrary orderings.

   It relies on fragments being allowed to be empty (assumption (2) asks for fragments from `≥ n − f` replicas each
   round). The violated property is clause (1) of Definition 4.1 (linear batch partition), together with ACC. The
   γ-precedence clause (2) holds in this run.
   *Rule:* R5 + R3. Theorem 6.6 ("FEAT achieves γ-Batch-Order-Fairness") is the paper's headline correctness claim
   for its named algorithm, so we give 🚨.
   *Borderline (R3).* The fix is one word: count all replicas (`scoreAll`). The honest-only score cannot be
   computed by replicas. The final inequality of the paper's proof is valid only for the all-replica score.
   Against excusing it: the paper states "honest" explicitly in the definition, and again in the proof ("more than
   `τ_dec` honest replicas have committed `z` but not `m`"). The natural "conservative" implementation
   (`score_all − f`, a lower bound on the honest count) also fails, by the same counterexample pattern with Byzantine
   weight. Changing the classification rule changes the protocol, and R3 excludes protocol design changes and proofs
   that reason with the wrong version. A reviewer who reads "honest" as a slip would give ⚠️.
   *Repaired:* `Setup.lemma_6_3`, `Setup.theorem_6_4`, `Setup.theorem_6_6` (with `scoreAll`).

2. **Algorithm 3 pseudocode drops the remaining suffix.** The post-loop tests `i = |TailList|` and `j = |RO_r|`
   should be `i > |TailList|` and `j > |RO_r|`. The prose (stitching steps (1)–(3)) is correct, and we formalize
   the prose (`List.merge` with `cmp_T`). *Rule:* R3 (local fix, intent recoverable) → ⚠️; dominated by item 1.

3. **Algorithm 1, "newly solid / newly shaded".** Read literally, a transaction that was shaded in round `r` and
   becomes solid in round `r' > r` would be inserted again. The prose says "newly non-blank", and we formalize that
   (`InsOK.new`). *Rule:* R3 → ⚠️.

## Proof-level issues (true statements)

4. **Lemma 6.3, Case 1.** The proof assumes that `z` was finalized in round `r − 1`. If round `r − 1` finalized
   nothing, `z` comes from an earlier round. Repaired by an invariant over rounds (`Setup.Inv`, `Setup.inv_step`):
   `FO ++ TailList` satisfies ACC, has no duplicates and consists of non-blank transactions, and the last finalized
   transaction is solid.
5. **Theorem 4.5, proof.** "Fix `cmp★`; then `A` sorts the random permutation" is valid only in the positional
   comparison model. There the algorithm sees input positions, not transaction names. We prove that version
   (`theorem_4_5_of_linear`, for every linear `cmp★`). We also prove the identity-aware version by averaging over
   the `|T|!` linear comparators (`theorem_4_5_identityAware`).
6. **Lemma 6.5.** The bound `W_r(T_j, T_i) ≤ (1−γ)(n−f) + f` assumes exactly `n − f` honest replicas. In general
   it is `≤ n − γ|H| ≤ n − γ(n−f)`, which is what we prove. Routine.

## Modelling choices

7. **Rounds and timing.** `L r i` is the committed ordering of replica `i` after round `r`. The consensus layer is
   abstracted into this data, as in the paper.
8. **Comparisons answered by `cmp_T`.** In FEAT, a comparison returns either `⊥` or `cmp_T`. A `⊥` delays a
   shaded insertion or the merge, and the eager definition of §4.1 makes `pcmp^(r')` equal to `cmp_T` once defined.
   So `Setup.run` uses `cmp_T` directly, and all theorems quantify over every insertion order (`InsOK`): solids
   first, then shaded ones in the order in which their insertions succeed.
   The paper's lazy implementation ("if the pair has not been decided before, compute with round-`r` weights")
   differs from the eager definition when a pair is first queried after the round in which it became decidable.
   We follow the definition of `cmp_T` in §4.1. The counterexample of item 1 makes no comparison at all (singleton
   trees, merges with an empty list), so it does not depend on this choice.
9. **AVL tree.** We use BST insertion followed by an arbitrary rebalancing `bal` that preserves in-order
   traversals. This covers AVL rotations. Heights are not modelled; Theorem 6.7 is not formalized.
10. **Reading of `W`.** `Before l a b`: `l` contains `a`, and `b` is absent or comes later. Lemma 6.3 uses this
    reading ("committed `z` but not `m`"), and so do the solid-vs-anything decidability claim and Case 2. Under the
    strict reading (both present), Case 2 fails even with the all-replica score; this is a sketch, not
    formalized. The counterexample of item 1 works under both readings: `W₁(m, z) = 4`, `W₁(z, m) ∈ {3, 0}`.
11. **Thresholds.** `W ≥ τ_dec = (n−f)/2` is `n − f ≤ 2W`, solid is `score ≥ n − f`, non-blank is
    `score ≥ (n−f)/2`. In rule (4) we read "exceed" as `≥`. Ties are broken by an antisymmetric `tb`. We set
    `pcmp r a a = some true`, and a pair that is never decided defaults to `tb`. That default is never used for
    γ-pairs, because they are always decided (`lemma_6_5`).
12. **"γ-fraction of honest replicas receive `a` before `b`"** is
    `γ·|H| ≤ #{i ∈ H | Before (recv i) a b}` (`GammaPrec`). `Setup` requires that every transaction received by
    an honest replica is eventually committed by all honest replicas.
13. **The transaction set and the final ordering.** Definition 4.1 is stated for a finite list `FO` (the
    transaction set is its elements). Batches are the strongly connected components of the comparator graph
    restricted to these elements, with reflexive reachability. Theorem 6.6 is proved for every `FO_r`.
    `FO_r` only grows (`Setup.FO_prefix`), and it never contains duplicates (`Setup.FO_nodup`).
14. **Tournament.** Theorem 4.4 assumes only that for distinct elements one of `c a b`, `c b a` holds (`Total`).
    `cmp_T` satisfies this (`Setup.cmpT_total`).
15. **Lower-bound model.** A deterministic algorithm on `N = |T|` items is one binary decision tree (fixed `N`)
    with queries `(i, j)` on input positions, answered by `cmp(π i, π j)`. It outputs positions. We count
    queries, and the expectation is over a uniform `π`. The `Ω` form is explicit:
    `E ≥ log₂ N! ≥ N log₂ N / 2` for `N ≥ 8`. Randomized algorithms are not considered, and neither does the paper.
16. **Corollary 4.6.** We prove more than stated: the bound holds for every algorithm whose outputs satisfy
    Definition 4.1 (for some `G`) under every tournament comparator (`corollary_4_6`), via
    `adjConsistent_of_batchOrderFair_linCmp`.

## Not formalized

Theorem 6.7 and Corollary 6.8 (per-round `O(|T| log |T|)` upper bound, retry counts), Theorem 6.9 (safety), the
query count in the Figure 4 example, and the liveness of FEAT (that every transaction is eventually finalized).
