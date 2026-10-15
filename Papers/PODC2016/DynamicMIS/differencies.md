# Differences between the formalization and the paper

Paper: K. Censor-Hillel, E. Haramaty, Z. Karnin, *Optimal Dynamic Distributed MIS*, PODC 2016
(arXiv:1507.04330v2). Summary: Theorem 1, Lemma 2, Lemma 3 (in corrected form), Claims 4–5 and
Corollary 6 (synchronous) are correct and formalized. We found no error that breaks a main result.
We did find several imprecise or wrong statements:
- the definition of the sets `S_i` (items 1–2);
- the equality in Lemma 3 (item 6);
- the informal arguments in Lemma 2, Claim 4 and the end of Lemma 3 (items 5–7).

Section 4 (Algorithm 2) is formalized; see the last section below.

## Definitions and modelling

1. **Recursion (1) for the influenced sets `S_i` is inconsistent with its use.** The rule for
   `M̄`-nodes is cumulative (`every v ∈ I(u) ∩ M is in S_0 ∪ … ∪ S_{i-1}`). Taken literally, a node
   that enters some `S_i` by this rule is in *every* later `S_j` (`DynamicMIS.mem_layer_of_inMbar`).
   Three consequences:
   - `i_u = max {i | u ∈ S_i}` is undefined, so Algorithm 1 ("for `i ← 1` until `S_i = ∅`") does
     not terminate whenever `S` contains such a node.
   - The paper's example (`u2` is in `S_1` and in `S_4`) is at least misleading. The paper never
     says `u2 ∉ S_2, S_3`, but by (1) `u2` is in every `S_i` with `i ≥ 1`.
   - The reasoning "`u2 ∈ S_4` via `w2`" only works if the states in (1) are the *current*,
     dynamically updated states, not the states before the change.

   **Verdict:** a genuine but notational flaw.

   We formalize the only unambiguous object, `S = ⋃ S_i`: the least set containing `v*` that is
   closed under the two rules (`DynamicMIS.Influenced`, with `mem_layers_iff` proving
   `⋃ layer i = Influenced`). The states used are the greedy states before the change. Theorem 1
   is about `|S|` only, so nothing else is needed.

2. **`S` versus the nodes that actually change.** `S` can be strictly larger than the set of nodes
   whose output differs (`u2` in the example changes twice and ends where it started). We prove
   `adjustments ⊆ S` (`adjustments_subset_infl`). Theorem 1 is stated for the paper's `S`
   (`theorem1`) and also for the adjustments (`expected_adjustments_le_one`).

3. **Node changes on a fixed vertex type.** A configuration is a graph `G` on a finite type `V`
   plus a set `A` of present nodes; the network is `G[A]`. A node insertion or deletion changes
   `A` only. The paper treats a deleted node `v*` as "still in the graph w.r.t. the invariant of
   the other nodes"; we use the node set `A_old ∪ A_new` in the closure, which differs from the
   paper's choice only at `v*` (the base of the closure), so the sets agree. No validity hypotheses
   are needed: changes that do nothing (inserting an existing edge, deleting a missing node, a
   self-loop `a = b`) give `S = ∅`.

4. **Random order.** `π` is a uniformly random bijection `V ≃ Fin |V|`. Expectations are finite
   averages (`Finset.expect`). The real IDs `ℓ_v ∈ [0,1]` of Section 4 are replaced by ranks; ties
   have probability 0 there.

## Proofs

5. **Lemma 2.** The paper states "`S ⊆ S′`" and argues in the outline that `S = S′`. We prove
   `S = S′` whenever `S ≠ ∅` (`lemma2`). Here `S′` is computed in the graph without the changed
   edge (or with the changed node), with `v*` moved to the front of the order. This is the
   paper's `S′`.

   The paper's proof of the first part ("`w ∈ M` … hence `w ∈ S′_1`, a neighbour of `v*`") mixes
   states computed for `π` and for `π′`. We replace it with
   `SimpleGraph.exists_mem_influenced_of_notMem`: if `v*` is present but not in the greedy MIS,
   then its earlier MIS neighbour is influenced once `v*` is moved to the front.

6. **Lemma 3 as stated (with "`= 1/|P|`") is false for edge changes.** This is a genuine
   misstatement, but harmless. If `v** ∈ P` and
   `v** ≠ v*`, the conditional probability is `0`. The paper's own proof treats this case ("the
   value of the expression is clearly 0") and concludes only `≤ 1/|P|`, which is all that
   Theorem 1 needs.

   Concrete instance: `H` = the path `v* – z – v**`, change = inserting or deleting the edge
   `{v*, v**}`. For any order `z < v** < v*` we get `S′ = {v*, z, v**}` and `π(v**) ≤ π(v*)`, so
   `Pr[π(v*) = min π(P) | S′ = P, π(v**) ≤ π(v*)] = 0 ≠ 1/3` (`lemma3_eq_counterexample` in
   `Lemma3Counterexample.lean`). The counterexample works whether `v*`, `v**` are read as fixed
   labels or as the `π`-dependent later and earlier endpoints: on the conditioning event they
   coincide.

   For node changes (`v** = v*`) the equality is true; we prove it in the summed form
   `Cslib.RandomOrder.sum_card_first_eq`. As a consequence, **`E|S| = 1` exactly** for effective node
   insertions and deletions (`theorem1_node_eq`), which is stronger than the paper's `≤ 1`.

7. **Claims 4–5 and the end of Lemma 3.** Our proof avoids states. The influenced set is the
   `none`-set of a three-valued (Kleene) greedy evaluation in which `v*` is unknown
   (`SimpleGraph.partialGreedy`). It equals the paper's closure for any state vector that satisfies
   the invariant away from `v*` (`DynamicMIS.influenced_iff`).
   - **Claim 4.** Case 2 ("since `w ∈ P` it is possible that after the algorithm `w` will be in
     `M` … so `u` must be in `M̄`") becomes the lemma "a surely-in node has no influenced
     neighbour" (`notMem_influenced_of_adj`). This lemma needs `v*` to be first and the ranks to be
     injective.
   - **Claims 4 and 5.** Combined, they become `partialGreedy_eq_of_reorder`. Claims 4–5 are
     stated for "`π|P = σ|P`", which includes the relative position of `v*`. The proof of Lemma 3
     uses them for orders that agree on `P \ {v*}` and on `V \ P` only. This is harmless because
     `S′` does not depend on `π(v*)`, and our statement directly uses `P \ {v*}`.
   - **End of Lemma 3.** The paper conditions on `π(v**) ≤ π(v*)` and argues by an independence
     claim (inside `Π_P`, "`v*` first in `P`" is independent of "`v**` before all of `P`"). The
     claim is true, but we replace it with a counting argument. Swapping `v*` with its successor
     in `P` is an injection that preserves `S′ = P` and the event "`v**` before `v*`". It gives
     `|P| · #{π ∈ Π_P : v* first, v** before v*} ≤ #{π ∈ Π_P : v** before v*}`
     (`Cslib.RandomOrder.sum_card_first_le`). Conditioning on the orientation of the changed edge is
     replaced by summing over both orientations (`sum_le_factorial_edge`).

8. **Theorem 1** is proved as stated, for all four kinds of changes (`theorem1`); there are no
   extra assumptions.

9. **Corollary 6.** Only the synchronous model is formalized. The "direct implementation" is: from
   the old states, every node repeatedly applies the greedy rule in the new graph. It is a SET-LOCAL
   algorithm in the CSLib `Cslib/Computability/Distributed/Local` round model (`run_directAlg`).
   - We prove that it reaches the new greedy MIS within `|S|` rounds and that only nodes of `S`
     ever change (`directAfter_eq_of_le`, `corollary6_changing_subset`).
   - Hence `E[rounds] ≤ 1` and `E[adjustments] ≤ 1`.
   - "Rounds" means the stabilisation time `directRounds`. The asynchronous model ("longest path
     of communication") is not formalized.

## Not formalized

10. The introduction's lower bound for deterministic algorithms (`n` adjustments on complete
    bipartite graphs), the correlation-clustering application (3-approximation of Ailon et al.),
    the `O(1)`-bit encoding of IDs, and the Section 5 examples (star, 3-paths, colouring) and
    composability claims.

11. **Section 5 (history independence): only a weak, almost trivial version.**
    - `historyIndependent` is proved for the *direct implementation*: each change is processed by
      `|V|` rounds. It is **not** proved for Algorithm 2.
    - It compares histories that start from the same `Config` and end in the same `Config`
      (graph on the full vertex type plus present set).
    - Its content is just that the output is the greedy MIS of the final configuration
      (`maintained_eq_greedyMIS`). This is weaker than Definition 14 and close to trivial.
    - For Algorithm 2, the per-change analogue is `Alg2.alg2_run_eq_of_le`: from round `3|V|` on,
      the configuration encodes the new greedy MIS. It follows directly from `graceful_run_eq`.
    - Composability and the examples are not formalized.
11b. **Round complexity via `sInf`.** `directRounds` and `alg2Rounds` are `sInf` of the set of
    stabilisation times, which is 0 if the set is empty. This is harmless: stabilisation is proved
    first (`directAfter_eq_of_le`, `graceful_stableFrom`, `abrupt_stableFrom`), and the bounds go
    through `Nat.sInf_le`.

## Section 4 (Algorithm 2)

12. **Model.** Synchronous broadcast rounds, with the four rules of Algorithm 2 encoded literally
    (`Alg2Defs.lean`).
    - "`u` changes to `C`" means `u` entered `C` in the previous round.
    - "Changed to `C` at least two rounds ago" means `C`-age `≥ 1`.
    - **Added:** rule 4 puts a node into `M` only if it is *active*. A gracefully deleted node
      still participates but must end in `M̄`; the paper is silent on this.
    - Ranks replace the real IDs `ℓ_v`.
    - Node insertion with announcement rounds (Section 4.1) is not modelled separately; unmuting
      is `insertNode`.
    - Message sizes (`O(log n)` bits, constant bits per broadcast) are not modelled.
    - The number of broadcasts is the number of (node, round) pairs in which the visible state
      class changes.
13. **Bounds are slightly better than the paper's.**
    - Stabilisation happens by round `3|S|` (paper, Lemma 11: `3|S|+2`), for both non-abrupt
      changes and abrupt deletion.
    - Lemma 12's spacing is `t₂ ≥ 3t₁ + 4` with initial `C`-entries at time 0, i.e. paper rounds
      `t₂ ≥ 3t₁ + 2`, versus the paper's `3t + 1`.
    - The `log` bound is stated as `log₃(|S|+1)+1` entries.
14. **Lemma 8 has a different proof.** The paper argues "`v*` is the first node to leave `R`, and
    then all of `S` is in `R`". We prove instead that distinct `C`-entries of a node have distinct
    *roots* (initially-`C` nodes). For non-abrupt changes `v*` is the only root, so every node
    enters `C` at most once and changes at most 3 times.
15. **Gap in Lemma 12, second part.** The paper claims "each change of `v` to `C` can be
    associated with a different `v_i*`". Its argument ("`v_i*` is already final, so the next entry
    comes from another `v_{i'}*`", while conceding that the new path may pass through `v_i*`) is
    incomplete. The missing fact, proved in `Alg2Roots.lean`: the root of the entry at `t₂` stays in
    `C` during `[0, 2t₂+1]`, whereas the root of the entry at `t₁` is already final by time
    `t₂ − 1 − t₁`; hence the two roots differ. The claim itself is true.
16. **Correctness of the final MIS in the abrupt case** is not argued in the paper ("It is
    straightforward to verify…"). We prove it with two invariants:
    - (J1) a node in `M` has all predecessors in `M̄` or just changed to `C`;
    - (J2) an active node in `M̄` has a predecessor in `M` or one that just changed to `C`.

    With all nodes final, J1 and J2 force the greedy rule everywhere.
17. **Theorem 7** is stated as expectations over the uniform order (`theorem7_graceful`,
    `theorem7_abrupt`). "Rounds" means the stabilisation time `alg2Rounds`. For abrupt deletion,
    `E[broadcasts] ≤ 3·min(log₃(n+1)+1, deg x)`, which is the paper's `O(min(log n, d(v*)))`.
