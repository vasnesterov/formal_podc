# Differences between the formalization and the paper

Paper: Feigenbaum, Godfrey, Panda, Schapira, Shenker, Singla, *On the Resilience of Routing Tables*,
arXiv:1207.3732v2 (full version of the PODC 2012 brief announcement).

## Model (Section 2)

1. **Links as neighbours.** The paper's `f^d_i : E_i × 2^{E_i} → E_i` takes the incoming edge and the
   set `E_i \ F` of live incident edges and returns an outgoing incident edge. In `Pattern.next i A u`
   the incoming edge is the neighbour `u`, the live set is the neighbour set `A`, and the result is a
   neighbour. For simple graphs this is a bijective re-encoding. The domain of `next` contains junk
   arguments (sets `A` that are not sets of neighbours, non-neighbours `u`); they are never used.
   `adj_next` keeps the codomain `E_i`: the output is an incident link, possibly a failed one, and a
   packet sent on a failed link is lost.
2. **Destination is a sink.** The paper constrains consecutive edges only at nodes `i ∈ [n]`, so a
   literal forwarding path may run through `d` and continue. With that reading condition (2) fails
   already with no failures whenever `d` has a link, because `d, y, …, d, y` repeats a directed edge.
   `Counterexamples.literal_K2` shows this on `d – 1`. We require interior vertices to be different
   from `d`, so packets stop at `d`. This is the obvious intent.
3. **Forwarding paths start anywhere.** As in the paper, a forwarding path may start with any live
   link, including one leaving `d`, and its first hop is unconstrained (the paper does not model the
   source). Condition (1) asks for *some* forwarding path from `i` to `d`. Condition (2) is checked
   on all forwarding paths.
4. **Loop.** "Loop-free" means that no directed link repeats, which is the paper's own definition in
   the proof of Theorem 4.3 ("a forwarding loop is formed when a packet repeats a directed edge").
   Forwarding paths are finite lists, as in the paper.
5. **Failure sets.** `F ⊆ E` (the paper's "`F ⊆ E`"). `|F| ≤ t` is `F.encard ≤ t`. Perfect
   resilience quantifies over all `F ⊆ E`.
6. **Connectivity.** "There exists some route from `i` to `d` in `H^F`" is
   `(G.deleteEdges F).Reachable i d`, for `i ≠ d`.

## Theorem 3.1

7. **Hypothesis: connected network.** We assume `G.Connected` (and `V` finite). Without it the
   statement is false as soon as some component without `d` has a link
   (`Counterexamples.theorem_3_1_disconnected`, two nodes `1 – 2` and an isolated `d`, `t = 0`).
8. **Different proof.** We do not formalize the algorithm of §3.2.1 (see 10). We prove existence with
   our own construction, based on an arbitrary rooted spanning tree (BFS tree in `theorem_3_1`):
   minimum lowest-common-ancestor exits and escape hops (`Theorem31.lean`, module docstring).
   It does not start from "arbitrary loop-free routing tables" as the introduction advertises.
   Our construction routes along the tree in the failure-free case, but we do not prove that an
   arbitrary given DAG can be extended.
9. **Stronger conclusion than needed.** The construction delivers every packet in `d`'s component
   whatever its first hop (`deliver_first` and `term_all`). Packets cut off from `d` are dropped.
   The paper's definition requires only one good first hop per node.
10. **The paper's algorithm is ill-specified.**
    - Step 1 sets entries to `∅`, a partial function, while the model has total functions.
    - Step 3 treats `T` as the *failed* set ("highest element in `E^i_D` that is not in `T`") while
      the model's argument is the *live* set. Its guard "`T ∩ E^i_D ≠ ∅`" should be "some outgoing DAG
      link is up".
    - Step 4e/4f write `f_{v_c}(v_{c+1}, v_c)` and `f_j(v_2, v_1)` without the failure-set argument,
      so the scenarios to which the new rules apply are unspecified.
    - The loop of 4e starts at `c = k − 1`, so no rule is installed at `i = v_k` itself. Figure 1's
      rule (a), "node 4 sends traffic from 5 back to 5", is such a rule at `i`.
    - "Bi-connected to `d` in `f^d`" (two edge-disjoint forwarding paths) is not defined precisely,
      for example with respect to which failure scenarios.
    - The proof of Claim 3.2 chooses "another route `R_2` ... not in `D`", but Step 2 orients every
      edge, so every route is in `D`.
    - Case II is argued on Figure 2 only, and refers to "iteration `q_1` of Step 2" (Step 4 is meant).
    - Nodes joined to `d` only through bridges, and loop-freedom (condition (2)) inside components
      cut off by a failure, are never addressed.
11. **Polynomial time** is not formalized (no complexity model). Our construction needs a BFS tree,
    depths of lowest common ancestors and a minimum per subtree, so it is polynomial; this is not
    stated in Lean.

## Lemma 4.1

12. **False as stated** (`Counterexamples.lemma_4_1_false`). The network is `d = 0 – 1` plus the
    triangle `1, 2, 3`. In the perfectly resilient pattern `f41`, every node forwards to 1 and node 1
    forwards to `d`. With no failures, node 2 has the path `2, 3, 1, d`, which avoids edge `21`,
    but `f41` sends packets travelling `1 → 2` back to 1.
13. **Corrected statement** (`lemma_4_1`): the hypothesis is that `v` reaches `d` in
    `G \ (F ∪ {links of u other than uv})`, which is exactly what the paper's proof uses. We also
    assume `u, v ≠ d` and that link `uv` is live. The core argument (`lemma_4_1_core`) concludes that
    `v` forwards a packet from `u` on a live link other than `vu`. The paper's proof only says "not
    back to `u`" and ignores dropping the packet; dropping is also excluded. `pass_through` is the
    special case used in Theorem 4.3. The proof needs only condition (1): if `v` bounces the packet
    back, `u`'s packets loop or are lost.

## Lemma 4.2

14. **False** (`Counterexamples.lemma_4_2_false`). Take the path `d = 0 – 1 – 2 – 3` and the pattern
    "forward to the neighbour closer to `d`". It is perfectly resilient. Node 2 is connected to `d`
    and not adjacent to it, and with no failures it sends packets from 1 and from 3 both to 1. That
    map is not a bijection of its live links, so it is no cyclic ordering. We formalize "routes in a
    cyclic ordering" as `RoutesCyclically σ A`: `σ` is a bijection of `A` onto itself and every
    element of `A` reaches every other by iterating `σ`. This is equivalent to the paper's
    `v_1 → v_2 → … → v_m → v_1` for `m ≥ 1`. The paper's proof assumes that the neighbours outside
    the "smaller cyclic ordering" can be given their own routes to `d`; dead ends and `d` itself
    break this. Its first step, "then `f_i` must have a smaller cyclic ordering", also ignores
    non-injective maps and drops.
15. **Instance used in Theorem 4.3** (`Fig3.exists_cycle`). For node 1 of Figure 3 with its four
    links up, the forwarding function is a 4-cycle on `{2, 3, 4, 5}`. For each neighbour `w` of node
    1 the proof uses the scenario where only the links of 1 and the path `w – m – d` survive
    (`Fig3.closed_false`). It then checks the 4⁴ possible tables of node 1.

## Theorem 4.3

16. **Network.** We read Figure 3 as 12 nodes and 22 links: `1` adjacent to `2, 3, 4, 5`, and a node
    for each pair of `{2, 3, 4, 5}` adjacent to that pair and to `d`: `6:{2,3}`, `7:{3,4}`,
    `8:{4,5}`, `9:{5,2}`, `10:{2,4}`, `11:{3,5}`. This matches the bold and dotted links of the
    figure. The network is connected (`Fig3.connected`).
17. **Proof gap repaired.** The paper uses one failure scenario (bold links) and Lemma 4.1 for node 2
    ("packets sent `1 → 2` must not loop back"). In that scenario every path from 2 to `d` passes
    through node 1. The stated Lemma 4.1 applies (the path `2, 10, 4, 1, 3, 11, d` avoids the edge
    `21`), but it is false; the corrected Lemma 4.1 does not apply. A SAT check
    (`satcheck/scenarios.py`) finds one pattern that satisfies conditions (1) and (2) in all
    scenarios the paper's proof uses: the four cyclic-ordering scenarios (those of
    `Fig3.closed_false`; the paper leaves the other links of these scenarios unspecified) and the
    Figure 3 scenario for each of the six cycles. So the written argument does not prove the theorem. We add, for each cycle
    `5 ↦ a ↦ b ↦ c ↦ 5` of node 1 (with `X = mid(a,c)`, `Y = mid(b,5)`), three scenarios with the
    same local views as the Figure 3 scenario: `1 – a – X – d`, `a – X – c – mid(c,5) – d` and
    `X – c – 1 – b – Y – d`. They force `a`, `X` and `c` to pass packets along (`pass_through`).
    Then node 5 has no forwarding path to `d` in the Figure 3 scenario (`Fig3.final_false`).
18. **"By symmetry, w.l.o.g. the ordering is 2, 3, 4, 5."** We handle all six 4-cycles explicitly;
    the scenario of Figure 3 is adapted to each cycle.
19. **Stronger statement.** The proof uses only condition (1). So on this network not even "every node
    connected to `d` has some forwarding path to `d`" can hold in all scenarios, loops or not. The
    proof uses `adj_next` (outputs are incident links) only to know that node 1 permutes its
    neighbours.

## Typos

20. Lemma 4.1's proof: "sends it back to `i`" should be "to `v`". Lemma 4.2: "in figure ??".
    Theorem 4.3: "figure (c)" means Figure 3. Case II: "iteration `q_1` of Step 2" should be Step 4,
    and "let `R_1 = (j_1, α, β, i_1)` be the route `R` selected at iteration `q`" should say `q_1`.
    The introduction says "starting with arbitrary loop-free routing tables" while §3 starts from an
    arbitrary DAG orientation.
