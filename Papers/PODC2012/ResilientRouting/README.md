# On the Resilience of Routing Tables — PODC 2012

Joan Feigenbaum, Brighten Godfrey, Aurojit Panda, Michael Schapira, Scott Shenker, Ankit Singla.
*Brief announcement: On the resilience of routing tables.* PODC 2012. DOI
[10.1145/2332432.2332478](https://doi.org/10.1145/2332432.2332478). Formalized version: arXiv
[1207.3732](https://arxiv.org/abs/1207.3732) v2 (full version); numbering follows it.

**Verdict: ❌ False claim.** Both theorems hold. Theorem 3.1 says every (connected) network
has a 1-resilient forwarding pattern. Theorem 4.3 says some network has no perfectly resilient
one; the Figure 3 network is indeed such a network. But both lemmas behind Theorem 4.3 are false
as stated, and its proof applies Lemma 4.1 where it does not hold. The algorithm of §3.2 is too
under-specified to verify. We prove Theorem 3.1 with a different construction and repair the
proof of Theorem 4.3.

## Mistakes in the paper

* **Lemma 4.2 is false.** It claims that every node in `d`'s component routes along a cyclic
  ordering of its live links. Counterexample: the path `d – 1 – 2 – 3` with no failures, where
  every node forwards to its neighbour closer to `d`. This pattern is perfectly resilient, yet
  node 2 sends packets from 1 and from 3 both to 1. The proof assumes that every neighbour of the
  node has its own route to `d`; dead ends and links to `d` break this. Theorem 4.3 needs the
  lemma only for node 1 of Figure 3 with all four of its links up. We prove that instance:
  node 1 permutes `{2,3,4,5}` in one 4-cycle. (`lemma_4_2_false`, `Fig3.exists_cycle`)
* **Lemma 4.1 is false as stated, and the proof of Theorem 4.3 misuses it.** The lemma: if `v`
  has a working path to `d` that avoids the *edge* `vu`, then `v` must not send packets travelling
  `u → v` back to `u`. The proof fails all other links of `u`, so it needs a path that avoids the
  *node* `u`. Counterexample: `d – 1` plus the triangle `1, 2, 3`, where every node forwards to 1
  and node 1 forwards to `d`. This pattern is perfectly resilient. Node 2 has the path
  `2, 3, 1, d`, which avoids edge `21`, yet it sends packets from 1 back to 1. The proof of
  Theorem 4.3 applies the lemma to node 2 in the Figure 3 scenario. There every path from 2 to `d`
  passes through node 1, so only the false literal statement applies; the corrected lemma says
  nothing. In fact, the paper's other ingredients do not suffice: one pattern is good in the four
  scenarios that force node 1 to route cyclically (those of `Fig3.closed_false`) and in the
  Figure 3 scenario of each of the six possible cycles. A SAT check (`satcheck/`, not part of the
  Lean development) finds it. So the written proof is incomplete, though Theorem 4.3 is
  true. We prove the corrected Lemma 4.1 (`v` reaches `d` after the other links of `u` fail). We
  then add three scenarios with the same local views. They force node 2 to pass packets from 1
  on to 10, node 10 to pass packets from 2 on to 4, and node 4 to pass packets from 10 on to 1.
  For the other five 4-cycles of node 1 we use the matching scenarios. Then the packet of node 5
  loops `5 → 1 → 2 → 10 → 4 → 1 → 5 → …`, as the paper says. Only condition (1) is used, so even
  "every connected node has *some* forwarding path to `d`" is impossible on this network.
  (`lemma_4_1_false`, `lemma_4_1`, `pass_through`, `Fig3.theorem_4_3`)
* **The algorithm of §3.2.1 is not well defined, and the proof of Theorem 3.1 is only a sketch.**
  Some steps are ambiguous or wrong:
  - Step 1 makes the forwarding functions partial (`∅`), but the model requires total functions.
  - In Step 3, `T` is the set of *failed* links (it says "the highest element of `E^i_D` not in
    `T`"), while the model's second argument is the set of *live* links. The condition
    "`T ∩ E^i_D ≠ ∅`" should say that some outgoing DAG link is up.
  - Steps 4e–4f drop the failure-set argument, so it is unclear for which failure sets the new
    rules apply.
  - The loop of Step 4e starts at `c = k−1`, so it never installs a rule at `i = v_k` itself.
  - The proof of Claim 3.2 takes a route "not in `D`", but every edge is in `D`.
  - Case II of the correctness proof is argued on a picture (Figure 2).
  - Nodes connected to `d` only through bridges are never handled. Neither is condition (2)
    (no forwarding loops) in components cut off from `d`.

  We did not formalize this algorithm. Theorem 3.1 itself is true; we prove it with a simple
  construction from a rooted spanning tree (see below). (`theorem_3_1`)
* **Degenerate readings of the model.**
  - *The destination must be a sink.* The definition of a forwarding path constrains only nodes
    `i ∈ [n]`, so taken literally a path may go on after reaching `d`. Then on the network `d – 1`
    with no failures, `d, 1, d, 1` is a forwarding loop, and no pattern is even 0-resilient on any
    network where `d` has a link. We let paths stop at `d`. (`literal_K2`)
  - *The network must be connected.* "For every network" in Theorem 3.1 fails if a component
    without `d` has a link: with no failures, packets there bounce forever. (`theorem_3_1_disconnected`)
* **Typos and slips.** Lemma 4.1's proof says "sends it back to `i`" (should be `v`). Lemma 4.2
  cites "figure ??", and Theorem 4.3 cites "figure (c)" (both mean Figure 3). The Case II proof says "iteration `q₁` of
  Step 2" (should be Step 4) and uses "`i_1 <_D γ`" without defining γ's role. Claim 3.2 and Step
  4b write "`i ⋬_D x`" without saying it means `x` is not above `i`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`).
* A static simple graph `G` and a destination `d`. A forwarding pattern gives each node `i` a total
  function `next i A u`. Here `A` is the set of neighbours of `i` over live links (the paper's
  `E_i \ F`), `u` is the neighbour the packet came from, and the result is a neighbour of `i`
  (`adj_next`; the paper's `f_i : E_i × 2^{E_i} → E_i`). If the result is a failed link, the
  packet is lost. Forwarding is deterministic and uses no packet-header bits.
* A failure scenario is any set `F` of edges. A forwarding path is a walk in `G \ F` that follows
  `next` at every interior vertex, and interior vertices are not `d`. The first hop is free, as in
  the paper.
* `Good G d f F` holds when (1) every node `i ≠ d` connected to `d` in `G \ F` has a forwarding path
  to `d`, and (2) no forwarding path repeats a directed link (the paper's loop notion, §4).
  A pattern is `t`-resilient (`IsResilient`) if it is good for all `F ⊆ E` with `|F| ≤ t`, and
  perfectly resilient if it is good for all `F ⊆ E`.
* Proof tools: a forwarding path is a prefix of the deterministic trajectory of its first link. So
  condition (2) follows from termination of all trajectories (`good_of`). A set of directed links
  that avoids `d` and is closed under forwarding refutes condition (1) (`not_good_of_trap`).

**Theorem 3.1, our construction** (`Theorem31.lean`). We take any spanning tree rooted at `d`; the
theorem uses a BFS tree from CSLib. An *exit* of a subtree is a non-tree link leaving one of its
nodes. Its value is the depth of the lowest common ancestor of its endpoints, and it leaves the
subtree of `u` iff its value is `< depth u`. Each node fixes a minimum-value exit of its subtree
and an *escape hop* towards it.
* A packet from the parent goes to the escape hop if that link is up, otherwise back to the parent.
* Any other packet goes to the parent if that link is up. Otherwise it goes to the escape hop if
  the parent link is not a bridge, and is dropped if it is.

When the parent link of `u` fails, a packet reaching `u` follows escape hops down the subtree of
`u`. All minimal exits on the way have the same value, so it leaves the subtree and then climbs to
`d` on a path that avoids the failure. Our result is stronger than the paper's 1-resilience: with
at most one failure, *every* packet in `d`'s component is delivered, whatever its first hop.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3.1 (1-resilient pattern exists; connected network) | `theorem_3_1` (any rooted spanning tree: `OneResilient.pattern_isResilient`) | `Theorem31.lean` |
| Theorem 3.1 for disconnected networks: **false** | `Counterexamples.theorem_3_1_disconnected` | `Counterexamples.lean` |
| Lemma 4.1 as stated: **false** | `Counterexamples.lemma_4_1_false` | `Counterexamples.lean` |
| Lemma 4.1, corrected hypothesis | `lemma_4_1` (core: `lemma_4_1_core`, `pass_through`) | `Lemma41.lean` |
| Lemma 4.2: **false** | `Counterexamples.lemma_4_2_false` | `Counterexamples.lean` |
| Lemma 4.2 for node 1 of Figure 3 | `Fig3.exists_cycle` (via `Fig3.closed_false`) | `Theorem43.lean` |
| Theorem 4.3 (Figure 3 has no perfectly resilient pattern) | `theorem_4_3`, `Fig3.theorem_4_3` | `Theorem43.lean` |
| Figure 3 network (connected) | `Fig3.G`, `Fig3.connected` | `Fig3.lean` |
| Literal definition (no sink at `d`) | `Counterexamples.literal_K2` | `Counterexamples.lean` |

**Not formalized.** The algorithm of §3.2.1 and the polynomial running time in Theorem 3.1. Our
construction (BFS tree, depths of lowest common ancestors, minimum exits) is clearly polynomial,
but there is no complexity model.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Finite checks on the 12-node network use `decide`. The counterexamples to the lemmas
exhibit perfectly resilient patterns, which also shows that the hypotheses of `lemma_4_1` and
`theorem_4_3` can be satisfied in general. [`satcheck/`](satcheck/) holds the SAT encoding
(python-sat) used to find the scenario set of the proof and to check the claim about the paper's
scenarios; it is not part of the Lean development. Only the CSLib rooted/BFS trees
(`Cslib/Foundations/Combinatorics/SimpleGraph/{RootedTree,BFSTree}.lean`) are reused. CSLib
candidate: the forwarding model and trajectory tools of `Model.lean` (static fast-failover routing).
