# Differences between the formalization and the paper

Paper: Austin, Gadouleau, Mertzios, Trehan, *Amnesiac Flooding: Easy to break, hard to escape*,
arXiv 2502.06001v2 (full version of the PODC 2025 brief announcement). Numbering follows the arXiv version.

## Model and definitions

1. **Graphs.** The paper assumes finite connected graphs with at least two nodes. We assume `Fintype V` where
   termination is concerned, and `G.Connected` only in Theorem 5.6 (broadcast part), where it is needed.
   Everything else holds for arbitrary (finite) graphs.
2. **Configurations** (Definition 3.1) are `Set (V × V)`. Results about termination assume `IsConfig G S`
   (messages travel along edges), as the paper does.
3. **Definition 5.4 (balance).** "For all subgraphs `H` that are cycles or FECs" is formalized via closed
   walks:
   * every `c : G.Walk u u` with `c.IsCycle` (each cycle subgraph is the support of such walks, with any base
     point and orientation);
   * every `F : FEC G` with `F.walk = c₁ ++ p ++ c₂ ++ p⁻¹` (any junction and orientation).
   
   The FEC structure requires:
   * the two odd cycles share only the junction vertex when `p` is trivial, and are vertex-disjoint otherwise;
   * the path `p` meets the cycles only at its ends.
   
   Quantifying over all base points and orientations is harmless:
   * balance along a closed walk is invariant under rotation and reversal;
   * for FECs, the alternating-occupancy part does not depend on the orientation of the cycles, and the flow
     part follows from the odd-cycle conditions (`Balanced ↔ BalancedAll`, `balancedAll_iff_balanced`).
4. **Balance on one walk** (`BalancedOn`). For every position `k₀`, the clockwise minus anticlockwise
   messages whose heads (senders) are at positions `k₀ + 2i` cancel.
   * Odd length: this is exactly "as many messages each way" (`balancedOn_iff_of_odd`).
   * Even length: it is the paper's "for any message `m`, equally many each way among messages whose heads
     are at even distance from `m`'s". We also require it for parity classes with no message, where it holds
     trivially.
   * The paper's `S^{2,H}` on `H²` (Definition 5.3) is exactly the pull-back of `S` along `F.walk`. The
     paper's case-by-case list (messages at `a₀`/`a₋₁`, duplicated path messages) is what the pull-back
     produces.
5. **Theorem 5.1** is stated as `(∃ k, A_∅^k(S) = ∅) ↔ Balanced G S` for configurations on a finite graph.
   **Corollary 5.1.1** is `∃ k ≤ 2|E|, A_∅^k(S) = ∅`, with `|E| = #G.edgeFinset`.
6. **Theorem 5.5 (2)** is `∃ Is : List (Set V), runFrom G Is ∅ = S` (apply `A_{I_1}` first). `k = 0` is
   allowed and gives `S = ∅`.
7. **Lemma 5.2.**
   * The printed `T` (the sinks of `S`) is replaced by the proof's `T`: the sinks of `S̄`, i.e. the nodes
     sending to all their neighbours in `S` (`sources`). The printed version is refuted
     (`lemma_5_2_as_stated_false`).
   * Isolated nodes belong to `sources` vacuously; this is harmless.
8. **Lemma 5.4 and Lemma A.1** are proved for `Balanced` (and for each closed walk). Lemma A.1 is for every
   initiator set `I`.

## Proofs

9. **Appendix A is not followed.** The invariance direction (Lemma A.1) is as in the paper, for arbitrary
   closed walks: they become cycles with external activations, `ind_cw_step_sub`. The hard direction uses
   instead:
   * the front lemma `not_balancedOn_of_front`;
   * ancestor chains and pigeonhole on darts (`iterate_eq_empty_of_balancedAll`), which gives the `2|E|`
     bound directly;
   * the spanning theorems `walkFlow_eq_zero_of_isCycle` and `walkSig_eq_zero_of_isCycle_of_fec`.
   
   Lemmas A.2–A.15 are not formalized individually.
10. **Theorem 5.5.** The paper proves (2) ⇒ (1) via the literature's Theorem 2.1, and uses balance for
    (1) ⇒ (2). We derive Theorem 2.1 itself (`theorem_2_1`, `lemma_3_1`) from the dichotomy.
11. **Theorem 2.1 / Lemma 3.1** are cited from the literature in the paper. Here they are proved
    (multicast with arbitrary sequences of initiator sets).

## Fault models (Section 5.2.2)

12. **Indexing.** The paper writes `S_{k+1} = A(S_k) \ T` with `k ≥ 1` (message dropping), and
    `∀ i ≥ 1, S_{i+1} = A(S_i) \ X` (link failures). This lets the first-round messages (and, read
    literally, the second-round ones) escape the fault. With the literal reading, the second claim of
    Theorem 5.7 fails on a single edge: the initiator's message crosses the failed link. We let faults act
    from the first round on:
    * `dropRun` drops `m ∈ srcRun G s k` for any `k ≥ 0`;
    * `uniRun` removes `X` in every round, including the initiators' round.
13. **Message dropping.** "The message `(u, v)`" is a message actually sent (`(u,v) ∈ srcRun G s k`).
    * "Not a bridge" is Mathlib's `¬ G.IsBridge s(u,v)`.
    * "`uv` lies on a path between odd cycles" is `∃ F : FEC G, s(u,v) ∈ F.p.edges`, the path of a
      faux-even cycle.
    * "First message sent along `uv`" means that no message used `uv` in either direction in an earlier
      round.
    * "Fails to broadcast" means that some node other than `s` never receives a message.
    * "The side of the cut containing `u` does not contain an odd cycle" is `¬ SideHasOddCycle`: no odd
      cycle of `G` all of whose vertices are reachable from `u` in `G − uv`.
14. **Uni-directional failures.** `X` is a set of directed links failing in every round.
    * The second claim of Theorem 5.7 needs, and we assume, that `X` is nonempty, consists of directed
      edges, and that no edge fails in both directions. If an edge on a cycle fails in both directions, it
      simply disappears, and flooding can succeed.
    * The first claim is proved for one initiator (`theorem_5_7_singleton`; the failed link is at the
      initiator) and refuted for `I = {0, 2}` on a path (`theorem_5_7_multi_false`).
    * "Fail to terminate" is `∀ t, uniRun t ≠ ∅`. "Fail to broadcast" is: some non-initiator never
      receives a message.
15. **Weak-Byzantine nodes.** `byzRun G I J k B`:
    * before round `k`, the honest messages are those of `A`, and the `J`-sent messages are an arbitrary
      `B t` restricted to edges; from round `k` on, everybody follows the protocol;
    * `k ≥ k₀` is chosen by the adversary (the paper fixes `k₀` = twice the diameter; our results hold for
      every `k₀`);
    * Byzantine nodes may also send in the first round.
    
    The statements:
    * Non-termination is "not eventually quiet" (`¬ EventuallyQuiet`). "Lies on a cycle or a path between
      odd cycles" is `OnCycleOrOddPath`: on the support of a cycle, or of the path of an FEC.
    * Theorem 5.8 (non-termination) is proved as stated, as an iff, assuming `I ∩ J = ∅`.
    * Theorem 5.8 (broadcast) is false; see the README. The corrected statement (`theorem_5_8_broadcast`)
      counts failures among honest non-initiators, and reads "some honest node is unreachable from every
      initiator in `G − J`" instead of "`J` contains a cut vertex set". It needs no disjointness of `I`
      and `J`: initiators in `J` are treated as Byzantine.
    * If failure is counted over all nodes (Byzantine ones included), the paper's "only if" direction fails
      instead, even for one initiator, in a degenerate way: on the path `s – u – b` with `J = {b}` (a leaf, no cut
      set), `b` sends to `u` in round 1, so `u` never forwards to `b` and `b` is never informed. (Not
      formalized; noted by the reviewer.)
16. **Theorem 5.6** is proved in two parts: non-termination ("if", as stated) and broadcast ("iff", on a
    connected graph). Brute force suggests the non-termination part is an "iff"; we did not formalize the
    converse.

## Not formalized

17. **Section 4.**
    * Theorem 4.1 (uniqueness): Definition 4.1 is under-specified (what labels and graphs range over, how
      `b` is used at non-initiators), and the proof relies on Ramsey numbers, many gadget graphs and an
      "exhaustive search".
    * Theorem 4.2 / Appendix C.
    
    Only one item is formalized: the Random Flooding window argument of Proposition C.2 is refuted on the
    5-cycle (`random_flooding_window_false`; Random Flooding as `rfStep`, a node with bit `1` forwarding to
    all neighbours). Parrot Flooding (Lemma C.3) was checked by brute force only. Neighbourhood-2 Flooding
    (Proposition C.1) is elementary and was not formalized.
18. **PODC-version statements.**
    * The bound `2|E| − 3` is refuted on the path with two edges (`podc_bound_false`); we prove the arXiv
      bound `2|E|`.
    * The PODC "consequences" (1)–(3) are not formalized separately: (1) and (2) follow from Theorem 5.6;
      (3) is refuted by the same path example as Theorem 5.8 (described in words).
