# Differences between the formalization and the paper

Paper: Ghaffari, Kantor, Lynch, Newport, *Multi-Message Broadcast with Abstract MAC Layers and Unreliable Links*,
PODC 2014, arXiv:1405.1671v1 (numbering of the arXiv version).

## Model

1. **One transition system instead of composed timed I/O automata.** BMMB and the MAC layer are modelled together
   (`step`). User well-formedness (one broadcast at a time) and BMMB's zero-delay `bcast` are built in: the message
   being broadcast is always the head of the queue.
2. **BMMB state.** `log i` is the list of messages `i` got, in order. It plays the role of `rcvd` and of the order of
   `bcastq`. `acks i` counts acknowledged broadcasts. Then `bcastq = log.drop acks`, `R_i = log`,
   `C_i = log.take acks`, and the "sent set" of §3.1 is `C_i`.
3. **Cause function.** It is implicit. A message instance is identified by `(sender, message)`, which is sound because
   BMMB broadcasts each message at most once per node (`Inv.nodup`). `heard v` records the receive events at `v`.
4. **Receive and acknowledgment correctness** are enforced by the guards of `step`:
   * `rcv u v` needs `G'.Adj u v` and that `v` did not receive this instance before. It happens only before the
     instance's ack.
   * `ack u` needs every `G`-neighbour to have received the instance.

   Disabled events are no-ops, so every event sequence is an execution.
5. **No aborts, no `ε_abort`, no crashes** (standard model; BMMB never aborts). The enhanced model is not modelled.
6. **Time.**
   * Event `n` happens at real time `T (n+1)`, with `T 0 = 0`, `T` monotone and `T → ∞` (admissibility).
   * Trajectories are not modelled: states only change at events.
   * The final state at time `t` is configuration `last t`, the last one with `T n ≤ t`.
   * `F_ack, F_prog ≥ 0` is assumed (the paper says positive).
7. **Acknowledgment bound** (`AckBound`). Every broadcast is acknowledged at most `F_ack` after the configuration in
   which it starts (`Fresh`). This includes the termination property.
8. **Progress bound** (`ProgBound`). It is required only for closed fragments from the final state at a time `t ≥ 0`
   to the final state at a time `t' > t + F_prog`. The paper requires it for every closed fragment. These are the only
   fragments used by the proofs (Lemmas 3.9, 3.10), and the weaker hypothesis makes the theorems stronger.
   * `connect(α', j)`: instances of `G`-neighbours of `j` that started by the first state and are not acknowledged
     by the last state.
   * `contend(α', j)`: instances of `G'`-neighbours not acknowledged by the first state.
   * Condition (c) counts receive events *by the end* of the fragment, including those before it, exactly as in the
     paper.
9. **Arrivals.** `arrive i m` can happen at any time. BMMB delivers `m` and appends it to the queue *only if
   `m ∉ rcvd`*. The paper's pseudocode does not check `rcvd` on `arrive`; the two coincide in MMB-well-formed
   executions, and we do not assume MMB-well-formedness at all.
10. **Nodes and messages** are arbitrary types (`V` need not be finite; ids are irrelevant for BMMB). There is no
    bound on the message size: each broadcast carries one MMB message, as in BMMB.
11. **The topology assumption `G ≤ G'`** is a hypothesis of Lemmas 3.3, 3.9, 3.10 and the `r`-restricted results
    only. Theorems 3.1 and 3.4 hold for any `G'`.
12. **`r`-restricted** (`RRestricted G G' r`): every `G'` edge `{u, v}` has `G.edist u v ≤ r`.
    `N^z_G(j) = {j' | G.edist j j' ≤ z}`. Distances use Mathlib's `edist`/`dist`. "`v` at distance `d` from `u`" is
    `G.edist u v = d`, which implies reachability.

## Problem statement

13. **MMB specification** (`SolvesMMB`).
    * (a) Every message that arrives at `i` is delivered at every node of `i`'s connected component of `G`. §3.2.2
      says "every process `j`"; we follow §2, which does not assume `G` connected.
    * (b) At most one `deliver(m)_j` per node and message, and it comes no earlier than some `arrive(m)_i` event (the
      same event when `i = j`).
14. **Time bounds.**
    * As in §3.1 and §3.2.3, all `arrive` events happen at time `0` (`ArrivalsAtZero`).
    * "`k` messages": the arriving messages lie in a `Finset K` with `#K ≤ k`.
    * `k` is not known to the algorithm (BMMB does not use it).

## Statements

15. **Theorem 3.4** (`theorem_3_4`) is proved for online arrivals. It assumes only the acknowledgment bound: nothing
    about `G'` and no progress bound.
16. **Theorem 3.1** (`theorem_3_1`, `theorem_3_1_diam`).
    * The explicit bound is: `v` has *acknowledged* (hence received) `m` by `(d_G(u, v) + k) F_ack`.
    * The diameter form gives `(D + k) F_ack` for every `v` within distance `D` of `u` in `G`.
    * No assumption on `G'` or `F_prog` is needed.
17. **Theorem 3.1, proof.** The key claim (`theorem_3_1_key`) is "`m ∈ C_v((d+ℓ) F_ack)` or `|C_v((d+ℓ) F_ack)| ≥ ℓ`"
    for all `ℓ ≥ 0`. "Contains `ℓ` other messages" is replaced by `|C_v| ≥ ℓ` when `m ∉ C_v`. The paper's base case
    `h = 0` is vacuous for `ℓ ≥ 1`; we start at `ℓ = 0`.
    * The induction is on `ℓ` (outer) and `d` (inner), equivalent to the paper's induction on `h = d + ℓ`.
    * The `d = 0` case is the queue argument (`mem_C_or_le_card`).
18. **Lemma 3.5** holds for all real `t ≤ t'` (no `t ≥ 0` needed). Part 3 is stated for `G`-neighbours `i, i'`.
19. **Lemma 3.6** is stated as an equality of `Finset`s plus `Nodup` of the queue.
20. **Lemma 3.7**, part 1: positions are 1-based (`queue[k-1]? = some m'`).
21. **Lemma 3.9** is derived from Lemma 3.10 (footnote 9 of the paper notes this).
22. **Lemma 3.10** needs `G ≤ G'`. Its hypothesis 1 is applied to `j`, which is a `G'`-neighbour of `i` only because
    `G ⊆ G'`.
23. **Lemma 3.11** is stated with an explicit `ℓ > 0`. The "closest `j″`" in the proof is not needed: any `j″ ≠ j`
    with `|R_{j″}| ≥ ℓ` works.
24. **Lemma 3.12.**
    * **`t_{d,ℓ}` is not defined in the paper.** We define `tdl r F_prog F_ack d ℓ = d F_prog + (ℓ−1)((r+1) F_prog +
      r F_ack)`. It has `t_{0,1} = 0` (used in Lemma 3.13) and `t_{D,k} ≤ t₁` (Theorem 3.16). The formula
      `(d + (r+1)ℓ − 2) F_prog + r(ℓ−1) F_ack` suggested by Theorem 3.16 has `t_{0,1} = (r−1) F_prog ≠ 0` for `r > 1`.
    * Parts 2 and 3 are stated with shifted indices: paper `ℓ` = ours `ℓ + 2`; paper `d ≥ 1` = ours `d + 1` in part
      3. Part 2 needs no `d ≥ 1`; part 3 needs `r ≥ 1` and `F_ack ≥ 0`.
    * **Part 5 is false** (`lemma_3_12_5_false`). It fails for every definition of `t_{d,ℓ}` that satisfies part 4
      and `t_{D,k} ≤ t₁` (`lemma_3_12_5_false_any`: `r = 1`, `k = ℓ = 2`, `F_prog = 1`, `F_ack = 3`), so the failure
      is not an artefact of our choice of `tdl`. We prove `(ℓ−1) F_ack ≤ t_{0,ℓ}` instead (`lemma_3_12_5'`, needs
      `r ≥ 1`). This is exactly what Lemma 3.14 uses.
    * Our increment `t_{0,ℓ+1} − t_{0,ℓ} = (r+1) F_prog + r F_ack` is not tailored: parts 2–4 force an increment
      `≥ max(r F_prog + r F_ack, (r+1) F_prog + F_ack)`, and with it `t_{D,k} = t₁ − (r−1) F_prog` (equal for `r = 1`).
25. **Lemma 3.13** is proved for our `t_{d,ℓ}`, with `t_{0,1} = 0` as in the paper. Part 2 follows from Lemma 3.7.3
    with `k = 1`.
26. **Lemma 3.14** needs `r ≥ 1` (through the repaired part 5).
27. **Lemma 3.15** follows the paper's double induction, with paper `ℓ ≥ 2` = ours `ℓ + 1` and paper `d ≥ 1` = ours
    `d + 1`. Typos repaired:
    * Case 1 derives `m′ ∈ R_{j*} \ C_{j*}` (the paper writes `j″`).
    * Case 2 cites Lemma 3.5, not 3.15.
28. **Theorem 3.16.**
    * `theorem_3_16` is the per-component statement: `m` reaches every `j` with `d_G(i₀, j) ≤ D` by `t₁`.
    * `theorem_3_16_connected` is the paper's statement `R_j(t₁) = K`, assuming `G` connected with all distances
      `≤ D`, and `K` the exact set of arriving messages. It is false for disconnected `G`.
29. **Theorem 3.2** (`theorem_3_2`) gives the explicit bound `D F_prog + 3 r k F_ack`, for every `j` within distance `D`
    of the source, with no relation between `F_prog` and `F_ack`. For `F_prog ≤ F_ack` it follows from Theorem 3.16.
    Otherwise it follows from Theorem 3.1. The paper's `t₁` alone is not `O(D F_prog + r k F_ack)` when
    `F_prog ≫ F_ack`.

## Not formalized

30. **§3.3 lower bounds** (Theorem 3.17, Lemmas 3.18–3.20). They need a model of arbitrary randomized algorithms, the
    message-size restriction and the grey-zone geometry. Informal observation, not checked in Lean: the proof of
    Lemma 3.20 assumes each broadcast carries a single MMB message.
    * With capacity `c ≥ 2`, node `b_{i+1}` learns `m₀` from the cross delivery of `a_i`'s broadcast.
    * Its later broadcast "containing `m₁`" can then carry `m₀` to `a_{i+2}` over a `G'` edge. The schedule breaks:
      against "send everything you know" it costs only `O(F_ack + D F_prog)`.
    * Repeated delivery of the same instance at the end of every `F_prog` sub-interval is also not allowed by receive
      correctness. This one is harmless: one delivery suffices, because condition (c) counts receive events before
      the fragment.
31. **§4** (enhanced abstract MAC layer, FMMB, the MIS/gather/overlay subroutines, Theorem 4.1) and the sphere packing
    Lemma 4.2.
