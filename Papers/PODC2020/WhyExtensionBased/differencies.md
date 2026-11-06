# Differences between the formalization and the paper

Paper: Alistarh, Aspnes, Ellen, Gelashvili, Zhu, *Why extension-based proofs fail*, arXiv 1811.01421v3
(full version of the PODC 2020 brief announcement; NIS model).

## Statements

1. **Theorem 5.7** (`theorem_5_7`): stated exactly for `n > k ≥ 2` processes `Fin n` and inputs
   `Fin (k+1) = {0,…,k}`. The general form `not_hasEBProof_setAgreement` holds for any finite set of
   processes and any finite, nonempty input set; `n > k` is not needed (for `n ≤ k` the task is
   solvable anyway). **Both are weaker than the paper's Theorem 5.7** in one respect: the class of
   provers is smaller (item 8, interleaved infinite chains). The Lean theorem does not formally
   imply the paper's. The restriction leaves part of Theorem 5.7 unchecked but shows nothing false.
   It is stated in the README's verdict paragraph and table.
2. **Lemmas 4.11, 4.13** are proved in a "carrier" form (`Far.subdiv`, `Far.subdiv_succ`). This form
   is more general than the paper's: the sets `A`, `B` need not be unions of cliques or sets of
   terminated vertices, only "carrier-closed" (every carrier of a vertex of `A'` lies in `A`). The
   paper's hypothesis "every path contains an edge between active vertices" is used as stated
   (`ActCut`).
3. **Lemma 5.4** (`actCut_T`): stated for `U(a)` (vertices that have not seen `a`) instead of
   `N_t(a)`. By the paper's Lemma 5.3 these are the same vertex sets, so the statements are equivalent.
4. **Lemma 5.5** (`subdiv_far`, `AInv.subdiv`): the distance part is proved for any distances
   `d₄ ≥ 2`, `d₅ ≥ 3` (each grows by one). The invariant part is proved for **our** invariants
   (`AInv`), which replace invariant 6 (see below). The claim "invariant 6 remains true" is part of
   the adversary's correctness argument. We neither prove nor refute it for the paper's invariant 6.
   It is a proof gap of Theorem 5.7 (🛠️). Nothing here is shown wrong. The literal definition of
   `X_t(a)` (all levels `≤ t`) does make invariant 6 fail for active vertices of lower levels. But
   that inconsistency is in a definition, the strategy text shows the intent (item 18), and the
   literal invariants hold in no non-trivial run, so it is not a refutation of the lemma. If
   someone showed that the intended invariant 6 can actually fail after a subdivision, Lemma 5.5
   would be a false numbered lemma, with Theorem 5.7 still true. A candidate scenario, based on
   README proof gap 1: `n = 3`, a Case-3 vertex `u`, and a descendant `(i, {u, x_k})` with no clique
   containing it and a terminated vertex. We did not construct it.
5. **Lemma 5.6** (`IsChain.false`): proved for chains of *consecutive* queries in phase 1 (see Model,
   winning condition).
6. **Lemma 5.3, Lemmas 4.4–4.10, Corollary 4.9** are not formalized: connectivity is not needed and
   the graph `G_t` is defined semantically. Lemma 4.10 is subsumed by the carrier form of 4.11.
7. **Section 3** (the valency proof of the impossibility of consensus is extension-based): not
   formalized.

## Model

8. **NIS model and game**: reused from `Podc/Computability/Distributed/NIS/{Model,Game}.lean` (staged
   by the PODC'21 companion). Differences from §2–§3:
   * a configuration is the vector of full-information states (Observation 4.1);
   * output queries `(C, Q, y)` may name any set `Q` of processes. The paper requires `Q` active in
     `C`, so ours is more power for the prover and the theorem only gets stronger;
   * the prover "loses at the start of phase `φ`" if all configurations of `A(φ)` are final and
     correct. We have no such rule; such a prover can only make oracle moves forever and does not
     win, so this is equivalent;
   * **winning by an infinite chain**: the prover wins if *from some point on every move* is a query
     from the configuration returned by the previous query. The paper also counts a prover that
     interleaves several chains (finitely many) of which one is infinite. Our theorem does not cover
     such provers. The argument extends: each chain terminates at most `n` processes, so the adversary's
     protocol is still eventually constant, and the rest of Lemma 5.6 applies to every infinite chain.
     It is not formalized, because it needs a different winning condition in the shared game.
     A faithful condition W3' would read: from some index on, all moves are queries, and they are
     labelled by finitely many chain labels so that consecutive moves with the same label are linked.
     Proving `not_wins` for W3' would require generalising `IsChain`, which now requires
     `A (k+1) = qstep (A k) (C k) (q k)`, to adversary states that also change through the other
     chains' queries. That only adds finitely many terminations and more subdivisions.
9. **Graphs `G_r`** (`Adj`, `Vtx` in `Layers.lean`): two states are adjacent if they belong to
   different processes and occur together in some *reachable* configuration. The paper requires an
   `r`-round configuration. The two agree by truncation (`Reach.trunc`), which is all we use; we do
   not prove that our graph equals `χ^r(G_0)`.
10. **`N_t(a)`** is replaced by `Uset` (vertices of `G_t` that have not seen `a`), and **`T_t(a)`** by
    `Tset`. Both are restricted to vertices occurring in reachable configurations.
11. **Partial protocol**: the adversary stores only the terminations decided so far (`AState.term`). A
    state with fewer than `t` rounds that is not terminated is "decided ⊥". Undecided states are
    treated as active, so subdividing does not change the protocol, only `t`.

## Adversary (proof repairs)

12. **Output queries** (`oq`, `OutputQuery.lean`): replaces the paper's three cases.
    * **(S)** If a `Q`-descendant of `C` has already output `y`, return a schedule to it, restricted
      to its causal past (`exists_sched_restrict`). The paper returns "a `Q`-only schedule from `C`
      that leads to `v`"; a schedule passing through undecided states could later become invalid.
    * **(U)** Otherwise, if some undecided `Q`-descendant with `≥ t` rounds is unprotected, let its
      process run alone until no other process has written to the next object, subdivide, and
      terminate the next state. The paper subdivides once and terminates `(i, {u})`; this schedule
      exists for the paper's adversary only by an unstated invariant (no process has written to
      `S_{t+1}` in a reached configuration); in our model undecided states are active, so it can
      fail and we use a solo run (README, slips).
    * **(N)** Otherwise answer `none`. Descendants are considered at **all** levels, in the protocol
      where undecided states are active. The paper uses only `Q` ∩ `G_t` and Case 3 (README, proof
      gap 1).
    * `oq` actually picks *any* good reaction (`OQGood`) when one exists; (S) and (U) show that one
      exists in their cases.
13. **Invariant 6** is replaced by `RecOK`. For every recorded `none` query, no `Q`-descendant has
    output `y`, and every undecided descendant with `≥ t` rounds is protected: it has not seen `y`,
    or it is adjacent (in its own layer) to a vertex terminated with a value `≠ y`. Preservation under
    terminations uses `adj_transfer` (edges survive when more states are terminated, by restricting to
    a causal past).
14. **Query rule** (`qstep`): as in the paper ("if there is an input `a` such that setting `δ(s') = a`
    maintains all invariants"), with the explicit safety condition `Safe`: distance `≥ 2` to `U(a)`
    and `≥ 3` to every other `T(b)`. Our invariants then make the paper's argument "`s' ∉ X_t(a)`"
    automatic.
15. **Phase 2** (`dstar`): after one more subdivision, every undecided state with `t + 1` rounds
    outputs `b` if it is adjacent to a vertex terminated with `b`, otherwise `a` if it has seen `a`
    (the input of the first process of `α(2)`), otherwise it stays active. The paper defines values
    only on `F'`. Ours is the same on `F'`, and the extra values are never reached by the prover. The
    paper does not say what happens to the undefined vertices outside `F'`; we leave them active.
16. **Final protocol**: when phase 1 ends we fix `dstar`. When the prover moves illegally we fix the
    current partial protocol. When phase 1 never ends, the protocol is the limit of the partial
    protocols (`limTerm`).
17. **Lemma 5.6**: the common seen input of the layer `Σ` is the input of the process with the
    smallest view of `S_r` (`common_seen`), not of "the first process to scan `S_{t'+2}`".
    Equivalent; ours needs no reasoning about the order of steps.

## Paper slips (no influence on the result)

18. ✏️ `X_t(a)` is defined over all levels `V_r`, `r ≤ t`, but invariant 6 and the strategy treat it as
    a set of vertices of `G_t`.
19. Lemma 5.5's proof: `χ(N_t(a), Δ)` for `χ(N_t(a), δ)`, and `χ(T_t(t), δ)` for `χ(T_t(a), δ)`.
20. ✏️ Case 1 uses "each vertex in `X_t(y)` is adjacent to a vertex in `T_t(b)`" and drops invariant 6's
    alternative `v ∈ N_t(y)`. This is harmless, since `T_t(y)` is far from `N_t(y)`.
