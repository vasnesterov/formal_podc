# Differences between the formalization and the paper

Paper: D. Sakavalas, L. Tseng, N. H. Vaidya, *Asynchronous Byzantine Approximate Consensus in
Directed Networks*, PODC 2020, arXiv 2004.09054v1 (the only version). Numbering follows it.

Classification: **[false]** false statement · **[degenerate]** false only in a degenerate case ·
**[gap]** proof gap, statement true · **[spec]** under-specified / inconsistent definition ·
**[typo]** · **[model]** modelling choice.

## Errors and gaps in the paper

1. **[spec] Inconsistent message-set definitions; both readings fail.**
   * *Paths stored by `v` end at `v`* (Definition 9). Definition 4 lets an `f`-cover be any set of
     at most `f` nodes, so `{v}` is an `f`-cover of every message set `v` holds (for `f ≥ 1`):
     * Algorithm 2 (`Completeness`) can never hold. Choose `Fw` with `v ∈ Fu ∪ Fw`; then
       `v ∉ S_{Fu,Fw}` and `H = {v} ⊆ V \ S_{Fu,Fw}` (`not_completenessLit`).
     * `Verify` therefore fails in every thread forever, because FIFO-Receive-All includes `v`'s
       own `COMPLETE(Fv)` (`RoundExec.never_verifyLit`). This is proved in the abstract round model,
       for every `RoundExec`, including the fault-free one on `K₄` with `f = 1`. It is not proved
       for an operational run of the literal algorithm.
     * Algorithm 3 trims the whole vector (`not_isFALit`).
   * *Paths end at the sender* (Appendix E). Then `ter(p) = v` never holds for a stored path, so no
     message set is full for `(A, v)` and Maximal-Consistency never fires (not formalized).

   The intent is evident from line 5 (`Fv ⊆ V \ {v}`), Eq. (1) in Lemma 8 (`F' ⊆ V \ S \ {v}`) and
   footnote 5: a node never suspects itself. Fix used throughout: paths end at `v`, and `v` is never
   in a cover. In Algorithm 2 this means `H ⊆ V \ (S_{Fu,Fw} ∪ {v})`; in Algorithm 3 it means
   `v ∉ F_lo, F_hi` (`CoverFor`).
2. **[typo] `(max − min)/2`** in Algorithm 3 line 5, in the proof of Lemma 15 and in Appendix G
   (`x_v[r+1] = (max O' − min O')/2`); it must be
   `(max + min)/2`. With `−`, a fault-free round where all inputs are `1` produces `0`
   (`minus_update_invalid`), which violates validity.
3. **[gap] The known input range is missing from the statements.** Section 4.6 states explicitly
   that the inputs lie in `[0, K]` for an a priori known `K`, and termination needs this. The
   assumption is missing only from Definition 1 and Theorem 4. So the sufficiency direction is proved only for a known input range. With a known range
   and `K ≤ ε` the problem is trivial. So the end-to-end characterization (`theorem4`) is stated
   for inputs in `[0, K]` with `0 < ε < K`. The necessity is proved both in that setting and for
   arbitrary real inputs (`threeReach_of_solvesOn`, `threeReach_of_solves`). Whether 3-reach
   suffices with unbounded inputs and no known bound is left open, as in the paper.
4. **[gap] Theorems 10, 11, 14: the case `F_lo = F_t` (and `f = 0`).** The common value sets
   `R_{Fw}` (Definition 12) are defined only for `Fw ≠ F_t`. Theorem 11 and the proof of
   Theorem 14 use `R_{F^z_lo}`, but the trimming cover `F^z_lo` may equal `F_t`. For `f = 0` the
   union in Theorem 10 is empty. The statements are true. When `H = F_t` we use any other
   `W ≠ F_t` (`F_t` is disjoint from `S_{F_t,W}`). When `Fv = Fu` we allow all `W`
   (`follower_witnessed`, `leader_witnessed`, `theorem10`).
5. **[spec] FIFO-Receive (Appendix F).** The paper says `v` FIFO-receives message `k` from `u` if
   it received messages `1..k−1` from `u`, along any path. Theorem 10 needs FIFO order along the
   specific path `p_{c,v}`: `v` must already hold the genuine `COMPLETE(Fu)` that `c` sent on
   that path. With "any path", a forged copy on a Byzantine path would do. We use per-path
   FIFO-receive: message `k` is accepted along `p` once `0..k−1` were received along `p`
   (`fifoCR`).
6. **[spec] Which `COMPLETE` messages `Verify` checks.** The proof of Lemma 8 and the discussion
   before Definition 11 consider the messages received "by the time the FIFO-Receive-All
   condition is satisfied". Algorithm 1 re-evaluates `Verify` on every receipt. We check all
   messages received so far, which is the literal algorithm. Lemma 8 then holds without the
   paper's extra hypotheses (`completeness_eventually`).
7. **[gap] Lemma 8, Case II.** "The `f+1` paths `p_1, …, p_{f+1}` trivially do not have an
   `f`-cover `H ⊆ V \ S`" is false: `H = {z}` covers all of them. The argument still works
   because the relevant cover `F'` does not contain `z`. Our proof is uniform: Theorem 5 is
   applied with `X = H` and gives a path `q ⇝ z` avoiding `Fu ∪ H` directly.
8. **[gap] Lemma 13 / Theorem 14 and ties.** The tie handling in Theorem 14 is informal ("at least
   one instance remains"). We avoid Lemma 13 and Theorem 14. Let `H_lo` be the cover trimmed at
   `v` and `H_hi` the cover trimmed at `u`. Theorem 12 gives
   `q ∈ S_{F_t,W(H_lo)} ∩ S_{F_t,W(H_hi)}`. Then `min O'_v ≤ x_q ≤ max O'_u`, and this is all
   Lemma 15 needs (`pair_le`). Theorem 14 itself (a common value in `O'_v ∩ O'_u`) is not
   formalized.
9. **[gap, minor] Theorem 18 (necessity).** With inputs `0` and `ε`, outputs `0` and `ε` are
   still "within `ε`" under the non-strict reading of Definition 1, so there is no
   contradiction. We use `0` and `2ε`, or more generally any two admissible inputs more than
   `ε` apart. The delays of `e₁`, `e₂` ("same as `e₁` and `e₂`") are circular. We take
   round-robin (fair) schedules. Execution `e₃` is built explicitly: replay the first `T₁`
   events of `e₁` restricted to deliveries into `reach_v(F ∪ Fv)`, then the first `T₂` events
   of `e₂` restricted to `reach_u(F ∪ Fu)` (`sim_phase`).
10. **[degenerate] Remark after Definition 3 (cliques).** "In a clique 1-, 2-, 3-reach are
    equivalent to `n > f`, `n > 2f`, `n > 3f`". In fact 1-reach always holds in a clique
    (`oneReach_top`). 2-reach and 3-reach hold iff `n ≤ 1` or `n > 2f`, resp. `n > 3f`
    (`twoReach_top_iff`, `threeReach_top_iff`).
11. **[degenerate] `n = 1`.** 3-reach holds vacuously and consensus is trivial. The source
    components may then meet `F₁ ∪ F₂`, which the proofs implicitly exclude. Our BW proofs assume
    `n ≥ 2`. For `n ≤ 1` the end-to-end theorem uses the algorithm "decide your input"
    (`trivAlg_solves`). With `n ≥ 2`, 3-reach implies `n > 3f`
    (`ThreeReach.three_mul_lt_card`).
12. **[typo] Termination paragraph.** `U[r+1] − μ[r+1] ≤ (U[0] − μ[0])/2^r` should have `2^{r+1}`.
    The weaker bound is still true. We prove `U[r] − μ[r] ≤ (U[0] − μ[0])/2^r`.
13. **[spec, minor]** Things the pseudo-code leaves implicit:
    * After outputting, nodes must keep relaying, or other nodes may never finish their last
      round. Our nodes never stop relaying.
    * Messages of a round may arrive before the receiver starts that round. We store them.
    * The thread executing Filter-and-Average is any thread whose `Verify` holds first (ties
      arbitrary). The output does not depend on the thread.
    * Sorting in Algorithm 3 breaks ties arbitrarily. All our results hold for every tie order.
14. **[gap, minor] Theorem 17.** Parts (a) and the direction "⇒" of (b) are proved by reference to
    [TV15, SST19]. We prove all three equivalences directly from one lemma (`partCond_iff`). The
    proof of (c) in the paper is a short reduction to (b), which we follow.
15. Hypotheses that are not needed (no error):
    * Theorem 5 does not need `F₂ ⊆ V \ F₁`.
    * Theorem 12 does not need `Fu, Fw ⊆ V \ Fv`; we prove it directly from 3-reach rather than
      via BCS.
    * Lemma 8 does not need the receipt along a nonfaulty path before FIFO-Receive-All.

## Modelling choices

* **[model] Asynchronous model** (`Podc/ApproxConsensus/Async/Model.lean`):
  * deterministic event-driven nodes that know `G`;
  * reliable links that are **FIFO**, with adversarial finite delays;
  * a static Byzantine set `B`, `|B| ≤ f`; Byzantine nodes may deliver any message to any
    out-neighbour at any time;
  * fairness: every non-empty link between correct nodes is eventually served.

  The paper does not assume FIFO links. For the necessity this is a strengthening, since
  impossibility in the FIFO model implies impossibility without FIFO. For the sufficiency it is a
  restriction: `bw_solves` and the end-to-end `theorem4` are proved only for FIFO links.
  FIFO-Receive uses counters as in Appendix F, but the delivery argument (`chan_inv`,
  `eventually_received`) is stated for FIFO channels. Sufficiency over non-FIFO links is not
  proved.
* **[model] Decisions** are irrevocable (the first output). The spec quantifies over all event
  sequences: convergence and validity at every time, termination in fair runs.
* **[model] Algorithm BW as a full-information algorithm** (`Operational/BWAlg.lean`). A node's
  state is its input plus the list of received messages. Every condition of Algorithm 1
  ("upon …", "for the first time") is evaluated on prefixes of this history. The parallel threads
  are the per-`F'` conditions; the shared `nextround` flag is "the first prefix at which some
  thread verifies". The node runs `N = outRound K ε` rounds and outputs `x_v[N]`.
* **[model] Two-level proof of sufficiency.** `RoundModel.lean` describes one round by what the
  correct nodes have received over time, with the guarantees of RedundantFlood and FIFO-Flood as
  structure fields (`RoundExec`). All the paper's arguments (Lemmas 6–8, Theorems 9–16) are proved
  there. `Operational/` then shows that every fair run of the operational algorithm yields such
  round executions (`mkRound`): every field is a theorem about the run, none is assumed. A
  fault-free instance (`RoundExec.faultFree`) shows the fields are consistent independently of
  the operational proof.
* **[model] Theorem 5** is stated in its "no `f`-cover" form: some node of `S_{F₁,F₂}` reaches
  `b` in `G − (F₁ ∪ X)` for every `|X| ≤ f`. By Menger's theorem this is equivalent to the `f+1`
  disjoint paths of the paper, and it is the form every proof uses. Menger for digraphs is not
  formalized.
* **[model] Paths** are lists of nodes. Simple = no repeated node. Redundant = `p₁ ‖ p₂` with
  `p₁`, `p₂` simple (Section 3). A value message stored by `v` carries its path extended by `v`
  (Definition 9 reading).
* **Not formalized:** Theorems 1–3 (results of [TV15]); the general `k`-reach family
  (Definition 20, no claims); Theorem 14 as stated (see item 8).
