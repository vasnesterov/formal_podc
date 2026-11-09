# Differences between the formalization and the paper

Paper: Kulkarni–Vaidya, *Effectiveness of Delaying Timestamp Computation*, PODC 2017; formalized from the full version
arXiv:1606.05962v1 (Vaidya–Kulkarni, *Efficient Timestamps for Capturing Causality*). Numbering follows arXiv.

## Mistakes (labelled)

1. **🔧 Theorem 1 is false for non-FIFO channels.** The paper assumes only reliable channels. Its algorithm sets
   `next[j] = index(inbound(p_j, e)) = index(recv(outbound(p_j, e)))` (Sections 2, 4.1, 4.2): the receive of the
   *first* message sent at or after `e`. Counterexample `theorem_1_false`: star graph on `{p_0, p_1}`, `C = {p_0}`, execution
   `send 1→0; send 1→0; p_0 receives the 2nd; p_0 receives the 1st`. Then `0 → 2` but
   `Q_t(0).next[0] = 2 > 1 = Q_t(2).vect[0]`. The literal pseudo-code (sets `N_e`, "a finite `next[j]` is never
   modified") returns 1 or 2 depending on the arrival order of the acknowledgements. Appendix E's variant (mark
   `next[j]` invalid at the send) always returns 2. The proof (Appendix A, Case 3) silently uses the *earliest*
   receive. So does the "Intuition behind inline timestamps" paragraph of Section 4 ("the *earliest* event at each
   `p_j ∈ C` … influenced directly"). FIFO channels are not assumed or used anywhere in the paper (Sections 1–2: "reliable
   bidirectional channels"; the lower-bound proofs need only one message per channel). Repairs, both proved: FIFO channels (`theorem_1`, hypothesis `Exec.FIFO`), or `next[j]` := least receive
   index over the messages `p_i` sent to `p_j` in `[e, t]` (`queryMin`, `theorem_1_min`, no FIFO).

## Proof gaps of true statements (labelled)

2. **🔧 Lemma 2, proof.** "Without loss of generality the entries are non-negative integers" is not justified: an
   online algorithm may use negative entries, and no uniform shift exists. Also, `E` is defined as the maximum over
   the radial events but used as the maximum over `W`, and "since `p_k ∉ W`" should be "`p_k ∉ S`". Repaired by a
   sum argument: the coordinate sum along `p_0`'s chain grows by `≥ 1` per event, and the start value is fixed before
   the chain length is chosen (`card_lt_of_online_int`, `lemma_2`).

## Typos (no label)

3. Lemma 1 proof: `e_{i,n−2}` should be `e_{0,n−2}`.
4. Lemma 2 proof: `e_{0,Pn}`, `e_{0,Pn+n−2}` with `P = (M+2)n` should be `e_{0,P}`, `e_{0,P+n−2}`.
5. Section 4.4: "events at processes in `C` do include an id field" should be "outside `C`".
6. Appendix E: "event `e` at process `p_i ∈ C` … `next` field" should be `p_i ∉ C`.
7. Section 3: "vector connectivity" should be "vertex connectivity".

## Modelling choices

8. **Executions.** A finite list of events in real-time order (position = real time). Events: unicast send, receive
   (referring to the position of its send) and local computation. `Exec.WF`: each receive matches an earlier send
   addressed to the receiver, at most once. Messages need not be delivered (an undelivered message has receive index `∞`); the
   inline `next` field may refer to a receive event after the query time, since the query waits for it. Channels are not FIFO unless
   `Exec.FIFO` is assumed. `Exec.OnGraph G`: sends only along edges of `G`.
9. **Happened-before.** Transitive closure of "previous event of the same process" and "send → receive" (`Exec.HB`),
   which is Lamport's relation.
10. **Online algorithms** are arbitrary functions of the execution prefix ending with the event (`onlineTs`), i.e. with
    global knowledge, including real time. The paper's online algorithms are distributed and see less, so our lower
    bounds are stronger. Correctness (`IsOnlineTimestamping G A`) is required on every well-formed execution over `G`,
    and includes distinctness, as the paper's definition of online algorithms (Section 1) does. Lemma 2's statement
    omits "distinct", but its proof uses it.
11. **Vector entries.** Lemmas 1, 3, 4: any linear order (the paper: reals). Lemma 2: `ℤ` (the paper: integers;
    no non-negativity assumed). Order on vectors: Mathlib's `Pi` order, which is exactly Section 3's `<`.
12. **Graphs.** Lean's `SimpleGraph`. "Vertex connectivity ≥ 2" is CSLib's `IsVertexConnected 2` (West: more than 2
    vertices, removing one vertex keeps it connected). Lemma 4 is stated for `IsVertexConnected 1` (connected, ≥ 2
    vertices), weaker than the paper's "connectivity exactly 1", with `X = nonCut G` (vertices whose removal keeps the
    rest connected). The star graph `star m` on `Fin (m+1)` has centre `0` and `n = m + 1`.
13. **Lower-bound executions.** The paper floods messages with delays tuned by `δ` and diameters `D`. We instead
    route a token from each `j ∈ X \ {k}` to a common process `r` along a walk avoiding `k` (`gather`), after one
    initial local step of every process of `X`. The causal structure is the same: everything of `X \ {k}` reaches `r`,
    nothing of `k` does. The initial events are local steps instead of sends.
14. **Lemma 2 execution.** The radial processes take their first step *before* the chain of local events of `p_0`.
    The paper lets `p_0` compute "initially", concurrently; for an online algorithm only the causal/real-time prefix
    matters.
15. **General forms.** `card_le_of_online` (any `X` such that for each `k ∈ X` the rest of `X` reaches some `r ≠ k`
    avoiding `k`) implies Lemmas 1, 3, 4. `card_lt_of_online_int` (additionally a common target `c ∉ X`, integer
    entries) implies Lemma 2.
16. **Appendix B.2.** The algorithm is a merge-and-update fold (`starAlg`), generalized to any cut vertex `c` in the
    centre's role (this covers the upper-bound remark at the end of B.3.2). "Any value in the open interval
    `(w[j], ⌊w[j]+1⌋)`" is an arbitrary `pick : position → coordinate → ℝ → ℝ` satisfying the interval property.
    The proof uses only that property, so a choice depending on more data would also work. The paper's correctness
    proof is omitted ("straightforward"); we prove it (`starAlg_captures`). The vector is indexed by the processes
    other than the centre and transported to `Fin (n−1)` in `appendix_B2`. The statement of `appendix_B2` is an existence
    claim over `IsOnlineTimestamping`, whose algorithms may use global knowledge, so on its own it is weaker than the
    paper's claim; its witness is the distributed fold `starAlg` with `midPick` (`starOnline_isOnline` states this directly).
17. **`n = 2`** (B.2, first paragraph): `two_le_of_ne` (any two processes force length `≥ 2`) and vector clocks of
    length 2 (`appendix_B2_two`). The case `n = 1` is not formalized (trivial).
18. **Theorem 1.** `Q_t(e)` (`query`) has `vect` computed by the algorithm (`inlineAlg`), and `next` by its
    specification (`outbound` at time `t`, then the index of the receive); control messages are not simulated.
    Timestamps of events in `C` keep (unused) `index` and `next = ∞` fields. The order `<` reads `id` and `vect` only
    for such events, so this changes nothing. The cover `C` is any `Finset` with `G.IsVertexCover C`; the paper
    renames it to `{p_0, …, p_{c−1}}`. The hypothesis `t ≥ e_r` is kept in `theorem_1`/`theorem_1_min` but not used.
    Distinctness of inline timestamps (Section 1) is `query_injective`.
19. **Theorem 2.** Figure 4 is read as: `p_1` (top line) sends `E1` and `E7` to `p_0`; `p_2` sends `E5`; `p_3`
    receives `E3`, sent by `p_0` at `E2`; `p_0` (bottom line) receives `E0` (from `E1`), `E4` (from `E5`), `E6` (from
    `E7`). The happened-before relation is computed in Lean (`fig4_hb_iff`). The proof is manual instead of Z3; vector
    entries may lie in any linear order, and distinctness is not needed.

## Not formalized

20. Section 5, Appendix D (related work); the optimizations of Appendix E; the control-message protocol and
    liveness of queries (Section 4.2).
