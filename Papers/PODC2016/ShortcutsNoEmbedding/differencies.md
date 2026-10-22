# Differences between the formalization and the paper

Paper: Haeupler, Izumi, Zuzic, *Low-Congestion Shortcuts without Embedding*, PODC 2016; formalized from the
journal version arXiv:1607.07553v3 (numbering follows it).

Summary: the deterministic results (Lemmas 1, 2, 3, 5, Theorem 2, Corollary 6, the deterministic version of
Theorem 1 and the combinatorial part of Lemma 4) are proved. Lemma 1 needs a precise reading. Lemma 3's proof
sketch has a gap, which we repaired. Lemma 2's broadcast is proved by a different argument (time reversal).

## 1. Errors and gaps in the paper

1. **Lemma 1, literal statement false.** Definition 4 allows a `T`-restricted `H_i` to contain tree edges that are
   not connected (via `H_i`) to `P_i`. Definition 5 counts only components containing a node of `P_i`. Definition 2's
   dilation is the diameter of `E_G[P_i] ∪ H_i`. For the path `0 – 1 – 2` rooted at `0`, `P = {2}`, `H = {01}`:
   `b = 1`, depth 2, but `E_G[P] ∪ H` is disconnected (`lemma_1_literal_false`; here the disconnection uses that
   the vertex set is `P ∪ V(H)`, as in CSLib's `DilationLE`). The failure does not depend on that reading: on the
   path `0 – … – 4` rooted at `0`, `P = {4}`, `H = {01, 23}` has `b = 1` and the edge set `{01, 23}` itself is
   disconnected (`lemma_1_literal_false_edgeSet`). The paper explicitly allows such `H_i` (remark after Definition 5:
   components without nodes of `P_i` "need not be counted"). Severity: degenerate / definitional; the repair (drop
   the useless components) is immediate. We prove:
   - (a) `lemma_1`: any two nodes of `P_i` are joined in `G[P_i] + H_i` by a walk of length `≤ b(2D+1) − 1`. This
     is what the paper's proof shows and what Theorem 2 uses.
   - (b) `lemma_1_dilation`: the full dilation bound `b(2D+1)` when every component of `(P_i ∪ V(H_i), H_i)` meets
     `P_i` (CSLib's `BlocksMeetPart`; then Definition 5 agrees with CSLib's `numBlocks`,
     `blockParam_eq_numBlocks`). All shortcuts built in the paper (`CoreSlow`, `CoreFast`, `FindShortcut`) satisfy
     this (`blocksMeetPart_cutShortcut`, `theorem_1_deterministic`).

   The same issue was found for Observation 2.6 of Ghaffari–Haeupler PODC'21
   (`Papers/PODC2021/LowCongestionShortcuts/`).
2. **Lemma 3, proof gap (statement true).** "Each leader `r` builds a BFS tree comprised of all the nodes that
   believe `r` is the leader": that set need not be connected to `r` (example in the README). Nodes outside every
   BFS tree are not covered by the failure-detection and counting argument. Repaired procedure (`Verification.lean`):
   BFS along edges whose endpoints share a leader, `b₀` supersteps. Unreached nodes reject. A node raises a flag if
   it is unreached or has a neighbour that is unreached or has another leader. Each BFS tree convergecasts the OR of
   flags and its size, and broadcasts the result. `verification_correct`: in a connected supergraph, a node accepts
   iff the supergraph has `≤ b₀` nodes. The proof does not need the IDs to be distinct. Supersteps: `4b₀ + 1`
   (`verificationSupersteps`). Caveat: BFS and convergecast are given by their output specifications; `group B`
   (all reached nodes with `B`'s leader) is one BFS tree only when each leader value has a unique source, i.e. when
   block IDs are distinct (as in the paper: block ID = smallest node ID in the block). With duplicate IDs the
   specification `Accept` is still correct but is not literally what a per-tree convergecast computes.
3. **Lemma 2, broadcast.** The paper proves the convergecast and says the broadcast is symmetric. The induction does
   not transfer: it uses that a more urgent subtree containing a child edge of `v` contains `v`'s edge (true
   upwards), and the per-edge rank is not monotone downwards (README, example). We prove the broadcast bound
   `D − 1 + c` by reversing time in the greedy convergecast schedule (`IsConvergecastSchedule.reverse`). The
   resulting algorithm first runs the convergecast with dummy messages, recording send rounds, and then replays them
   in reverse. This is a different (still simple, deterministic) algorithm from the paper's greedy broadcast. The
   greedy broadcast's `D − 1 + c` bound (true by a standard delay-sequence argument) is not formalized.
4. **Typos/slips.** Algorithm 2 uses the threshold `≥ 4c·p`; the text uses `> 4·p`. In the proof of Lemma 4 the
   second Chernoff bound is written `Pr[S ≤ 2E[S]]` instead of `Pr[S ≥ 2E[S]]`. The `O(log N)` iterations of
   `FindShortcut` are exactly `⌊log₂ N⌋ + 1` (`numIter`, `remaining_numIter`).

## 2. Statements changed or strengthened

- **Congestion.** All hypotheses use CSLib's `CongestionLE` (each edge in at most `c` of the `H_i`). This is weaker
  than Definition 2 (`PartCongestionLE`: at most `c` of the sets `E_G[P_i] ∪ H_i`, implies `CongestionLE` by
  `PartCongestionLE.congestionLE`), so Lemmas 4, 5 and Theorem 1 are proved under a weaker hypothesis. Conclusions
  about the computed shortcut are also in the `CongestionLE` sense.
- **Lemma 5 / Lemma 4 blame argument.** We blame part `i` for an unusable edge `e` when `e` sees `P_i` and
  `e ∉ H_i`. The paper also requires `e ∉ E_G[P_i]`; this is not needed. A missed edge is `e ∈ U ∩ H_i` (the paper
  says `e ∈ U ∩ (E_G[P_i] ∪ H_i)`). We prove `#blocks(H'_i) ≤ #blocks(H_i) + #missed_i`
  (`blockParam_cutShortcut_le`), `#blamed_i ≤ #blocks(H_i)` (`card_blamed_le`) and `Σ missed ≤ Σ blamed`
  (`sum_missed_le_sum_blamed`). Hence the parts with `missed_i ≤ 2b` (at least half) have `≤ 3b` blocks
  (`many_good_of_cut`). The bound `|U| ≤ Nb/c` is not needed. The hypothesis is only "each unusable edge sees at
  least `2c` parts", which covers both `CoreSlow` (`> 2c`) and `CoreFast` (`≥ 2c` w.h.p.).
- **"At least half".** `|P'| ≥ |P|/2` is `card ι ≤ 2·|J|`.
- **Lemma 2 height.** The paper's `height_T(v)` is generalized to any `h` with `h(w) + 1 ≤ h(parent w)`
  (`sent_of_le`); the final bound uses `h(v) = D − depth(v)`, giving `D − 1 + c` rounds. The priority is any
  injective key compatible with the tree (`Compatible`); the paper's (depth of the subtree's top, then ID) is one
  (`compatible_topDepth`, `exists_schedules`). Subtrees are given by their edges and top vertex (`SubtreeFamily`).
- **Theorem 1.** Only the deterministic version is proved: `FindShortcut` with `CoreSlow` gives congestion
  `2c(⌊log₂ N⌋+1)` and block parameter `≤ 3b`. The paper's statement is the randomized one with `CoreFast`
  (congestion `8c` per iteration w.h.p.); its deterministic analysis is `lemma_4_combinatorial` plus the same
  iteration. The verification step is identified with its output specification (`goodOn`: parts with `≤ 3b`
  blocks), justified by `corollary_6`.
- **Theorem 2.** "Convergecasting `O(log n)`-bit messages" is formalized for an arbitrary commutative monoid
  aggregate (`theorem_2_convergecast`). The broadcast from the leader down the BFS tree of the supergraph
  (`b − 1` supersteps) is described but has no separate Lean statement (it is the trivial downward flooding along
  the tree). The total `O(b(D+c))` is `aggregationRounds_le`: `(4(b−1)+1)` supersteps of `≤ 2(D−1+c)+1` rounds. This lemma is
  pure arithmetic; there is no end-to-end theorem about a CONGEST execution of Theorem 2 (see §3, Supersteps).

## 3. Modelling choices

- **Rounds.** CONGEST is modelled through schedules: per tree edge and round at most one message (an `O(log n)`-bit
  ID or partial aggregate), plus causality. Message contents and local computation are not modelled. For Lemma 2 the
  greedy algorithm is an explicit round-by-round process (`greedy`), and its send times form a convergecast
  schedule.
- **Supersteps.** Theorem 2, Lemma 3 and Corollary 6 are verified on the supergraph of a part: synchronous
  algorithms in which each node updates from its neighbours' values via min, `+1`-min or sums. One superstep's cost
  (`superstepRounds D c = 2(D−1+c)+1`) is justified by Lemma 2 applied to the family of all blocks of all parts
  (`blockFamily`, congestion `≤ c` by `blockFamily_congestionLE`) plus one round over intra-part `G`-edges. The
  composition of the message-level schedules across supersteps is not formalized. In the BFS step we use CSLib's
  `Connected.bfsTree` (parents = neighbours with smaller label) after proving that the flooded labels are the
  distances (`floodDist_spec`). For Lemma 3 the multi-source BFS within regions and the per-tree convergecast are
  given by their specifications (`Reached`, `group`, `Accept`).
- **CoreSlow** is modelled by its output (the unique fixed point `coreSlowCut`, existence by the bottom-up
  construction `exists_cut`, uniqueness `cut_unique`); its `O(D·c)` running time is reduced to the fact that every
  transmitted list has `≤ 2c` IDs (`card_coreSlow_list_le`) over `depth(T)` phases.
- **Iteration.** Parts that are already good or not under consideration are replaced by `∅` (`restrictParts`); empty
  parts are seen by no edge, so this is the same as running the subroutine on the remaining parts only.
- **Randomness.** `CoreFast` (shared randomness, Chernoff bounds) is not modelled; Lemma 4 is proved conditionally on
  the two high-probability events (`lemma_4_combinatorial`).
- Trees are rooted spanning trees with parent pointers and depths (CSLib `RootedTree`), depth `≤ D`; the paper's
  "depth `O(D)`" is an explicit parameter `D`.

## 4. Not formalized

- Chernoff bounds and the w.h.p. statements of Lemma 4 / randomized Theorem 1 (`O(c log N)` congestion, round count
  `O(D log n log N + bD log N + bc log N)`), shared randomness.
- Corollaries 4–5 (genus-`g` graphs, MST via Boruvka), the cited existence theorem of [GH16], Section 1.4 survey
  results (Corollaries 1–3, [HHW18]).
- The greedy broadcast's bound (see 1.3) and the message-level implementation of supersteps.
