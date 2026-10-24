# Differences between the formalization and the paper

Paper: O. Michail, G. Skretas, P. G. Spirakis, *Distributed Computation and Reconfiguration in
Actively Dynamic Networks*, PODC 2020 (arXiv:2003.03355v1, full version with Appendices A–D).

## Errors in the paper

1. **Lemma 3.1 is false for GraphToStar as printed** (`GraphToStar.lemma_3_1_breaks`,
   `GraphToStar.line4_phase2`). On the line `0-1-2-3` with increasing IDs, the pulling rule
   ("`u` activates `uw` where `w` is the leader that `v` activated an edge with in the previous
   phase") makes `C(0)` jump to node `2` in phase 2, while `C(2)` merges into `C(3)` in that same
   phase. In phase 3 `C(0)`'s target "did not activate", so `C(0)` enters merging. In phase 4 it
   merges into node `2`, a follower. Afterwards `lead 0 = 2` and `lead 2 = 3`, so the committees are
   not stars. In phase 5 `C(3)` is the only committee and enters termination while `0` is still
   attached only to `2` (`GraphToStar.line4_terminates_wrong`), so the output is not a spanning
   star around `3`. The proof of Lemma 3.1 claims that
   pulling committees run TreeToStar on committees, with the root's children merging and the
   grandchildren becoming children. This overlooks great-grandchildren jumping onto children that
   dissolve in the same phase. Consequently Theorem 3.8 is not established. A natural repair is to
   redirect a pointer whose target merged away to the absorbing leader (one extra round, distance 2
   through the former leader). It terminated with `O(log n)` phases in our simulations
   (`scripts/g2s.py` finds the failure, `scripts/g2s_fix.py` + `run_fix*.py` test the repair), but
   the repair is not proved.
2. **Lemmas 3.2–3.7 (time of GraphToStar)**: informal and partly garbled. They are not formalized,
   since the algorithm they analyse is broken (item 1).
   - Lemma 3.2's computation `S(C(u_{s+log i})) = S(C(u_s)) + 2·S + 4·S + … + 2^{log(i-1)}·S = 2^{k+i}`
     does not typecheck as written. For a pulling tree of depth `j`, the root gains about
     `j·2^k`, not `2^{k+j}`; the intended bound needs depth `≥ 2^{j-1}` after `j` waiting phases.
   - Lemmas 3.4 and 3.5 use inconsistent exponents (`2^{k+p-4}` vs `2^{k+p-3}`) and phase indices
     (`p+1` vs `s+p+1`).
   - Lemma 3.7 ("each phase consists of at most 2 rounds") ignores the communication between
     followers and leaders needed to learn neighbouring committees' UIDs and modes.
3. **Theorem 6.4 / D.12**: the proof is a sketch.
   - "Corresponding states" (Def. D.7) is garbled. Lemma D.11 uses undefined `i_min`, `i_max` and
     "a previous proof" for `k − log k`. Observation 2 has no proof. The final sum is claimed
     "`= Θ(log n)`" instead of `Θ(n log n)`.
   - The theorem implicitly assumes comparison-based algorithms, which §2.1 says of all of the
     paper's lower bounds; the proof uses increasing-order rings.

   Not formalized.
4. **Proposition 2.1 / A.1, "`⌈log d⌉ ≤ log n`"**: false in general. For the 6-node line
   (`d = 5`), TreeToStar needs exactly `⌈log₂ 5⌉ = 3` rounds and `3 > log₂ 6`
   (`ceil_log_depth_le_log_false`, `line6_not_star_two`). We prove the exact round count
   `⌈log₂ d⌉` (`TreeToStar.star_iff`).
5. **Observation 1 (App. D.1)** says a Depth-`log n` tree forces `PO_{u,v} ≤ log n`. The correct
   bound is `2 log n`: two leaves can be at distance twice the depth. Lemma D.3's final bound
   `n − 1 − 2 log n` is nevertheless what we obtain (`lemma_6_2_total` with `d = log n`).
6. **Minor slips.**
   - Proof of Prop. A.1: "`O(log n)` total edge activations" should be `O(n log n)`.
   - Prop. 2.2 says maximum degree 3, while §2.3 and the proof of A.2 say at most 4. We prove
     `≤ 3` for every snapshot (`degree_le_three`); 4 is only reached in the middle of a round,
     between activations and deactivations.
   - CutInHalf only activates edges, so its output is not a tree. We add the deactivations of the
     edges that become redundant.

## Modelling choices and deviations

- **Model.** Snapshots are `SimpleGraph V` and rounds are 0-indexed (`E 0` is the paper's
  `D(1) = G_s`).
  - `ValidRound G G'` states that every edge of `G'` is in `G` or joins two nodes with a common
    `G`-neighbour. `validRound_iff` shows it is equivalent to the paper's
    `E(i+1) = (E(i) ∪ E_ac(i)) \ E_dac(i)` with `E_ac` between potential neighbours and
    `E_dac ⊆ E(i)`.
  - The rules for duplicate or conflicting requests (two endpoints activating the same edge, or
    disagreeing) are subsumed: only the resulting graph matters.
  - Connectivity of snapshots is not part of the model. All our executions are trees at every
    round (`isTree`).
- **"Active edges per round" (Props. 2.1/2.2).** We count the edges active during the round,
  i.e. the old edges plus the activated ones (`(E t ⊔ jumpAct …).edgeSet.ncard ≤ 2n − 3`). That
  is the count the paper's proof uses. We also prove that every snapshot has exactly `n − 1` edges.
  The paper's separate measure "maximum activated edges" `|E(i) \ E(1)|` is not stated separately.
  It is at most `n − 1` here.
- **Total activations.** The paper's "`O(n log n)`" / "`n log n`" is proved in explicit form:
  - TreeToStar: `≤ (n − 2)⌈log₂ d⌉`.
  - LineToCompleteBinaryTree: `≤ (N − 2)⌈log₂ d⌉` for `N` nodes.
  - CutInHalf: `≤ N − 1`.

  All three hold over any horizon.
- **Distributed details of the subroutines.** We formalize the global effect of the per-node
  rules (pointer jumps). Each node knows its parent; learning the grandparent's identity and
  child count needs one message from the parent within the same round, which is not modelled.
- **LineToCompleteBinaryTree.**
  - The rule "repeat until attached to the root or the grandparent has two children" is
    formalized statelessly: in each round, move iff the parent is not the root and the grandparent
    has `< 2` children. By the closed form (`LineArith.Q`), a node that stops never satisfies the
    condition again, so the stateful and stateless rules have the same executions (checked
    numerically up to 300 nodes, `scripts/check_stateful.py`).
  - The line is rooted at an endpoint, as in the paper's construction and its asynchronous
    variant. The paper says "any line rooted at `u0`"; simulations suggest that lines rooted at an
    interior node also work, but this is not formalized.
  - "Binary tree centered at `u0`" is proved in the strong form "complete binary tree in level
    order": node `i` has depth `⌊log₂(i+1)⌋`, total depth `⌊log₂ N⌋` (`final_edist`,
    `final_isDepthTree`).
  - The time is `kk n ≤ ⌊log₂ n⌋ ≤ ⌈log₂ d⌉`. After that the network is constant
    (`exec_stable`), and before it the network still changes (`exec_succ_ne`).
- **Depth-`d` Tree target** (`IsDepthTree G r d`): `G` is a tree and every node is within distance
  `d` of `r`. Leader election (the "unique leader at the root" part) is irrelevant for the
  centralized statements and is not modelled.
- **Lemma 6.1 / D.2.**
  - Proved for every execution from the spanning line whose final snapshot has radius `≤ d`:
    `n − 1 ≤ 2^{T+1} d` (`lemma_6_1`), hence `⌊log₂(n−1)⌋ ≤ T + 1 + ⌈log₂ d⌉`.
  - The "`Ω(log n)`" is made explicit as `⌊log₂ n⌋ ≤ 2T + 7` for `d ≤ ⌊log₂ n⌋ + 1`
    (`lemma_6_1_asymp`).
  - The proof halves distances instead of using the paper's information "potential" `PO`.
- **Lemma 6.2 / D.3–D.4.**
  - `n − 1 ≤ (total activations) + 2d` holds with **no** time restriction (`lemma_6_2_total`).
    The paper assumes `O(log n)` time, which is only needed for the per-round version.
  - Per round: `n − 1 ≤ T · m + 2d` if every round activates `≤ m` edges (`lemma_6_2_perRound`).
    With `T, d = O(log n)` this gives `m = Ω(n / log n)`.
  - The key fact is that one activated edge shortens any distance by at most one
    (`ValidRound.edist_le_add`; a shortest path uses each new edge once).
- **Theorem 6.3 / D.5.**
  - Only the line case is formalized (`CutInHalf.theorem_6_3_line`): `⌊log₂(N−1)⌋` rounds,
    `≤ N − 1` activations, final tree of depth `≤ ⌈log₂ N⌉` rooted at `0`.
  - The paper's general-graph version (Euler tour of a spanning tree used as a virtual ring of
    `≤ 2n` nodes) is not formalized. Its depth bound would be `log(2n)`, not `log n`.
  - The paper's CutInHalf indexes rounds from 1 and activates `u_j u_{j+2^i}` for
    `j ≡ 1 (mod 2^i)`; we use 0-indexed nodes with `2^{i+1} ∣ j` in round `i`.
- **GraphToStar model** (`GraphToStar.lean`).
  - Committee/phase level: leaders, modes, the leader each leader last activated an edge with
    (`tgt`), and flags for "activated a leader edge in the previous phase" and "some committee
    activated an edge with me in the previous phase".
  - Committees are neighbours iff an edge of `G_s` joins their members or one leader activated an
    edge with the other.
  - Phases are synchronous and all decisions use the state at the start of the phase, which is how
    the mode descriptions read.
    §2.4 says the algorithms run in "asynchronous phases"; lock-step phases are one admissible
    schedule, and Lemma 3.1 claims correctness for every execution.
  - Under every reading of "the leader of `C(v)`" (the node `2`, or the current leader `3` of its
    committee) the printed rules fail: the merging rule moves only followers and presupposes that
    the leader `u` is already adjacent to the target leader, and `0` is never adjacent to `3`. At
    the committee level the intent (`C(0)` becomes a child of `C(3)`) is clear, but realising it
    needs an activation step that the algorithm does not contain.
  - The model ignores rounds within a phase, the temporary edge `e₁` of the selection, and the
    termination phase. None of these affects the failure in phases 1–4.
- **Not formalized.** Lemmas 3.2–3.7, Theorem 3.8, Section 4 (GraphToWreath, Theorem 4.2),
  Section 5 (GraphToThinWreath, Theorem 5.1), Appendices B and C, Theorem 6.4 / D.12, and the
  asynchronous LineToCompleteBinaryTree (Lemma B.4, Corollary B.5).
