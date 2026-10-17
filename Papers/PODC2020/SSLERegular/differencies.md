# Differences between the formalization and the paper

Hsueh-Ping Chen, Ho-Lin Chen. *Self-Stabilizing Leader Election in Regular Graphs.* PODC 2020,
DOI 10.1145/3382734.3405733 (proceedings version; no arXiv version exists).

Classification: **[F]** false statement, **[G]** proof gap with (morally/provably) true statement,
**[U]** under-specified definition, **[T]** typo, **[M]** modelling choice of ours.

## Errors in the paper

1. **[F] Lemma 4.2 / Theorem 4.3 (SS-Tree) are false for the protocol as printed.**
   MultipleRootDetector (Protocol 6) only moves coins along parent–child pairs, a root tosses only when
   its coin is `0`, and a root's coin never becomes `0` again (it is only reset when it is the *child*
   of an interaction). In a configuration where every node is a root whose `parentColor` is a colour
   of none of its neighbours (a "ghost" parent, ignored by the ghost-parent check because roots do not
   count), no parent–child pair exists, so no coin ever moves; with all coins `+1` the opposite-sign
   test never fires; CycleDetector never runs the ring protocol (no parent–child pair) and only ever
   copies non-leader ring states; the counter of a root stays `0`. All nodes are leaders forever.
   This holds for every `k ≥ 2`, every graph of maximum degree `≤ k` with ≥ 2 nodes and every
   neighbourhood-injective colouring with `k²` colours (the stable output of SS-TwoHop), for every
   ring protocol with a non-leader state. We formalized the reading of the ambiguous indentation of
   Protocols 5–6 most favourable to the paper (the leader test of CycleDetector and the opposite-coin
   test apply to all interacting pairs); by inspection the same configuration is stable under the
   other readings too (all coins are `+1`, so no toss and no coin move is enabled). Lean:
   `ssTree_all_roots_forever`, `ssTree_not_solvesSSLE`, `ssTree_fails_on_complete` (`K_{k+1}`),
   `ssTree_prob_zero`. The intended mechanism ("when a random walk returns to the root, the root
   tosses a coin again") is not implemented by Protocol 6, and isolated roots have no tree to walk
   on; the detector needs a redesign, not a typo fix.
2. **[F] Lemma 3.1 / Theorem 3.3 (SS-EulerCycle) are false for Protocol 1 as printed.** The
   coherence check only accepts a virtual edge *from the initiator to the responder*
   (`u.node[i].successorColor = v.color ∧ v.node[j].predecessorColor = u.color`), else
   `u.errFlag ← True`. An Euler cycle uses every edge in one direction only, and the scheduler also
   lets the head of the edge initiate. We prove that from **every** configuration an error is
   reachable (either some ordered adjacent pair lacks a forward virtual edge, or by pigeonhole two
   neighbours of a node share a colour and the paper's own sequence `(A,B),(A,C),(A,B)` makes
   SS-TwoHop recolour and break the virtual edge), and an erroneous initiator can take any state, so
   **no configuration is output-stable** on any graph whose degrees exceed `k` (every `2k`-regular
   graph, `k ≥ 1`), for every ring protocol with a leader and a non-leader state. Lean:
   `literal_error_reachable`, `literal_not_outputStable`, `literal_not_solvesSSLE`,
   `literal_fails_on_complete` (`K_{2k+1}`).
   **Repair (ours):** if there is no virtual edge `u → v` but one `v → u`, run the Ring-Protocol and
   SS-Token on it with `v`'s virtual node as the ring initiator (`ssEuler true`). With this repair
   Theorem 3.3 holds (`repaired_solvesSSLE`, `repaired_selfStab`, `repaired_prob_one`), assuming the
   Ring-Protocol solves SSLE on directed rings (`RingSpec`, see below).
3. **[G] Lemma 4.1 (existence of a stable SS-Tree configuration): the chain argument does not cover
   CycleDetector's dynamics** (not formalized, not refuted). The proof shows that a fixed chain cut
   out of a stable ring never generates a leader. But CycleDetector re-copies `ringState` into
   `ringStateCopy` whenever a node is (re)marked, nodes unmark at random leaving stale
   `loopChild/loopParent` flags, and a re-marked parent can then interact with a child whose copy has
   already evolved (e.g. parent `b` unmarks, is re-marked by extension from another child `a'`, and
   `cdRing` runs on `(b, a)` with fresh `b` and evolved `a`). Such mixed configurations are not
   reachable on the static chain, so "never generates a leader" does not follow from the property of
   [11] that is used. Whether a leader can actually appear depends on the internals of [11].
4. **[G] Lemma 4.2's case analysis is incomplete.** It treats "no leader" and "several leaders",
   but an invalid configuration can also have exactly one leader and still not be output-stable
   (e.g. a cycle in the pedigree graph elsewhere, ghost parents, a bad colouring). Moot given item 1.
5. **[G] Lemma 3.2's proof is a sketch.** The facts used without proof: that every edge must carry a
   virtual edge and every slot is used exactly once (we prove it by a counting argument on
   neighbourhood-injective colourings, `vperm`), that coherent configurations form a *permutation*
   of virtual nodes (`vperm`, `edge_iff_vperm`), that two rings always share a node (we prove it from
   connectivity), and the convergence of SS-Token from arbitrary token/bit states with a ring leader
   whose ring state keeps changing (`TokenRing.run_legit`, `token_run`). All proved for the repaired
   protocol (`single_reach`, `multi_reach`, `error_or_coherent`).
6. **[G] Lemma 2.1 omits two hypotheses** that the paper only states in the surrounding prose: a
   valid output-stable configuration exists, and error-detected configurations reach it. Our
   `GProtocol.derc_lemma` has both as explicit hypotheses (and `derc_lemma'` the weaker "reach some
   valid output-stable configuration"). The paper's claim that "an error-detected configuration could
   reach all possible configurations" is proved for SS-EulerCycle (`err_reach_all`, any connected
   graph with ≥ 2 nodes, both versions of the protocol); the last interaction needs care because the
   final responder's SS-TwoHop memory is overwritten.

## Under-specified definitions and typos

7. **[T] SS-TwoHop's guard** is printed as `(u.color, v.prevColor, u.colorBit) = (v.prevColor,
   v.color, ¬v.colorBit)`. We read it as Sudo et al.'s "matching colours with different bits":
   `u.prevColor = v.color ∧ v.prevColor = u.color ∧ u.colorBit ≠ v.colorBit` (`twoHopE`, `twoHop`).
8. **[U] "2-hop colouring".** The paper says nodes at distance *exactly two* get different colours;
   what the protocols need (and what SS-TwoHop's detection guarantees) is that the neighbours of every
   node have distinct colours (`InjCol`). We use the latter; `4k²` colours suffice for it on
   `2k`-regular graphs (greedy, `exists_injCol_coloring`). If "2-hop colouring" were read as
   distance-≤2 colouring, `4k²` (resp. `k²`) colours would not suffice on `C₅` (resp. the Petersen
   graph); this reading is not needed.
9. **[U] Protocols 5 and 6** lose their indentation: whether the leader test of CycleDetector and the
   opposite-coin test of MultipleRootDetector are inside the parent–child guard, and whose `errFlag` is
   set. We put both tests outside the guard and set `u.errFlag` (see item 1 for robustness).
10. **[U] "Find i, j"** in Protocol 1 does not say which match is used when several exist; we allow
    any (`EChoice.pick`). In coherent configurations the match is unique.
11. **[T] State count of SS-Tree.** Exactly `320 c² k⁶ (k²+1)² (k+1)²` states in our transcription
    (`card_tstate`), consistent with the claimed `O(k¹²)`. SS-EulerCycle: exactly
    `(64 c k⁴)^k · 64 k⁴` (`card_estate`), consistent with `O((64c)^k k^{4k+4})`.

## Modelling choices

12. **[M] Randomness as nondeterminism.** Random choices (`RandState`, random bits/colours, "randomly
    do") are modelled by their support: `δ p q` is a set of outcomes. Under global fairness and, for
    finite state spaces, for "with probability 1" this is exact (`TS.fair_iff_reach`,
    `TS.tendsto_compl_of_reach`, `TS.prob_eq_zero_of_not_reach`).
13. **[M] Global fairness.** We use the standard definition of Angluin et al. (if `C` occurs infinitely
    often and `C → C'`, then `C'` occurs infinitely often). The paper's wording ("if a configuration
    is always reachable it will be reached eventually") is a different, informal phrasing; for finite
    systems both lead to "a closed set reachable from everywhere is eventually entered". We prove that
    globally fair executions exist (`TS.exists_globallyFair`), so the negative results are not vacuous.
14. **[M] The Ring-Protocol of [11] is a black box** (`RingProtocol`, arbitrary nondeterministic
    protocol with a leader output). For the repaired Theorem 3.3 we assume `RingSpec`: SSLE on every
    *directed* ring of size ≥ 3 (initiator = predecessor, which is how Protocol 1 calls `δ_ring`),
    in reachability form, phrased for all cyclic permutations `(X, τ)` (equivalent to rings `Fin N`).
    We do not formalize [11]; satisfiability of `RingSpec` rests on [11]. The negative results need
    only that the ring protocol has a leader state and/or a non-leader state.
15. **[M] Sub-protocols.** SS-Token ([5]) is reproved from scratch (`TokenRing`); SS-TwoHop ([20]) is
    not proved correct in general — we prove exactly what is used: stability under a
    neighbourhood-injective colouring with matched bits equal (`BitInv`), and detection of the two
    kinds of colour errors.
16. **[M] Scope.** Only even-degree regular graphs (Section 3) and `k`-regular graphs (Section 4).
    The extensions of Section 3.5 (odd degree by doubling edges, general graphs with known degrees)
    are not formalized. The probability statements hold for every Markov kernel whose
    positive-probability moves are exactly the protocol's steps; we do not construct a particular one.
