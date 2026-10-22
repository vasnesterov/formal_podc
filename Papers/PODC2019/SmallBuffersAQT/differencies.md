# Differences between the formalization and the paper

Paper: Miller, Patt-Shamir, Rosenbaum, *With Great Speed Come Small Buffers: Space-Bandwidth Tradeoffs for
Routing*, PODC 2019; formalized from arXiv 1902.08069v1 (the only version; it contains the appendix with the proofs).

## Model (Section 2)

1. **Rounds and intervals.** Rounds are numbered from 0 and intervals are half-open (`cross A n v s t` counts rounds
   `[s, t)`); the excess `ξ_t` is the excess after the injections of rounds `< t`. Definition 2.1 writes `N_T(v)`
   for an interval `I` (typo). `ρ` and `σ` are arbitrary reals (the paper: `σ ∈ ℕ`).
2. **Routes.** A packet with source `a` and destination `b` "contains" buffer `v` iff `a ≤ v < b` (it must be
   forwarded over the edge `(v, v+1)`); the paper writes `v ∈ Path(i_P, w_P)`, which would also count the destination.
3. **Configurations are counts** `c i w` (packets at `i` with destination `w`): packets of one pseudo-buffer are
   interchangeable for buffer sizes. Which packet a pseudo-buffer forwards is arbitrary in every round (`sel`,
   `ValidSel`), so the results hold for every priority rule (the paper suggests LIFO "for concreteness").
4. **ℓ-reduction (Definition 2.4).** Batch `φ` = packets injected in rounds `[ℓ(φ−1), ℓφ)`, accepted at round `ℓφ`
   (paper: rounds `(k−1)ℓ+1 … kℓ` treated as injected at `kℓ`; same up to the 0/1 indexing). The proof of Lemma 2.5
   writes `ℓ·s + 1 ≤ u ≤ ℓ·t`; it should be `ℓ(s−1)+1 ≤ u ≤ ℓt` (typo, statement true).
5. **Non-accepted packets.** As in the paper, packets injected during the current phase and not yet accepted are not
   counted in the buffer occupancy of Theorem 4.1 (they are "pending"). (At a node they number at most `ℓρ + σ`.)

## HPTS (Section 4)

6. **`n = m^ℓ`** is assumed, as in the paper ("for simplicity"); general `n` (padding) is not formalized.
7. **Pseudo-buffers** `L_{j,k}(i)` are named by (level, intermediate destination) `key i w` instead of `(j, k)`.
8. **Badness (Definition 4.5).** The sum over `k ∈ ⟨m⟩` is restricted to intermediate destinations `w_k > i`
   (packets that still have to cross `i`), as in Definition 3.3 and as the prose says. Without the restriction,
   badness of packets that do not cross `i` would be counted, and the first inequality of the proof of Theorem 4.1,
   `B(i) ≤ ξ(i) + 1`, fails (`m ≥ 6`, `σ = 2`: three packets injected at once at node 0 for node 1 give `B(5) = 2`,
   `ξ(5) = 0`). The counterexample of item 11 is stated for the restricted badness; under the literal sum, node 10's
   badness in that instance drops from 2 to 1 (it also counts node 8's bad level-2 packet for intermediate
   destination 9). Checked by `decide +kernel` during review, not kept in the files.
9. **FormPaths (Algorithm 4) in closed form.** Node `v` activates the level-`λ` pseudo-buffer whose intermediate
   destination is the largest among the bad level-`λ` pseudo-buffers at nodes `u ≤ v` with intermediate destination
   `> v` (`fpAct`). This is what the loop computes (the interval `[i_k, min(i'−1, w_k−1)]` contains `v` iff `w_k` is
   that largest one); the equivalence with the loop is proved (`fpAct_eq_loop`, `FormPaths.lean`; the loop is
   `loopAct`, run on the level-`λ` interval of the node with `ws = [w_{m−1}, …, w_0]` and pointer `w_{m−1}`). The same closed form
   is our PPTS (Algorithm 2, whose line 2 `i ← w_d` is undefined) and PTS (Algorithm 1).
10. **ActivatePreBad (Algorithm 5).** Line 5 `w ← max{i ∈ I : i ≤ w_k and [a, i] inactive}` is read with `i < w_k`:
    activating the (empty) pseudo-buffer at `w_k` itself is meaningless and would mark `w_k` as active, blocking the
    pre-bad run of a packet arriving there at a lower level. "∃ P pre-bad for `a` at level `j`" is read as: the packet
    forwarded into `a` by `a−1` under the activation built so far has level `j` at `a` and its new pseudo-buffer at `a`
    is nonempty (Definition 4.6). The calls for `j = λ−1, …, 0` are made in this order, as in Algorithm 3.
11. **Schedule — the main error.** Algorithm 3 sets `λ ← t mod ℓ` and accepts packets when `λ = 0`, so within a phase
    the levels are `0, 1, …, ℓ−1` (increasing); the indexing in the statement of Lemma 4.8 (phase = rounds
    `t+1, …, t+ℓ`) gives `1, …, ℓ−1, 0`. The proof of Lemma 4.8 needs decreasing levels ("levels are activated in
    decreasing order over the course of a phase"). **Lemma 4.8 is false for both orders** (`lemma_4_8_false_alg3`,
    `lemma_4_8_false_indexing`, `m = ℓ = 3`; badness as in item 8; the instance does not depend on the reading of
    Algorithm 5 line 5 in item 10, since node 10 is active anyway). We formalize HPTS with the order `ℓ−1, …, 0` (`fixedSched`) and prove
    Lemma 4.8 (`lemma_4_8`) and Theorem 4.1 (`theorem_4_1`) for it. Whether Theorem 4.1 holds for the literal schedule
    is open: its proof does not apply. Evidence that it may still hold: random simulations with `m = 3`, `ℓ ∈ {2, 3}`
    found no violation; a node has at most `ℓ(m−1)` pseudo-buffers in use, so the bound has slack `ℓ`; and in the
    abstract per-node game defined by our per-round facts (`Bad_high_eq`, `Bad_lam_le`, `Bad_low_le`, which hold for
    any level order), a brute-force search (`ℓ ≤ 4`, `σ ≤ 2`) finds badness at most `ξ + ℓ` for the increasing
    order, against `ξ + 1` for the decreasing one. `ξ + ℓ` would still give `ℓ(m−1) + σ + ℓ ≤ ℓm + σ + 1`. Not proved.
12. **Lemma 4.7** (feasibility) holds by construction: an activation is a function `node → Option pseudo-buffer`, and
    `ActivatePreBad` only activates inactive nodes.
13. **Claim 2.** Item 1 says "for all `j < λ`, `B_j^{s+} = B_j^s`"; it must be `j > λ` (as its proof says). The proof of
    item 3 (cases (a)–(c), Cases 1–3) is replaced by a different argument (`RoundBad.lean`, `RoundMain.lean`): for a
    node `i` and its level-`(λ−1)` block `J`, the nodes of `J` active at level `λ` form a suffix of `J`; a lower-level
    pseudo-buffer can gain a bad packet only at the first node of that suffix (`fpAct_of_bad_arrival`,
    `BadArr_unique`), so the lower levels gain at most one unit of badness of `i`, and only if `i` is active at level
    `λ`, where it loses one unit (`Bad_low_le`, `Bad_lam_le`).
14. **Proof of Lemma 4.8.** The last sentences ("Consider the largest `s` … hence `B^{s+}(i) = B^s(i)`, as desired")
    do not prove the claim; replaced by an induction over the levels in decreasing order (`phase_decreasing`).
15. **Theorem 4.1** is proved in a slightly sharper form: occupancy `≤ (#pseudo-buffers in use at the node) + σ + 1`
    (`Run.occ_le_keys`), and `#pseudo-buffers ≤ ℓm = ℓ n^{1/ℓ}` (`card_keysAt_le`). The hypothesis `0 ≤ ρ` is added
    (`ρ ∈ ℝ⁺` in the paper).
16. **Abstract / introduction.** The upper bound `O(ℓ d^{1/ℓ} + σ)` in terms of the number `d` of destinations (and the
    consequence "`ρ ≤ 1/log d` ⇒ `O(log d)` space") is not proved in the paper: Theorem 4.1 is in terms of `n`, not `d`.
    Not formalized. (Our sharper form gives `min(ℓ n^{1/ℓ}, d) + σ + 1`.)
16a. **Indexing typos in Section 4.** Section 4.1 says `I_{j,r}` "consists of all `m^j` nodes" and
    `I_j = {I_{j,r} : r ∈ ⟨m^j⟩}`; Algorithm 3 line 6 ranges over `r ∈ ⟨m^{ℓ−λ}⟩`. Correct: `m^{j+1}` nodes,
    `r ∈ ⟨m^{ℓ−j−1}⟩` (as in the definition of `I_{j,r}` and Algorithm 5). Our level-`j` interval of `v` starts at
    `lvl m j v = ⌊v / m^{j+1}⌋ m^{j+1}`.

## PTS / PPTS (Section 3)

17. **Propositions 3.1, 3.2** are derived from Theorem 4.1's machinery with `ℓ = 1`, `m = n` (then every packet has
    level 0 and intermediate destination = destination, `ActivatePreBad` never runs, FormPaths = PPTS); packets are
    accepted in their injection round (`b = A`). Lemma 3.4 and Claim 1 are `Bad_lam_le` / `fpAct_of_Bad_lam_pos`
    (in telescoping form). Lemma B.1 (feasibility) holds by construction.
18. **Trees (Section 3.3, Appendix B.2), `Tree.lean`.** Model: a finite forest (`DTree`: parent map + depth), packets
    travel towards ancestors and are delivered at the destination; deterministic execution (`exec`), buffer bound
    after injection. Destinations are ordered by an index increasing along `≺` (a topological sort, as Algorithm 6
    assumes); the loop of Algorithm 6 (`alg6`) is proved equal to the closed form `act` (`alg6_eq_act`). The paper's
    `Path(u, w_k)` includes `w_k`; this is harmless: the literal version forwards exactly the same packets
    (`alg6Incl_fwd_iff`). **Badness:** Definition B.4 / the tree PPTS badness sum over all destinations, which makes
    "`B(v) ≤ ξ(v) + 1`" false (3 packets injected at a child of `v` with destination `v`: `ξ(v) = 0`, `B(v) = 2`; no Lean
    counterexample); we sum only over destinations `w ≻ v`. Proposition 3.5 omits `ρ ≤ 1` (added). We prove
    occupancy `≤ #{w ∈ W : v ≺ w} + σ + 1` (`prop_3_5`) and `≤ 1 + d′ + σ` for `d′` bounding the destination chains
    (`prop_3_5_depth`); Proposition B.3 for any single destination (not only the root), `prop_B_3`. The proofs of
    Lemma B.5 and Propositions 3.5/B.3 ("analogous") are written out (`bad_step_le`, `bad_exec_le`).

## Lower bound (Section 5)

19. **Path length.** The paper takes `n = (ℓ+1)m^ℓ` nodes but type-1 packets go to "destination `n`"; we use
    `(ℓ+1)m^ℓ + 1` nodes (`0 … (ℓ+1)m^ℓ`).
20. **Injection pattern.** "Inject `ρm` packets into buffer `v` during the phase" is made precise as: in every round
    `t < (m−1)m^ℓ` with `⌊ρ(t+1)⌋ ≠ ⌊ρt⌋`, one packet of each type is injected. Injecting `ρm` packets at once would
    not be `(ρ, 1)`-bounded. Requires `ρ ≤ 1` (stated by us; the paper only says `ρ > 1/(ℓ+1)`); the adversary
    stops at round `(m−1)m^ℓ`.
21. **Protocols.** Arbitrary offline (clairvoyant, centralized) protocols: any packet trajectories moving at most one
    hop per round with at most one packet per edge per round (`Execution`). Delivered packets occupy no buffer.
22. **Lemma 5.4 gap.** The paper bounds the number of β-stale packets by the load of `[F(t+1)+1, F(t)]` in round `t+1`,
    but such a packet may be delivered in round `t+1` and then occupies no buffer. We count them in round `t` in
    `[F(t+1), F(t)]` (they are fresh, hence undelivered by Lemma 5.3).
23. **Lemma 5.5 replaced.** Instead of the per-phase dichotomy, a global telescoping count: with `L` the maximal load,
    at most `1 + 2L(F(t) − F(t+1))` packets become stale at the end of round `t` (`card_injected_le_real`). The paper's
    computation `F(t) − F(t+1) = ∑_{j=0}^{k} m^j` is checked (`lemma_5_4_drop`) but not needed.
24. **Constants.** We prove: some buffer has load `≥ ((ℓ+1)ρ − 1)(m−1)/(4(ℓ+1)) − 1` (`theorem_5_1`), from the sharper
    `((ℓ+1)ρ−1)(m−1)m^ℓ − (ℓ+1) ≤ 2(ℓ+1)m^ℓ · load` (`exists_load_ge`). With `n ≈ (ℓ+1)m^ℓ` this is the paper's
    `Ω(((ℓ+1)ρ−1)/ℓ · n^{1/ℓ})` up to constant factors (`n^{1/ℓ} ≤ 3m` for `ℓ ≥ 1`). The paper's proof writes `/2k`
    for `/2ℓ` once (typo).
25. **`ℓ ≥ 1`** instead of `ℓ ≥ 2`; `m ≥ 2`.
26. **Claim 3 / Lemma 5.3** are stated with phase numbers `P = t/m`; the "highest differing digit" is the least `k`
    with `P'/m^k = P/m^k`.
