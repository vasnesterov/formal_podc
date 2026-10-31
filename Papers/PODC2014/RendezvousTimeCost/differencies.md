# Differences between the formalization and the paper

Paper: A. Miller, A. Pelc, *Time versus cost tradeoffs for deterministic rendezvous in networks*,
PODC 2014; arXiv 1508.02471v1 (identical to the proceedings text we have). Rules R1–R6 refer to
the project's verdict scale.

## Statement-level issues

1. **Proposition 2.3, cost bound `2·w(L)·E`: false.** (R1 numbered proposition; R3 not
   applicable, since the fix changes the constant, which is the claim itself; R5 secondary result, so
   ❌.) FastWithRelabeling runs Algorithm Fast (Algorithm 2) on the new labels. The time bound
   `(4t+5)E` shows that the modified label `M(ℓ')` of length `2t+2` is used. Every agent explores
   in segment 1 (`T[1] = 1`), and segments are doubled. With simultaneous start in the oriented
   ring the two agents explore in lock-step during segment 1 and cannot meet, so the cost is already
   `2E` before anything distinguishes them. Then one more exploration is needed. Concrete
   instance: `n = 3` (`E = 2`), `L = 2`, `w ≡ 1` (`t = 2`), starts 0 and 1. The cost is
   `6 > 2wE = 4` (`prop_2_3_cost_false`). The bound fails under every reading we could find: with
   or without `M`, and with arbitrary or simultaneous start whenever `M` is used. The only exception
   is simultaneous start without `M` and without the leading `1`, which is not the algorithm the
   proposition is about. The failure is not confined to `w = 1` (so R2 does not apply): for
   `w = 2` two new labels sharing a leading `1` (e.g. `1001`, `1100` for `L = 6`, `t = 4`) give
   schedules that agree on their first 5 segments, all explorations, so in an oriented ring with
   simultaneous start the cost is already `10E > 2wE = 4E` (a simulation of the 5-ring also finds
   cost `44 > 2wE` for `w = 2, 3`). Correct bound: each agent explores in at most `1 + 2(2w+1) = 4w+3`
   segments, so the cost is at most `(8w+6)E` (`prop_2_3_cost_repaired`). The time bound
   `(4t+5)E` holds.
2. **Corollary 2.1** ("cost `O(E)`, time `O(L^{1/w}E)` for `w ∈ O(1)`"): true. Its proof quotes
   the false constant `2cE`; the repaired `(8c+6)E` is still `O(E)`. The proof also takes
   `t' = c·L^{1/c}`, which need not be an integer; we use any integer `k` with `k^c ≥ L`
   (`cor_2_1`).

## Proof-level issues (statements true)

3. **Theorem 3.2: Fact 3.11 is false; the proof is repaired.** (R1: a claim inside a proof → 🛠️.)
   The proof says that if all partial surpluses of `Agg_x` are at most 1 in absolute value, then
   `x` stays in `P_{j-1} ∪ P_j ∪ P_{j+1}`. That holds only at block boundaries: in mid-block an
   agent at the end of `P_{j+1}` can enter `P_{j+2}` and come back. Counterexample (`n = 12`,
   sectors and blocks of size 2, `i = 1`, `m = 2`): `x` moves `+1,+1,+1,-1` from node 0 and `y`
   moves `-1,-1,-1,+1` from node 6. Then `Agg_x = (1,0)` and `Agg_y = (-1,0)`, all partial
   surpluses are `±1`, and yet both agents are at node 3 after round 3. The vectors belong to a
   correct 2-label algorithm, and trimming does not touch the first 4 rounds
   (`Fact311.fact_3_11_false`, `Fact311.V_correct`, `Fact311.mx_ge_four`). Fact 3.11 is used for
   every zero run in Fact 3.15, so the proof that progress vectors are distinct does not go
   through as written.
   *Repair* (`LowerBoundTime.lean`): use 10 sector-lengths of slack. Blocks and sectors have size
   `s = ⌊n/10⌋`, sectors are taken of the displacement (on `ℤ`), and two agents with equal
   progress vectors stay within `< 5s ≤ n/2` of each other's relative start. The rest of the
   proof is the paper's: a greedy progress vector, distinctness, `≥ s+1` moves per pair of
   non-zero entries, counting, and asymptotics. Only constants change.
4. **Theorem 3.2, other proof details** (all harmless):
   - The proof assumes `6 ∣ n` ("can be modified in the general case"). Our repaired proof works
     for every `n ≥ 10`.
   - The pigeonhole over the block `B(x)` containing `m_x` is unnecessary. We use the same number
     `K = ⌈T/s⌉` of blocks for all agents (trimmed vectors are 0 after `m_x`).
   - Our progress vector records only the second "significant" entry `b_j` of each pair
     `(a_j, b_j)`, with its sign. This carries the same information.
   - Fact 3.15's induction invariant `Prog_x[i..M] = Prog_y[i..M]` does not by itself make `y`'s
     zero runs maximal. The full equality `Prog_x = Prog_y` (the hypothesis) does.
   - Fact 3.16 counts `{-1,0,1}`-vectors with at most `k` non-zeros as `Σ_{i≤k} C(M,i)` and
     forgets the factor `2^i` for signs; it only changes constants. We bound the count by
     `λ^{-k}(1+2λ)^K` instead of the entropy estimate.
   - Fact 3.17's "visited every node of `P_{j+1}`, i.e. at least `E/6` edges": we count
     `≥ s + 1` moves per jump directly.
5. **Theorem 3.1, minor slips in the proof** (statement true; proof essentially as in the paper):
   - Fact 3.1's witness `p'_B = p_A + forward(A) + 1 + back(B)` uses `back(B)` of `B`'s whole
     (trimmed) solo execution. Correct is `B`'s counterclockwise extent *during `α`*. With the
     larger value the shifted segment of `B` can wrap around onto `A`'s. We use the extent within
     the execution.
   - Facts 3.6–3.8 need `F > 3φ` (and `E ≤ 2F`). The paper gets these implicitly from
     `φ ∈ o(E)`; our finite statement assumes `3φ < ⌊n/2⌋`.
   - Fact 3.7 is stated for `i ≤ ⌊L/2⌋ - 1` but refers to `α_{i+1}`; it should be
     `i ≤ ⌊L/2⌋ - 2`.
   - Segments, `forward`, `back` are measured on the line `ℤ` (prefix-sum extremes), not as ring
     segments; the two coincide unless an agent wraps around, and the line version is what the
     proof uses.
   - The Hamiltonian path of the tournament is obtained by insertion sort.
6. **Proposition 2.2, typos in the proof:**
   - "for each `i ∈ {2,…,m}`, `T_X[2i] = T_X[2i+1] = S_X[i]`" should be `i ∈ {1,…,m}`.
   - The delay is first `1 ≤ τ` and later `0 ≤ τ ≤ E`, an off-by-one in the round numbering. We
     use the delay `δ = τ - 1 ∈ [0, E-1]`.
   - The proposition writes `log(L-1)`; the proof gives `⌊log₂(L-1)⌋`, which is what we prove.

## Modelling choices

- **Section 2 (upper bounds).** Nodes form an arbitrary type `V`. `EXPLORE` is an arbitrary walk
  `V → ℕ → V` that visits every node within `E` rounds from any start, as the paper assumes
  ("an agent knows how to explore the graph in time at most `E`"). No graph structure or
  port numbers are needed, so the upper bounds hold in this more general setting. Cost is the
  number of rounds in which an agent changes position (an edge traversal in a simple graph).
  Wake-up: one agent wakes in round 1 and the other `δ ≥ 0` rounds later. A sleeping agent sits at
  its start node and can be found there, as in the paper. Time is counted from the earlier
  wake-up, and cost is counted for both agents until the first meeting.
  The upper bounds are proved without the hypotheses `vA ≠ vB`, `L ≥ 2` and `w ≤ L`, which are
  not needed. The counterexample `prop_2_3_cost_false` satisfies all of them. Wake-up delays are
  given as `δA = 0 ∨ δB = 0`, so either agent may be the late one. Segment indices are 0-based, so
  the paper's "meet by `(2j+1)E`" for the 1-based index `j` reads `(2j+3)E` in `fastSched_meet`.
  For `prop_2_3_time` we assume `w ≥ 1`: for `w = 0` and `L ≥ 2` the parameter `t` does not
  exist.
- **Section 3 (lower bounds).** The oriented ring of size `n` is `ZMod n` and `E = n - 1`. Start is
  simultaneous. An algorithm is a family of behaviour vectors `V : Fin L → ℕ → {-1,0,1}`, exactly
  as in the paper. This is no loss of generality: before meeting, the observations of an agent
  (degree 2, entry port) are determined by its own moves. Labels are `Fin L` (0-based) instead of
  `{1,…,L}`. Meeting means the same node at the end of the same round; crossings on an edge are not
  meetings.
- **Theorem 3.1** is stated three ways:
  - `thm_3_1_explicit`: finite. Cost `≤ E + φ` with `3φ < ⌊n/2⌋` gives an execution of length
    `≥ (⌈L/2⌉-1)(⌊n/2⌋-3φ)/2`. The paper's version has `⌊L/2⌋-1`; we take the larger of the
    clockwise- and counterclockwise-heavy classes.
  - `thm_3_1_linear`: cost `≤ E + E/7` already gives time `≥ EL/112`, a stronger statement than
    `E + o(E)`.
  - `thm_3_1`: the paper's form for a family of algorithms with cost `E + φ(n,L)`, where
    `φ = o(n)` uniformly in `L`.
- **Theorem 3.2** is stated as `∀ c > 0, ∃ c' > 0, ∃ L₀, ∀ n ≥ 10, ∀ L ≥ L₀`: time `≤ cE log₂ L`
  implies some execution of cost `≥ c'E log₂ L`. The paper does not say how `Ω` treats small
  rings; we require `n ≥ 10`, and the finite core is `thm_3_2_core`.
- **Non-vacuity.** For Theorem 3.1, simultaneous-start Cheap in the ring is correct, has cost
  `≤ E` and time `≤ (L-1)E` (`RingCheap.thm_3_1_tight`), so the `Ω(EL)` bound is tight. For
  Theorem 3.2, Algorithm Fast satisfies the hypothesis by Proposition 2.2, but that is proved in
  the abstract Section 2 model. No formal bridge to the behaviour-vector model was written.
