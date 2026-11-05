# Differences between the formalization and the paper

Paper: Klasing, Kosowski, Pająk, Sauerwald, *The Multi-Agent Rotor-Router on the Ring*, PODC 2013, full version
hal-00735113v2 (2014). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Model (Section 1.3, Section 2.1)

1. **Graphs.** The paper uses the directed symmetric version of an undirected connected graph. `RotorGraph` allows
   any finite directed multigraph with out-degree ≥ 1 and a fixed cyclic order of the out-arcs of each node.
   Lemmas 2.1–2.3 are proved in this generality, which includes the paper's setting. Connectivity is not needed.
2. **Pointers.** The paper fixes port labels so that the initial pointer is port 0. We keep the cyclic order
   `port v 0, …` and an explicit initial pointer `ptr v` (read mod `deg v`). This is equivalent.
3. **Delays.** The paper's `D(v, t)` is the number of agents stopped at `v` in round `t`, implicitly at most
   the number present. We allow any `D : ℕ → V → ℕ`, and `min (pos v) (D t v)` agents stay. With this
   truncation the hypothesis `D₁ ≥ D₂` of Lemma 2.1 is meaningful even when the two runs have different
   numbers of agents on a node. It covers the paper's reading.
4. **Visits.** `visits c₀ D t v` = initial agents on `v` + arrivals at `v` in rounds `1..t`, as in equation
   (4) / `n_v(0)` of the paper. A stopped agent does not create a new visit; this matches equation (2)
   (`e_v(t+1) = n_v(t) − D(v, t+1)`). Proved as `exits_succ_eq` (with truncation, as a `max`).
5. **Cover time.** `Covered c₀ D t` (all nodes have positive visit count after round `t`) and
   `CoverTime c₀ D T` (covered at `T`, not before). The cover time of the paper is the `T` with
   `CoverTime … T`.
6. **Ring.** `ZMod n`, port 0 to `v + 1`, port 1 to `v − 1`. On the ring only the initial pointers matter, as
   the paper notes.
7. **Labelled agents** (`Domains.lean`) are used only for Lemma 2.4, since domains need identities. Agents on
   a node are released in index order (the paper: order irrelevant, agents indistinguishable). The labelled
   model is not connected formally to the counting model; for the counterexample the two agents are always on
   different nodes, so each simply follows its node's pointer.

## Statements

8. **Lemma 2.1** (`lemma_2_1`): as stated (same initial configuration, `D₁ ≥ D₂` pointwise). We also prove the
   joint monotonicity in the initial placement (`visits_mono`). That gives the remark `R[k−1] ≤ R[k]`
   (`visits_remove_agent`): remove one agent from a node, same pointers.
9. **Lemma 2.2** (`lemma_2_2`): as stated. `τ = activeRounds D T` counts the rounds `t ∈ [1, T]` with
   `D(v, t) = 0` for all `v`.
10. **Lemma 2.3** (`lemma_2_3`): stated as "if `CoverTime D T` then there is `C` with `CoverTime R C` and
    `τ ≤ C ≤ T`", where `τ` is the number of fully active rounds among the first `T`. ("In at least `τ` of
    these rounds" follows.)
11. **Lemma 2.4**, first property (`lemma_2_4_false`): false as stated; agents may swap along an edge without
    meeting at a node. **Rule: R3/R4 → ⚠️.** The intended hypothesis ("never meet *or pass each other on an
    edge*") is recoverable from the paper itself (proof of Theorem 4.1 uses exactly this wording); the fix is a
    local strengthening of the hypothesis. The paper's later lemmas (2.5–2.9) do not reason about swaps at all.
    The counterexample is a delayed deployment (two undelayed rounds, then both agents stopped), which Lemma 2.4
    allows ("a deployment"). The second and third properties are not refuted (in the counterexample the third
    holds for the agent `0`: its domains after rounds 1 and 2 differ in 2 nodes). The counterexample depends on
    giving the (indistinguishable, Section 1.3) agents identities that are kept through an edge crossing; with
    the equally admissible convention that crossing agents swap labels (two bounces) it disappears. This is a
    further reason for ⚠️ rather than ❌, and Lemma 2.4 does not affect the overall verdict.
12. **Repaired Lemma 2.4** (`pattern_invariant`): a label-free invariant of the *undelayed* system, valid for
    every initialization. For two adjacent empty nodes, the patterns `(L,R)`, `(L,U)`, `(U,R)` never occur
    (`L`/`R` = visited with pointer counter-clockwise/clockwise, `U` = unvisited). Equivalently, between
    consecutive occupied nodes the empty nodes read `R…R U…U L…L`: domains are arcs, and visited pointers point
    away from the agent of their domain. This is our formulation, not the paper's.
13. **Lemma 3.1** (`lemma_3_1_false`): false as stated; (1)–(4) are contradictory for every `k ≥ 2`.
    **Rule: R3 not satisfied → ❌ (non-headline, R5).** The intended identity (4') `a_i / a₁ = 2/a_i − …` is
    recoverable from the lemma's proof (`a₁ = 1/c²`). But the proof of Theorem 3.2 reasons with the misprinted
    form: it computes `g_i ≈ 2 a_i a_k k⁴ a₁`, `S_{j+1} = S_j + k⁴ a₁ a_k + 12k`, `B₁ ∈ Θ(n²/a₁)`, and then
    substitutes `a₁ = Θ(1/H_k)` to claim `Θ(n²/log k)`. That is a second slip; consistently it would give
    `Θ(n² log k)`. Borderline call: if one only looks at Lemma 3.1 and its own proof, it is a ⚠️ typo. We
    follow R3's clause "not excused if the paper's proof reasons with the wrong version". (Checked on the rendered pages 14 and 17–18 of the full version: (4) is printed `a_i · a₁`, and the
    Phase B deployment itself is defined with the step `⌈k⁴ a₁ a_k⌉`, so the corrected identity also changes the
    deployment, to steps of about `2k⁴ a_k / a₁`.) The corrected
    Lemma 3.1, with (4'), is proved with all six properties for every `k ≥ 2` (paper: `k > 3`)
    (`lemma_3_1_corrected`, `H_k` = `harm k`). The proof follows the paper's construction (`b_i(c)`, root
    of `d_{k+1}(c) = 0` by a sup/continuity argument). The upper half of (5), `c² ≤ 4(H_k+1)`, gets a simpler
    proof than the paper's `e^{c²/4}` estimates: if `4H_k ≤ c²` then `b_j ≥ jc/2` for all `j`, which
    contradicts `d_{k+1} = 0`. The paper's step "by the intermediate value theorem" is made precise (the `b_i`
    are continuous only where the earlier `b_j` are nonzero; the first `d_j` to vanish is `d_{k+1}`, since
    `d` decreases). (1) `a₀ = +∞` is encoded as `1/a₀ = 0`.
14. **Theorem 3.7** (`theorem_3_7`):
    - hypothesis `n ≥ 8k` and `k ≥ 1` instead of `n ≥ 440k²` (stronger theorem);
    - the hidden constant is explicit: every covering time `T` satisfies `n² < 8192 k² T`;
    - the pointer arrangement is explicit: all pointers point away from a node `v` chosen by counting (towards
      the farther neighbour; ties at the antipode arbitrary but fixed);
    - "any set of initial locations" is read as any multiset of `k` start nodes (`pos₀` with `Σ pos₀ = k`),
      as in the paper's "not necessarily distinct starting vertices";
    - the paper's proof is replaced entirely. Its gaps (**🛠️**, proof of a true statement): reliance on
      Lemmas 2.5/2.6, whose proofs are sketchy, at a scale they are not stated for; "pointers point away from
      the closest agent" where the negative initialization (towards the closest agent) is meant; "by Lemma
      2.1" where the lower-bound half of Lemma 2.2/2.3 is needed; the final `Ω(n²/400k²)` step is not
      derived. Our proof uses the potential identity `potential_run` (a Holroyd–Propp-type potential, not in
      the paper), `hit_lemma`, `scale_step`, `multiscale` and `exists_good_center` (a counting substitute for
      the good vertices of Lemma 3.6).

## Not formalized (no verdict contribution)

15. **Theorem 3.5** (well-spaced initialization, `O((n/k)²)` for every pointer arrangement; a headline together
    with Theorem 3.7, so by R5 this unestablished headline gives ❌, the label Lemma 3.1 already gives). Proof gap:
    in the deployment, after each step agent `i` "returns to node `q_i`". But the pointer of `q_i` was flipped
    to the left when the agent left it to the right, so in the next step the agent would be sent left, not
    "moves (to the right)". Moreover, if agent `i−1` does not move in the initial phase and agent `i` runs left
    down to `p_{i−1}`, then `q_i = q_{i−1}`, and the two agents on one node leave in opposite directions.
    Numerically the statement holds: adversarial hill-climbing over pointer initializations, agents equally
    spaced with gap `L ∈ {3,5,8}`, `k ≤ 32` (`k ≤ 16` for `L = 8`), maximal cover time found
    `≈ 1.25 (L+1)²`.
16. **Theorems 3.2, 3.4, Lemma 3.3**. Besides the Lemma 3.1 issue (item 13), the proof of Theorem 3.2 asserts
    "the cover time is also monotonous with respect to the size of the ring" without proof. Simulation of its
    initialization (all agents on `v`, pointers along the shortest path to `v`) finds no violation for
    `4 ≤ n ≤ 59`, `k ∈ {1,2,3,4,5,8,16}`. Monotonicity in `k` follows from Lemma 2.1 (`visits_remove_agent`).
    Also `Θ(n²/log k)` is meaningless for `k = 1` (degenerate, R2).
17. **Lemmas 2.5–2.9, Theorem 4.1.** Not formalized. Slips noticed: Lemma 2.8 says "`2n²` consecutive time
    steps `t, …, t + n² − 1`"; Lemma 2.5 is used in Theorem 3.7 with initial interiors `n/(20k)` but stated for
    `22k`, and its proof only bounds the loss by `11k`.
18. **Lemma 3.6** (≥ `0.8n − o(n)` good vertices). Not formalized; the scanning algorithm mixes window lengths
    `r(n/k)` and `r(n/(10k))` (typo). The statement is plausible by a rising-sun/maximal-inequality argument.
19. **Section 3.3** (random walks) and the random-walk columns of Table 1: out of scope.

## Typos (no verdict contribution)

20. Equation (4) in the proof of Lemma 2.1 and the recurrence in the proof of Lemma 2.2 use `e_v(t)` where
    `e_v(t+1)` is meant, relative to equation (2) and the visit convention. Our `visits_eq_visitsOf` /
    `exits_succ_eq` give the correct indexing.
21. In the proof of Lemma 2.1 the notation switches between `port_v(u)` and `port_u(v)`.
