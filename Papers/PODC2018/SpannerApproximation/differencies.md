# Differences between the formalization and the paper

Paper: K. Censor-Hillel, M. Dory, *Distributed Spanner Approximation*, PODC 2018. Formalized from
arXiv:1802.03160v1 (numbering as there).

## Section 2: directed `k`-spanner lower bounds

1. **Exact vertex count, padding.** The paper picks `ℓ, β` from an auxiliary `n'`, runs the
   algorithm on `G(ℓ, β)` with `n = 2ℓβ + 5ℓ ≤ n'` vertices, and assumes `α(n)` is monotone with
   `α(Θ(n)) = Θ(α(n))`. Our algorithms run on a fixed vertex type `V` with `|V| = n`, so
   `G(ℓ, β)` is padded with `p` pendant vertices, each with a single arc `padᵩ → x¹₀` (`Vtx.pad`).
   Every spanner must contain these `p` arcs, so the optimum for disjoint inputs grows by `p`; the
   gap then needs larger constants (`156 α < β²` instead of `84 α < β²` in Thm 2.8;
   `q = ⌈34α⌉ + 1` instead of `⌈7α⌉ + 1` in Thm 1.1). No monotonicity assumption on `α` or `T` is
   needed. With `p = 0` the gadget is exactly the paper's graph (`lemma_2_3`, `lemma_2_6`).
2. **Concrete bounds instead of `Ω`.** Thm 2.8 is `⌊n/(2β+5)⌋ ≤ 18·B·T + 1` for any `β` with
   `156 α < β²` and `β(2β+5) ≤ n` (`theorem_2_8`), or with the explicit `β = ⌊√⌈156α⌉⌋ + 1`
   (`theorem_2_8'`). Thm 1.1 is `κ·⌊√⌊n/8q⌋⌋ ≤ 6·B·T + 1` for `q = ⌈34α⌉ + 1`, `8q ≤ n`
   (`theorem_1_1`). The bandwidth `B` is a parameter; `B = O(log n)` gives the paper's
   `Ω(n/(√α log n))` and `Ω(√n/(√α log n))`. The ranges `α ≤ n/c'` and `α ≤ n/100` become
   `β(2β+5) ≤ n` and `8(⌈34α⌉+1) ≤ n` (other constants, same form).
3. **Randomized CC of disjointness is a hypothesis.** Lemma 2.1 (randomized part,
   Kalyanasundaram–Schnitger / Razborov) is not formalized; it enters Thm 1.1 and Lemma 2.4 as
   `RandDisjLB δ κ` (every private-coin protocol for `¬DISJ_K` with error `≤ δ` uses `≥ κ K` bits;
   coin spaces nonempty, see the pitfall in `wiki/congest-lower-bounds.md`). The deterministic
   Lemma 2.5 (gap disjointness, cited from Kushilevitz–Nisan Ex. 5.5) **is proved**
   (`gapDisj_lowerBound`: `N ≤ 3c`, via a Gilbert–Varshamov code and a fooling set).
4. **Lemmas 2.4 / 2.7 specialised.** The paper states them for an abstract threshold `t`; we state
   them for the family and the concrete threshold `t = 2ℓβ + 2ℓ² + 3ℓ + p` (the number of non-`D`
   arcs, which bounds the optimum for disjoint inputs). The gap condition is `α·t < β²`
   (randomized) and `12·α·t < β²ℓ²` (deterministic), exactly what the paper uses.
5. **Model of the distributed problem.** Deterministic synchronous CONGEST from CSLib
   (`Cslib.Congest.Algorithm`), IDs = vertex names, `B`-bit messages. A digraph is a loopless arc
   set `E` whose underlying graph `net E` is the (connected) network; node `v` knows the
   directions of its incident arcs (`view E v`). Each node selects incident arcs (`pick`), and the
   output spanner is the union (`outArcs`), as in §1.5. Algorithms are only required to be correct
   on loopless digraphs with connected underlying network (weaker hypothesis than "all digraphs").
   Randomized algorithms: private random strings `r v : ρ` (uniform, finite `ρ`), failure
   probability `≤ δ` per instance (`failCount`). A `k`-spanner is defined with walks of length `≤ k`
   (equivalent to paths).
6. **Simulation output.** The CSLib simulation theorem only computes "all nodes accept". The
   paper's Alice decides from the number of `D`-arcs output by her nodes; we added
   `LBFamily.simulation_alice` (cost `T·2·|Ecut|·B + 1`) and its randomized version.
7. **Typo.** Proof of Lemma 2.4: "`V_B = Y1, V_A = V \ V_A`" should be `V_A = V \ V_B`.
8. **Approximation range.** The paper assumes `α ≥ 1`; we only need `α ≥ 0` (for `α < 1` the
   hypotheses are unsatisfiable on these graphs, so nothing changes).

No statement of §2 that we formalized is wrong. The proofs go through as written, up to the
routine details above. Decided by R1: none of the items is a false statement or a genuine proof
gap.

## Section 3: weighted 2-spanner vs. minimum vertex cover

9. **Lemma 3.2, proof gap: an extra round is needed.** The proof says that, after the
   simulation, every node computes `C_H` "without any communication". Under the paper's own
   output convention (§1.5: each node outputs incident edges, the spanner is the union), `v`
   cannot know whether `u₂` output the cross edge `{v₁, u₂}`. The communication-free rule "apply
   `C_H` to the edges output by my copies" fails (`localRule_counterexample`): on the triangle, an
   optimal 2-spanner can be output in two ways that give the non-covers `{0}` and `{2}`. Repair:
   one extra round in which every node tells each neighbour whether it output their cross edge.
   We prove `T + 1` rounds with `3B`-bit messages (`lemma_3_2`), and `3(T + 1)` rounds with
   `B`-bit messages via a generic slowdown (`lemma_3_2_congest`; `slow 3`, `slow_run`,
   `slow_out`). The paper claims `3T(3n)`.
   *Verdict call (R1/R6, borderline).* The lemma is a statement, and the exact `3T(3n)` count is
   not established. We did not refute it either: we refuted only the natural local rule, not every
   algorithm. The lemma is used only inside `Ω`-bounds (Thms 3.3/3.4), where `+O(1)` is
   irrelevant. Under the also-common convention that both endpoints learn the output edges, the
   paper's argument is exact. We treat the item as a proof repair (🛠️), not a false claim.
10. **Claim 3.1.** True; the proof is correct. The paper converts `H` into `H'` and asserts
    "`H'` has the same cost". In general only `w(H') ≤ w(H)` holds. For the minimum `H` of Claim
    3.1 this gives equality, but Lemma 3.2 reuses the conversion for an `α`-approximate `H`. There
    `|C_H| ≤ w(H)` is what is needed, and it holds. Our proof
    (`isVertexCover_CH`) works on `H` directly. The middle vertex of a 2-path covering `{v₁, u₂}`
    can be `v₂`, `u₁`, or `w₁` / `w₂` for a common neighbour `w`. In the last case the other path
    edge is a cross edge at `u₂` resp. `v₁`. `C_H` contains `v` iff `{v₁,v₂}` or a cross edge at
    `v₁` or `v₂` is in `H`. We prove `|C_H| ≤ cost(H)` (`ncard_CH_le_cost`) and give an exact
    cover-to-spanner map of cost `|C|` (`HC`, `cost_HC`; it adds the whole triangle of every
    `v ∈ C`, and the extra edges have weight 0). `claim_3_1` states
    `min 2-spanner cost = vertexCoverNum` (`ℕ∞`). `approx_transfer` transfers `α`-approximations.
11. **Model of Lemma 3.2.**
    - CSLib deterministic CONGEST; `V` is fixed, so the paper's `T(3n)` is just `T`.
    - The cross edge is `{v₁, u₂}` for `v < u` (linear order on IDs).
    - Spanner node input: incident `G_S`-edges with weights (`inpS`). Node `v` computes the inputs
      of `v₁, v₂, v₃` from its neighbourhood (`localInpS_eq`).
    - Output: union of the nodes' selections (`spannerOut`).
    - `B > 0` is needed for the extra bit.
    - Correctness is required only on a class `P` of graphs (e.g. connected ones).
12. **Not formalized.** Theorems 3.3/3.4 (consequences of the Kuhn–Moscibroda–Wattenhofer LOCAL
    lower bounds for MVC), Theorems 2.9/2.10 (weighted `k`-spanner), and §§4–6 (algorithms).
