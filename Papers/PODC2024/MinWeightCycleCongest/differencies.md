# Differences between the formalization and the paper

Paper: V. Manoharan, V. Ramachandran, *Computing Minimum Weight Cycle in the CONGEST Model*,
PODC 2024. The PODC paper gives no lower-bound proofs. It refers to the full version
arXiv:2308.08670v3, which for Theorems 1.2.A/1.4.A refers to [38] = arXiv:2205.14797v2 (§3.1.1,
Lemma 13, Thm 2; §3.1.2, Lemma 14, Thm 6.A). The proofs below are those of [38].

## Proof repairs (statements true)

1. **Constant diameter (Thm 1.2.A, 1.4.A).** Both theorems claim the bound "even on graphs with
   constant diameter". The graphs of Lemmas 13/14 have no such property: for `x = y = 0` they are
   perfect matchings. [38] adds a sink only in its replacement-path proof (§2.1.1).
   *Repair.* Add a vertex `hub` and padding vertices `pad_j`.
   - Directed graphs (`darc`): an arc `v → hub` for every `v ≠ hub`. The hub is a sink and the pads
     are sources, so neither lies on a cycle.
   - Undirected graphs (`uval`): an edge `hub–v` of weight `2w` for every `v ≠ hub`. A cycle through
     the hub uses two hub edges and weighs at least `4w` (`uGraph.weight_ge_of_hub`). With unit
     weights the hub would create triangles of weight 3 and break the reduction.

   Every vertex is adjacent to the hub, so the diameter is `≤ 2` (`ediam_le_two_of_hub`). The hub and
   the pads go to Alice. The cut then has exactly `4k` edges, as [38] states. Decided by R1: the
   claim is a statement; it is true and its proof is repaired → 🛠️.
2. **Lemma 14 for a general heavy weight `w`.** [38] proves Lemma 14 for `w = 2`. It then says the
   weight may be any `w ≥ 2`, so that one must tell `2 + 2w` from `4w`, without further argument.
   The written argument ("bipartite + light edges form a matching ⇒ at most as many light as heavy
   edges ⇒ a cycle with ≥ 6 edges weighs ≥ 9") gives only `3w + 3` for 6-cycles. This is `< 4w` for
   `w > 3`, so it does not give the `(2 − ε)` claim.
   *Repair* (`uGraph.weight_ge`). Light edges are exactly the edges between Alice's and Bob's sides.
   So a cycle has an even number `A` of light edges (`hAeven`, a `ZMod 2` telescoping sum). The
   graph is bipartite, so its length `L` is even (`hlen`). The matching property gives `2A ≤ L`
   (`h2A`). Then `L − A ≥ 4`, except when `L = 4` and `A = 2`. That case forces an element of
   `S_a ∩ S_b` (`uval_four`). Hence the weight is `≥ (L − A)·w ≥ 4w`. Decided by R1: the gap is in a
   proof and the lemma is true → 🛠️.

## Typos and slips (in the proofs of [38]; no effect)

3. Proof of Thm 2 of [38]: "checking if the resulting minimum length cycle has length at least 4".
   This should be "at least 8" (every cycle has length ≥ 4). Proof of Thm 6.A: "weight at least 6"
   should be "> 6" / "≥ 8". The intent is clear from Lemmas 13/14.
4. "Since the cut has `4k` edges": without the hub, the cut of both constructions has `2k` edges
   (`ℓ_i r_i`, `ℓ'_i r'_i`). This only affects constants.
5. Lemma 14's case analysis of 4-cycles lists `ℓ_i ℓ'_j ℓ_p ℓ'_q` but not the all-heavy Bob-side
   cycles `r_i r'_j r_p r'_q`. Both weigh `4w`; the formal proof handles every case uniformly.
6. Lemma 13's proof chases a single cycle "w.l.o.g. starting with `(ℓ_i, r_i)`". We prove instead
   that every directed cycle has length divisible by 4: the levels `ℓ ↦ 0, r ↦ 1, r' ↦ 2, ℓ' ↦ 3`
   increase by 1 along every arc (`dGraph.four_dvd_len`). We then chase only the length-4 case
   (`darc_four`).

## Modelling choices

7. **Model.** We use the deterministic synchronous CONGEST of CSLib (`Algorithm V I σ B`), with
   exactly `B` bits per edge, direction and round, and vertex names as IDs. The paper fixes
   `B = Θ(log n)`. We keep `B` as a parameter and prove `n ≤ 32·B·T + 12`. This bound is explicit;
   the paper's `Ω(n / log n)` is its asymptotic reading for `B = Θ(log n)`.
8. **Inputs.** Arc/edge weights are `Option (Fin (W + 1))` (`none` = no arc), matching the paper's
   `w : E → {0, …, W}`. Node `v` knows the weights of all arcs incident to it, in both directions.
   This is §1.1's "the weight of an edge is known to the vertices incident to it". Directions are
   known to both endpoints.
9. **Cycles.** A simple cycle is a `len`-periodic sequence `ℕ → V` that is injective on a period,
   with consecutive vertices joined by an arc/edge. For digraphs `len ≥ 2`, so 2-cycles `u → v → u`
   count. For undirected graphs `len ≥ 3`. MWC is the infimum of cycle weights in `ℝ≥0∞`, `∞` if
   acyclic. Relabelling invariance: `WDigraph.mwc_comap`, `WGraph.mwc_comap`.
10. **Output convention.** `ApproxOutput α opt o`: some node outputs an estimate, and every estimate
    lies in `[opt, α·opt]`. The paper's algorithms have all nodes output. Its lower bounds are
    claimed "even when only one node is required to know the weight". Our convention covers both.
    The reduction thresholds every estimate at `b` (`thresholdAlg`) and uses CSLib's "all nodes
    accept" convention.
11. **Hypothesis class.** Thm 1.2.A assumes correctness only on *unweighted* digraphs (all weights
    1) whose underlying network has diameter `≤ 2`. So it covers both "weighted" and "unweighted"
    algorithms (§1.2.1). Thm 1.4.A assumes correctness on all weighted graphs of diameter `≤ 2`
    with weight bound `W ≥ W₀ = 2w(α)`. Here `w(α)` is a constant with `α(2w + 2) < 4w`
    (`exists_heavy_weight`), consistent with the paper's `W = poly(n)`.
12. **Approximation factor.** "`(2 − ε)`-approximation for constant `ε > 0`" is formalized as "`α`
    for any `α < 2`" (`α : ℝ≥0∞`). The exact problem is `α = 1`.
13. **All `n`.** Padding vertices (pendant to the hub, on Alice's side) realise every `n` as
    `4k + 1 + p` with `p < 4` (`exists_equiv_vtx`). The bound is proved for every `n`, not only
    along a subsequence.
14. **Randomization.** The paper claims its lower bounds for randomized algorithms. We model a
    randomized algorithm as a deterministic one whose nodes get private random strings `r v : ρ`
    (uniform). Its failure probability is the fraction of `r` on which `ApproxOutput` fails
    (`failCount`). Shared randomness is not modelled. The randomized two-party lower bound for
    disjointness, `CC^R_δ(DISJ_K) ≥ κK`, is the hypothesis `RandDisjLB δ κ` (Razborov;
    Kalyanasundaram–Schnitger) and is not proved. It quantifies over private-coin protocols with
    *nonempty* finite coin spaces `RA`, `RB`. An empty coin space would make every protocol
    vacuously correct, and the hypothesis would then force `κ ≤ 0`
    (`randDisjLB_without_nonempty_degenerate`). With it, `κ·n ≤ 32·B·T + 8 + 4κ`
    (`theorem_1_2_A_rand`, `theorem_1_4_A_rand`).
15. **4-cycle detection (§1.2.1).** "Implicit … is an `Ω̃(n)` lower bound for detecting a directed
    cycle of length `q`, any `q ≥ 4`." We formalize `q = 4` only
    (`directed_four_cycle_lowerBound`). The convention is: some node rejects iff the digraph has a
    directed 4-cycle.

## Not formalized

16. Thm 1.2.B, 1.3.A, 1.4.B (`Ω̃(√n)`, `Ω̃(n^{1/4})` for larger constant factors; they need the
    Das Sarma et al. simulation lemma) and Thm 2.A of the full version (`(2.5 − ε)`, girth). Also
    all upper bounds: Thm 1.2.C, 1.2.D, 1.3.B, 1.4.C, 1.6 and the algorithms of §2–5.
