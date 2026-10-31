# Differences between the formalization and the paper

Drucker, Kuhn, Oshman, *On the Power of the Congested Clique Model*, PODC 2014 (10-page author copy;
the "full version" cited for several proofs is not online). Verdict rules refer to
`.claude/skills/formalize-paper/verdicts.md`.

**Verdict ⚠️.** The worst refuted statements hold except in degenerate cases: Lemma 18 at `ℓ = 5`, `N = 4` (R2) and
Theorem 22 at `ℓ = 1` (R2/R3). Theorem 2 and Claim 6 need proof repairs (🛠️). Lemma 21 and Theorem 22 for `ℓ ≠ m`,
and Claim 6 for disconnected `H`, are unestablished but not refuted: their proofs fail, and R1 decides that this is not
a false statement. The borderline call on Lemma 21 is discussed under Section 3.5.

## Models

- **CLIQUE-UCAST** (Section 2): CSLib-candidate `Prog V Bool σ ρ` (phase programs on the congested clique,
  `Podc/Computability/Distributed/CongestedClique/Phases.lean`) with one-bit words; a direct step whose longest
  per-pair list has `w` bits costs `⌈w / B⌉` rounds at bandwidth `B` (`Prog.roundsAt`, `Bandwidth.lean`). Local
  computation is free; a node may "send to itself" (counted, harmless). Initial state of player `v`: its own input
  bits (`inputState`). The protocol may depend on the circuit and the input partition, not on the input.
- **CLIQUE-BCAST** (Section 3): `Bcast.Algorithm V I σ b` (`Broadcast.lean`): synchronous rounds, every node
  broadcasts `b` bits, node input = its adjacency row (`adjInput`). Randomized algorithms: private coins `r v ∈ ρ`
  (uniform, finite) in the node input.
- **CONGEST-UCAST**: CSLib's `Cslib.Congest.Algorithm` (deterministic CONGEST on the input graph, `B`-bit messages).
- **Output convention for detection**: "all nodes accept iff the input graph is `H`-free" (equivalently some node
  reports a copy). The paper says "some player outputs the answer"; the conventions differ by one extra round
  of one bit and do not affect any bound.
- **Copies of `H`**: Mathlib `SimpleGraph.Copy` (injective homomorphisms = not necessarily induced subgraphs
  isomorphic to `H`), as in the paper's "`G` contains a subgraph isomorphic to `H`".

## Section 2 (circuits)

- **Definition 1**: partitions are maps `π : ι → κ` into an arbitrary index type; empty parts are allowed
  (equivalent: `g_j` on an empty part is a constant that `h` can absorb). Only non-input gates need to be separable.
- **Circuits**: DAG given by `wire`, input gates `src`, and a layering `rank` with `wire g h → rank g < rank h`;
  "depth `≤ D`" = `rank ≤ D` (equivalent to "longest path `≤ D`"). Input gates may have in-wires (more general).
  `f : {0,1}^X → {0,1}` with `|X| ≤ n²` (paper: exactly `n²`).
- **Theorem 2, parameter `s`**: the paper sets `s = N / n²` (possibly fractional); we take `s ∈ ℕ` with
  `N ≤ n² s` (so `s ≤ ⌈N/n²⌉`, which changes the bandwidth `O(b + s)` by at most a constant since `b ≥ 1`).
- **Theorem 2, constants** (the theorem has `O(·)`; we give explicit ones): bandwidth `b + 4s + 3`,
  `2D + 4` rounds.
- **Theorem 2, proof (repair, 🛠️ R1)**: the paper's counting is off by a factor 2. The total weight
  `Σ_G (|in G| + |out G|)` is `2N`, not `N`, so (i) "the number of heavy gates (`w ≥ ns`) cannot exceed `n`" is false
  (`heavy_count_counterexample`: `n = 2`, `s = 1`, the path on 5 gates has `4 = n² s` wires and 3 heavy gates), and
  (ii) the contradiction "total weight `> n² s`" in the light-gate assignment does not contradict anything. Repair:
  weight `w(G) = |in G| + |out G| + [G is an input gate]` (total `≤ n²(2s + 1)`), heavy iff `w ≥ n(2s + 1)`,
  light load `≤ 2n(2s + 1)` (`Circuit.exists_assignment`, greedy assignment `exists_greedy_assign`). The `+1` for
  input gates bounds the number of input bits a player receives in the input-routing step (input gates of weight 0
  could otherwise pile up at one player).
- **Theorem 2, routing**: the paper uses Lenzen's routing algorithm; we use oblivious routing (König splitting,
  Dolev–Lenzen–Peled Lemma 1; `exists_oblivious_bw`, `exists_slots`), which suffices since every communication
  pattern of the simulation is fixed in advance. Each stage (and the input routing) is one routed step of 2 rounds.
  Heavy-gate values are sent in every stage to the players that need them (instead of "unless already done").
- **Theorem 4**: the paper writes "cannot be computed by circuits of depth `c · R`" with `c > 1`; the simulation gives
  the contrapositive with depth `R / c`, which we prove (`theorem_4`: depth `D` with `2D + 4 ≤ R`). The literal
  "depth `c·R`, `c > 1`" does not follow from Theorem 2 (typo, R3; not refuted, so it does not affect the verdict).
- Remark 3 (multi-bit outputs), Section 2.1 (matrix multiplication / triangles), the threshold/ACC discussion and the
  counting lower bound of the full version are not formalized.

## Section 3.1 (upper bounds)

- **Claim 6** is proved for **connected `H` with at least one edge** (`claim_6`, `claim_6_isDegenerate`). The proof
  uses "`ex(n, H)` is non-decreasing" and "`ex(2n, H) ≥ 2 ex(n, H)` (two disjoint copies)", both false for some
  disconnected `H`: for `H = K₂ ∪ K₁`, `ex(2, H) = 1 > 0 = ex(3, H)` (`extremalNumber_edge_plus_point`). Claim 6 is
  stated for every graph `H`; for disconnected `H` it is neither proved nor refuted here (a brute force over several
  disconnected forests and `n ≤ 6` found no violation). The doubling step also fails for the forest `2K₂`:
  `ex(3, 2K₂) = 3` (triangle), `ex(6, 2K₂) = 5` (star). Proof gap; the statement is **unestablished** for disconnected
  `H`, not refuted (R1: no statement refuted, so it does not lower the verdict). The paper applies Theorem 7 to
  cycles, cliques, complete bipartite graphs and also "a tree or a forest of a fixed size", so the restriction to
  connected `H` does not cover every use (forests).
- **Remark after Theorem 7**: "If `H` is a tree or a forest of a fixed size, we have `ex(n, H) = O(1)`" is false
  (`ex(n, T) ≥ ⌊n/(h−1)⌋·C(h−1, 2)` for a tree on `h ≥ 3` vertices, disjoint copies of `K_{h−1}`); the intended
  `ex(n, H) = O(n)` is what the stated running time `O(log(n)/b)` needs (typo with evident intent, R3, ⚠️; not
  formalized).
- **Degeneracy**: `IsDegenerate G k` = every nonempty vertex set has a vertex with `≤ k` neighbours inside the set
  (equivalent to the paper's definition).
- **Theorem 7**: the paper uses the one-round algorithm of Becker et al. [2] as a black box. We formalize our own
  version of it: every node broadcasts its degree and an `𝔽₂`-linear sketch of its neighbourhood with
  `m = 2k⌈log₂(n+1)⌉ + 1` bits, the sketch matrix having every `≤ 2k` columns with nonzero sum (counting argument,
  `exists_independent`); a `k`-degenerate graph is the unique graph with these degrees and sketches (peeling,
  `eq_of_sketch`). Nodes decode non-constructively (local computation is free). Rounds `⌈L / b⌉` with
  `L = (2k + 1)⌈log₂(n+1)⌉ + 1`, `k = ⌊4 ex(n, H)/n⌋`: `O((ex(n,H)/n + 1) log n / b)`; the `+1` matters only when
  `ex(n, H) < n` (e.g. `H = K₂`), where the paper's bound would be `0`. Proved for connected `H` with an edge (as
  Claim 6). Only `b ≥ 1`.
- Lemma 8, Theorem 9 (sampling, unknown Turán number), and 4-cycle detection over `G` (full version) are not
  formalized.

## Section 3.2–3.5 (lower bounds)

- **Definition 10**: `LowerBoundGraph H F G'` with `φA, φB : F.Copy G'` (injective homomorphisms, images `F_A`, `F_B`
  not necessarily induced), vertex-disjoint; conditions I and II with (b) "`φA(e)`, `φB(e)` are edges of the copy"
  and (c) "the copy's vertices in `V_A ∪ V_B` are exactly the four endpoints".
- **Observation 11**: proved (`observation_11`).
- **Lemma 13**: the paper says "with constant error probability ... `Ω(|E_F| / (n b))`". We prove the deterministic
  bound `|E_F| ≤ T · n · b + 2` unconditionally (CSLib's `CC(DISJ_K) ≥ K`), and the randomized one
  `C ≤ T · n · b + 2` under the hypothesis `RandDisjLB E_F ε C` (private-coin protocols for `DISJ` with error `ε` need
  `C` bits; `C = Ω(K)` is Razborov / Kalyanasundaram–Schnitger, not formalized). CONGEST part: deterministic
  `|E_F| ≤ T · 2 · |cut| · b + 2` and `δ`-sparse form `|E_F| ≤ 2 T δ n b + 2`, randomized with the same hypothesis.
  In the reduction Alice simulates every node outside `V_B` (the paper: "each player simulating `Θ(n)` nodes";
  balance is irrelevant in BCAST).
- **Lemma 14**: proof deferred to the full version in the paper; we supply it (`lemma_14`). It holds for all
  `N ≥ 1` (paper: `N ≥ 4`). Typo: the universal nodes are `u_1, …, u_{ℓ−4}` (the paper writes `u_{ℓ−1}` in the edge
  list). Padding nodes are isolated.
- **Theorem 15**: `((n − ℓ)/4 + 1)² ≤ T · n · b + 2` for `n ≥ ℓ` (`theorem_15`), real form `T b ≥ n/64 − 2/n` for
  `n ≥ 2ℓ` (`theorem_15_real`), randomized under `RandDisjLB` (`theorem_15_rand`). Remark 16 is covered by
  `lemma_14` (any `ℓ ≥ 4`), not stated separately.
- **Lemma 18 (cycles)** — false for `ℓ = 5`, `N = 4` (⚠️, R2):
  - The paper's statement ("for some extremal `C_ℓ`-free `F` on `N` vertices", every even `N`, `n ≥ ℓN/2`) is
    formalized as `Lemma18Statement`/`Lemma18Concl` and refuted: `lemma_18_false : ¬ Lemma18Concl 5 4 n` for every
    `n`, `not_lemma18Statement`. The only extremal `C₅`-free graph on 4 vertices is `K₄`
    (`isExtremal_top_fin4`, `eq_top_of_isExtremal`), and no `(C₅, K₄)`-lower bound graph exists
    (`no_lowerBoundGraph_C5_K4`). The proof's "if `ℓ` is odd, `ex(N, C_ℓ) = N²/4`" holds only for large `N`.
    Classified ⚠️ (R2): the refuted instance has `N < ℓ`, where every graph on `N` vertices is `C_ℓ`-free (the
    extremal problem is vacuous), and the only use (Theorem 19, `ℓ` fixed, asymptotic in `n`) never needs it; the
    fix (drop "extremal" for odd `ℓ`, or assume `N` large) is local. Borderline: the lemma says "let `N` be an even
    integer". We did not check whether it also fails for some `N ≥ ℓ` with odd `ℓ` (e.g. `ℓ = 7`, `N = 8`, where
    `ex(8, C₇) = 18 > 16 = N²/4`); a failure there would still be a small-`N` corner outside Theorem 19's range.
  - Corrected `lemma_18`: any `C_ℓ`-free `F` on `Fin N` (`N` even), with all edges between `{i < N/2}` and
    `{i ≥ N/2}` when `ℓ` is odd; gives an `N/n`-sparse lower bound graph on `Fin n` for `n ≥ ℓN/2`. Corollaries
    `lemma_18_odd` (`F = K_{N/2,N/2}`, `N²/4` edges) and `lemma_18_even` (extremal `F`, `ex(N, C_ℓ)` edges; the
    paper's statement holds for even `ℓ`: `lemma18Concl_of_even`).
  - Condition II (every `C_ℓ` in `G'` is an intended one) is not argued in the paper; we prove it
    (`CycleLB.lowerBoundGraph`: paths are traversed completely, then length counting).
  - Path lengths: we follow the stated lengths `⌊ℓ/2⌋ − 1` (first `N/2` indices) and `⌈ℓ/2⌉ − 1` edges; the index
    ranges for `u_{i,j}` in the paper (`0 ≤ j ≤ ⌊ℓ/2⌋ − 1`) would give paths 2 edges longer and contradict the
    count `(ℓ − 4)N/2` of extra nodes (typo). The graph is built on its own vertex type and embedded into `Fin n`
    (remaining vertices isolated). Sparsity: the cut puts the `V_B` ends on Bob's side, `≤ N` edges, `δ = N/n`.
  - "If `ℓ` is even, `ex(N, C_ℓ) = Ω(N^{3/2})`": false for even `ℓ ≥ 6` (Bondy–Simonovits:
    `ex(N, C_{2k}) = O(N^{1+1/k})`), but unused; not formalized.
- **Theorem 19**: stated with explicit constants: `ex(n, C_ℓ) ≤ 2ℓ² (T n b + 2)` (BCAST, `theorem_19_bcast`) and
  `ex(n, C_ℓ) ≤ 2ℓ² (2 T N B + 2)`, `N = 2⌊n/ℓ⌋ ≤ 2n/ℓ` (CONGEST, `theorem_19_congest`), for `ℓ ≥ 4`, `n ≥ ℓ`,
  deterministic algorithms. The paper's `Ω(ex(n, C_ℓ)/(nb))` hides the step from `|E_F|` (with `N ≈ 2n/ℓ`) to
  `ex(n, C_ℓ)`; we prove `ex(n, C_ℓ) ≤ 2ℓ² |E_F|` (odd `ℓ`: `ex ≤ n²/2`; even `ℓ`: monotonicity of
  `ex(n, H)/C(n, 2)`, Mathlib's `antitoneOn_extremalNumber_div_choose_two`). Randomized versions follow from
  `lemma_13_bcast_rand` / `lemma_13_congest_rand` in the same way but are not stated separately.
- **Lemma 21 (complete bipartite)** — the construction is wrong for `ℓ ≠ m`:
  - the proof's claim "`L^H` and `R^H` must each include at least two nodes from `V_A ∪ V_B`, as `|W^L| = ℓ − 2`,
    `|W^R| = m − 2` (and no mixing between `W^L`, `W^R` is possible)" ignores that nodes of `W^R` can lie on the
    `ℓ`-side of a (non-induced) copy. For `m = ℓ + 1` and a vertex `k ∈ R` with two `F`-neighbours, `W^R ∪ {u_k}`
    and two `F_A`-neighbours of `u_k` plus `v_k` and `W^L` form a `K_{ℓ,ℓ+1}` that fits no edge of `F`
    (`lemma21_fails_succ`, symmetric `lemma21_fails_succ'`); it uses only Alice's edges and fixed edges, so the
    reduction graph with Bob's input empty contains `K_{ℓ,m}` (Observation 11 fails). For `m ≥ ℓ + 2` (and enough
    vertices) there is even a copy using no `F_A`/`F_B` edge at all, so every instance answers "intersecting"
    (`lemma21_fails_free`). Smallest instance: `ℓ = 2`, `m = 3`, `F` = path `i – k – i'` (`N = 3`, bipartite,
    `C₄`-free, 2 edges `≥ ex(3, C₄)/2 = 3/2`) (`lemma_21_counterexample`, `k21_hypotheses`,
    `extremalNumber_three_cycleGraph_four`).
  - For `ℓ = m` the construction passed brute-force tests for small `F`; not formalized.
  - Lemma 21 is an existence statement; we do not know whether some other `(K_{ℓ,m}, F)`-lower bound graph exists
    for `ℓ ≠ m` in general. For `F = P₃`, `ℓ = 2`, `m = 3` a brute-force search finds 14 valid gadgets on exactly
    `2N + ℓ + m − 4 = 7` vertices (with `φA`, `φB` fixed), so the smallest instance of Lemma 21 is true. Lemma 21 and
    Theorem 22 are therefore **unestablished** for `ℓ ≠ m`, not refuted.
  - **Classification (decides the verdict).** Lemma 21 states only that *some* `(K_{ℓ,m}, F)`-lower bound graph
    exists; "the graph `G'` constructed above is a lower bound graph" is a claim inside its proof. By R1 a false
    claim inside a proof is not a false statement, and R5's "unestablished → ❌" covers results whose proof uses a
    *false* lemma, which is not the case here (Lemma 21 is not refuted). So this item does not make the paper ❌.
    It is a substantial proof failure (the gadget fails for every `ℓ ≠ m` once `F` has a vertex of degree 2, i.e.
    for every `F` the lemma is meant for), not a local gap, and it leaves half of Theorem 22's range without proof.
    Borderline toward ❌ if one counts a refuted construction as a refuted claim; we follow R1 (cf. the ⚠️ verdict of
    SynchronousCounting with an unestablished Theorem 2 constant).
  - Typo: the proof says "assume `n = 4N + ℓ + m − 4`"; the construction has `2N + ℓ + m − 4` nodes (as in the
    statement).
- **Theorem 22**: stated "for any `ℓ, m ≥ 1`". For `ℓ = 1` it is false: `K_{1,m}` (a star) is detected in one round
  with one-bit messages (`starAlg`, `theorem_22_false_of_l_eq_one`). Lemma 21 assumes `ℓ, m ≥ 2`, so the intended
  statement is evident (R3; also R2, star detection is trivial), ⚠️. Symmetrically for `m = 1`. The bound `Ω(√n / b)` also needs `ex(N, C₄) = Θ(N^{3/2})` (not in Mathlib); we did
  not formalize Theorem 22 for `ℓ = m`.
- Section 3.6 (triangles vs. 3-party NOF disjointness, Theorem 24, Corollaries 25–26) is not formalized.
