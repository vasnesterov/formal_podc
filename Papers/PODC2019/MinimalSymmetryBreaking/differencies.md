# Differences between the formalization and the paper

Paper: Balliu, Hirvonen, Olivetti, Suomela, *Hardness of minimal symmetry breaking in distributed computing*,
PODC 2019, arXiv 1811.01643v3. Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Model

1. **Randomness.** The paper gives each node an infinite sequence of unbiased random bits. We give each node an
   independent value from an arbitrary *finite* probability space (Ω, μ), with any weights.
   - This covers every algorithm that reads a bounded number of random bits; Ω = bit strings of a fixed length with
     the uniform distribution is one instance.
   - Algorithms that read unboundedly many bits are not covered literally.
   - All probabilities are finite sums (`Field.lean`). Conditioning on a region is resampling outside it.
2. **Oriented regular tree.** The 4-regular oriented tree with directions U/D/L/R (Section 5), and the 2k-regular tree
   with k oriented dimensions (Section 7), are modelled as the Cayley graph of the free group on k generators
   (`Tree k`). A t-round anonymous algorithm is a function of the random values within distance t of the origin;
   node v applies it to the field shifted by v. This matches "A(v) depends only on B_t(v)" with the same algorithm
   at every node.
3. **Edge algorithms.** The output of the edge {v, v gᵈ} is `out d (shift v x)`. It is a function of the values
   within distance t of either endpoint and may depend on the dimension d, as in the paper.
4. **Local failure.** Local failure is evaluated at the origin. The paper's "for each node v, Pr[...] ≤ p" is the
   same thing by translation invariance.
5. **Finite instances (Claim 10, Theorems 6/13).**
   - An instance is an n-node set V of nodes of the oriented tree containing the ball B_K, K = ⌊log_{2k+1} n⌋ / 3.
     The network is the induced subgraph.
   - The paper uses "a 4-regular tree of n nodes" whose ball B_k(v) of about n^{1/3} nodes contains no leaf; our
     choice is equivalent up to constants. Subtrees of every size exist (`exists_subtree`, `theorem_6_instances`).
   - `theorem_6` quantifies over all V ⊇ B_K, including disconnected ones; this only strengthens it.
   - The algorithm sees the nodes of V within *tree* distance t, with identifiers, random values and orientation.
     For connected V this is the LOCAL view. It knows n.
   - Identifiers are exactly Fin n (injective on V, |V| = n), as in the paper ("identifiers exactly in {1..n}").
6. **Weak 2-colouring** has output type `Bool`. Success means every node of V has a neighbour in V with the other
   colour.
7. **Lemma 2 and P\*.** These use CSLib's extensional LOCAL locality `IsLocal R f`: the graph and labels within
   radius R determine the output. Node names are the identifiers, and n = |V| is fixed and known.
   - Lemma 2 is proved for arbitrary simple graphs: no degree bound, finiteness or connectivity is needed. The
     algorithm is anonymous.
   - P\*: d(v) ∈ ℕ with d(v) < Δ, and the pointer is the neighbour's name rather than a port number (equivalent).
     deg is the cardinality of the neighbour set.
8. **Δ.** The paper assumes Δ ∈ {4, 6, ...} for P\*. Our P\* results hold for every Δ ≥ 3. The weak-colouring lower
   bound holds for every k ≥ 1 (Δ = 2k ≥ 2).

## Statements

9. **Lemma 2.**
   - Proved as stated (`lemma_2`), with an explicit radius k + 2c (`lemma_2_explicit`).
   - The paper's second step (Cole–Vishkin to 3 colours, then an MIS in a pseudoforest, O(log\* c) rounds) is
     replaced by a greedy MIS over the 2c colour classes of the subgraph of differently-coloured edges (2c rounds).
     Both are O(1) for constant c.
   - Definition 1 is unsatisfiable for k = 0 and for graphs with isolated nodes, where the lemma is vacuous (R2).
10. **Lemmas 7, 8, 14, 15.**
    - Proved as stated for general Δ = 2k (`lemma_14`, `lemma_15`). Δ = 4 gives Lemmas 7 and 8.
    - The exponents of c are Δ/(Δ+1) = 1 − 1/(Δ+1) and 1 − 1/Δ.
    - The palettes are `Finset α × Finset α` (2^{2c} colours) and `Fin k × Bool → Finset β` (2^{Δc} colours).
    - Lemma 7 is stated for a (t+1)-round algorithm, i.e. t ≥ 1 in the paper's indexing.
    - We also prove the inequalities used by the proofs, `speedup1_ineq` (p ≥ (p' − Δcf) f^Δ) and `speedup2_ineq`
      (p ≥ (p' − (Δ−1)cf) f^{Δ−1}), for every threshold f ≥ 0.
11. **Claims 11/16.** Proved (`claim_16`): (p₀/((Δ+1)c₀))^{(Δ+1)^{2t+1}} with p₀ = 1/c₀^Δ, for any c₀ that bounds the
    end of the palette chain c ↦ 2^{Δ·2^{2c}}. The paper's recursion (Claim 11) is `lb`, and `nodeLB_lb` is its
    validity.
12. **Claim 12.**
    - The first step, "a 0-round algorithm fails with probability ≥ 1/c₀^Δ", is proved (`failProb_zero_round`) via
      the power-mean inequality Σ qᵢ^{Δ+1} ≥ c^{−Δ}.
    - The asymptotic part is proved with our own constants (`qT_mul_large`): for 2t + 2k + 15 ≤ log\* n, the local
      failure probability is large compared with the number of independent nodes.
    - The paper's exact statement ("(½log\* n − b − 3)-round algorithms fail with probability ≥ 1/log^{(2b)} n") is
      not checked. Its proof uses "for large enough n", which the statement does not mention. Not checked, so it is
      not part of the verdict.
13. **Claim 10 / Lemma 9.**
    - We prove a variant (`succProb_le`). If every anonymous t-round algorithm with randomness Fin n × Ω fails
      locally with probability ≥ q, then some identifier assignment gives success probability
      ≤ (1−q)^{|S|} + |B_K|²/n, for any S ⊆ B_{K−t−1} with pairwise disjoint (t+1)-balls.
    - With `exists_separated`, |S| ≥ |B_{K−t−1}| / |B_{2t+2}|.
    - The paper's exact bounds (1−p)^{n^{1/(3(2t+1))}} + 1/(2n^{1/3}) and the formula in Lemma 9 are not
      re-derived. Their proof has the independence error below; they are not refuted.
14. **Theorems 6 and 13.**
    - Proved (`theorem_6`, `theorem_13`): constants C, N₀ exist such that for n ≥ N₀ and 2t + C ≤ log\* n, every
      t-round algorithm has success probability < 1/2 under some identifier assignment. So Ω(log\* n) rounds are
      needed for success probability ≥ 1/2.
    - Our C is 2k + 15, so t ≤ ½ log\* n − (k + 7.5).
    - The paper's prose (Section 6) claims "at least ½ log\* n − 4 rounds" for Δ = 4. That additive constant is not
      checked.
15. **Lemma 3.** Proved for a repaired algorithm (`lemma3_repaired`).
    - Radius 6r + 3 (O(r)). "Irregularity within distance r" means a node of degree < Δ within distance r, or a
      cycle of degree-Δ nodes all within distance r. The paper's dist(v, C) = min dist + ℓ(C) ≤ r implies the
      latter.
    - Every such node is P\*-happy. This is "solved in the 1-neighbourhood" read as happiness of the nodes concerned;
      apply it with r + 1 to cover 1-neighbourhoods.
16. **Lemma 17.** Proved (`lemma17`): radius 6⌈log_{Δ−1} n⌉ + 3 for all graphs of maximum degree ≤ Δ on n nodes,
    Δ ≥ 3. The ball-counting step ("every node sees an irregularity within O(log_Δ n)") is Lemma 2.2 of the
    PODC 2026 SinklessOrientation formalization.
17. **Lemma 18.**
    - Proved (`lemma18`): no r-round algorithm solves P\* on both T and T', the balanced Δ-regular tree of radius
      r+1 and its modification with the same node set. The randomized form (`lemma18_randomized`) gives
      Pr[success on T] + Pr[success on T'] ≤ 1.
    - `lemma18_lowerBound` gives n ≤ Δ^{2r+2}, hence Ω(log_Δ n).
    - The paper's T' modification (re-attach a leaf of each depth-(r−1) node below another leaf) is implemented
      literally.
18. **Theorem 4.** `theorem4` combines Lemmas 17 and 18. The upper bound is in log_{Δ−1} n, the lower bound in
    log_Δ n; both are Θ(log n) for fixed Δ.

## Proof repairs (decide the verdict 🛠️)

19. **Lemma 3's algorithm is incorrect** (Section 8.1).
    - Under "closest irregularity by distance": take a 4-cycle a < b < c < d of degree-4 nodes, a leaf x on b, and
      r = 2.
      - Ties going to the cycle: a outputs (p = b, d = 0) while b outputs (p = x, d = 1). Condition (3) fails at a.
      - Ties going to the node: d points to a with d = 0 ≠ d(a) = 1.
    - Under Section 8.1's own definition (distance + full cycle length), the same graph with x three degree-4 steps
      from b and r = 4 also fails.
    - Under "cycles take precedence": a degree-Δ node whose shortest path to a cycle starts with a low-degree
      neighbour w points to w with d = 0, but w is forced to output (⊥, deg w).
    - Root cause: the case irr(p(v)) ≠ C only checks non-backtracking, not d(v) = d(p(v)). The claim "each node v on
      C will have a cycle as their closest irregularity" is false.
    - Scripts: `/home/vasilii/podc-wt/p10/MinimalSymmetryBreaking-work/pstar/lemma3_cex*.py`.
    - Repair: the mode-based algorithm described in the README, `pstarAlg`.
    - **Borderline (R1/R5):** the algorithm appears only inside the proof of Lemma 3 and the lemma is existential,
      so we count this as a proof repair (🛠️), not a false algorithm claim. A reader who counts the algorithm of
      Section 8.1 as a "correctness claim about the paper's algorithm" would get ❌. Lemma 3 is not a headline
      result, so it would not be 🚨.
20. **Claim 10, independence.**
    - The paper takes nodes at pairwise distance ≥ 2t+1 and says their failure events are independent. A node's
      failure depends on its (t+1)-ball, so this needs distance ≥ 2t+3.
    - Repaired with disjoint (t+1)-balls. The resulting count differs from n^{1/(3(2t+1))}; see item 13.
      The packing bound |S| ≥ |B_{K−t−1}| / |B_{2t+2}| (about n^{1/3} / 3^{O(t)}) is far larger than
      n^{1/(3(2t+1))} once t ≥ 1 and n is large. So the paper's count is very likely recoverable with the
      correct spacing; only its derivation is wrong.
    - The step Pr[X|Y] ≤ Pr[X'|Y'] conditions on different events, and X' is not determined by B_k(v). We replace it
      by an averaging argument over identifiers that are i.i.d. on the central ball and conditioned to be injective,
      then extend them to a bijection (`exists_injOn_extend`, `exists_le_of_expect`).
21. **Lemmas 7/8/14/15, threshold choice.**
    - The paper sets f = p'/(5c) (resp. p'/(4c), p'/((Δ+1)c), p'/(Δc)), where p' is the failure probability of the
      algorithm built with threshold f. This is circular.
    - Repaired by choosing f = q/((Δ+1)c) for the target bound q and arguing by contradiction (`lemma_14`,
      `lemma_15`). This needs p > 0, which we prove (`NodeAlg.failProb_pos`, `EdgeAlg.failProb_pos`) from the
      lower-bound chain.
    - Claim 11 only needs the lower-bound forms `nodeLB_succ_of_edgeLB` / `edgeLB_of_nodeLB`, which avoid this.

## Minor imprecisions and typos (not affecting the verdict)

22. In Claim 11 the recurrence for p̂_{t−1} uses ĉ_t; it should be ĉ_{t−1}. Claim 11's bound has exponent 5^{2t+1}
    after 2t steps; this is correct but not tight.
23. Lemma 2's proof: "u must be *the* closest node of different colour to w" fails under ties, but only
    dist(w, ·) = dist(v, u) − 1 is used. The tie-breaking rule is irrelevant; only distances matter.
24. Lemma 3: the tie-break "cycle with the smallest maximum identifier" is ambiguous when two cycles share their
    maximum-ID node. We use any fixed well-order on candidate cycle lists.
25. Section 3.2 defines the distance to a cycle with ℓ(C) = |C|/2 or ⌊|C|/2⌋+1. Section 8.1 says "the length of the
    cycle".

## Not formalized

- Theorem 5 and Table 1 (classification of homogeneous LCLs; they depend on the external Theorems 19–24 in
  Appendix A.1).
- The minimality argument of Section 8.3.
- The exact numeric forms of Claim 12, Lemma 9 and Claim 10, and the "½ log\* n − 4" remark.
