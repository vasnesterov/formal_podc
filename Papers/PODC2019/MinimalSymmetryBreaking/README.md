# Hardness of Minimal Symmetry Breaking — PODC 2019

Alkida Balliu, Juho Hirvonen, Dennis Olivetti, Jukka Suomela. *Hardness of minimal symmetry breaking in distributed
computing.* PODC 2019. DOI [10.1145/3293611.3331605](https://doi.org/10.1145/3293611.3331605). Formalized version:
arXiv 1811.01643v3 (full version with Sections 5–8).

**Verdict: 🛠️ Hard fix.** Every checked statement holds: Lemma 2, the speedup Lemmas 7/8/14/15, Claim 16, the
Ω(log\* n) lower bound for weak 2-colouring (Theorems 6/13), and Θ(log n) for the pointer problem P\* (Theorem 4, with
Lemmas 3, 17, 18). The lower bound needed only local repairs to its proofs, but the algorithm in the proof of Lemma 3,
which the classification of Theorem 5 relies on, is wrong, and we replaced it with a different, correct one. The
classification itself (Theorem 5) and the minimality argument of Section 8.3 were not checked.

## Mistakes in the paper

### ✏️ Slips
- In Claim 11 the recurrence for p̂ is written with ĉ_t; it should be ĉ_{t−1}.
- Section 3.2 defines the distance to a cycle C using ℓ(C) ≈ |C|/2. Section 8.1 uses "the length of the cycle"
  instead.

### Typos
- In the proof of Lemma 2, "u must be *the* closest node of different colour to w" is imprecise under ties. Only the
  distance matters.

## Proof gaps (statements true)

### 🛠️ Lemma 3 (Section 8.1, the P\* algorithm)
The algorithm in the proof of Lemma 3 does not produce a valid P\* labelling: on a 4-cycle of degree-4 nodes with a
leaf hanging on one of them, either tie-break breaks the labelling (condition (3) fails at a, or d(d) ≠ d(a)).

**Impact.** Lemma 3, the upper bound behind Theorem 4 and the homogeneous LCLs, is nevertheless true; we prove it
(and Lemma 17) with a repaired algorithm (`lemma3_repaired`, `lemma17`, `theorem4`).

**Details.** The paper's case analysis for a node v on a cycle C with irr(v) = C only checks that pointers do not
backtrack. It never checks d(v) = d(p(v)) when p(v) chose a *low-degree* irregularity.
- Counterexample (Δ = 4, r = 2): a 4-cycle a, b, c, d of degree-4 nodes with IDs a < b < c < d, a leaf x hanging on
  b, and deep degree-4 trees elsewhere.
  - Node a sees C and x at the same distance 2.
  - b's closest irregularity is x, at distance 1, so d(b) = deg x = 1.
  - If a's tie-break picks C, then a outputs d(a) = 0 and points to b (the orientation goes from the smallest ID a
    toward its smaller neighbour b). Condition (3) fails at a.
  - If the tie-break picks x, then node d points to a with d(d) = 0 ≠ d(a) = 1.
- The alternative reading "cycles take precedence whenever one is within r" fails as well. A degree-Δ node whose
  shortest path to the cycle starts at a degree-< Δ neighbour w points to w with d = 0, while w must output
  (⊥, deg w).
- The claim "each node v on C will have a cycle as their closest irregularity" is false.

**Repair.** The repaired algorithm:
- A node is in *low mode* if its distance to a degree-< Δ node is at most its distance to the set Z of nodes on short
  degree-Δ cycles. Low-mode nodes point towards the nearest low-degree node and copy its degree.
- Otherwise the node is in *cycle mode*: d = 0, pointers lead towards Z, and inside Z each node follows the least (in
  a fixed global order) short cycle through it.
- Both modes are closed under following pointers. Non-backtracking inside Z follows because both endpoints of an edge
  compare the same candidate cycles.

(`lemma3_repaired`, `lemma17`, `theorem4`; analysis scripts in the work notes.)

### 🔧 Claim 10 (proof of Lemma 9, independence)
The proof treats failure events of nodes at pairwise distance ≥ 2t+1 as independent, but a node's failure depends on
its (t+1)-ball, and two such balls intersect when the distance is 2t+1 or 2t+2.

**Impact.** Lemma 9 and Claim 10 are not refuted, and Theorem 13 is unaffected; the exact bound n^{1/(3(2t+1))} of
Claim 10/Lemma 9 is not re-derived (`succProb_le`, `theorem_6`).

**Repair.** We use disjoint (t+1)-balls (distance ≥ 2t+3), which changes the counting. (`succProb_le`, `theorem_6`.)

### 🔧 Claim 10 (proof, step Pr[X | Y] ≤ Pr[X' | Y'])
The step Pr[X | Y] ≤ Pr[X' | Y'] mixes conditionings on different events, and X' (all nodes of B_k(v) succeed) is not
determined by the identifiers in B_k(v), since nodes near the boundary see outside the ball.

**Impact.** The local-to-global bound survives once this step is replaced (`succProb_le`).

**Repair.** We bypass the conditioning step: we choose identifiers that are injective on the central ball by
averaging, and extend them to a bijection. (`succProb_le`, `theorem_6`.)

### 🔧 Lemmas 7/8/14/15 (circular choice of the threshold)
The proofs set f = p'/(5c), where p' is the failure probability of the algorithm built *with threshold f*.

**Impact.** The lemmas hold as stated, and the inequality the paper derives is unchanged (`lemma_14`, `lemma_15`).

**Repair.** We set f from the target bound instead and argue by contradiction. This needs p > 0, which holds on the
infinite tree because of the 0-round bound (`lemma_14`, `lemma_15`, `NodeAlg.failProb_pos`). The lower-bound form
used by Claim 11 needs no fixed point (`nodeLB_succ_of_edgeLB`, `edgeLB_of_nodeLB`).

### 🔧 Lemma 3 (tie-break between cycles)
The tie-break "cycle with the smallest maximum identifier" is ambiguous, because two cycles may share their maximum-ID
node.

**Impact.** Nodes need not agree on the chosen cycle; the repaired algorithm of Lemma 3 does not use this rule.

**Repair.** Any fixed total order on candidate cycles works (`lemma3_repaired`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Lower bound (Sections 5–7).** The network is the consistently oriented Δ = 2k-regular tree, i.e. the Cayley
  graph of the free group on k generators, `Tree k`.
  - Each node has an independent random value from a **finite** probability space (Ω, μ) with arbitrary weights.
    The paper uses infinite random bit strings; ours covers every algorithm that reads finitely many random bits.
  - A t-round anonymous algorithm is a function of the random values in the radius-t ball around the origin. Node v
    applies it to the shifted field, so it knows n and Δ implicitly and has no identifiers.
  - Local failure is evaluated at the origin; all nodes look alike.
- **Finite instances (Claim 10, Theorem 6).**
  - An instance is an n-node set V ⊆ `Tree k` containing the ball of radius K = ⌊log_{2k+1} n⌋/3. Such subtrees
    exist for every n (`theorem_6_instances`). The network is the subgraph induced by V.
  - Identifiers are an injection V → Fin n, i.e. exactly {1..n}. Each node also gets an independent random value.
  - A t-round algorithm (`IdAlg`) sees, within tree distance t, which nodes exist, with their identifiers, random
    values and the orientation. For connected V this is the LOCAL view, and seeing more only strengthens the lower
    bound.
  - Success means every node of V has a neighbour in V with the other colour.
- **Lemma 2 and P\* (Theorem 4).** Deterministic LOCAL in CSLib's extensional form: `Cslib.Local.IsLocal R f`, where
  f maps graph × labels to outputs.
  - Node names serve as identifiers, and n = |V| is known.
  - P\* pointers are neighbour names, which is equivalent to port numbers.
  - The randomized lower bound of Lemma 18 holds for arbitrary random input labels (`lemma18_randomized`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2 (distance-k weak c-colouring → weak 2-colouring, O(1) rounds) | `lemma_2`, `lemma_2_explicit` (k + 2c rounds) | `WeakColoring.lean` |
| Lemma 7 / Lemma 14 (first speedup lemma) | `lemma_14`; inequality `speedup1_ineq` | `Lemmas78.lean`, `Speedup1.lean` |
| Lemma 8 / Lemma 15 (second speedup lemma) | `lemma_15`; inequality `speedup2_ineq` | `Lemmas78.lean`, `Speedup2.lean` |
| Claim 11 / Claim 16 | `claim_16` (via `nodeLB_lb`) | `Chain.lean` |
| Claim 12, first step (0 rounds: p₀ ≥ 1/c^Δ) | `failProb_zero_round` | `Chain.lean` |
| Claim 12 (asymptotics, own constants) | `qT_le_failProb`, `qT_mul_large` | `Theorem6.lean`, `Asymptotics.lean` |
| Claim 10 / Lemma 9 (own constants) | `succProb_le` | `FiniteTree.lean` |
| Theorem 6, Theorem 13 (Ω(log\* n)) | `theorem_6`, `theorem_13`; instances `theorem_6_instances` | `Theorem6.lean`, `Main.lean` |
| Lemma 3 (repaired algorithm) | `lemma3_repaired` | `PointerUpper.lean` |
| Lemma 17 (P\* in O(log n)) | `lemma17` | `PointerUpper.lean` |
| Lemma 18 (P\* needs Ω(log n)) | `lemma18`, `lemma18_lowerBound`, `lemma18_randomized` | `PointerProblem.lean` |
| Theorem 4 (P\* is Θ(log_Δ n)) | `theorem4` | `PointerUpper.lean` |

Infrastructure:
- `Field.lean`: i.i.d. random fields on any node type, with conditioning on a region by resampling. It provides the
  tower property, conditional independence for disjoint regions, invariance of the support, and relabelling.
- `FieldProd.lean`: product and uniform distributions, the collision bound, and averaging.
- `Tree.lean`: free-group geometry of balls.
- `Packing.lean`: ball sizes and separated sets.
- `Subtree.lean`: finite subtrees of every size.

**Not formalized.**
- Theorem 5 and Table 1 (the classification of homogeneous LCLs). They rest on external gap theorems (Appendix A.1).
- The minimality argument of Section 8.3.
- The exact constants of Claim 12, Lemma 9 and the "½ log\* n − 4" claim.

Claims 12 and 16 and the prose of Section 6 ("at least ½ log\* n − 4 rounds") give explicit constants. Their proofs
say "for large enough n", and we did not check these exact constants. We prove the Ω(log\* n) bound with
t ≤ (log\* n − 2k − 15)/2.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
- Non-vacuity: the instances of Theorem 6 exist for every n (`theorem_6_instances`), the speedup bounds are
  instantiated in the chain, and Lemma 2 applies to a concrete non-proper distance-2 weak colouring (`example` in
  `WeakColoring.lean`).
- The LOCAL model and locality come from CSLib `Cslib.Computability.Distributed.Local.Locality`, and `log*` from
  `Cslib.Foundations.Data.Nat.LogStar`.
- `PointerUpper.lean` reuses `SinklessOrientation.lemma_2_2_of_card_le` (PODC 2026 paper folder) for the
  ball-counting step.
- CSLib candidates, marked `-- CSLib candidate` in the code:
  - the random-field layer (`Field.lean`, `FieldProd.lean`);
  - `GLocal`/`tdist` and `TNode`/`tree`/`chain_eq` in the P\* files;
  - `isLocal_map` in `WeakColoring.lean`;
  - the tower lemmas in `Asymptotics.lean`.
