# Hardness of Distributed Optimization — PODC 2019

Nir Bachrach, Keren Censor-Hillel, Michal Dory, Yuval Efron, Dean Leitersdorf, Ami Paz. *Hardness of
Distributed Optimization.* PODC 2019. DOI [10.1145/3293611.3331597](https://doi.org/10.1145/3293611.3331597).
Formalized version: arXiv [1905.10284](https://arxiv.org/abs/1905.10284) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** The near-quadratic CONGEST lower bounds of Section 2 hold: we formalize them for minimum
dominating set (Thm 2.1), directed Hamiltonian path and cycle (Thms 2.2, 2.3), Steiner tree (Thm 2.7) and weighted
max-cut (Thm 2.8), with the deterministic framework (Theorem 1.1, including `CC(DISJ) ≥ K`) proved. Every gadget lemma
is true; the dominating-set and Steiner-tree proofs need local repairs, but Claim 2.2 for Hamiltonian path needed a new
proof replacing Claims 2.3–2.5. The undirected variants and Sections 3–5 were not checked.

## Mistakes in the paper

### ✏️ Slips
- Section 2.2.1: the textual construction defines no arcs out of `r_c`, so taken literally `r_0` and `end` both have
  out-degree 0 and no input has a Hamiltonian path (`paperArc_not_hamPath`). The proof of Claim 2.1 goes "from `r_s`
  into `ℓ^{s,k−1}_{q'}`", and Figure 2 draws these arcs. With the arcs `r_c → ℓ^{c,k−1}_q` added, Claims 2.1 and 2.2
  hold (`hamPath_iff`). The partition `V_A/V_B` and `E_cut` are not given; we choose one with `|E_cut| ≤ 24 log k + 1`.
- Section 2.2.1, Claims 2.1 and 2.5: index errors. "`log(k) ≤ s ≤ log(k) − 1`" should end at `2 log k − 1`,
  `r_{log k − 1}` should be `r_{2 log k − 1}`, `choose_s` for `s ≥ log k` tests bit `s − log k` of `j`, and Claim 2.5's
  range excludes the last box.
- Claim 2.7 omits "spanning": `K₄` plus two pendant vertices has a 2-edge-connected subgraph with `n = 6` edges but no
  Hamiltonian cycle. The proof assumes a spanning subgraph, and the claim is true for spanning subgraphs. (Not
  formalized.)
- For `k = 1` there is no crossing edge, so the Steiner-tree graph is disconnected and Claim 2.8 is false; we prove
  Claim 2.8 for `k ≥ 2` (`claim_2_8`). The max-cut weight `2k² log k − k²` is also negative for `k = 1`.
- Claim 2.9: the proof bounds the total weight of the light edges, exactly `16k³ log k − 4k³ + 2k² + |x| + |y|`, by
  `k⁴`, which fails for `k ≤ 64`, so the proof only works for `k ≥ 128`. Claim 2.9 and Lemma 2.4 still hold for every
  `k ≥ 2` (`claim_2_9`, `lemma_2_4`): we prove them with a direct counting inequality valid for every cut instead of
  the exchange arguments of Claims 2.9–2.12.
- Definition 1.1 requires "`P` iff `DISJ = TRUE`"; all constructions give "`P` iff `DISJ = FALSE`".
- In the max-cut construction `|E_cut| = 4 log k + 1`, not only the T/F edges: `C̄_A – C_B` also crosses.
- Proof of Claim 2.10: the edges from `a^j_1` to `A₂` and `N_A` are said to have weight 1, but the `N_A` edge weighs
  `Σ_j x_{i,j}`; only the total at most `k` is used.
- In Lemma 2.3, `E'` should only contain pairs `(u, w) ∈ E`.
- The step "`T(n) = O(n²)` hence `2T(3n) = O(T(n))`" in Lemmas 2.2–2.3 is not a valid inference. The lower bound
  transfers directly anyway. (Not formalized.)

### Typos
- "Three crossing edges" should be two (Claim 2.8).
- `i ∈ [n]` should be `[k]` (bin); `t^j_S` in `bin̄`.
- `b^{j_i}_z` should be `b^{j_z}_z`, plus other index typos in Section 2.4.1.

## Proof gaps (statements true)

### 🛠️ Claims 2.3–2.5 (Hamiltonian path, Claim 2.2)
Claim 2.4 assumes `g_c` is visited before `r_c`, and Claim 2.5 uses an unproved "rows before `s¹₁` are entered from
launch vertices".

**Impact.** Claim 2.2 is true; our proof replaces Claims 2.3–2.5 (`hamPath_iff`).

**Repair.** A new proof with path positions and a classification of the blocks (`claim_2_2`).

### 🔧 Lemma 2.1 (MDS), case "two row vertices in `D`"
The proof claims that `D` contains exactly one of every pair `f^h_S, t^h_S`, which is false
(`paper_intermediate_claim_false`).

**Impact.** The lemma stands; a different case analysis replaces this step (`lemma_2_1`).

**Details.** The proof argues "if `f_A ∈ D` then `f_B ∈ D` to dominate `u_A`", overlooking `u_A ∈ D`.
Counterexample for `k = 2`: with `x = y =` "column `p` all ones",
`D = {a^p_2, b^p_2, u⁰_{A₁}, u⁰_{B₁}, t⁰_{A₂}, t⁰_{B₂}}` dominates `G_{x,y}`, has size `4 log k + 2`, and its
first-layer cycle is covered by `{u_A, u_B}`.

**Repair.** Every 6-cycle holds exactly two vertices of `D`, `D` has exactly one row per side, and the nine possible
two-vertex patterns of a cycle are analysed by `decide`. (`paper_intermediate_claim_false`, `lemma_2_1`)

### 🔧 Lemma 2.1 (MDS), case "`4 log k + 1` gadget vertices, one row vertex in `A₁`"
The conclusion that `B₁` or `B₂` gets exactly `log k` gadget vertices of `D` is not implied by the counts.

**Impact.** The lemma stands; the step needs one extra fact.

**Repair.** The rows of `A₁` outside `D` force `log k` gadget vertices on `A₁`.

### 🔧 Claim 2.8 (Steiner tree), `⇐` direction
The proof joins the two copy-cliques through a crossing edge, assuming that an *arbitrary* minimum dominating set
contains `f⁰_{A₁}, f⁰_{B₁}` or `t⁰_{A₁}, t⁰_{B₁}`, which the Lemma 2.1 counterexample refutes.

**Impact.** The claim holds for `k ≥ 2`, with the repair below (`claim_2_8`).

**Repair.** Use the canonical dominating set of the intersecting index.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous CONGEST on a fixed vertex set `V`; vertex names are the IDs. Exactly `B` bits per edge,
  direction and round. Deterministic, or with private random strings per node. Every node knows its
  neighbourhood (for directed / weighted problems also its incident arcs / weights). The algorithm may
  depend on `V`, which only makes the lower bounds stronger. "Decides `P` in `T` rounds" means: all nodes
  accept iff `P` holds (`Cslib/Computability/Distributed/Congest/LowerBound.lean`).
* Two-party communication: deterministic protocol trees (Kushilevitz–Nisan); private-coin randomized
  protocols are deterministic trees over inputs extended by coins (`Cslib/Computability/CommunicationComplexity/Protocol.lean`,
  `Randomized.lean`).
* Families of lower bound graphs follow Definition 1.1 (`LBFamily`). The cut is given as a finset of
  directed pairs `(a ∈ V_A, b ∈ V_B)` containing all cut edges.
* `k = 2^L`; row indices are `L`-bit strings; inputs `x, y : [k] × [k] → {0,1}`.
* Only the decision versions of the problems are covered ("is there a dominating set of size
  `≤ 4 log k + 2`", …).
* The MDS family contains a disconnected graph (under-specified model, harmless): `G_{0,0}` is disconnected,
  while CONGEST networks are normally connected. All other `G_{x,y}` are connected, and the fooling-set argument
  never uses `(0,0)`. So the lower bound holds even for algorithms that only work on connected graphs.
  (`mdsGraph_zero_not_connected`, `theorem_2_1_connected`)

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| `CC(DISJ_K) ≥ K` (cited in the paper) | `Protocol.disj_lowerBound`, `not_disj_lowerBound(_of_ne_zero)` | `Cslib/Computability/CommunicationComplexity/Protocol.lean` |
| Theorem 1.1 (deterministic: simulation + bound) | `LBFamily.simulation`, `LBFamily.lowerBound`, `LBFamily.not_disj_lowerBound` | `Cslib/Computability/Distributed/Congest/LowerBound.lean` |
| Theorem 1.1 (randomized; `CC^R(DISJ)` as hypothesis) | `LBFamily.rand_simulation`, `LBFamily.rand_lowerBound` | `Cslib/Computability/Distributed/Congest/Randomized.lean` |
| Lemma 2.1 | `lemma_2_1`, `lemma_2_1_le`, `four_mul_add_two_le_card` | `MDS.lean` |
| Theorem 2.1 (`k² ≤ 8TB log k + 2`; `n² ≤ 256(8TB log n + 2)`) | `theorem_2_1`, `theorem_2_1_n` | `MDSTheorem.lean` |
| Theorem 2.1 for connected-only algorithms | `theorem_2_1_connected` | `MDSConnected.lean` |
| Theorem 2.1, randomized | `theorem_2_1_randomized` | `MDSRandomized.lean` |
| False intermediate claim in Lemma 2.1's proof | `paper_intermediate_claim_false` | `MDSCounterexample.lean` |
| Claims 2.1 + 2.2 (with the missing arcs) | `HamPath.claim_2_1`, `HamPath.claim_2_2`, `HamPath.hamPath_iff` | `HamPathSuff.lean`, `HamPathNec.lean`, `HamPathTheorem.lean` |
| Construction as literally written has no Hamiltonian path | `HamPath.paperArc_not_hamPath` | `HamPathTheorem.lean` |
| Theorem 2.2 (`k² ≤ 2T(24 log k + 1)B + 2`; `n²` form) | `HamPath.theorem_2_2`, `HamPath.theorem_2_2_n` | `HamPathTheorem.lean` |
| Claim 2.6, Theorem 2.3 (directed Hamiltonian cycle) | `HamPath.claim_2_6`, `HamPath.theorem_2_3` | `HamPathCycle.lean` |
| Claim 2.8 (`k ≥ 2`) | `claim_2_8` | `Steiner.lean` |
| Theorem 2.7 (`k² ≤ 2T(8 log k + 2)B + 2`) | `theorem_2_7` | `Steiner.lean` |
| Claim 2.9 (all `k ≥ 2`) | `claim_2_9` | `MaxCutLemma.lean` |
| Lemma 2.4 (`≥ M` and `= M`, all `k ≥ 2`) | `lemma_2_4`, `lemma_2_4_eq` | `MaxCutLemma.lean` |
| Theorem 2.8 (`k² ≤ 2T(4 log k + 1)B + 2`) | `theorem_2_8` | `MaxCutTheorem.lean` |

**Not formalized.**
* `CC^R(DISJ) ≥ κ · K` (real `κ`), which is a hypothesis of the randomized statement (over protocols with nonempty
  coin spaces; without nonemptiness it would be degenerate, `hCC_without_nonempty_degenerate`).
* The "computing" (search) versions of the problems.
* The undirected Hamiltonian path/cycle and 2-ECSS results (Lemmas 2.2–2.3, Theorems 2.4–2.5, Claim 2.7).
* Claims 2.10–2.12: replaced by a counting inequality, not checked one by one.
* Section 2.4.2 (approximation algorithm for max-cut), Section 3 (bounded degree), Section 4
  (approximation) and Section 5 (limitations).

**Trust.**
* No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Non-vacuity: the full-information gathering algorithm (`Cslib/Computability/Distributed/Congest/Gather.lean`) decides every graph
  property on connected graphs in `n` rounds. It satisfies the hypothesis of `theorem_2_1_connected`
  (`theorem_2_1_hyp_satisfiable`).
* Brute-force checks under resource caps, before proving:
  * Lemma 2.1: `k = 2` all inputs; `k = 4` all minimal intersecting and all maximal disjoint inputs, by
    monotonicity.
  * Hamiltonian path family: `k = 2`, all inputs.
  * Lemma 2.4: `k = 2`, all inputs.
* The framework (`Cslib/Computability/Distributed/Congest/`) is now in CSLib. `IsDominating G D` is
  `SimpleGraph.IsDominatingSet G ↑D` (`Cslib/Foundations/Combinatorics/SimpleGraph/Ball.lean`).
