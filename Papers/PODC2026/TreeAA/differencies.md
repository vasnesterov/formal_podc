# Differences between the formalization and the paper

Paper: Fuchs, Ghinea, Parsaeian, Rybicki, *Round and Resilience-Optimal Approximate Agreement on Trees and
Block Graphs*, PODC 2026 (arXiv 2502.05591v5). Numbering follows the arXiv version.

## Errors and gaps in the paper

1. **Lemma 13, Case 3: the proof is wrong; the statement is true** (proof gap). For a clique output
   `c_out = c` with `v_in ∉ V_G(c)`, the proof takes `c'` = the neighbour of `c` towards `c_b` and claims the
   output (the vertex of `c` closest to `v_in`) is the separator `u ∈ V_G(c) ∩ V_G(c')`. This is false in
   general: the output is the separator towards the party's **own** clique `c_in`, which can be on the side
   of `c_a`. Example: path `x₀ – x₁ – x₂ – x₃`, cliques `{x₀,x₁}, {x₁,x₂}, {x₂,x₃}`, honest clique inputs
   `c_a = {x₀,x₁}` (input `x₀`, this party) and `c_b = {x₂,x₃}`; output `c = {x₁,x₂}`: the closest vertex to
   `x₀` is `x₁`, while the separator towards `c_b` is `x₂`. Corrected proof (formalized): `c` lies between
   `c_in` and one of `c_a, c_b` (tripod property of trees); with `c''` the neighbour of `c` towards `c_in`,
   Lemma 12 shows that the separator `u'' ∈ V_G(c) ∩ V_G(c'')` is the unique closest vertex and lies on a
   shortest path between two honest inputs. (`blockOut_spec`)
2. **Lemma 15: the proof is wrong; the statement is true but not formalized** (proof gap). The proof claims
   that in a minimum-diameter clique tree, a longest path cannot contain four consecutive cliques sharing a
   vertex, because "replacing the subpath by a star strictly decreases the diameter". Replacing the subpath
   only shortens paths through it; another longest path may remain. Counterexample to the claim: `G` = the
   path `x₀ – … – x₆` with two pendant vertices `a, b` at `x₃` (8 maximal cliques). Its clique trees have
   minimum diameter 5 (the six path cliques form a forced path); the tree `e₁–e₂–e₃–e₄`, `e₄–e₅–e₆`,
   `e₄–{x₃a}–{x₃b}` has diameter 5, and its longest path `e₁,e₂,e₃,e₄,{x₃a},{x₃b}` has separators
   `x₁,x₂,x₃,x₃,x₃` (exhaustive enumeration of all 8⁶ labelled trees on the 8 cliques; 16 are clique trees;
   script `scripts/lemma15_check.py`). The bookkeeping at the end is also off by one (`|S| = k`, not `k − 1`; a path with
   `|P_G|` vertices has length `|P_G| − 1`). The statement `D(T) ≤ 2·D(G)` is nevertheless true: the clique tree
   in which, for every cut vertex, the cliques containing it form a star has diameter `≤ 2·D(G)` (along a
   longest path every separator occurs at most twice in a row and never again later, and the end cliques add
   one vertex each), and a minimum-diameter tree is not longer. The proof's step "`P_G` is a path in `G`, hence `|P_G| ≤ D(G)`" also
   needs that `P_G` is a shortest path (true in block graphs: consecutive edges of `P_G` lie in distinct blocks). We did not formalize Lemma 15 (it needs the
   construction of clique trees); Theorem 8 is stated with the round complexity of the tree protocol on the
   subdivided tree `T_S`, and we prove `D(T_S) ≤ 2·D(T)` (`diam_subdiv_le`).
3. **Theorem 7 (authenticated RealAA, `t = c·n`, `c ∈ [1/3, 1/2)`) relies on a false cited theorem** (proof gap,
   statement plausibly true; not formalized). For small `D/ε` the proof uses Theorem 10 (= Theorem 3.1 of [25],
   Ghinea–Liu-Zhang–Wattenhofer PODC 2022) with `t_a = 0`. That theorem is false in synchronous networks when
   `n ≤ 3t_s`: in this project, `Papers/PODC2022/HybridApproxAgreement/` proves that for `n = 3`, `t_s = 1`,
   `t_a = 0` one Byzantine party keeps the honest values at `0` and `1` forever (`AA.theorem_3_1_sync_false`).
   This is exactly the regime `t ∈ [n/3, n/2)` used here. Easy fix: for constant `D/ε` use the Proxcensus-based
   `RealAA₁^PKI` with a constant number `R` of iterations such that `(c′R)^R ≥ D/ε`. Corollaries 3 and 5 depend
   on Theorem 7. Our Theorems 5 and 8 take RealAA as a black box, so they are unaffected.
   Consequently the protocol `RealAA^PKI` defined in the proof of Theorem 7 is itself incorrect for small `D/ε`:
   for `n = 3`, `t = 1` (`c = 1/3`), `D = 1`, `ε = 1/2` the test `log₂((1−2c)/c) + log₂ log₂(D/ε) > 0` fails
   (`0 + 0`), so it runs `RealAA₂^PKI` = `Π_AA` of [25] with exactly the parameters of `AA.theorem_3_1_sync_false`,
   whose honest outputs `0` and `1` are not `ε`-close. Only the existential statement of Theorem 7 survives.
4. **Theorem 2's bound is false for `D/ε < 2` and undefined at `D/ε = 2`** (false only in a degenerate case).
   For `1 < δ = D/ε < 2`, `log₂ log₂ δ < 0`, so `7·log₂ δ / log₂ log₂ δ + 3 < 3`, while RealAA needs at least
   one 3-round iteration when the inputs are not `ε`-close (`theorem2_bound_degenerate`); at `δ = 2` the
   expression divides by `log₂ log₂ 2 = 0`. The proof's iteration count `⌈(20/9) log₂ δ / log₂ log₂ δ⌉` has the
   same issue. For `δ > 2` the arithmetic is correct (`theorem2_iterations`, `theorem2`). In the tree protocols
   `ε = 1` and `D = D(T)` is an integer, so only stars (`D(T) = 2`) hit the degenerate case; the asymptotic
   corollaries are unaffected.
5. **Lemma 12: proof gap; statement true** (`sep_mem_support`, `sep_btw`). The proof says the subtree `T_P`
   "must contain two adjacent clique vertices `d ∈ V(T_c)`, `d′ ∈ V(T_{c′})`", and that "since both belong to
   `T_P`, there exists a vertex `v_i` of the path contained in both". The second step does not follow from the
   first as written; one must use that the crossing happens inside a single clique-tree path between two
   consecutive cliques of the walk, all of whose cliques contain the same walk vertex. Also the cliques
   containing `x` (resp. `y`) need not be on `c`'s (resp. `c′`'s) side a priori. Our proof is an induction along
   the walk with the invariant "all cliques containing the current vertex are on `c`'s side".
6. **Theorem 8's round bound `R_TreeAA(4·D(G))`** uses Lemma 15 (see 2) and silently assumes that
   `R_TreeAA` is monotone in the diameter. We state Theorem 8 with the round bound of the tree protocol on
   `T_S` and prove `D(T_S) ≤ 2·D(T)`.
7. **Lemma 11** is formalized in the form in which Lemma 10 uses it: there is a hull vertex `m` (the one
   closest to `v_start`) whose root path is a prefix of every honest root path (`exists_common_prefix`). This is
   the longest common prefix of the honest paths; we do not define longest common prefixes of lists.
8. **Typos and small slips.**
   * §4.1: "the `k := D(P)` vertices in the path `P`" — a path of diameter `D(P)` has `D(P) + 1` vertices.
   * Proof of Lemma 6: "`1 ≤ i ≤ k_max ≤ D`" — `k_max` (a number of vertices) can be `D + 1`; the honest RealAA
     inputs are still `D`-close, which is what is needed (`close_projIdx`).
   * Proof of Theorem 3: "`R_RealAA(|V(T)|, 1)`" should be `R_RealAA(2·|V(T)|, 1)` as in the statement.
   * Lemma 3.2: the list has exactly `2|V(T)| − 1` entries (the bound `≤ 2|V(T)|` is what is used).
   * Lemma 13, Case 1 applies Lemma 12 without treating the case where an honest input equals the separator
     `u` (trivial: then `u` is itself an honest input).

9. **Lemma 3 and Theorem 3** (`TreeAA0.lean`): no error. The proofs of Lemma 3.3/3.4 are informal but correct;
   Lemma 3.1 does not need `|V(T)| > 1` (the hypothesis is kept but unused); in Theorem 3's validity argument the
   step "`k* ∈ [i_min, i_max]`" needs that the short-path party's own projection index is `≤ k*`. Lemma 4/5 hold
   as stated. The ListConstruction is formalized literally (DFS with children in label order, fuel `|V|`).

## Modelling choices

* **Model.** CSLib's synchronous lock-step Byzantine model (`Cslib.Byzantine.LockStep`): parties `P`
  (`n = |P|`), complete network (`⊤`, no self-messages), deterministic protocols whose state is the full history,
  reliable channels, **static** adversary corrupting a set `B` with `|B| ≤ t` (`atMost t`), messages of Byzantine
  parties arbitrary functions of round, sender and receiver (this covers rushing). The paper's protocols are
  stated against an adaptive adversary; our reductions are proved against a static one (the black-box
  hypotheses are also static). The proofs of the reductions do not use static-ness, but we do not formalize
  adaptive corruption.
* **Authentication.** All protocol theorems are stated for arbitrary ideal-signature structures (`Auth`,
  CSLib), the composed protocol using `Auth.seq`/`Auth.parallel` of the black boxes' structures. With
  `Auth.none` this is the unauthenticated setting. This covers both settings of the paper (`t < n/3` without
  signatures, `t < n/2` with signatures) at the level of the reduction.
* **Black boxes.** Gradecast (Definition 4) and RealAA (Definition 1) are hypotheses on lock-step protocols:
  `SolvesAuthWithin ⊤ alg A (atMost t) pre spec R` = spec holds and every honest party decides within `R`
  rounds in every admissible run whose inputs satisfy `pre`. For RealAA, `pre = Close D` ("honest inputs are
  `D`-close"), matching the paper's `R_RealAA(D, ε)` (properties are only required for `D`-close inputs, a
  weaker hypothesis than the paper's). One gradecast protocol per sender, run in parallel (CSLib
  `Protocol.parallel`).
* **Sequential composition** ("wait until round `R` ends", Section 4.3.2/4.6) is `Protocol.seq A R f B`: phase 2
  starts at round `R` for everybody, with input computed from the first decision of phase 1 (or a default if
  there is none — never the case for honest parties). Messages are tagged by phase (`M₁ ⊕ M₂`).
* **Root.** `v_start`/`v_root` is an arbitrary fixed vertex `r` (the paper picks the lexicographically smallest
  label; any fixed vertex works).
* **Projection** `proj_P(v)`: the first index of `P` at minimal distance to `v` (`projIdx`); in a tree the closest
  vertex of a path is unique, so the tie-breaking is irrelevant.
* **Rounding** `[j] = ⌊j + 1/2⌋` (ties up), exactly as in Section 4.1. Indices are 0-based.
* **Definition 5 (longest supported prefix)** returns `[]` if no prefix is supported; this never happens for
  honest parties (`lsp`, `lsp_spec`).
* **Block graphs.** `IsBlockGraph G`: distinct maximal cliques share at most one vertex. Chordality is provided
  by the clique tree `(T, bag)` given as data (`IsCliqueTree`: bags are exactly the maximal cliques, injectively,
  adjacent bags intersect, running intersection property). Every chordal graph has a clique tree (cited by the
  paper, [10]); we take it as input. The minimum-diameter requirement is only needed for Lemma 15 (not
  formalized). Every party may choose its input clique arbitrarily (`cl : P → V → C`).
* **Lower bound (Theorem 1).** Fekete's chain construction (Lemma 1, cited from [20]) is not formalized; we
  formalize the step that generalizes it to graphs (`exists_consecutive_far`) and the arithmetic deriving the
  `Ω(log D / (log log D + log((n+t)/t)))` bound (`theorem1_rounds`, explicit constant 1/2, for `D(G) ≥ 4`).
* **Theorem 2.** Lemma 16 (Claim 12 of Ben-Or–Dolev–Hoch, the contraction of BDH's RealAA) is a hypothesis; the
  arithmetic is formalized (`theorem2`).
* **Theorem 4** (BDH gradecast, cited) is verified in our model for `3t < n` (`bdhGradecast_solves`): round 0
  the sender sends, round 1 everybody echoes, round 2 "ready" on `n − t` equal echoes (counting the own one, since
  `⊤` has no self-loops), decision at round 3 with thresholds `n − t` (grade 2) and `t + 1` (grade 1); grade-0
  outputs carry the own input as a dummy value.
* **Lemma 12** is proved for any walk without connectivity of `G`; the hypothesis `y ≠ u` is not needed.

