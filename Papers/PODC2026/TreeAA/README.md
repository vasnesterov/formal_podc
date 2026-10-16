# Approximate Agreement on Trees and Block Graphs — PODC 2026

Marc Fuchs, Diana Ghinea, Zahra Parsaeian, Joel Rybicki. *Round and Resilience-Optimal Approximate Agreement
on Trees and Block Graphs.* PODC 2026. DOI [10.1145/3796701.3815967](https://doi.org/10.1145/3796701.3815967).
Formalized version: arXiv [2502.05591](https://arxiv.org/abs/2502.05591) v5; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The reductions are correct: AA on trees reduces to real-valued AA plus
gradecast (Theorems 3 and 5), and AA on block graphs reduces to AA on trees (Theorem 8). We proved them in the
synchronous lock-step model with the black boxes as hypotheses. Some proofs are wrong but the statements hold:
Lemma 13 (validity on block graphs), Lemma 12 and Lemma 15. The authenticated RealAA protocol of Theorem 7 uses, for
small `D/ε`, a protocol of [25] whose correctness theorem is false for `t ≥ n/3`. Theorem 2's round bound fails for `1 < D/ε ≤ 2`.

## Mistakes in the paper

* **Theorem 7 (authenticated RealAA, `t = c·n`, `c ∈ [1/3, 1/2)`) cites a false theorem.** For constant `D/ε` it
  uses Theorem 10, i.e. Theorem 3.1 of [25] (PODC 2022) with `t_a = 0`. That theorem is false in synchronous
  networks when `n ≤ 3t`. This project's formalization of [25] has a run with `n = 3`, `t = 1`, `t_a = 0` in
  which the honest values stay at `0` and `1` forever (`Papers/PODC2022/HybridApproxAgreement/`,
  `AA.theorem_3_1_sync_false`). So the protocol `RealAA^PKI` defined in the proof of Theorem 7 is itself incorrect
  for small `D/ε`: with `n = 3`, `t = 1` (`c = 1/3`), `D = 1`, `ε = 1/2` the test `log₂((1−2c)/c) + log₂log₂(D/ε) > 0`
  fails, so `RealAA^PKI` runs exactly that broken protocol and the honest outputs `0` and `1` are not `ε`-close.
  The statement of Theorem 7 (existence of some protocol) is probably still true: run the Proxcensus-based `RealAA₁^PKI` for a
  constant number `R` of iterations with `(c′R)^R ≥ D/ε`. Corollaries 3 and 5 depend on Theorem 7; our
  reductions use RealAA as a black box and are unaffected. Not formalized.
* **Theorem 2's bound fails in a degenerate range.** For `1 < D/ε < 2` the bound `7 log₂δ / log₂log₂δ + 3` is
  below 3 rounds, i.e. below one iteration. At `D/ε = 2` it divides by zero. The arithmetic is correct for
  `D/ε > 2`. (`theorem2_bound_degenerate`, `theorem2`)
* **Lemma 13, Case 3: wrong proof, true statement.** Case 3 is a clique output `c` that does not contain the
  party's input `v_in`. The proof says the output (the vertex of `c` closest to `v_in`) is the separator between
  `c` and its neighbour towards the honest clique `c_b`. In fact it is the separator towards the party's *own*
  clique. Example: the path `x₀–x₁–x₂–x₃` with cliques `{x₀x₁}, {x₁x₂}, {x₂x₃}`. Take honest inputs `x₀`
  (this party) and `x₃`, and the tree output `{x₁x₂}`. The party outputs `x₁`, while the separator towards
  `{x₂x₃}` is `x₂`. Validity still holds: by the tripod property of trees, `c` lies between the own clique
  and one of the two honest cliques, and Lemma 12 puts the correct separator on a shortest path. (`blockOut_spec`)
* **Lemma 15 (`D(T) ≤ 2·D(G)` for a minimum-diameter clique tree): wrong proof, true statement, not
  formalized.** The proof says that if a longest path passes ≥ 4 consecutive cliques sharing a vertex, then
  "replacing them by a star strictly decreases the diameter". But another longest path may survive the change.
  Counterexample to this step: the path `x₀ … x₆` with two pendant vertices at `x₃`. Exhaustive enumeration
  (`scripts/lemma15_check.py`) finds minimum-diameter clique trees (diameter 5) whose longest path has the
  separators `x₁, x₂, x₃, x₃, x₃`. The final counting is also off by one, and `|P_G| ≤ D(G)` is justified only by "`P_G` is a path" (it holds
  because such a path is a shortest path in a block graph). The statement is still true:
  compare with the clique tree in which the cliques at each cut vertex form a star. Theorem 8's bound
  `R_TreeAA(4·D(G))` rests on this lemma, and also silently assumes `R_TreeAA` is monotone. We state Theorem 8
  with the round bound of the tree protocol on `T_S` and prove `D(T_S) ≤ 2·D(T)`.
* **Lemma 12 (Appendix D): proof gaps, true statement.** The proof assumes the first clique of the walk lies on
  `c`'s side. It also asserts without justification that some walk vertex lies in both cliques of the crossing
  edge. Our proof is an induction along the walk with the invariant "every clique containing the current vertex
  is on `c`'s side". (`sep_mem_support`, `sep_btw`)
* **Lemma 3 (Euler tour) and Theorem 3: sketchy but correct proofs.** Properties 3–4 of Lemma 3 are argued
  informally; Theorem 3's validity step `k* ∈ [i_min, i_max]` needs the unstated remark that the short-path
  party's own projection index is at most `k*`. Lemma 3.1 does not need `|V(T)| > 1`. (`subtree_iff_indices`,
  `exists_median_between`, `treeAA0_spec`)
* **Slips.** §4.1 says "the `k := D(P)` vertices of `P`", but there are `D(P)+1`. The proof of Lemma 6 claims
  `k_max ≤ D`, but in fact `k_max ≤ D+1`; the inputs are still `D`-close. The proof of Theorem 3 writes
  `R_RealAA(|V(T)|,1)` where the statement has `2·|V(T)|`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's synchronous lock-step Byzantine model (`Cslib.Byzantine.LockStep`) on the complete network, with
  `n = |P|` parties. Protocols are deterministic and history-based, and channels are reliable. A **static**
  adversary corrupts at most `t` parties (`atMost t`) and sends arbitrary messages; this covers rushing. The
  paper allows adaptive corruption. Our reductions never use static-ness, but adaptivity is not modelled.
* Ideal signatures are the abstract CSLib tokens (`Auth`), and every theorem holds for arbitrary token
  structures. This covers both of the paper's settings: `t < n/3` unauthenticated (`Auth.none`), and `t < n/2`
  with PKI.
* Black boxes are hypotheses on lock-step protocols. `SolvesAuthWithin … pre spec R` means: the spec holds and
  all honest parties decide within `R` rounds, in every admissible run whose inputs satisfy `pre`.
  * Gradecast (Def. 4): one protocol per sender, run in parallel.
  * RealAA (Def. 1, `ε = 1`): only required for `D`-close inputs (`pre = Close D`), matching `R_RealAA(D, ε)`.
* Sequential composition ("wait until round `R` ends") is `Protocol.seq` in `Podc/LockStep/Sequential.lean`.
  Phase 2 starts at round `R` for everybody.
* Graphs are Mathlib `SimpleGraph`s. The hull `⟨S⟩` is the union of all shortest paths between vertices of `S`
  (`hull`, via `Btw a w b := d(a,w)+d(w,b) = d(a,b)`). A block graph is a graph whose distinct maximal cliques
  share at most one vertex, given together with a clique tree (`IsCliqueTree`); chordality is the existence of
  the clique tree, as in the paper. The root `v_start` is an arbitrary fixed vertex.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2 (projection onto a path meeting the hull) | `lemma2`, `proj_mem_hull` | `Lemmas.lean` |
| Lemma 10 (`PathsFinder`, `t < n/2`) | `pathsFinder_spec` | `Lemmas.lean` |
| Lemma 11 (common prefix ends in the hull) | `exists_common_prefix` | `Lemmas.lean` |
| Lemmas 6–9 (`TreeAAFromPaths`) | `fromPaths_spec`, `close_projIdx` | `Lemmas.lean` |
| **Theorem 5** (`TreeAA` from GC + RealAA, `R_GC + R_RealAA(D(T),1)` rounds) | `treeAA_solves` | `Protocol.lean` |
| Theorem 4 (3-round gradecast, `t < n/3`, cited from BDH) | `bdhGradecast_solves` | `Gradecast.lean` |
| Theorem 5 + Theorem 4 (towards Corollary 2) | `treeAA_bdh_solves` | `Corollaries.lean` |
| Lemma 3 (`ListConstruction` = Euler tour, properties 1–4) | `listConstruction_adj`, `length_listConstruction_le`, `mem_listConstruction`, `subtree_iff_indices`, `exists_median_between` | `TreeAA0.lean` |
| Lemma 4 | `rpath_listConstruction_meets_hull` | `TreeAA0.lean` |
| Lemma 5 (`PathsFinder₀`) | `pathsFinder0_spec` | `TreeAA0.lean` |
| **Theorem 3** (`TreeAA₀`, `R_RealAA(2|V(T)|,1) + R_RealAA(D(T),1)` rounds) | `treeAA0_solves` (value level: `treeAA0_spec`) | `TreeAA0.lean` |
| Lemma 12 (clique-tree edge separator) | `sep_mem_support`, `sep_btw` | `BlockGraph.lean` |
| Lemmas 13–14 (model independent, so also the reduction behind Corollary 6) | `blockOut_spec` | `BlockGraph.lean` |
| **Theorem 8** (`BlockGraphAA`, rounds of the tree protocol on `T_S`) | `blockGraphAA_solves` | `BlockGraph.lean` |
| `T_S` is a tree, `D(T_S) ≤ 2·D(T)` | `subdiv_isTree`, `diam_subdiv_le` | `BlockGraph.lean` |
| Theorem 8 + Theorem 5 (towards Corollaries 4/5) | `blockGraphAA_of_gc_realAA` | `BlockGraph.lean` |
| Theorem 1 (arithmetic, from Lemma 1) and the metric step of Lemma 1 | `theorem1_rounds`, `exists_consecutive_far` | `Bounds.lean` |
| Theorem 2 (arithmetic, from Lemma 16) | `theorem2`, `theorem2_iterations` | `Bounds.lean` |
| Theorem 2 fails for `1 < D/ε < 2` | `theorem2_bound_degenerate` | `Bounds.lean` |

**Not formalized.**
* Fekete's chain construction (Lemma 1, cited), and the contraction of BDH's RealAA (Lemma 16, cited).
* The authenticated RealAA (Theorems 6, 7, 9, 10, cited).
* Lemma 15, and the existence of minimum-diameter clique trees.
* The asynchronous tree protocol of [37] (Corollary 6 is covered only at the level of the reduction).
* The asymptotic corollaries beyond the stated combinations.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity:
* The black boxes are satisfiable. Simple `t = 0` gradecast and RealAA protocols satisfy the hypotheses, and
  instantiate Theorem 5 on a 3-vertex path (`treeAA_nonvacuous`, `NonVacuity.lean`) and Theorem 8 on `K₂`
  (`blockGraphAA_nonvacuous`, `NonVacuityBlock.lean`).
* For `t ≥ 1` the gradecast hypothesis is discharged by the verified BDH gradecast (`treeAA_bdh_solves`).
* The lock-step model, parallel composition and signatures come from CSLib. Sequential composition and wrapping
  are new (`Podc/LockStep/Sequential.lean`, CSLib candidate).
