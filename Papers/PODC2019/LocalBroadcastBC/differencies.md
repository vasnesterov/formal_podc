# Differences between the formalization and the paper

Paper: Khan, Naqvi, Vaidya, *Exact Byzantine Consensus on Undirected Graphs under Local Broadcast
Model*, PODC 2019 / arXiv:1903.11677v2.

**Verdict.** The characterization (Theorems 4.1 and 5.1) is correct for `n ≥ 2`. Theorem 4.1 and
Lemma A.2 are false as stated for `n = 1`, `f = 0`; the paper's standing assumption `f < n` allows
this case. The other points are proof gaps that are easy to fix, imprecisions, and resolved
ambiguities.

## 1. A false statement: Theorem 4.1 / Lemma A.2 for `n = 1`

The paper defines "`G` is `k`-connected" as "`n > k` and removing fewer than `k` nodes does not
disconnect `G`". It assumes `f < n`. Take `n = 1` and `f = 0`. Consensus is trivially solvable:
every node decides its own input. But the single-node graph is not `1`-connected, because
`n > 1` fails. So Lemma A.2 ("consensus solvable ⇒ `(⌊3f/2⌋+1)`-connected") and Theorem 4.1 are
false here.

Lean: `not_theorem_4_1_single_node` (`Counterexample.lean`).

**Cause.** The proof of Lemma A.2 starts: "Suppose `G` is not `(⌊3f/2⌋+1)`-connected … Then there
exists a vertex cut `C` of size at most `⌊3f/2⌋`". This misses the case of a complete graph with
`n ≤ ⌊3f/2⌋ + 1`, which has no vertex cut.

* For `f ≥ 1` this case is excluded by Lemma A.1: minimum degree `≥ 2f` gives `n ≥ 2f + 1 > ⌊3f/2⌋ + 1`.
* For `f = 0` it is the single-node graph.

**Fix.** `lemmaA2` proves what the argument actually shows: there is no vertex cut of size
`≤ ⌊3f/2⌋`. `theorem_4_1` adds the hypothesis `2 ≤ n`. It derives `n > ⌊3f/2⌋ + 1` from Lemma A.1
when `f ≥ 1`, and from `n ≥ 2` when `f = 0`. The final characterization `consensus_iff` assumes
`f < n` and `n ≥ 2`.

The assumption `f < n` is also necessary. For `n = 1`, `f = 1`, consensus is solvable but the
minimum degree is `0 < 2` (`not_degree_single_node`).

The same degenerate case breaks the remark in §4 (p. 4) that "a complete graph consisting of `2f + 1`
nodes satisfies the necessary conditions in Theorem 4.1 for any `f`". For `f = 0` this graph is the
single-node graph, which is not `1`-connected (`n ≤ k`). For `f ≥ 1` the remark is correct
(`complete_iff`, `top_isVertexConnected`).

## 2. Proof gaps and imprecisions in Appendix A (necessity)

* **Lemma A.1, edges of the cover.** Item 4 says that the edges for `u ∈ F²`, `v ∈ W` are "`u→v₀`
  and `uv₁`". It then describes the figure the other way round: "a directed edge from `F²` to `W₁`
  and an undirected edge between `F²` and `W₀`". The executions need the first version: `F²` and
  `W₁` must hear each other in `E₃`. Our cover (`c` in `lemmaA1`) uses it.
* **Lemma A.1, case analysis (a simplification, not a gap).** The paper's steps are correct but not
  needed. The proof first claims (as "easy to show") that every node has
  degree `≥ 1`. It then chooses the partition so that `F² ≠ ∅`. Neither step is needed. The
  disagreement in `E₂` can be between `z` and any node of `F² ∪ W`, and `F² ∪ W ≠ ∅` because
  `|F¹ ∪ {z}| ≤ f < n`. Our proof covers degree-0 nodes uniformly.
* **Lemma A.2.** The edges of the cover are only "deduced from Figure 3". We give them explicitly:
  `C²` listens to `A₀` and `B₁`, `C¹` to `A₀, B₀`, and `C³` to `A₁, B₁`. The part sizes
  `⌊f/2⌋, ⌊f/2⌋, ⌈f/2⌉` are as in the paper.
* **Cover semantics.** In local broadcast, the cover argument needs every Byzantine node to be
  simulated by a *single* node of the cover. Otherwise it could not send the same message to all
  neighbours. The paper uses this tacitly; it holds for both covers. Our general lemma
  `decides_lbScenario_iff` states it as a hypothesis (`LBLift.nbr_τ`).

## 3. Algorithm 1: choices where the paper is ambiguous

These do not affect correctness. The proofs work for any deterministic choice.

* **Message format.** A message is a set of pairs `(b, Π)`. Byzantine nodes may send arbitrary
  sets, including infinite ones and ones with both `(0, Π)` and `(1, Π)`. This only strengthens the
  adversary.
* **"Takes the following steps sequentially".** The paper does not order the pairs inside one
  transmission. If a transmission contains both `(0, Π)` and `(1, Π)`, we accept `0`. Rule (ii)
  ("previously received from `u` a message containing `Π`") becomes "a value along `Π - u` is
  already recorded". Rule (iii) checks `v ∉ Π - u`, which is equivalent because `u ≠ v`.
* **Default message.** A neighbour that sends no `(b, ⊥)` in the first round of a phase is treated
  as having sent `(1, ⊥)` in that round. A later `(b, ⊥)` is then discarded by rule (ii). This
  default is what fixes the timing of flooding for faulty originators (§4 below).
* **Step (c).** If `v` receives `0` along `f+1` node-disjoint paths and also `1` along another `f+1`
  node-disjoint paths, the paper's "then `γ_v := δ`" is ambiguous. We take `0`. By Lemma 5.3 this
  cannot happen in the phase with `F ⊇` faulty nodes.
* **Phases, rounds, output.** Phases follow an arbitrary fixed enumeration of `{F : |F| ≤ f}`, and
  each phase has `n` rounds. A node outputs `γ` at round `|phases| · n`; this is its first and only
  decision.
* **Steps (b)/(c) paths.** In the paper a "path" is a sequence of pairwise adjacent nodes, i.e. a
  walk. Step (c)'s "`f + 1` node-disjoint `A_v v`-paths" are walks in our `Accepts` as well; the
  disjointness and the exclusion of `F` follow the paper's definitions.

## 4. Proof gaps in Section 5 / Appendix B (sufficiency)

* **Step (b) needs simple paths.** The paper lets `P_uv` be "an arbitrary `uv`-path that excludes
  `F`". Here a path may be a walk. If `P_wv` repeats a node `x`, then `x` discards the value
  forwarded back to it by rule (iii). So `v` receives nothing along `P_wv` and puts `w` into `N_v`
  even if `w` flooded `0`. The step "`v` receives 0 along `P_wv` and correctly puts `w` in `Z_v`" in
  the proof of Lemma 5.3 then fails. We require simple paths (`SelSpec`); Lemma 5.4 provides them.
* **Observation B.1 is used in both directions.** It states only *soundness*: a value received along
  a fault-free path is the value broadcast by the origin. The proof of Lemma 5.3 also uses
  *completeness*: along every fault-free *simple* path the value is actually received within the
  `n` rounds of the phase. Completeness depends on the default-message rule and on the round in
  which each path prefix is accepted. Both directions are proved in `floodInv`. The "value
  flooded" by a faulty node is defined explicitly (`fv`): it is what its first-round transmission
  says about `⊥`, which all neighbours receive identically.
* **Lemma 5.5 for faulty `w`.** The proof of Lemma 5.3 applies Lemma 5.5 to an arbitrary `w ∈ B`,
  but Lemma 5.5 is stated only for non-faulty nodes. Its proof does not use non-faultiness, so we
  prove it for every `w` and every `Z` (`PathsExist`). Our proof of Lemma 5.3 does not need
  `A ≠ ∅` separately.
* **Lemma 5.4** cites Menger's theorem, but it follows directly from the definition of
  connectivity. Remove `F \ {u, v}` (at most `f < ⌊3f/2⌋ + 1` vertices) and shortcut the resulting walk to a path
  (`exists_path_excluding`).
* **Lemma 5.5, cases 1/3,** use the fan lemma: "`k`-connected ⇒ `k` node-disjoint `Uv`-paths". We
  prove Menger's theorem and the fan lemma (`Cslib/Foundations/Combinatorics/SimpleGraph/Menger.lean`). The paper's argument that
  the paths exclude `F` uses that the `f+1` endpoints exhaust `A'_v`. Hence no path passes through
  another node of `A'_v`; we prove this explicitly. In case 2 the bound `|N_v ∩ F| ≤ ⌊f/2⌋` is not
  needed, and case 4 needs only the minimum degree. Both match the paper.

## 5. Model

* **Synchronous lock-step model** (CSLib `LockStep`) with local broadcast as a restriction on both
  honest protocols and the adversary (`IsBroadcast`, `IsLocalBroadcast`). The paper's "FIFO links"
  are subsumed by lock-step rounds. Messages carry the sender's identity.
* **Impossibility quantifies over all broadcast protocols** of a very general kind:
  history-based, with arbitrary message types and possibly no termination bound. Possibility uses
  the concrete Algorithm 1.
* **Validity** is the paper's: the output is the input of some non-faulty node. For binary values
  it is equivalent to CSLib's `BA` validity (`consensus_iff_BA`).

## 6. Not formalized

* Theorem 5.6 / Appendix C: the `O(n)`-round algorithm for `2f`-connected graphs.
* Section 6 / Theorem 6.1 / Appendix D: the hybrid model with `t` equivocating faults.
* Figure 1 examples. The Section 2 remark that on complete graphs the condition is `n ≥ 2f+1` is
  formalized (`complete_iff`).
