# Differences between the formalization and the paper

Paper: F. Kuhn, Y. Moses, R. Oshman, *Coordinated Consensus in Dynamic Networks*, PODC 2011,
DOI 10.1145/1993806.1993808. There is no arXiv/full version; we used the 10-page proceedings
version (many proofs are sketches).

## Errors and imprecisions in the paper

1. **Theorem 4.1 is false as stated (quantifier order).** It says: there is an `i ∈ {0,1}` such that
   in *any* execution `(V, E, σ_{V,i})` (all inputs `i`, bound `2n`), no node decides before it has
   heard from everybody. Since `σ_{V,i}` carries the bound `2|V|`, an algorithm may behave
   differently for different `n`. Counterexample (`theorem_4_1_literal_false`, `CountBound.lean`):
   the rule `cexRule` is biased towards `bias N = [⌊N/2⌋ odd]`. It decides `bias N` as soon as it
   has heard an input `bias N`, and otherwise decides `¬bias N` at time `N - 1`. It solves consensus
   for every valid bound `N ≥ n` (`cexRule_consensus`), ignores UIDs and is therefore
   comparison-based (`cexRule_comparisonBased`). With `n = 2` and all inputs `0`, and with `n = 3`
   and all inputs `1`, node `0` decides at time `0`.
   The proof sketch stitches the two bad executions `G₀, G₁` and gives every node the bound `2n`.
   This silently assumes `|V₀| = |V₁| = n`. With `i` allowed to depend on `n` ("for every `n` there
   is an `i`") the theorem and the stitching proof are correct (`theorem_4_1`).
   *Severity:* false statement as written, but the intended per-`n` statement holds.

2. **Definition 3 (dynamic diameter) is vacuous as written.** "`(u, max{0, t'−D}) ↝ (v, t')` for all
   `t' ≤ t`" fails at `t' = 0` for any two distinct nodes, so no graph with `n ≥ 2` has a finite
   dynamic diameter (`not_diamLit`, `UpperBoundsDiameter.lean`). The parenthetical form
   `past(u,t')(t'−D) = V` has the same problem. Read literally, the dynamic-diameter protocol never
   decides early. We use the evident fix: only `D ≤ t' ≤ t` (`DiamUpTo`).
   *Severity:* under-specified definition / typo.

3. **Running time of the dynamic-diameter protocol: the precise claim is false; the final bound
   holds.** The paper says "if we choose `kmax ≥ ⌊n/(D+Δ)⌋`, nodes can stop as early as time
   `n − kmax·Δ − 1`". Its constraint `(k−1)D < n − kΔ − 1` is necessary but not sufficient. To know
   that the diameter was `≤ D` up to time `(k−1)D`, a node must have heard every node's state at
   time `(k−1)D`, which takes until time `kD`. So level `k` fires only when `k(D+Δ) ≤ n − 1`.
   Counterexample (`diamProtocol_counterexample`): the clique on `n = 4` nodes, `D = Δ = 1`,
   `kmax = 2 = ⌊n/(D+Δ)⌋`. This satisfies the protocol's constraint `(k−1)D ≤ n − kΔ − 1`, but not
   the strict version `(kmax−1)D < n − kmax·Δ − 1` stated in the following paragraph (`1 < 1` fails).
   For `D = 1` the strict constraint is equivalent to the correct `k(D+Δ) ≤ n − 1`, so a
   counterexample under the strict reading needs `D ≥ 2`. One exists (`diamProtocol_counterexample_strict`):
   `n = 6`, `D = 2`, `Δ = 1`, `kmax = 2` (`1·2 < 6 − 2 − 1`), the static diameter-2 graph with edges
   `{0,1},{0,2},{0,3},{1,4},{2,4},{3,5},{4,5}`, and node `u = 3` at time `3`. `u` cannot distinguish
   it from the execution whose round 1 is the same graph, round 2 is `{0,1},{0,2},{0,3},{3,5},{4,5}`
   and round 3 is `{1,2},{1,4},{0,3},{3,5},{4,5}` (the Lean instance `h6`; any round-3 graph keeping
   node 3's edges and isolating node 2 from the time-2 holders of node 5's input works). There,
   node 2 has not heard from node 5 by time 3, so no `D' ≤ 3` works, and node 3 has not decided at
   time `3`, whatever `f`. In the clique: no node has decided at time
   `n − kmax·Δ − 1 = 1`, since node `u` cannot exclude that round 1 was a star centred at `u`. What
   is true is `diamProtocol_decides`: with dynamic diameter `≤ D` up to time `kD` and
   `k(D+Δ) ≤ n − 1`, everybody decides by `n − kΔ − 1`. The paper's final bound
   `t < nD/(D+Δ) + Δ` follows (`diamProtocol_time`, with `kmax ≥ ⌊(n−1)/(D+Δ)⌋`).
   *Severity:* false intermediate statement; the stated asymptotic bound survives.

4. **The abstract's `min{O(nD/Δ), n − Ω(nΔ/D)}` holds only up to an additive `Δ`.** The proved bound
   is `nD/(D+Δ) + Δ`. For `Δ ≥ n` the protocol never decides before `n − 1`
   (`diamProtocol_eq_none_of_le`), which is not `O(nD/Δ)`.
   *Severity:* imprecise asymptotic claim, false only in a degenerate regime.

5. **Lemma 6.5 names the wrong node, and the case `s < 0` needs a stronger hypothesis.** For `s ≥ 0`
   the node that cannot distinguish `G` from `G'` is `u_{k+s+1}`, the first node of `P_{k+s}`, not
   `u_{k+s−1}`. The paper's own example `n = 6, k = 0, s = 2, a = 1, b = 2, t = 3` already fails:
   `u_1` distinguishes, `u_3` does not (`lemma_6_5_paper_node_false`). The arc of nodes that can
   distinguish at time `t − b` is `u_{k−a+1..k+a}`, not `u_{k−a..k+a+1}`. For `s < 0` the hypothesis
   `a + b < n − s` must be `a + b < n − |s|`: with `n = 6, k = 0, s = −2, a = 2, b = 4, t = 5`,
   every node distinguishes (`lemma_6_5_neg_false`). Only `s ≥ 0` is used later, so nothing
   downstream breaks. The hypotheses `b < t ≤ n − 1` are not needed.
   *Severity:* typo (node index), plus a false statement in an unused case.

6. **Lemma 6.6: base case omitted, `n ≥ 3` needed.** The base case `n ≤ 2β + 1` is handled as
   `P_k → C → P_{k'}` with Lemma 6.5 (`b = 0`). For `n = 2` the "paths" `P_k` are disconnected,
   so `n ≥ 3` is required. The model section indeed says `|V| > 2`.
   *Severity:* proof gap (statement true) / missing assumption.

7. **Theorem 6.7: typos and constants.** The proof writes `(n/β)^{log₂ e}` twice for
   `(n/β)^{log₂ 3}`. The indistinguishability time can be `T = n − β − 1` instead of `n − 2β − 1`.
   Explicit statement (`theorem_6_7`): with `n ≤ 2^m β`, no node decides by any `t` with
   `t + ⌈n/β⌉·3^{m+1}·Δ ≤ n − 1 − β`. Asymptotic statement (`theorem_6_7_asymptotic`): no node
   decides by `t` whenever `t + 57·Δ^{1/(2+log₂3)} n^{1−1/(2+log₂3)} ≤ n`, assuming `Δ ≥ 1`.
   *Severity:* typos; constants made explicit.

8. **Lemma 6.2 (clear majority).** The proof writes "`(kmax choose 2)`" without the factor `Δ`. The
   statement assumes `Δ ≤ (εn−1)/2` but the proof uses `Δ ≤ (2εn−1)/4` (the former implies the
   latter). The arithmetic needs `Δ ≥ 1`. The formula for `kmax` is
   `⌊√((2εn−1)/Δ) − 1⌋` (the square root is lost in text extraction).
   *Severity:* typos; statement correct.

9. **Lemma 6.3 (approximate Δ-ladder) leaves the level-0 rule implicit.** The rule at time `n − 1`
   (deciding `v` when `Φ^{0,v}` holds) is never written down, but termination and (a)/(b) rely on
   it. Levels with `kΔ ≥ n` must be disabled, otherwise their decision times are negative. With
   these made explicit no hypothesis is missing. Agreement holds even if two levels fire for
   different values, because (c) iterated down to level 0 and (a) force the valency (`LadderSpec.val_eq`).
   *Severity:* under-specified definition.

10. **Lemma 3.1 is about the system with unknown `n`.** This is said in the surrounding text but not
    in the statement. With `n` known, `u` knows `past(u,t)(0) = V` iff `|past(u,t)(0)| = n`.
    *Severity:* imprecise statement.

## Modelling choices

* **Views.** Instead of the view object of Definition 1 we define the relation "same
  full-information view" `Indist G H u t` recursively. At time `0` a node sees its UID, input and
  the a-priori information `N`. At time `t+1` it also sees which nodes were its round-`t+1`
  neighbours and their views at time `t`. This is exactly what a full-information protocol's state
  contains. `Protocol.state_eq_of_indist` proves that the state of *every* deterministic protocol
  (broadcast of a message computed from the state; receivers know the senders' UIDs) is a function
  of this view. Lower bounds are therefore stated for arbitrary *local decision rules*
  `D : DGraph → node → time → Option Bool` (`D G u t = some v`: decided `v` by time `t`). This
  covers all protocols (`Protocol.local_out`).
* **Locality lemma** `indist_of_agree`: `u` cannot distinguish `G` from `H` if they agree on the
  inputs of, and the edges into, all time-nodes in the causal past of `(u, t)`. All
  indistinguishability arguments go through it.
* **Signature.** Nodes are their UIDs (`V : Finset ℕ`). `input : ℕ → α`. The a-priori information
  is a single number `N` given to all nodes: `N = n` for known `n` (`KnownN n`), a dummy `0` for
  unknown `n` (`UnknownN`), and any `N ≥ n` for an upper bound (`BoundN`).
* **Adversary.** Each round is an arbitrary undirected, loopless graph on `V`, connected in every
  round `r ≥ 1` (1-interval connectivity). No failures. Consensus is binary (`Bool`).
* **Knowledge** is defined semantically (`Knows S G u t φ`: `φ` holds at all points of the
  system `S` that `u` cannot distinguish). The similarity component is `Sim S t`, and common
  knowledge is `CK`. Theorem 5.1 is stated as connectivity of the similarity graph, which is the
  form in which the paper uses it.
* **Theorem 5.1** is proved in a stronger form than stated. (1) All executions of size `n` with
  known `n`, *including different UID sets*, are similar at every `t ≤ n − 2`
  (`theorem_5_1_known`). (2) With unknown `n`, *all* executions with at least `t + 1` nodes are
  similar at time `t` (`theorem_5_1_unknown`), which gives the paper's `(G, n−1) ∼ (H, n−1)`.
* **Proof of Theorem 5.1 (hiding).** The sketch's "remove edges by first hiding both endpoints"
  is made precise as a joint induction of two statements. `HideP k` is the paper's hiding claim,
  with "rounds before `t − k` are unchanged". `FreeP k` says that rounds after `t − k` can be
  changed arbitrarily inside the similarity component. Round `t − k` is changed one edge at a time:
  first all new edges are added, which keeps the round connected, then the old ones are removed.
  Each single-edge change hides its two endpoints from a third node, which needs `k + 3 ≤ n`. In the
  hiding step we replace round `t − k` by a star centred at a fresh node `w` instead of the paper's
  "add a star at `w`, then remove the edges leaving `X ∪ {w}`". Any connected graph in which `X`
  only talks to `X ∪ {w}` works. Inputs are changed by hiding a single node at time `0`. UIDs are
  changed by hiding a node at time 0 and renaming it. For unknown `n`, a fresh leaf is attached to
  a node that is hidden at time 1.
* **Δ-coordination** (`Coordinated S Δ D`): if some node has decided by time `t`, every node has
  decided by `t + Δ`. Simultaneous consensus is `Δ = 0`.
* **Comparison-based** (Theorem 4.1): decisions are invariant under renaming the UIDs along a
  strictly increasing map `ℕ → ℕ` (`ComparisonBased`).
* **Lemma 6.4** is proved both as stated (`lemma_6_4_general`, step `i` at time `t + iΔ`) and in
  the "simplified" form used later (`lemma_6_4`, all steps at time `T ≥ t + ℓΔ`).
* **Theorem 6.1**: "no node decides before round `n − Δ − 1`" is formalized as: there is an
  execution in which every decision time `t` satisfies `n ≤ t + Δ + 1`.
* **Upper bounds for simultaneous consensus** (`simKnown`, `simUnknown`) are given explicitly.
  They decide exactly at `n − 1` (known `n`) and at `n` (unknown `n`), so the lower bounds are
  tight. The paper states the known-`n` one and implies the unknown-`n` one.
* **Lemma 6.3** is formalized abstractly. `Φ k v G u` are local predicates evaluated at time
  `N − kΔ − 1`, and `val G` is the valency of the underlying eventual-consensus algorithm (a value
  of some input). Since the `Φ` are local, `K_u Φ = Φ` (`knows_iff_of_local`).
* **Dynamic-diameter protocol**: "knows the input assignment" is `∃ V x̄, K_u(V_H = V ∧ input = x̄)`,
  and "knows ∃D …" is `K_u ∃D …` (as worded), with knowledge taken in `KnownN n`. The decided value
  is `f(V, x̄)` for any `f` with `f(0ⁿ) = 0`, `f(1ⁿ) = 1` (`GoodF`).

11. **Theorem 6.8: the graph `H` and the walk are not specified.** The proof is a short sketch.
    Our reconstruction (`Diameter68.lean`):
    - `H` is the path `0 — ⋯ — (n−1)`, plus a star centred at `a` joined to all `x < a`, plus a star
      centred at `b = n/2 − 1` joined to all `y > b`, with `b − a = D − 2`. Its diameter is `≤ D`.
    - The executions `ex σ p q` use the path in every round, the left star in rounds `≤ p` and the
      right star in rounds `≤ q`.
    - Deleting the left star from a block of rounds is invisible to node `n − 1` at time
      `T = n/2 − 1` (`stepL`). Deleting the right star is invisible to node `0` (`stepR`). The
      blocks have length `D − 1` and the two kinds of deletion alternate in staggered order, so
      `⌈t/(D−1)⌉ + 1` steps turn "`H` for `t` rounds, then the path" into the static path.
    - Two more steps flip the inputs of each half of the path. Lemma 6.4 then gives no decision by
      `t` whenever `t + (⌈t/(D−1)⌉ + 3)Δ ≤ n/2 − 1` (`theorem_6_8`). Equivalently, by
      `t(D−1+Δ) + 4Δ(D−1) ≤ (D−1)(n/2−1)` (`theorem_6_8'`), which is `Ω(nD/Δ)` for `D ≤ Δ + 1`.
    - Side conditions: `2 ≤ D ≤ n/2 + 1`. `D = 1` (the clique) is not covered by this `H`. The
      hypothesis `D = O(Δ)` is not needed for the explicit bound.
    - "`E(r) = E_H` until the first node decides" is formalized as "`G` follows `H` in rounds
      `≤ t` ⇒ no decision by `t`", which is equivalent by locality. Nodes are `{0, …, n−1}`.
    *Severity:* under-specified proof; the statement is true.

## Not formalized

* The remark that the results of Section 5 hold for facts about any time `t` ("cannot become
  common knowledge until time `t + n − 1`"), and the exact (non-approximate) `Δ`-ladder with
  nested `E^{@t}` operators. Only its approximate version, Lemma 6.3, is formalized.
