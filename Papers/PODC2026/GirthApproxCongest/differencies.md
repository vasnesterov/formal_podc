# Differences between the formalization and the paper

Chechik, Lifshitz, Mukhtar, *Girth Approximations in the CONGEST Model*, PODC 2026 (arXiv:2603.27601v1), §6.

## Errors and gaps in the paper

1. **Claim 6.2(1) is false as stated (statement, ❌, harmless).** The claim is `girth(G) = 2q/ε · (1 + ε)` for intersecting
   inputs. The proof counts `2q · 1` for the two pipes, but each pipe `r_1 → … → r_q` has `q − 1` edges. The directed
   Claim 6.1 counts this correctly as `2(q − 1) + 2`. The cycle through a shared edge weighs `2(q − 1) + 2q/ε`, so the girth
   is strictly smaller than the stated value (`claim_6_2_value_lt`). We prove `girth ≤ 2(q − 1) + 2·Win`
   (`uGraph_mwc_of_inter`), which is all the reduction uses.
   *Rule.* R1: a numbered stand-alone claim is a statement. R3 does not excuse it, because the proof reasons with the wrong
   count. It is not a headline (R5), so ❌. Borderline: the intended content (an upper bound) is clear and the theorem is
   unaffected. The verdict reflects the letter of the rules.
2. **Claim 6.2(2), proof gap (proof repair).** "Projecting C onto H yields a cycle in H" fails for undirected graphs: a cycle
   can use two Alice edges at `l_1` and two Bob edges at `l_q`, so its projection visits `l` twice. The projection is a
   closed trail. Its edges are distinct because `E_A ∩ E_B = ∅`, and it is non-empty because a cycle cannot lie inside one
   pipe. Its length is still at least the girth of `H` (`egirth_le_card_of_stutter`, via Mathlib's
   `IsCircuit.egirth_le_length`). The directed projection really is a cycle; we use the same circuit argument for both.
3. **Black-box Lemma 4.1 of Das Sarma et al. (verified).** The paper applies it to "the network consisting of the pipes and
   the shortcut tree". We did not assume it. We formalized a general moving-cut simulation (`MovingCutFamily`) and verified
   its hypotheses for the paper's network (`gadgetFamily`). Alice knows column `c` at time `t` iff `c ≤ q − 2 − t`, Bob iff
   `c ≥ t + 1`. Only one tree arc per level enters each shrinking set per round (`card_toA_le`, `card_toB_le`). All nodes
   are covered when `2T + 2 ≤ q` (`cover`). The resulting bound is `q ≤ 2T + 1` or `m ≤ 2T(d + 1)B + 2`, which is
   `Ω̃(min(q, m))`.
4. **Quoted extremal bound (slip, ⚠️-level, not a result of the paper).** §6 states `ex(n, C_{<2k}) = O(n^{1+1/k})`
   (attributed to [3]) and that this is conjecturally tight. For girth `≥ 2k` the exponent is `1 + 1/(k − 1)`. `k = 3` is a
   counterexample: girth-6 graphs with `Ω(n^{3/2})` edges exist (`ex_bound_misquoted`, from `denseHighGirth_three`). The
   paper's later uses (`z(n^{2/5}, C_{<6}) = Θ(n^{3/5})`, §6.2 `m = Θ(a^{1+1/(k−1)})`, "known for `k ∈ {3, 4, 6}`") all use
   the correct exponent.
   *Rule.* R3 typo: the intent is recoverable from §6.0.1 and §6.2, the fix is local, and no proof uses the wrong version.
5. **Vertex count.** "`n^{2/5} · n^{3/5} = n`" ignores the `≈ 2q` tree vertices. Our parameter choice (`aOf`, `qOf`, `dOf`,
   `exists_equiv_vtx`) bounds the tree by `(d + 1)q` and pads with pendant vertices to exactly `n`.

## Modelling choices

* **Network and inputs.** The communication network is the underlying undirected graph. A node's input is its incident arcs
  (with directions and weights). Messages have `B` bits; IDs are the vertex names (`Cslib.Congest.Algorithm`).
* **Output convention.** `ApproxOutput` (from `MinWeightCycleCongest`): some node outputs, and every output lies in
  `[girth, α·girth]`. This is weaker than the paper's "each node computes an approximation", so our theorems are stronger.
  The moving cut covers every node at time `T`, so "all nodes accept" can be evaluated by Alice and Bob jointly.
* **Randomization.** The paper says the lower bounds hold for randomized algorithms "even when shared randomness is
  allowed". We model randomized algorithms with private random strings per node (`failCount`). The simulation needs
  **public** coins, because nodes in the middle are simulated by both players. The randomized theorems are conditional on
  `PubRandDisjLB δ κ`, the public-coin randomized lower bound for set disjointness, which is not formalized. The paper
  itself cites it [16, 24]. Nonempty coin spaces and real `κ` avoid the vacuity pitfall of the companion folder.
* **Directed vs. weighted directed.** The directed theorems require correctness only on *unweighted* digraphs (weights in
  `{0, …, W+1}`, all arcs of weight 1). This covers both unweighted and weighted directed algorithms.
* **Weights (§6.1).** The paper uses weights `1`, `q/ε`, `6q/ε`, which must be integers. We take integer `Win` (input edges)
  and `Wt ≥ k·Win` (tree, leaf and padding edges), under the gap condition `α(2(q − 1) + 2Win) < 2k·Win`. In Theorem 6.2:
  `Win = Mq` with `M = ⌈α/(k − α)⌉ + 1`, `Wt = k·Win`, and weights bounded by `Wm ≥ kMn` (polynomial, as in the paper).
  The paper's `Wt = 6q/ε` also satisfies `Wt ≥ 3·Win`.
  As in the paper's model (§2: weights in `{1, …, c·n^k}`), the weighted algorithms only have to be correct on graphs
  with **positive** weights (hypothesis `∀ u v c, G.wt u v = some c → 0 < c.val` in `hA`); the gadget graphs have
  positive weights (`uComap_pos`).
* **`H`.** Any bipartite graph with girth `≥ 2k` (Mathlib `egirth`). The paper takes an extremal one. Its size enters only
  through `|E(H)|`.
* **Erdős–Simonovits.** `DenseHighGirth k`: for all `a ≥ 1` there is `E ⊆ [a] × [a]` with girth `≥ 2k` and
  `|E| ≥ c·a^{1+1/(k−1)}`. This is the bipartite (Zarankiewicz) form the paper uses. For `k = 3` it is proved
  (`denseHighGirth_three`, points–lines over `ZMod p`, `c = 1/9`). For `k = 4, 6` the paper says "unconditionally"
  (generalized quadrangles and hexagons); we keep the hypothesis there.
* **Shortcut tree.** A balanced binary segment tree with nodes `(h, c)`: level `h ≤ d`, leftmost leaf `c` a multiple of
  `2^h`, with `q ≤ 2^d`. In Theorem 6.2, `d = ⌊log₂ n⌋ + 1`. Arcs go from parent to child and from every layer vertex to its
  leaf, as in the paper. Padding vertices hang below the root (arc root → pad), so they lie on no directed cycle. In the
  weighted case their edges get weight `Wt`.
* **Diameter.** Proved `≤ 2(d + 1)`, i.e. `≤ 2⌊log₂ n⌋ + 4` (`ediam_le`). The paper says `O(log n)`.
* **Asymptotic form.** Theorem 6.2 is stated with explicit constants: there are `C > 0` and `n₀` such that for `n ≥ n₀`,
  `C · n^{k/(2k−1)} ≤ (T + 1)(B + 1)(⌊log₂ n⌋ + 2)`. With `B = Θ(log n)` this is `T = Ω̃(n^{k/(2k−1)})`.
  The parameters are `a = ⌊n^{(k−1)/(2k−1)}⌋` and `q = ⌊n/(2a + d + 1)⌋`.
* **Columns.** The paper's layers `1, …, q` are our columns `0, …, q − 1`.

## Not formalized

* §§3–5 (upper bounds; randomized w.h.p. algorithms).
* The unconditional cases `k = 4, 6` of Theorem 6.2, and the Lazebnik–Ustimenko–Woldar remark (`Ω̃(n^{1/2+β_k})`).
* The randomized communication lower bound for set disjointness (hypothesis `PubRandDisjLB`).
