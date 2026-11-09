# Deterministic Connectivity in the Broadcast Congested Clique — PODC 2016

Pedro Montealegre, Ioan Todinca. *Brief Announcement: Deterministic Graph Connectivity in the Broadcast
Congested Clique.* PODC 2016. DOI [10.1145/2933057.2933066](https://doi.org/10.1145/2933057.2933066).
Formalized version: arXiv [1602.04095](https://arxiv.org/abs/1602.04095) v3 (June 2017, 5 pages, "Deterministic
graph connectivity in the broadcast congested clique"). It has the content of the brief announcement plus proof
sketches of every result; no longer version exists. Numbering follows it.

**Verdict: 🔧 Easy fix.** All results hold: the deterministic sparse linear sketch (Lemma 1), one-round
`d`-pruning with `O(d log n)` bits (Theorem 2), the `⌈1/ε⌉`-round spanning forest in `BClique[n^ε log n]`
(Theorem 1) and the one-round spanning forest in `BClique_r[n^{1/r} log n]` (Theorem 3). Proposition 2 is
misstated: "girth at least `2r`" must be "girth larger than `2r`". As printed it is false, but the paper only
applies it to a graph of girth `> 2r`. The proof sketch of Theorem 1 stops one round late when `1/ε` is an
integer, which a local change to the stopping rule fixes.

## Mistakes in the paper

### ✏️ Slips
- Proposition 2 (and the proof of Theorem 3) says "girth at least `2r`". It is false for `r = 2`: `K_{m,m}`
  has girth 4 and degeneracy `m = n/2`, not `O(√n)` (`proposition_2_false`). It holds for girth `> 2r`
  (`proposition_2`), and that is what Theorem 3 uses: the text itself notes that `G̃` has no cycles of length
  `≤ 2r`.

## Proof gaps (statements true)

### 🔧 Theorem 1 (stopping rule of the supernode protocol)
The stopping rule "the protocol finishes when every supernode is inactive" can need `⌈1/ε⌉ + 1` rounds. The
counting `n_{t+1} ≤ n_t / n^ε` of active supernodes only gives `n_{⌈1/ε⌉} ≤ 1`, not `0`.

**Impact.** Statement true; repaired by a fixed-round protocol and a sharper count (`theorem_1`).

**Details.** A supernode of round `t` is *active* if it contains at least `n^ε` supernodes of round `t − 1`.
Take `ε = 1` and a connected `G`. In round 1 every node announces all its neighbours (it sees fewer than `n`
supernodes), so after round 1 there is a single supernode `V`. It contains `n ≥ n^ε` supernodes of round 0, so
it is active, and the protocol as described runs a second round. The same happens whenever `1/ε` is an integer
and `n_t` ends at exactly 1. The sketch's other claims are right: an inactive supernode is a connected component,
and inactive supernodes never merge again. This counterexample to the literal stopping rule is a
paper-level argument: the paper's protocol with its "active" bookkeeping is not modelled in Lean, only the
repaired fixed-round protocol is. (The paper defines "active" only for rounds `t > 1`; we read it as `t ≥ 1`,
otherwise round-1 supernodes are never classified and the rule is undefined for `ε = 1`.)

**Repair.** Nodes simply output after `T = ⌈1/ε⌉` rounds. We count *open* supernodes (some edge of `G` leaves
them) instead of active ones. A closed supernode never grows. An open supernode of round `t+1` contains a node
that saw more than `k = ⌈n^ε⌉` foreign supernodes, so it contains at least `k + 1` open supernodes of round `t`.
Hence `o_t (k+1)^t ≤ n`, and `o_T = 0` because `(k+1)^T > k^T ≥ n` (`Supernodes.exists_fiber`,
`Supernodes.card_openComps_mul_pow_le`, `Supernodes.reachable_ann_iff`). Equivalently, one can keep the paper's
count and add: if at most one active supernode is left, it is a component too, since all the others are.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Broadcast congested clique `BClique[b]` = CLIQUE-BCAST `Cslib.CongestedClique.Bcast.Algorithm V I σ b`
  (staged in `Podc/Computability/Distributed/CongestedClique/Broadcast.lean`). It is synchronous, every node
  broadcasts one `b`-bit message per round, deterministic, failure-free, and local computation is free. Nodes
  are `Fin n`, so IDs are `0, …, n−1` and every node knows `n`. The paper allows IDs up to a known
  polynomial `N = poly(n)`; the same protocols work with dimension `N`, which changes the bit bounds by a constant
  factor only (not formalized). The node input in `BClique` is the adjacency row `nbrs G v`. In
  `BClique_r` it is `localView G r v`: the edges of `G` between vertices of the radius-`r` ball of `v`.
- Protocols are written with messages in a finite type `M` (`TAlg`). `TAlg.toBits` turns them into `b`-bit
  algorithms with exactly the same runs whenever `|M| ≤ 2^b` (`TAlg.run_toBits`). Outputs are a fixed function of the
  final local state. In all three protocols it depends only on the broadcast messages, so all nodes output the same;
  the theorems state only that each node's output is correct.
- Message sizes are explicit. Theorem 1 uses `⌈n^ε⌉ · ⌈log₂(n+1)⌉` bits (`theorem_1_bits_le`: at most
  `(n^ε + 1)(log₂(n+1) + 1)`). Theorem 2 uses `pruneBits n d = ⌈log₂((n+1)p)⌉ ≤ (2d+2)⌈log₂(n+1)⌉ + 1`
  (`pruneBits_le`). Theorem 3 uses `pruneBits n s` with `s < n^{1/r} + 1` (`theorem_3_bits`).
- A "spanning forest" is a maximal one (footnote 1): `IsSpanningForest G F` means `F ≤ G`, `F` is acyclic, and
  `F` has the same reachability as `G`.
- The edge order `σ` of Theorem 3 is the paper's lexicographic order (`lexRank`). Propositions 1 and 2 hold for
  any injective edge rank.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (sketch, `p ≤ 2(1+n)^{2d} n`) | `lemma_1`, `sk_injOn`, `sketchPrime_le` | `Sketch.lean` |
| Theorem 2 (one-round `d`-pruning) | `theorem_2`, `pruneBits_le` | `Pruning.lean` |
| reconstruction of `d`-degenerate graphs | `reconstruct_degenerate` | `Pruning.lean` |
| Theorem 1 (`⌈1/ε⌉` rounds) | `theorem_1`, `theorem_1_bits_le` | `Supernodes.lean` |
| Theorem 1, general form (`n < (k+1)^T`) | `Supernodes.bitAlg_isSpanningForest` | `Supernodes.lean` |
| "`G̃` has no cycle of length `≤ 2r`" | `prunedGraph_noShortCycles` | `Cycles.lean` |
| Proposition 1 | `proposition_1`, `connected_iff`, `IsSpanningForest.of_prunedGraph` | `Cycles.lean` |
| Proposition 2 (girth `> 2r`) | `proposition_2` | `Cycles.lean` |
| Proposition 2 as printed: **false** | `proposition_2_false` | `Cycles.lean` |
| locality of `G̃`'s rows | `isHeavy_localView_iff`, `tildeRow_localView` | `Cycles.lean`, `Connectivity.lean` |
| Theorem 3 | `theorem_3`, `theorem_3_bits` | `Connectivity.lean` |

Propositions 1 and 2 are cited from Awerbuch et al. and Drucker–Kuhn–Oshman; we prove both. Theorem 1 does not
need `ε ≤ 1`, and its general form works for any `k ≥ 1` and `T` with `n < (k+1)^T`. Theorem 2's decoder
peels the least remaining node of current degree `≤ d`, and its output is the pruning sequence together with
all edges incident to it.

**Not formalized.** The optimality remark after Theorem 2 (`2^{Ω(nd log n)}` `d`-degenerate graphs), the
Discussion's remarks on bipartiteness and dynamic streaming, and IDs from a polynomial range instead of `[n]`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The theorems are existence statements over all input graphs, with only `r ≥ 1`, `ε > 0` and `n > 0` (for the
bit bounds) as hypotheses. The model is CSLib's / `Podc`'s broadcast congested clique. Girth and the Moore-bound
core (`NoShortCycles.pow_lt_card`) come from CSLib `SimpleGraph/Girth.lean`. `IsDegenerate` comes from
`Papers/PODC2014/CongestedCliquePower/Claim6.lean`.
