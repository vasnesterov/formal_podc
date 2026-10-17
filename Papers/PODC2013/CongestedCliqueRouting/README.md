# Optimal Deterministic Routing and Sorting on the Congested Clique — PODC 2013

Christoph Lenzen. *Optimal Deterministic Routing and Sorting on the Congested Clique.* PODC 2013.
DOI [10.1145/2484239.2501983](https://doi.org/10.1145/2484239.2501983). Formalized version: arXiv
[1207.1852](https://arxiv.org/abs/1207.1852) v4 (10 May 2013, the PODC version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** Both headline results hold: routing (Theorem 3.7, 16 rounds)
and sorting (Theorem 4.5, 37 rounds). We prove them for every `n`, with packets of a constant
number of `O(log n)`-bit items, in 15 and 32 rounds. The square case `n = s²` follows the paper's
algorithms. The proofs have gaps that need fixing:
- the non-square case of Theorem 3.7 does not work as written;
- the relay nodes of Corollary 3.3 lack routing information;
- the final step of the sorting algorithm needs global information that no step distributes;
- several "bundling" and "exactly `f|W|` messages" steps are not justified.

## Mistakes in the paper

* **Theorem 3.7, non-square `n`: the reduction is broken (proof gap; the statement is true).** With
  `s = ⌊√n⌋` the proof splits the messages into three sub-instances on `V₁ = {1..s²}`,
  `V₂ = {n-s²+1..n}` and `V₃`. Four things go wrong:
  - The cover claim fails only for `n = 3`: there the message from node 2 to itself belongs to
    none of the sub-instances (`coverClaim_false_three`). For `n ≠ 3` the claim holds, because
    `2⌊√n⌋² ≥ n` (kernel-checked for `n ≤ 40` in `coverClaim_small`, elementary for larger `n`).
  - Corollary 3.4 is applied to `W = V₁ ∩ V₃`, but it requires `|W| ≤ √n`. This fails, e.g., for
    `n = 8`, where `|W| = 4` (the arithmetic is recorded in `cor34_size_fails_eight`).
  - Corollary 3.4 also requires every node to hold exactly `⌊n/|W|⌋·|W|` messages. This fails,
    e.g., for `n = 7`, where up to 21 messages must be spread over 3 nodes holding at most 6 each
    (the set identities and arithmetic are recorded in `cor34_load_fails_seven`; this is not a
    full execution).
  - The square algorithm run on `V₁` (`s²` nodes) is built for `s²` messages per node, but nodes
    can have up to `n > s²` messages inside `V₁`. The paper's "factor 2" accounts for running the
    `V₁` and `V₂` instances in parallel. Its remark after Problem 3.1 (overloaded instances "can be
    split up into smaller ones") partly covers this, but how to split them without coordination
    is not worked out.

  We instead simulate the square algorithm on `⌈√n⌉² ≤ 2n` virtual nodes, at most two per real
  node (`theorem_3_7`).
* **Corollary 3.3: the relay nodes cannot know where to forward (proof gap).** In round 1 the
  messages go to nodes `1..m`, which need not be in `W`. Only nodes of `W` know the routing pattern.
  This is harmless when a message's current target is its final destination, which the message
  header contains. It is not harmless in Step 5 of Algorithm 2 and Step 3 of Algorithm 1
  (Corollary 3.5), where the targets are intermediate. Fix: attach the target (and the target group
  in Algorithm 2) to the message. This costs a constant factor in message size (`c33a`/`c33b`).
* **Algorithm 4, Step 8 needs global information that is never distributed (proof gap; the round
  count survives).** To send a key to the node responsible for its global rank, a node must know
  the sizes of all buckets of the other groups. Corollary 3.3 (with `W = V`) also requires everyone
  to know all sources and destinations. No step announces these counts. We add one round in which
  every node broadcasts how many keys it holds (`P29`). This still fits easily into 37 rounds.
* **Bundling arguments in Theorem 4.5 / Lemma 4.4 (proof gap, constant factors).**
  - Step 6 of Algorithm 4: "receive at most `2n` keys" is true. It follows from
    `⌈|K_{i,j}|/√n⌉ ≤ d_i + 1`, not from the stated bound `Σ|K_{i,j}| < 2n^{3/2}`.
  - "Bundling up to two keys in each message, nodes need to … receive at most `n` messages" does
    not follow. With per-sender bundling a node can need about `1.5 n` messages.
  - Lemma 4.4 applies Corollary 3.4 (exactly `f|W|` messages) where only an upper bound holds.

  We use packets with a few more slots and route Step 6 through the routing algorithm on a virtual
  clique of `4n` nodes, which allows receiver loads up to `4n` (`load_tgt`, `box_spec`).
* **Theorem 4.5, non-square `n`:** the proof is a one-sentence sketch. We prove it by the same
  virtual-node simulation (`theorem_4_5`).
* **Minor slips and under-specified steps.**
  - Problem 4.1 asks for the keys with indices `i(n−1)+1, …, in`; it should be
    `(i−1)n+1, …, in`.
  - Proof of Corollary 3.3: node `i` receives exactly **one** message (not `f`) for each
    destination `j`. The nearby claim "each node will receive exactly one message of each color" is
    also wrong (node `c` receives only messages of colour `c`); this is cosmetic.
  - Lemma 3.6, Steps 2–3: the group-level colouring must be distributed over the group members (a
    transportation problem). The paper hands this to a footnote ("deferred completion"), and Step 3
    should announce counts per destination group.
  - Corollaries 3.3/3.4 are stated for exactly `f|W|` messages per node but used with fewer; this
    needs dummies or an "at most" version (we prove the "at most" version).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Network.** Synchronous congested clique (`Model.lean`) on nodes `Fin n` with known
  identifiers. Algorithms are deterministic and in full-information form: in round `t` node `v`
  computes its packet to each node from its identifier, its input and all packets received so far.
  The algorithm may depend on `n`. No failures, no randomness.
* **Packets.** In every round every node sends every node (itself included) one packet of `B`
  slots. A slot carries one message/key or one number. The theorems fix `B` as an absolute constant
  (12 for routing, 384 for sorting) and bound numbers by `8n²` resp. `32n²`. So packets have
  `O(log n)` bits, as in the paper.
* **Opaque messages and keys.** They can only be forwarded: a node may send only items it holds,
  i.e. its own inputs or items it received (`Holds`, `SortHolds`). Keys can be compared.
* **Routing (Problem 3.1).** Every node sends at most `n` messages and receives at most `n`
  (`Solves`). `theorem_3_7_exact` is the paper's "exactly `n`" version.
* **Sorting (Problem 4.1).** Node `i` gets `n` distinct keys; the key of global rank `r` must reach
  node `⌊r/n⌋` (`SortSolves`). Distinctness is the paper's w.l.o.g. assumption.
* **Proof technique.** Algorithms are built as *intended runs* (global formulas for all packets).
  We then prove that every packet is determined by its sender's view (`IsLocal`, `Knowledge.lean`),
  which yields a genuine distributed algorithm (`synth_sent`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3.2 (König line colouring, matrix form) | `Matrix.exists_perm_decomposition`, `Matrix.exists_split_parts` | `Cslib/Foundations/Combinatorics/Matrix/Birkhoff.lean` (shared) |
| Corollary 3.3 (two-round routing in a group, known pattern) | `mem_tagged_c33`, `C33Unique` | `Primitives.lean` |
| Lemma 3.6, Cor. 3.5, Step 4, Cor. 3.4 (square case: 6+4+1+4 rounds) | `HB_of_inp`, `HB_col`, `HC_of_HB`, `HD_of_HC`, `HE_of_HD` | `SquarePhaseA/BCD.lean` |
| Theorem 3.7, square case, loads ≤ `s²` (15 rounds) | `Setup.square_correct` | `SquareMain.lean` |
| **Theorem 3.7** (all `n`, ≤ `n` messages per node, 16 rounds) | `theorem_3_7`, `theorem_3_7_exact` | `Main.lean` |
| Non-square proof of Thm 3.7: failing claims | `coverClaim_false_three`, `cor34_size_fails_eight`, `cor34_load_fails_seven` | `PaperGaps.lean` |
| Lemma 4.3 (bucket sizes) and its Algorithm 4 analogue | `sum_bucket_le`, `Alg3.sum_bucket`, `sum_K` | `Buckets.lean`, `SortAlg3Spec.lean`, `SortSpec1.lean` |
| Lemmas 4.2, 4.4 (Algorithm 3, 6 rounds) | `Alg3.mem_Bk'`, `Alg3.rk_GA`, `Alg3.isLocal_alg3` | `SortAlg3Spec.lean` |
| Theorem 4.5, square case (32 rounds) | `SortSetup.sort_correct` | `SortSpec2.lean` |
| **Theorem 4.5** (all `n`, 37 rounds) | `theorem_4_5` | `SortMain.lean` |

The round counts are 15 instead of 16 and 32 instead of 37. In Algorithm 2 we merge Steps 1 and 3
into one group announcement. In Algorithm 3 we use Corollary 3.3 instead of 3.4, since the counts
are already known. Delimiters are announced in one round with larger packets.

**Not formalized.** Corollary 4.6 (ranks with repeated keys), Section 5 (local computation and
memory, Theorem 5.4's 12-round variant) and Section 6 (other parameter ranges). Edge colourings are
obtained by `Classical.choice` (deterministic, but not efficiently computable).

**Trust.** No `sorry`; `theorem_3_7`, `theorem_3_7_exact`, `theorem_4_5` and the square-case
theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. Non-vacuity:
`routing_not_zero_rounds` and `sorting_not_zero_rounds` (`Sanity.lean`) show that the
specifications cannot be met without communication. The paper-gap facts are checked by
`decide +kernel`.

König/Birkhoff for ℕ-matrices (splitting into `k` parts, transportation) is shared code in
CSLib, `Cslib/Foundations/Combinatorics/Matrix/Birkhoff.lean`. Remaining CSLib candidates (marked in
the files): `Assign.lean`, `Buckets.lean` (ranks, samples, Lemma 4.3). `Knowledge.lean`,
`Simulation.lean` and `Compose.lean` are specific to the congested-clique model.
