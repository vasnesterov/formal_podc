# Differences between the formalization and the paper

Paper: C. Lenzen, *Optimal Deterministic Routing and Sorting on the Congested Clique*, PODC 2013
(arXiv:1207.1852v4).

## Errors and gaps in the paper

1. **Theorem 3.7, non-square case: the reduction fails** (proof gap; the statement is true).
   Here `s = ⌊√n⌋` and the sub-instances are on `V₁ = {1..s²}`, `V₂ = {n−s²+1..n}` and
   `V₃ = {1..n−s²} ∪ {s²+1..n}`.
   - (a) The claim "every message not inside `V₁` or `V₂` goes from `V₁∩V₃` to `V₂∩V₃` or vice
     versa" fails for `n = 3`: the message 2→2 is handled by nobody (`PaperGaps.coverClaim_false_three`).
     It fails only for `n = 3`: it holds whenever `2s² ≥ n`, i.e. for all `n ≠ 3`
     (kernel-checked for `n ≤ 40` in `coverClaim_small`). *False only in a degenerate case.*
   - (b) Corollary 3.4 needs `|W| ≤ √n`, but `|V₁∩V₃| = n − s²` can be up to `2s`; for `n = 8`,
     `|W| = 4 > √8` (`cor34_size_fails_eight` records only this arithmetic). *Proof gap*: the helper announcements need
     `|W|² ≤ 4n` slots, i.e. 4 numbers per message.
   - (c) Corollary 3.4 needs exactly `f|W|` messages per node, `f = ⌊n/|W|⌋`. After the two
     redistribution rounds a node of `V₁∩V₃` may hold up to `n > f|W|` messages, e.g. for `n = 7`
     (`cor34_load_fails_seven` records only the set identities and the counting `21 > 3·6`, not a full
     execution). *Proof gap*; the "at most `n`" version of Corollary 3.3 suffices.
   - (d) The instances on `V₁`/`V₂` (`s²` nodes) are fed up to `n > s²` messages per node. The
     square algorithm is designed for `s²`. The paper's "factor 2" refers to running the `V₁` and
     `V₂` instances in parallel. Its remark after Problem 3.1 (overloaded instances "can be split
     up into smaller ones") partly covers the overload, but the split (which needs coordination to
     keep receiver loads `≤ s²`) is not worked out. *Proof gap.*

   **What we prove instead:** the square algorithm handles loads *at most* `s²`, and we simulate it
   on `⌈√n⌉² ∈ [n, 2n]` virtual nodes, at most two per real node. A virtual node's packets are
   carried in sub-slots of its host's packets (`Simulation.lean`, `Main.theorem_3_7`).
2. **Corollary 3.3: the relays lack routing information** (proof gap / under-specified). The
   intermediate nodes `1..m` (possibly outside `W`) must forward each message to its destination,
   but only nodes of `W` know the pattern. This is fine when the destination is in the message
   header. It is not fine for intermediate targets: Step 5 of Algorithm 2 and Corollary 3.5. We
   attach the target member (and a tag, the target group, in Algorithm 2) to each message (3 slots
   per packet, `c33a`/`c33b`).
3. **Algorithm 4, Step 8 needs global information** (proof gap). A node must know the bucket sizes
   of the other groups to compute global ranks, and Corollary 3.3 for `W = V` needs everyone to know
   all sources and destinations. Neither is announced. We add round 29 (each node broadcasts how
   many keys it holds); the total stays ≤ 37 rounds.
4. **Bundling in Theorem 4.5 / Lemma 4.4** (proof gap, constant factors).
   - Step 6: "receive at most `2n` keys" is true. Our analysis gives the weaker `< 3n` (`load_tgt`),
     which suffices. The paper's justification (`Σ_i|K_{i,j}| < 2n^{3/2}`) is not enough because of
     the ceilings; the bound follows from `⌈|K_{i,j}|/√n⌉ ≤ d_i + 1`.
   - "Bundling up to two keys in each message … receive at most `n` messages" does not follow (a
     node can need about `1.5n` messages with per-sender bundling).
   - Lemma 4.4 uses Corollary 3.4 (exact loads) with upper bounds only.

   We route Step 6 with the routing algorithm on a virtual clique of `4n` nodes (receiver load up to
   `4n`, `RoutingBox.lean`). Inside Algorithm 3 we use Corollary 3.3 with up to 6 keys per edge,
   since buckets have `< 6s²` keys for holdings `≤ 3s²`.
5. **Theorem 4.5, non-square case**: only a sketch in the paper ("work with subsets of size
   `⌊√n⌋`…"). We use the virtual-node simulation (`SortMain.theorem_4_5`, `out r = prim ⌊r/n⌋`).
6. **Typos / slips.**
   - Problem 4.1: "indices `i(n−1)+1, …, in`" should be `(i−1)n+1, …, in`. We use 0-based ranks:
     node `v` gets the ranks in `[vn, (v+1)n)`.
   - Proof of Corollary 3.3: "node `i` receives exactly `f` messages … for node `j`" should be
     exactly one. Likewise "each node will receive exactly one message of each color in the first
     round": node `c` receives messages of colour `c` only. Cosmetic.
   - Lemma 3.6, Step 3 ("announce the number of messages they need to move to each set") must
     announce the counts per destination group. Members cannot know their quota before knowing the
     others' counts.
   - The footnote's "deferred completion" of Step 2 is a transportation problem among group members
     (`exists_transport`, `Setup.q`).
   - Corollaries 3.3/3.4 are stated for exactly `f|W|` messages but applied to fewer (e.g. the
     `|W|²` helper messages). We prove "at most" versions.

## Modelling choices

- **Message size.** "`O(log n)` bits" is modelled as packets with a fixed number of slots (12 for
  routing, 384 for sorting), each carrying one message/key or one number. Numbers are bounded by
  `8n²` (routing) or `32n²` (sorting). Messages and keys are opaque: they can only be forwarded by a
  node holding them. The paper leaves the constant in `O(log n)` unspecified.
- **Algorithms.** Deterministic, in full-information form (`Algorithm`), and may depend on `n`
  (non-uniform), as usual for this model. Local computation is unbounded. Edge colourings
  (König/Birkhoff) are chosen by `Classical.choice` as a function of the known count matrix. This
  is deterministic and every node computes the same colouring, but efficiency (Section 5) is not
  modelled.
- **Problem 3.1.** Formalized in the relaxed form (at most `n` messages per source and per
  destination; the paper says this relaxation is trivial). `theorem_3_7_exact` states the exact
  form. Messages carry `(src, idx, dst)` headers.
- **Problem 4.1.** Keys are given as `keys : Fin n → Fin n → M` with `M` linearly ordered, and
  must be pairwise distinct (the paper's w.l.o.g., realizable by tie-breaking). "Learn the keys"
  means: hold them at the end.
- **Round counts.** We get 15 (routing) and 32 (sorting) rounds instead of 16 and 37, and state the
  theorems with the paper's 16 and 37 (silent extra rounds).
  - In Algorithm 2, Steps 1 and 3 are merged into one 2-round group announcement followed by a
    1-round broadcast (6 rounds instead of 7).
  - In Algorithm 3, Step 6 uses Corollary 3.3 (2 rounds) instead of 3.4, since Step 5 already
    distributed the counts.
  - Delimiters are broadcast in 1 round with up to 6 keys per packet.
  - One round is added for the layout broadcast (item 3 above).
- **Our version of Algorithm 3** selects every `3s`-th key (holdings `≤ 3s²`) instead of every
  `2s`-th (exactly `2s²`), so the same routine serves Step 3 (`≤ s²` samples per node) and Step 7
  (`< 3s²` keys per node). Buckets have `< 6s²` keys. Delimiters are the first `s − 1`
  every-`s`-th selected keys; the last bucket is unbounded above. This avoids losing keys above the
  last delimiter when a node's maximum is not selected.
- **The spreading in Step 6** of Algorithm 4 is fixed concretely: the key of rank `t` within
  `K_{v,j}` goes to member `t mod s` of group `j`.
- **Group structure.** Nodes are indexed by `Fin s × Fin s` (group, member) via an equivalence;
  general `n` uses virtual nodes (see item 1).

## Not formalized

- Corollary 4.6 (positions among *distinct* keys with repetitions; selection, modes).
- Section 5 (local computation `O(n log n)`, memory; Lemma 5.1, Corollary 5.2, Lemma 5.3,
  Theorem 5.4 with 12 rounds).
- Section 6 (other bandwidth / key-size / key-number regimes).
