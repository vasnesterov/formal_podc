# Differences between the formalization and the paper

Paper: Koutris, Pagourtzis, *Brief Announcement: k-Shot Distributed Broadcasting in Radio Networks*,
PODC 2010. Formalized version: Karmakar, Koutris, Pagourtzis, Sakavalas, *k-shot Broadcasting in Ad
Hoc Radio Networks*, arXiv:1603.08393v1 (the full version; numbering follows it).
No copy of the brief announcement was available: all differences are relative to the arXiv text.
The general adaptive `k`-shot lower bound (Section 5) is not in the BA (the arXiv text says its
CATS 2011 conference version treated adaptive protocols only for `k = 1`).

## Model (Section 2)

- Nodes are a finite type `V` (labels), `n = Fintype.card V`. A network is a directed relation
  `E u v` ("`u` transmits to `v`") with a source `s`; undirected networks are `E = G.Adj` for a
  `SimpleGraph G`.
- Oblivious protocol = schedule `σ : ℕ → Finset V` (step `t ≥ 1`). The `k`-shot rule
  (`TransmitsAt`): a node informed at step `r` transmits at its first `k` appearances at steps
  `> r`. No spontaneous transmissions, no collision detection; an uninformed node is informed at
  step `t` iff exactly one in-neighbour transmits at `t` (`recvTime`).
- "Running time = worst case over networks" is formalized as: for every schedule there is a
  network on which broadcasting is not complete before the bound. The lower bound does **not**
  assume the protocol is correct: if it fails on some connected network, that network is the
  witness (`theorem_3_3` splits on `CorrectOnUndirected`).
- The paper's `t_i(v,T)`, `t_{≤i}(v,T)` with `shots(v,T) = 0` are undefined; we never use them and
  express "`t_{≤k}(w,T) ≥ X`" as "`w`, informed at `T`, transmits at some step `≥ X`".
- First occurrence `t(R,T)` is `occ σ R T : Option ℕ` (`none` = never occurs, i.e. the chain is
  blocked forever, which only strengthens lower bounds).

## Section 3 (oblivious lower bound)

- **Lower bound for undirected networks.** All constructed networks are connected `SimpleGraph`s
  and correctness is only assumed on those (`CorrectOnUndirected`), as the paper remarks the bound
  holds in symmetric networks. This is stronger than the directed statement.
- **Chain execution** (`Chain.lean`). The paper identifies, without proof, the step at which a chain
  `S ∘ …` delivers the message with the first occurrence of `S`. We prove it
  (`chain_outside_none`, `chain_last_informs`) for any network that "starts with the chain"
  (`StartsWithChain`). Requires `k ≥ 1` (for `k = 0` nothing is ever transmitted).
- **Lemma 3.1.** Stated for `|Q| ≥ 2` (✏️ degenerate case: for `|Q| = 1` and `V(S) ∪ Q = V` the
  single node of `Q` need not transmit at all, so `t_{≤k}(w,T)` is undefined). Lemma 3.2 only uses
  it with `|Q| ≥ 2` once `|Q| > k`. The proof is by the selective-family bound
  `Cslib.card_le_of_forall_exists_card_inter_eq_one` (parity argument) instead of the paper's
  peeling of degree-1 step vertices. (The paper's peeling step says "`G'` is not conflicting, hence
  some `u' ∈ B` has degree 1 in `G'`", but `G'` may be non-conflicting only because of degree-0 step
  vertices; one has to restrict to `A' ∪ N(A')`. Minor, the statement is true.) The collision
  network (`exists_blocked_network`) attaches all nodes outside `S ∪ P ∪ {v_t}` to `v_t` so that
  it is connected; the paper leaves them unspecified.
- **Lemma 3.2.** Proved as stated (`t(R,T) ≥ T + n − |S| − k`, written `T + (n − ℓ) ≤ T' + k` in
  `ℕ`), for any `|Q|` (trivial when `|Q| ≤ k`). The construction of `R` is reorganized as an
  induction (`exists_seq_exhausted`): pick the node of `W` with the latest next appearance and
  recurse; this is the paper's greedy `M_i` construction. The paper's final step ("any node in
  `{w_{j+1},…,w_k}` does not occur after …") misindexes the unused nodes of `W`; harmless.
- **Theorem 3.3.** ✏️ The paper's sum `1 + ∑_{j=1}^{⌊n/k⌋} (n − jk)` is off: Lemma 3.2 gives
  `T_j ≥ T_{j−1} + n − |S_{j−1}| − k` with `|S_{j−1}| ≤ 1 + (j−1)k`, so each stage gains
  `n − 1 − jk`, not `n − jk` (already `T_1 ≥ 1 + n − k` should be `≥ n − k`); and the last stages
  may use up all nodes, so that no node is left to be informed after the chain. We stop at
  `m = ⌊(n−2)/k⌋` stages and prove: broadcasting is not complete at any step
  `t ≤ ∑_{j=1}^{m} (n − 1 − jk)` (`theorem_3_3`), hence not at any `t` with
  `2kt + k(n−1) < (n−1)²` (`theorem_3_3'`). Same `Θ(n²/k)` order. Also typos: "`a3`" for `a2`,
  "until we have constructed a sequence of length `k` or less", `|s|` for `|S|`.
- Assumptions added: `k ≥ 1`, `n ≥ 2`.

## Section 4 (upper bound)

- Ids are `Fin n` with 0-based labels (label `i` ↦ point `⟨i div p, i mod p⟩`); `p` is the least
  prime with `n ≤ p²` (`smallestPrime`), i.e. the least prime `≥ ⌈√n⌉`; by Bertrand `p ≤ 2⌊√n⌋`.
  The paper's 1-based labels also work (coordinates are read mod `p`).
- The schedule (`obliviousKShot`): step `t ≥ 1` is a Line-Transmit step iff
  `(t − 1) mod (K+1) = 0`; stages of `p(K+1)` steps cycle through the directions `0, …, p`;
  Round-Robin slots cycle through `0, …, p² − 1` (empty slots for labels `≥ n`).
  `K = ⌈p/(k−2)⌉ = (p + k − 3)/(k − 2)`.
- Networks: directed, every node reachable from the source (`Relation.ReflTransGen E s v`).
- **Lemma 4.1** proved as stated for `k ≥ 3`, plus a time bound (the lone transmission happens by
  the end of stage `⌊r/S⌋ + p`), needed by the progress argument (`exists_lone_transmission`).
  Typo: `>` should be `≥` in `p(k−2)⌈p/(k−2)⌉ > p²`.
- **Lemma 4.2** 🛠️ (proof gap): the proof's claim "`v` transmits during `T` at least `k − k/r`
  times" is impossible (`T` has `r|F|` stages, one line transmission per stage); also mixes up
  collisions at `w` with arbitrary simultaneous transmissions, ignores that `w` may get informed
  during `T`, and "odd-numbered steps" holds only for `K = 1`. Proved instead (`progress_add_le`):
  progress (= #informed + #complete) grows by `≥ |F|` within `2|F|` stages, for every `|F|`
  (no `|F| ≤ k/2` needed), using the colliders-at-`w` argument and the time bound of Lemma 4.1.
- **Theorem 4.3** proved with explicit constants: completion within `2(2n−1)` stages
  (`obliviousKShot_complete`); `k·T ≤ 80 n²` for `3 ≤ k ≤ √n` (`theorem_4_3`, hypothesis
  `k·k ≤ n`); `T ≤ 32 n ⌊√n⌋` for `k > √n` (`theorem_4_3_large_k`; the paper's detour through
  running the algorithm with `√n` shots is unnecessary). The paper's case split
  `|F| > k/2` / `|F| ≤ k/2` is replaced by the uniform Lemma 4.2. Gap 🔧 (merged with the Lemma 4.2
  item in the README): "Round-Robin guarantees progress `k/2` in `O(n)` steps" needs Lemma 4.1's
  time bound.
- 🔧 `k ∈ {1, 2}`: the algorithm is undefined (`K = ⌈p/(k−2)⌉`); plain Round-Robin gives
  `≤ 4n²` steps (`roundRobin_complete`).

## Section 5 (adaptive lower bound)

- Protocols are general deterministic state machines `Protocol V σ M` (`init`, `act`, `δ`); the
  paper's full-information protocol `π(v, t, H_{t−1}(v))` is the special case where the state is
  the view. Spontaneous transmissions allowed, as in the paper. Rounds are numbered from `0`
  (paper's round `t` = our round `t − 1`).
- "Informed" is semantic (`Protocol.informed`): a node is informed when it hears a node informed
  at the start of the round — the most generous notion, so lower bounds are at least as strong.
- `k`-shot is assumed only on the networks of the family `G` (`KShotOnFamily`), weaker than on all
  networks. Correctness of the protocol is not assumed.
- Family `G`: a listing `e : V ≃ Fin n` with the source at position `0`; position `p` is in layer
  `⌊(p+1)/2⌋` (our layer `i` = paper's `L_{i+1}`), complete bipartite edges between consecutive
  layers.
- Definitions 1–2: transmission trees are encoded by the transmission patterns of the ids
  (`cell A p t x` = the depth-`t` tree node containing `x`); `HeightLE`, `KShotTree`. The paper's
  "leaves are singletons" (justified by correctness) is the hypothesis `HeightLE`.
- **Theorem 2** 🔧 (proof gap): the paper's induction over `k` with `O`/`ω` reasoning on a single
  tree ("`|P| ≠ O(a^{(i−1)/i}) ⇔ |P| = ω(a^{(i−1)/i})`") is not rigorous. Proved by counting:
  `a ≤ ∑_{i≤k} C(h, i) ≤ (h+1)^k`, so `h ≥ a^{1/k} − 1` (`card_le_sum_choose_of_kShotTree`,
  `rpow_sub_one_le_of_kShotTree`); for `k = 1` this is the paper's `a − 1`.
- **Theorem 1** proved as stated, in absolute rounds (`exists_extension_of_not_heightLE`).
- **Theorem 3** 🛠️ (proof gap): summing the absolute heights over layers is unjustified
  (`onceProtocol_heightLE`: one spontaneous shot per node makes all absolute trees of all layers
  of height `≤ B`). Proved by relative windows (`exists_extension_of_same_window`,
  `exists_extension_quiet`, `exists_slow_network`): for delays `d_j` with
  `∑_{r≤k} C(d_j, r) + 2(j+1) ≤ n`, some network is not informed after `∑_j d_j` rounds;
  uniform form `⌊n/4⌋·d` rounds when `(d+1)^k ≤ ⌊n/2⌋`; and `n^{1+1/k}/32` rounds when
  `k ≥ 1`, `n ≥ 2·4^k` (`exists_slow_network_rpow`). The paper's sum
  `(n−1)^{1/k} + (n−3)^{1/k} + …` is replaced by the uniform bound over `⌊n/4⌋` layers; the
  constant differs, the order `n^{1+1/k}` is the same.
- ✏️ Arithmetic of Theorem 3: "half of these terms are lower than `(n/2)^{1/k}`" should be
  "at least"; "`2^{1/k} ≥ 2`" should be "`≤ 2`".
- Minor: the two nodes of a layer need not receive the same incoming view (a transmitter hears
  nothing); harmless, behaviour is still determined by the earlier layers (`state_eq_solo`).
- Appendix A (alternative 1-shot proof) is not formalized.
