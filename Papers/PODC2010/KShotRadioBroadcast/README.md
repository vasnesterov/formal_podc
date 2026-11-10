# k-Shot Broadcasting in Radio Networks — PODC 2010

Paraschos Koutris, Aris Pagourtzis. *Brief Announcement: k-Shot Distributed Broadcasting in Radio
Networks.* PODC 2010. DOI [10.1145/1835698.1835717](https://doi.org/10.1145/1835698.1835717).
Formalized version: the full version, Karmakar, Koutris, Pagourtzis, Sakavalas, *k-shot Broadcasting
in Ad Hoc Radio Networks*, arXiv [1603.08393](https://arxiv.org/abs/1603.08393) v1; numbering follows
it. We found no open copy of the 2-page brief announcement. Copy of the paper: [paper.pdf](paper.pdf).

**Version caveat.** All mistakes below are those of the 2016 arXiv text. The brief announcement
(2 pages, no public abstract) presumably states the oblivious bounds (`Θ(n²/k)` for `k ≤ √n`,
`O(n^{3/2})` above) with at most proof sketches, which may differ from the full proofs checked
here. The adaptive `k`-shot lower bound of Section 5 is a later result: the arXiv text says its
conference version (CATS 2011) studied adaptive protocols only for `k = 1` (Appendix A, not
formalized). The verdict rests on Section 4 (Lemma 4.2), which concerns the oblivious upper bound.

**Verdict: 🛠️ Hard fix.** All three results hold, and we proved them in Lean with explicit constants:
the `Ω(n²/k)` lower bound for oblivious `k`-shot protocols, the `O(n²/k)` upper bound of *Oblivious
k-Shot* (`k ≤ √n`), and the adaptive `Ω(n^{1+1/k})` lower bound. Two proofs do not work as written
and needed new arguments: the proof of Lemma 4.2 (the progress lemma behind the upper bound) and the
proof of the adaptive Theorem 3, which adds tree heights measured in absolute rounds. The rest are
slips and a missing case `k ∈ {1, 2}`.

## Mistakes in the paper

### 🔧 Section 4 (Oblivious k-Shot, `k ∈ {1, 2}`)
The algorithm uses `K = ⌈p/(k−2)⌉` Round-Robin steps per Line-Transmit step, which is undefined
for `k ≤ 2`, yet the paper claims the `O(n²/k)` bound for every `k ≤ √n`.

**Impact.** Local fix: for `k ∈ {1, 2}` plain Round-Robin broadcasts in `≤ 4n²` steps
(`roundRobin_complete`), so the claimed bound holds for all `k ≤ √n`.

### ✏️ Slips
- Theorem 3.3: the sum `1 + ∑_{j=1}^{⌊n/k⌋} (n − jk)` overcounts. Lemma 3.2 gives a gain of
  `n − |S| − k` with `|S| ≤ 1 + (j−1)k`, so stage `j` gains `n − 1 − jk` (already `T₁ ≥ 1 + n − k`
  should be `T₁ ≥ n − k`). Also the last stages may use up every node, so that no node is left to
  be informed after the chain. With `m = ⌊(n−2)/k⌋` stages the bound is
  `∑_{j=1}^{m} (n − 1 − jk) ≥ ((n−1)² − k(n−1))/(2k)`, the same order (`theorem_3_3`, `theorem_3_3'`).
- Lemma 3.1 is false for `|Q| = 1` when `V(S) ∪ Q = V`: the node of `Q` then need never transmit,
  so `t_{≤k}(w,T)` is undefined. Lemma 3.2 needs it only for `|Q| ≥ 2`; we state it so
  (`lemma_3_1`).
- Theorem 3 (§5), final estimate: "half of these terms are lower than `(n/2)^{1/k}`" should say
  "at least", and "`2^{1/k} ≥ 2`" should say "`≤ 2`".

### Typos
- Lemma 4.1: "`p(k−2)⌈p/(k−2)⌉ > p²`" should be `≥` (equality at `k = 3`). The chain of inequalities
  is still strict.
- Theorem 3.3: "`a3`" for `a2`, and "until we have constructed a sequence of length `k` or less".
  Lemma 3.2: `|s|` for `|S|`. Its last step names the unused nodes of `W` as `w_{j+1}, …, w_k`; any
  unused node works.
- Lemma 4.2 says `v` transmits "during the odd-numbered steps"; that holds only when `K = 1`.

## Proof gaps (statements true)

### 🛠️ Theorem 3 (§5, adaptive `Ω(n^{(1+k)/k})` lower bound)
The proof adds up the heights of the transmission trees of all layers, but Definition 1 builds a
tree over *absolute* rounds, starting at round 1. So Theorem 1 bounds only the absolute round of
the relay from `L_{i+1}` to `L_{i+2}`, not its delay after `L_{i+1}` receives the message.

**Impact.** Statement true; repaired with a relative-delay argument (`exists_slow_network`,
`exists_slow_network_rpow`).

**Details.** Adaptive protocols may transmit before they hold the message. With one spontaneous
shot per node, the ids are separated before the message arrives: every absolute tree of every layer
has height at most `B` (`onceProtocol_heightLE`). Theorems 1 + 2 then only give relay rounds
`≥ max_i height(T_i)`, not the sum. Theorems 1 and 2 themselves are correct
(`exists_extension_of_not_heightLE`, `card_le_sum_choose_of_kShotTree`).

**Repair.** Measure from the round `τ_i` before which layer `i+1` cannot be informed. In the
window `(τ_i, τ_i + d]` each unused id has a 0/1 transmission pattern with at most `k` ones, so
there are at most `∑_{r≤k} C(d, r) ≤ (d+1)^k` patterns. If there are more unused ids than that,
two ids share their pattern. Placing them in `L_{i+1}` keeps `L_{i+2}` uninformed for `d` more
rounds (`exists_extension_quiet`). These delays add up over `⌊n/4⌋` layers with
`(d+1)^k ≤ n/2`: some network is not informed after `n^{1+1/k}/32` rounds when `n ≥ 2·4^k`.

### 🛠️ Lemma 4.2 (progress per stage) and Theorem 4.3
The proof's count is impossible: it claims `v` transmits at least `k − k/r` times during the
`r|F|` stages of `T`, but `v` transmits at most once per stage. With `|F| = 1`, `r = 2`, `k > 4` it
would need more than 2 transmissions in 2 stages.

**Impact.** Statement true (with `r = 2`, and even without `|F| ≤ k/2`); repaired with a new
counting argument (`progress_add_le`), giving Theorem 4.3 with explicit constants (`theorem_4_3`).

**Details.** The proof also splits on "`v` transmits alone in `T`" instead of "`v` is complete at
the end of `T`". It ignores that the uninformed neighbour `w` may be informed during `T`. And it
counts co-transmitters "outside `F`" as progress, although complete nodes that still have shots may
also transmit. In Theorem 4.3, "Round-Robin guarantees progress `k/2` over `O(n)` steps" needs that
a Round-Robin appearance lies within the node's first `k` appearances, which is Lemma 4.1 with a
time bound.

**Repair.** Let `f = |F|` and look at the next `2f` stages. If some `v ∈ F` is not complete at
their end, fix an out-neighbour `w` of `v` that is still uninformed then. Before that, `v` never
transmitted alone, and by Lemma 4.1 it still has shots left. So `v` transmitted in each of the
`2f` stages, on a line, colliding at `w`. Each collider is an in-neighbour of `w`, hence active and
in `F` or newly informed. The colliders are pairwise distinct, since two nodes share a line in at
most one of `p + 1` consecutive stages (`eq_of_onLine_two_dirs`). This forces progress `≥ f + 1`.
Otherwise every node of `F` completes, and progress is `≥ f`. Hence broadcasting completes within
`2(2n−1)` stages of `p(K+1)` steps (`obliviousKShot_complete`). For long windows (`2f > p+1`), the
time bound of Lemma 4.1 (`exists_lone_transmission`) completes every active node within `p + 1`
stages.

### 🔧 Theorem 2 (§5, height of `k`-shot transmission trees)
The induction on `k` reasons with `O`/`ω` about a single tree, as in
"`|P| ≠ O(a^{(i−1)/i}) ⇔ |P| = ω(a^{(i−1)/i})`", which is not rigorous.

**Impact.** Statement true. A direct count proves it: `a ≤ ∑_{i≤k} C(h, i) ≤ (h+1)^k`, so
`height ≥ a^{1/k} − 1` (`card_le_sum_choose_of_kShotTree`, `rpow_sub_one_le_of_kShotTree`).

### 🔧 Lemma 3.1 (degree-1 peeling)
After removing a step vertex and its neighbour, the proof says the remaining graph `G'` is not
conflicting, hence some step vertex has degree 1 in `G'`. But `G'` may fail to be conflicting only
because of step vertices of degree 0.

**Impact.** Statement true (for `|Q| ≥ 2`): one should restrict to `A' ∪ N(A')`. We use the
selective-family bound instead (`lemma_3_1` via `Cslib.card_le_of_forall_exists_card_inter_eq_one`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Synchronous radio network on a finite id set `V`, `n = |V|`, directed links `E` (`u` transmits to
  `v`), one source, no collision detection. A node receives iff exactly one in-neighbour transmits.
  Deterministic protocols, no failures.
- Oblivious protocols (`Model.lean`): a schedule `σ : ℕ → Finset V`. A node informed at step `r`
  transmits at its first `k` appearances after `r`, with no spontaneous transmissions. The execution
  is `recvTime`.
- Lower bound (§3): proved for **undirected** networks. Correctness is assumed only on connected
  undirected networks (`CorrectOnUndirected`), and every constructed network is a connected
  `SimpleGraph`; this is the stronger form, as the paper remarks. The statement does not assume
  correctness: if the protocol fails somewhere, that network is the witness.
- Upper bound (§4): every directed network in which all nodes are reachable from the source, ids
  `Fin n` with 0-based labels, `p` the least prime with `n ≤ p²`.
- Adaptive protocols (§5, `Adaptive.lean`): general deterministic state machines (state, action
  `transmit m / listen`, update on the received message), with spontaneous transmissions allowed.
  This contains the paper's full-information views. "Informed" is tracked semantically (hearing an
  informed node). `k`-shot is assumed only on the paper's layered family (`KShotOnFamily`), which
  is weaker than assuming it on all networks.
- "Running time `Ω(f)`" is stated as "some network is not fully informed after `f` steps", with
  explicit constants.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| (implicit) message travels along a chain at first-occurrence times | `chain_outside_none`, `chain_last_informs` | `Chain.lean` |
| Lemma 3.1 | `lemma_3_1` (collision network `exists_blocked_network`) | `ObliviousLB.lean` |
| Lemma 3.2 | `lemma_3_2` (core: `exists_seq_exhausted`) | `ObliviousLB.lean` |
| Theorem 3.3 | `theorem_3_3`, `theorem_3_3'` | `ObliviousLB.lean` |
| Line properties (§4) | `exists_onLine`, `eq_of_onLine_two_dirs` | `Lines.lean` |
| Algorithm *Oblivious k-Shot* | `obliviousKShot` | `UpperBoundSchedule.lean` |
| Lemma 4.1 | `lemma_4_1`, `exists_lone_transmission` | `UpperBoundSchedule.lean` |
| Lemma 4.2 (repaired) | `progress_add_le` | `UpperBoundProgress.lean` |
| Theorem 4.3 | `obliviousKShot_complete`, `theorem_4_3` (`k·T ≤ 80n²`), `theorem_4_3_large_k` (`≤ 32 n ⌊√n⌋`) | `UpperBound.lean` |
| `k ∈ {1,2}` | `roundRobin_complete` | `UpperBound.lean` |
| Definitions 1–2, Theorem 2 | `HeightLE`, `KShotTree`, `card_le_sum_choose_of_kShotTree`, `rpow_sub_one_le_of_kShotTree` | `Adaptive.lean` |
| Theorem 1 | `exists_extension_of_not_heightLE` (as stated), `exists_extension_quiet` (relative) | `Adaptive.lean` |
| Theorem 3 | `exists_slow_network`, `exists_slow_network_uniform`, `exists_slow_network_rpow` | `Adaptive.lean` |

**Not formalized.** Appendix A (an alternative proof for adaptive 1-shot protocols).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: *Oblivious k-Shot* satisfies the correctness hypothesis of Lemmas
3.1–3.2 (`obliviousKShot_correctOnUndirected`), and `onceProtocol_kShot` is a `1`-shot adaptive
protocol. Reused: `Cslib.card_le_of_forall_exists_card_inter_eq_one` (`Podc/Foundations/Combinatorics/SelectiveFamily.lean`).
CSLib candidates: the oblivious radio model and the chain lemma (`Model.lean`, `Chain.lean`), and the
affine-plane line facts (`Lines.lean`).
