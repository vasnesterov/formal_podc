# Source Detection with Limited Bandwidth — PODC 2013

Christoph Lenzen, David Peleg. *Efficient distributed source detection with limited bandwidth.* PODC 2013.
DOI [10.1145/2484239.2484262](https://doi.org/10.1145/2484239.2484262). Formalized version: Section 4 (with Theorem 1.2
and Definition 1.1) of the open-access journal version that merges it with two other papers: Lenzen, Patt-Shamir,
Peleg, *Distributed distance computation and routing with small messages*, Distributed Computing 32:133–157 (2019),
DOI [10.1007/s00446-018-0326-6](https://doi.org/10.1007/s00446-018-0326-6). Numbering follows the journal version.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✏️ Slip.** The main result holds: the pipelined Bellman–Ford algorithm (Algorithm 1) solves unweighted
`(S, h, σ)`-detection in `σ + h − 1` rounds with one `(distance, source)` pair per message. Lemmas 4.3, 4.5 and 4.6,
Corollaries 4.7 and 4.10 and the `β`-pairs-per-message remark are proved too. The only mistake is a slip: the second
part of Corollary 4.4 is false as stated when `v` has fewer than `k` sources within `h` hops, but the proofs only use
the prefix property, which the paper states in the sentence before it.

## Mistakes in the paper

### ✏️ Corollary 4.4 (second part)
"If `top_k(L_v^{(h)}) ⊆ L_v^r` then `top_k(L_v^r) = top_k(L_v^{(h)})`" is false for Algorithm 1 as printed. On the path
`0 — 1 — 2` with `S = {0}`, `h = 1`, `k = 1`, node `2` has `L_2^{(1)} = ∅` but `L_2^2 = {(2, 0)}`
(`corollary_4_4_literal_false`).

**Impact.** None on the results. Lemma 4.6 uses only "these are the first elements of `L_v^{r+1}`", i.e. that
`top_k(L_v^{(d)})` is a prefix of `L_v^r`. That property is true (`mem_topk_of_mem_entries`), and the paper states it
in the sentence before the corollary. The proof of Theorem 1.2 needs the equality only after Line 16 has deleted the
entries with distance `> h`, and that version is true (`output_eq_of_subset`).

**Details.** Line 16 sits after the loop, so `L_v^r` keeps entries at distance `> h` during the loop. When
`|L_v^{(h)}| < k`, such an entry gets into `top_k(L_v^r)`. The equality holds when `|L_v^{(h)}| ≥ k`, or when `L_v^r`
is filtered to distances `≤ h`.

### Typos
- Corollary 4.7 defines `p_s(v)` as "the node from which `v` receives `(hd(s,v) − 1, s)` for the first time". Several
  neighbours may send it in the same round, so a tie-break is needed. Every choice works (`corollary_4_7`). The tree
  edges `{(v, p_s(v)) | v ∈ V \ {s}}` should range over the nodes that output `s`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Synchronous rounds, deterministic, no failures. The communication graph is an arbitrary relation `E` on a finite set
  `V` (`E u v`: `u` can send to `v`). Undirected graphs are `E = G.Adj` for a Mathlib `SimpleGraph`, where the hop
  distance is `SimpleGraph.edist` (`hd_adj_eq_edist`). Directed graphs give Section 4.4. Connectivity is not needed:
  unreachable sources have distance `⊤`.
- Node identifiers are the elements of `V`, which is linearly ordered. Pairs `(distance, source)` are compared
  lexicographically in `ℕ ×ₗ V`. A node's input is whether it is a source. `h` and `σ` are known to all nodes.
- A node's state is its list `L_v` (at most one entry per source, so a function `V → ℕ∞`) and the `sent_v` flags. In
  each round a node sends its `β` smallest unsent entries to all out-neighbours (`β = 1` is Algorithm 1) and then
  processes all received pairs. Processing them one by one, as Lines 11–15 do, gives the same result as taking the
  minimum per source, which is what `step` does. Line 16 is a parameter `cap`: `⊤` means after the loop (as printed)
  and `h` means in every round.
- The run does not terminate. "Solves the problem in `T` rounds" means that the output computed from the state after
  `T` rounds (Line 16, then `top_σ`, as a sorted list) is `top_σ(L_v^{(h)})`.
- CONGEST: every stored and sent distance is `< n` (`est_lt_card`), whatever `h` and `σ` are. So Algorithm 1 is a
  typed CSLib CONGEST algorithm `pbf` with messages in `Option (Fin n × V)`, that is `≤ 2⌈log₂ n⌉ + 1` bits
  (`msgBits_pbf_le`). Its runs are exactly the abstract runs (`pbf_run`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 1.1 / 4.1 (`L_v^{(h)}`, `top_k`) | `Lspec`, `topk`, `sort_topk` | `Basic.lean`, `TopK.lean` |
| Algorithm 1 | `run`, `step`, `output`, `alg1` | `Algorithm.lean` |
| Lemma 4.3 | `lemma_4_3` | `Analysis.lean` |
| Corollary 4.4, first part | `corollary_4_4_persist`, `corollary_4_4_persist_init` | `Analysis.lean` |
| Corollary 4.4, second part, corrected / literal is false | `mem_topk_of_mem_entries`, `output_eq_of_subset` / `corollary_4_4_literal_false` | `Analysis.lean`, `Counterexamples.lean` |
| Lemma 4.5 | `lemma_4_5` (core: `mem_topk_Lspec_pred`) | `Basic.lean` |
| Lemma 4.6 (for `β` pairs per message) | `lemma_4_6` | `Main.lean` |
| Theorem 1.2 | `theorem_1_2`, `theorem_1_2_graph`, `theorem_1_2_truncated` | `Main.lean`, `Congest.lean` |
| Theorem 1.2 in CSLib's CONGEST model | `theorem_1_2_congest`, `msgBits_pbf_le` | `Congest.lean` |
| Remark after Thm 1.2 (`h + ⌈σ/β⌉ − 1` rounds) | `theorem_1_2_beta` | `Main.lean` |
| Corollary 4.7 (i)–(iii) | `corollary_4_7`, `corollary_4_7_all` | `Trees.lean` |
| Corollary 4.10 (directed graphs) | `corollary_4_10` | `Main.lean` |

The Lean statements are slightly more general than the paper's. Lemma 4.5 holds for all `d, k ≥ 0` and for every
predecessor on a shortest path. Lemma 4.6 holds for every `r`, since the run does not terminate. Corollary 4.7(i)
gives reception by round `h + σ − 1`, where the paper says `h + σ`. The paper's closing remark on Lemma 4.6 ("the
missing element is the same for all such values") is not needed: for each `(d, k)` the missing element is the smallest
unsent entry.

Line 16 is clearly printed after the loop, and with that reading Lemma 4.6 holds for all `d`, including `d > h`. Under
the other conceivable reading, Line 16 executed in every round (`cap = h`), Lemma 4.6(i) fails for `d > h`
(`lemma_4_6_truncated_false`), but Theorem 1.2 still holds (`theorem_1_2_truncated`). This is not a mistake of the
paper.

**Not formalized.** The lower bound `h + ⌈σ/β⌉ − 1` (remark after Theorem 1.2, Fig. 2): the paper does not fix a
model of "what fits in a message". Corollary 4.7(iv) (echo) is just (iii) with time reversed. Corollary 4.8 (routing
tables). Sections 5–8 (approximate weighted detection, skeleton spanners, routing) are randomized and out of scope.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`. The
main theorems have no hypotheses beyond `β ≥ 1` and `h ≤ cap`. The counterexamples are proved from the general
lemmas, not by evaluation. The CONGEST bridge uses `Podc/Computability/Distributed/Congest/Typed.lean`
(`TAlgorithm`, `toAlgorithm`, `run_toAlgorithm`).
