# Differences between the formalization and the paper

Paper: Lenzen–Peleg, PODC 2013, formalized from Section 4 of the journal version (Lenzen, Patt-Shamir, Peleg,
Distributed Computing 32, 2019). We did not have the conference version itself; its abstract (not checked against the paper) states the
running time as "`d + k` rounds" (`d = h`, `k = σ`), which the journal's `σ + h − 1` implies.

## Mistakes (labels from `mistakes-labeling.md`)

- ✏️ **Corollary 4.4, second part.** "`top_k(L_v^{(h)}) ⊆ L_v^r` ⇒ `top_k(L_v^r) = top_k(L_v^{(h)})`" is false for
  Algorithm 1 as printed (Line 16 after the loop) when `|L_v^{(h)}| < k` and `L_v^r` has an entry at distance `> h`
  (`Counterexample.corollary_4_4_literal_false`: path `0—1—2`, `S = {0}`, `h = 1`, `k = 1`, `r = 2`). Replaced by the
  prefix property `mem_topk_of_mem_entries` (stated in the paper's sentence before the corollary, and what Lemma 4.6
  uses) and the filtered equality `output_eq_of_subset` (what the proof of Theorem 1.2 needs, with Line 16).

## Imprecisions and alternative readings (not labeled as mistakes)

- **Lemma 4.6 and Line 16 (alternative reading, not a mistake).** The range `d + k ≤ r + 1 ≤ h + σ` allows `d > h`. With Line 16 executed in every round
  (or with `L_v^{h+σ−1}` taken after Line 16), (i) fails for `d > h`
  (`Counterexample.lemma_4_6_truncated_false`, same path, `cap = h = 1`, `d = 2`, `k = 1`, `r = 2`, `σ = 2`). Our
  `lemma_4_6` assumes `d ≤ cap`, which is no restriction for the printed algorithm (`cap = ⊤`). Theorem 1.2 holds for
  both readings. The pseudocode prints Line 16 after the loop, and Definition 4.2 takes `L_v^r` at the end of
  round `r`; with that reading Lemma 4.6 holds for all `d` (our `lemma_4_6` with `cap = ⊤`).
- **Corollary 4.7, `p_s(v)` (imprecision; every claim stays correct).** "The node from which `v` receives `(hd(s,v) − 1, s)` for the first time" is not
  unique if several neighbours send it in the same round. We prove (ii)/(iii) for every such neighbour. The tree edges
  `{(v, p_s(v)) | v ∈ V \ {s}}` should range over the nodes `v` that output `s`.

## Proof details not in the paper (not mistakes)

- Lemma 4.6(ii) needs that a sent correct entry stays marked as sent (Line 15 resets the flag only when the entry
  improves, impossible for a correct entry by Lemma 4.3). The paper does not say this; `sent_persist`,
  `sent_succ_eq_true`. Conversely a set flag means the current entry was sent earlier (`sent_spec`).
- The remark "the missing element is the same for all such values" after Lemma 4.6 is not needed: for each `(d, k)`
  the missing element of `top_k(L_v^{(d)})` is the smallest unsent entry of `L_v^{r+1}`, so it is sent.
- `L_v` has at most one entry per source (implicit in Lines 13–14); we store it as `est : V → ℕ∞`.

## Modelling choices and generalizations

- Communication graph: an arbitrary relation `E` on a finite linearly ordered `V` (IDs = nodes). Undirected graphs:
  `E = G.Adj`, `hd_adj_eq_edist` identifies our `hd` with `SimpleGraph.edist`; the paper's `hd(v, s)` is
  `G.edist v s` (`mem_Lspec_graph`). Directed graphs: `E` = arcs, `hd(s, v)` = directed distance (Def. 4.9,
  Corollary 4.10). Connectivity (assumed in Section 3.1) is not needed.
- `top_k` of a list is `topk k F` for the finset `F` (elements with fewer than `k` smaller elements). `sort_topk` shows
  sorting it gives the first `k` entries of the sorted list. The main theorems are stated for sorted lists.
- Lines 11–15 process received pairs one by one; `step` takes the per-source minimum `recv`, which gives the same
  `L_v` and flags (the flag is reset iff the entry improves).
- The run does not terminate; the output after `T` rounds is `output h σ (run … T v)` (Line 16 then Line 17). Lemma 4.6
  holds for all `r`, not only `r ≤ h + σ − 1`.
- The `β`-pairs-per-message generalization (remark after Theorem 1.2): each node sends its `β` smallest unsent
  entries. The paper does not say how the `β` pairs are chosen; this is the natural choice. Algorithm 1 is `β = 1`
  (`msg_one`: the message is the minimum unsent pair, if any).
- Line 16 is a parameter `cap` (`⊤`: after the loop as printed; `h`: every round).
- Lemma 4.5 is proved for all `d, k` (the paper: `h, k ∈ ℕ`, i.e. `≥ 1`), and in a stronger form: every predecessor
  `w` of `v` on a shortest path from `s` works (`mem_topk_Lspec_pred`).
- Corollary 4.7(i): received by round `h + ⌈σ/β⌉ − 1` (paper: `h + σ`). (iii) is stated as: the child sends its pair
  in some round `≤ h + ⌈σ/β⌉` and every round in which it sends it comes after the round in which the parent sent the
  parent's pair. The "BFS tree" in (ii) is stated through the parent properties (`hd(s, p) = hd(s, v) − 1`, `p`
  outputs `s`), from which the tree structure is immediate.
- CONGEST: messages of Algorithm 1 are typed `Option (Fin n × V)` (`pbf`), `msgBits ≤ 2⌈log₂ n⌉ + 1`. The paper
  only says `O(log n)` bits; distances `< n` hold for all rounds (`est_lt_card`), not just `≤ h + σ − 1`.

## Not formalized

- The lower bound `h + ⌈σ/β⌉ − 1` (remark after Theorem 1.2, Fig. 2): no model of what fits into a message is given.
- Corollary 4.7(iv) (echo schedule, time reversal of (iii)) and Corollary 4.8 (routing tables).
- Sections 5–8 of the journal version (other papers).
