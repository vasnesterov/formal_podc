# Differences between the formalization and the paper

Paper: Chan, Lesani, *Brief Announcement: Brokering with Hashed Timelock Contracts is NP-Hard*, PODC 2021
(proceedings version, 4 pages).

## Errors and gaps in the paper

1. **Lemma 4.2 (and the forward direction of Lemma 4.4) is false with the printed `m`.** The paper sets
   `m = ⌈Σ_w(X)/min_w(X) − 1⌉ + 1`, rendered from the PDF to rule out a `pdftotext` artifact. The broker's
   total bitcoin income is `W + (m − 1)(min_w(X) − 1)`, and its outgoing bitcoin contracts total `Σ_w(X)`. Since
   the broker owns nothing initially, `Σ_w(X) ≤ W + (m − 1)(min_w(X) − 1)` is necessary for adequacy of *any*
   leader set (`budget_of_adequate`). The instance `K₁`, with items `(1,2), (1,2), (1,4)`, `V = 2` and `W = 4`,
   satisfies every assumption of the paper and is satisfiable. Yet `8 > 4 + 3·1`, so the flower graph has no
   adequate leader set (`lemma_4_2_false`).
   *Rule.* For instances with all weights ≥ 2 this alone would be R3 (typo with evident intent, ⚠️). The intended
   formula is `m = ⌈Σ_w(X)/(min_w(X) − 1)⌉ + 1`, for three reasons. (a) `⌈x − 1⌉ + 1` is a pointless way to write
   `⌈x⌉`. (b) The proof's sentence "after repeating this process `m` times [each time gaining (min_w(X) − 1) B], by
   the definition of `m`, the broker `b` is left with (at least) `Σ_w(X)` B" is true exactly under this reading.
   (c) The fix only moves a parenthesis. With it the reduction is correct for weights ≥ 2 (`theorem_4_1_fixed`).
2. **`min_w(X) = 1`: Lemma 4.2 is false for any `m` (decides the verdict).** The contracts `(yᵢ, b)` carry
   `(min_w(X) − 1)` B = `0 B`, so the broker's bitcoin income is only `W`, and the graph is adequate only if
   `Σ_w(X) ≤ W` (`paper_minW_one`, and `lemma_4_2_false_minW_one` for every `m`). The instance `K₂`, with items
   `(1,1), (1,1), (1,2)`, `V = 2` and `W = 2`, satisfies every assumption of the paper (and every item fits by
   itself), is satisfiable, and its flower graph has no adequate leader set. Under the intended formula `m` is
   undefined (division by zero). The amount cannot be raised to `min_w(X)`: Lemma 4.3's proof ("by definition of
   `min_w(X)`, the broker cannot create any contracts to any item party") needs it to be below every weight. We
   repair this by doubling all weights and the capacity before the construction (`Knapsack.double`,
   `theorem_4_1_repaired`).
   *Rule.* Not R2: Knapsack instances with a weight-1 item are not trivial, and the paper reduces from general
   Knapsack. Not R3: the doubling step is not recoverable from the paper (it never mentions this case) and adds a
   step to the reduction. Not R4: the paper never restricts the weights, and `min_w ≥ 2` is no standard convention.
   So Lemma 4.2, a numbered lemma, is false without excuse → ❌. Not 🚨 (R5): Theorem 4.1 (NP-hardness) is not
   refuted; the repaired reduction proves it, so the headline is only unestablished by the paper's proof.
   *Borderline:* one could read this as a missing case with a standard fix (⚠️). The fix is standard, but R3 also
   requires the intended version to be recoverable from the paper itself, and it is not.
3. **"Otherwise the Knapsack problem is trivial."** Lemma 4.3's proof assumes that no single item has value
   `≥ V`. This is not justified as stated: an item with `vᵢ ≥ V` and `wᵢ > W` does not make the instance trivial,
   and it breaks Lemma 4.3. For the items `(2, 20), (0, 10)` with `V = 2` and `W = 12`, the paper's own construction
   (`m = 3`, `c = 9`) makes `{b, x₁}` adequate, although the instance is unsatisfiable. This was checked by hand,
   not in Lean. The reduction must first remove the items with `wᵢ > W`. All our theorems carry the paper's
   assumption `∀ i, vᵢ < V` (`hv`). *Rule:* the assumption is stated in the paper (in the
   proof of Lemma 4.3) and the false "otherwise trivial" is a claim inside a proof (R1); the lemma is true under
   the stated assumption, and the reduction's missing preprocessing step is covered by the paper's remark up to
   the overweight items → proof gap, not a false statement.
4. **`V ≥ 2` is needed** (hypothesis `hV` of `lemma_4_3` and of the main theorems). With `V = 1`, the assumption
   `vᵢ < V` makes all values 0, and `(b, y₁) = 0 E`. Then `{b, z₁}` is adequate whenever the budget allows, although
   the instance is unsatisfiable. *Rule:* degenerate (R2).
5. **Positive weights are needed** (`0 < wᵢ`, used through `c = min_w(X) − 1 < wᵢ`). A weight-0 item can be funded
   by the broker for free. This is standard for Knapsack (R4).
6. **Slips in proofs (no effect on the statements).** Lemma 4.2's proof counts `m` bitcoin-giving rounds; there are
   `m − 1` (`y₂, …, y_m`). Lemma 4.3's proof says that `{b, yᵢ}` gives `b` `min_w(X) − 1` bitcoins; this is false for
   `y₁` and `y_{m+1}`, which is harmless. The proof does not discuss the leader set `{b}`; it is covered by
   monotonicity (`not_adequate_of_supplier_not_mem` handles any `L ⊆ {b, p}`, `s ∉ L`).

## Modelling choices

* **Edge creation semantics** (§§2–3 are informal). We create contracts one at a time. A leader may create any
  outgoing contract at any time. A follower may create its outgoing contracts only after *all* its incoming
  contracts exist. The sender must own the amount at that moment: endowment + received − escrowed, the
  master-contract bookkeeping. `Adequate L` means that *some* order creates all contracts, matching "the set `L` can
  create all edges"; the broker's choices, such as which items to fund, are part of the existential.
* **Endowments.** The paper does not state what the broker owns initially. Every argument in §4 (for example "`b`
  needs `2 D` to create `(b, s)`" and "`b` only receives `W` B from `s`") requires that it owns nothing. Every other
  party of a flower graph owns exactly what it sends ("all other parties have the assets to create their outgoing
  contracts at the beginning"). This is `TxGraph.brokerOwn`.
* **Secrets, hashlocks, timelocks and triggering are not modelled.** Adequacy in the paper concerns only edge
  creation.
* **Flower graph definition** (`TxGraph.IsFlower`): the broker `c` is incident to every contract; there are no
  loops; every other party has a contract to and from `c`; no other party is a broker; and every other party owns
  what it sends.
* **Construction parameters.** `flower K m c` takes the number of levels `m` and the bitcoin amount `c` of the
  contracts `(yᵢ, b)`, `2 ≤ i ≤ m`, as parameters. `paperFlower K` uses the paper's values. Levels are indexed
  `0, …, m` (paper: `y₁, …, y_{m+1}`); the paper's coin `Cᵢ` is `Asset.C i`.
* **`min_w(X)`** is `⨅ i, wᵢ` (0 for the empty instance, for which all theorems still hold). `m` uses
  the rational ceiling `Nat.ceil`, as printed.
* **Knapsack** is over ℕ: `Satisfiable K ↔ ∃ R, V ≤ Σ_R v ∧ Σ_R w ≤ W`.
* **NP-hardness is not formalized.** No complexity classes and no polynomial-time bounds. We prove that the
  reduction is correct: `K` satisfiable ⇔ `{b, s}` is a minimum leader set ⇔ some minimum leader set has size 2. The
  paper's closing remark is not formalized either: `m` may be exponential, and Knapsack stays NP-hard for
  polynomially bounded weight ratios. With the repaired `m ≈ Σ_w/(min_w − 1) ≤ 2n·max_w/min_w` (for `min_w ≥ 2`, and
  doubling preserves ratios), that remark still makes the reduction polynomial.
* **§3, general graphs.** The paper derives NP-hardness for general transaction graphs from the NP-hardness of
  FVS. We formalize the two facts behind this: every adequate leader set is an FVS (any endowment), and without
  brokering every FVS is adequate (`adequate_iff_isFVS`). FVS is defined as acyclicity of the follower subgraph
  (`¬ TransGen u u`).
