# Brokering with HTLCs is NP-hard — PODC 2021

Eric Chan, Mohsen Lesani. *Brief Announcement: Brokering with Hashed Timelock Contracts is NP-Hard.* PODC 2021.
DOI [10.1145/3465084.3467952](https://doi.org/10.1145/3465084.3467952). Formalized version: the 4-page proceedings
version (no arXiv version exists).

**Verdict: ❌ False claim.** The reduction from Knapsack to minimum leader sets in flower graphs is right in
spirit, and NP-hardness (Theorem 4.1) holds: we prove a repaired reduction correct. Lemma 4.3 and the backward half
of Lemma 4.4 hold as stated. Lemma 4.2 (and the forward half of Lemma 4.4) is false for the construction as written.
For weights ≥ 2 this is a misplaced parenthesis in the number of levels `m`. But for instances with a weight-1
item the construction cannot work for any `m`: its "bitcoin pump" contracts carry `min_w(X) − 1 = 0` B. Such
instances are ordinary Knapsack instances, and the paper gives no way to handle them (we double all weights first).

## Mistakes in the paper

* **Lemma 4.2 fails on all instances with a weight-1 item (so does the forward direction of Lemma 4.4).** The
  `y`-parties are the broker's only bitcoin source besides the supplier: each `yᵢ`, `2 ≤ i ≤ m`, pays
  `(min_w(X) − 1)` B. With `min_w(X) = 1` they pay nothing, so the flower graph is adequate only if all items fit
  into the knapsack, whatever `m` is. Take the items `(v, w) = (1, 1), (1, 1), (1, 2)` with `V = 2` and `W = 2`.
  The instance is satisfiable (the first two items) and meets all the paper's assumptions; even every single item
  fits. But `Σ_w(X) = 4 > 2 = W`, so the flower graph has no adequate leader set for any number of levels
  (`lemma_4_2_false_minW_one`, `paper_minW_one`). The intended formula for `m` (below) divides by zero here. The
  amount `min_w(X) − 1` cannot simply be raised: Lemma 4.3's proof needs it to be below every weight. Weight-1
  items are not a degenerate case of Knapsack, and the paper reduces from Knapsack in general. The repair is a
  new step of the reduction: double all weights and the capacity first (`theorem_4_1_repaired`). Theorem 4.1
  (NP-hardness) is therefore true, but Lemma 4.2, a numbered lemma, is false without an excuse.
* **Lemma 4.2 is also false with the printed `m` when all weights are ≥ 2.** The broker `b` starts with nothing.
  It must pay every item contract `(b, xᵢ) = wᵢ B`, so it must receive `Σ_w(X)` bitcoins in total. Its only bitcoin
  income is `W` from the supplier `s` and `min_w(X) − 1` from each of `y₂, …, y_m`. So
  `Σ_w(X) ≤ W + (m − 1)(min_w(X) − 1)` is necessary for **any** leader set to be adequate, whatever the schedule
  (`budget_of_adequate`). The paper sets `m = ⌈Σ_w(X)/min_w(X) − 1⌉ + 1 = ⌈Σ_w(X)/min_w(X)⌉`, which is too small.
  Take the items `(v, w) = (1, 2), (1, 2), (1, 4)` with `V = 2` and `W = 4`. The instance is satisfiable (the first
  two items), and it meets all the paper's assumptions. Here `m = 4`, so the broker can collect at most
  `4 + 3·1 = 7 < 8` bitcoins: the flower graph has no adequate leader set at all (`lemma_4_2_false`). The proof's
  arithmetic goes wrong in the same place. It says that after "repeating this process `m` times", `b` "is left with
  at least `Σ_w(X)` B by the definition of `m`". Only `m − 1` parties send bitcoins, and with the printed `m` the
  total is short.
  *Evident intent:* `m = ⌈Σ_w(X)/(min_w(X) − 1)⌉ + 1`. Writing `⌈x − 1⌉ + 1` instead of `⌈x⌉` makes no sense
  otherwise, and the proof's "left with at least `Σ_w(X)` B" holds exactly for this reading. With it the reduction
  is correct whenever all weights are ≥ 2 (`theorem_4_1_fixed`). More generally it is correct for every `m ≥ 1`
  that satisfies the budget (`lemma_4_4_of_budget`, `theorem_4_1_of_budget`). On its own, this part would be a
  typo with evident intent.
* **"Otherwise the Knapsack problem is trivial" is not quite right (proof gap; the lemmas are true under the
  stated assumption).** Lemma 4.3's proof assumes that no single item has value `≥ V`. An item with `vᵢ ≥ V` but
  `wᵢ > W` does not make the instance trivial. Without the assumption, Lemma 4.3 and the backward half of
  Lemma 4.4 fail even for the paper's own `m`. Take the items `(2, 20), (0, 10)` with `V = 2` and `W = 12`. The
  instance is unsatisfiable, yet `{b, x₁}` is adequate: `x₁`'s `2 E` start the whole chain, which then releases
  the supplier's bitcoins. This example was checked by hand, not in Lean. The reduction therefore first has to
  discard items with `wᵢ > W`, and then answer "yes" directly if some remaining item has `vᵢ ≥ V`.
* **Small slips.** Lemma 4.3 also needs `V ≥ 2`. With `V = 1`, the assumption forces all values to be 0; then
  `(b, y₁) = 0 E` and `{b, z₁}` is adequate although the instance is unsatisfiable. This case is degenerate. In
  Lemma 4.3's proof, `{b, y₁}` and `{b, y_{m+1}}` give `b` no bitcoins, not `min_w(X) − 1`; this is harmless. The
  leader set `{b}` alone is not discussed; it is covered by the same argument.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A transaction graph is a multigraph of contracts. Each contract `e` has a sender, a receiver, an asset and an
  amount, and each party has an initial endowment `own p a` (`TxGraph`, `Model.lean`). Contracts are created one at
  a time, under the HTLCP rules with brokering of §§2–3. A leader may create its outgoing contracts at any time. A
  follower may do so only once all its incoming contracts exist. In both cases the sender must tentatively own the
  amount: its endowment, plus what it received on created incoming contracts, minus what it already escrowed. This
  is the paper's master-contract bookkeeping.
* `Adequate L`: **some** order of creations creates every contract ("the set `L` can create all edges"). The model
  is asynchronous, with no failures and no adversary: everybody conforms, and the broker chooses the order. Secret
  release and triggering are not modelled; the paper's notion of adequacy concerns only edge creation. A minimum
  leader set is an adequate set of minimum cardinality (`IsMinimumLeaderSet`).
* A flower graph (`IsFlower`) has a broker `b` incident to every contract, with contracts to and from every other
  party. Only `b` is a broker, and every other party owns exactly what it sends. In the paper's graphs `b` starts
  with nothing (`brokerOwn`); the paper's case analysis assumes this throughout.
* `flower K m c` is the construction of Figure 2, parameterized by the number of levels `m` and by the bitcoin
  amount `c` on the contracts `(yᵢ, b)`, `2 ≤ i ≤ m`. `paperFlower K` is the paper's choice, `c = min_w(X) − 1` with
  the printed `m`. The construction is a flower graph (`Flower.isFlower`). Knapsack has natural-number values and
  weights.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| §3: every adequate leader set is a feedback vertex set | `TxGraph.Adequate.isFVS` | `Model.lean` |
| §3: without brokering, every FVS is adequate (adequate ⇔ FVS) | `TxGraph.adequate_of_isFVS`, `TxGraph.adequate_iff_isFVS` | `Model.lean` |
| §3: the construction is a flower graph | `Flower.isFlower` | `Flower.lean` |
| Lemma 4.2: **false** (weight 1, any `m`; printed `m`, weights ≥ 2) | `lemma_4_2_false_minW_one`, `paper_minW_one`, `lemma_4_2_false` | `Main.lean` |
| Lemma 4.2, repaired (budget condition) / budget is necessary | `adequate_of_satisfiable` / `budget_of_adequate` | `Run.lean` |
| Lemma 4.3 | `lemma_4_3`, `lemma_4_3_paper` | `Inadequate.lean`, `Main.lean` |
| Lemma 4.4 (backward half, paper's graph) | `satisfiable_of_adequate`, `lemma_4_4_backward_paper` | `Inadequate.lean`, `Main.lean` |
| Lemma 4.4 (any budget-respecting `m`) | `lemma_4_4_of_budget` | `Main.lean` |
| Theorem 4.1: correctness of the reduction | `theorem_4_1_of_budget`, `theorem_4_1_fixed`, `theorem_4_1_repaired` | `Main.lean` |

**Not formalized.** Polynomial running time of the reduction and NP-hardness as a complexity class. We verify the
combinatorial correctness of the reduction: `K` is satisfiable iff `{b, s}` is a minimum leader set, iff minimum
leader sets have size 2. Also not formalized: the example of Figure 1, and the counterexample without the
`vᵢ < V` assumption (hand-checked only).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
hypotheses are not vacuous: `lemma_4_2_false` and `lemma_4_2_false_minW_one` exhibit instances meeting all assumptions (`V ≥ 2`, `vᵢ < V`,
positive weights), and `theorem_4_1_repaired` holds for all such instances. The model is self-contained
(Mathlib only). The two generic tools `Adequate.first_hit` and `Reachable.batch'` are possible CSLib candidates if
another token-game model needs them.
