# Brokering with HTLCs is NP-hard — PODC 2021

Eric Chan, Mohsen Lesani. *Brief Announcement: Brokering with Hashed Timelock Contracts is NP-Hard.* PODC 2021.
DOI [10.1145/3465084.3467952](https://doi.org/10.1145/3465084.3467952). Formalized version: the 4-page proceedings
version (no arXiv version exists).

**Verdict: 🔧 Easy fix.** The reduction from Knapsack to minimum leader sets in flower graphs is right in spirit, and
two local changes make it correct (`theorem_4_1_repaired`): double all weights and the capacity first, and read the
number of levels `m` with the parenthesis in its intended place. Lemma 4.2 (and the forward half of Lemma 4.4) is
false for the construction as printed, while Lemma 4.3 (for `V ≥ 2`) and the backward half of Lemma 4.4 hold. What is
checked is the combinatorial correctness of the reduction: its polynomial running time and NP-hardness as a complexity
class are not formalized.

## Mistakes in the paper

### 🔧 Lemma 4.2 (and the forward half of Lemma 4.4) for instances with a weight-1 item
When some item has weight 1, the "bitcoin pump" contracts `(yᵢ, b)` carry `min_w(X) − 1 = 0` B, so for the
satisfiable instance `(v, w) = (1, 1), (1, 1), (1, 2)`, `V = 2`, `W = 2` the flower graph has no adequate leader
set for any number of levels `m` (`lemma_4_2_false_minW_one`, `paper_minW_one`).

**Impact.** The construction cannot work on such instances. They are ordinary Knapsack instances, weight-1 items are
not a degenerate case, the paper reduces from Knapsack in general, and it gives no way to handle them. A new first
step, doubling all weights and the capacity, repairs the reduction (`theorem_4_1_repaired`).

**Details.** The `y`-parties are the broker's only bitcoin source besides the supplier: each `yᵢ`,
`2 ≤ i ≤ m`, pays `(min_w(X) − 1)` B. With `min_w(X) = 1` they pay nothing, so the flower graph is adequate
only if all items fit into the knapsack, whatever `m` is. The instance above is satisfiable (the first two
items) and meets all the paper's assumptions; even every single item fits. But `Σ_w(X) = 4 > 2 = W`. The
intended formula for `m` (see the slips) divides by zero here. The amount `min_w(X) − 1` cannot simply be raised:
Lemma 4.3's proof needs it to be below every weight.

**Repair.** Double all weights and the capacity first (`theorem_4_1_repaired`).

### ✏️ Slips
- Lemma 4.2, number of levels (all weights ≥ 2). The printed `m = ⌈Σ_w(X)/min_w(X) − 1⌉ + 1` has a misplaced
  parenthesis. It equals `⌈Σ_w(X)/min_w(X)⌉`, which is too small: for the satisfiable instance
  `(v, w) = (1, 2), (1, 2), (1, 4)`, `V = 2`, `W = 4` (which meets all the paper's assumptions) `m = 4` and the broker
  gets at most `4 + 3·1 = 7 < 8`, so the flower graph has no adequate leader set at all (`lemma_4_2_false`). The broker
  `b` starts with nothing and must pay every item contract `(b, xᵢ) = wᵢ B`, so it must receive `Σ_w(X)` bitcoins in
  total. Its only bitcoin income is `W` from the supplier `s` and `min_w(X) − 1` from each of `y₂, …, y_m`. So
  `Σ_w(X) ≤ W + (m − 1)(min_w(X) − 1)` is necessary for **any** leader set to be adequate, whatever the schedule
  (`budget_of_adequate`). The intent is `m = ⌈Σ_w(X)/(min_w(X) − 1)⌉ + 1`: writing `⌈x − 1⌉ + 1` instead of `⌈x⌉` makes
  no sense otherwise, and the proof's "left with at least `Σ_w(X)` B" holds exactly for that reading. The reduction is
  correct for every `m ≥ 1` that satisfies the budget (`lemma_4_4_of_budget`, `theorem_4_1_of_budget`), in particular
  for the intended `m`, whenever all weights are ≥ 2 (`theorem_4_1_fixed`).
- Lemma 4.3's proof assumes that no single item has value `≥ V`, justified by "otherwise the Knapsack problem is
  trivial", but an item with `vᵢ ≥ V` and `wᵢ > W` does not make the instance trivial. The lemmas are true under the
  stated assumption (`lemma_4_3`, `satisfiable_of_adequate`). Without it, Lemma 4.3 and the backward half of Lemma 4.4
  fail even for the paper's own `m`: take the items `(2, 20), (0, 10)` with `V = 2` and `W = 12`. The instance is
  unsatisfiable, yet `{b, x₁}` is adequate: `x₁`'s `2 E` start the whole chain, which then releases the supplier's
  bitcoins. This example was checked by hand, not in Lean. The reduction first has to discard items with `wᵢ > W`,
  and then answer "yes" directly if some remaining item has `vᵢ ≥ V`.
- Lemma 4.3 also needs `V ≥ 2`. With `V = 1`, the assumption `vᵢ < V` forces all values to be 0; then
  `(b, y₁) = 0 E` and `{b, z₁}` is adequate although the instance is unsatisfiable. This case is degenerate.
- The reduction needs positive weights, which the paper never states: a weight-0 item can be funded for free and
  `min_w(X) − 1` is meaningless. This is standard for Knapsack (`theorem_4_1_repaired`).
- Lemma 4.2's proof says "after repeating this process `m` times", but only the `m − 1` parties `y₂, …, y_m` send
  bitcoins; the `+ 1` in the intended `m` pays for this (`adequate_of_satisfiable`).
- In Lemma 4.3's proof, `{b, y₁}` and `{b, y_{m+1}}` give `b` no bitcoins, not `min_w(X) − 1`; this is harmless.

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

**Not formalized.** Polynomial running time of the reduction, the closing remark that Knapsack stays NP-hard for
polynomially bounded weight ratios, and NP-hardness as a complexity class. We verify the
combinatorial correctness of the reduction: `K` is satisfiable iff `{b, s}` is a minimum leader set, iff minimum
leader sets have size 2. Also not formalized: the example of Figure 1, the counterexample without the
`vᵢ < V` assumption (hand-checked only), and the step that discards overweight items.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
hypotheses are not vacuous: `lemma_4_2_false` and `lemma_4_2_false_minW_one` exhibit instances meeting all assumptions (`V ≥ 2`, `vᵢ < V`,
positive weights), and `theorem_4_1_repaired` holds for all such instances. The model is self-contained
(Mathlib only). The two generic tools `Adequate.first_hit` and `Reachable.batch'` are possible CSLib candidates if
another token-game model needs them.
