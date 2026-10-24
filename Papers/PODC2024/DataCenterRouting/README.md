# Data-Center Routing with Congestion Control — PODC 2024

Miguel Alves Ferreira, Nirav Atre, Justine Sherry, João Luís Sobrinho. *Impossibility Results for
Data-Center Routing with Congestion Control and Unsplittable Flows.* PODC 2024. DOI
[10.1145/3662158.3662777](https://doi.org/10.1145/3662158.3662777). Formalized version: the PODC
proceedings version (no arXiv version); numbering follows it.

**Verdict: ⚠️ Correct with fixes.** Theorems 3.4, 4.2 and 4.3, the upper bound of Theorem 5.4 and
all lemmas are correct. The proofs that the paper omits as "routine" (Lemma 2.2, Lemma 3.2, Lemma 4.4,
Lemma 4.6, Lemma 5.2) are also proved here. The tightness part of Theorem 5.4 is proved only for odd
`n`. The paper reduces to odd `n` "without loss of generality", but for even `n` its construction gives
only `ε → 1/(n-2)`. The proof of Theorem 5.4 also computes wrong rates for `n = 3`.

## Mistakes in the paper

* **Theorem 5.4, second part: the "w.l.o.g. `n` odd" step is unjustified.** The claim is: for every
  `n ≥ 3` and every `ε > 1/(n-1)`, some collection of flows has `T^{T-MmF} ≥ 2(1-ε) T^MmF`. The proof
  stacks `(n-1)/2` copies of the gadget of Example 3.3 and uses one extra middle switch as the "doom"
  switch. This needs `n` odd. For even `n` the same idea fits only `(n-2)/2` gadgets, which gives
  `ε > 1/(n-2)`. Other gadget shapes do not seem to help. By an informal count (not formalized):
  take `L ≤ n-1` type-1 flows on `I_1`/`O_1` forming chains of length ≥ 2, consecutive flows of a
  chain joined by a bundle of `k` type-2 flows, `B` bundles in all, every bundle on the doom
  switch. Then the Doom-Switch throughput is `L(1 - 1/B) + 1`, while `T^MmF → B ≥ L/2`. For even
  `n` the best ratio is `max(2 - 2/(n-2), 2 - 4/n + 4/n²)`, still below `2(1 - 1/(n-1))`. (For
  `n = 4` a single chain of three type-1 flows gives ratio `→ 5/4`, i.e. `ε → 3/8`. This beats the
  formalized `1/(n-2) = 1/2` but not the paper's `1/3`.) We prove the claim for odd `n` and the
  weaker bound `ε > 1/(n-2)` for even `n ≥ 4`. Whether the claim holds for even `n` is open. This is a proof gap in a stated
  theorem. The paper's message ("the bound becomes tight as `n` grows") is unaffected.
  (`theorem_5_4_tight_odd`, `theorem_5_4_tight_even`)
* **Proof of Theorem 5.4, `n = 3`: the Doom-Switch rates are wrong.** The proof says that under the
  Doom-Switch routing the type-1 flows get `1 - 2/(n-1)` and the type-2 flows get `2/(k(n-1))`. For
  `n = 3` this gives type-1 rate `0` and type-2 rate `1/k`. That allocation is not max-min fair: the
  type-1 flows have no bottleneck, and giving every flow `1/(k+1)` is feasible for the same routing and
  lexicographically larger. The rates are correct for odd `n ≥ 5`, where `k(n-3) ≥ 2`. The statement
  for `n = 3` is still true, trivially, because then `2(1-ε) < 1`. (`doom_paper_rates_not_isMaxMinFair`;
  correct rates: `doom_clos_isMaxMinFair`)
* **Lemma 4.6, Step 2, is only sketched; the statement is true.** The paper argues that every routing
  that raises some rate must lower "a flow of equal (or no greater) rate", and concludes `a*↑ ⪰ a_r↑`.
  It never states which lexicographic principle makes this inference valid, especially when several
  rates change at once. We prove this principle in general (the *leximin criterion*): if `a ≠ b` and
  every flow that gains in `b` is matched by a flow of no larger `a`-rate that loses in `b`, then
  `b↑ ≺ a↑`. With it, Step 2 shows more than the paper claims: `a*` lex-dominates every allocation that
  is feasible for *any* routing, whether max-min fair or not. Hence the lex-max-min fair allocation is
  unique and equals `a*`. (`sortedRates_lt_of_forall`, `aStar_criterion`, `lemma_4_6`)
* **Omitted "routine" proofs; all statements are true.** Lemma 2.2 is cited from [6,28]. Lemma 3.2
  and Lemma 5.2 are "folklore", and Lemmas 4.4 and 4.6 (Step 1) are left to the reader. All of them
  are proved here: Lemma 3.2 via König's theorem in Hall-deficiency form, Lemma 5.2 via König's
  line-colouring theorem. (`isMaxMinFair_iff_hasBottlenecks`, `lemma_3_2`, `lemma_5_2`, `lemma_4_4`,
  `aStar_isMaxMinFair`)
* Typos and small slips:
  * In the routing of Lemma 4.6, the type-2.b flow is written `(s_i^1, t_i^j)`. It should be
    `(s_i^1, t_{n+1}^j)`.
  * Definitions 2.4/2.5 speak of "the" max-min fair allocation of every routing. Existence
    (water-filling) is assumed; we prove uniqueness, and our statements do not need existence.
  * The proof of Theorem 5.4 writes `T^{T-MmF} ≤ T^{T-MT} = T^MT`. Only `≤` is needed, so Lemma 5.2
    is not used for the bound.
  * In (R1), "max-main" should be "max-min".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Static rate allocation; there is no dynamics, so synchrony, failures and randomness do not arise.
  A collection of flows is a finite type `F` with source and destination servers
  (`Server n = Fin (2n) × Fin n`). A routing assigns a middle switch to every flow (unsplittable
  flows). An allocation is `F → ℝ`. It is feasible if all rates are non-negative and every link's
  load is at most its capacity.
* `C_n` (`clos fl r`): `n` middle switches, `2n` input and `2n` output switches, `n` servers per
  switch, unit capacities. A flow's path is its two server links plus `I M_{r f}` and `M_{r f} O`.
  `MS_n` (`macroSwitch fl`): a flow traverses only its two server links. The infinite-capacity
  links between switches are omitted, since they never constrain an allocation.
* Max-min fair (`IsMaxMinFair`): the sorted rate vector (`Multiset.sort`) is maximum in Mathlib's
  lexicographic order on `List ℝ`. Lex-max-min fair and throughput-max-min fair are defined over all
  routings exactly as in Definitions 2.4/2.5.
* Statements quantify over *every* max-min fair, maximum-throughput, lex-max-min fair or
  throughput-max-min fair allocation, and separately exhibit one. So they do not rely on the
  (unformalized) general existence of max-min fair allocations. Indices are 0-based.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.2 (bottleneck property), uniqueness of MmF | `Cslib.RateAllocation.Network.isMaxMinFair_iff_hasBottlenecks`, `IsMaxMinFair.eq` | `Podc/Computability/Distributed/RateAllocation/MaxMinFair.lean` |
| §2.3: Clos-feasible ⇒ MS-feasible, `a^MmF↑ ⪰ a^{L-MmF}↑` | `Feasible.toMacroSwitch`, `sortedRates_le_of_clos` | `Model.lean` |
| Lemma 3.2 | `lemma_3_2` (König: `exists_matching_sum_le`) | `Matching.lean` |
| Example 3.3 | `example_3_3` | `Section3.lean` |
| Theorem 3.4 | `theorem_3_4_lower`, `theorem_3_4_tight` (`gadget_throughputs`) | `Section3.lean` |
| Example 4.1 | `example_4_1` | `Section4.lean` |
| Theorem 4.2 | `theorem_4_2` (Example 4.1 flows, every routing), `theorem_4_2'` (Theorem 4.3 flows, with an L-MmF allocation) | `Section4.lean` |
| Lemma 4.4 | `lemma_4_4` | `Section4.lean` |
| Claim 4.5 | `claim_4_5` (core: `exists_perm_of_feasible`, `t3_le`) | `Section4.lean` |
| Lemma 4.6 | `lemma_4_6` (existence and uniqueness of the L-MmF allocation) | `Section4.lean` |
| Theorem 4.3 | `theorem_4_3` | `Section4.lean` |
| Lemma 5.2 | `lemma_5_2` (routing: `exists_routing_feasible_of_isMatching`) | `Section5.lean`, `LinkDisjoint.lean` |
| Example 5.3 | `example_5_3` | `DoomSwitch.lean` |
| Theorem 5.4 | `theorem_5_4_upper`, `theorem_5_4_tight_odd`, `theorem_5_4_tight_even` | `Section5.lean`, `DoomSwitch.lean` |
| Proof of Thm 5.4, `n = 3` slip | `doom_paper_rates_not_isMaxMinFair` | `DoomSwitch.lean` |

`theorem_3_4_lower` is proved through the general bound `throughput_le_mul_of_isMaxMinFair`: if every
path has at most `k` links, every feasible allocation has throughput at most `k · T^MmF`. This replaces
the paper's matching argument, which is also correct. Lemma 3.2 is proved separately.

**Not formalized.** Example 2.3. Algorithm 1 (Doom-Switch) as a general algorithm: only its output on
the adversarial collection is formalized, as the explicit routing `doomRouting`. Existence of max-min
fair allocations (water-filling) in general. Whether Theorem 5.4's tightness holds for even `n`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity: every theorem with max-min fair or lex-max-min fair hypotheses comes with
an explicit allocation satisfying them (`gadget_isMaxMinFair`, `lemma_4_4`, `lemma_4_6`,
`doom_macroSwitch_isMaxMinFair`, `doom_clos_isMaxMinFair`, `exists_isMaximumMatching`). The model is
new. The general max-min fairness layer is staged in `Podc/Computability/Distributed/RateAllocation/`.
CSLib's `Matrix.exists_split_parts` (König line colouring) is used for Lemma 5.2.

**CSLib candidates.** `Podc/Computability/Distributed/RateAllocation/MaxMinFair.lean` (whole file);
`exists_matching_sum_le` (fractional matching number = matching number of a bipartite multigraph) in
`Matching.lean`; `exists_map_card_filter_eq` (distributing a finite set with prescribed fibre sizes) in
`LinkDisjoint.lean`.
