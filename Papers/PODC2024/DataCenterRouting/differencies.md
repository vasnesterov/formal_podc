# Differences between the formalization and the paper

Paper: Ferreira, Atre, Sherry, Sobrinho, *Impossibility Results for Data-Center Routing with Congestion
Control and Unsplittable Flows*, PODC 2024 (proceedings version).

## Errors and gaps in the paper (see README)

1. **Theorem 5.4, tightness, even `n`.** The proof assumes "w.l.o.g." that `n` is odd. Nothing in the
   paper reduces even `n` to odd `n`. Proved: odd `n ≥ 3` with every `ε > 1/(n-1)`
   (`theorem_5_4_tight_odd`), and even `n ≥ 4` with every `ε > 1/(n-2)` (`theorem_5_4_tight_even`). The
   paper's bound for even `n` remains open.
2. **Proof of Theorem 5.4 for `n = 3`.** The claimed Doom-Switch max-min fair rates (`1 - 2/(n-1) = 0`
   and `2/(k(n-1)) = 1/k`) are not max-min fair (`doom_paper_rates_not_isMaxMinFair`). They are correct
   for `n ≥ 5`, i.e. `g = (n-1)/2 ≥ 2` gadgets (`doom_clos_isMaxMinFair`). For `n = 3` (and for even
   `n = 4`) the tightness statement is proved with a single flow, since then `2(1-ε) < 1`.
3. **Lemma 4.6, Step 2.** The informal "each increase is paid by a decrease of a flow of equal or
   smaller rate" is made rigorous by the leximin criterion `sortedRates_lt_of_forall`. The formal
   Step 2 (`aStar_criterion`) is stronger: it compares `a*` with every allocation feasible for any
   routing, not only max-min fair ones.
4. **Typo in Lemma 4.6 Step 1.** The type-2.b flow is written `(s_i^1, t_i^j)` instead of
   `(s_i^1, t_{n+1}^j)`.
5. **Unproved cited/"routine" results, all proved here.** Lemma 2.2 (both directions), Lemma 3.2,
   Lemma 4.4, Lemma 4.6 Step 1 (feasibility of the routing and bottlenecks), Lemma 5.2 and the
   Section 2.3 remark that Clos-feasible allocations are macro-switch-feasible.

## Modelling choices

* **Indices are 0-based.** Switch `I_i` / `O_i` is `i - 1 : Fin (2n)`; server `s_i^j` is
  `(i - 1, j - 1) : Fin (2n) × Fin n`; middle switch `M_m` is `m - 1 : Fin n`. In Section 4, `n = k + 1`
  internally (`tor i` for `i < n`, `torN k` for `I_{n+1}`), and the final theorems are stated for `n`.
* **Collections of flows** are finite index types `F` with maps `src`, `dst` (multisets of
  source–destination pairs). A **routing** is `F → Fin n` (the middle switch), equivalent to choosing
  one of the `n` paths.
* **Macro-switch.** The infinite-capacity links between input and output switches are omitted, so a
  flow's path is its two server links. A link of infinite capacity never constrains feasibility and
  can never be a bottleneck, so this is equivalent. Both networks share the link type `Link n`. The
  macro-switch leaves the inner links unused (load `0`).
* **Allocations** are `F → ℝ`. Feasibility includes non-negativity of the rates (the paper says
  "non-negative rate" in the definition of an allocation).
* **Sorted vector and lexicographic order.** `sortedRates a = (univ.val.map a).sort` and Mathlib's
  `LinearOrder (List ℝ)` (lexicographic). All compared vectors have the same length `|F|`, so this is
  the paper's order.
* **"The" max-min fair allocation.** The paper presupposes existence (water-filling) and uniqueness.
  We prove uniqueness (`IsMaxMinFair.eq`) but not general existence. Every theorem either quantifies
  over all max-min fair allocations, or exhibits one, or both. The same holds for `T^MT`, `T^MmF`,
  `a^{L-MmF}`, `a^{T-MmF}`.
* **Definitions 2.4, 2.5, 3.1, 5.1** are `IsLexMaxMinFair`, `IsThroughputMaxMinFair`,
  `Network.IsMaxThroughput` and `IsThroughputMaxThroughput`, quantifying over all routings and all
  max-min fair (resp. maximum-throughput) allocations of these routings.

## Statement-by-statement

* **Lemma 2.2** is proved for arbitrary networks with fixed routing and arbitrary real capacities
  (`Network.isMaxMinFair_iff_hasBottlenecks`). The "only if" direction needs no hypothesis: a flow with
  an empty path makes max-min fairness impossible.
* **Theorem 3.4, lower bound** (`theorem_3_4_lower`): `T^MmF ≥ t(b)/2` for every max-min fair `a` and
  every feasible `b`, i.e. with `T^MT` replaced by the throughput of any feasible allocation (stronger).
  The proof differs from the paper's. It uses the general bound `throughput_le_mul_of_isMaxMinFair`
  (every flow has a saturated link, and every macro-switch path has 2 links) instead of Lemma 3.2.
* **Theorem 3.4, tightness** (`theorem_3_4_tight`): for `n ≥ 1` and every `ε > 0` there are flows (with
  existing max-min fair and maximum-throughput allocations) such that every max-min fair `a` and every
  maximum-throughput `b` satisfy `t(a) ≤ (1+ε) t(b)/2`. The explicit values `T^MmF = 1 + 1/(k+1)`,
  `T^MT = 2` are `gadget_throughputs`.
* **Lemma 3.2** (`lemma_3_2`): the `0/1` allocation of *every* maximum matching is maximum-throughput.
  Matchings of `G^MS` are sets of flows with pairwise distinct sources and destinations (`IsMatching`).
* **Example 4.1 / Theorem 4.2.** `example_4_1` generalizes Example 4.1 to every `n ≥ 3`: no routing
  makes the macro-switch max-min fair rates feasible. `theorem_4_2` states `a↑ ≺ a^MmF↑` for the
  max-min fair allocation `a` of *every* routing, which needs no existence of an L-MmF allocation.
  `theorem_4_2'` uses the flows of Theorem 4.3 and also exhibits an L-MmF allocation.
* **Lemma 4.4** (`lemma_4_4`) is proved for any number `p ≥ 1` of copies of the type-1 flows: `p = n+1`
  in the paper, `p = 1` for Example 4.1.
* **Claim 4.5** (`claim_4_5`). Instead of "the collection consisting only of type 1 and 2 flows", the
  type-3 flow is present with an arbitrary non-negative rate (rate `0` gives the paper's setting).
  Part (1) is stated with the paper's counts `x_i^m`, `y_i^m` (`cnt1`, `cnt2`); part (2) counts the
  type-2.b flows per middle switch. The coprimality of `p` and `n` (used in the paper as
  `lcm(n, n+1) = n(n+1)`) is a hypothesis of the general version. The core lemma `t3_le` needs only
  lower bounds on the type-1/2 rates.
* **Lemma 4.6** (`lemma_4_6`). The routing of Step 1 sends the type-1 flows of server `j+2` of `I_{i+1}`
  through `M_{(i.succAbove j)+1}`, i.e. through all middle switches except `M_{i+1}`, one per server.
  This is equivalent to the paper's `M_{((i+j-2) mod n)+1}`, which also avoids `M_i` exactly once. The
  type-3 flow uses `M_n` as in the paper. Additionally proved: *every* lex-max-min fair allocation
  equals `a*`.
* **Theorem 4.3** (`theorem_4_3`): existence of an L-MmF allocation, and `a(f) = a^MmF(f)/n` for the
  type-3 flow `f` and *every* L-MmF allocation `a`.
* **Lemma 5.2** (`lemma_5_2`): there are a maximum-throughput allocation of `MS_n` and a routing for
  which it is a throughput-maximum-throughput allocation of `C_n`. The link-disjoint routing uses CSLib's
  König line-colouring (`Matrix.exists_split_parts`) on the input/output-switch matrix of a maximum
  matching.
* **Theorem 5.4, upper bound** (`theorem_5_4_upper`): `t(a) ≤ 2 T^MmF` for the max-min fair allocation
  `a` of *every* routing. This is stronger than for `a^{T-MmF}`, and Lemma 5.2 is not needed.
* **Theorem 5.4, tightness.** The statement gives a routing `r` with max-min fair allocation `a` such
  that `t(a) ≥ 2(1-ε) T^MmF`, and the same bound for every throughput-max-min fair allocation. The
  construction stacks `g` gadgets on `I_1`/`O_1` with `q` type-2 flows each. The type-2 flows go
  `(s_1^{2p+1}, t_1^{2p})` (0-based), as in the paper's `(s_1^j, t_1^{j-1})`, `j` even. The routing
  (`doomRouting`) is the output of Algorithm 1 on this input: the type-1 flows form the maximum
  matching, each on its own middle switch; the type-2 flows all use middle switch `2g` (0-based). The
  algorithm itself (maximum matching, colouring, choice of `m'`) is not formalized in general.
* **Example 5.3** (`example_5_3`): `n = 7`, three gadgets, one type-2 flow each; `9/2 → 5`.

## Not formalized

* Example 2.3 (an illustration of bottleneck transfer).
* Algorithm 1 as a general algorithm.
* General existence of max-min fair allocations.
* The informal Theorems 1.1–1.3 (they are the formal Theorems 3.4, 4.3 and 5.4).
* The discussion in Sections 6–7.
