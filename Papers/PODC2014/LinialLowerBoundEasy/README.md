# Linial's Lower Bound Made Easy — PODC 2014

Juhana Laurinharju, Jukka Suomela. *Brief announcement: Linial's lower bound made easy.* PODC 2014. DOI
[10.1145/2611462.2611505](https://doi.org/10.1145/2611462.2611505). Formalized version: arXiv
[1402.2552](https://arxiv.org/abs/1402.2552) v1 (3 pages, the full text of the brief announcement with complete proofs).

**Verdict: ✏️ Slip.** Everything holds: the reduction from `T`-round algorithms to `(2T+1)`-ary colouring functions,
Lemma 1, Lemma 2, the bound `k + 1 ≥ log* n` and Linial's bound (1) `T ≥ log*(n)/2 − 1`, for every `n`. The only flaw
is that Lemma 2 is stated for every `k` but is false for `k = 1`, a case the proof never uses.

## Mistakes in the paper

### ✏️ Slips
- Lemma 2 is false for `k = 1`: a `0`-ary colouring function would need `A() ≠ A()` by (3), so none exists when
  `n ≥ 1`, although `1`-ary ones exist (`lemma2_false_of_k_eq_one`). The proof only applies it with `k ≥ 2`, and
  Lemma 2 holds for every `k ≥ 2` (`lemma2`).

## The formalization

The paper's proof goes through as written: Lemma 1 by pigeonhole, Lemma 2 with `B` = the set of colours of the
extensions `x_k > x_{k−1}` (the empty set when `x_{k−1} = n` is among the `2^c` values), then Lemma 2 iterated down
to Lemma 1. Bound (1) needs no assumption on `n`. For `n < 2T + 2` there are no `2T + 2` distinct identifiers, so (3)
is vacuous, but the bound still holds because `log* n ≤ n`. For `n = 1` (where `v + 1 = v`) no algorithm exists.

**Model.**
- Deterministic synchronous LOCAL on the directed `n`-cycle: nodes `ZMod n`, edges `v → v + 1`. The nodes carry
  unique identifiers from `{1, …, n}` (`IdAssignment n`), and every such assignment is quantified over.
- A `T`-round algorithm is a function `A` of the radius-`T` window `(id(v − T), …, id(v + T))`, as in §2 and
  Figure 1 (`IdAssignment.window`). `A` must give colours in `{1, 2, 3}` that differ on every edge
  (`Is3ColouringAlgorithm`).
- We also cover the extensional LOCAL formulation: an algorithm is any function `f` of the view
  `j ↦ id(v + j)`, `j : ℤ`, that depends only on offsets `|j| ≤ T` (`IsLocal3ColouringAlgorithm`). Such an `f`
  induces a window function (`windowFun_window`). If `2T + 1 > n`, the window wraps around; that is still the
  information a node has after `T` rounds.
- Colouring functions (§3): `A : (Fin k → ℕ) → ℕ` with (2) and (3) required only on strictly increasing tuples from
  `{1, …, n}` (`IsColouringFunction`).
- `log*` is the paper's real-valued iterated logarithm (`log* x = 0` for `x ≤ 1`, else `1 + log*(log₂ x)`), defined
  as the least `m` with `x ≤ ^m2`. Its two defining equations are proved (`logStar_of_le_one`, `logStar_of_one_lt`).
  This is not CSLib's floor-based `Nat.logStar`. The paper's version is larger (e.g. `log* 3 = 2`, `Nat.logStar 3 = 1`),
  so the bound with it is the stronger one. For `n ≥ 2`, `logStar n = Nat.logStar (n − 1) + 1` (`logStar_natCast`).
- `^i2` is `Nat.tower i` (`tower 0 = 1`, `tower (i+1) = 2^(tower i)`, so `^2 2 = 4`, `^3 2 = 16`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition of `k`-ary `c`-colouring function, (2)–(3) | `IsColouringFunction` | `ColouringFunctions.lean` |
| Lemma 1 | `lemma1` | `ColouringFunctions.lean` |
| Lemma 2 (`k ≥ 2`), the function `B` | `lemma2`, `lemma2B` | `ColouringFunctions.lean` |
| Lemma 2 fails for `k = 1` | `lemma2_false_of_k_eq_one` | `ColouringFunctions.lean` |
| §4: `^{k+1}2 ≥ n` | `le_tower_of_isColouringFunction_three` | `ColouringFunctions.lean` |
| `log*` (§2) | `logStar`, `logStar_of_le_one`, `logStar_of_one_lt` | `LogStar.lean` |
| §3–4: `k + 1 ≥ log* n` | `logStar_le_of_isColouringFunction` | `LogStar.lean` |
| §2: an algorithm satisfies `A(x₁…) ∈ {1,2,3}`, `A(x₁…) ≠ A(x₂…)` | `algorithm_mem`, `algorithm_ne` | `Cycle.lean` |
| §3: algorithm ⇒ `(2T+1)`-ary 3-colouring function | `isColouringFunction_of_algorithm` | `Cycle.lean` |
| Equation (1), `T ≥ log*(n)/2 − 1` | `linial_bound`, `linial_bound_local` | `Cycle.lean` |

**Not formalized.** The remark "the converse is not necessarily true" (§3).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `is3ColouringAlgorithm_three` (on the 3-cycle, "colour = own identifier" is a 0-round algorithm) and
`isColouringFunction_id`. `Nat.tower`/`Nat.logStar` come from CSLib `Cslib.Foundations.Data.Nat.LogStar`; the
`Fin.snoc` lemmas come from the staged `Podc.Foundations.Combinatorics.ShiftGraph`. That module's
`Cslib.ShiftGraph.card_le_iterate_of_proper` is the same argument in a type-generic form. Here it is redone in the
paper's own terms, with colours in `{1, …, c}` and an explicit binary code for the sets of colours.

CSLib candidate: the real-valued `logStar` with its API (`LogStar.lean`).

Full list of differences: [differencies.md](differencies.md).
