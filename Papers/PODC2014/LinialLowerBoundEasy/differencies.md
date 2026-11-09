# Differences between the formalization and the paper

Paper: Laurinharju, Suomela, *Linial's lower bound made easy*, PODC 2014 BA; formalized from arXiv 1402.2552v1.

## Mistakes

- ✏️ **Lemma 2 for `k = 1`.** It is stated for every `k`, but for `k = 1` it would produce a `0`-ary colouring
  function. None exists for `n ≥ 1`: (3) requires `A() ≠ A()` (`not_isColouringFunction_zero`,
  `lemma2_false_of_k_eq_one`). `lemma2` is stated for `k + 2`-ary functions (paper's `k ≥ 2`), which is all that the
  iteration in §4 uses.

## Modelling choices and imprecisions (not mistakes)

- **Tuples.** `x₁, …, x_k` is `x : Fin k → ℕ`. `(x₁, …, x_k)` and `(x₂, …, x_{k+1})` are `Fin.init x` and
  `Fin.tail x`. "`1 ≤ x₁ < ⋯ < x_k ≤ n`" is `StrictMono x ∧ ∀ i, x i ∈ Icc 1 n`.
- **Colours are natural numbers** with condition (2) `A x ∈ Icc 1 c`. `A` is a total function on all tuples; its
  values outside increasing tuples of identifiers are irrelevant, as in the paper.
- **Encoding in Lemma 2.** The paper encodes subsets of `{1, …, c}` as integers `{1, …, 2^c}` without fixing the
  encoding. We take `B(x) = 1 + ∑_{a ∈ S} 2^a`, where `S` is the set of extension colours shifted down by one
  (`colourSet`, `lemma2B`). The empty set (when `x_{k−1} = n`) is coded as `1`.
- **`log*`.** The paper's `log*` is over the reals with `log₂`. We define `logStar x` as the least `m` with
  `x ≤ ^m2` and prove both defining equations of the paper (`logStar_of_le_one`, `logStar_of_one_lt`), which
  determine the function. CSLib's `Nat.logStar` (floor of `log₂`) is a different, smaller function: e.g. `3 ↦ 1`
  instead of `2`. Using it would give a weaker theorem. `logStar_natCast` relates the two.
- **Power tower.** `^i2` (with `i` twos) is `Nat.tower i`.
- **Directed `n`-cycle.** Nodes are `ZMod n`, and node `v + 1` is the successor of `v`. Identifiers are an injective
  map into `{1, …, n}` (hence a bijection). For `n = 0` there is no assignment, and for `n = 1` there is no correct
  algorithm. Both theorems hold for all `n`.
- **`T`-round algorithm.** In §2 the paper *defines* the algorithm as a function of the `2T + 1` identifiers within
  distance `T`. We take this as the model (`Is3ColouringAlgorithm`, window of node `v` =
  `(id(v−T), …, id(v+T))`, Figure 1's orientation). We also prove the bound for any `T`-local function of the full
  view `j ↦ id(v + j)` (`linial_bound_local`), which the window model is an instance of. We do not connect it to a
  message-passing round semantics. "Information within distance `T`" is the standard abstraction of `T` LOCAL rounds,
  as the paper states.
- **§2's claim** "`A(x₁…x_{2T+1}) ≠ A(x₂…x_{2T+2})` whenever the `xᵢ` are distinct identifiers" is proved for every
  injective tuple (`algorithm_ne`), by placing the identifiers on consecutive nodes and filling in the remaining
  identifiers (`exists_idAssignment`). The paper leaves this step implicit.
- **The bound `k + 1 ≥ log* n`** is proved for every `k ≥ 0` (for `k = 0`, only `n = 0` admits a colouring function).
- **Not formalized:** "the converse is not necessarily true" (§3).
