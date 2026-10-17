# Differences between the formalization and the paper

Paper: Brandt, Olivetti. *Truly Tight-in-Δ Bounds for Bipartite Maximal Matching and Variants.*
PODC 2020, arXiv 2002.08216v1. Throughout, `Δ = d + 1` in Lean.

## Statements that are false or ill-defined

1. **Theorem 1.2 and the last sentence of §6 are false for `y = Δ` (false only in a degenerate case).**
   Theorem 1.2 says "the x-maximal y-matching problem requires exactly `T_Δ(x, y)` rounds" and §6 ends with
   "for any combination of integers `x ≥ 0, y ≥ 1, Δ ≥ 2`, our bound of `T_Δ(x, y)` is truly tight". For
   `y = Δ` and `x < Δ`, `T_Δ(x, Δ) = 2·1 − 1 = 1`, but the problem is 0-round solvable (all edges matched),
   as the paper itself notes after Theorem 4.5 and in §5. Lean: `theorem_1_2_false_y_eq_Δ`
   (`Degenerate.lean`). For `x > Δ` the formula for `T_Δ` is meaningless (negative ceilings); Lean's `Tval`
   uses truncated subtraction. We prove Theorem 1.2 for `0 ≤ x ≤ Δ`, `1 ≤ y ≤ Δ − 1` (the range of
   Theorem 4.5 and §5).
2. **Lemma 4.3 names a problem outside the family when `x > Δ − y` (under-specified).** `Ψ^W_Δ(a, b, c)` is
   defined only for `a + b ≤ Δ`, but Lemma 4.3 (stated for all `0 ≤ x ≤ Δ`) produces `Ψ^W_Δ(y, x, 0)`. We
   prove it with `Ψ^W_Δ(y, min{x, Δ − y}, 0)` (`lemma_4_3`); for `x ≤ Δ − y` this is the paper's problem.
   The proof of Theorem 4.5 only needs the lemma when `⌈(Δ − x)/y⌉ ≥ 2`, i.e. `x < Δ − y`, where both
   versions coincide; so Theorem 4.5 is unaffected.

## Proof gaps (statements true)

3. **Configurations containing `∅` (proof gap, harmless).** `R_B(Π)` takes labels from `2^{Σ_Π}`, which contains
   `∅`. A configuration containing `∅` satisfies the universal condition vacuously and can be maximal, e.g.
   `(∅, MZPOX, …, MZPOX)` for `Ψ^W_Δ(a, b, c)` with `a ≤ Δ − 2` (adding any label to `∅` creates a choice with
   `Δ − 1 > a` labels from `{M, Z}`). It cannot be extended to any of the three configurations listed in the
   proof of Lemma 4.1 (they contain at most `a` sets `MZPOX`), so the first claim of that proof ("any
   configuration in the black constraint of `R_B(Ψ^W_Δ(a, b, c))` can be extended to one of …") is false; the
   case analysis silently assumes nonempty sets. The same applies to Lemmas 4.2 and 4.3. The lemmas
   themselves are fine because `∅` can never occur in a correct solution (the white side's existential
   constraint rejects it), and the round elimination theorem only produces nonempty sets. We define `R_B`,
   `R_W` with nonempty sets only (`univC`), which makes the round elimination theorem (slightly) stronger.
   Lean witness of the failing claim: `emptyConf_counterexample` (`EmptySet.lean`).
4. **Theorem 4.5, the case `⌈(Δ − x)/y⌉ = 1`.** The general formulas `b = (⌈(Δ−x)/y⌉ − 1)·y`,
   `c = x + (⌈(Δ−x)/y⌉ − 2)·y` are meaningless for `⌈(Δ−x)/y⌉ = 1`; this case (`T = 2`, resp. `T = 1`) needs
   that `Φ'(x, y)` (resp. `Φ^W_Δ(x, y)`) is not 0-round solvable, which the proof asserts without argument
   ("with an analogous argumentation … if and only if `x = Δ` or `y = Δ`"). We prove the needed directions
   (`phi'_not_zero`, `phi_not_zero`). The proof also ignores the caps `min{c + a, Δ − a}` of Lemma 4.1; they are
   inactive because the uncapped values stay `≤ Δ − y − 1` (`seqBC_le`, `seqU_even`, `seqU_odd`).
5. **Lemmas 4.1–4.3, maximality arguments.** The paper argues via maximality ("any set containing `M` must
   also contain `X`") and Lemma 2.4/Observation 2.5. We do not use maximality: for *every* universally good
   configuration of nonempty sets we construct the target configuration directly (sorting the ports into
   classes). This proves a stronger statement. The hypotheses `b, c ≤ Δ − a` of Lemma 4.1 are not needed.

## Errors in the algorithm's output rule (§5; proof errors, bound true)

6a. **Output of white nodes after the last round.** The output rule ("white matched nodes output M on matched
   edges and O on all the others, while white unmatched nodes output P on all the edges where they sent a
   proposal and X on all the others") ignores proposals that black nodes sent in the last round. These must be
   accepted at output time: a white node with pending proposals (and no match) picks one and outputs M on it.
   Otherwise an unmatched black node that proposed in the last round can see more than `x` labels X. The text
   hints at this ("white nodes … output the solution without informing black nodes"). We implement the
   corrected rule. The literal rule fails, e.g., for `Δ = 2`, `x = y = 1` (2 rounds) on the 8-cycle
   `w0 b1 w1 u w2 b2 w3 b3`: `w0, w1` propose to `b1`, `w2, w3` to `b2`; `b1` accepts `w0`, `b2` accepts `w3`;
   `u` proposes to `w1`; then `w1, w2` are unmatched and both output `X` towards `u`.
6b. **The `2⌈(Δ−x)/y⌉ − 1` variant (black nodes start, `x = 0` solved).** Whites are active only `k − 1` times
   there, so "P on the edges where they sent a proposal" can give fewer than `Δ − x` labels P. Unmatched whites
   must output P on *all* edges; this is valid because every unmatched black node proposed to all its `Δ`
   neighbours (`k·y ≥ Δ`), so every neighbour of an unmatched white node is matched. The paper's sentence "if
   one side is matched or proposed to all neighbours, then there is no reason for the other side to send
   additional proposals" is the idea; we implement it. The literal rule fails already for BMM with `Δ = 2`
   (3 rounds) on a suitably port-numbered 6-cycle (an unmatched white node outputs `P X`).
6c. The proof that every node has at most `y` matched edges needs that a proposal batch is answered exactly one
   round later (the last batch is tracked explicitly in the state). The upper bound is proved on *all*
   `Δ`-regular properly 2-coloured port-numbered (multi)graphs, not only trees.

## Typos

6. Theorem 2.1: "black (resp. white) complexity `min{0, T(n, Δ) − 1}`" should be `max{0, T(n, Δ) − 1}`.
7. Proof of Lemma 4.1: "the black constraint of `R_B(Ψ^W_Δ(a, b, c))` is obtained by applying the universal
   quantifier to the *white* constraint" — it is the black constraint.
8. Theorem 1.2: "2-colored Δ-regular balanced trees" is imprecise: finite trees have leaves of degree 1, while
   the encoded problems are defined for `Δ`-regular graphs. The lower bound holds on the infinite 2-coloured
   Δ-regular tree (and on high-girth graphs). We use infinite trees.

## Modelling choices

9. **Model.** Deterministic port-numbering model, 2-coloured `Δ`-regular trees, no identifiers, no randomness;
   the colour is the only input. A `t`-round algorithm is a function of the radius-`t` view (`View d t`,
   `Solves`), which is exactly what a node can learn in `t` rounds in a tree. `Bridge.lean` connects this to
   CSLib's message-passing algorithms (`Algorithm Bool (ℕ → L)`): the state of every node of any
   `Δ`-regular properly 2-coloured port-numbered graph is a function of its view (`state_eq`), and every view
   is realized at the root of an explicit port-numbered infinite tree (`treeGraph`, `viewOf_treeGraph_root`).
   The paper works with `Δ`-regular bipartite graphs of girth `≥ 4Δ + 2` (with `n` possibly known); the
   transfer from trees to finite high-girth graphs (existence of such graphs, locality of algorithms that know
   `n`) is not formalized.
10. **White algorithms.** As in the paper, complexities are white (resp. black) complexities: only the white
    nodes output, and the black constraint is checked on the labels their white neighbours wrote. The
    "natural" version of x-maximal y-matching (both endpoints know the matching; Definition 1.1) and its
    1-round equivalence with the encoded problem `Φ^W_Δ(x, y)` (§4) are not formalized; all statements are
    about the encoded problem, as in the paper ("All the results … refer to the locally checkable encoded
    version").
11. **Round elimination.** We prove only the forward direction of Theorem 2.1 (the one used for lower bounds),
    in the bipartite form, from scratch (`re_forward`, `theorem_2_1`, `theorem_2_1_dual`), without the
    maximality simplification and without "removing unused sets". Relaxations are 0-round relabellings of
    the active side's own configuration (`Relax`), as in §2.2.
12. **Problems.** `Φ^W_Δ(x, y)`, `Φ'(x, y)`, `Ψ^W_Δ(a, b, c)` are transcribed literally as unions of condensed
    configurations (`Cond.Gens`), with truncated subtraction in exponents (`Δ − a − b` etc.).

## Not formalized

13. Theorems 1.3, 1.4 and §6 (randomized and LOCAL-model lower bounds): they rely on the cited Lemma 6.1
    (Lemma 41 of Balliu et al., randomized round elimination) and on ID-generation / gap arguments.
14. §7 (automation) and §8 (open problems): no formal claims.
