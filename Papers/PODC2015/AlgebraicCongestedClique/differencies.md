# Differences between the formalization and the paper

Paper: K. Censor-Hillel, P. Kaski, J. H. Korhonen, C. Lenzen, A. Paz, J. Suomela, *Algebraic Methods
in the Congested Clique*, PODC 2015 (arXiv:1503.04963v1).

## Errors and gaps in the paper

1. **Section 2.1, Step 1 (3D algorithm): wrong recipients of the `T`-blocks.** The paper (checked
   on the rendered page 7) says node `v` sends `T[v, w₃∗∗]` to each `w ∈ ∗v₂∗`, and that `v`
   receives `T[w, v₃∗∗]` from `w ∈ ∗v₂∗`. Node `v` computes `S[v₁∗∗, v₂∗∗] T[v₂∗∗, v₃∗∗]` and so
   needs the rows `v₂∗∗` of `T`. Correct: send to `w ∈ ∗v₁∗` (`w₂ = v₁`); receive from
   `w ∈ v₂∗∗`. With the pattern as written, for `q = n^{1/3} ≥ 2` node `v` misses a needed row
   (`step1_as_written_wrong`). The message counts (`2n^{4/3}`) are unaffected. *Rule:* R3
   (typo, intent evident from "each node `v` receives … `T[v₂∗∗, v₃∗∗]`") → ⚠️.
2. **Lemma 12 is stated without its hypothesis.** The lemma itself says only "It is possible to find
   sets …". It is false for dense graphs: for `K_n`, `n ≥ 67`, disjoint tiles with sides
   `≥ (n−1)/8` cannot fit in `V × V`. It is meant (and used) only under `∑_y deg(y)² < 2n²`, which
   is derived in the sentence before ("Using this bound, we obtain the following lemma"). We add the
   hypothesis, and also `deg(y) < n` (true in a simple graph). *Rule:* R4 (implied assumption,
   holds at the only use) → ⚠️.
3. **Proof of Lemma 12: `f(y)` for `1 ≤ deg(y) ≤ 3`.** "`deg(y)/4` rounded down to the nearest power
   of 2" is not a positive integer for these degrees, but `|A(y)| = f(y) ≥ deg(y)/8 > 0` is needed.
   With `f(y) = 1` the step `∑ f(y)² ≤ ∑ deg(y)²/16` fails. Repaired: `16 f(d)² ≤ d² + 15`
   for all `d` (`sixteen_mul_tileSize_sq_le`), hence `∑ f² ≤ k²` for `n ≥ 3` (via `2k ≥ n + 1`),
   and directly for `n ≤ 2` (`sum_tileSize_sq_le`). The rest of the chain
   (`∑ deg²/16 < n²/8 < k²`) is correct. *Proof repair* (🛠️).
4. **Last step of 4-cycle detection: Lenzen's routing with loads `> n`.** The paper routes
   `P(x,∗,∗)` to `x` with "the dynamic routing scheme [46]", where nodes send `≤ 64n` and receive
   `≤ 2n − 2` words, and concludes `O(1)` rounds. Lenzen's Theorem 3.7 needs loads `≤ n`, and
   splitting without global knowledge needs an argument. We give one (`Prog.exists_routedBig`): one
   round of counts, one round of receiver offsets, then `a·b` routing instances of load `≤ n`
   (sender class × receiver class), in `2 + a·b·16` rounds; the receiver restores the original
   order (`flatMap_sel`). *Proof gap* (🛠️; arguably folklore).

## Modelling choices

5. **Round complexity model** (`Phases.lean`). Programs are sequences of steps. A *direct* step
   costs the length of its longest per-link list (exact congested clique). A *routed* step requires
   send and receive loads `≤ n` and costs `lenzenRounds = 16` rounds: this is Lenzen's Theorem 3.7
   (PODC'13), taken as the cost model. It is formalized in `Papers/PODC2013/CongestedCliqueRouting`
   for opaque messages, but the two formalizations are not composed at the level of rounds. A routed
   step delivers to each receiver the per-source lists in order; this is justified because Lenzen's
   messages carry source and index.
6. **Words.** 4-cycle detection: a word is a triple of natural numbers `≤ 64n` (`WordOK`); node
   ids, degrees, flags, counts and offsets use one component, a 2-walk `(x, y, z)` uses all three.
   This is `O(log n)` bits. Matrix multiplication: a word is one semiring element (the paper also
   assumes `O(log n)`-bit entries).
7. **Constants.** Theorem 4: `≤ 2069` rounds (`1 + 1 + 8 + 8 + (2 + 128·16) + 1`); the paper only
   claims `O(1)`. Theorem 1 (semiring): `≤ 6 n^{1/3}` rounds. We split Step 1 into an `S` step and
   a `T` step of `2q` rounds each, which equals the paper's merged `4q`, and fold Steps 2 and 4 into
   the receive functions.
8. **Oblivious routing.** The paper uses Dolev et al. [24, Lemma 1] as a black box; we prove it
   (`Prog.exists_oblivious`, two hops via König's line-colouring theorem `Matrix.exists_split_parts`
   from CSLib). The intermediate assignment is obtained by `Classical.choice`: deterministic and
   known to all nodes, but not given as an efficient procedure.
9. **Lemma 12 construction.** The paper places the power-of-two squares by an iterative quadtree
   procedure. We use the equivalent Z-order (Morton) placement: sort by decreasing size, lay the
   squares consecutively along the Morton curve. Aligned intervals are exactly aligned squares
   (`morton_div_pow`). Ties are broken by node id. The tiles are a concrete function of the degree
   vector, which every node knows after one broadcast round.
10. **Partitions `N_A(y,a)`, `N_B(y,b)`.** The paper does not specify them. We use `chunk`: the
    element of rank `r` in `N(y)` goes to the element of rank `⌊r/8⌋` in `A(y)` (resp. `B(y)`).
11. **Phase 1 stop.** "The algorithm stops" is implemented by one broadcast of the flags. After it,
    all nodes know whether some flag is set, all further steps send nothing, and the output is
    "yes".
12. **`W(b)`** is defined as `{(x,y,z) ∈ P(∗,∗,∗) : z ∈ N_B(y,b)}`, which equals the paper's
    `⋃_{y : b ∈ B(y)} N(y) × {y} × N_B(y,b)`. Lemma 13 is stated with the hypothesis of the second
    phase (`∑ deg² < 2n²`), as in the paper's context.
13. **Theorem 1** is proved only for `n = q³` (the paper's convention "assume `n^{1/3}` is an
    integer") and over any `NonUnitalNonAssocSemiring` (more general than the paper).
14. **Graphs.** Theorem 4 is for simple undirected graphs (the paper's Section 3.1 uses
    `{x,y} ∈ E`). A 4-cycle is a `SimpleGraph.Walk` cycle of length 4 (`HasFourCycle`).
15. **Lemma 14** is proved for girth exactly `g` (`lemma_14`) and for "all cycles have length
    `≥ g ≥ 3`" (`lemma_14_of_le`). It follows from the Moore bound already in CSLib.
16. **Theorem 15** is not formalized as an algorithm, since it needs Theorem 3 (colour coding,
    `k`-perfect hash families) and fast matrix multiplication. Checked: for `ρ > 0` and
    `ℓ = ⌈2 + 2/ρ⌉`, either `m > n^{1+1/⌊ℓ/2⌋} + n` and the girth is `≤ ℓ`
    (`theorem_15_dense`), or `m ≤ n^{1+1/⌊ℓ/2⌋} + n ≤ 2n^{1+ρ}` (`theorem_15_sparse`). The
    `ρ = 0` case (`ℓ = log log n`) is not covered.

## Not formalized

Lemma 10 and the ring part of Theorem 1, the exponent `ρ`, Corollary 2 (trace formulas),
Lemma 11 and Theorem 3, Corollaries 6–8 and 16, Theorem 9, Lemmas 17–21, Section 4 (lower bounds).
