# Differences between the formalization and the paper

Paper: L. Feuilloley, *Brief Announcement: Average Complexity for the LOCAL Model*, PODC 2015
(arXiv 1505.05072v1, identical text).

## Model

1. **Oriented rings.** We formalize rings with a consistent orientation (`IdRing`; node `v + 1` is
   the right neighbour of `v`), and views are the sequences `j ↦ id (v + j)`. The paper's LOCAL
   model on cycles has no orientation. Every algorithm for unoriented rings is an algorithm for
   oriented rings with the same radii, so the lower bound (Theorem 1) for oriented rings implies the
   one for unoriented rings. Lemmas 2 and 3 are proved for minimality within the class of oriented
   algorithms (which is what the oriented Theorem 1 needs).
2. **Views wrap around.** For `2r + 1 > n` the view of radius `r` is the periodic sequence, not the
   ball as a graph. Both carry the same information (the ball of radius `⌊n/2⌋` is the whole ring,
   which determines the periodic sequence, and conversely).
3. **Algorithms** (`Alg C`) decide at each radius `r` from the view restricted to `[-r, r]` whether to
   stop and with which output; the radius `r(v)` is the first radius at which the node stops
   (`Alg.rad`). They do not know `n` (as in the paper). Identifiers are arbitrary distinct
   naturals, and validity (`Alg.Valid`) is required on all rings of all sizes `n ≥ 3` with all
   identifier assignments. The paper's construction implicitly needs this too (it runs the same
   algorithm on smaller cycles whose identifiers are a subset of `{1, …, n}`).
4. **Theorem 1's ring** uses identifiers `{0, …, n - 1}` (a permutation of them), the paper's
   "permutation of the identifiers". The total radius is summed over positions `0, …, n - 1`.
5. Lemma 2 is stated in the paper for "a graph `G` with identifiers"; only cycles are meant and only
   cycles are formalized.

## Gaps and errors in the paper's proof (all repaired; Theorem 1 holds)

6. **"Without loss of generality … only for minimal algorithms" is unjustified.** The paper gives no
   argument that a minimal algorithm below a given one exists. There are infinitely many
   neighbourhoods, so a descending sequence of improvements need not stop, and the limit of a chain
   of algorithms is not obviously an algorithm (the outputs need not converge). We prove existence
   by Zorn's lemma on radius functions plus a compactness argument (Tychonoff) for the outputs of
   the limit algorithm (`Alg.exists_isMinimal_le`, `exists_valid_le_of_isChain`, `Minimal.lean`).
7. **Lemma 3's reduction from 3- to 4-colouring is invalid.** Lemma 2 is proved for algorithms that
   are minimal *among 4-colouring algorithms*. Lemma 3 is stated for algorithms minimal among
   3-colouring algorithms, and its proof says "it is sufficient to prove the result for
   4-colouring, as it implies the result for 3-colouring". But a 3-colouring algorithm that no
   3-colouring algorithm improves may still be improved by a 4-colouring algorithm (Lemma 2's
   modified algorithm uses all 4 colours), so Lemma 2 does not apply to it. We do not know whether
   Lemma 3 as stated (minimal for 3-colouring) is true; we neither prove nor refute it. Repair: we
   state Lemma 3 for minimal 4-colouring algorithms and prove Theorem 1 for all 4-colouring
   algorithms (`theorem_1_four`). A 3-colouring algorithm is a 4-colouring algorithm with the same
   radii (`Alg.map`, `Valid.map`), which gives the 3-colouring statement (`theorem_1_three`,
   `theorem_1`). This needs Linial's bound for 4-colourings rather than 3-colourings
   (`Alg.exists_lt_radAt_four`).
8. **Lemma 2: ring size.** We assume the ring has at least `2T + 1` nodes, where
   `T = max {r(x), r(y)} + k` is the threshold, so the radius-`T` views do not wrap. The modified
   algorithm `A'` then also checks that the `2T + 1` identifiers it sees are distinct. This makes
   the node's offset `d` from `x` well defined. The paper's proof ignores wrap-around. Lemma 3 and
   Theorem 1 only use the lemma in this case. When `2T + 1 > n` and `2r + 1 ≤ n`, the inequality
   `r ≤ T` that Lemma 3 needs holds trivially. We have not checked whether Lemma 2 holds without
   this hypothesis.
9. **Lemma 2: orientation.** The paper picks the orientation "w.l.o.g. `ID(x) > ID(y)`". With oriented
   rings, `x` is simply the left end. The paper's `d` is "the distance between `v` and `x`"; we use
   the offset along the segment from `x` to `y`. The colour rules are the paper's. A neighbour that
   stopped strictly before the threshold is avoided. If some neighbour did not stop before the
   threshold, the colour is taken in `{0, 1}` (even `d`) or `{2, 3}` (odd `d`). When both neighbours
   stopped early, any colour avoiding both is chosen (the paper leaves this case implicit).
10. **Lemma 3: `r` versus `r(v)`.** We assume `r ≤ r(v)` instead of `r = r(v)` and require
    `2r + 1 ≤ n`. The paper applies Lemma 3 in Theorem 1 with `r = ½ log*(n/2)`, and the centre's
    radius is only known to be at least that. With `r = r(v)` the ball of radius `r(v)/2` could
    exceed the slice, so this is the form the proof needs. The quantitative form is
    `r + h (r - h) ≤ ∑_{|j| ≤ h} r(v + j)` with `h = ⌊r/2⌋`, and the average over the `2h + 1` nodes
    is at least `r / 4`. The paper only writes `Ω(r)`.
11. **Linial's bound as a black box.** The paper cites "for every algorithm that 3-colours a cycle
    of length larger than `n/2`, there exists a permutation of the identifiers such that at least
    one vertex needs a radius of `½ log*(n/2)`". The exact constant (no `- O(1)`) is not justified
    by the citation. We prove our own version from scratch, for any number of colours, with the
    shift-graph argument: if `|S| > tower (2t + 2)`, every valid 4-colouring algorithm has a node
    of radius `> t` on some ring with identifier set `S` (`Alg.exists_lt_radAt_four`; general `C`:
    `(2^·)^[2t] |C| < |S|`). We use `R = ⌊(log*(n/2) - 1)/2⌋` in place of `½ log*(n/2)`.
12. **Constants in Theorem 1.** The paper states `Ω(log* n)`. We prove the explicit bounds
    `n ⌊(log*(n/2) - 1)/2⌋ ≤ 16 ∑_v r(v)` and `n (log* n - 3) ≤ 32 ∑_v r(v)` for every `n ≥ 3`
    (`theorem_1_three`, `theorem_1`), and the average form `(log* n - 3)/32 ≤ (∑_v r(v))/n`
    (`theorem_1_average`).
13. **Slice bookkeeping in Theorem 1.** The paper removes "a `½ log*(n/2)`-ball around a vertex with
    large radius" until fewer than `n/2` identifiers remain. We remove slices of exactly `2R + 1`
    identifiers while more than `⌊n/2⌋` remain (`exists_slices`). The remaining identifiers are
    appended in increasing order. We note that the slice must be the ball in the ring produced by
    Linial's bound for the *remaining* identifiers, and that the centre's radius in `π` is
    `≥ R` because its views of radius `< R` are unchanged (the paper says the whole `R`-neighbourhood
    is "exactly the same", which is what we use).

## Section 2 (largest ID)

14. **"Has seen all the cycle"** (the stopping rule of the straightforward algorithm) is made precise
    as "some identifier appears twice in the window". A node that does not know `n` has no other way
    to tell it has seen the whole ring. Correctness of the algorithm is proved
    (`LargestId.straightforward_correct`).
15. **Worst case.** The paper says the maximum "needs `n/2` rounds". We prove that for every correct
    algorithm, on *every* ring the maximum node has radius `≥ ⌊n/2⌋` (`LargestId.half_le_radAt_of_max`).
16. **Average `O(log n)`: different proof.** The paper uses the recurrence
    `a(p) = max_{1≤k≤⌈p/2⌉} {k + a(k−1) + a(p−k)}` for the worst-case total radius on a segment, and cites
    OEIS A000788 for `a(p) = Θ(p ln p)`. Neither the recurrence's correctness nor the asymptotics are
    proved there. We do not formalize them. We only define `a` (`LargestId.segA`) and check
    `a(0..15)` against A000788 (`segA_eq_A000788`). Instead, we prove directly that two nodes of
    radius `≥ d` are at cyclic distance `≥ d`, hence `∑_v r(v) ≤ ∑_{d=1}^n n/d ≤ n (⌊log₂ n⌋ + 1)`
    (`LargestId.sum_radAt_straightforward_le`). This gives the paper's conclusion: the average radius is
    `O(log n)`.
17. The paper's "the radius needed by these other vertices is the minimum distance to a vertex
    with larger ID or an endpoint" is used only implicitly: our radius is the actual stopping radius
    of the formal algorithm.
