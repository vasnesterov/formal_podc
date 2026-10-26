# Differences between the formalization and the paper

Paper: S. Brandt, *An Automatic Speedup Theorem for Distributed Problems*, PODC 2019; arXiv 1902.09958v1
(the version formalized; numbering as there).

## Errors in the paper

1. **Theorem 1, (2) ⇒ (1), is false as stated (false statement of a headline claim; verdict 🚨).** The proof lets the two endpoints `u, v`
   of an edge `e` pick a pair `(o, o')` from their `Π_1`-outputs with `{o, o'} ∈ g_{1/2}(Δ)` "by looking only at
   `N^t(e)`", `v` keeping `o` and `u` keeping `o'`. If `N^t(e)` looks the same from both endpoints (same port
   number of `e` at both ends, same radius-`(t-1)` views), both endpoints make the same choice. Counterexample
   (`theorem_1_backward_false`, `Counterexample.lean`): `Π` = edge orientation (`g = {{0,1}}`, all node
   configurations allowed). The constant `Π_1`-output `{{0},{1}}` solves `Π_1` in 0 rounds on every graph, but
   on the class `{K_2}` (no inputs; `n = 2`, `Δ = 1`, simple, connected, girth `∞`; `t`-independent for every
   `t`) `Π` is not solvable at all. The same holds for every class consisting of one `d`-regular graph whose
   port numbering is a proper edge colouring (`theorem_1_backward_false_of_symmetric`), e.g. high-girth
   bipartite `d`-regular graphs. This is not a degenerate case. The paper itself says that input-free
   classes of high-girth graphs are `t`-independent, so the natural class of input-free `Δ`-regular
   high-girth graphs with arbitrary port numbers is a counterexample. Consequently Corollary 1 is false as stated, and so are the claims in the
   abstract and in §1.1 that the speedup is "reversible" / that `Π_1` "can be solved one round faster but not
   any faster" without symmetry breaking on edges.
   The same goes for the "exact complexities `T − 1, T − 2, …`" of §1.1/§2.1. The lower bounds (§4.4,
   Theorem 4) use only the correct direction (1) ⇒ (2).
   **Fix:** add edge symmetry breaking at radius `t` (`EdgeAsym`: for each edge the endpoints have different
   radius-`(t-1)` views or the edge has different port numbers at its ends). Then (2) ⇒ (1) holds, with no
   independence hypothesis (`theorem_1_backward`). All applications in the paper have such symmetry breaking
   (edge orientations in §4.4, Theorem 2, Lemmas 3–4, Theorem 4; IDs forming a colouring in §4.5; unique IDs in
   Theorem 3), so they are unaffected. The paper itself notes the need for edge symmetry breaking only for the
   maximality simplification (§4.2), not for Theorem 1.

## Modelling choices and imprecisions

2. **Neighbourhoods = information (definition).** The paper defines `N^t(v)` as "the collection of information
   that `v` can obtain in `t` rounds, i.e. the topology of the ball together with the inputs", which agree only
   when the ball is a tree (girth). We use the information itself: the full-information state (`ViewT`,
   `LGraph.view`): own input labels, and per port the neighbour's radius-`(t-1)` view and the remote port
   number. `N^t(e)` (`eview`) is the pair of radius-`(t-1)` views of the endpoints plus both port numbers.
   A `t`-round algorithm is a CSLib port-numbering algorithm run for `t` rounds (`SolvableIn`), proved
   equivalent to a function of radius-`t` views (`solvableIn_iff_view`).
3. **Girth is not needed** for Theorems 1 and 2 with this definition: the proofs use only `t`-independence.
   We therefore state them without the girth hypothesis (stronger). Girth matters for making
   `t`-independence true for natural classes and for identifying views with balls; neither is formalized.
4. **`t`-independence** (`IsIndependent`, clauses `IndepClause1/2`) is the paper's definition verbatim with
   the views above; extensions `Ext` are represented by the full node/edge views they extend to (equivalent,
   since the views being extended are fixed).
5. **Class of graphs.** `𝒢_{n,Δ}` is any set of input-labelled port-numbered graphs on `Fin n` with all
   degrees `≤ Δ` (hypothesis `hΔ`); simplicity/connectivity are not required (the theorems hold for any class).
   Problems are given for all `Δ` but only `f Δ, g Δ, h Δ` at the class's `Δ` matter. Algorithms may depend on
   `n`, `Δ`, `t` (they are fixed), as in the paper.
6. **Problem well-formedness** (`f Δ` finite, `g Δ` 2-element multisets over `f Δ`, `h Δ` multisets of
   `≤ Δ` elements over `f Δ`) is `Problem.WF`, preserved by the operators; the theorems do not need it.
   Maximal supersets in §4.2 are obtained by Zorn's lemma, so finiteness is not needed there either.
7. **Edge constraints are checked from both sides** (for each node and port), which is equivalent for
   symmetric multisets.
8. **Nonempty label type** (`[Nonempty L]`) is assumed in the backward direction (a total function into an
   empty label type cannot exist; degenerate).
9. **Theorem 2** is proved under the paper's hypothesis (input orientation, `theorem_2`) and more generally
   under `EdgeAsym` (`theorem_2_of_edgeAsym`). The paper's remark that with node colourings/IDs the
   simplification fails for "1-round ⇒ 0-round" is overly cautious in our model: radius-1 edge views contain
   both endpoints' inputs, so `EdgeAsym` holds at `t = 1` already.
10. **§4.2, compression.** The paper drops unusable labels from `Π'_{1/2}` before deriving `Π'_1` ("assume `O`
    and `f(Δ)` contain only outputs that can occur in a correct solution"). We never compress: `speedupMax` is
    the uncompressed problem. For lower bounds we instead map solutions of the uncompressed problems to the
    compressed descriptions (e.g. `speedupMax_sinkless_relax`, the trit description in §5).
11. **§4.4 (sinkless colouring).** We prove the direction of "`Π'_1 = Π`" needed for lower bounds
    (`speedupMax_sinkless_relax`: every `Π'_1` solution on `Δ`-regular graphs maps to a sinkless colouring) and
    the exact maximal configurations of `Π'_{1/2}` (`sinkless_edgeAllMax`). The paper's listing of `g_{1/2}`
    omits the configurations containing `∅` (harmless). The `Ω(log n)` conclusion needs the existence of
    `t`-independent high-girth classes with `t = Ω(log n)` ([Bollobás]); we prove the conditional statement
    `sinklessColoring_lower_bound` / `sinklessOrientation_lower_bound` with `t`-independence for all
    `t' ≤ t` and a richness hypothesis on the class (`SinklessRich`) as assumptions.
12. **§4.5 (colour reduction)** is verified for rings (`Δ = 2`; the second property fails for `Δ ≥ 3`, as the
    paper's restriction to rings suggests) and all even `k = 2m+2`, with `k' = 2^{|Reps m|}` and
    `2·|Reps m| = C(k, k/2)` (`two_mul_card_reps`). The `O(log* n)` consequence is not formalized.
13. **Theorem 3 (order-invariant algorithms, unique IDs) is not formalized.** Imprecision noticed: the proof
    re-assigns IDs in `N^t(e)` so that "any two differ by at least `2Δ^t + 1`"; for an arbitrary finite
    `S ⊆ ℕ_+` this should be a gap of `2Δ^t` elements *of `S`* (ranks, not values), with room also below the
    smallest and above the largest ID (under-specified; easily fixed, and for `S = {1, …, N}` as used in
    Theorem 4 it is fine).
14. **§4.6 (weak 2-colouring)**: the trit description of `Π'_{1/2}` is formalized in the generality of §5
    (superweak `k`-colouring, `TritEquiv.lean`). The claim "`h_1(Δ)` contains only 9 elements (or fewer if `Δ`
    is very small)" is stated without proof in the paper; we checked it by exhaustive enumeration in C
    (`modelcheck/weak2_h1.c`, trit alphabet `{01,02,10,11,12,20,21}`): for `Δ = 3, 4, 5` exactly 9 maximal
    families with nonempty sets (plus one degenerate family containing `∅`, which never occurs in a solution);
    `Δ = 2`: 8. Not a Lean proof.
15. **§5.1, `g'_{1/2}` listing** (under-specified): the listed per-colour cases omit the swapped case
    `Y^c = {(c,⊸)}`, `Z^c = {(c,→),(c,⊸),(c,•)}`; the trit description (tritwise sum `22…2`) is correct.
    We use only one direction of the "equivalent description" (maximal `Π'_{1/2}` solutions map to trit
    solutions: `ViewSystem.solvesE_toTrit`), which is what the lower bound needs; `Π'_1` is then taken in its
    trit description `tritOne k`, derived from the trit `Π'_{1/2}` (`tritHalf k`), as the paper does.
16. **Lemma 4 / Theorem 4 are proved in the port-numbering model with input orientations, without IDs**
    (`lemma_4`, `theorem_4`). The paper's LOCAL version goes through Theorem 3 (not formalized),
    Naor–Stockmeyer's order-invariance theorem [24, Thm 3.3] and the existence of high-girth regular graphs
    [Bollobás]; these are external. Hypotheses of `theorem_4` that the paper obtains from its choice of class
    (all `Δ`-regular `n`-node graphs of girth `≥ 2(T+1)+2` with arbitrary orientations, `n` large):
    `t`-independence for all `1 ≤ t ≤ T+1`, and richness (`RichFor`: for an input list `ι` with `≥ (Δ−1)/2`
    ports of each orientation, every port `p` of a node with inputs `ι` can be joined to every port `q` of
    opposite orientation of another node with inputs `ι`). Odd `Δ` is not needed for the lower bound.
    The paper's pigeonhole over IDs is not needed (0-round outputs depend only on the inputs).
17. **Theorem 4 constants** (typo): the proof fixes `T(Δ) ≤ (log*Δ − 7)/5` and later uses `(log*Δ − 8)/5`;
    `5T + 7 ≤ log*Δ` (with CSLib's `Nat.logStar`) suffices (`theorem_4`); `theorem_4_paper` is the
    `(log*Δ − 8)/5` form. The paper's `k_{i+1} = F^5(k_i)` is replaced by `kSeq i = tower(5i+1)` with
    monotonicity of superweak colouring in `k` (`SolvableIn.superweak_mono`).
18. **Weak 2-colouring ⇒ pointer version** (`solvableIn_weakPtr`) needs `Δ`-regularity and `Δ ≥ 1` (implicit in
    the paper). Weak 2-colouring itself is modelled as node outputs in `Bool` (not a `Problem`, since it is not
    edge-checkable).
19. **Lemma 1 cardinality.** The paper's `h_1(Δ)` consists of multisets of exactly `Δ` sets (regular graphs);
    our `nodeStepMax` follows §3 and also admits fewer elements, so `lemma_1` assumes `Multiset.card Q = Δ`
    (without it, `{∅}` is a vacuous counterexample: `lemma_1_needs_card`). Node configurations of solutions on
    `Δ`-regular graphs always have `Δ` elements, so Lemmas 2–4 are unaffected.
20. **Proof variations (statements as in the paper).** Lemma 1 is proved by a simpler exchange argument (if two
    distinct sets occur more than `(k+1)·3^k` times, enlarging one copy to their union keeps Property A, contradicting
    maximality) instead of the global `Q'` construction. Lemma 2 uses Hall only for one-sided sets plus a
    Mendelsohn–Dulmage-type pairing lemma (`exists_pairing_cover`, proved by induction instead of the path/ring
    decomposition); the `J'_in/J'_out` split is unnecessary. Lemma 3 uses a cruder colour count
    `2^(3^k)·(2^(4^k)+1)^(3·2^(3^k)) ≤ 2^(2^(5^k))` instead of `(3·2^(3^k))^(2^(4^k)+1)`.
