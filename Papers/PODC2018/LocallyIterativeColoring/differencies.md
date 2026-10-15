# Differences between the formalization and [BEG18] (arXiv 1712.00285v2)

## Errors in the paper (with Lean counterexamples)

1. **Section 1.2: the `2p + 1`-round claim is false.** The paper says: start from a proper
   `(Δ+1)²`-colouring with `Δ + 1 = p` prime, run AG over `GF(p)`, and "when all vertices run this
   simple iterative step for `2p + 1 = 2(Δ + 1) + 1` rounds, the ultimate coloring ψ is a proper
   `(Δ + 1)`-coloring".
   * **Counterexample** (`IntroCounterexample.intro_claim_false`, `Counterexamples.lean`): a tree on
     16 vertices with `Δ = 4` and `p = 5`. After `2p + 1 = 11` rounds vertex 0 still has colour
     `⟨1,1⟩` and 6 colours are in use. Vertex 0 finalizes only after 13 rounds.
   * **How it was found.** A dynamic program over rooted trees and per-vertex trajectories
     `⟨a, b + t·a⟩` / stopping times found the example; plain random search did not. On paths
     (`Δ = 2`, `p = 3`) the claim holds: at most 5 rounds are needed.
   * **Why the argument breaks.** With `q = Δ + 1`, a neighbour that finalizes during a window of `q`
     rounds can conflict twice in that window. So a window may have no free round.
   * **Correct statement** (`ag_final_of_lt`): for any prime `q > Δ`, all vertices are final after
     `(Δ + 1) q` rounds. The general form is `ag_final`: all final after `m q` rounds whenever
     `Δ (m + 1) < m q`.
   * Section 3 itself works with `q > 2Δ`, which is correct (`ag_final_of_two_mul_lt`).
2. **Section 7: Algorithm 7 (3AG) does not terminate**, so Corollaries 7.2 and 7.3 are false.
   * **Counterexample** (`threeAG_never_finalizes`): on `K₂` with the proper colouring `⟨1,0,0⟩`,
     `⟨1,0,1⟩`, both vertices always have equal `b`. So in every round they move to `⟨1, b+1, ·⟩` and
     `c` is never `0`. This holds for every `p ≥ 2`, including `p ≥ 3Δ + 1` and `p ≥ 2Δ + 2`.
   * **The flaw.** The termination argument ("each neighbour may have a conflicting `b_u` … at most
     three times") assumes that two neighbours in the same phase with the same `c` have different
     `b`. That is true in 2-D AG, where properness forces it. In 3-D, `⟨c, b⟩` may coincide and only
     `a` differs.
   * The phase-based alternative at the start of Section 7 (AG on sub-palettes, then AG again) is not
     affected. It is not formalized.

## Section 3.1 (AG): changes and minor issues

* **Choice of `q`.**
  * The paper picks a prime `√k ≤ q ≤ 2√k` but then uses `q > 2Δ` (Corollary 3.5). These conditions
    are compatible only when `k ≥ (2Δ+1)²`-ish.
  * We take `q = agPrime Δ k`, the least prime `> max(2Δ, ⌊√k⌋)`. Then `2Δ < q` and `k < q²`, and
    Bertrand gives `q ≤ 2·max(2Δ+1, ⌊√k⌋+1)` (`agPrime_le`).
  * `q = O(Δ)` holds when `k = O(Δ²)`. The statements keep the explicit bound instead of `O(·)`.
* **Number of rounds.** Algorithm 1 loops over `i = 0, …, q` (`q + 1` rounds). We prove that `q`
  rounds suffice.
* **Lemma 3.2.**
  * The proof's case "exactly one of them had a conflict ⇒ the first coordinates differ" overlooks
    the case where the conflicting vertex already has `a = 0`. The statement is still true: the other
    vertex had no conflict, so the second coordinates differ.
  * We prove the lemma over any additive commutative group (`ag_isProper`). Primality is not needed
    for properness, which is relevant for the `Z_{Δ+1}` remark in Section 1.2.
* **Lemmas 3.3 / 3.4.**
  * They are stated with `t ≤ q` rounds. We prove a single counting lemma for windows of `m q`
    rounds: at most `m + 1` conflicts with one neighbour (`IsAGRun.card_conflicts_le`). The paper's
    case is `m = 1`.
  * The proof splits at the first round in which the neighbour is final, and counts residue classes
    (`card_filter_mul_eq_le`).
* **Corollary 3.5.**
  * The proof's counting ("a node cannot conflict with each of its neighbors more than twice")
    really bounds the number of *conflict rounds per neighbour*. This is how we formalize it.
  * Only properness of the initial `GF(q)²`-colouring is needed. No bound like `k = Θ(Δ²)` is
    required beyond `k < q²`.
* **Abstraction.** The running-time proof only uses three properties of a run, bundled as `IsAGRun`
  (AG move while working, final stays final, a final vertex with a working neighbour keeps its
  colour). This lets the same proof cover the uniform algorithm of Section 4.1.
* **One-bit messages.** These are not modelled. The locally-iterative model sends whole colours.

## Corollary 3.6

* Linial's algorithm is not part of the paper. We formalized a polynomial version
  (`Cslib/Computability/Distributed/Local/Linial.lean`) with explicit constants: from a proper colouring with colours `< n`,
  after `log* n + 3` rounds the colours are `< max(16Δ², 256)`, and every round is proper.
  * `Nat.logStar` is defined as `0` for `n ≤ 1` and `logStar (log₂ n) + 1` otherwise.
  * Each round uses the least admissible field size `q` and polynomial degree `d`.
  * We assume `Δ ≥ 1`.
* The composite algorithm (`fullColoring n Δ`) uses the round number to switch phases: Linial, then
  AG, then the standard colour reduction. The paper's notion of locally-iterative (Szegedy–
  Vishwanathan) is informal about this. The uniform alternative is `uniform` (Section 4.1).
* The explicit bound is `log* n + 16Δ + 71` rounds (`fullRounds_le`), instead of `O(Δ) + log* n`.
* The standard colour reduction (cited from [6]) is formalized in `Cslib/Computability/Distributed/Local/ColorReduction.lean`:
  `m - (Δ + 1)` rounds, as stated in the paper.

## Section 3.2 (one-bit halving)

* Colours are `Bool × ZMod q`, where `true` stands for `a = 1`. `q` is any positive integer, matching
  the paper's "no prime needed".
* Lemma 3.7 needs neither `k ≥ 2Δ + 2` nor any assumption on `q`.
* Lemma 3.8 holds even from a non-proper initial colouring.
* The condition actually used is `Δ + 1 ≤ q` together with colours `< 2q`. The paper's
  `k ≥ 2Δ + 2, q = ⌈k/2⌉` is one way to get it. In particular, the last halving phase may use
  `q = Δ + 1` whenever `k ≤ 2Δ + 2`.
* Algorithm 2 loops over `i = 0, …, Δ + 1` (`Δ + 2` rounds), while Lemma 3.8 says `Δ + 1` rounds. We
  prove `Δ + 1`.
* **Corollary 3.9.**
  * The first assertion (bit complexity `O(Δ + log n)` including Linial's phase) is not formalized,
    since bits are not modelled.
  * The second assertion is `oneBitColoring_run`: AG followed by `s` halving phases, with
    `q ≤ 2^s (Δ+1)`. For Linial's palette, `s = 6` suffices (`agPrime_linial_le`).

## Section 3.3 (Refine-AG)

* Colours are a structure `⟨a, b, c⟩`, with `a, b ∈ ZMod q` and `c ∈ ℕ`. A finalizing vertex picks
  the least free index `j`. The paper allows any free index.
* **Slips.**
  * The conflict definition before Lemma 3.12 reads `⟨b_u + j·a_v, j⟩ = ⟨b_u, c_u⟩`. It should be
    `⟨b_v + j·a_v, j⟩`.
  * Index ranges are written `0 ≤ j ≤ k` where `j < k` is meant.
  * In the proof of Lemma 3.12, "`0 ≤ j, j′ ≤ q`" should be "`< k`".
  * The final-state case of that proof swaps the roles of `u` and `v`.
* **Gap in Corollary 3.13.** The proof needs "≥ `k` conflicting neighbours per non-final round". This
  requires that each neighbour blocks at most one index per round, which is Lemma 3.11 for working
  neighbours plus `j = c_u` for final ones. The paper does not say this. We count blocked
  `(round, index)` pairs instead.
* **Sharper constants.** The paper's window `⌊q/k⌋ − 1` is loose: `k·(rounds) ≤ q` suffices. We prove
  the result with `q ≥ 2Δ + k` and `⌊2Δ/k⌋ + 1` rounds (`run_final`, `corollary_3_13`). The paper's
  `q ≥ 2Δ + 3k` and `⌈2Δ/k⌉ + 1` rounds follow as `corollary_3_13_paper`.
* The bit-round implementation remark is not formalized.

## Section 4 (self-stabilization)

* We formalize only the round-independent `(Δ + 1)`-colouring step described before Theorem 4.4
  (`Uniform.lean`).
  * The step: AG for working vertices. In addition, a final `⟨0, b⟩` with `b > Δ` whose neighbours
    are all final with smaller `b` recolours to the least `b'` not used by a neighbour, so `b' ≤ Δ`.
  * Result: from a proper `GF(q)²`-colouring with `2Δ < q`, every round is proper, and after
    `2q - (Δ+1)` rounds all colours are `⟨0, b⟩` with `b ≤ Δ` (`uniform_le`).
  * The key observation, used in `isAGRun_uniform`: a final vertex with a working neighbour never
    recolours, so the AG analysis is unaffected. The paper does not spell this out.
* Not formalized:
  * The fault model (arbitrary RAM corruption, dynamic topology), Check-Error, Excl-Linial,
    Mod-Linial, and Lemmas 4.1–4.3.
  * Theorem 4.4 as stated (stabilization from arbitrary states).
  * MIS and MM (Theorems 4.5, 4.6).
  * Our `uniform_le` covers only the phase that starts once all colours are in the AG range `I₀` and
    form a proper colouring.

## Sections 5, 6, 7

* Section 5 (edge colouring in CONGEST and Bit-Round) is not formalized. Its AG part is AG on the
  line graph, so `ag_final` applies to `G.lineGraph`, whose maximum degree is `Δ_L ≤ 2Δ − 2`.
  * Section 5 only requires `q ≥ 2Δ − 1`, which gives `q > Δ_L`. Under that condition our bound
    (`ag_final_of_lt`) is `(Δ_L + 1) q = O(Δ²)` rounds.
  * The `O(Δ)` bound of Lemma 5.1 needs `q > 2Δ_L`, e.g. a prime `q > 4Δ − 4`. That is still `O(Δ)`,
    so the result is morally right, but the stated condition on `q` is too weak for the cited
    argument (Corollary 3.5). We did not search for a line-graph counterexample.
* Section 6 (arbdefective colouring) is not formalized.
* Section 7 is covered as follows:
  * The `(1+ε)Δ` phase argument for 2-D AG is covered by `ag_final` with `m = 1 + ⌈1/ε⌉`
    (`Δ(m+1) < m q ⇐ q ≥ (1+ε)Δ`). It is consistent with the paper.
  * 3AG is refuted (see above).
