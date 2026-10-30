# Differences between the formalization and the paper

King, Kutten, Thorup. *Construction and impromptu repair of an MST in a distributed network with
o(m) communication.* PODC 2015 (arXiv 1502.03320v1). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Errors and gaps in the paper

1. **`HP-TestOut` with the paper's edge numbers is blind** (Section 2.2; algorithm claim "w.h.p.
   `HP-TestOut(x)` outputs 1 if `T_x` has a leaving edge"). The *edge number* is defined for an
   undirected edge `{u, v}` (concatenation of the IDs, *smallest first*), but `𝒫(D)(z) =
   ∏_{e∈D}(z − edge_number(e))` is applied to the sets `E↑(T)`, `E↓(T)` of *ordered* pairs. With
   the literal definition, `(u, v)` and `(v, u)` get the same number and `𝒫(E↑(T)) = 𝒫(E↓(T))`
   identically (even node by node: `Local↑(y) = Local↓(y)`), so `HP-TestOut` always returns 0.
   Lean: `fp_Eup_eq_fp_Edown_of_symm`, `hpTestOut_symm_never`, `hpTestOut_edgeNumber_never`.
   Fix: number a dart `(u, v)` by the ordered concatenation `ID(u)·ID(v)` (`dartNumber`), and take
   `p` larger than the largest *dart* number. Rule R3 (⚠️): the intent is evident from
   Observation 1, which is about ordered pairs; the fix is local to one definition.
   With the fix everything works: `hpTestOut_dartNumber_error_lt`.

2. **`FindMin`'s initial range misses `maxWt`** (Section 3.1, step 3 `k ← maxWt(T_x)`;
   Lemma 2). Step 5 tests `[j_i, k_i]` with `j_i = j + i⌈(k−j)/w⌉`, `k_i = j + (i+1)⌈(k−j)/w⌉ − 1`;
   their union is `[j, j + w⌈(k−j)/w⌉ − 1]`, which is `[j, k − 1]` when `w | k − j` (and empty
   when `k = j`). Step 7(a)'s update `k = k_min + 1` shows the range is meant half-open, `[j, k)`,
   so the initialisation should be `k ← maxWt + 1`. As written, if the lightest leaving edge is
   the heaviest edge at `T_x` and `w | maxWt − 1`, no subrange ever contains it, `TestOut` (one-sided)
   never answers 1 and `FindMin` returns `∅` although an edge leaves `T_x`, contradicting Lemma 2.
   Example: the path `0 − 1 − 2` with weights `1, 3`, `T = {0}` (a singleton fragment in the first
   phase of `Build MST`): `maxWt(T) = 1`, all subranges are empty. Lean: `run_none_of_max`,
   `findMin_paper_misses`, `p3_counterexample`; corrected version `findMinFixed_correct`.
   Rule R3 (⚠️): off-by-one, intent recoverable from step 7(a).

3. **`FindAny`'s hash range `r > ∑ deg` is too small for Lemma 4** (Section 4.1, step 3a; Lemma 5).
   Lemma 4 assumes `0 < |W| < 2^(ℓ−1) = r/2` and its witness `j = ℓ − ⌈lg|W|⌉ − 1` can be `0`,
   while step 3a only asks `r > ∑_{y∈T} deg y ≥ |W|` and step 3b uses the indices
   `i = 1, …, lg r`. The proof of Lemma 5 applies Lemma 4 without checking its hypothesis. This
   makes Lemma 5 **false as stated** for some pairwise independent families: for the star
   `K_{1,3}`, `T = {center}` (`∑ deg = 3`, so `r = 4`, indices `{1, 2}`), the three leaving edges
   have edge numbers `10, 11, 12`; the family `hfam` (high bits of the three hash values
   `s₁, s₂, ¬(s₁⊕s₂)`, low bits and all other keys independent uniform) is pairwise independent on
   all of `[0, 12] ⊇ [1, maxEdgeNum(T)]`, but for **every** seed the number of leaving edges hashing
   into `[2]` is 0 or 2, so `min = 2`, `w(T) = 10 ⊕ 11 ⊕ 12 = 13` is the number of no edge, and the
   round fails. `FindAny-C` succeeds with probability `0 < 1/16`, and `FindAny` never finds an edge.
   Lean: `FindAnyCex.lemma5_findAnyC_false`, `FindAnyCex.findAny_eq_none`,
   `FindAnyCex.hfam_pairwiseIndep` (via the general `IsPairwiseIndep.extend`).
   Fix: `r ≥ 4 ∑ deg` (then `j ≥ 1`) or `r > 2 ∑ deg` with the index `0` added; with it Lemma 5
   holds (`lemma5_findAnyC`, `lemma5_findAny`, `lemma5_findAny_whp`).
   Rule: borderline ❌/⚠️, recorded as ⚠️ by R3 — the intended requirement is stated in the paper's
   own Lemma 4 (`|W| < 2^(ℓ−1)`), the fix is a local parameter change (constant factor in `r`, no
   effect on the complexity) and the claim itself is unchanged; moreover the failing family is
   artificial (for the linear family `x ↦ Ax` over `GF(2)` the three numbers are linearly independent,
   their hash values independent, and the round succeeds with probability `≥ 3/8` on this instance).

4. **Lemma 5's proof gives `1/16 − 1/(2n^c)`, the statement claims `1/16`** for `FindAny-C`.
   The statement is nevertheless true (with item 3's fix): the chain of inequalities in Lemma 4
   actually yields `> 1/8` (the paper writes `= 1/16` at the end; `(1/4)·(1/2) = 1/8`), and the
   exact bound `|W| p (1 − (|W|−1) p)` with `p ∈ (1/(4|W|), 1/(2|W|)]` is `≥ 3/16`
   (`lemma4_strong`); then `(1 − 1/2)·3/16 ≥ 1/16` as soon as `p ≥ 2 ∑ deg` (`lemma5_findAnyC`).
   Proof repair (🛠️).

5. **`B` in inequality (2).** Section 2.2 calls `B` "the number of edges incident to nodes in `T`",
   but step 0 computes it "by summing up the degrees of nodes in `T`". Only the latter works: the
   fingerprints agree at the number of every dart with both endpoints in `T`, so at least
   `2·#(edges inside T)` values of `α` are bad (`card_inter_le_card_hpTestOut_fail`), and with
   `B = #incident edges` the bound `Pr < ε` for `p > B/ε` fails when `T` has many inside edges.
   With `D = ∑ deg` we prove `Pr ≤ (D−1)/p < ε` (`hpTestOut_fail_prob_le`, `hpTestOut_error_lt`).
   Typo with evident intent (step 0), R3. Also, (2) is stated unconditionally; it holds only when
   `E↑(T) ≠ E↓(T)`.

6. **`FindMin`'s step 6 is undefined when no subrange answers 1** (`min` of the empty set) and
   step 7 names `TestHigh` what step 6 calls `TestInterval`. We repeat the iteration in that case
   (`iter`). With exact `HP-TestOut`s and one-sided `TestOut`s, step 7(b) ("both return 0") is dead
   code, so `FindMin` returns `∅` only when `Count` runs out — and returns `∅` with no leaving edge
   (`run_none_of_empty`). Missing case in pseudocode, R3.

7. **Lemma 2, `FindMin-C` (not formalized, noted).** "The probability that the number of `TestOut`
   trials needed exceeds the expected number by a factor of `2c/q + 1` is less than 1/3 for `c ≥ 1`,
   by Markov's inequality": the budget is `K′ = (2c/q)L` failures plus `L = lg maxWt/lg(w−1)`
   successes, i.e. `(2c/q + 1)L` trials, which is only `2c + q` times the *expected* number `L/q`
   of trials; so Markov gives `1/(2c + q) ≈ 0.47` for `c = 1`, `q = 1/8`, not `< 1/3` (that
   needs `c ≥ 1.44`). This is a claim inside a proof (R1), so it does not affect the verdict. The bound is
   still true by concentration of sums of geometric variables. Also "worst case `O(log n)` time and
   messages" should be `O(|T_x| log n)`.

8. **Lemma 3, phase count (not formalized, noted).** "Let `c′ = 8c/C`. Then `(16 + 24)(c/C) lg n`
   phases suffice": `16c/C + (2c′ + 8c)/C = 24c/C + 16c/C²`, which exceeds `40c/C` for `C < 1`
   (`C ≈ 2/3`); the slip treats `c′` as `8c`. Only constants change. Also "reduced by a fraction of
   `C/2` ... `lg n / lg(C/2)` phases" (the log is negative; the count of fragments drops by a factor
   `1 − C/4`).

9. **Section 3.2 `Insert(u, v)` (not formalized, noted).** Only the case `v ∈ T_u` is described;
   if `u` and `v` are in different trees, `{u, v}` must be added to the forest. Typo: `Delete` marks
   "`{u′, v}`" for `{u′, v′}`.

10. **Section 4.2 (not formalized, noted).** "it is possible that k distinct edges are picked and (at
    most one) cycle is formed": one cycle per merged component (each fragment picks one edge, so
    every component of the fragment graph has exactly one cycle, possibly of length 2).

11. **Thorup's odd hash for `w = 1` (degenerate).** With `a` odd in `[1, 2]`, `t ∈ [1, 2]` and keys
    `{1, 2}`, both keys are always sampled (`thorup_not_odd_one`). Irrelevant for `w = Θ(log n)`;
    the `1/8` bound of [33] is checked exhaustively for `w = 2, 3` (`thorup_odd_two`,
    `thorup_odd_three`) and by a Python script for `w = 4` (min probability `7/32`).

Pure typos: Lemma 4 writes `|X|` and `W \ {x}` for `|W|` and `W \ {w}`; Lemma 5 "If there is an
edge no leaving"; step 5 of `FindAny` says `TestOut`/`TestOut-C` for `FindAny`/`FindAny-C`;
`O(log n/ log n log n)` in Lemma 2's proof.

## Modelling choices

- **Abstraction level.** No message-passing execution model is formalized. Each procedure is
  modelled by the values its broadcast-and-echo computes: `TestOut`/`h_i(T)`/`w(T)` as sums over
  the nodes of `T` of the local values (`testOut`, `hT`, `wT`), `HP-TestOut` as the product of the
  local fingerprints (`fp_Eup_eq_prod_local`). Message/time complexities (Lemma 1, Theorems 1.1,
  1.2, Lemmas 2, 3, 6) are not formalized.
- **Randomness.** Finite uniform sample spaces (`Cslib.Probability.uprob`): the point `α ∈ ℤ_p`,
  a seed `ω ∈ Ω` of the hash family, independent repetitions as `Fin K → Ω`, independence of `α`
  and `ω` as a product space. An `ε`-odd or pairwise independent hash function is an arbitrary
  finite family with the stated property (stated by counting seeds), as in the paper.
- **Edge numbers** are an arbitrary type `U` with an injective encoding `enc : U → N` into a group of
  characteristic 2 (XOR of bit vectors); the hash function is evaluated on numbers (`hv : U → ℕ`).
  Distinctness of edge numbers (`Set.InjOn`) is assumed where the paper's concatenation guarantees it.
- **`FindMin`** is modelled on the set `L` of weights of leaving edges (weights distinct). `TestOut`
  answers are an adversarial function, constrained only to be one-sided (`AllOneSided`); the
  `HP-TestOut`s are exact (the w.h.p. event). The probability that `TestOut` succeeds often enough
  (Chernoff/Markov) is not formalized; we prove the deterministic search correctness
  (`run_sound`, `run_of_inv`, `findMinFixed_correct`).
- **`FindAny`.** Steps 3–5 for one hash function are `step`; `findAnyC` and `findAny` add
  `HP-TestOut` and `K` repetitions. We prove the paper's statements with `r = 2^ℓ ≥ 4 ∑ deg` and
  the paper's indices `{1, …, ℓ}` (`step_success_prob_paperIdx`), and also with `2|W| < 2^ℓ` and
  indices `⊇ {0, …, ℓ−1}` (`step_success_prob`). `HP-TestOut`'s error parameter is used through
  `p ≥ 2 ∑ deg` (`lemma5_findAnyC`) or `p > D/ε` (`lemma5_findAny_whp`).
- **Lemma 4** is proved with the paper's `j = ℓ − ⌈lg |W|⌉ − 1` and the stronger constant `3/16`
  (`lemma4_strong`), and the paper's `1/16` form (`lemma4`).
- **Thorup's hash** (`thorupHash`) is defined but its `1/8`-oddness (cited from [33]) is not proved
  in general; `TestOut`'s guarantee is stated for any `ε`-odd family (`testOut_prob`).
- **Appendix B**: the cycle-breaking facts (probability `1/2^(k−1)` that no edge is unmarked, at most
  half of the edges unmarked) are formalized for a cycle `Fin k` (`CycleBreak.lean`); the rest of the
  analysis of `Build ST` is not.

## Not formalized

Lemma 1 and all message/time bounds; the Chernoff/Markov parts of Lemmas 2, 3, 5, 6; `Build MST`,
`Build ST`; the MST/ST repair correctness of Section 3.2 (classical cut/cycle properties); Appendix A
(superpolynomial weights); the general `1/8`-oddness of Thorup's hash.
