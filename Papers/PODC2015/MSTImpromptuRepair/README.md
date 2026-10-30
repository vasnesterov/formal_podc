# MST construction and impromptu repair with o(m) messages — PODC 2015

Valerie King, Shay Kutten, Mikkel Thorup. *Construction and impromptu repair of an MST in a distributed
network with o(m) communication.* PODC 2015. DOI
[10.1145/2767386.2767405](https://doi.org/10.1145/2767386.2767405). Formalized version: arXiv
[1502.03320](https://arxiv.org/abs/1502.03320) v1; numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The combinatorial core is sound: the cut-parity identity
behind `TestOut`, Observation 1, the fingerprint test `HP-TestOut`, Lemma 4 (isolation by a
pairwise independent hash), and the correctness of the `w`-ary search `FindMin` and of
`FindAny`/`FindAny-C` (Lemma 5). Three procedures are wrong as written, each fixed by a local change:
`HP-TestOut` uses unordered edge numbers and can never detect a leaving edge, `FindMin`'s first range
misses its top weight, and `FindAny`'s hash range `r > ∑ deg` is too small for Lemma 4, which makes
Lemma 5 false for some pairwise independent hash families.

## Mistakes in the paper

* **`HP-TestOut` as written always answers "no leaving edge" (Section 2.2).** The polynomial
  `𝒫(D)(z) = ∏_{e∈D} (z − edge_number(e))` is applied to the sets `E↑(T)`, `E↓(T)` of *ordered* pairs,
  but the edge number is defined for the *undirected* edge (IDs concatenated, smallest first). Then
  `(u, v)` and `(v, u)` get the same number, already `Local↑(y) = Local↓(y)` at every node, and the two
  fingerprints are equal for every `α`, whatever `T` is. The fix is to number the dart `(u, v)` by the
  ordered concatenation `ID(u)·ID(v)` and to pick `p` above the largest dart number. Observation 1
  makes the intent clear. With this fix we prove inequality (2): error `≤ (D−1)/p < ε` with
  `D = ∑_{y∈T} deg y` (`hpTestOut_symm_never`, `hpTestOut_edgeNumber_never`; fixed:
  `hpTestOut_dartNumber_error_lt`).
* **`FindMin` misses the heaviest weight (Section 3.1, Lemma 2).** Step 3 sets `k ← maxWt(T_x)`. The
  `w` subranges of step 5 cover `[j, j + w⌈(k−j)/w⌉ − 1]`, which is `[j, k−1]` when `w | k − j`
  (empty when `k = j`). Step 7(a) narrows to `(j_min, k_min + 1)`, so the range is meant to be
  half-open. If the lightest leaving edge is also the heaviest edge at `T_x` and `w | maxWt − 1`,
  `TestOut` (which never answers 1 wrongly) never answers 1, and `FindMin` returns `∅` even though an
  edge leaves `T_x`. Example: path `0 − 1 − 2` with weights `1, 3` and `T = {0}`, a singleton
  fragment in `Build MST`'s first phase. Then `maxWt(T) = 1` and every subrange is empty. With
  `k ← maxWt + 1` the search is correct (`run_none_of_max`, `p3_counterexample`; fixed:
  `findMinFixed_correct`).
* **Lemma 5 needs a larger hash range than `FindAny` uses (Section 4.1).** Lemma 4 assumes
  `|W| < 2^(ℓ−1) = r/2` for the set `W` of leaving edges, and its witness `j` can be `0`. Step 3a only
  asks `r > ∑ deg`, and step 3b only uses the indices `1, …, lg r`. The proof of Lemma 5 never checks
  Lemma 4's hypothesis, and the statement fails. Take the star `K_{1,3}` with `T = {center}`: then
  `∑ deg = 3`, so `r = 4` and the indices are `{1, 2}`, and the edge numbers are `10, 11, 12`. We
  build a pairwise independent family on all keys `[0, 12]`: the high bits of the three hash values
  are `s₁, s₂, ¬(s₁ ⊕ s₂)`, and everything else is independent and uniform. With it, the number of
  leaving edges hashing into `[2]` is always 0 or 2. So `min = 2`, `w(T) = 10 ⊕ 11 ⊕ 12 = 13` is not
  the number of any edge, and every round fails. `FindAny-C` succeeds with probability `0` (not
  `≥ 1/16`), and `FindAny` never finds an edge. The family is artificial: the linear family over
  `GF(2)` succeeds here. The fix is `r ≥ 4 ∑ deg`, or `r > 2 ∑ deg` plus index `0`; with it,
  Lemma 5 holds (`FindAnyCex.lemma5_findAnyC_false`, `FindAnyCex.findAny_eq_none`; fixed:
  `lemma5_findAnyC`, `lemma5_findAny_whp`).
* **Proof slips with true statements.**
  * Lemma 4's chain of inequalities ends with "`= 1/16`" but in fact gives `> 1/8`. The exact
    bound is `≥ 3/16` (`lemma4_strong`).
  * The proof of Lemma 5 only derives `1/16 − 1/(2n^c)` for `FindAny-C`, but the stated `1/16`
    holds by the `3/16` bound.
  * Inequality (2) needs `B` = the *sum of the degrees* in `T`, as in step 0, not "the number of
    edges incident to `T`". The fingerprints agree at the number of every dart inside `T`
    (`card_inter_le_card_hpTestOut_fail`).
* **Not formalized, noted in [differencies.md](differencies.md).**
  * Lemma 2's Markov step gives `≈ 0.47`, not `< 1/3`, for `c = 1`.
  * Lemma 3's phase count adds up to `24c/C + 16c/C²`, not `40c/C`.
  * `Insert` misses the case where `u` and `v` are in different trees.
  * `FindMin`'s step 6 is undefined when no subrange answers 1.
  * Typos: `|X|`, `TestHigh`, `{u′, v}`, and "TestOut" in `FindAny`'s step 5.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **No execution model.** Each broadcast-and-echo is represented by the value it aggregates: sums
  over the nodes of `T` of local parities, local XORs or local fingerprint products. Message, time
  and memory bounds are out of scope. The paper's own model is synchronous CONGEST for construction
  and asynchronous for repair; KT1, distinct IDs, `n` known.
* **Graph.** A finite `SimpleGraph` and a vertex set `T` (the marked tree `T_x`). `cut G T` is the set
  of edges with exactly one endpoint in `T`. Edge weights are distinct, and `FindMin` works on the
  set of leaving weights.
* **Randomness.** Finite uniform sample spaces (`Cslib.Probability.uprob`). The point `α ∈ ℤ_p` of
  `HP-TestOut`, the seed of an arbitrary `ε`-odd or pairwise independent hash family, independent
  repetitions as `Fin K → Ω`, and independence of `α` and the hash as a product space.
* **Adversarial parts.** `FindMin`'s `TestOut` answers are an arbitrary function, assumed only to be
  one-sided. Its `HP-TestOut`s are exact, which is the w.h.p. event. Probabilities of `TestOut`
  successes (Chernoff/Markov) are not formalized.
* **Edge numbers.** These are abstract keys with an injective encoding into a characteristic-2
  group (XOR of bit vectors). The counterexamples use the paper's concrete concatenation numbers.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| `TestOut` identity `∑_{v∈T}∑_{e∈E(v)} h(e) = ∑_{e∈Cut} h(e)` (mod 2), interval version | `sum_incidence_eq_sum_cut`, `sum_incidence_filter_eq_sum_cut` | `Cut.lean` |
| `TestOut` correct if 1, succeeds w.p. `≥ ε` for `ε`-odd `h` | `exists_cut_of_testOut_eq_one`, `testOut_prob` | `TestOut.lean` |
| `h(x) = [(ax mod 2^w) ≤ t]` is `1/8`-odd ([33]); checked for `w = 2, 3` | `thorup_odd_two`, `thorup_odd_three`, `thorup_not_odd_one` | `TestOut.lean` |
| Observation 1 | `exists_cut_iff_Eup_ne_Edown` | `Cut.lean` |
| `HP-TestOut`: aggregation, one-sided, inequality (2) | `fp_Eup_eq_prod_local`, `hpTestOut_false_of_no_cut`, `hpTestOut_fail_prob_le`, `hpTestOut_error_lt` | `HPTestOut.lean` |
| `HP-TestOut` with the paper's edge numbers never detects | `hpTestOut_symm_never`, `hpTestOut_edgeNumber_never` | `HPTestOut.lean`, `EdgeNumbers.lean` |
| `HP-TestOut` with ordered dart numbers | `hpTestOut_dartNumber_error_lt` | `EdgeNumbers.lean` |
| Lemma 2 (deterministic part): soundness, `∅` without leaving edge, search terminates | `run_sound`, `run_none_of_empty`, `iter_of_inv`, `run_of_inv`, `findMinFixed_correct` | `FindMin.lean` |
| Lemma 2 fails with `k ← maxWt` | `run_none_of_max`, `findMin_paper_misses`, `p3_counterexample` | `FindMin.lean` |
| Lemma 4 | `lemma4`, `lemma4_strong`, `card_isolated_ge` | `Isolation.lean` |
| Lemma 5, steps 3–4 ("Event A") and soundness | `step_eq_some_of_isolated`, `step_sound`, `findAnyC_sound`, `findAny_sound`, `findAnyC_findAny_none_of_no_cut` | `FindAny.lean` |
| Lemma 5 (with `r ≥ 4∑deg`) | `lemma5_findAnyC`, `lemma5_findAny`, `lemma5_findAny_whp` | `FindAny.lean` |
| Lemma 5 false with `r > ∑deg` | `FindAnyCex.lemma5_findAnyC_false`, `FindAnyCex.findAny_eq_none` | `FindAnyCounterexample.lean` |
| Appendix B: no edge unmarked w.p. `1/2^(k−1)`; at most half unmarked | `CycleBreak.uprob_no_unmarked`, `CycleBreak.two_mul_card_unmarked_le` | `CycleBreak.lean` |

**Not formalized.**
* Lemma 1 and all message, time and memory bounds (Theorems 1.1 and 1.2, Lemmas 3 and 6).
* The Chernoff/Markov parts of Lemma 2.
* `Build MST` and `Build ST`.
* The MST/ST repair correctness of Section 3.2.
* Appendix A.
* The general `1/8`-oddness of the hash of [33].

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`.
* The counterexample hash family is checked to be pairwise independent on all keys
  (`FindAnyCex.hfam_pairwiseIndep`), via the general extension lemma `IsPairwiseIndep.extend`.
* The hypotheses of `hpTestOut_error_lt` are shown satisfiable by the ordered dart numbers
  (`dartNumber_injective`).
* Probability uses CSLib `Cslib.Probability.Finite.Uniform`.
* CSLib candidates, marked in the files:
  * `uprob_prod_and` (`Prob.lean`);
  * `IsPairwiseIndep`, `card_isolated_ge`, `IsPairwiseIndep.extend` (`Isolation.lean`, `PairwiseExtend.lean`);
  * the cut identity and Observation 1 (`Cut.lean`);
  * `card_prod_sub_eq_le` (`HPTestOut.lean`).
