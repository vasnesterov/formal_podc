# MST construction and impromptu repair with o(m) messages — PODC 2015

Valerie King, Shay Kutten, Mikkel Thorup. *Construction and impromptu repair of an MST in a distributed
network with o(m) communication.* PODC 2015. DOI
[10.1145/2767386.2767405](https://doi.org/10.1145/2767386.2767405). Formalized version: arXiv
[1502.03320](https://arxiv.org/abs/1502.03320) v1; numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** `HP-TestOut`, `FindMin` and `FindAny` are each wrong as printed and saved by a local
change proved in Lean, and the one step we did not repair, the Markov bound for `FindMin-C`, changes only a
constant. The combinatorial core is sound: the cut-parity identity behind `TestOut`, Observation 1, the fingerprint
test `HP-TestOut`, Lemma 4 (isolation by a pairwise independent hash), and the correctness of the `w`-ary search
`FindMin` and of `FindAny`/`FindAny-C` (Lemma 5). The paper's main point, the message bounds of `Build MST`,
`Build ST` and the repair, was not checked.

## Mistakes in the paper

### ❌ Lemma 2, proof (`FindMin-C`, Markov step)
The budget `(2c/q + 1)L` is only `2c + q` times the expected `L/q` trials, so Markov gives `1/(2c + q) ≈ 0.47` for
`c = 1`, `q = 1/8`, not "less than 1/3 for `c ≥ 1`" (that needs `c ≥ 1.44`).

**Impact.** This step of the proof is wrong and we did not repair it in Lean. The statement is still true, by
concentration of sums of geometric variables or a larger budget, and only the constant `C` of Lemma 3 depends on it.

### 🔧 `HP-TestOut` (Section 2.2, edge numbers)
`HP-TestOut` as written always answers "no leaving edge", because the edge number of the *undirected* edge
is used for the *ordered* pairs in `E↑(T)`, `E↓(T)`, so both fingerprints are equal for every `α`
(`hpTestOut_symm_never`, `hpTestOut_edgeNumber_never`).

**Impact.** Local fix with evident intent (Observation 1 makes it clear): number the dart `(u, v)` by the
ordered concatenation `ID(u)·ID(v)` and pick `p` above the largest dart number. With this fix we prove
inequality (2): error `≤ (D−1)/p < ε` with `D = ∑_{y∈T} deg y` (`hpTestOut_dartNumber_error_lt`).

**Details.** The polynomial `𝒫(D)(z) = ∏_{e∈D} (z − edge_number(e))` is applied to the sets of ordered
pairs, but the edge number concatenates the IDs smallest first. Then `(u, v)` and `(v, u)` get the same
number, already `Local↑(y) = Local↓(y)` at every node, and the two fingerprints are equal whatever `T` is.

### 🔧 `FindMin` (Section 3.1, Lemma 2: the heaviest weight is missed)
`FindMin` returns `∅` although an edge leaves `T_x` when the lightest leaving edge is also the heaviest edge
at `T_x` and `w | maxWt − 1`, e.g. on the path `0 − 1 − 2` with weights `1, 3` and `T = {0}`
(`run_none_of_max`, `p3_counterexample`).

**Impact.** Off-by-one with evident intent (step 7(a) treats the range as half-open): with
`k ← maxWt + 1` the search is correct (`findMinFixed_correct`).

**Details.** Step 3 sets `k ← maxWt(T_x)`. The `w` subranges of step 5 cover
`[j, j + w⌈(k−j)/w⌉ − 1]`, which is `[j, k−1]` when `w | k − j` (empty when `k = j`). Step 7(a) narrows to
`(j_min, k_min + 1)`, so the range is meant to be half-open. In the failing case `TestOut` (which never
answers 1 wrongly) never answers 1. In the example, a singleton fragment in `Build MST`'s first phase,
`maxWt(T) = 1` and every subrange is empty.

### 🔧 Lemma 5 (Section 4.1, `FindAny`'s hash range)
Lemma 5 is false for some pairwise independent hash families: on the star `K_{1,3}` with `T = {center}`,
`FindAny`'s range `r > ∑ deg` gives `r = 4`, too small for Lemma 4, and `FindAny-C` succeeds with probability
`0` instead of `≥ 1/16` (`FindAnyCex.lemma5_findAnyC_false`, `FindAnyCex.findAny_eq_none`).

**Impact.** Local parameter fix: with `r ≥ 4 ∑ deg`, or `r > 2 ∑ deg` plus index `0`, Lemma 5 holds
(`lemma5_findAnyC`, `lemma5_findAny_whp`). The failing family is artificial: the linear family over
`GF(2)` succeeds here.

**Details.** Lemma 4 assumes `|W| < 2^(ℓ−1) = r/2` for the set `W` of leaving edges, and its witness `j` can
be `0`. Step 3a only asks `r > ∑ deg`, and step 3b only uses the indices `1, …, lg r`. The proof of
Lemma 5 never checks Lemma 4's hypothesis. In the star example `∑ deg = 3`, so `r = 4` and the indices are
`{1, 2}`, and the edge numbers are `10, 11, 12`. We build a pairwise independent family on all keys
`[0, 12]`: the high bits of the three hash values are `s₁, s₂, ¬(s₁ ⊕ s₂)`, and everything else is
independent and uniform. With it, the number of leaving edges hashing into `[2]` is always 0 or 2. So
`min = 2`, `w(T) = 10 ⊕ 11 ⊕ 12 = 13` is not the number of any edge, and every round fails. `FindAny`
never finds an edge.

### ✏️ Slips
- Inequality (2) needs `B` = the *sum of the degrees* in `T`, as in step 0, not "the number of edges
  incident to `T`". The fingerprints agree at the number of every dart inside `T`
  (`card_inter_le_card_hpTestOut_fail`).
- Inequality (2) is stated unconditionally but holds only when `E↑(T) ≠ E↓(T)` (`hpTestOut_error_lt`).
- `FindMin`'s step 6 is undefined when no subrange answers 1. We repeat the iteration in that case.
- Lemma 2's "worst case `O(log n)` time and messages" should be `O(|T_x| log n)`.
- Lemma 3's phase count adds up to `24c/C + 16c/C²`, not `40c/C`. Only constants change. Not formalized.
- Claim 1 of Lemma 3: "`lg n / lg(C/2)`" has a negative logarithm, and the number of trees drops only by a factor
  `1 − C/4`. This is still `O(log n)` phases. Not formalized.
- `Insert` misses the case where `u` and `v` are in different trees (not formalized).
- Section 4.2's "(at most one) cycle": one cycle forms per merged component, possibly of length 2. Not formalized.
- The odd hash of [33] is not `1/8`-odd for `w = 1` (`thorup_not_odd_one`), a parameter the paper does not use.

### Typos
- Lemma 4's chain of inequalities ends with "`= 1/16`" but in fact gives `> 1/8`.
- `|X|`, `W \ {x}`, `TestHigh`, `{u′, v}`, "TestOut" in `FindAny`'s step 5, "an edge no leaving" in Lemma 5, and
  `O(log n/ log n log n)` in the proof of Lemma 2.

## Proof gaps (statements true)

### 🔧 Lemma 5, proof (the `1/16` bound)
The proof of Lemma 5 only derives `1/16 − 1/(2n^c)` for `FindAny-C`, not the stated `1/16`.

**Impact.** Statement true, read with the fix of `r` above: the exact bound in Lemma 4 is `≥ 3/16` (`lemma4_strong`),
and the stated `1/16` for `FindAny-C` follows from it (`lemma5_findAnyC`).

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
* The Chernoff/Markov parts of Lemmas 2, 3, 5 and 6.
* `Build MST` and `Build ST`, apart from the arithmetic points listed under Slips.
* The MST/ST repair correctness of Section 3.2.
* Appendix A.
* The general `1/8`-oddness of the hash of [33], for `w ≥ 4` (cited; `w = 2, 3` are proved in Lean).

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
