# Finding mobile data with searching costs — PODC 2010

Amotz Bar-Noy, Panagiotis Cheilaris, Yi Feng, Asaf Levin. *Finding mobile data under delay constraints with
searching costs.* PODC 2010. DOI [10.1145/1835698.1835774](https://doi.org/10.1145/1835698.1835774).
Formalized version: the PODC'10 paper (8 pages, author copy at corelab.ntua.gr/~philaris); no full
version exists, so the proofs omitted there (Lemmas 5, 6, Theorem 5) were supplied by us.

**Verdict: 🛠️ Hard fix.** The headline results hold. FRO is an `8/7`-approximation for two rounds
(Theorem 4), and a `(7-2√7)/(28-10√7) = (4+√7)/6 ≈ 1.108`-approximation for typical tokens (Theorem 5); both
bounds are tight. The paper's proof of both theorems does not work: its reduction to `N = 3, 4` boxes
(Lemma 4) has a false step, and the cases `N = 3, 4` (Lemmas 5, 6) are omitted. We proved both theorems for
every `N` with a new argument. Sections 2–4 (Propositions 1–3, Lemmas 1–3, Corollary 1) hold; the proof of
Lemma 1 misses a degenerate case (identical or zero-probability boxes).

## Mistakes in the paper

### ✏️ Slips
- Lemma 7 and "the ratio 8/7 is attainable" (Theorem 4): the tight instance has a tie `p₁/w₁ = p₂/w₂`. FRO
  reaches `8/7` only if it breaks the tie adversarially (box 1 before box 2); with the other order FRO is
  optimal on this instance, and then `8/7` is only a supremum. Section 5.2 states the adversarial convention
  for typical tokens; we use it throughout (`lemma7`, `theorem4_tight`, `lemma8`).
- Lemma 1, proof: from `j < i` it concludes the strict `p_i < p_j`, `w_i > w_j`, so the swap is strictly
  cheaper and *every* optimal strategy respects the order. Both fail in a degenerate case: the swap has equal
  cost exactly when `C_i, C_j` are identical boxes or both have probability 0 in a round of probability 0. The
  statement holds (`lemma1_isOptimal`): a weak exchange step (`cost_comp_swap_le`) and the potential
  `∑ k · A(k)` give a monotone strategy at least as cheap as any strategy (`exists_monotone_cost_le`). The
  proof also uses, without saying so, that a non-respecting partition into non-empty rounds has an inversion
  between adjacent rounds (true).

### Typos
- Section 4, before Lemma 3: "X = (1 + Y)/2" with X the load-balancing and Y the search objective; by
  Proposition 3 it is `Y = (1 + X)/2` (the proof of Lemma 3 uses the correct relation).
- Lemma 1, proof: "does not respect the non-decreasing order of the ratios" should be non-increasing.
- Lemma 3, proof: the load-balancing cost is "greater than 1/D and smaller than 1"; it is `≥ 1/D` and `≤ 1`,
  as written in the next sentence.

## Proof gaps (statements true)

### 🛠️ Theorems 4 and 5 (Lemma 4 reduction to `N = 3, 4`; Lemmas 5, 6 omitted)
The proof of Lemma 4 claims that FRO on the merged 4-box instance `I₄ = {C_A, C_B, C_C, C_D}` outputs
`⟨{C_A, C_B}, {C_C, C_D}⟩`, hence `cost(FRO₄) ≥ cost(FRO_N)`. This is false: with `p = (8,1,6,5,1)`,
`w = (1,1,7,6,4)` (strict ratio order), FRO costs `246` and OPT `243`, but on the merged instance FRO
costs `245` and OPT `243`, so the ratio drops from `246/243` to `245/243` (`lemma4_proof_step_fails`).

**Impact.** Statements true. We proved Theorem 4 (`theorem4`) and Theorem 5 (`theorem5`) for every `N`, so
Lemmas 5 and 6 follow (`lemma5`, `lemma6`), and Lemma 4's statement holds too (`lemma4`), because of Lemma 7.

**Details.** FRO on `I₄` minimises over all prefixes of the ratio order of `I₄`. Merged boxes keep FRO's split
`A ∪ B | C ∪ D` among these prefixes, so in fact `cost(FRO₄) ≤ cost(FRO_N)`, the wrong direction. The
other prefixes, such as `{C_A}` or `{C_A, C_B, C_C}`, are not prefixes of the original order and can be
cheaper. In the counterexample `FRO₄ = ⟨{C_A, C_B, C_C}, {C_D}⟩` with `A = {1}`, `B = {2}`, `C = {4}`,
`D = {3, 5}` (1-based). The proof of Theorem 5 is an outline that reuses Lemma 4 and leaves its own
`N = 3, 4` cases unproved. A merge-based reduction only works for runs of boxes that are consecutive in
the ratio order and on the same side of OPT, and that does not bound `N`.

**Repair.** A direct argument for every `N` (`bracket_gen`, `TwoRounds.lean`). For two rounds,
`cost(S) = P·W − p(S)·w(Sᶜ)`. Let `S` be any first round and `k` the largest index with
`w(C₁…C_k) ≤ w(S)`. Then the FRO candidates `{C₁…C_k}` and `{C₁…C_{k+1}}` already satisfy
`7 · min cost ≤ 8 · cost(S)`. The ratio order bounds `p(S)` by the line through the critical box
`C_{k+1}`. Integrality enters as a case split: either `C_{k+1} ∉ S` (so `p(S) ≤ P − p_{k+1}`) or
`C_{k+1} ∈ S` (so `w(S) ≥ w_{k+1}`). Rescaling then reduces everything to two polynomial inequalities in
three variables (`ineq_case1`, `ineq_case2`, `key_real`). For typical tokens the same bracketing gives
`(4+√7)/6` (`typ_real`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Centralized combinatorial optimization; no distributed model, no failures, no randomness beyond the
  known placement distribution. Boxes are `Fin N`, `p i ≥ 0` (not necessarily summing to 1), `w i ≥ 0`.
  A `D`-round strategy is a map `A : Fin N → Fin D`, box `i` unlocked in round `A i`. Empty rounds are
  allowed; this changes no optimum.
- `cost p w A = ∑ i, p i · ∑_{A j ≤ A i} w j` is the expected unlocking cost. Proposition 1 shows it equals
  both of the paper's formulas.
- FRO: the boxes are indexed in non-increasing order of `p i / w i` (`RatioSorted`, stated without
  division). `IsFRO` means minimum cost among monotone strategies, i.e. those respecting the order. Every
  theorem quantifies over all `RatioSorted` indexings, so it holds for every tie-breaking. For typical
  tokens (`p = w`) every order is a ratio order, matching the paper's adversary.
- Theorems 4 and 5 hold for every `N` (the paper says `N > 2`) and allow zero costs (the paper assumes
  positive costs; Lemma 8 uses its "0/0 = 1" convention, which we need not).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Proposition 1 | `prop1_eq1`, `prop1_eq2` | `Basic.lean` |
| Proposition 2 | `cost_smul`, `prop2_isOptimal`, `prop2_ratio` | `Basic.lean` |
| Lemma 1 | `lemma1_ratioSorted`, `lemma1_isOptimal` | `Optimal.lean` |
| Lemma 2 | `lemma2` (exact identity `cost_swap_rounds`) | `Optimal.lean` |
| Uniform probabilities, atypical token | `uniformProb_isOptimal`, `atypical_isOptimal` | `Optimal.lean` |
| Corollary 1 (`D = N`) | `corollary1`, `corollary1_isOptimal` | `Optimal.lean` |
| Proposition 3 | `prop3` | `Typical.lean` |
| Lemma 3 | `lemma3`, `lemma3_half`, `lemma3_lt_half`, `lemma3_tight` | `Typical.lean` |
| Theorem 4 (upper bound) | `theorem4` (via `bracket`, `key_real`) | `TwoRounds.lean`, `Ineq.lean` |
| Lemma 4 (statement) | `lemma4` | `Tight.lean` |
| Lemma 4 (proof step false) | `lemma4_proof_step_fails` | `Lemma4.lean` |
| Lemmas 5, 6 | `lemma5`, `lemma6` | `Tight.lean` |
| Lemma 7, Theorem 4 tightness | `lemma7`, `theorem4_tight` | `Tight.lean` |
| Theorem 5 (upper bound) | `theorem5` | `TwoRounds.lean` |
| Lemma 8 (tightness) | `lemma8` | `Tight.lean` |

**Not formalized.** Theorem 1 (the `Θ(ND)` dynamic program), Theorem 2 (strong NP-hardness), Theorem 3 and the
greedy bounds of Table 1 (quoted from the load-balancing literature), the PTAS of Section 5.3, and the
conjecture of Section 6.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The tightness lemmas (`lemma7`, `lemma8`, `lemma4_proof_step_fails`) are concrete instances, so the hypotheses
of Theorems 4 and 5 are satisfiable. Self-contained (Mathlib only); no CSLib model needed.
