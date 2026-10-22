# Uncoordinated Beeps — PODC 2020

Fabien Dufoulon, Janna Burman, Joffroy Beauquier. *Can Uncoordinated Beeps tell Stories?* PODC 2020. DOI
[10.1145/3382734.3405699](https://doi.org/10.1145/3382734.3405699). Formalized version: the PODC proceedings
version (there is no arXiv version). The extended version [7], which contains the omitted proof of Theorem 1, was
not used. Numbering follows the proceedings.

**Verdict: ⚠️ Correct with fixes.** The coding-theory core of the paper (Section 3) holds. We prove that
Definitions 2 and 3 of uncoordinated superimposed (USI) codes are equivalent (Theorem 1). A USI(h,k)-code decodes
every uncoordinated transmission scenario with conflict at most k (Theorem 2). Sidon sets give USI(h,k)-codes of
length at most 8h²(k+1)² (Theorems 3, 5, 7, Lemma 6, Corollary 8). Lemma 4 is false as literally stated, because
it takes differences mod l. Its integer version is what the proofs use, and it holds. The remaining problems are
missing side conditions in degenerate cases. The beeping simulation of Sections 4–6 was not formalized.

## Mistakes in the paper

* **Lemma 4 is false as stated (harmless).** Lemma 4 says that in an (l,K) Sidon set every non-zero element of
  {0,…,l−1} is "a difference d₁ − d₂ mod l" of at most one pair. This fails even if a pair and its reverse count
  once. D = {0, 1, 3} is a (4, 3) Sidon set, yet 1 ≡ 1 − 0 ≡ 0 − 3 (mod 4) comes from the two different pairs
  {0,1} and {0,3} (`lemma_4_mod_false'`). The sets of the paper's own Theorem 3 fail too, for ordered pairs. For
  p = K = 3 the Erdős–Turán set is D = {0, 7, 13}, a (14, 3) Sidon set since 14 ≤ 2p². There 7 − 0 ≡ 0 − 7
  (mod 14) (`lemma_4_mod_false`). The proof ignores the "mod l" and proves the integer statement: non-zero
  integer differences are distinct (a Golomb ruler). That integer version is all Lemma 6 needs, and we proved it.
  (`lemma_4_mod_false'`, `lemma_4_mod_false`; repaired: `lemma_4`)
* **Definition 4 is ambiguous in a way that matters.** "All pairwise sums of elements in D are different" must
  include the sums d + d. Under the weaker reading, where only sums of two distinct elements count, D = {0,1,2} would
  be a Sidon set, but its codeword 111 overlaps its own shift by 1 in two positions. Then Lemma 4 and Lemma 6 fail.
  The Erdős–Turán sets satisfy the strong reading, so the results stand. (`lemma_6_needs_strong_sidon`)
* **Missing side conditions (degenerate cases).**
  - Lemma 6 needs t ≠ t'. The surrounding text says "two" shifted words, so this is clearly intended. (`lemma_6`)
  - Theorem 1 needs codeword length l ≥ 1. For l = 0 no shift is admissible, so Definition 2 holds vacuously while
    Definition 3 fails. (`theorem_1_length_zero`)
  - Theorems 5 and 7 need K ≥ 1. Otherwise "USI(1, K−1)" is meaningless.
  - Corollary 8 uses Theorem 3, which needs an *odd* prime in [K, 2K]. For K = h(k+1) = 1 none exists. This case is
    trivial (D = {0}).
  - Theorem 10's last step, f(Δ_up² + Δ_up + 2) ≤ f(Δ_up+1)², needs Δ_up ≥ 1 (arithmetic check only; Section 4
    is not formalized).
  - Footnote 4 ("σ̄(c,t₁) ≠ σ̄(c,t₂) iff t₁ ≠ t₂") fails for the all-zero codeword.
* **Suspected gap in Section 4 (not formalized, not checked in Lean).** This is a suspicion, not a confirmed
  error. Algorithm 3 tests history windows H[r−l−(i−1), r−1−(i−1)] that start before the node's wake-up (local
  index ≤ 0). The paper does not say what these bits are, and Lemma 11 is stated only for windows that start
  while the node is awake. Suppose the missing bits read as 0 and c₁[1] = 0, which Theorem 7 allows because it
  fixes no partition. Then a node u that wakes one round after a neighbour w started c₁ would "decode" that c₁
  and relay it. A neighbour v of u would then record a 2-hop beep of w in a round when the path v–u–w was not yet
  awake, which would contradict Definition 5 and Remark 2. Either fix would close the gap: choose c₁ to contain
  the position of the Sidon element 0, or decode only windows that lie inside the awake period.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Binary words of length n are `Fin n → Bool`, with 0-based positions (paper position i is our i−1). Shifted
  words σ(x,t), extended shifted words σ̄(x,t) of length 3l−2, and superpositions (bitwise OR over a `Finset`) are
  defined literally. A "set of codeword–shift pairs" is a `Finset (Word l × ℤ)`, compared as pairs.
* Theorem 2 uses an *uncoordinated transmission scenario* (`Scenario`). The model is the beeping model with
  uncoordinated starts on a static graph `G` with finitely many nodes, global rounds in `ℤ`, and a wake-up round
  `wake v` per node. Local round r_v ≥ 1 is global round `wake v + r_v − 1`. Each node starts a finite set of
  codeword transmissions (codeword, global start round), each at or after its wake-up. A node beeps in a round iff
  one of its transmissions has a 1 there, so concurrent schemes are OR-ed. H_v records whether v or a neighbour
  beeped. The conflict at (v, r) is the number of distinct (codeword, start) pairs started in N(v) within l−1
  rounds of r, as in the paper's proof. The theorem is quantified over all graphs, wake-up patterns and
  transmission sets. It does not need the hypothesis r_v ≥ 1.
* Sidon sets are `Finset ℕ` with the strong Sidon property (sums d + d included).

**Main results in Lean** (namespace `Podc.UncoordinatedBeeps`).

| Paper | Lean | File |
|---|---|---|
| Definition 2 / Definition 3 | `IsUSICode` (`IsUSI₂`) / `IsUSICode'` (`IsUSI₃`) | `USICode.lean` |
| Theorem 1 | `theorem_1` (+ `theorem_1_length_zero`) | `USICode.lean` |
| Theorem 2 | `Scenario.theorem_2` (Def. 2 codes), `Scenario.theorem_2'` (Def. 3 codes) | `Transmission.lean` |
| Definition 4 | `IsSidonSet` | `Construction.lean` |
| Theorem 3 (Erdős–Turán) | `theorem_3` (from `Cslib.SidonSet.erdosTuran_spec`) | `Construction.lean`, `Podc/Foundations/Combinatorics/SidonSet.lean` |
| Lemma 4 | `lemma_4` (integer differences); `lemma_4_mod_false'`, `lemma_4_mod_false` (stated version false) | `Construction.lean` |
| Lemma 6 | `lemma_6` (+ general `card_common_le_one`, `lemma_6_needs_strong_sidon`) | `Construction.lean` |
| Theorem 5 | `theorem_5` | `Construction.lean` |
| Theorem 7 | `theorem_7` (general form `isUSICode_of_sidon`: disjoint (k+1)-subsets of a Sidon set) | `Construction.lean` |
| Corollary 8 | `corollary_8` (length ≤ 8h²(k+1)²), `corollary_8_two` (≤ 32(k+1)²) | `Construction.lean` |

**Not formalized.** Section 4 (BEEP2H/LISTEN2H, Algorithms 1–3, Lemma 9, Theorem 10, Lemma 11, Theorem 12),
Section 5 (2-hop desynchronization, probabilistic) and Section 6 (local message broadcast).

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Corollary 8 shows that the code definitions are not vacuous: USI(h,k)-codes exist for all h and k. The Sidon-set
infrastructure is in `Podc/Foundations/Combinatorics/SidonSet.lean` (a CSLib candidate). It uses Mathlib's
Bertrand postulate `Nat.exists_prime_lt_and_le_two_mul`.
