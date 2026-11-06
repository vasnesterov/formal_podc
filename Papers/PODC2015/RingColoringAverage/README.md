# Average Complexity for the LOCAL Model — PODC 2015

Laurent Feuilloley. *Brief Announcement: Average Complexity for the LOCAL Model.* PODC 2015. DOI
[10.1145/2767386.2767446](https://doi.org/10.1145/2767386.2767446). Formalized version: arXiv
[1505.05072](https://arxiv.org/abs/1505.05072) v1 (same text as the brief announcement); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** Theorem 1 holds: for every 3-colouring algorithm on rings, the worst-case average radius
is `Ω(log* n)`, and we prove it with explicit constants. Its proof needs a new argument, because the "w.l.o.g. minimal
algorithm" step has no existence proof; we supply one with Zorn's lemma plus compactness, and the other repairs are
local. Section 2 (largest ID: linear worst case, logarithmic average) holds as well.

## Mistakes in the paper

### 🔧 Lemma 3 (reduction from 3- to 4-colouring)
Lemma 3 assumes `A` is minimal *for 3-colouring*, but Lemma 2, which it uses, is stated and proved only for
algorithms minimal *for 4-colouring*, and a 3-colouring algorithm that no 3-colouring algorithm improves can
still be improved by a 4-colouring algorithm.

**Impact.** Theorem 1 unaffected after repair (`lemma_3`, `theorem_1_four`, `theorem_1`). We do not know
whether Lemma 3 holds as stated.

**Details.** Lemma 2's modified algorithm `A'` uses all four colours. Lemma 3 says it "is sufficient to prove
the result for 4-colouring, as it implies the result for 3-colouring". For a 3-colouring algorithm improved
only by a 4-colouring algorithm, Lemma 2 says nothing.

**Repair.** Prove Theorem 1 for every 4-colouring algorithm: take a minimal 4-colouring algorithm below it,
and use Lemma 3 for minimal 4-colouring algorithms together with Linial's bound for 4 colours. A 3-colouring
algorithm is a 4-colouring algorithm with the same radii.

### 🔧 Section 3 (black-box corollary of Linial's bound)
The corollary uses the exact constant `½ log*(n/2)`, and the citation does not justify dropping the `−O(1)` term.

**Impact.** Only the constant changes, and the `Ω(log* n)` conclusion is untouched. We do not know whether the exact
constant fails.

**Repair.** We prove our own version, for 4 colours: `|S| > tower (2t+2)` implies a node of radius `> t`
(`Alg.exists_lt_radAt_four`). We use `R = ⌊(log*(n/2) − 1)/2⌋` in place of `½ log*(n/2)`.

### ✏️ Slips
- Lemma 2's proof ignores rings so small that the threshold views wrap around. We assume `n ≥ 2T + 1`, the
  only case used (`lemma_2`), and did not check the wrapped case. With this assumption Lemma 2 and the slicing
  construction are correct.

## Proof gaps (statements true)

### 🛠️ Theorem 1 ("without loss of generality … minimal algorithms")
The paper never shows that a minimal algorithm exists below a given one, and a chain of improvements need
not have a valid limit.

**Impact.** Statement true; we prove existence with Zorn's lemma plus compactness (`Alg.exists_isMinimal_le`).

**Details.** Minimal means that no valid algorithm uses at most the same radius everywhere and a strictly
smaller one somewhere. Algorithms have infinitely many neighbourhoods, so improvements can go on forever. The
limit of a chain of improvements has well-defined radii (pointwise minima), but its outputs need not
converge. So it is not clear that the limit is a valid algorithm.

**Repair.** Zorn's lemma on radius functions. For a chain, the limit algorithm stops at the pointwise minimum
radius. Its colour table exists by Tychonoff compactness: being proper on the finitely many nodes where a
given chain member attains the minimum is a closed condition, and these conditions are directed.

### 🔧 Theorem 1 (application of Lemma 3)
Lemma 3 is about the radius `r` that `v` actually uses, but Theorem 1 applies it with `r = ½ log*(n/2)` while the
centre's radius is only `≥ r`; with `r = r(v)` the ball of radius `r(v)/2` could leave the slice.

**Impact.** Statement true; the lemma's proof goes through unchanged.

**Repair.** We state Lemma 3 for `r ≤ r(v)` (`lemma_3`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`).
* Deterministic LOCAL on rings of `n ≥ 3` nodes with distinct natural identifiers. Nodes do **not** know `n`.
* A node gathers the ball of radius `r = 0, 1, 2, …` and at each radius decides from the IDs at offsets `[-r, r]`
  whether to stop and output. `r(v)` is the stopping radius.
* Rings are **oriented**: views are the ID sequences `j ↦ id(v + j)`. This only strengthens the lower bound, since
  an unoriented algorithm is an oriented one with the same radii.
* Validity: stop everywhere, and adjacent outputs differ. It is required on all rings with all identifier
  assignments, as the paper's construction implicitly needs.
* Complexity: the worst case over identifier assignments of the *average* radius `∑_v r(v) / n`. Theorem 1's
  ring uses the identifiers `{0, …, n−1}`.
* "Ω(r)" and "Ω(log* n)" are made explicit: average `≥ r/4`, and `n (log* n − 3) ≤ 32 ∑ r(v)`.

**Main results in Lean** (namespace `Podc.RingColoringAverage`).

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (3-colouring, average `Ω(log* n)`) | `theorem_1_average`, `theorem_1` (`n (log* n − 3) ≤ 32 ∑_v r(v)`), `theorem_1_three` | `Theorem1.lean` |
| Theorem 1 for 4-colouring (what the proof really shows) | `theorem_1_four` (`n ⌊(log*(n/2) − 1)/2⌋ ≤ 16 ∑_v r(v)`) | `Theorem1.lean` |
| Proof of Thm 1: slicing / permutation `π` | `exists_slices`, `sum_radAt_ge_of_isMinimal` | `Theorem1.lean` |
| "W.l.o.g. minimal" (missing) | `Alg.exists_isMinimal_le`, `exists_valid_le_of_isChain` | `Minimal.lean` |
| Lemma 2 | `lemma_2` (modified algorithm `Lemma2.alg`, validity `Lemma2.alg_valid`) | `Lemma2.lean` |
| Lemma 3 | `lemma_3` (average `≥ r/4`), `lemma_3_sum` | `Lemma3.lean` |
| Linial's bound (black box) | `Alg.exists_lt_radAt`, `Alg.exists_lt_radAt_four`, `Alg.exists_lt_radAt_three` | `Linial.lean` |
| Shift-graph colouring bound (Linial / Erdős–Hajnal) | `Cslib.ShiftGraph.card_le_iterate_of_proper` | `Podc/Foundations/Combinatorics/ShiftGraph.lean` |
| §2: largest ID needs radius `≥ n/2` at the maximum (linear worst case) | `LargestId.half_le_radAt_of_max`, `LargestId.worst_case` | `LargestId.lean` |
| §2: the straightforward algorithm is correct with total radius `O(n log n)` | `LargestId.straightforward_correct`, `LargestId.sum_radAt_straightforward_le` (`≤ n (⌊log₂ n⌋ + 1)`), `LargestId.average_radAt_straightforward_le` | `LargestId.lean` |
| §2: recurrence `a(p)` (values only) | `LargestId.segA`, `LargestId.segA_eq_A000788` | `LargestId.lean` |

**Not formalized.**
* §2 asserts without proof that the recurrence `a(p) = max_k {k + a(k−1) + a(p−k)}` is the worst-case total radius on
  a segment, and cites OEIS A000788 for `a(p) = Θ(p ln p)`. We did not try to verify the recurrence's derivation or
  the asymptotics; we only check the first 16 values against A000788. The conclusion is true: we prove directly, by a
  different argument and not through the recurrence, that the total radius is `≤ n (⌊log₂ n⌋ + 1)`, which is
  `O(n log n)`. Nothing points to an error.
* The cited `O(log* n)` upper bound (Cole–Vishkin without knowledge of `n`).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `exists_valid_three` (`NonVacuity.lean`) exhibits a valid 3-colouring algorithm (every node
waits until it has seen the whole ring and colours by its offset from the minimum identifier). So Theorem 1
quantifies over a non-empty class.
Linial's lower bound is proved from scratch: the shift-graph argument is staged as a CSLib candidate
(`Podc/Foundations/Combinatorics/ShiftGraph.lean`). It is the only shared code added. The model is new and
specific to this paper; it does not build on the CSLib LOCAL models, because they have no per-node radii.
