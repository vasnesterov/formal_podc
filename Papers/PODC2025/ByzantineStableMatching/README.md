# Byzantine Stable Matching — PODC 2025

Andrei Constantinescu, Marc Dufay, Diana Ghinea, Roger Wattenhofer. *Byzantine Stable Matching.* PODC 2025. DOI
[10.1145/3732772.3733525](https://doi.org/10.1145/3732772.3733525). Formalized version: arXiv
[2502.05889](https://arxiv.org/abs/2502.05889) v2 (full version with appendix; numbering follows it).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The solvability characterizations (Theorems 2–7) are proved for every
`k ≥ 2`, in both directions. For `k = 1` all their "only if" directions are false. The proof of Theorem 2's
necessity does not cover `k = 2`, the reduction in Lemma 13 is invalid, and one case of Theorem 7 cites an
inapplicable theorem; all statements still hold for `k ≥ 2`.

## Mistakes in the paper

1. **`k = 1` breaks every "only if" direction (Theorems 2, 3, 4, 6, 7; false in a degenerate case).** The paper
   never assumes `k ≥ 2`. With one party per side, bSM is solvable with no communication on every network and
   against every adversary: each party outputs the only party on the other side. So, for example, Theorem 2's
   claim that `k = 1`, `tL = tR = 1` is unsolvable (since `1 ≥ k/3`) is false (`theorem2_only_if_false_k1`,
   `bSM_solvable_k1`, `bSM_solvableAuth_k1`). (Theorems 6 and 7 are worded as "if" only, but the introduction and
   §5.2 claim and argue necessity too; Lemma 13 and Corollary 5 fail for `k = 1` in the same way.)
2. **Lemma 13's reduction is invalid (proof error; statement true for `k ≥ 2`).** The proof uses Corollary 2 and Lemma 3 to
   obtain an sSM protocol on 6 nodes with `tR = 3`, `tL = 1`. Lemma 3 with `d = 3` only yields
   `⌊tR/⌈k/3⌉⌋ = ⌊k/⌈k/3⌉⌋` Byzantine right parties, which is less than 3 for `k = 4, 5, 7, 8, …` (for `k = 4`:
   `4/⌈4/3⌉ = 2`). It also needs `k ≥ 3`, and Corollary 2 (unauthenticated bipartite) is irrelevant here. We run
   the split-brain argument directly with groups, for every `k ≥ 2` (`lemma3_not_enough_for_lemma13`; fix
   `lemma13_sSM`).
3. **Theorem 2, necessity: `k = 2` not covered (proof gap; statement true).** The proof applies Lemma 3 with
   `d = 3`, which needs `k ≥ 3`. Our version of Lemma 5's 12-node cover argument works directly for every `k ≥ 2`;
   for `k = 2` the cover degenerates to an 8-node double cover of `K₄` (`lemma5`).
4. **Theorem 7, case `tR = k`, `tL < k/3`, cites the wrong result (proof gap; statement true).** It invokes
   Theorem 4, which needs `tR < k/2`. The protocol ΠbSM of Lemma 9 only uses `L–R` edges, so it also works on the
   one-sided network and settles the case.
5. **Typos / misreferences.**
   - Corollary 1 says "if `tL < k/2`"; it should be `tR < k/2`, since in a one-sided network `L` relays through
     `R`.
   - The proof of Theorem 4 cites "Corollary 2" (should be Corollary 1) and "one of the conditions `tL < k/3`,
     `tR < k/2`" (the second should be `tR < k/3`).
   - Lemma 5's proof: "c1 must decide to match party v2" should be `v1`.
   - The proof of Theorem 8 writes `n − 2tL` for `k − 2tL`.
   - The implicit requirement that BA/BB outputs are non-`⊥` on runs without omissions (Theorems 8/9) is
     needed and is made explicit.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (CSLib, `Cslib/Computability/Distributed/Byzantine/LockStep/`).
- `2k` parties `Fin k ⊕ Fin k` (`L`, `R`) run deterministic protocols in synchronous lock-step rounds over a fixed
  network (`fully`, `oneSided`, `bipartite`) with authenticated point-to-point channels. There is no randomness.
- Static Byzantine adversary with at most `tL` corruptions in `L` and `tR` in `R`. Byzantine messages are
  arbitrary functions of round, sender and receiver, which covers rushing. The paper claims adaptive security
  for its protocols; we prove only static security.
- Authenticated setting: ideal unforgeable signatures as abstract tokens, with a rushing, eavesdropping adversary
  (the strongest standard one, so the impossibilities hold a fortiori).
- A party's output is its first decision. bSM/sSM are specs on inputs, the honest set and honest decisions.
- Impossibilities are proved directly for all `k ≥ 2` by group-level FLM covers, for every network (Lemma 7/13:
  every network without `L–L` edges). This subsumes the paper's "small `n` + scaling" route.
- Shared library: lock-step helpers (`deliver_honest`, `firstSome_iff_of_ne`, `firstSome_map_iff`,
  `status_comapInput`) from `Cslib/Computability/Distributed/Byzantine/LockStep/Parallel.lean`; the `R`-parties' vote is `Finset.majority?`
  from `Cslib/Foundations/Data/Finset/Quorum.lean` (`PiBSM.majority_eq`: "a suggestion of more than half of `L`").
- Staged shared code: the generic group simulation of Lemma 3 (`GroupSim.*`,
  `Podc/Computability/Distributed/Byzantine/LockStep/GroupSim.lean`), double covers (`CoverSystem.doubleCover`,
  `…/LockStep/Cover.lean`) and labellings into `Fin m` (`Fintype.exists_fin_labelling_le`,
  `Podc/Foundations/Combinatorics/Labelling.lean`).
- Cited protocols are **hypotheses**: Fitzi–Maurer general-adversary BB (Theorem 10), Dolev–Strong, and
  Theorems 8/9 (BA/BB with omissions). Only the sufficiency directions use them.

**Main results in Lean** (namespace `Papers.PODC2025.ByzantineStableMatching`; each theorem is an `↔` for `k ≥ 2`).

| Paper | Lean | File |
|---|---|---|
| Theorems 2–7 | `theorem2`, `theorem3`, `theorem4`, `theorem5`, `theorem6`, `theorem7` | `Main.lean` |
| `k = 1` counterexample | `bSM_solvable_k1`, `theorem2_only_if_false_k1` | `Necessity.lean` |
| Lemmas 1, 2, 3 (BB ⇒ bSM, sSM ≤ bSM, scaling) | `lemma1`, `lemma2`, `lemma3` | `Lemma1.lean`, `Problem.lean`, `Scaling.lean` |
| Lemma 5 (12-node cover), Lemma 7 (8-cycle) | `lemma5`, `lemma7` | `Lemma5.lean`, `Lemma7.lean` |
| Lemma 9 (ΠbSM), Corollaries 1–4 | `lemma9`, `corollary1`, `corollary2`, `corollary34` | `Main.lean` |
| Lemma 13 (repaired), Corollary 5 | `lemma13_sSM`, `bSM_not_solvableAuth_R` | `Lemma13.lean`, `Necessity.lean` |

**Not formalized.** The cited protocols (Fitzi–Maurer, Dolev–Strong, Phase-King with omissions) are hypotheses
(`FitziMaurerBB`, `DolevStrongBB`, `OmissionBA`, `OmissionBB` in `Hypotheses.lean`). Adaptive adversaries are not
treated.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
necessity directions use no hypotheses. Gale–Shapley (Theorem 1) is a computable CSLib function with a stability
proof (`Cslib.StableMatching.galeShapley_isStable`).
