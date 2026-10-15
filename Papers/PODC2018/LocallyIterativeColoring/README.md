# Locally-Iterative Distributed (Δ+1)-Coloring below the Szegedy–Vishwanathan Barrier

Leonid Barenboim, Michael Elkin, Uri Goldenberg. *Locally-Iterative Distributed (Δ+1)-Coloring below
Szegedy–Vishwanathan Barrier, and Applications to Self-Stabilization and to Restricted-Bandwidth
Models.* PODC 2018, pp. 437–446. DOI [10.1145/3212734.3212769](https://doi.org/10.1145/3212734.3212769),
arXiv [1712.00285](https://arxiv.org/abs/1712.00285). The version used here is arXiv v2 (Aug 2021),
which is the local PDF. It is cited as [BEG18].

## Status

**Done: Section 3 (all of it), the Section 4.1 colour-reduction step, and two counterexamples. No
`sorry` or `axiom`.** `lean_verify` on the main theorems shows only `propext`, `Classical.choice` and
`Quot.sound`. Linial's `O(Δ²)`-colouring, which the paper only cites, is also formalized, so
Corollary 3.6 is proved end to end.

The main result is correct. Two statements in the paper are **false**, and both have Lean
counterexamples:

1. **Section 1.2.** The paper claims that with `p = Δ + 1` prime, `2p + 1` rounds of AG turn a
   `(Δ+1)²`-colouring into a `(Δ+1)`-colouring. This fails on a 16-vertex tree with `Δ = 4`: after 11
   rounds a vertex is still working and 6 colours are in use (`intro_claim_false`). The correct bound
   for any prime `q > Δ` is `(Δ + 1)·q` rounds (`ag_final_of_lt`). Section 3 itself correctly
   assumes `q > 2Δ`.
2. **Section 7, Algorithm 3AG.** 3AG never terminates on `K₂` started from `⟨1,0,0⟩, ⟨1,0,1⟩`
   (`threeAG_never_finalizes`). This refutes Corollaries 7.2 and 7.3 for every `p`.

There are also a number of minor slips. See `differencies.md`.

Not formalized:
* Section 4: the self-stabilization model with faults, Excl-/Mod-Linial, MIS and MM.
* Section 5 (edge colouring) and Section 6 (arbdefective colouring).
* All bit and message complexity claims. They are only noted in docstrings.

Rough token spend: about 0.55M tokens in total (paper agent about 0.3M, plus 2 subagents with about
0.11M and 0.13M).

## Model

* **Graph.** `G : SimpleGraph V` with `[G.LocallyFinite]`. It may be infinite. The bound on the
  maximum degree is the hypothesis `∀ v, G.degree v ≤ Δ`, so `Δ` is an upper bound.
* **Synchronous, deterministic, fault-free LOCAL rounds, in locally-iterative form.** We use
  `Cslib.LocallyIterative.Algorithm C` from `Cslib/Computability/Distributed/Local/LocallyIterative.lean`. In round `t` every vertex
  computes its new colour as `step t (own colour) (SET of neighbours' colours)`.
  * Since only the set of neighbour colours is used, everything also holds in the SET-LOCAL model.
  * The round number is global knowledge. This is used only to switch between phases (`seq`).
  * The AG step, the halving step, Refine-AG and the uniform step of Section 4.1 do not depend on
    the round number.
* **Colourings.** A colouring is a function `V → C`. `IsProper G c` means adjacent vertices get
  different colours.
  * "`k`-colouring" means colours in `ℕ` that are `< k`, or pairs or triples over `ZMod q`.
  * `enc`/`dec` implement the paper's encoding `i ↦ ⟨⌊i/q⌋, i mod q⟩`.
* **Initial colouring of Corollary 3.6.** Any proper colouring with colours `< n`, for example
  distinct identifiers.

## Theorem ↔ Lean map

Files are in this folder. The infrastructure is in `Cslib/Computability/Distributed/Local/`.

| Paper | Lean |
|---|---|
| Locally-iterative algorithm (Sec. 1.1) | `Cslib.LocallyIterative.Algorithm`, `Algorithm.run`, `nbrColors`, `IsProper`, `Algorithm.seq`, `Algorithm.comap` |
| Algorithm 1 (AG), Def. 3.1 (conflict) | `BEG18.agStep`, `BEG18.ag`, `BEG18.Conflict` (`AG.lean`) |
| Footnote p. 6 (final colours are fixed) | `ag_run_succ_of_final`, `ag_run_of_final` |
| **Lemma 3.2** | `ag_isProper` (over any additive commutative group); one step: `isProper_agStep`, `agStep_ne` |
| **Lemmas 3.3, 3.4** | `IsAGRun.card_conflicts_le`: at most `m + 1` conflicts with one neighbour in `m q` rounds. Uses `card_filter_mul_eq_le` ("`d + x c ≡ b` has one solution") |
| **Corollary 3.5** | `ag_final_of_two_mul_lt` (`2Δ < q` ⇒ all final after `q` rounds); generalized form `ag_final` (`Δ(m+1) < m q` ⇒ final after `m q` rounds); ℕ-colours: `agNat_isProper`, `agNat_lt` (`Main.lean`) |
| Choice of `q` (Bertrand) | `agPrime`, `two_mul_lt_agPrime`, `lt_agPrime_sq`, `agPrime_le` |
| Standard colour reduction (cited) | `Cslib.LocallyIterative.colorReduction`, `colorReduction_isProper`, `colorReduction_le` (`Cslib/Computability/Distributed/Local/ColorReduction.lean`) |
| Linial's `O(Δ²)`-colouring (cited, [36]) | `Cslib.LocallyIterative.linial`, `linial_isProper`, `linial_lt` (`< max(16Δ², 256)` colours after `log* n + 3` rounds), `Nat.logStar` (`Cslib/Computability/Distributed/Local/Linial.lean`) |
| **Corollary 3.6** | from a `k`-colouring: `begColoring`, `begColoring_isProper`, `begColoring_le` (`≤ 4 max(2Δ+1, ⌊√k⌋+1)` rounds); end to end: `corollary_3_6` / `fullColoring_le`, `fullColoring_isProper` (`≤ log* n + 16Δ + 71` rounds, `Corollary36.lean`) |
| Algorithm 2, **Lemma 3.7** | `BEG18.Halving.algorithm`, `Halving.isProper_run` (`Halving.lean`) |
| **Lemma 3.8** | `Halving.run_final`, `Halving.halvingNat_run` |
| **Corollary 3.9** (2nd assertion) | `Halving.iterHalving_run`, `oneBitColoring_run`, `agPrime_linial_le` (`OneBit.lean`) |
| Algorithm 3 (Refine-AG) | `BEG18.RefineAG.algorithm`, `RefineAG.step`, `RefineAG.Free` (`RefineAG.lean`) |
| **Lemma 3.10** | `RefineAG.isProper_run` (with the invariant `Inv`: `a ≠ 0 → c = 0`) |
| **Lemma 3.11** | `RefineAG.lemma_3_11` |
| **Lemma 3.12 / Corollary 3.13** | `RefineAG.run_final`, `corollary_3_13` (sharper: `q ≥ 2Δ + k`, `⌊2Δ/k⌋ + 1` rounds); `corollary_3_13_paper` (the paper's constants) |
| Sec. 4.1, `(Δ+1)`-colouring paragraph before Thm 4.4 | `BEG18.uniform` (round-independent AG + local-maximum recolouring), `uniform_isProper`, `isAGRun_uniform`, `uniform_le` (`2q - (Δ+1)` rounds, `Uniform.lean`) |
| Sec. 1.2 claim (`p = Δ+1`, `2p+1` rounds) | **false**: `IntroCounterexample.intro_claim_false`; corrected bound: `ag_final_of_lt` |
| Sec. 7, Algorithm 7 (3AG), Cor. 7.2/7.3 | **false**: `threeAG_never_finalizes` (`Counterexamples.lean`) |
| Sec. 7, `(1+ε)Δ` phase argument for 2-D AG | covered by `ag_final` with `m = 1 + ⌈1/ε⌉` |

## CSLib candidates

Migrated to CSLib (from `Podc/Local/`):
* `Cslib/Computability/Distributed/Local/LocallyIterative.lean`: the synchronous locally-iterative (SET-LOCAL) round model, with
  phases (`seq`), simulation through encodings (`comap`) and properness.
* `Cslib/Computability/Distributed/Local/ColorReduction.lean`: the standard colour reduction and `firstFree`.
* `Cslib/Computability/Distributed/Local/Linial.lean`: Linial's colour reduction (polynomial version) and `Nat.logStar` /
  `Nat.tower`. `Nat.logStar` is a Mathlib candidate.

Still candidates:
* `AG.lean`: `card_filter_natCast_eq_le` (a residue class mod `q` within an interval) is a Mathlib
  candidate. The AG algorithm and the `IsAGRun` abstraction could go to CSLib together with the
  round model.
