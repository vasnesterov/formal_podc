# Locally-Iterative (Δ+1)-Coloring — PODC 2018

Leonid Barenboim, Michael Elkin, Uri Goldenberg. *Locally-Iterative Distributed (Δ+1)-Coloring below
Szegedy–Vishwanathan Barrier, and Applications to Self-Stabilization and to Restricted-Bandwidth Models.*
PODC 2018. DOI [10.1145/3212734.3212769](https://doi.org/10.1145/3212734.3212769). Formalized version:
arXiv [1712.00285](https://arxiv.org/abs/1712.00285) v2 (Aug 2021).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** The core of the paper, Section 3 (the additive-group algorithm AG, one-bit halving, Refine-AG,
and Corollary 3.6: a locally-iterative `(Δ+1)`-colouring in `O(Δ) + log* n` rounds), holds end to end after local
changes; the introduction's `2p + 1`-round bound for `p = Δ + 1` fails, and Section 3's `q > 2Δ` replaces it.
**Algorithm 3AG of Section 7 never terminates on `K₂`**, which refutes Corollaries 7.2 and 7.3, and no uniform
replacement is proved, but nothing else in the paper uses it. The applications to self-stabilization, edge colouring and
arbdefective colouring were not checked beyond the AG bounds they use.

## Mistakes in the paper

### ❌ Section 7, Algorithm 3AG (Corollaries 7.2 and 7.3)
Algorithm 3AG never terminates on `K₂` with the proper colouring `⟨1,0,0⟩`, `⟨1,0,1⟩`, for every `p ≥ 2`, so Corollaries 7.2 and 7.3 are false (`threeAG_never_finalizes`).

**Impact.** Refutes the 3-D variant of Section 7, including `p ≥ 3Δ + 1` and `p ≥ 2Δ + 2`, and we proved no uniform
replacement. The phase-based alternative at the start of Section 7, which 3AG was meant to avoid, is not affected, and
neither is the core of the paper (Section 3); nothing else in the paper uses 3AG.

**Details.** The two vertices always have the same `b`. So in every round both conflict, both move
to `⟨1, b+1, ·⟩`, and `c` never becomes `0`. The termination argument says "each neighbour may have a
conflicting `b_u` at most three times". It assumes that two neighbours in the same phase with the
same `c` have different `b`. That is forced by properness in 2-D AG, but in 3-D, `⟨c, b⟩` can
coincide while only `a` differs.

### 🔧 Section 1.2 (`2p + 1` rounds of AG for `p = Δ + 1`)
The introduction's claim that `2p + 1` rounds of AG over `GF(p)`, with `p = Δ + 1` prime, turn a proper `(Δ+1)²`-colouring into a proper `(Δ+1)`-colouring is false on a 16-vertex tree with `Δ = 4`, `p = 5` (`intro_claim_false`).

**Impact.** A claim of the introduction, not used later: Section 3 itself correctly assumes `q > 2Δ` and still gets
`O(Δ)` rounds (`ag_final_of_two_mul_lt`, `corollary_3_6`). A correct bound with `q = Δ + 1` is `(Δ + 1)·q` rounds
(`ag_final_of_lt`).

**Details.** After 11 rounds vertex 0 still has colour `⟨1,1⟩`, 6 colours are in use, and vertex 0
finalizes only after 13 rounds. (On paths, `Δ = 2`, the claim does hold.) The argument breaks
because with `q = Δ + 1`, a neighbour that finalizes inside a window of `q` rounds can conflict
twice in that window, so a window may have no free round.

**Repair.** Rewrite the paragraph with Section 3's prime `q > 2Δ`. For any prime `q > Δ`, everything is final after `(Δ + 1)·q` rounds (`ag_final_of_lt`).

### ✏️ Slips
- Section 3.1 picks a prime `√k ≤ q ≤ 2√k` but then uses `q > 2Δ`; we use the least prime above
  `max(2Δ, ⌊√k⌋)`.
- Refine-AG's conflict definition has `b_u` for `b_v`, and index ranges `j ≤ k` for `j < k`.
- The final-state case of Lemma 3.12 swaps `u` and `v`.

### Typos
- Algorithms 1 and 2 loop one round longer than needed.

## Proof gaps (statements true)

### 🔧 Section 5 (edge colouring: the condition on `q`)
Section 5 only requires `q ≥ 2Δ − 1`, i.e. `q > Δ_L` for the line graph, but the cited `O(Δ)` argument of Corollary 3.5 needs `q > 2Δ_L`, so the bound is unestablished (not refuted).

**Impact.** Under the stated condition our bound is `O(Δ²)`. We did not look for a counterexample.

**Details.** Edge colouring runs AG on the line graph, whose degree is `Δ_L ≤ 2Δ − 2`.

**Repair.** A prime `q > 4Δ − 4` is still `O(Δ)` and satisfies the printed lower bound; the bound is then our general
theorem applied to `G.lineGraph` (`ag_final_of_two_mul_lt`). Section 5 itself is not formalized, so this covers its AG
part, the only part affected.

### 🔧 Lemma 3.2 (properness of AG)
The proof overlooks the case where the conflicting vertex already has `a = 0`.

**Impact.** The statement stands: then the second coordinates differ (`ag_isProper`).

### 🔧 Corollary 3.13 (Refine-AG running time)
The proof needs "each neighbour blocks at most one index per round", but never says so.

**Impact.** The statement stands (`corollary_3_13`, `corollary_3_13_paper`).

**Details.** It follows from Lemma 3.11 for working neighbours and from `j = c_u` for final ones. We
count blocked (round, index) pairs instead.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A simple graph, possibly infinite but locally finite. `Δ` is any upper bound on degrees.
* Synchronous, deterministic, fault-free rounds in *locally-iterative* form: each vertex's new colour
  is `step t (own colour) (set of neighbours' colours)`. This is CSLib's `LocallyIterative` model.
  Only the *set* of neighbour colours is used, so the results also hold in SET-LOCAL.
* The round number is global knowledge, used only to switch phases in the composite algorithm. The
  individual steps (AG, halving, Refine-AG, the Section 4.1 step) are round-independent.
* Corollary 3.6 starts from any proper colouring with colours `< n` (e.g. IDs). Linial's
  `O(Δ²)`-colouring, which the paper only cites, is formalized too, so Corollary 3.6 is end to end;
  the output is a `fullRounds n Δ`-local function of the initial colours (`fullColoring_isLocal`).
* Message/bit sizes are not modelled.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.2 (AG proper; any additive group) | `ag_isProper` | `AG.lean` |
| Lemmas 3.3, 3.4 (conflict counting) | `IsAGRun.card_conflicts_le` | `AG.lean` |
| Corollary 3.5 (`2Δ < q` ⇒ final after `q` rounds); general form | `ag_final_of_two_mul_lt`, `ag_final` | `AG.lean` |
| Corollary 3.6 (end to end, `≤ log* n + 16Δ + 71` rounds) | `corollary_3_6`, `fullColoring_le` | `Corollary36.lean` |
| Lemmas 3.7, 3.8, Corollary 3.9 (one-bit halving) | `Halving.isProper_run`, `Halving.run_final`, `oneBitColoring_run` | `Halving.lean`, `OneBit.lean` |
| Lemmas 3.10–3.12, Corollary 3.13 (Refine-AG) | `RefineAG.isProper_run`, `RefineAG.lemma_3_11`, `RefineAG.run_final`, `corollary_3_13`, `corollary_3_13_paper` | `RefineAG.lean` |
| Section 4.1, round-independent `(Δ+1)`-colouring | `uniform_isProper`, `uniform_le` | `Uniform.lean` |
| Section 1.2 claim: false; corrected bound | `intro_claim_false`; `ag_final_of_lt` | `Counterexamples.lean`, `AG.lean` |
| Section 7, 3AG: does not terminate | `threeAG_never_finalizes` | `Counterexamples.lean` |

`corollary_3_13` is sharper than the paper: `q ≥ 2Δ + k` and `⌊2Δ/k⌋ + 1` rounds. The paper's
constants follow as `corollary_3_13_paper`. Section 7's `(1+ε)Δ` phase argument for 2-D AG is the
case `m = 1 + ⌈1/ε⌉` of `ag_final`.

The paper does not check that the extra recolouring rule of Section 4.1 leaves the AG analysis intact. It does
(`uniform_isProper`, `uniform_le`): the rule's guard (all neighbours final) means a final vertex with a working neighbour
never recolours.

**Not formalized.**
* Section 4: the self-stabilization fault model, Excl-/Mod-Linial, Theorem 4.4 as stated, MIS and MM.
* Section 5 (edge colouring) and Section 6 (arbdefective colouring).
* The phase-based algorithm at the start of Section 7.
* All bit and message complexity claims.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Both counterexamples are concrete executions checked in Lean. The round model, the
standard colour reduction and Linial's algorithm (`linial_lt`: `< max(16Δ², 256)` colours after
`log* n + 3` rounds) are in CSLib `Cslib/Computability/Distributed/Local/`; locality of runs and the
"final colours stay final" lemma come from `Cslib/Computability/Distributed/Local/OnlineLocalLocality.lean` and `Cslib/Foundations/Data/Nat/TimeRec.lean`
(`Nat.eq_of_le_of_stable`).
