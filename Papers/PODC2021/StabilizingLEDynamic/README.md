# Stabilizing Leader Election with Weak Assumptions on Network Dynamics — PODC 2021

Karine Altisen, Stéphane Devismes, Anaïs Durand, Colette Johnen, Franck Petit. *On Implementing
Stabilizing Leader Election with Weak Assumptions on Network Dynamics.* PODC 2021. DOI
[10.1145/3465084.3467917](https://doi.org/10.1145/3465084.3467917). Formalized version: the full
journal version on HAL, [hal-03346225](https://hal.science/hal-03346225) (Research Square preprint,
2023), Theorems 1–7. The PODC numbering (Theorem 2.1, Lemma 3.2, Theorems 3.3–3.11, 4.1) is in the
docstrings.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All main results are proved:
* the class hierarchy (Theorem 1);
* all impossibility results (Theorems 2–5, Corollaries 1–3);
* the correctness of Algorithm `LE` (Corollary 6), with the speculative `6Δ + 2` bound of
  Theorem 7.

There are four caveats.
* The impossibilities need an identifier domain with more than `n` elements; the paper never says
  so.
* Lemma 7 is false as stated, though harmless.
* The proofs of Lemmas 12 and 16 have small gaps, which we fix.
* The proof of Theorem 1 does not work for two vertices.

## Mistakes in the paper

* **The impossibilities need more identifiers than processes (under-specified definition).**
  Every impossibility proof swaps a process for a fresh one, so it relies on fake identifiers.
  The paper only says `IDSET` is "an arbitrary totally ordered domain". If `|IDSET| = n`, every
  system is the whole of `IDSET`, and "`lid := min IDSET`" is self-stabilizing in every class.
  Then Theorems 2–5 all fail. We assume an infinite identifier domain. (`constAlg_selfStab`)
* **Lemma 7 is false as stated (harmless).** The lemma says that if `p` receives a record whose
  map contains `id ≠ id(p)`, then `id ∈ Gstable(p)` for the next `Δ` configurations. This fails
  when the record is `p`'s own relayed record, because line 12 skips records with `id = id(p)`.
  - Setup: 0-indexed rounds, `Δ = 2`, `V = {p, a, k}`, empty initial maps.
  - Edges: `k → p` in round 1, `p → a` in round 3, `a → p` in round 4.
  - In round 4, `p` receives its own record `⟨p, {p, k}, 1⟩` back, and it is skipped. The entry
    of `k` expired at configuration 4, so `k ∉ Gstable(p)` at configuration 5.

  Every use of the lemma has `id ≠ id(p)`. We add this hypothesis. (`lemma_7`)
* **Lemma 16: proof gap, statement true.** This has the same root cause as Lemma 7.
  - The proof takes the last round in which `q` received *any* record mentioning `id(p)`, and
    assumes that line 17 refreshed `Gstable(q)[id(p)]` in that round.
  - But line 12 skips `q`'s own relayed records.

  Restricting to records with `id ≠ id(q)` fixes this; Lemma 5's proof already does so.
  (`lemma_5`, `lemma_16`)
* **Lemma 12: proof gap, statement true.** In the third case the distance `d = d̂_i(r, q)`
  depends on `i`, yet the proof concludes "`∀ i ≥ t_p + d + 1`". Choosing the source round as
  (target − `Δ`) fixes it. (`lemma_12`)
* **Theorem 1: proof slip, statement true.** The proof works inside "a set `V` of `n > 1`
  vertices". With `n = 2` the per-`V` hierarchy collapses in two ways.
  - "Recurrent" equals "quasi-timely": the direct edge must appear infinitely often.
  - "Has a source" equals "has a sink": the out-star witness `G(1S)` has a sink.

  Classes range over all vertex sets, so Theorem 1 itself holds (`theorem_1_classes`). It
  follows from the per-`V` version for `n ≥ 3` (`theorem_1`). The `n = 2` facts are
  `theorem_1_false_card_two`, `J_src_eq_snk_of_card_two` and `not_theorem_1_card_two`.
* Small slips:
  * An intermediate claim of Lemma 8's proof is wrong: "no record tagged with a fake ID in any
    `msgs` after `Δ` rounds" fails at `γ_{Δ+1}`. An initial record can still be there with timer
    `0`, but it is never sent. Lemma 8 itself (for `i > 4Δ`) holds. (`lemma_8a_imprecise`,
    `fake_G`)
  * Lemma 10's proof considers rounds `i > 2Δ + 1` but concludes `t_r ≤ 2Δ + 1`. The argument
    does work from `2Δ + 1`. (`lemma_10`)

Theorem 4 needs `n ≥ 3`, as the paper says. For `n = 2`, LE is pseudo-stabilizing in
`J^B_{*,1}(Δ)` (`theorem_4_card_two`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Dynamic graphs.** `ι` is the identifier domain (processes = identifiers), infinite. A system
  is `V : Finset ι` with `|V| = n`. A dynamic graph is a sequence of loopless digraphs on `V`
  (`G t p q`: edge `p → q` in round `t`, 0-indexed).
* **Journeys and classes.** Journeys are the inductive `Reach`, and `tdist` is `d̂`. The nine
  classes `J k τ Δ V` transcribe Table 1 and are proved suffix-closed (`J_shift`).
* **Communication.** Synchronous, deterministic, full-information rounds (CSLib
  `Cslib.HeardOf`). Every process broadcasts its whole state to its current out-neighbours, and
  receivers know the senders. Codes may depend on the process. Each algorithm is designed for a
  fixed `n` and `Δ` and does not know `V` (the paper's well-formedness). Full information only
  strengthens the impossibilities.
* **No failures besides transient ones.** The initial configuration is arbitrary, and so are all
  local states, including the initial `msgs` of Algorithm `LE` (finite maps, timers in
  `{0, …, Δ}`).
* **Stabilization.** `SelfStab` is Definition 1 (legitimate set, convergence, correctness).
  `PseudoStab` is Definition 2 (every execution has a suffix satisfying `SP_LE`).
  `PseudoStabWithin T` bounds the pseudo-stabilization phase by `T`.
* **Weaker than the paper.** There is one state type for all processes, while the paper allows a
  set per process. This is equivalent up to a tagging reduction, which is not formalized; see
  differencies.md.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (hierarchy of classes over all vertex sets; per vertex set for `n ≥ 3`) | `theorem_1_classes`, `theorem_1`; `n = 2`: `not_theorem_1_card_two` | `Classes.lean` |
| Remark 1 (self ⇒ pseudo on recurring classes) | `SelfStab.pseudoStab`, `J_shift` | `Model.lean` |
| Lemma 1 | `lemma_1` | `Impossibility.lean` |
| Theorem 2 (no self-stab. LE in `J^B_{1,*}(Δ)`) | `theorem_2` | `Impossibility.lean` |
| Theorem 3 (no pseudo-stab. LE in `J^Q_{1,*}(Δ)`) | `theorem_3` | `Impossibility.lean` |
| Theorem 4 (no pseudo-stab. LE in `J^B_{*,1}(Δ)`, `n ≥ 3`) | `theorem_4`, `theorem_4_card_two` | `Impossibility.lean`, `Main.lean` |
| Theorem 5 (unbounded pseudo-stab. time in `J^B_{1,*}(Δ)`) | `theorem_5` | `Impossibility.lean` |
| Corollaries 1, 2, 3 | `corollary_1`, `corollary_2`, `corollary_3` | `Main.lean` |
| Algorithm 1 (`LE`) | `LE.algLE`, `LE.roundLE` | `LE/Defs.lean` |
| Lemmas 2–7 | `LE.provenance`, `LE.lemma_3`, `LE.lemma_4`, `LE.lemma_5`, `LE.lemma_6`, `LE.lemma_7` | `LE/Exec.lean`, `LE/Propagation.lean` |
| Lemmas 8–16 | `LE.fake_L`, `LE.fake_lsps`, `LE.fake_G`, `LE.lemma_9` … `LE.lemma_16` | `LE/Stable.lean` |
| Theorem 6, Corollary 6 (`LE` pseudo-stabilizing in `J^B_{1,*}(Δ)`) | `LE.theorem_6`, `LE.corollary_6` | `LE/Main.lean` |
| Theorem 7 (time `≤ 6Δ + 2` in `J^B_{*,*}(Δ)`) | `LE.theorem_7` (sharper: `LE.theorem_7_sharp`, `≤ 6Δ`) | `LE/Main.lean` |
| Figure 1 (summary, `n ≥ 3`) | `figure_1` | `Main.lean` |
| `IDSET` must be larger than `n` | `constAlg_selfStab` | `Counterexample.lean` |

**Not formalized.** The self-stabilizing algorithms for the three `J_{*,*}` classes, which come
from the authors' earlier paper (ICDCN 2021) and give the green area of Figure 1.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The hypotheses are satisfiable:
* `LE` is a concrete algorithm, and the classes are nonempty (e.g. `K_mem_J1sB`, `PK_mem_J1sB`).
* The impossibilities hold for every nonempty state type over any infinite identifier domain.

The dynamic-graph model reuses CSLib's `Cslib.HeardOf` (`conf`, `conf_agree`, `conf_splice`).

**CSLib candidates.** Temporal journeys / temporal distance (`Reach`, `tdist`, `tdist_le_iff`,
`Reach.shift_iff`) and the nine timeliness classes (`Model.lean`, `Classes.lean`) would fit next to
`Cslib.DynNet`. Finite maps with finite support (`LE.FMap`) are too ad hoc.
