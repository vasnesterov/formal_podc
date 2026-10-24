# Error-Free Multi-Valued Consensus — PODC 2011

Guanfeng Liang, Nitin Vaidya. *Error-Free Multi-Valued Consensus with Byzantine Failures.* PODC 2011.
DOI [10.1145/1993806.1993809](https://doi.org/10.1145/1993806.1993809). Formalized version: arXiv
[1101.3520](https://arxiv.org/abs/1101.3520) v1; numbering follows it.

**Verdict: ⚠️ Correct with fixes.** Algorithm 1 achieves consensus on `L`-bit values for `3t < n`
(Lemmas 1–5 and the correctness part of Theorem 1 hold). But the claim that the diagnosis stage runs at
most `t(t+1)` times (and thus the complexity bound) is false for the pseudo-code as printed: an already
isolated faulty processor can trigger the diagnosis stage in every generation. It holds once
announcements of isolated processors are ignored, as the paper's prose intends.

## Mistakes in the paper

* **An isolated processor can force the diagnosis stage forever (Theorem 1's `t(t+1)` bound, Lemma 4).**
  In Algorithm 1, every `P_j ∉ P_match` broadcasts `Detected_j`, and the diagnosis stage starts as soon
  as one of these bits is `true`. A faulty processor whose vertex is already isolated is never in
  `P_match`: the fault-free members do not trust it. So it can announce `Detected = true` in every
  generation. Take `n = 4`, `t = 1`, `P₃` faulty, all inputs equal. `P₃` behaves correctly except that
  it broadcasts `M₃ = false…false` and `Detected₃ = true`. In generation 1, step 3(f) isolates vertex 3.
  From then on the diagnosis stage runs in every generation and removes nothing, since vertex 3 has no
  edge left. Case 2 of the proof of Lemma 4 assumes that step 3(f) removes some edge at `j`, and misses
  the case where none is left. So Lemma 4 is false ("at least one edge … will be removed") and so is the
  `t(t+1)` bound; with 3 generations there are already `3 > 2` diagnosis stages. This is a false
  statement about the printed algorithm. The intended algorithm is clear from the prose: §3.3 says
  of an isolated processor that "the fault-free processors will not communicate with it anymore", and
  the proof of Theorem 1 argues that once all faulty processors are identified "the diagnosis stage
  will not be performed any more". So: ignore the `Detected` bits of isolated processors. For this repaired algorithm we prove Lemma 4 and the `t(t+1)` bound. Correctness holds
  for both versions. (`Counterexample.literal_not_theorem_1`, `Counterexample.literal_lemma_4_false`;
  repaired: `Run.theorem_1_numDiag`)
* **`⊥` in the checking stage is under-specified.** Untrusted senders give `R_i[j] = ⊥`, and
  "`R_j/P_match ∈ C₂ₜ`" is defined by equality with a codeword. Read literally, a fault-free processor
  outside `P_match` that distrusts a faulty member of `P_match` always reports a detection. Step 3(f)
  can then isolate this *fault-free* processor (a 2-generation scenario with `n = 4` is in
  `differencies.md`). The prose of §3.2 ("checks whether the symbols received from the trusted
  processors in `P_match` are consistent") and the proof of Lemma 4 (case 2(a)) state the intended
  reading: `⊥` entries are ignored, and the check and decoding use the trusted members of `P_match`. We formalize this reading.
  The literal reading's failure is described in `differencies.md` but not proved in Lean.
* **Minor.** Lemma 3 should assume that no processor *announces* a detection, not that none *detects*
  one. "`v_i(g)`, represented by `n − t` symbols" in §3.1 should be `n − 2t`. "`Detected_i`" in §3.2
  should be `Detected_j`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Synchronous, fully connected network of `n` processors with a static set `F` of `|F| ≤ t` Byzantine
  processors and `3t < n`. The paper's adaptive corruption is equivalent to this: the algorithm is
  deterministic and the adversary omniscient.
* Each generation is computed at the level of Algorithm 1's steps. `Broadcast_Single_Bit` is a black
  box with its specification: all fault-free processors get the same value, which is the source's
  value if the source is fault-free. So the broadcast values of faulty sources (`M_j`, `Detected_j`,
  `R#[j]`, `Trust_j`) are adversary choices. The point-to-point symbols of step 1(a) are explicit, and
  a faulty sender may send a different symbol to each receiver.
* The adversary also picks `P_match` and `P_decide` among the valid sets. This covers every
  deterministic selection rule.
* The code `C₂ₜ` is an abstract code with the MDS property: any `n − 2t` symbols determine the data.
  A `D`-bit part is a data word, and an `L`-bit value is a vector of `N = L/D` data words. A
  Reed–Solomon instance shows that the hypotheses are satisfiable.
* The diagnosis graph is a `SimpleGraph (Fin n)`, complete at the start and common to all fault-free
  processors.
* Two variants: `Variant.literal` (pseudo-code as printed) and `Variant.repaired` (`Detected` bits of
  processors without edges are ignored).

**Main results in Lean** (namespace `Podc.ErrorFreeMultivaluedBC`).

| Paper | Lean | File |
|---|---|---|
| Lemma 1 | `Gen.lemma_1` | `Generation.lean` |
| Lemma 2 | `Gen.lemma_2` | `Generation.lean` |
| Lemma 3 | `Gen.lemma_3` | `Generation.lean` |
| Lemma 4 (only bad edges removed; good processors always trust each other) | `Gen.lemma_4_goodClique`, `Run.goodClique_graph` | `Generation.lean`, `Theorem.lean` |
| Lemma 4 (some bad edge removed; repaired algorithm) | `Gen.lemma_4_progress` | `Generation.lean` |
| Lemma 4 is false for the literal algorithm | `Counterexample.literal_lemma_4_false` | `Counterexample.lean` |
| Lemma 5 (existence of `P_decide`) | `Gen.exists_pdecide` | `Generation.lean` |
| Lemma 5 | `Gen.lemma_5` | `Generation.lean` |
| Theorem 1 (consensus on `L`-bit values; both variants) | `Run.theorem_1_consensus` | `Theorem.lean` |
| Theorem 1 (≤ `t(t+1)` diagnosis stages; repaired) | `Run.theorem_1_numDiag`, `Run.theorem_1` | `Theorem.lean` |
| Theorem 1's bound is false for the literal algorithm | `Counterexample.literal_not_theorem_1` (`_rs` with Reed–Solomon) | `Counterexample.lean` |
| Equation (1) | `Run.cost_le` | `Complexity.lean` |
| Equation (2) | `ccon_opt` | `Complexity.lean` |
| Equation (3), `O(nL + n⁴L^0.5 + n⁶)` | `ccon_opt_le` | `Complexity.lean` |

**Not formalized.** The `Broadcast_Single_Bit` protocol (used as a specification). A bit-level cost
model: the per-stage counts of §3.4 are taken as definitions. Section 4 (broadcast and `t ≥ n/3`).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `Counterexample.theorem_1_nonvacuous` gives an admissible run of the
repaired algorithm with a Reed–Solomon code and a Byzantine processor. It runs the diagnosis stage
exactly once (`Counterexample.repaired_numDiag`). The abstract code (`Cslib.MDSCode`, with
`MDSCode.reedSolomon`) is staged in `Podc/Foundations/InformationTheory/MDSCode.lean` as a CSLib
candidate. The final statement uses CSLib's `Cslib.Byzantine.Problem.Consensus`.
