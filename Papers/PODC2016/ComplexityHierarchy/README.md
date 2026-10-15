# A Complexity-Based Hierarchy for Multiprocessor Synchronization

Faith Ellen, Rati Gelashvili, Nir Shavit, Leqi Zhu. PODC 2016, pp. 289–298.
DOI [10.1145/2933057.2933113](https://doi.org/10.1145/2933057.2933113); full version arXiv
[1607.06139](https://arxiv.org/abs/1607.06139) (v2, 2018; used for the formalization). Local PDF:
`papers/2016/2933057.2933113_A_Complexity_Based_Hierarchy_for_Multiprocessor_Synchronization.pdf`.

The paper classifies instruction sets `I` by `SP(I, n)`, the number of memory locations needed
to solve obstruction-free `n`-valued consensus among `n` processes (Table 1): upper bounds by
algorithms, lower bounds by covering/valency arguments. Main technical results: the `ℓ`-buffer
lower bound `⌈(n−1)/ℓ⌉` (Thm 6.8, extending Zhu's `n−1` register bound) and the multiple
assignment lower bound `⌈(n−1)/2ℓ⌉` (Thm 7.5).

## Model (explicit choices)

CSLib asynchronous shared-memory model `Cslib.SharedMemory`:

* asynchronous, deterministic processes `P` (finite, `n = |P|`), arbitrary interleavings; no
  explicit crashes (a process may stop taking steps); no randomization;
* shared memory = base objects (`Impl A B P L`), each access is one atomic instruction on one
  location; the uniformity requirement (all locations support the same instruction set) is built
  into the base-object family (`fun _ : ι => obj`). Initial memory contents are arbitrary
  (`Impl.memInit`, chosen by the algorithm) — the lower bounds hold for every initialization;
* **multiple assignment** (Section 7): the whole memory of `ℓ`-buffers is one base object
  `MB R ℓ V` (locations `R`) with `read r` and `write w` (an `ℓ-buffer-write` to every `r` with
  `w r = some x`, atomically). Section 6's per-location model (`fun _ : ι => bufferSpec ℓ V`)
  embeds into it (`toMB`);
* consensus as a one-shot task (`Cslib/Computability/Distributed/SharedMemory/{Task,Consensus}.lean`): a process invokes the
  task with its input and returns its decision; `consensus P V` = agreement + validity (decision =
  input of a participant); lower bounds assume only `weakConsensus` (agreement + "if all
  participants have input `v`, decide `v`"), which is implied by the paper's validity;
* progress: obstruction-freedom. Lower bounds assume only `Impl.OneShotOF` (solo termination from
  configurations reached by one-shot executions); upper bounds prove CSLib's full
  `Impl.ObstructionFree`;
* "every process has an input initially" = all processes invoked first (`Impl.Reach`).

## Results ↔ Lean

Namespace `Cslib.SharedMemory.ComplexityHierarchy` unless noted.

| Paper | Lean | File | Status |
|---|---|---|---|
| Lemma 3.1 (racing counters, `m`-component unbounded counter) | `lemma_3_1`, `racing_solves`, `racing_obstructionFree` | `RacingCounters.lean` | proved |
| Lemma 3.2 (bounded counter, values in `{0..3n−1}`) | `lemma_3_2`, `racing2_solves`, `racing2_obstructionFree` | `RacingCountersBounded.lean` | proved (gap filled, see differencies) |
| Thm 3.3 (one location: read + multiply / set-bit / add) | `theorem_3_3_multiply`, `theorem_3_3_setBit`, `theorem_3_3_add` (+ `_general`) | `RacingCounters{Multiply,SetBit,Add}.lean` | proved |
| Thm 4.1 (one max-register is not enough) | `theorem_4_1` (any linear order of values) | `MaxRegister.lean` | proved |
| Thm 4.2 (two max-registers suffice) | `theorem_4_2` (+ `_general`, `TwoMax.alg_safe`, `TwoMax.alg_obstructionFree`, encoding `TwoMax.encode_strictMono`) | `MaxRegisterAlg.lean` | proved |
| Thm 5.1 (one read/write/FAI location is not enough) | `theorem_5_1` | `FetchInc.lean` | proved |
| Lemma 6.1 (one ℓ-buffer = history object with ≤ ℓ appenders) | `lemma_6_1` (CSLib `Linearizable`), core `recon_correct` | `BufferAlg.lean` | proved |
| Lemma 6.2 (ℓ single-writer registers from one ℓ-buffer) | not stated separately (the algorithm of Thm 6.3 appends increments directly to the group's history) | — | skipped |
| Thm 6.3 (`⌈n/ℓ⌉` ℓ-buffers suffice for `n`-consensus) | `theorem_6_3`, `BufCons.alg_safe`, `BufCons.alg_obstructionFree` | `BufferAlgConsensus.lean` | proved (tightness / non-vacuity of Thm 6.8) |
| Lemma 6.4 | `Impl.exists_initial_bivalent` | `Cslib/Computability/Distributed/SharedMemory/Valency.lean` | proved |
| Lemma 6.5 / Lemma 7.3 | `key_lemma` (common generalization; needs `R ≠ ∅`) | `CoreLemma.lean` | proved |
| Lemma 6.6 | `Impl.Reach.exists_two_deciders` | `Cslib/Computability/Distributed/SharedMemory/Valency.lean` | proved |
| Lemma 6.7 / Lemma 7.4 | `zhu_induction` (with `k`-packings, `k = ℓ` or `2ℓ`) | `Zhu.lean` | proved |
| Thm 6.8 (`⌈(n−1)/ℓ⌉` ℓ-buffers necessary) | `theorem_6_8`, `theorem_6_8_ceil`; Zhu's `n−1` registers: `zhu_registers` | `BufferLB.lean` | proved |
| Lemma 7.1 | not used; replaced by augmenting paths (`exists_packing_lt_of_walk`); the proof's maximal-trail claim is refuted by `lemma71_trail_counterexample` | `Packing.lean` | statement fine, proof gap documented |
| Lemma 7.2 | `fullyPacked_of_cov` | `Packing.lean` | proved (different proof) |
| Thm 7.5 (`⌈(n−1)/2ℓ⌉` locations with multiple assignment) | `theorem_7_5`, `theorem_7_5_ceil` | `BufferLB.lean` | proved |
| Lemmas 8.1–8.6 (swap/read algorithm, atomic-scan level) | `SwapRead.AInv`, `SwapRead.AInv.agree`, `SwapRead.AInv.valid` | `SwapAlgAbstract.lean` | proved (strong validity; Lemma 8.2 needs ℓ ≥ 2) |
| Thm 8.8 (`n−1` read/swap locations suffice), Lemma 8.7 (termination part) | `theorem_8_8`, `swapAlg_solves`, `swapAlg_obstructionFree`; double collect reduced to atomic scans by `SInv.sim` | `SwapAlg.lean`, `SwapAlgOF.lean` | proved (the `3n−2` scan bound not formalized) |
| Lemma 9.1 | `lemma_9_1` (finitely many locations, `[Fintype ι]`) | `TestAndSet.lean` | proved (proof repaired) |
| Thm 9.2 (read + test-and-set: unbounded number of locations, `n ≥ 3`) | `theorem_9_2` (binary), `theorem_9_2_multivalued` (`n`-consensus): for every *finite* set of locations (`[Fintype ι]`) no algorithm exists | `TestAndSet.lean`, `NConsensus.lean` | proved |
| "lower bounds for binary consensus apply to `n`-consensus" | `Impl.toBinary`, `solves_toBinary`, `oneShotOF_toBinary`; `theorem_{4_1,5_1,6_8,7_5,9_2}_multivalued` | `Cslib/Computability/Distributed/SharedMemory/BinaryReduction.lean`, `NConsensus.lean` | proved |

### Not formalized

* Lemma 5.2 / Thm 5.3 (`O(log n)` locations with read/write/increment): needs composition of
  consensus sub-protocols, for which there is no infrastructure (CSLib has no composition theorem).
* Thms 9.3/9.4 and the Table 1 entries that cite other papers ([GR05], [Bow11], [FHS98], [EGZ18]).
* The remarks after Thm 6.8 (heterogeneous capacities: sum of capacities `≥ n−1`; other
  instruction sets simulated by ℓ-buffers) and the corresponding remark for Section 7.

## Infrastructure built

* `Cslib/Computability/Distributed/SharedMemory/Consensus.lean` — consensus tasks (`consensus`, `weakConsensus`).
* `Cslib/Computability/Distributed/SharedMemory/Valency.lean` — valency framework for binary consensus (`BinCons`, `Steps`,
  `CanDecide`, `Bivalent`, `Reach`, agreement lemmas, solo decisions, initial configurations,
  Lemmas 6.4 and 6.6).
* `Cslib/Computability/Distributed/SharedMemory/BinaryReduction.lean` — multivalued → binary consensus reduction.
* Paper folder: `Buffer.lean` (ℓ-buffer memory with multiple assignment, block-write
  obliteration), `Packing.lean` (k-packings, Lemma 7.2), `CoreLemma.lean`, `Zhu.lean`.

## CSLib candidates

* `Cslib/Computability/Distributed/SharedMemory/{Consensus,Valency,BinaryReduction}.lean` (now in CSLib).
* `Packing.lean` (pure combinatorics of capacitated assignments; augmenting paths).
* From the racing-counters files: `cntF_update`, `respsOf_ret_single`; from `BufferAlg.lean`: `GoodW`/`recon_correct` (history object from an ℓ-buffer), `BufCons.AgreeV`; `swapLoc` (read/swap base object).
* `Config.ext'` (CSLib's `Config` has no `@[ext]`).

## Status

Complete for the formalized results: no `sorry`/`axiom` in any file of this folder or in
`Cslib/Computability/Distributed/SharedMemory/{Consensus,Valency,BinaryReduction}.lean`; all modules build and import
together without name clashes; `#print axioms` / `lean_verify` of the main theorems
(`theorem_3_3_*`, `lemma_3_1/3_2`, `theorem_4_1/4_2`, `theorem_5_1`, `lemma_6_1`, `theorem_6_3`,
`theorem_6_8`, `theorem_7_5`, `theorem_8_8`, `lemma_9_1`, `theorem_9_2`, `*_multivalued`) shows only
`propext`, `Classical.choice`, `Quot.sound`. Algorithms were model-checked in Python/C++ (small
parameters) before proving. Model-checking scripts were not kept in the repo.
