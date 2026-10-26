# A Complexity-Based Hierarchy for Multiprocessor Synchronization — PODC 2016

Faith Ellen, Rati Gelashvili, Nir Shavit, Leqi Zhu. *A Complexity-Based Hierarchy for Multiprocessor
Synchronization.* PODC 2016. DOI [10.1145/2933057.2933113](https://doi.org/10.1145/2933057.2933113).
Formalized version: arXiv [1607.06139](https://arxiv.org/abs/1607.06139) v2 (2018).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** All formalized theorems hold as stated: the space lower bounds
(`⌈(n−1)/ℓ⌉` ℓ-buffers, `⌈(n−1)/2ℓ⌉` locations with multiple assignment, one max-register / one
read-write-FAI location insufficient, unboundedly many test-and-set locations) and the matching
algorithms. But several proofs needed repair: Lemma 9.1 has a real gap, Lemma 7.1's proof is wrong
(statement true), and Lemma 8.2 is false as stated, though never used in the false case.

## Mistakes in the paper

* **Lemma 9.1 (test-and-set): proof gap, statement true.** The proof takes `β`, the shortest prefix of
  `z`'s solo execution from `Cα_kξ` that ends with a test-and-set on a location `r ∉ L_k`. It then
  reasons about `Cα_kξψβ` and `Cα_kξψψ'β`, where `ψ, ψ'` are steps of `p_1`. But in those executions
  `z`'s preliminary steps of `β` (reads, test-and-sets on `L_k`) run *after* `ψ`, which may set
  locations to 1. They may then return different values, so `z` need not perform `β` at all, and the
  claims that "`β` sets `r` to 1" and that the two configurations are indistinguishable to `p_0` are
  unjustified. Repair: run `z`'s preliminary steps first (they change no memory), so that `z` is
  poised on `r`; its single remaining step commutes with any single step of `p_0`/`p_1`. This also
  removes the case analysis on `ψ'`. Lemma 9.1 and Theorem 9.2 then hold as stated (`lemma_9_1`).
* **Lemma 7.1: proof wrong, statement true.** The proof takes *any* maximal Eulerian trail
  `r_1, …, r_t` and re-packs along it from each `r_j` to `r_t`. If the trail visits `r_t` earlier,
  this does nothing. Example: locations `A, B, C`, processes `p1, p2, p3`, 2-packings `g = (A, B, C)`
  and `h = (B, C, B)`. The unique maximal trail from `A` is `A→B→C→B`, and re-packing from `j = 2`
  leaves `B` unchanged. Taking a *shortest* such sequence fixes the proof. We prove Lemma 7.2 directly
  instead, by an augmenting-path argument (`lemma71_trail_counterexample`; `fullyPacked_of_cov`).
* **Lemma 8.2 (swap/read algorithm): false in an unused edge case.** For a scan `S` with
  `ℓ_v(S) = 1` it asks for an earlier scan `T` in which all laps are `0`. But every scanner has lap
  `≥ 1` on its own input from line 1, so no such `T` exists. The lemma is applied only with
  `ℓ_v(S) ≥ 2` (Lemma 8.4), where it holds. Theorem 8.8 is unaffected (invariant `SwapRead.AInv`).
* **The proofs of Lemmas 6.5 / 7.3 need `R ≠ ∅`** (they start from a process `p ∈ R`), but
  Theorems 6.8 / 7.5 use them for `n = 2`, where `R = ∅`.
  The needed conclusion (at least one location) follows from a separate easy argument: with no
  locations, two processes cannot communicate (`no_locations`).
* **Implicit steps, filled in.**
  * Lemma 3.2: validity needs every scan to see a nonzero component. Otherwise the argmax of an
    all-zero vector could be an unproposed value, since decrements lower counts.
  * Lemma 6.6: one must truncate `α` after its first decision, so that `U'` stays undecided.
  * Theorem 4.2 and Section 8: the step from linearizable double-collect scans to atomic-scan
    reasoning is left implicit; we prove it (a ghost chain of
    observed pairs for Theorem 4.2, a step-by-step simulation for Section 8).
  * Theorem 4.2: validity needs the observation that a process seeing `m1 = (0,0)` itself wrote
    `(0, input)`.
  * Lemma 8.6 proves only weak validity; standard validity also holds.
* **Typos.**
  * The Section 7 introduction says `⌈n/2ℓ⌉` locations are necessary; Theorem 7.5 and the proof
    give `⌈(n−1)/2ℓ⌉`.
  * Lemma 7.3: "`Cζβ1β2`" should be "`Cξβ1β2`".
  * Lemma 7.4: "at mostwot two".
  * Theorem 4.2: "(r,x) ≺ (r′,x)" should be "(r,x) ≺ (r′,x′)".
  * "Anonymous" (Section 8) is inaccurate: the swapped values carry process ids.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (CSLib asynchronous shared memory, `Cslib.SharedMemory`).
* Deterministic processes, arbitrary interleavings, no randomization; a process may stop taking steps.
  Every location supports the same atomic instruction set. Initial memory is arbitrary, and the lower
  bounds hold for every initialization.
* Multiple assignment (Section 7): the whole memory is one base object with an atomic multi-location
  ℓ-buffer write. Section 6's per-location model embeds into it, so both lower bounds are instances
  of one theorem (`lowerBound_core`).
* Consensus as a one-shot task: a process participates by invoking it with its input. Lower bounds
  assume only weak validity ("all inputs `v` ⇒ decide `v`") and only one-shot obstruction-freedom
  (solo termination). Upper bounds prove agreement, standard validity and full obstruction-freedom.
  Both directions are thus at least as strong as the paper's.
* Lower bounds are proved for binary consensus and transferred to `n`-valued consensus
  (`*_multivalued`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemmas 3.1, 3.2 (racing counters) | `lemma_3_1`, `lemma_3_2` | `RacingCounters.lean`, `RacingCountersBounded.lean` |
| Theorem 3.3 (one location: multiply / set-bit / add) | `theorem_3_3_multiply`, `theorem_3_3_setBit`, `theorem_3_3_add` | `RacingCounters{Multiply,SetBit,Add}.lean` |
| Theorems 4.1, 4.2 (max-registers) | `theorem_4_1`, `theorem_4_2` | `MaxRegister.lean`, `MaxRegisterAlg.lean` |
| Theorem 5.1 (read/write/FAI) | `theorem_5_1` | `FetchInc.lean` |
| Lemma 6.1, Theorem 6.3 (ℓ-buffer algorithms) | `lemma_6_1`, `theorem_6_3` | `BufferAlg.lean`, `BufferAlgConsensus.lean` |
| Lemmas 6.5/7.3, 6.7/7.4 | `key_lemma`, `zhu_induction` | `CoreLemma.lean`, `Zhu.lean` |
| Theorem 6.8 (and Zhu's `n−1` registers) | `theorem_6_8`, `theorem_6_8_ceil`, `zhu_registers` | `BufferLB.lean` |
| Lemma 7.2, Theorem 7.5 | `fullyPacked_of_cov`, `theorem_7_5`, `theorem_7_5_ceil` | `Packing.lean`, `BufferLB.lean` |
| Theorem 8.8 (`n−1` swap/read locations) | `theorem_8_8` | `SwapAlgOF.lean` |
| Lemma 9.1, Theorem 9.2 | `lemma_9_1`, `theorem_9_2`, `theorem_9_2_multivalued` | `TestAndSet.lean`, `NConsensus.lean` |

**Not formalized.** Lemma 5.2 / Theorem 5.3 (needs composition of consensus protocols), Theorems
9.3–9.4, Table 1 entries cited from other papers, the remarks on heterogeneous capacities, and the
`3n−2` scan bound of Lemma 8.7 (only solo termination is proved).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The upper bounds (Theorems 6.3, 8.8) also show that the lower bounds are not vacuous.
Model, consensus tasks, valency framework (Lemmas 6.4, 6.6) and the binary reduction come from CSLib
`Cslib/Computability/Distributed/SharedMemory/`, including the parts first developed in this project's shared library (now upstreamed): the readable swap
object `rswapObj` (Theorem 8.8's locations), poised processes and blocks (`Impl.PoisedAt`,
`Impl.runFrom_poised_block`, behind `Impl.Poised` and `Impl.runFrom_block`), reachability of solo
steps (`Impl.Reachable.soloStep`), the "last index" argument of valency proofs
(`Nat.exists_lt_and_not_succ_of_not`), `Fintype.sum_update_add`, the current operation instance
`curOp` (`Cslib/Computability/Distributed/SharedMemory/History.lean`, in `BufferAlg.lean`), and the walks of the packing
argument are CSLib's `Relation.RelatesInSteps`, cut at the first visit of their target by
`Relation.RelatesInSteps.exists_le_first_visit` (`Cslib/Foundations/Combinatorics/Digraph/Walk.lean`).
