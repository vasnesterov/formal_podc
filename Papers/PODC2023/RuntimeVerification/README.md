# Wait-Free Runtime Verification of Linearizability — PODC 2023

Armando Castañeda, Gilde Valeria Rodríguez. *Asynchronous Wait-Free Runtime Verification and
Enforcement of Linearizability.* PODC 2023. DOI
[10.1145/3583668.3594563](https://doi.org/10.1145/3583668.3594563). Formalized version: arXiv
[2301.02638](https://arxiv.org/abs/2301.02638) v3 (Nov 2025, full version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All main results hold:
* the impossibility of runtime verification (Theorem 5.1);
* the impossibility of predictive runtime verification (Theorem A.1), under the black-box reading
  of the model;
* the predictive verifier for `DRV` and every `O ∈ GenLin` (Theorem 8.1);
* self-enforced implementations (Theorem 8.2).

Lemma 7.4 is false as stated: it fails for pending operations that no view has seen yet. The
proofs of Lemmas 8.1/8.2 routinely meet such operations. Their statements are still true once the
comparison is made with a prefix, and we prove them that way.

## Mistakes in the paper

* **Lemma 7.4 is false as stated.** It claims that every tight execution `E` is equivalent to its
  sketch `X(λ_E)`. This fails when a pending operation has written to `N` but no view has seen it
  yet, i.e. its `N.Write` comes after every `N.Snapshot`. Such an operation is missing from
  `X(λ_E)`. Example: a process completes one operation, then invokes a second one and writes it to
  `N`.
  This is an edge case for the lemma itself, but the proofs of Lemmas 8.1 and 8.2 meet it
  routinely. They apply Lemma 7.4 to executions in which such operations are normal: the execution
  `F` of Lemma 8.1, obtained by removing snapshot steps, and `T(E'|A*)` in Lemma 8.2. The proof of
  Lemma 8.1 also claims `≺_{F'} = ≺_{T(E')}`, where only `⊆` holds.
  The statements of Lemmas 8.1/8.2 are true. The fix is to compare with a prefix: truncate at the
  last relevant snapshot and use prefix closure. (`lemma_7_4_false`; `Exec.sketch_mem_of_tight`,
  `Exec.cut_mem_of_sketch`, `sketch_isAStarHist`)
* Smaller slips:
  * Claim 7.2 is stated for all implementations. It fails for abstract ones (sets of histories)
    but holds for `A*`.
  * Theorem 8.2 (2) needs `O ≠ ∅`.
  * Typos in the proofs of Lemma 7.3 ("`E` and `T(E)` are equivalent") and Lemma 8.2 (`H` should
    be a prefix of `X(τ'')`).
  * Theorem 8.2 (3) states the direction of similarity backwards.
  * Section 3 says the black-box requirement is "modeled as conceptually `V_O` taking `A` as its
    input". The intended reading is that one verifier works for every `A` (`∃V ∀A`), which is what
    we formalize. If `V_O` could depend on `A`, Definition 6.1 would be trivially solvable
    (`Impossibility.trivialVerifier_predictive`, a remark).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Histories.** We use CSLib's single-object Herlihy–Wing histories. Linearizability is CSLib's
  amended definition (Sela–Herlihy–Petrank), which is the paper's Definition 4.2. Similarity
  (Def. 7.1) is defined literally (`Obtain`, `Similar`) and shown equivalent to a semantic form
  (`similar_iff_simS`). `GenLin` (Def. 7.2) means closed under prefixes and similarity.
* **Impossibility.** `n ≥ 2` asynchronous processes run a verifier with the structure of Fig. 2.
  * Lines 03–05 and 08–12 are atomic transitions on an *arbitrary* shared memory, so any base
    objects are allowed, of any consensus number. They may read a global clock.
  * The environment chooses operations; each process chooses each operation at most once.
  * The input `A` is an abstract implementation: a prefix-closed set of well-formed histories. It
    answers within this set.
  * Executions are infinite and fair: each process runs infinitely many iterations. There are no
    crashes; wait-freedom is reflected in the atomic blocks.
  * The verifier does not depend on `A` (black box). `thm_5_1_nonuniform` and
    `trivialVerifier_predictive` treat the other reading.
* **Positive part.** An execution of `V_O` (Fig. 10) running `A*` (Fig. 7) over a black-box `A` is
  given by:
  * the operations each process invokes;
  * `A`'s responses, which must form a history of the prefix-closed set `𝒜`;
  * injective times of the 8 steps of each operation: `A*` invocation, `N.Write`, `A` invocation,
    `A` response, `N.Snapshot`, `A*` response, `M.Write`, `M.Snapshot` + test.

  Snapshots are atomic and return everything written before them. Executions of `A*` alone have
  6 steps per operation. Histories of `A*`, of `A`, of the tight execution `T(E)` and of
  `V_{O,A}` are timed histories (`TimedHist.lean`); their list versions are obtained by sorting by
  time. The sketch `X(τ)` of Section 7.3.3 is the timed history `XTH τ`.
* **Infinite executions** (`thm_8_1_inf`). A process may block forever inside `A`. The two standing
  assumptions are hypotheses:
  * a process that took its `N.Snapshot` also writes `M`;
  * tests occur at arbitrarily late times.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 3.1, Def. 6.1 | `RuntimeVerifies`, `PredictivelyVerifies` | `Impossibility.lean` |
| Theorem 5.1 (generic; queue, stack, priority queue, set, counter, consensus) | `Impossibility.thm_5_1`, `thm_5_1_weak`, `Objects.thm_5_1_queue`, … | `Impossibility.lean`, `Objects.lean` |
| Theorem A.1 | `Impossibility.thm_A_1`, `Objects.thm_A_1_queue`, … | same |
| Def. 6.1 trivial under the non-uniform reading | `Impossibility.trivialVerifier_predictive` | `Impossibility.lean` |
| Def. 7.1, 7.2 | `Similar`, `GenLin`, `similar_iff_simS` | `Similarity.lean` |
| Lemma 7.1 | `lemma_7_1` | `Similarity.lean` |
| Lemma 7.2 (correctness, ⇒) | `lemma_7_2` | `Main.lean` |
| Lemma 7.3 | `Exec.simTH_S_T`, `Exec.simTH_T_A` | `Exec.lean` |
| Lemma 7.4 (false) | `lemma_7_4_false` | `Lemma74.lean` |
| Lemma 8.1 (1), Cor. 7.2 | `sketch_isAStarHist` | `Witness.lean` |
| Lemma 8.1 (2) | `Exec.sketch_mem_of_tight` | `Theorems.lean` |
| Lemma 8.2 | `Exec.cut_mem_of_sketch` | `Theorems.lean` |
| Theorem 8.1 (finite / infinite executions) | `thm_8_1`, `thm_8_1_inf` | `Main.lean` |
| Theorem 8.2 | `thm_8_2` (+ `Exec.hVy_mem_of_noReport`, `Exec.hVy_cut_mem`) | `Main.lean`, `Enforce.lean` |

**Not formalized.**
* Progress and step-complexity claims (Lemma 7.2 progress part, Claim 8.1, Thm 8.1 (1),
  Thm 8.2 (1)).
* Read/write implementations of snapshots.
* Lemma 7.2 (⇐).
* Set-/interval-linearizability as members of `GenLin`.
* Section 9 extensions.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The model builds on CSLib's Herlihy–Wing histories
(`Cslib/Computability/Distributed/SharedMemory/HerlihyWing/`).

Non-vacuity:
* linearizability w.r.t. any state machine is in `GenLin` (`lemma_7_1`);
* the impossibility instances exhibit concrete objects satisfying the hypotheses;
* `lemma_7_4_false` is a concrete execution.

CSLib candidates (not upstreamed):
* `TimedHist.lean`: timed histories ↔ Herlihy–Wing histories, with sorted-list uniqueness helpers;
* `Similarity.lean`: `similar_iff_simS` and Lemma 7.1, i.e. prefix and similarity closure of
  linearizability.
