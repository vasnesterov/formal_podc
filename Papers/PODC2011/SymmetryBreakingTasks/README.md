# The Universe of Symmetry Breaking Tasks — PODC 2011

Damien Imbs, Sergio Rajsbaum, Michel Raynal. *The universe of symmetry breaking tasks.* PODC 2011
(brief announcement). DOI [10.1145/1993806.1993857](https://doi.org/10.1145/1993806.1993857).
Formalized version: the full version, IRISA technical report PI 1965 (January 2011; HAL inria-00560453v1, the PDF
in this repository). There is no arXiv version. Numbering follows the technical report.

**Verdict: 🔧 Easy fix.** The combinatorics of GSB tasks (feasibility, kernel sets, anchoring, the hardest task and
the canonical form) and the reductions (perfect renaming is universal, Theorem 10's parity reduction, the
slot-to-renaming algorithm) hold after local changes. Theorem 9 is correct for index-independent algorithms but
false for the comparison-based algorithms that Section 2.3 requires of all algorithms, and Lemma 1 misses the
hypothesis `ℓ_v ≤ u_v`. Theorems 1, 2 and 11 were not checked, and the cited impossibility of WSB is a hypothesis.

## Mistakes in the paper

### 🔧 Theorem 9 (no-communication solvability) vs. Section 2.3
Theorem 9 is false for the comparison-based algorithms that Section 2.3 requires of all algorithms: then
`⟨2,3,0,1⟩` meets the criterion (`ℓ = 0`, `⌈3/3⌉ ≤ 1`) but is not solvable without communication
(`theorem_9_comparisonBased_false`).

**Impact.** Theorem 9 is correct for index-independent algorithms that may use the identity's value; we
formalize it that way (`theorem_9`). The same goes for the "decide your own identity" solution of
`(2n−1)`-renaming and for Corollary 2.

**Details.** Section 2.3 says that only index-independent *and comparison-based* algorithms are
considered, and Theorem 2 claims this is without loss of generality. That claim only holds with
communication: its transformation runs a renaming algorithm first. Without communication, a
comparison-based decision function is constant. Then a GSB task with `m ≥ 2` is solvable iff
`ℓ = 0 ∧ u ≥ n`, and Theorem 9's "if" direction fails (`noComm_comparisonBased_iff`). Index independence
is essential: with index-dependent decisions, perfect renaming needs no communication
(`perfectRenaming_indexDependent`).

### 🔧 Lemma 1 (missing hypothesis `ℓ_v ≤ u_v`)
"Feasible iff `Σℓ_v ≤ n ≤ Σu_v`" is false for asymmetric bounds with some `ℓ_v > u_v`: `n = 3`,
`ℓ⃗ = [2,0]`, `u⃗ = [1,5]` satisfies `2 ≤ 3 ≤ 6`, but value 1 would have to be decided at least twice and at
most once (`lemma_1_false`).

**Impact.** The correct statement adds `ℓ_v ≤ u_v` for all `v` (`lemma_1`). Lemma 2, the symmetric case,
is correct as stated.

### ✏️ Slips
- Theorem 4 (anchoring criterion, `ℓ = 0`): "`u`-anchored iff `ℓ ≤ n − u(m−1)`" fails in integer arithmetic whenever
  `ℓ = 0` and `u(m−1) > n`, e.g. for `⟨6,3,0,6⟩` and every `(2n−1)`-renaming task `⟨n,2n−1,0,1⟩` with `n ≥ 3`
  (`theorem_4_int_false`, `theorem_4_int_false_renaming`). Every `⟨n,m,0,u⟩` task is trivially `u`-anchored, as the
  paper itself says, but the right-hand side is negative; `⟨6,3,0,6⟩` is the task that Figure 1 labels "trivially
  u-anchored". Corollary 1 uses `max(0, n−u(m−1))`, so the authors knew the expression can be negative. With
  `n − u(m−1)` truncated at 0 the theorem holds (for `m ≥ 1`), and we prove that version (`theorem_4`).
- Section 4.2, the canonical representative: "an `(ℓ,u)`-anchored task is its own representative" picks two
  different representatives when `u > n`: `⟨4,2,0,5⟩` and `⟨4,2,0,4⟩` are synonyms and both `(ℓ,u)`-anchored
  (`canonical_not_unique`). This happens only in degenerate cases (also for `m = 1`), and Theorem 7's map `f` fixes it
  (`theorem_7`, `theorem_7_iff`): `f` reaches its fixed point after one step, and two feasible tasks are synonyms iff
  they have the same `f`-image. The `f`-image is the pair (least, largest) number of times a value is decided in a
  legal output.
- Theorem 8 needs a *feasible* task (`theorem_8`).
- Corollary 2 needs `x ≥ 1` (`corollary_2`).
- Theorem 11 needs `n ≥ 2`: for `n = 1` election is trivial.
- Table 1 claims to list all feasible `⟨6,3,ℓ,u⟩` tasks with `u ≤ 6`, but `⟨6,3,2,6⟩` is missing. Every
  printed entry is correct (`table_1`, `table_1_missing_row`).
- The kernel set of `⟨6,3,1,4⟩` is printed as `{[4,1,1],[4,1,1],[2,2,2]}`; it should be
  `{[4,1,1],[3,2,1],[2,2,2]}`.
- Section 4.2 says `⟨6,3,2,2⟩` is the representative for four tasks, but §4.1 and Table 1 list six synonyms.

### Typos
- Theorem 6 is trivial as stated: `S(T1) ⊆ S(T)` for `ℓ' ≥ ℓ` is just Lemma 5 (and (ii) is Lemma 4). The
  intended statement, shown by its proof, is that `T1` and `T` are *synonyms*. That is true and needs no
  feasibility assumption (`theorem_6`, `theorem_6_eq`).
- Theorem 8's proof writes `m/n` for `n/m` throughout.
- Theorem 11's proof cites "Lemma 2" for Theorem 2.
- In the Remark of §4.1, `[4,2,1]` sums to 7, so it is not a kernel vector of any 6-process task.

## Proof gaps (statements true)

### 🔧 Theorem 9 (the `ℓ = 0` part of the proof)
"The task specification requires `|G_i| ≤ u`" is not what the specification says.

**Impact.** Statement true (for index-independent algorithms); the `ℓ > 0` part is fine (`theorem_9`).

**Repair.** Pick `u+1` identities from a group of size `> u` and complete them to `n` distinct
identities. This needs `u+1 ≤ n`, which holds because `⌈(2n−1)/m⌉ ≤ n` for `m ≥ 2`. (`theorem_9`)

### 🔧 Theorem 10 (Lemma 4 used in the wrong direction)
`S(T) ⊆ S(T')` makes `T'` *easier*, so unsolvability of `T` says nothing about `T'`.

**Impact.** Statement true, given the cited results: the conclusion survives because the tasks involved
are synonyms (Theorem 3) (`theorem_10`).

**Repair.** It also follows directly: the parity map turns every `⟨n,m,1,u⟩` output into a WSB output,
for every `u`. (`parity_mem_wsb`, `theorem_10`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* A GSB task is its set of output vectors `O : Fin n → Fin m` (Definition 2): `gsb n ℓ u` (asymmetric)
  and `sgsb n m ℓ u` (symmetric). Values are `0..m−1` and identities are `Fin N`. Synonyms are equal
  sets. Arithmetic is in `ℕ`.
* Algorithms (Theorems 8, 10, Corollary 5): CSLib's iterated full-information model `Cslib.Iterated`
  (any round model, any number of rounds). A GSB task is the task `gsbTask N S`: any participating set,
  distinct identities, and the participants' decisions must extend to an output vector in `S` (the
  validity of Definition 1). Reductions are local post-processing of decisions by a fixed map, so they
  preserve uniform code (`Alg.IndexIndependent`, `Podc/.../IteratedModel/PostProcess.lean`). For
  `t ≥ 1` rounds this is weaker than the paper's permutation-invariant index independence, since
  full-information views are indexed by process; for `0` rounds (Theorem 9) the two coincide.
* No communication (Theorem 9, Corollaries 2–4): one decision function `δ : Fin N → Fin m` applied by
  every process to its own identity, with `N = 2n − 1`. `noComm_iff` proves this is exactly 0-round
  solvability by an index-independent algorithm in any iterated model.
* Theorem 12 (Figure 2): executions where all processes decide, abstracted to the `(n−1)`-slot outputs
  of the `KS` object and the linearization times of each process's write and snapshot (all distinct).
  A snapshot contains `STATE[j]` iff `j`'s write precedes it. Decisions are write-once and validity only
  concerns such executions, so this loses nothing.
* Not modelled: the full asynchronous crash-prone read/write model of Section 2 (runs, schedules).
  Impossibility results (Theorem 10, Corollary 5) are taken as hypotheses about any iterated model.

**Proof remarks.** Corollary 4 is stated with `k ≤ n` (`corollary_4`), which is implicit in the `k ≤ n/2` of
Section 3.2.

**Main results in Lean** (namespace `Podc.SymmetryBreakingTasks`).

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (corrected / counterexample) | `lemma_1` / `lemma_1_false` | `Basic.lean` |
| Lemma 2 | `lemma_2` | `Basic.lean` |
| Lemmas 4, 5 | `lemma_4`, `lemma_5` | `Basic.lean` |
| §3.2: renaming, perfect renaming, `k`-slot, WSB, election | `sgsb_zero_one`, `sgsb_one_one`, `kSlot_eq`, `wsb_synonyms`, `election_subset_wsb` | `Basic.lean` |
| Defs 3–4, Lemma 3; kernel set determines the task | `countingVectors`, `kernelSet`, `lemma_3`, `kernelSet_eq_iff` | `Structure.lean` |
| Balanced kernel vector in every feasible task | `balanced_mem_kernelSet` | `Structure.lean` |
| Def 5, Theorem 3 | `LAnchored`, `UAnchored`, `theorem_3` | `Structure.lean` |
| Theorem 4 (ℕ version / integer version false) | `theorem_4` / `theorem_4_int_false`, `theorem_4_int_false_renaming` | `Structure.lean` |
| Corollary 1 | `corollary_1` | `Structure.lean` |
| Theorem 5 (+ examples `⟨10,4,2,3⟩`, `⟨10,5,2,2⟩`) | `theorem_5`, `theorem_5_examples` | `Structure.lean` |
| Theorem 6 (as stated / as synonymy) | `theorem_6` / `theorem_6_eq` | `Structure.lean` |
| Theorem 7 (canonical form) | `canon`, `theorem_7`, `theorem_7_iff` | `Structure.lean` |
| §4 examples, Table 1 | `anchoring_examples`, `table_1`, `table_1_missing_row`, `synonyms_6_3`, `incomparable_6_3`, `canonical_not_unique` | `Examples.lean` |
| Theorem 8 (output maps / algorithms) | `theorem_8_asymm`, `theorem_8_symm` / `theorem_8` | `Computability.lean` |
| Theorem 9, `m = 1` remark | `theorem_9`, `noComm_of_one`, `noComm_iff` | `Computability.lean` |
| Corollaries 2, 3, 4 | `corollary_2`, `corollary_3`, `corollary_4` | `Computability.lean` |
| Model sensitivity of Theorem 9 | `perfectRenaming_indexDependent`, `ComparisonBased.const`, `noComm_comparisonBased_iff`, `theorem_9_comparisonBased_false` | `Computability.lean` |
| Theorem 10 (reduction; cited result as hypothesis) | `parity_mem_wsb`, `theorem_10` | `Computability.lean` |
| Election solves WSB; Corollary 5 (Theorem 11 as hypothesis) | `election_solves_wsb`, `corollary_5` | `Computability.lean` |
| Theorem 12 (Figure 2) | `SlotRenaming.theorem_12` | `SlotRenaming.lean` |

**Not formalized.** Theorems 1 and 2 (they rely on a cited comparison-based `(2n−1)`-renaming
algorithm) and Theorem 11 (pseudomanifold/connectivity argument on the protocol complex). The cited
impossibility of WSB (Castañeda–Rajsbaum) is a hypothesis of `theorem_10`; election impossibility is a
hypothesis of `corollary_5`. The cited equivalence of WSB with `(2n−2)`-renaming was not checked.

**Trust.** No `sorry`, `axiom` or `native_decide`. The listed theorems use only the axioms `propext`,
`Classical.choice`, `Quot.sound`; Table 1 is checked by `decide +kernel`. Non-vacuity: every
feasibility hypothesis is discharged in the examples (`table_1`, `synonyms_6_3`, …), and the
hypotheses of Theorem 12 are satisfiable (`theorem_12_hyps_satisfiable`). The algorithm model is
CSLib's `Cslib.Computability.Distributed.IteratedModel.Basic`; `Fintype.exists_fin_labelling` (CSLib
`Foundations/Combinatorics/Labelling`) realizes count vectors.

**CSLib candidate.** `Podc/Computability/Distributed/IteratedModel/PostProcess.lean` covers
`Alg.mapDec`, `Alg.IndexIndependent`, and `Solves.mapDec` / `Solvable.mapDec` / `Solvable.mapDec_contra`
(reductions by local post-processing).
