# How Fast Reads Affect Multi-Valued Register Simulations — PODC 2019

Soma Chaudhuri, Reginald Frank, Jennifer L. Welch. *Brief Announcement: How Fast Reads Affect
Multi-Valued Register Simulations.* PODC 2019. DOI
[10.1145/3293611.3331580](https://doi.org/10.1145/3293611.3331580). Formalized version: the 3-page
brief announcement (author copy from NSF-PAR, retrieved via web.archive; no arXiv or full version), whose
proofs are condensed; numbering follows it. The gaps in Section 3 below are of the kind expected from such
compression; the Lemma 4.2 gap is not (its one-line justification is false). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired.** All results hold: Theorem 3.1 (`log₂ k` reads are needed), Theorem 3.2 and
Corollary 3.5 (a safe/regular simulation whose reads take `log₂ k` reads needs writes of `log₂ k` base writes),
Lemmas 3.3/3.4, and Theorem 4.1 (no atomic simulation with two readers has reads of `log₂ k` steps; `k > 2`).
The proof of Lemma 4.2, on which the paper's proof of Theorem 4.1 rests, has a genuine gap: it relies on a
claim about decision trees that is false. We repair the proof of Theorem 4.1 with a case split.

## Mistakes in the paper

No mistakes in the statements.

## Proof gaps (statements true)

### 🛠️ Lemma 4.2 (same root of `T₁` and `T₂`), used by Theorem 4.1
The proof's key step "a value `z` whose root-to-leaf path in `T₂` does not include `r₁` must exist since `r₁` is
not the root of `T₂`" is false for decision trees (`lemma_4_2_gap`).

**Impact.** Lemma 4.2 and Theorem 4.1 are true; we repair the proof of Theorem 4.1 with a case split
(`theorem_4_1`, `setting_false`).

**Details.** The proof picks "a value `z` whose root-to-leaf path in `T₂` does not include `r₁`. Such a value must
exist since `r₁` is not the root of `T₂`." This does not follow. In a complete decision tree of depth 2 whose root
reads register 1 and whose two children both read register 0, every root-to-leaf path reads register 0, which is
not the root (`lemma_4_2_gap`). The argument after this step is correct; it shows only "if some path of `T₂`
avoids the root `ρ` of `T₁`, contradiction" (`lemma_4_2_core`).

Lemma 4.2 itself is not false: like every step of a proof by contradiction, it is stated under the assumption that
the simulation `A` exists, which Theorem 4.1 refutes, so once Theorem 4.1 is proved it holds trivially
(`lemma_4_2`). This is not a defect of the reductio; the point is that the paper gives no valid derivation of it,
and we found none from the facts available at that point. The gap example is about the inference inside the proof
(abstract decision trees with the properties of Lemmas 3.3–3.4), not a counterexample to a stated lemma; it cannot
be realized by a simulation satisfying the hypotheses, since none exists.

**Repair.** The main argument of Theorem 4.1 (writes `W₀(a) W₁(z) W₂(b)`) does not need "same root". It only needs
that `b`'s path in `T₂` reads `ρ` (with value 0, while `R₂` sees `ρ = 1`). So we split: if some path of `T₂` avoids
`ρ`, the Lemma 4.2 argument gives a contradiction (`Sec4.caseA`); otherwise every path of `T₂` reads `ρ`, and the
main argument goes through with `ρ` read at any depth instead of at the root (`Sec4.caseB`). (`theorem_4_1`,
`setting_false`)

### 🛠️ Theorem 4.1 (main part of the proof)
Two steps of the main argument need care: the first write of 1 to `x` may lie inside `W₁`, and Case 2 presumes
that `R₁` reads `x`.

**Impact.** Statement unaffected; both steps are fixed in the formal proof.

**Details.**
- (a) "The first write of 1 to `x` between the beginning of `W₁` and the end of `W₂`" may lie inside `W₁`. Then
  `R₁` returns `b` while only `a` and `z` have been written, which already violates regularity. We treat this as
  a separate case.
- (b) In Case 2, "`R₁` cannot return `b`, since `R₁` read 0 in `x`" presumes that `R₁` reads `x`. The correct
  argument: `R₁` must return `b` by regularity, so it follows `b`'s path, which reads `x` and needs `x = 1`; but
  `x = 0` at that time.
- The cases "first write of 1 to `x` before / after the first write of 0 to `r`" are exhaustive because one step
  writes one register.

### 🛠️ Lemma 3.3 and Theorem 3.2 (small gaps in Section 3)
Lemma 3.3 bounds the depth of every path of `T_i`, although the step bound only constrains paths that occur in
executions, and the last step of Theorem 3.2 forgets that the reader might write a register itself.

**Impact.** Statements unaffected; routine fixes, with a stronger form of Lemma 3.4.

**Details.**
- (a) Lemma 3.3 bounds the depth of *every* path of `T_i` by the step bound. But the bound only constrains paths
  that occur in executions, and the code may do anything on other branches. The correct argument counts the `k`
  paths realized by the executions `σ_v`: they form a prefix-free family of binary strings of length `≤ log₂ k`,
  hence are exactly all strings of length `log₂ k`.
- (b) Theorem 3.2 counts only *reads* of the simulated read, so the read may also write. The last step ("`WP`
  writes 1 to each of the `log₂ k` registers read") forgets that the reader might have written such a register
  itself. It cannot: the argument of Lemma 3.4 shows that every read accesses a register for the first time, so
  it returns the value left by the write. We prove this stronger form of Lemma 3.4.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`). Processes are deterministic and there
  are no crashes. Executions are finite label lists (`inv`/`tau`/`ret`); a `tau` step is one access to one base
  object. Wait-freedom is CSLib's `WaitFree`; only its consequence obstruction-freedom is used.
* A simulation `I : Sim V v₀ ι P L` implements a `V`-valued register with initial value `v₀` from atomic binary
  registers indexed by an arbitrary type `ι`, with arbitrary initial contents. One writer `w`; the readers are
  any processes allowed to read.
* Safe / regular / atomic (`Sim.Safe`, `Sim.Regular`, `Sim.Atomic`) must hold in every finite execution in which
  only `w` writes. Safe: a read overlapping no write returns the latest preceding write's value (or `v₀`).
  Regular: every read returns the value of an overlapping or the latest preceding write (or `v₀`). Atomic:
  linearizable (CSLib's `IsLinearization`). `Atomic → Regular → Safe` is proved.
* Costs: `Sim.accesses` lists the base accesses of an execution. `ReadReadsLE I r t` / `ReadStepsLE I r t`: every
  read operation of `r` performs at most `t` base reads / steps. `SomeWriteWritesGE I w t`: some write operation
  performs at least `t` base writes. `k = |V| = 2^m` as in the paper.
* The hypotheses are only needed for the readers named in the theorem (one reader in Section 3, two in
  Theorem 4.1) and only for their first reads, so the results are slightly stronger than the paper's.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 3.1 (some read performs `≥ ⌈log₂ k⌉` base *reads*, hence steps; any `k`) | `theorem_3_1` | `Section3.lean` |
| Lemma 3.3 (complete tree, `k` leaves at depth `log₂ k`) | `lemma_3_3` (abstract: `SeqReads.complete`) | `Section3.lean`, `ReadTree.lean` |
| Lemma 3.4 (no repeated register; fresh registers) | `lemma_3_4` (abstract: `SeqReads.fresh`, `nodup_regs`) | `Section3.lean`, `ReadTree.lean` |
| Theorem 3.2 (safe: write needs `≥ log₂ k` writes) | `theorem_3_2` | `Section3.lean` |
| Corollary 3.5 (regular) | `corollary_3_5` | `Section3.lean` |
| First read is invisible (Section 3 remark) | `all_reads`, `mem_const` | `FastTree.lean` |
| Lemma 4.2 (same root; holds once Theorem 4.1 refutes the setting) | `lemma_4_2` | `Theorem41.lean` |
| Lemma 4.2, argument of its proof | `lemma_4_2_core` (= `Sec4.caseA`) | `Theorem41.lean`, `Section4.lean` |
| Lemma 4.2, proof gap | `lemma_4_2_gap` | `Theorem41.lean` |
| Theorem 4.1 (atomic, two readers, `k > 2`) | `theorem_4_1` (core `setting_false`, `Sec4.caseB`) | `Theorem41.lean`, `Section4.lean` |
| Atomic ⇒ regular ⇒ safe | `regularHist_of_atomicHist`, `Sim.Atomic.regular`, `Sim.Regular.safe` | `Consistency.lean` |

Supporting files: `Defs.lean` (model), `Kraft.lean` (prefix-free strings), `ReadTree.lean` (solo runs, lockstep,
`SeqReads`), `Bridge.lean` (CSLib executions ↔ local solo runs), `FastTree.lean` (decision tree of a read with
`log₂ k` steps), `Exec4.lean`, `Section4Exec.lean` (executions with inserted reads), `LinFacts.lean` (reads in a
linearization, no new–old inversion).

**Not formalized.** The tightness claims (algorithms of [4], [6], [5]) and the closing remark that one reader
suffices if its first two reads start with the same register.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity (`Examples.lean`): for `k = 2` the trivial simulation (one base register, CSLib `atomicImpl`) is
wait-free and atomic, and every read takes one step. So it satisfies all hypotheses of Section 3
(`trivialSim_hyps`), and the assumption `k > 2` of Theorem 4.1 is necessary (`theorem_4_1_needs_k_gt_two`).

CSLib candidates (`-- CSLib candidate` in the files): `resp_of_split`, `lt_of_split`, `resp_reads`
(`Consistency.lean`, no new–old inversion in any linearization where one process changes the state) and the
prefix-free counting lemmas of `Kraft.lean`.
