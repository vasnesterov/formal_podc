# Space Complexity of Timestamps — PODC 2011

Maryam Helmi, Lisa Higham, Eduardo Pacheco, Philipp Woelfel. *The space complexity of long-lived and
one-shot timestamp implementations.* PODC 2011. DOI
[10.1145/1993806.1993826](https://doi.org/10.1145/1993806.1993826). Formalized version: arXiv
[1103.5794](https://arxiv.org/abs/1103.5794) v2 (full version, matches the PODC results; numbering
follows it).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Hard fix.** All stated results hold: Theorems 1.1 (`n/6 - 1`, long-lived), 1.2 (`√(2n) - log n - O(1)`,
one-shot) and 1.3 (`2⌈√n⌉` registers). The proof of Theorem 1.2 does not go through as written (final counting,
empty-prefix case) and needed new inductive invariants; the gap in Lemma 6.5 (last phase) closes locally. The lower
bounds were checked for deterministic (obstruction-free) implementations only.

## Mistakes in the paper

### 🔧 Theorem 1.2 (proof: "every register in `R_last` is covered")
The claim that every register in `R_last` is covered by at least one process may fail, since the threshold `ℓ - j` can
be `≤ 0` in the last step.

**Impact.** The claim is not needed: only `|R_last| ≤ #registers` is used, and the Lean proof drops it (`theorem_1_2`).

### ✏️ Slips
- Lemma 3.1 is stated for every quiescent `D` but needs `D` reachable; its only use has `D` reachable (`lemma_3_1`).
- Section 2's definition of covering ("there is a non-deterministic decision such that") lets one process cover
  several registers, which would break the signature counting; the paper fixes the decisions in its lower bound proofs,
  and then a process covers at most one register (`Impl.Covers.unique`).
- Section 4: "`idle(Cᵢ) < idle(Cᵢ₊₁)`" should be `>`.
- Algorithm 2's comment: "processes `2i` and `2i+1`" should be `2i-1, 2i`, as in its code.

### Typos
- Proof of Lemma 3.2: "`πBᵢλπB₁₋ᵢπBⱼη`" should be `πB₂`.

## Proof gaps (statements true)

### 🛠️ Theorem 1.2 (final counting)
The step "`|idle(C_last)| ≤ 1` is impossible" needs every `Cᵢ` to be `ℓᵢ`-constrained, which the proof
never establishes, and its association argument is inexact.

**Impact.** The stated invariant cannot deliver the count; a new inductive invariant does (`Inv.nbound`, `idle_ge_two`).

**Details.**
- Being `ℓᵢ`-constrained is not part of the stated construction invariant (a)–(e), and it is never proved
  for the columns already in `Rᵢ`.
- The association argument `g(r) = |poised(C_{f(r)}, {r})|` is also inexact: after its block write, a
  block-writer may cover another register, and then it is associated with a register it did not cover at
  time `f(r)`.

**Repair.** We replace both with an inductive invariant: the number of non-idle processes that cover
nothing outside `R` is at most `Σ_{c≤j}(m - c)`. Together with sparsity (next item), it gives
`n - |idle| ≤ m(m-1)/2 ≤ n - 2`. (`Inv.nbound`, `idle_ge_two`)

### 🛠️ Theorem 1.2 (empty prefix after Case 2)
The bound `|poised(C_{k+1}, Q)| ≤ Σ(ℓ_k - c - 1) + 1` comes from the minimality of the prefix `γ_{k+1}`,
but after a Case-2 step `γ_{k+2}` may be empty, and then minimality gives nothing.

**Impact.** Invariant (c) of the proof is not established; a sparsity invariant replaces minimality (`Inv.sparse`,
`step`).

**Details.** A Case-2 step lowers `ℓ`, so the next configuration may already contain a full column set
w.r.t. the new `ℓ`.

**Repair.** We use sparsity w.r.t. the *previous* diagonal (no nonempty `S ⊆ R̄` has all counts
`≥ ℓ + 1 - j - |S|`), which is preserved in both cases. (`Inv.sparse`, `step`)

### 🔧 Theorem 1.2 (Case-2 count, log term)
The proof claims each Case-2 step moves at least `⌈|idle|/2⌉` idle processes, but only `⌊|idle|/2⌋` are
guaranteed to move.

**Impact.** The proof gives `⌊√(2n)⌋ - ⌈log₂ n⌉ - 2` instead of `⌊√(2n)⌋ - log n - 2`; the O(1)
form of the theorem is unaffected (`theorem_1_2`, `theorem_1_2_real`).

**Details.** `γ_{k+1}` may cut `σ'`, so only the `≥ ⌊|idle|/2⌋` processes of `σ` are guaranteed to move.
Case 2 then occurs up to `⌈log₂ n⌉` times (e.g. idle sizes 5 → 3 → 2 → 1).

### 🔧 Theorem 1.2 (counting equality in the step)
The equality `|poised(C_k, R̄_k)| + |idle(C_k)| = |poised(γ(C_k), R̄_k)| + |idle(γ(C_k))|` is false, because
block-writers may cover registers outside `R_k` after their write.

**Impact.** Only `≤` holds, which is the direction needed (`Inv.nbound`, `step`).

### 🔧 Lemma 6.5 (space of Algorithm 4, last phase)
"`Σ_{ϕ=1}^{Φ} ϕ ≤ 2M`" treats the last phase as complete, but Claim 6.10 applies only to completed phases,
so the paper's claims give only `⌈2√M⌉ + 1` registers.

**Impact.** The bound `⌈2√M⌉` is nevertheless true (`sq_le_of_written`, `alg4_space`).

**Repair.** The getTS that starts a phase never spends its "first invalidation" credit, so
`#invalidations + Φ ≤ 2M`, which gives `K² + K + 2 ≤ 4M` for every written index `K`.
(`sq_le_of_written`, `alg4_space`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Proof remarks.** The proof of Lemma 3.2 uses without justification that the first two block writes commute once
`B₂` has written; this holds because `πB₂` overwrites both (`blockWrite_swap`).

**Model.**
* Asynchronous shared memory: CSLib `Cslib.SharedMemory.Impl`; invocation, internal steps and
  responses are separate labels.
* **The lower bounds are proved for deterministic implementations only**, i.e. for
  obstruction-freedom on admissible executions (`SoloTerm`). The paper's Theorems 1.1 and 1.2
  claim the bounds for non-deterministic solo-termination. The nondeterministic case reduces to the
  deterministic one with the same registers: before each step, read all `m` registers, then take
  the choice with the shortest solo-termination distance. This reduction is not formalized.
* Timestamp object `tsObj T` over an *arbitrary* universe `T`, with `getTS` and `compare`; `compare`
  may access memory. `TSCorrect α` says:
  - every completed `getTS` returns a timestamp;
  - if `g₁` happened before `g₂`, then any `compare(t₁,t₂)` invoked after `g₂` returned answers
    `true`, and any such `compare(t₂,t₁)` answers `false`.
* `IsTS I oneShot`: all operations allowed; correctness and solo termination on all executions
  (long-lived) or on executions where each process calls `getTS` at most once (one-shot; `compare`
  unrestricted).
* Lower bounds: finitely many base objects, each read/write-like (`RWLike`: every primitive is
  read-only or a blind overwrite). This covers registers of arbitrary, even unbounded, value types.
  `n = Fintype.card P` processes, `m = Fintype.card ι` objects.
* Upper bound (Algorithm 4): the memory is one base object holding an unbounded array of
  registers, with `read i`, `write i v` and an **atomic** `scan`, exactly as the paper treats scan
  ("we treat it as atomic"). The space claim says every accessed index is in `[1, ⌈2√M⌉]`. The
  double-collect implementation of the scan is not verified.
* Algorithm 2 uses `⌈n/2⌉` CSLib registers over `ℕ` (`Fin ((n+1)/2)`), with process `p` (0-based)
  writing register `p/2`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 (Ellen–Fatourou–Ruppert) | `lemma_2_1` | `EFR.lean` |
| Lemma 3.1, Lemma 3.2 | `lemma_3_1`, `lemma_3_2` | `LongLived.lean` |
| Theorem 1.1: `m ≥ n/6 - 1` (long-lived) | `theorem_1_1` (`⌊n/2⌋ ≤ 3m`), `theorem_1_1_real` | `LongLived.lean` |
| Lemma 4.1 | `lemma_4_1` | `Lemma41.lean` |
| Theorem 1.2: `m ≥ √(2n) - log n - O(1)` (one-shot, `n ≥ 3`) | `theorem_1_2` (`⌊√(2n)⌋ ≤ m + ⌈log₂ n⌉ + 2`), `theorem_1_2_real` (`m > √(2n) - log₂ n - 4`) | `OneShotMain.lean` |
| Lemma 5.1 (Algs. 1–2, `⌈n/2⌉` registers, wait-free one-shot) | `SimpleTS.lemma_5_1` | `SimpleAlgCorrect.lean` |
| Lemma 6.4 (Algs. 3–4 correct; for every execution) | `Alg4.alg4_correct` | `Alg4Correct.lean` |
| Lemma 6.5 (indices `≤ ⌈2√M⌉` with `≤ M` getTS calls) | `Alg4.alg4_space`, `Alg4.alg4_written_lt` | `Alg4Space.lean` |
| Lemma 6.14 (wait-free with `≤ M` getTS calls) | `Alg4.alg4_waitFreeUpTo` | `Alg4WaitFree.lean` |
| Theorem 1.3 (wait-free one-shot, indices in `[1, ⌈2√n⌉] ⊆ [1, 2⌈√n⌉]`) | `Alg4.theorem_1_3` | `Alg4Main.lean` |

**Not formalized.** The double-collect scan of Algorithm 4 (only the atomic scan the paper's
proofs assume). The historyless-object version of Theorem 1.2 (Section 7), and
nondeterministic or randomized algorithms: Theorems 1.1 and 1.2 for genuinely non-deterministic processes rest on the
reduction sketched under **Model**.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The hypotheses of both lower bounds are satisfiable for every `n`:
* Theorem 1.1: the folklore "max + 1" algorithm (`n` registers) is a wait-free long-lived `IsTS`
  implementation from registers (`MaxTS.maxTS_isTS`, `MaxTS.maxTS_rwLike`; `MaxAlg.lean`).
* Theorem 1.2: Algorithm 2 is a one-shot one (`SimpleTS.lemma_5_1`).

The model is CSLib's `SharedMemory` (`Model`, `Covering`, `Progress`). From the shared library
`Cslib/Computability/Distributed/SharedMemory/`: `SoloTerm` is `Impl.ObstructionFreeOn (Adm oneShot)` and `WaitFreeUpTo` is
`Impl.WaitFreeOn` (`Progress`, with `soloTerm_iff`, `waitFreeUpTo_iff`); `RWLike`
(`ObjClasses`); covering and block-write lemmas (`Impl.Covers.congr`, `Impl.Covers.unique`,
`Impl.blockWrite_swap`, `Covering`); solo runs under restricted obstruction-freedom
(`Impl.soloOp_spec_of_obstructionFreeOn`, `Impl.exists_finish`, `Solo`); potentials
(`Impl.waitFreeOn_of_cfgPotential`, `Impl.waitFree_of_potential`, `Potential`); and the computable
step function used to evaluate the long-lived counterexample (`Impl.crun`, `Compute`); the effect of
one appended label on operations and responses (`opOf_concat_of_ne`, `respOf_concat_of_ne`,
`respsOf_concat_of_ne`, `Completed.of_respOf_eq_some`, `Invoked.of_opOf_eq_some`, `History`).
