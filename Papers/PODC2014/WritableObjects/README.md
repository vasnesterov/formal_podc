# Making Objects Writable — PODC 2014

Zahra Aghazadeh, Wojciech Golab, Philipp Woelfel. *Making Objects Writable.* PODC 2014. DOI
[10.1145/2611462.2611483](https://doi.org/10.1145/2611462.2611483). Formalized version: Chapter 4 of Z. Aghazadeh's
PhD thesis *Efficient Shared Memory Algorithms for Bounding Space* (U. Calgary, 2018), which contains the paper
with full proofs; numbering follows the thesis (the PODC version is not openly available).

**Verdict: 🛠️ Hard fix.** All checked statements hold: the template lemma (Lemma 4.5), the correctness of the
wait-free algorithm (Lemma 4.8, hence the linearizability part of Theorem 4.1 and of Corollary 4.4) and the
sequentially resettable `(k,b)`-array (Lemma 4.2). The proof of Lemma 4.5 has a genuine gap: it never uses the
template's "not in use" requirement, without which the lemma is false, and it took a new construction of the
linearization to save it; the proof of Lemma 4.8 has smaller gaps. The wait-freedom and complexity claims of
Theorem 4.1 were not checked.

## Mistakes in the paper

### ✏️ Slips
- Claims 4.15(b) and 4.16 (inside the proof of Lemma 4.8) are literally false at the level of single points, because
  within one `recycle()` line 26 can add `i*` to `free_p` at the same point at which lines 27–28 read `i*` from `Annc`
  and enqueue it (the mechanism is checked on the local queue state by an `example` in `Lemma48.lean`; no full
  execution was built). Their uses (Claims 4.17, 4.21–4.22) keep one `recycle()` call of margin.

### Typos
- Lemma 4.2, proof of Part (b1): "`[t_W@rsp, t_R@inv] = [t_W@64, t_R@60]`" and "q reads `(x_W, v_W)` from `A[i*]` in
  line 60" should say line 59; "when p reads this variable in line 60 of R" should say q.
- Lemma 4.8, proof of (4.32): "q completes" should be "p completes".
- Lemma 4.2 needs `k ≥ 1` (the version counter is taken `mod k`); implicit.

## Proof gaps (statements true)

### 🛠️ Lemma 4.5 (template lemma, proof of Claim 4.7)
The proof obtains a linearization of the sub-history `Λ_ℓ` of the timestamp-`ℓ` calls from sequential writability, an
inference that fails without the template's "not in use" requirement, which the proof never uses
(`notInUse_necessary`, `lambda1_not_linearizable`).

**Impact.** Statement true; repaired with a different construction of the linearization (`lemma_4_5`).

**Details.** The step reads: "no `A[i_ℓ].SWrite()` overlaps any other operation call on `A[i_ℓ]`. Therefore,
there is a linearization `S_ℓ` of `Λ_ℓ`". But a sub-history of a linearizable history need not be linearizable,
and without "not in use" Lemma 4.5 itself is false. Counterexample to the step (all other hypotheses of Lemma 4.5 hold): a register over `ℕ`, three
processes. `p₀` writes `1` with index `0`; then `p₀` starts `Write(2)` *reusing index `0` while `Ptr = 0`* and
completes `A[0].SWrite(2)`; `p₂`'s `Exec(read)` sees `Ptr = 0`, reads `2`; `p₁` writes `3` with index `1` and
returns; `p₀` sets `Ptr := 0` and returns; `p₂` reads `2` again. Condition (C), ownership and sequential
writability hold, but the high-level history is not linearizable: the first read forces `Write(2)` before it,
real time puts `Write(3)` between the two reads, so the second read must return `3`. Here
`Λ_1 = {A[0].SWrite(1), read → 2}` has no overlapping `SWrite` and is not linearizable, while the whole history
of `A[0]` is.

**Repair.** Take one linearization `L_i` of the *whole* history of each `A[i]`. Using "not in use", show that on
each `A[i]` an operation of a call with a smaller timestamp returns before any operation of a call with a larger
timestamp is invoked (`IsCtrl.ret_before_of_keyPos_lt`), so the timestamps are sorted along `L_i`; each
timestamp-`ℓ` block is then a contiguous segment of `L_{i_ℓ}` starting with its `SWrite`, and its legality
follows from that of `L_{i_ℓ}`. The high-level linearization lists these blocks by increasing timestamp
(`linWT`, `IsCtrl.isLinearization_linWT`).

### 🔧 Theorem 4.1 (the algorithm follows the template)
Lemma 4.5 requires that the write-index of a `Write` is not in use when chosen, but this is never proved for the
algorithm of Figure 4.5; the proof of Theorem 4.1 only establishes condition (C) (Lemma 4.8).

**Impact.** Statement true; it follows quickly from Claim 4.22(a) (a `Write` contains only one `recycle()`),
and is proved as part of our invariant (`WF.lemma_4_8`, which gives `Template ∧ CondC`).

### 🔧 Lemma 4.8 (the algorithm satisfies (C)), proof of (4.32)
The count "p invokes more than `n` `Write()` calls during `[t_E@36, t_E@39]`, and so q completes at least `n`
`Write()` calls during this interval" may include a `Write` invoked before `t_E@35`, to which Claim 4.20 (stated
for `Write`s completing during `(t_E@35, t_E@40]`) does not apply as stated.

**Impact.** Statement true; only line 14 of that `Write` (its read of `S_q`) needs to come after `t_E@35`, which
holds (`WF.lemma_4_8`).

**Details.** Claim 4.19's "both writes happen in the same `Write`" is asserted without argument; it is true.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, any set of processes, deterministic algorithms, no failures other than processes
  stopping (pending operations), linearizability in CSLib's sense (`IsLinearization`, the amended
  Herlihy–Wing definition).
- Lemma 4.5 is stated on **transcripts** (`Ev`): the high-level invocations/responses of `Write`/`Exec`, the
  invocations/responses of operations on the base objects `A[i]`, and the writes to `Ptr`. The base objects are
  *not* atomic; the hypothesis "`A[i]` is sequentially writable" is the hypothesis that the history `lowH i α`
  of each `A[i]` is linearizable whenever no write overlaps another operation on it (`SeqWritable`). Template
  (`Template`): a per-process control automaton (`PStep`) for Figure 4.4, ownership of indices, and "not in use"
  at the invocation of `SWrite` (implied by the paper's "at the invocation of `Write`",
  `notInUse_of_atWriteInv`). Condition (C): `CondC`.
- The algorithm of Figure 4.5 (`WF.Step`, `Algorithm.lean`) is a nondeterministic transition system for `n ≥ 1`
  processes: one atomic register access per step (local lines attached as on p. 58–59 of the thesis), indices
  `Fin n × Fin (8n+9)` owned by their first component, `free_p.remove()` arbitrary, the objects `A[i]` black
  boxes whose invocation and response are separate steps with *arbitrary* responses (their correctness is the
  `SeqWritable` hypothesis), environment-chosen invocations, ghost variables that no guard reads. Executions
  (`WF.IsExecution`) start with the solo `Write(v₀)` of process 0, as in the paper; the high-level history
  includes that `Write`.
- Lemma 4.2 and Figure 4.2 use CSLib's `Impl` model with atomic registers as base objects.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 4.5 (template + (C) ⇒ linearizable) | `lemma_4_5` | `Lemma45.lean` |
| (4.1): no `SWrite` overlaps another operation on `A[i]` | `IsCtrl.writesIsolated` | `HighLow.lean` |
| "not in use" is needed (gap in Claim 4.7) | `Counterexample.notInUse_necessary`, `Counterexample.lambda1_not_linearizable` | `Counterexample.lean` |
| Lemma 4.2 (sequentially resettable `(k,b)`-array, Fig. 4.15) | `lemma_4_2`, `card_baseObjects`, `stepBound_invoke`, `stepBound_access` | `ResettableArray.lean` |
| Fig. 4.2: `k`-word register is sequentially writable | `kWord_seqWritable` | `KWordRegister.lean` |
| Lemma 4.8 (+ template conditions, incl. "not in use") for Fig. 4.5 | `WF.lemma_4_8`, `WF.lemma_4_8_exec` | `Lemma48.lean` |
| Theorem 4.1 (linearizability of the transformation) | `WF.theorem_4_1` | `Theorem41.lean` |
| Corollary 4.4 (linearizable `k`-word register) | `WF.corollary_4_4`, `template_kWord_linearizable` | `Theorem41.lean`, `Cor44.lean` |

**Not formalized.** The complexity parts of Theorem 4.1 and Corollary 4.4 (constant additive step overhead,
register sizes `2 log n + O(1)`, wait-freedom; they look right by inspection of `WF.Step`, but we did not examine
them, and Claim 4.14 — `free_p` is never empty — is not proved), Corollary 4.3 and the applications of Sections 4.1.2–4.1.3.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `Counterexample.lemma_4_5_nonvacuous` (a concurrent transcript satisfying all hypotheses of
Lemma 4.5), `WF.exists_initialized` (the initial `Write(v₀)` is an execution of the model), `WF.ptr_ne_none`,
`resetsIsolated_of_no_reset`. CSLib modules used: `SharedMemory.{History, Linearization, LinPoints,
Model}`. CSLib candidates: `Proj.lean` (histories of projected event lists, real time by positions),
`TauFree.lean` (dropping internal steps), the list lemmas in `ListAux.lean`.
