# History-Independent Concurrent Objects

Hagit Attiya, Michael A. Bender, Martín Farach-Colton, Rotem Oshman, Noa Schiller.
*History-Independent Concurrent Objects.* PODC 2024, pp. 14–24.
DOI [10.1145/3662158.3662814](https://doi.org/10.1145/3662158.3662814),
arXiv [2403.14445](https://arxiv.org/abs/2403.14445) (v1; the local PDF is the arXiv version with appendices).

## Model

Asynchronous shared memory, built in `Podc/SharedMemory/`, now CSLib `Cslib/Computability/Distributed/SharedMemory/` (namespace `Cslib.SharedMemory`):

* `n` processes (any type `P` with decidable equality; the results need two distinct processes),
  deterministic programs, crash-free asynchrony (any interleaving; infinite executions for progress).
* Base objects `B i` (`i : ι`) with deterministic sequential specifications, accessed atomically, one
  access per step; returning a response is a separate step without memory access.
* An implementation fixes initial memory, local programs and an access discipline (`allowed`).
* Linearizability with explicit operation identities; linearization functions (Def. 4).
* Wait-free / lock-free / obstruction-free as conditions on infinite / solo executions.
* History independence w.r.t. a set of executions (Def. 4), perfect / state-quiescent / quiescent HI
  (Defs. 5, 7, 8). Deterministic implementations only (as in the paper).

## Main results ↔ Lean

| Paper | Lean | File | Status |
|---|---|---|---|
| Defs. 4, 5, 7, 8 | `Impl.HIwrt`, `PerfectHI`, `StateQuiescentHI`, `QuiescentHI` | `Cslib/Computability/Distributed/SharedMemory/Model.lean` | defs |
| Prop. 6 | `prop6` | `Perfect.lean` | proved |
| Def. 13 (class `C_t`) | `ClassC` | `ClassC.lean` | def |
| Prop. 14 | `prop14` (for `t ≥ 2`) | `Perfect.lean` | proved |
| Lemmas 15, 16 (+ 37, 38) | `Good.ret_resp`, `Good.extend`, `Good.init` | `Avoidance.lean` | proved (gap `q_k = q_{k+1}` fixed) |
| Thm. 17 | `thm17` (via `not_waitFree_stateQuiescentHI`) | `ClassC.lean`, `Avoidance.lean` | proved |
| Cor. 18 | `cor18` | `ClassC.lean` | proved |
| Prop. 19 | `prop19` | `Prop19.lean` | proved |
| Thm. 20 (queue with Peek) | `thm20` (for `t ≥ 1`) | `Queue.lean` | proved |
| Thm. 9 (Alg. 2) | `Alg2.theorem9` (`linearizable`, `lockFree`, `stateQuiescentHI`), any `K ≥ 1` | `Alg2.lean` | proved |
| SWSR linearizability via reads-from (App. A construction) | `SWSRReadsFrom.isLinearization` | `Cslib/Computability/Distributed/SharedMemory/SWSRRegister.lean` | proved |
| — (Alg. 2 + Cor. 18) | `alg2_not_waitFree` | `Consistency.lean` | proved |
| Thm. 12 (Alg. 4) | `Alg4.theorem12` (linearizable, wait-free, quiescent HI; HI for *every* linearization function: `quiescentHI_any`) | `Alg4Thm.lean` (+ `Alg4*.lean`) | proved |
| Lemmas 10, 11, 34 | `Alg4.lemma10`, `lemma11`, `lemma34` (weak form suffices) | `Alg4Thm.lean` | proved |
| Lemmas 35, 36 | forward invariants (`bprot`, `mem_quiescent`) | `Alg4Inv.lean`, `Alg4Thm.lean` | proved |
| — (Alg. 4 + Prop. 19) | `alg4_reader_writes` | `Consistency.lean` | proved |
| R-LLSC object (§6.1) | `rllsc` | `UniversalRLLSC.lean` | def |
| Alg. 5 over atomic R-LLSC; Invariants 21–22, Lemmas 23–27 | `Universal.alg5`, `inv_run`, `isLinFun`, `linState_hlin`, `mem_eq_canon`, `stateQuiescentHI` | `Universal*.lean` | proved |
| Alg. 5 wait-free (atomic R-LLSC) | `Universal.waitFree`, `Universal.alg5_main` | `UniversalWF.lean` | proved |
| "without the RL lines Alg. 5 is not quiescent HI" (§6.1) | `alg5NoRL_not_quiescentHI` | `UniversalExample.lean` | proved |
| Thm. 28 (Alg. 6: R-LLSC from CAS), Lemmas 29, 30, 40 | `RLLSCFromCAS.linearizable`, `perfectHI`, `lockFree` (finite `P`), `lemma29`, `lemma30` | `UniversalCAS.lean` | proved |
| Thm. 32 (Alg. 5 with Alg. 6 inlined, from CAS) | `Universal.theorem32` (linearizable ∧ wait-free ∧ state-quiescent HI), `flat_mem_eq_canon` | `UniversalFlat.lean`, `UniversalFlatWF.lean` | proved for **one deterministic `∥` schedule (strict alternation), flattened** — not for every interleaving, not compositionally |
| — (implicit `n ≥ 2`) | `prop14_needs_two_processes` | `OneProcess.lean` | proved |
| — (non-vacuity, tightness) | `register_tight`, `Atomic.perfectHI`, `Atomic.waitFree` | `Sanity.lean`, `Cslib/Computability/Distributed/SharedMemory/Atomic.lean` | proved |

## Status

**Complete: every result of the paper is formalized and proved; no `sorry`, no axioms** beyond
`propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms` / `lean_verify` for all
theorems in the table).

**Caveat — Theorem 32:** proved only for one deterministic resolution of each `∥` (strict
alternation) of the flattened Alg. 5 + Alg. 6, not for every interleaving and not compositionally
(Lemma 25 + Thm. 28 + Lemma 27). It captures the existence claim; linearizability/HI are plausibly
interleaving-independent, so the restriction matters essentially for wait-freedom.

Findings (details in `differencies.md`): no result is wrong. Genuine (minor) gaps: Lemma 16 misses
`q_k = q_{k+1}` (`ochange(q,q)` undefined; fixed by an empty move); Prop. 14's "solo `oread` from the
same memory returns the same response" needs identical local state (a second, fresh process);
Theorem 32's proof applies Theorem 28 to non-well-formed per-object histories (abandoned `LL`s; rigor
gap, easily patched); Lemma 41 omits the `RL` of line 18R.2. Not errors: the reader-returns case of
Lemma 16 (artifact of our model), the implicit `n ≥ 2` scope (counterexample
`prop14_needs_two_processes`), Lemma 15's footnote 4 (avoided); the `n` vs `n+1` helping bound is
unclear/immaterial. Typos (`∉ R` for `∈ R` in lines 6R.1/18R.1, `o_change`/`o_read`,
`X_i`/`R_i`, `α`/`β`, `t`/`t+1`, Lemma 16/38, line numbers in Thm. 12).

## CSLib candidates

The shared-memory framework (`Spec`, `History`, `Model`, `Linearization`, `Progress`, `Indist`, `LinPoints`, `Atomic`,
`SWSRRegister`) has been migrated to CSLib (`Cslib/Computability/Distributed/SharedMemory/`). Remaining: the general
avoidance lower bound (`AvoidData`, `not_waitFree_stateQuiescentHI`);
the R-LLSC object and Alg. 6 (`UniversalRLLSC.lean`, `UniversalCAS.lean`); `Impl.waitFree_of_potential` (`Alg4WaitFree.lean`:
bounded own steps ⇒ wait-free).

## Token spend

≈ 2.9M tokens in total: paper agent ≈ 0.5M (framework, impossibility results, integration);
subagents: Alg. 2 + SWSR criterion ≈ 0.27M, Alg. 4 ≈ 0.48M, universal construction ≈ 1.65M
(incl. a helper for Alg. 6).
