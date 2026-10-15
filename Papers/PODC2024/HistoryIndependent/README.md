# History-Independent Concurrent Objects — PODC 2024

Hagit Attiya, Michael A. Bender, Martín Farach-Colton, Rotem Oshman, Noa Schiller. *History-Independent Concurrent
Objects.* PODC 2024, pp. 14–24. DOI [10.1145/3662158.3662814](https://doi.org/10.1145/3662158.3662814). Formalized
version: arXiv:2403.14445v1 (with appendices).

**Verdict: ⚠️ Correct with fixes.** Every result of the paper is formalized and proved:
- the impossibilities (Props. 6, 14, 19, Thm. 17, Cor. 18, Thm. 20);
- Algorithms 2 and 4 (Theorems 9, 12);
- the universal construction (Algorithms 5, 6, Theorems 28, 32).

No statement is wrong within the paper's intended scope. The impossibilities silently need at least two processes.
Lemma 16 and the proof of Prop. 14 have small gaps, and the proof of Theorem 32 has a rigor gap. **Our Theorem 32
covers one fixed resolution of the `∥` interleavings**, not all of them.

## Mistakes in the paper

- **The impossibility results need `n ≥ 2` (implicit scope, not an error).** Props. 6, 14, 19, Thm. 17, Cor. 18 and
  Thm. 20 all fail with a single process. That process can keep the abstract state locally and leave shared memory
  constant, which is wait-free and perfectly history independent. Example: a 3-valued register with no base objects
  at all. We assume a reader and a changer `c ≠ r` with suitable access rights. (`prop14_needs_two_processes`)
- **Lemma 16: the case `q_k = q_{k+1}` is not handled (proof gap, morally trivial).** The construction may pick the
  same state twice in a row. Definition 13 provides `o_change(q, q')` only for `q ≠ q'`, so the changer's step is
  undefined. Fix: the changer does nothing in that round. (`thm17`)
- **Prop. 14: "a solo `o_read` from the same memory returns the same response" needs the same local state (proof
  gap).** With the same reader process the claim can fail, because its local state may differ between the two
  executions. We use a second process that has taken no steps.
- **Theorem 32: Theorem 28 is applied outside its hypothesis (rigor gap).** In Algorithm 5 the right side of `∥`
  (lines 6R, 18R, 25R) can jump away while the left-side `LL` is still pending. The per-object history seen by the
  R-LLSC implementation then has two pending operations of one process on one object, so it is not well-formed,
  whereas Theorem 28 (Algorithm 6 is linearizable) is proved only for well-formed histories. The gap is easily
  patched, since an abandoned `LL` never takes effect. Relatedly, Lemma 41 only discusses the `RL` of line 22. The
  `RL` of line 18R.2 can also run while the process is still in the context of `announce[j]` from an earlier
  iteration, and it needs the same argument.
- **Unclear count (immaterial).** In the proof of Theorem 32, "after at most `n` mode transitions" may need `n + 1`.
  Two readings disagree, and our proof uses its own potential function.
- **Statements stronger than claimed.** Prop. 14 holds for `t ≥ 2` (the paper says `t ≥ 3`). Theorem 20 holds for
  `t ≥ 1` (the paper says `t ≥ 2`). The footnote-4 assumption of Lemma 15 ("no unused values") is unnecessary.
- **Typos.**
  - Lines 6R.1 and 18R.1 read "wait until `Load(announce[i]) ∉ R`"; it must be `∈ R`.
  - `o_change` for `o_read` in Prop. 14; `X_i` for `R_i` in Thm. 17; `α′` for `β` in Prop. 6.
  - "`t` executions" for `t + 1` in Lemma 38. Theorem 20's proof cites Lemma 16 for Lemma 38.
  - Wrong line numbers in Theorem 12. `W` for `W₂` in Lemma 10.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** Asynchronous shared memory, CSLib's `Cslib.SharedMemory`.
- Processes of any type with decidable equality, deterministic programs, and no crashes. Any interleaving is
  allowed; progress is defined on infinite executions.
- Base objects have deterministic sequential specifications. Each step makes one atomic access; returning is a
  separate step with no memory access.
- An implementation fixes initial memory, local programs, and an access discipline (e.g. SWSR registers).
- Linearizability is the standard definition with explicit operation identities. CSLib's notion is proved
  equivalent to Herlihy–Wing's amended definition in the PODC 2021 *Linearizability: A Typo* formalization.
- Wait-, lock- and obstruction-freedom are conditions on infinite or solo executions.
- History independence follows Def. 4: there is a linearization function such that executions in a given class
  with equal abstract states have equal memory. Perfect, state-quiescent and quiescent HI are Defs. 5, 7, 8.
- Theorem 32 is proved for the flattened algorithm: Algorithm 5 with every R-LLSC operation replaced by the
  Algorithm 6 code over CAS. Each `∥` is resolved by strict alternation. Linearizability and HI are plausibly
  independent of the interleaving, so the restriction matters mainly for wait-freedom.

**Main results in Lean** (namespace `Cslib.SharedMemory`).

| Paper | Lean | File |
|---|---|---|
| Props. 6, 14 | `prop6`, `prop14` | `Perfect.lean` |
| Thm. 17, Cor. 18 (Lemmas 15–16 via a general avoidance bound) | `thm17`, `cor18`, `not_waitFree_stateQuiescentHI` | `ClassC.lean`, `Avoidance.lean` |
| Prop. 19 (the reader must write) | `prop19` | `Prop19.lean` |
| Thm. 20 (queue with Peek) | `thm20` | `Queue.lean` |
| **Thm. 9** (Alg. 2: linearizable, lock-free, state-quiescent HI) | `Alg2.theorem9` | `Alg2.lean` |
| **Thm. 12** (Alg. 4: wait-free, quiescent HI), Lemmas 10, 11, 34 | `Alg4.theorem12`, `Alg4.lemma10`, `Alg4.lemma11` | `Alg4Thm.lean` |
| Alg. 5 over atomic R-LLSC (wait-free, state-quiescent HI) | `Universal.alg5_main` | `UniversalWF.lean` |
| §6.1: without the RL lines, Alg. 5 is not quiescent HI | `alg5NoRL_not_quiescentHI` | `UniversalExample.lean` |
| **Thm. 28** (Alg. 6: R-LLSC from CAS), Lemmas 29, 30 | `RLLSCFromCAS.linearizable`, `RLLSCFromCAS.perfectHI`, `RLLSCFromCAS.lockFree` | `UniversalCAS.lean` |
| **Thm. 32** (flattened, one `∥` schedule) | `Universal.theorem32` | `UniversalFlatWF.lean` |
| (new) consequences, tightness, `n ≥ 2` needed | `alg2_not_waitFree`, `alg4_reader_writes`, `register_tight`, `prop14_needs_two_processes` | `Consistency.lean`, `Sanity.lean`, `OneProcess.lean` |

**Not formalized.** A compositional proof of Theorem 32 (Lemma 25 + Theorem 28 + Lemma 27) covering every
interleaving of `∥`.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `register_tight` gives a wait-free, perfectly HI register, and the algorithms themselves are concrete
instances of the definitions. The shared-memory model (histories, linearizability, progress, HI, the SWSR
reads-from criterion) is in CSLib, `Cslib/Computability/Distributed/SharedMemory/`.
