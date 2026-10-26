# Space Complexity of Scannable Binary Objects — PODC 2021

Sean Ovens. *The Space Complexity of Scannable Binary Objects.* PODC 2021. DOI
[10.1145/3465084.3467916](https://doi.org/10.1145/3465084.3467916). Formalized version: the proceedings
version (no arXiv full version exists); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The lower bounds proved in the body hold (Lemmas 5–6, Theorem 8,
Corollary 9), and so does the Section 4.1 upper bound. Two statements fail in edge cases. Observation 3 is
false when the start configuration is not `p₀`-idle. The headline bound "`n + k − 2` for `n ≤ 2^(k−1)+2`"
in the abstract, introduction and conclusion fails for `k = 1`, `n = 3`, and some cases of it are unproved.

## Mistakes in the paper

* **Observation 3 is false when the start configuration is not `p₀`-idle** (false only in a degenerate
  case). If `p₀` has a pending `Update` that has not taken a step, a scanner's solo `Scan` may be
  linearized before that update and return the old value `V`. Yet the execution is `V`-absent, because
  the only `p₀`-idle configuration reached during `αα'` is the one after the update. The paper applies
  Observation 3 only from `C₀α_j`, which is `p₀`-idle, so the proofs are unaffected. We prove the
  correct version: a scan returns the value after some number of `p₀`'s operations that is at least
  the number of operations completed before the scan was invoked (`scan_resp`). The counterexample to
the statement as written is given in prose only, not in Lean.
* **The abstract overstates the range of the `n + k − 2` bound** ("when `n ≤ 2^(k−1) + 2`"). The body
  assumes `k ≥ 3` and `n > 2`, and the claim fails without them. For `k = 1` a single 1-bit object
  suffices for every `n`, because the atomic implementation works and the component is itself a 1-bit
  object. So the claimed bound of 2 for `n = 3` is false, and Lemma 6's `k ≥ 2` is needed
  (`abstract_bound_fails_k1`). For `n = 1` no shared object is needed at all, yet the claim gives `k − 1`.
  For `k = 2`, `n = 4` the abstract claims 4 objects, but the paper proves only 3 (Lemma 6). Theorem 8
  needs `k ≥ 3`, so this case is unproved; we do not know whether it holds. Similarly, the introduction
  states the `n + k − r − 2` range without Theorem 8's condition `k ≥ r + 3`.
* **Small gaps, true statements.** Corollary 9 (c) for `n > 2^k − 2` is asserted ("also applies to
  larger values of `n`") without proof. We prove it for all `n ≥ 2^k − 2` and all `k ≥ 2` (`corollary9c`).
  Lemma 7 does not argue that the simulated implementation `I'` is obstruction-free (local simulation
  steps must terminate). We avoid `I'` altogether (see below). Lemma 6's proof treats only `m = k`.
* **Typo.** In the proof of Lemma 6, "`V₁` contains a 1 in every component" should be "in its `k`-th
  component", which is all the argument uses.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory, CSLib `Cslib.SharedMemory`: deterministic processes `P` (`n = |P|`),
  invocation, steps and response as separate labels, no crashes. Base objects `B : ι → ObjSpec`
  (`m = |ι|`). Each one stores at most one bit (`OneBit`: states inject into `Bool`) and has arbitrary
  invocations and responses, arbitrary types and arbitrary initial values.
* The implemented object `scannable O` has `k` components. Each is an arbitrary non-monotonic 1-bit
  object (`BitObj`), initially `0`. The operations are `update i o` and `scan`. Readability of the
  components is *not* assumed, which strengthens the lower bounds.
* Hypotheses on the implementation `I`: it allows at least the single-updater invocations
  (`SingleUpdater p₀`: `p₀` updates, the others scan), so multi-updater implementations are covered
  too. It is `Linearizable` and `ObstructionFree`, both over all executions it allows.
* Proof structure: instead of Lemma 7's simulated implementation `I'`, we work with **stages** of `I`.
  A stage is a reachable configuration with active processes `A`, frozen objects `F` and `k'` live
  components. No execution of active processes that updates only live components may change `F`.
  The paper's executions of `I'` are exactly these restricted executions. Lemma 5 is proved for
  stages, and `reduce_stage` plays the role of Lemma 7.

**Main results in Lean** (namespace `Cslib.SharedMemory.Scannable`).

| Paper | Lean | File |
|---|---|---|
| Observation 3 (corrected) | `scan_resp` | `Basic.lean` |
| Lemma 5 (for stages) | `lemma5`, step `lemma5_step`, `γ`-construction `replay` | `Lemma5Step.lean`, `Exec.lean` |
| Lemma 6 | `lemma6` (stages: `lemma6_stage`) | `Main.lean`, `Lemma6.lean` |
| Lemma 7 | `reduce_stage` (replaces the simulation) | `Lemma6.lean` |
| Theorem 8 | `theorem8` (stages: `theorem8_stage`) | `Main.lean` |
| Corollary 9 (a)–(c) | `corollary9`, `corollary9c` (all `k ≥ 2`) | `Main.lean` |
| `k = 1` counterexample to the abstract | `one_component_one_object`, `abstract_bound_fails_k1` | `Degenerate.lean` |
| Implementation 1, Theorem 2 (`s + k` objects, linearizable, lock-free) | `impl1`, `impl1_theorem2`, `impl1_linearizable`, `impl1_lockFree`, `impl1_obstructionFree` | `Impl1*.lean` |
| §4.1 corollaries (`n + k`; single scanner `k + 1`; single updater `n − 1 + k`) | `impl1_nScanner_nUpdater`, `impl1_singleScanner`, `impl1_singleUpdater` | `Impl1Tight.lean` |
| `n = 2`: exactly `k + 1` objects (Lemma 6 + Implementation 1) | `two_process_tight` | `Impl1Tight.lean` |

**Not formalized.** The wait-free single-updater implementation from `2^k` registers (§4.2) is cited from
Vidyasankar and not formalized. Lemma 1 is not a separate theorem; its counting argument is part of the
linearizability invariant of Implementation 1. The `n = 1` degenerate case is only discussed in prose.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The model is CSLib's (`Model`, `Linearization`, `Progress`, `Covering`, `Indist`,
`Atomic`). Shared library (`Cslib/Computability/Distributed/SharedMemory`, `Cslib/Foundations/Data/Nat`, `Cslib/Foundations/Data/Finset`): `curOp` and
`Impl.linearizable_of_run`/`Impl.run_induction` for the linearizability invariant,
`Impl.exists_finish` (completing pending operations by solo runs, paper's `τ'`, `τ''`),
`Impl.LockFree.obstructionFree`, `InfExec.pre`, `Nat.eventually_const_of_succ_le` and
`Fintype.sum_lt_sum_of_eq_off` for the two potentials of the lock-freedom proof.
Non-vacuity: every hypothesis of the lower bounds is met by Implementation 1 with
`k ≥ 2` and readable non-monotonic components, which uses `k + 1` objects for two processes
(`two_process_tight`). For `k = 1`, CSLib's atomic implementation meets them as well (`Degenerate.lean`).
The upper bound assumes *readable* components (`BitObj.Readable`: a read invocation that does not change
the value, with a response that determines it), as the paper does. Implementation 1 leaves the initial
values of the handshake bits arbitrary.
