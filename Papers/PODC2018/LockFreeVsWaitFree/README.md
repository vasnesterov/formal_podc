# Separating Lock-Freedom from Wait-Freedom — PODC 2018

Hagit Attiya, Armando Castañeda, Danny Hendler, Matthieu Perrin. *Separating Lock-Freedom from
Wait-Freedom.* PODC 2018. DOI [10.1145/3212734.3212739](https://doi.org/10.1145/3212734.3212739).
Formalized version: HAL hal-02053248 v1 (no arXiv version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ✅ Correct.** The impossibility half of the separation, Theorem 11, is proved in Lean with
Lemmas 8 and 10 and Claim 9: no wait-free linearizable `n`-LLAA exists from `(n-1)`-window
registers. Our version is stronger than the paper's. The lock-free algorithms (Theorems 4 and 7)
are not formalized.

## Mistakes in the paper

We found no mistakes. Some steps of Section 5 are informal, and we made them precise:

* **Lemma 10: "since A is wait-free, eventually we reach …".** Proof sketch; the statement is true.
  We give the full argument. If every bivalent execution had an extension (without `p₀`) after
  which `p₀`'s next step is not univalent, iterating would build an infinite admissible execution.
  In it `p₀` would stay pending forever while taking infinitely many steps, contradicting
  wait-freedom (`exists_biv_univ`, `exists_critical`).
* **Lemma 8, case `n > 2`.** The "otherwise" branch uses an infinite solo run of some `q` that
  never writes `R`, and then needs a critical `q`-extension (Definition 4). This is unnecessary.
  We stop each solo run once the process is about to write `R` or has completed `k + 3` operations,
  where `k` is fixed by `1/2^k < |v − v'|`. The finite run already gives the contradiction of
  Theorem 11, Case 2 (`Ctx.build`).
* **Lemma 8, "w.l.o.g. `p₁`" and the case split.** Steps that access no memory (invocations,
  responses) are not discussed. Our case split is semantic: does `q`'s step write the object
  accessed by `p₀`'s step? It covers all steps. The case `n = 2` needs no separate treatment: the
  window argument with the block `p₀, p₂, …, p_{n-1}` reduces to `p₀` alone.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib asynchronous shared memory (`Cslib.SharedMemory`). Processes are deterministic. A step
  applies one atomic primitive to one base object. Invocations and responses are separate,
  memory-free labels.
* Processes: any finite type `P` with `n = |P| ≥ 2`. `p₀` is the only process of side `0`; all
  others are on side `1`, as in Section 5. The object knows the caller's side: the operation
  `output()` of side `i` is `i : Fin 2`. Responses are real numbers. The sequential specification
  `llaaSpec` is nondeterministic (Definition 2).
* Base objects: any family (any index type) that is *window-like with window `n − 1`*. That is,
  every operation is read-only or a blind write with a state-independent response, and any
  `n − 1` consecutive writes determine the state. This covers `k`-window registers for `k ≤ n − 1`,
  including read/write registers.
* Progress is CSLib `WaitFreeOn` (wait-freedom in every infinite execution). Correctness is
  linearizability (`IsNLinearization`) of finite executions. The main theorem assumes both **only
  on admissible executions**: every process invokes its side's operation, and `p₀` invokes at most
  once. This is stronger than the paper, which assumes them for all executions.
  `theorem_11_window` is the unrestricted form for window registers.
* No crashes are needed, and the adversary is the scheduler. Since the statement is an
  impossibility, crash-freedom only makes it stronger.

**Main results in Lean.** (namespace `Podc.LockFreeVsWaitFree`)

| Paper | Lean | File |
|---|---|---|
| Definition 2 (n-LLAA) | `llaaObj`, `llaaSpec` | `Spec.lean` |
| final computation of Thm 11 | `close_of_legal`, `Ctx.close_of_univ` | `Spec.lean`, `Valency.lean` |
| Section 5 valency (`v`-potent, univalent, bivalent) | `Ctx.Potent`, `Ctx.Univ`, `Ctx.Biv` | `Valency.lean` |
| Definition 5 (critical) | `Ctx.Critical` | `Critical.lean` |
| Lemma 10, bivalent initial execution | `Ctx.biv_nil` | `Critical.lean` |
| Lemma 10 | `Ctx.exists_critical` | `Critical.lean` |
| Claim 9 | `Ctx.claim9` | `Claim9.lean` |
| Lemma 8 (window argument, construction) | `Ctx.window`, `Ctx.build` | `Main.lean` |
| Lemma 8 + Theorem 11 from a critical execution | `Ctx.false_of_critical` | `Main.lean` |
| **Theorem 11** | `theorem_11` (window-like objects, admissible executions), `theorem_11_window` | `Main.lean` |

The other files hold supporting infrastructure. `Basic.lean` has the setting `Ctx`, schedules and
transfer between indistinguishable executions. `Valency.lean` has solo runs under wait-freedom.
`Commute.lean` has commuting steps (`step_swap`).

**Not formalized.** Theorem 4 (Algorithm 1, lock-free 2-LLAA from reads/writes, with Lemmas 1–3 and
12–16) and Theorem 7 (Algorithm 5, lock-free `n`-LLAA from `(n−1)`-consensus, with Lemmas 5–6).
As a sanity check only (bounded model checking, **not formalized**), a Python checker with exact
rationals ([modelcheck/llaa_mc.py](modelcheck/llaa_mc.py)) explored all interleavings of
Algorithm 1 with up to 3 operations per process and found no violation of linearizability or
lock-freedom.

**Trust.** No `sorry`. `theorem_11` and `theorem_11_window` use only the axioms `propext`,
`Classical.choice`, `Quot.sound`. Non-vacuity: the base-object hypothesis is met by window
registers (`windowObj_windowLike`), and the specification has legal sequences (example in
`Spec.lean`). The model comes from CSLib `Cslib.Computability.Distributed.SharedMemory.{Model,
History, Progress, Solo, Covering, Linearization, ObjClasses.Basic, Objects.Window}`.

**CSLib candidates** (marked `-- CSLib candidate`): `step_swap`, `mem_step_eq`,
`mem_step_of_readOnly` (`Commute.lean`), `PoisedAt.op_eq` (`Claim9.lean`),
`eventually_const_of_mono_lt`, `le_idx_of_sublist` (`Valency.lean`).
