# Consistent Refereeing: Impossibilities for Strong Linearizability — PODC 2026

Hagit Attiya, Armando Castañeda, Constantin Enea. *Impossibility Results for Strong Linearizability: The
Difficulty of Consistent Refereeing.* PODC 2026. DOI
[10.1145/3796701.3815906](https://doi.org/10.1145/3796701.3815906). Formalized version: arXiv
[2506.18401](https://arxiv.org/abs/2506.18401) v3 (same text as the proceedings version); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** All theorems we formalized hold: Theorems 1, 3, 4, 5, 25, 30,
Proposition 11, Corollary 12, and Lemma 14 for counters, max registers and snapshots. The proof of
**Theorem 30 has a gap** in its test&set case; we closed it with a different argument. Case 4c (stack,
push/pop) of Theorem 5 is only sketched; our stack argument does not need it.

## Mistakes in the paper

* **Theorem 30, case "all processes apply T&S to the same test&set object R": proof gap, statement
  true.** The proof compares `αβγpγ′₁q′ᵏγ′₂` with `αβγ′₁q′ᵏγpγ′₂` and claims they end with the same shared
  memory and look the same to every other competitor `q″`. If `R` is still unset after `αβ`, then `q` wins
  the test&set in the first execution and `q′` wins it in the second.
  - `q′` then takes `k` more steps in different local states, and so do the processes of `γ′₂`. These
    steps may write different values to other objects, and `q″` can read them.
  - So neither the memory equality nor the indistinguishability follows.

  Our fix does not use Lemma 29(2). Once some competitor has set `R`, every later referee step on `R`
  changes nothing and commutes with every competitor step. By Lemma 17 the singleton valency `W(αβq·u·p)`
  is then the same for every competitors-only extension `u`. Taking `u` in which some competitor completes
  more operations than that value contradicts the specification. (`const_valency_contra`, `theorem30`)
* **Theorem 5, stack case 4c: sketched only (imprecise proof, statement true).** Case 4c (one push, one
  pop) refers to case 4b, "conceiving the step of `p_i` as a push of `u_i`". The two orders leave
  different stack shapes than in 4b (`u_j·T` vs `s₀·T`, where `s₀·T` is the stack in `C`), so the transfer is
  not immediate. The "w.l.o.g. pushed values are distinct" step (footnote 3, stamping) is standard and
  sound, but our proof does not need it. Our replacement argument covers 4b and 4c:
  - Run the canonical extension (a third competitor solo, then the referee) from `α·i·j` and from `α·j`
    in lock-step. The stacks are `X₁ ++ S` and `X₂ ++ S` and differ only below a common top.
  - If no step pops into `X₁`/`X₂`, the referee returns the same value from a descendant of `α·i` and of
    `α·j`.
  - Otherwise, at the first such pop by `q`, the configurations `α·i·j·β·q` and `α·j·β·q·i` are
    identical.

  (`Crit.stack_push`, `lockstep`)
* **Under-specified steps in Section 5.**
  - Lemma 17 needs `decide` to be pending.
  - In Lemma 17's proof, the operations of `q` must be counted inside `β′`.
  - The case analyses of Lemmas 20, 23, 27, 28 and Theorems 25, 30 omit the referee's invocation and
    response steps.
  - Lemma 29(2) fails in the degenerate case `w = 0`: the sequences it needs do not exist, so we use
    window `max(w, 1)`.
* **Typos.**
  - The last paragraph of Theorem 25 ("We have that αβp is closed. Otherwise…") is garbled; we
    formalized the intended argument.
  - Lemma 28's test&set case calls `αβq′` closed, but it is supervalent there.
  - Lemma 29's proof cites Lemma 21 instead of Lemma 27.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`).
  - Deterministic processes; atomic base objects with deterministic sequential specifications.
  - Executions are label lists, and responses are separate steps.
  - Crashes are processes that stop taking steps.
* `P` is any finite type of processes with a referee `ref`; all other processes are competitors.
* `compete` carries the caller's id, because objects cannot see the caller. The implementation must
  allow each role's operation.
* The contest object of Section 4 is one-shot by definition, but our model lets a process invoke
  operations repeatedly. Statements that hold only for one-shot use are therefore restricted, and this is
  not an error in the paper:
  - Proposition 11 and Theorem 3 are proved on executions where the referee decides at most once.
    Theorem 3's algorithm is not linearizable with two `decide`s. Proposition 11 also assumes an injective
    encoding of process ids as queue values.
  - Theorem 4: the paper's algorithm would overflow the `(n−1)`-window under repeated `compete`s. Our
    variant writes only on the first `compete`, so it is the same algorithm on one-shot executions, and
    it is strongly linearizable on all executions.
  - Theorem 5 says "wait-free" and the introduction says "lock-free". On one-shot executions the two
    coincide: there are only finitely many operations, so both say that no such execution has
    infinitely many steps.
    We prove both (`theorem5_lockFree`, `theorem5_waitFree`).
* Correctness and progress are assumed **only on admissible executions**, which makes the impossibility
  results stronger. Corollaries give the versions with the unrestricted `LockFree`/`WaitFree`/
  `StronglyLinearizable`.
  - One-shot contest (`Adm`): every process invokes at most one operation, the one of its role, and the
    referee starts after some `compete` completed.
  - Long-lived contest (`LLAdm`): roles are respected and the referee decides at most once.
* The long-lived contest is a **nondeterministic** specification (`llSpec`): `decide` may return any
  bound on all competitors' counts. Strong linearizability is taken with respect to it.
* Base objects are given by semantic classes (`Podc/SharedMemory/ObjClasses.lean`,
  `Podc/SharedMemory/ObjClasses/Basic.lean`):
  - Herlihy-interfering (per state);
  - window-like with window `w` (`w`-window registers are window-like with every `w′ ≥ w`);
  - stack-like (isomorphic to a stack);
  - read/write (every primitive is read-only or a blind write);
  - test&set-like (every primitive sets the object to a fixed state).

**Main results in Lean** (namespace `Cslib.SharedMemory.Referee`).

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (no lock-free SL queue from interfering primitives, `n ≥ 4`) | `theorem1` | `QueueCor.lean` |
| Theorem 3 (wait-free linearizable contest from a register) | `theorem3` | `ReadWrite.lean` |
| Theorem 4 (wait-free SL contest from an `(n−1)`-window register) | `theorem4`, `windowObj_not_windowLike` | `Window.lean` |
| Theorem 5 (no lock-free SL contest from interfering objects, `(n−2)`-window registers, stacks, `n ≥ 4`) | `theorem5`, `theorem5_lockFree`, `theorem5_waitFree` | `Contest.lean` |
| Claims 7, 9, 10 | `mem_val_nil`, `val_subsingleton`, `exists_critical` | `OneShot.lean` |
| Proposition 11 | `proposition11` | `Queue.lean` |
| Corollary 12 | `corollary12` | `QueueCor.lean` |
| Lemma 14 (counter, max register, snapshot) | `lemma14_counter`, `lemma14_maxRegister`, `lemma14_snapshot` | `LongLivedPossible.lean` |
| Def. 15, Prop. 16, Lemmas 17, 19, 20–24, 27–29 | `LLCtx.W`, `lemma17`, `lemma19`, `lemma20`, `lemma27`, `lemma28`, `lemma24_1`, `lemma24_2`, … | `LongLived*.lean` |
| Theorem 25 (no wait-free SL long-lived contest from read/write registers, `n ≥ 3`) | `theorem25`, `theorem25'` | `LongLivedMain.lean` |
| Theorem 30 (same from `w`-window registers and test&set, `n ≥ 4`, `3w ≤ n`) | `theorem30`, `theorem30'` | `LongLivedMain.lean` |

**Not formalized.**
* Decisive linearizability, so Theorems 3 and 13 are not covered as decisive. Theorem 13 is not
  formalized at all; Theorem 3 is proved only as linearizable.
* Lemma 14 for fetch&increment and fetch&add.
* Corollaries 26 and 31: they need a general composition theorem for strongly linearizable
  implementations. For queues (Proposition 11) the composition is done concretely.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`.

**Non-vacuity.**
* `theorem4` gives an implementation meeting every hypothesis of Theorem 5 except the window bound,
  and the `(n−1)`-window register is not `(n−2)`-window-like, so Theorem 5 is tight.
* `lemma14_*` give wait-free strongly linearizable long-lived contest implementations, so the
  hypotheses of Theorems 25/30 are not contradictory on their own.
* `register_rw`, `windowObj_hyp30`, `tasObj_hyp30`, `register_interfering`, `stackObj_stackLike`:
  the standard objects belong to the classes.

**Shared infrastructure** (`Podc/SharedMemory/`, CSLib candidates):
* `StrongLin/Restricted.lean`, `Progress.lean`: strong linearizability and progress (`LockFreeOn`,
  `WaitFreeOn`, `ObstructionFreeOn`) restricted to a set of executions; `Solo.lean`: finishing
  pending operations by solo runs (`Impl.exists_finish`).
* `Objects/` (window registers, stacks, queues, counters, max registers, snapshots; `ObjSpec.iface`
  for the long-lived contest's interface `llObj`) and `ObjClasses.lean` (object classes).
* `LinResp.lean` (`ObjSpec.respIn`: responses in sequential histories), `History.lean` (`curOp`,
  `linState_concat`, prefix lemmas), `Run.lean` (forward step equations, `run_induction`),
  `Covering.lean` (agreement of configurations, poised processes and block writes
  `Impl.runFrom_poised_block`, and the locality/commutation lemmas `Impl.step_exact`,
  `Impl.step_comm`), `StrongLin/OneAccess.lean` (single-access implementations, Theorem 4 and
  Lemma 14).
