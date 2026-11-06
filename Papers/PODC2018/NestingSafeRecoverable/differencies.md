# Differences between the formalization and the paper

Attiya, Ben-Baruch, Hendler. *Nesting-Safe Recoverable Linearizability: Modular Constructions for
Non-Volatile Memory.* PODC 2018 (author copy, 10 pages, proofs included).

## Model (Section 2)

1. **One implemented object, atomic base objects.** `Cslib.SharedMemory.NRL.Alg P O` (in
   `Podc/Computability/Distributed/SharedMemory/NRL/Model.lean`) models one recoverable object `O`
   implemented from atomic base objects. Nested recoverable objects are not modelled generically.
   Lemmas 2 and 3 and Theorem 4 concern exactly this setting. Algorithm 4 (nesting) gets a separate
   concrete two-level interpreter (`Alg4.lean`).
2. **Crash + recovery step = one event.** The paper has separate `CRASH` and `REC` steps. A crashed
   process takes no step until it recovers, so the time in between looks like a slow process. Merging
   the two steps changes no finite history up to the position of the crash step, and `N(H)` (which
   drops both) is the same. A crash that is never followed by a recovery is a process that takes no
   more steps. A crash of a process with no pending operation has no effect. The paper leaves this
   case undefined: such a crash has no "crashed operation".
3. **Volatile state and `LI_p`.** A local state is a location `pc` plus volatile variables. A crash
   erases the volatile variables and restarts the process at `recover p o pc`. Here `pc` is the
   location the process was about to execute (the paper's `LI_p`), and `o` carries the arguments of
   the crashed operation ("the same arguments"). The paper resets locals to *arbitrary* values. We
   let the algorithm fix the values after a crash, which gives algorithms more power, so the
   impossibility (Theorem 4) only gets stronger. For the positive Lemmas 2–3 the recovery code
   never reads a volatile variable before writing it, so nothing is lost.
   **The location after a primitive step does not depend on the primitive's response**
   (`Act.access i op pc' k`: the response goes into the volatile variables through `k`). This is how
   we read "`LI_p` identifies the instruction of `Op` that `p` was about to execute": in the paper's
   pseudo-code a primitive is a line `x ← prim()` and a test of `x` is a later line. Theorem 4
   depends on this. If the next location could depend on the response (e.g. `t&s` jumping to
   different lines on 0 and 1), then `T&S.Recover` could read the outcome from `LI_p`, and a trivial
   wait-free NRL test&set built on one test&set object would exist. This remark is not formalized.
4. **Response steps.** Returning from the implemented operation is a separate step (`Act.ret`). A
   crash in a state whose next action is `ret` is a crash of the still-pending operation. This is the
   paper's "the response value is lost if p incurs a crash before persisting it".
5. **Histories.** `Cfg.hist` records `inv`/`res`/`crash`/`rec` steps. `N H` is a CSLib `Label`
   history, and linearizability is CSLib's `IsLinearization`. It is equivalent to Definition 2's
   "completion + equivalent legal sequential history": the linearization may include pending
   operations and must include all completed ones.
6. **Environment assumptions as `Env`.** Assumptions on how operations are invoked (distinct written
   values, at most one `T&S` per process, `old ≠ new`) are a predicate on the invocations of
   `N(H)`. `Alg.NRL Env` requires NRL only for histories satisfying `Env`.
7. **Wait-freedom** (`Alg.WaitFree`) is stated with infinite schedules. A process with a pending
   operation that never crashes again and takes infinitely many steps eventually completes. This
   covers "the operation and its recovery function are wait-free" at once. We use exactly this
   consequence of the paper's two hypotheses, so the theorem is not weakened.

## Lemma 1

8. `recWellFormed_run`: every history of the model is recoverable well-formed. This is the paper's
   Lemma 1 for one implemented object over atomic base objects (condition (1) holds in the stronger
   form "every crash step is immediately followed by its recovery step"). The paper's Lemma 1 also
   covers histories of nested recoverable objects. That version is not formalized.

## Theorem 4

9. **Statement.** `theorem4`. "read/write and non-resettable TAS base objects" is generalized to
   "base objects that are read/write-like or test&set-like" (`ObjSpec.RWLike ∨ ObjSpec.TASLike`
   from CSLib). The proof works for any objects satisfying `CritOK`: two operations on the same
   object either absorb one another or lead to the same object state in both orders. NRL is assumed
   only for histories in which every process invokes `T&S` at most once (`OneShot`; the paper
   assumes this for Algorithm 3). Only two processes `p ≠ q` are used. The hypotheses are weaker
   than or equal to the paper's, so the statement is at least as strong.
10. **Proof repair: the "w.l.o.g." renaming of `p` and `q` (🔧).** At each critical configuration
    the paper assumes "w.l.o.g. `C₁∘p` is `p`-valent and `C₁∘q` is `q`-valent" and then crashes
    `p`. In the other case (`C₁∘p` is `q`-valent), renaming the processes makes *`q`* the crashing
    process. "Repeating the same argument" can therefore change the crashing process from round to
    round. The final step, "a crash-free execution of `q` in which it executes an infinite number of
    steps", then needs a process that crashes only finitely often, and the argument does not provide
    one. If both processes crash infinitely often, wait-freedom is not contradicted. Fix (`round`):
    always crash `p`. Whichever of `D·p`, `D·q` is `p`-valent, one of `D·p·q·crash_p` and
    `D·q·p·crash_p` is bivalent. Proof: `p`'s solo recovery from both configurations returns the
    same value, so they share a valency, and each of them also has the valency of `D·p` or `D·q`
    respectively, because `q` cannot see `p`'s crash (`agree_val` applied three times). The paper's
    own case split on `u` ("the other case is symmetric") covers only half of this.
    This is a gap in the proof of a true theorem.
11. "This must be a TAS base object other than those previously used" is true but not needed. The
    contradiction comes from `q` taking infinitely many steps without crashing. We do not use it,
    which is why the proof extends to objects with a finite state set.
12. "`C₀` is bivalent – a solo execution of each process returns 0": with both processes having
    invoked `T&S`, this needs the observation that `p`'s solo run from `C₀` is indistinguishable to
    `p` from its solo run when `q` has not invoked. Then linearizability forces `0` (`val_C0`).
    Routine; not counted as a gap.
13. Valency is defined as in the paper, with crash-free extensions (`Val`). Critical configurations
    exist by wait-freedom (`exists_crit`), and an infinite bivalent crash-free chain contradicts
    `WaitFree` directly.

## Lemmas 2 and 3 (Algorithms 1 and 2)

A. **Lemma 2 (`lemma2`, files `Alg1*.lean`).** The implemented object is CSLib's `register V v₀`.
   A `write v` returns `v`, which stands for the paper's `ack`. Base objects: the register `R` and
   the per-process registers `S_p = ⟨flag, curr⟩`, initially `⟨0, null⟩`. One primitive per step.
   The tests of lines 12 and 14 are internal steps, and `R` is read in line 14 only when
   `flag = 1` (short-circuit evaluation). `READ.RECOVER` (lines 19–20) is the same code as
   `READ`, so its recovery restarts at line 8.
   **Environment (`Env1`):** all `WRITE` arguments are pairwise distinct *and differ from the
   initial value `v₀`*. The paper says only "all values written to the object are distinct". Read
   so that the initial value does not count as written, Lemma 2 is false.
   `alg1_not_nrl_of_initial_rewritten` gives a 27-event run with pairwise distinct written values,
   one of which is `v₀`: `p` writes 1 and crashes, `q` reads 1, writes `v₀ = 0` and reads 0. Then
   `p` recovers, sees `R` equal to its saved `temp` and re-executes the write, and `q` reads 1
   again. The history is not linearizable. The paper's own use (the counter writes 1, 2, …, never
   the initial 0) satisfies the stronger assumption, and "the initial value is the first write" is
   the standard convention. Implied assumption (✏️).
   **Proof.** The paper linearizes a recovered `WRITE` that did not write `R` "immediately before
   `q`'s write". At the time of `q`'s write, `p` may still be about to execute line 4 itself, so
   this is a speculative linearization point; the paper leaves that implicit. We add such
   "phantom" entries speculatively at `q`'s write and retract them (`erase_absorbed`) if `p` writes
   after all. A crashed `READ` is retracted with `erase_ro`. Referee-level detail, not a gap.
B. **Lemma 3 (`lemma3`, files `Alg2*.lean`).** The implemented object is `casRObj V`: state
   `Option V`, initially `null`; operations `cas (old : Option V) (new : V)` and `read`. `new` is
   never `null`. This is needed, because the registers `R[p][j]` start at `null` and would make the
   recovery return `true`. Null is the paper's sentinel (✏️, standard convention).
   **Environment (`Env2`):** the `new` values of each process's `CAS` invocations are pairwise
   distinct, and `old ≠ new`. The paper says "values written to `C` by the same process are
   distinct"; we read it as distinct `new` arguments, which is the paper's "augment with a sequence
   number". The recovery's loop over `R[p][1..N]` reads one register per step, after the read of
   `C` (the paper's "left term first"). The step implicit in the paper: the process `q` that
   overwrote `⟨p,new⟩` never later overwrites `R[p][q] = new` before `p` recovers, because every
   later read by `q` of a content with id `p` returns `⟨p,new⟩` itself (`eq_of_noAfter`). No error.
C. **Non-vacuity of Theorem 4's hypotheses (`NonVacuity.lean`, not in the paper).** With one
   compare&swap base object there is a recoverable test&set satisfying both `NRL OneShot` and
   `WaitFree OneShot` (`casTAS_nrl_waitFree`), and compare&swap is neither read/write-like nor
   test&set-like (`casTASObj_not_rw_tas`). So the definitions of NRL and wait-freedom in the model
   are satisfiable together, and the restriction on base objects in Theorem 4 matters.

## Algorithm 3 / Claim 1 (recoverable TAS, non-wait-free recovery)

14. **Not formalized.** Lines 26 and 28 of Algorithm 3 read `await(R[p] = 0 or R[p] = 3)` and
    `await(R[p] = 0 or R[p] > 2)`. They should be `R[i]`: the prose says "p waits for all
    lower-indexed processes", and the proof uses `R[i]`. As printed, line 26 never terminates for
    `p > 0`, because `p` has just set `R[p] ← 4`. Typo with evident intent (✏️). We checked the
    proof of Claim 1 informally with `R[i]` and found no error. Its second part ("if all operations
    run long enough, some operation returns 0") is a liveness argument used to build linearizations
    of finite histories; a mechanized proof would need a prophecy or a retroactive argument.

## Algorithm 4 (recoverable counter)

15. **Algorithm 4's `READ` does not satisfy NRL (❌, `read_not_nrl`).** The paper presents
    Algorithm 4 as a "nesting-safe recoverable Counter" and says it constructs a recoverable object
    "satisfying the same condition". `READ` accumulates `val` and the loop index `i` in volatile
    variables while calling the recoverable `R[i].READ` (line 14). (They are volatile by the
    paper's own conventions: §3 uses lower-case names for local variables, and §2 keeps local
    variables in volatile registers, all reset by a crash; `Res_p`, capitalised, is the only shared
    variable of `READ`.) After a crash inside
    `R[i].READ`, the model (Section 2) resumes the process by running `R[i].READ.RECOVER`. That is
    the innermost pending recoverable operation, and `READ.RECOVER` (which would restart at line 12)
    is not invoked. The caller then continues line 14 with `val` and `i` reset. Counterexample
    (`schedRead`, 2 processes, volatile variables reset to `0`, the most benign "arbitrary"
    values): process 0 completes `INC`, then process 1's `READ` reads `R[1] = 1`, crashes inside
    `R[2].READ`, recovers and returns `0`. This is not linearizable. The interpreter in `Alg4.lean`
    follows the paper's nesting semantics literally ("once its recovery is completed, INC returns
    in line 5"). A repair needs a design change (e.g. `val` and `i` in non-volatile memory, or
    primitive reads of `R[i]`'s register instead of the recoverable `READ`); no repair is proved.
16. **`INC.RECOVER` tests `LI_p < 4`; it should be `LI_p ≤ 4` (✏️, `inc_recover_not_nrl`).** A
    crash when `p` is about to execute line 4 (before invoking `R[p].WRITE`) gives `LI_p = 4`, and
    `INC.RECOVER` returns `ack` without incrementing. The prose says "whether the last crash inside
    INC occurred before line 4 – in which case INC is re-executed". Counterexample `schedInc`: a
    later `READ` returns `0`. Typo with evident intent.
17. Claim 2 (the non-recoverable counter is linearizable) is standard and not formalized.

## Not formalized

* Definition 1 (strict recoverability), the nested version of Lemma 1, Claim 1, Claim 2.
