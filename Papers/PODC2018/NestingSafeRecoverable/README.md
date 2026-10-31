# Nesting-Safe Recoverable Linearizability — PODC 2018

Hagit Attiya, Ohad Ben-Baruch, Danny Hendler. *Nesting-Safe Recoverable Linearizability: Modular
Constructions for Non-Volatile Memory.* PODC 2018. DOI
[10.1145/3212734.3212753](https://doi.org/10.1145/3212734.3212753). Formalized version: the authors'
copy of the conference paper (10 pages, proofs included; no arXiv version). Copy of the paper:
[paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The main results hold. Lemma 1 holds. The recoverable read/write
object (Lemma 2) and the recoverable compare&swap object (Lemma 3) satisfy NRL. Theorem 4 (no
wait-free recoverable test&set from read/write and test&set) is true, but its proof needed a
repair. The false claim is the example built on top of these results: Algorithm 4, the "nesting-safe
recoverable counter", does not satisfy NRL. Its `READ` loses its partial sum when a nested
recoverable `READ` crashes, and `INC.RECOVER` has an off-by-one test.

## Mistakes in the paper

* **Algorithm 4's `READ` is not NRL (false claim about an example algorithm).** `READ` sums
  `R[1..N]` with nested recoverable `R[i].READ` calls, keeping `val` and the loop index `i` in
  volatile variables. Under the paper's own model, a crash inside `R[i].READ` is recovered by
  `R[i].READ.RECOVER`, the innermost pending recoverable operation, and not by the counter's
  `READ.RECOVER`. The caller then continues line 14 with `val` and `i` lost. Counterexample with two
  processes and the most benign reset (volatile variables become 0): process 0 completes `INC`.
  Process 1 starts `READ`, reads `R[1] = 1`, and crashes inside `R[2].READ`. After `R[2].READ.RECOVER`
  it adds 0 to the reset `val = 0` and returns `0`. Repairing this requires a design change, e.g.
  keeping `val` and `i` in non-volatile memory. (`Alg4.read_not_nrl`)
* **`INC.RECOVER` tests `LI_p < 4`; it should be `LI_p ≤ 4`.** Suppose process 0 crashes in `INC`
  when it is about to execute line 4, before invoking `R[p].WRITE`. Then `LI_p = 4`, and
  `INC.RECOVER` returns `ack` without incrementing. A later `READ` returns `0`. The prose ("before
  line 4 – INC is re-executed") gives the intended test. Typo. (`Alg4.inc_recover_not_nrl`)
* **Theorem 4's proof: the "w.l.o.g." renaming breaks the infinite construction; statement true.**
  At each critical configuration the proof assumes "w.l.o.g. `C₁∘p` is `p`-valent" and crashes `p`.
  Renaming the processes can therefore make the crashing process change from round to round. The
  concluding step needs "a crash-free execution of `q`" with infinitely many steps, and a process
  that crashes infinitely often does not contradict wait-freedom. The repair: always crash the same
  process `p`. Whichever of `D·p`, `D·q` is `p`-valent, one of `D·p·q·crash_p` and `D·q·p·crash_p`
  is bivalent. The two configurations share a valency, because `p`'s solo recovery cannot tell
  them apart. Each also inherits the valency of `D·p` or `D·q`, because `q` cannot see `p`'s crash.
  We proved the theorem for all base objects that are read/write-like or test&set-like.
  (`theorem4`, `round`)
* **Lemma 2 needs written values to differ from the initial value too.** The paper assumes "all
  values written to the object are distinct". If a process may later write the initial value
  `v₀`, the following run breaks Algorithm 1. `p` writes 1 and crashes after its write to `R`.
  Then `q` writes `v₀`. `p`'s recovery sees `R` equal to its saved old value, so it writes 1 a
  second time, and a reader sees `1, v₀, 1`. Implied assumption, satisfied by the paper's counter.
  (`alg1_not_nrl_of_initial_rewritten`; `lemma2` is proved with the assumption.)
* **Typos and slips.**
  * Algorithm 3, lines 26 and 28 read `await(R[p] = …)`; they should be `R[i]`. As printed, line 26
    never terminates. Not formalized.
  * In Lemma 3 (Algorithm 2), `new` must not be `null`, because the helping registers start at
    `null`. This is the paper's sentinel convention.
  * The paper's proofs of Lemmas 2 and 3 leave implicit that "linearize the recovered `WRITE` /
    failed `CAS` right before / after another process's step" is a speculative point. Our proofs
    linearize speculatively and retract the entry if the guess turns out wrong.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/Computability/Distributed/SharedMemory/NRL/Model.lean`, a staged CSLib candidate).
* Asynchronous shared memory with atomic base objects in non-volatile memory, for one implemented
  object `O`. Deterministic processes; the adversary chooses the schedule and the crashes.
  There is no randomness.
* Individual crash-recovery. A crash erases the volatile variables, and the system restarts the
  process in `Op.Recover` with the same arguments and `LI_p`, the location it was about to execute.
  The crash and the recovery step form one event. After a primitive, the next location does not
  depend on the primitive's response; this is how we read `LI_p`, and Theorem 4 depends on it.
  After a crash the algorithm fixes the values of the volatile variables; the paper says
  "arbitrary values". This gives algorithms more power, so the impossibility is stronger, and the
  positive algorithms do not read their volatile variables before writing them.
* NRL is Definitions 3–4: recoverable well-formedness, and linearizability of `N(H)` (the history
  without crash and recovery steps) in CSLib's sense. It is required for every finite history that
  satisfies the paper's assumptions on invocations (`Env`).
* Wait-freedom is stated on infinite schedules: a process that never crashes again and takes
  infinitely many steps completes. This covers both the operation and its recovery function.
* Nesting (Algorithm 4) is modelled by a separate concrete interpreter with two-level frames. A
  crash inside a nested operation runs the nested `RECOVER`, and the caller keeps only its return
  address.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (one implemented object over atomic base objects) | `Cslib.SharedMemory.NRL.Alg.recWellFormed_run`, `Alg.nrl_iff` | `Podc/…/NRL/Model.lean` |
| Lemma 2 (Algorithm 1 is NRL) | `lemma2` | `Alg1Main.lean` (+ `Alg1*.lean`) |
| Lemma 2 needs "≠ initial value" | `alg1_not_nrl_of_initial_rewritten` | `Alg1Counter.lean` |
| Lemma 3 (Algorithm 2 is NRL) | `lemma3` | `Alg2.lean` (+ `Alg2*.lean`) |
| Theorem 4 | `theorem4` | `Thm4.lean` (+ `Thm4Basic`, `Thm4Valency`) |
| Algorithm 4 is not NRL (`READ`) | `Alg4.read_not_nrl` | `Alg4.lean` |
| Algorithm 4 `INC.RECOVER` off-by-one | `Alg4.inc_recover_not_nrl` | `Alg4.lean` |
| (sanity) NRL + wait-freedom satisfiable with compare&swap | `casTAS_nrl_waitFree`, `casTASObj_not_rw_tas` | `NonVacuity.lean` |

**Not formalized.** Claim 1 (Algorithm 3), Claim 2 (non-recoverable counter), Definition 1
(strict recoverability), and the nested version of Lemma 1.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Theorem 4's hypotheses are jointly satisfiable once a compare&swap base object is
allowed (`NonVacuity.lean`), so the theorem is not vacuous. The Algorithm 4 runs are evaluated by
the kernel (`rfl`/`decide`). The model is in `Podc/Computability/Distributed/SharedMemory/NRL/`
(`Model`, `Indist`, `Erase`; CSLib candidates). It builds on CSLib's `ObjSpec`, `Label`
histories and `IsLinearization`.
