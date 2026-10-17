# Space Complexity of Detectable Objects — PODC 2020

Ohad Ben-Baruch, Danny Hendler, Matan Rusanovsky. *Upper and Lower Bounds on the Space Complexity of
Detectable Objects.* PODC 2020. DOI [10.1145/3382734.3405725](https://doi.org/10.1145/3382734.3405725).
Formalized version: arXiv [2002.11378](https://arxiv.org/abs/2002.11378) v1; numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** Algorithm 2 (detectable CAS, Lemma 2) is not linearizable: a crash-free run of
two processes each executing `Cas(v₀, v₀)` breaks it. We prove a fixed version correct. Theorems 1 and 2 (the
first assuming |V| ≥ N values), Lemmas 3–8 and Algorithm 3 are proved, and Algorithm 1's initialization is
under-specified (it fails only with 0-based process ids; the fixed version is proved).

## Mistakes in the paper

* **Lemma 2 is false for `Cas(v, v)`.** Two processes both run `Cas(v₀, v₀)` while the value is `v₀`.
  Both read `C = ⟨v₀, vec⟩`. The first hardware CAS succeeds and flips its own bit of `vec`, so the
  second one fails. That process returns `false`, although the value was `v₀` the whole time. The
  history `inv a, inv b, res a true, res b false` has no linearization; no crash is needed.
  The proof says "the CAS fails only if another process performed a successful CAS … hence the value
  … must be other than old", which overlooks successful CASes that do not change the value.
  `Cas(v, v)` is a legitimate operation that the paper never excludes, and the run consists of the
  first operations of the two processes. Severity: false statement. Fix: `Cas(v, v)` just reads `C` and
  persists and returns `val = v`. We prove the fixed algorithm wait-free, durably linearizable and
  detectable. (`alg2_not_durLinDet`; fix `alg2fix_durLinDet`)
* **Algorithm 1's initialization `R = ⟨v_init, 0, 0⟩` is under-specified; it fails if process 0 is a real process.**
  The proof's key observation is that q writes with the same toggle index again only after
  completing a write with the other index. This fails for the fictitious initial write, because
  `T_0 = 0` and process 0's first write uses toggle 0. Counterexample with 2 processes and 1 crash:
  - Process 0 starts `Write(v_init)` and passes line 6 (`CP = 1`).
  - Process 1 completes `Write(v₁)`.
  - Process 0 executes line 7, rewriting the initial triple `⟨v_init, 0, 0⟩`.
  - Process 1 completes a `Read`, which returns `v_init`.
  - The system crashes.
  - Process 0's `Write.Recover` sees the old triple and `A[0][0][1] = 0`, so it returns `fail`.

  A read after a completed `Write(v₁)` thus returns a value whose only write "failed".
  Severity: under-specified definition. The paper's ids are 1-based ("for i = 1 to N",
  `p1, …, pN`), so "process 0" is fictitious. But then line 2 writes the entry `A[p][0][·]`,
  which is not part of `A[N][N][2]`. The counterexample applies only to the 0-based reading. Fix: initialize `R = ⟨v_init, 0, 1⟩`. We prove the fixed algorithm wait-free,
  durably linearizable and detectable for all `n` and all value types. (`alg1_not_durLinDet`; fix
  `alg1fix_durLinDet`)
* **Theorem 2, statement.** "Let Op be a recoverable operation" cannot be meant universally: a register
  `read`, for instance, needs no auxiliary state. The intended `Op` is the witness of double perturbation,
  and we prove the theorem in that form. (`theorem2`)
* **Theorem 2, last step (proof gap, statement true).** "Executing `Op_q` starting from `E₁` returns
  `u ≠ v`" does not follow from linearizability, because the second `Op_p` is pending in `E₁` and
  could be linearized first. The contradiction is obtained instead from the linearization of
  execution `D`, where the single `Op_p` must precede `Op_r`. (`theorem2`)
* **Definition 1 is imprecise (under-specified definition).** "A write is made to a non-volatile
  variable accessible by `Op` in-between two successive invocations" is satisfied by the operation's
  *own* writes (e.g. `Ann.result := r`), which would make the conclusion of Theorem 2 trivially satisfied. The intended (and
  needed) notion is a write made *outside* the operation, by the system or the caller; we model it
  as a hook `aux` applied at invocation.
* **Minor proof gaps in Theorem 1 (statement true).**
  - The induction hypothesis is applied to a non-initial configuration with a halted pending
    operation and a shrunk value domain.
  - "`Cas_q(0,1)` after `C ∘ α` returns true" needs an indistinguishability argument when `α` is
    empty.

  We unroll the induction. (`theorem1`)
* **Imprecisions in the proof of Lemma 1 (statement of the fixed algorithm true).**
  - The text says recovery detects a write between the two reads of `R` "if and only if" q's toggle bit is 1.
    The "only if" direction is false: q may complete a whole write with the other toggle between p's lines
    1 and 2. Then the bit is 0 although a write occurred, and recovery returns `fail`. This is harmless.
  - "Linearize W immediately before W′" must use the first write W′ after p's line 1. Recovery may be
    re-run after a crash between deciding `fail` and returning, so the linearization must be retractable.
    The paper does not discuss this; our proof handles it with speculative entries.
* **Typo.** Proof of Lemma 2: "Cas.Recover simply re-invokes Op (line 41)", but line 41 returns
  `fail`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`, self-contained).
* Asynchronous processes `P` communicate through non-volatile shared memory, under the
  private-cache model with **system-wide crashes**. A crash resets the local state of every
  running process to the start of its recovery function; idle processes stay idle.
* A step is either an arbitrary atomic transformation of the *whole* shared memory, or an access
  to the process's own private NVM. Hence the lower bounds hold for any primitives, which is
  stronger than the paper. The algorithms use only single-variable read/write/CAS steps.
* At an invocation the system or caller may write the invoker's private NVM (`aux`: auxiliary
  state via NVM, e.g. `Ann_p.CP := 0`). Operations receive exactly the abstract arguments, so
  there is no auxiliary state via arguments.
* **Correctness** (`DurLinDet`) is durable linearizability plus detectability, as one condition:
  every finite execution has a sequential order that contains every operation that returned a
  value (with that value), contains no operation whose recovery returned `fail`, may contain
  pending operations, and respects real-time order. `fail` is only returned by recovery
  functions.
  Sanity check against CSLib (`LinBridge.lean`): let `h` be a history without crashes and `fail`
  responses that records a well-formed CSLib history `α`, with identifier `ι (p, k)` for the
  `k`-th operation of `p` and `ι` injective on the invoked instances. Then a list of invoked
  instances is a CSLib linearization (`IsLinearization`) of `α` iff its renaming by `ι` is a
  `DLin` of `h` from `O.init`. Hence `h` has a `DLin` from `O.init` iff `α` is linearizable
  (`dLin_iff_isLinearization`, `exists_dLin_iff_exists_isLinearization`).
* **Progress.** `ObstructionFree`: from every reachable configuration, a solo process completes.
  `WeakOF` (Definition 2): the same, but only when all others are idle. `BoundedSteps` is a
  syntactic wait-freedom certificate.
* Deterministic processes; no randomness. The adversary chooses the schedule and the crashes.
* Objects: sequential specifications `ObjSpec` with the shared catalog (`register`, `casObject`,
  `queueObj`, `maxRegObj`); the paper-specific ones are the counters, the read/CAS object `casRC`
  and fetch-and-add with `read` (`Perturbing.lean`). Responses assigned by a sequential order are
  the library's `ObjSpec.respIn`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (≥ 2^(N−1) reachable shared-memory states; ≥ N−1 bits) | `theorem1`, `theorem1_bits` | `Thm1.lean` |
| Theorem 2 (the witness operation of a doubly-perturbing object needs auxiliary state) | `theorem2`, `theorem2_exists`; instances `register_needs_aux`, `cas_needs_aux`, `counter_needs_aux`, `faa_needs_aux`, `queue_needs_aux` | `Thm2.lean` |
| Definition 3, Lemmas 3, 5, 6, 7, 8 (doubly-perturbing objects) | `DoublyPerturbing`, `register_doublyPerturbing`, `counter_doublyPerturbing`, `bcounter_doublyPerturbing`, `cas_doublyPerturbing`, `casRC_doublyPerturbing`, `faa_doublyPerturbing`, `queue_doublyPerturbing` | `Perturbing.lean` |
| Lemma 4 (max register is not doubly-perturbing) | `maxReg_not_doublyPerturbing` | `Perturbing.lean` |
| Lemma 2 is false (Algorithm 2) | `alg2_not_durLinDet` | `Alg2Counter.lean` |
| Lemma 2 for the fixed Algorithm 2 (wait-free, DL, detectable) | `alg2fix_durLinDet`, `alg2Gen_boundedSteps`, `alg2fix_thm1_hyps` | `Alg2Fix.lean`, `Alg2Defs.lean` |
| Lemma 1 is false (Algorithm 1, initial toggle 0) | `alg1_not_durLinDet` | `Alg1Counter.lean` |
| Lemma 1 for the fixed Algorithm 1 (initial toggle 1; wait-free, DL, detectable) | `alg1fix_durLinDet`, `alg1_boundedSteps`, `alg1fix_obstructionFree` | `Alg1Fix.lean`, `Alg1Defs.lean` |
| Algorithm 3 (detectable max register without auxiliary state; no proof in the paper) | `alg3_durLinDet`, `alg3_obstructionFree`, `alg3_noAux` | `Alg3.lean` |

**Not formalized.**
* Independent (per-process) crashes and the shared-cache model; the paper only remarks that the
  results transfer to them.
* The notion of perturbable objects, hence the claims "bounded counter is not perturbable" and
  "max register is perturbable".
* The NRL transformation of Section 6.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`.
* Non-vacuity: `alg2fix_thm1_hyps` exhibits an obstruction-free (indeed wait-free), durably
  linearizable and detectable CAS, so Theorem 1's hypotheses are satisfiable. The same algorithm
  uses auxiliary state (`aux` resets `CP`/`result`), as Theorem 2 demands.
* `alg3_*` show that without the doubly-perturbing hypothesis Theorem 2 fails: a detectable max
  register needs no auxiliary state.

CSLib candidates: the long-lived crash-recovery model with durable detectable linearizability
(`Model.lean`, `Basic.lean`, `Lin.lean`, `Alg2LinTools.lean`, register tools in `Alg1Lin.lean`,
the bridge `LinBridge.lean`).
