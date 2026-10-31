# Wear Leveling in Persistent Data Structures — PODC 2022

Xialin Liu, Wojciech Golab. *Brief Announcement: Towards a Theory of Wear Leveling in Persistent Data Structures.*
PODC 2022. DOI [10.1145/3519270.3538457](https://doi.org/10.1145/3519270.3538457). Formalized version: the
4-page proceedings version (no arXiv version). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The round-robin counter of Figure 1 is correct: it is strictly linearizable
(Theorem 4.1, for unbounded words) and lock-free (Theorem 4.2). With `k` words of endurance `T` it survives `k·T` FAIs
(Theorem 4.3). (If a worn-out word only stores wrong values but keeps responding, it even survives `k·T + 1`; this
exactness detail depends on how worn-out words fail, which the paper leaves open, and is not counted as a mistake.)
Theorem 4.4 ("any implemented object … can guarantee endurance at most `k·T`") is false as stated: a test-and-set
from one word of endurance 1 never wears out. It is true for fetch-and-increment, so the counter is optimal.

## Mistakes in the paper

* **Theorem 4.4 is false for general objects.** The proof says that, under sequential access, "each
  update operation on the implemented object must update at least one base object". This fails for objects
  whose updates stop changing the state. Counterexample: test-and-set (an update operation) from one word
  `A[0]`: `CAS(A[0], false, true)`, `Flush(A[0])`, return "lost" iff the CAS failed. In the model of the
  proof of Theorem 4.3 (wear = write-backs to persistent memory), `A[0]` is written back at most once in any
  execution, so the refutation holds whatever a worn-out word does (wrong values or no response). With `k = 1` and `T = 1`, the object is strictly linearizable and lock-free in all
  executions, with any number of TAS operations; Theorem 4.4 promises a failure after `k·T + 1 = 2`
  updates. This is a false theorem, not a degenerate case: TAS is a standard object and the theorem says
  "any implemented object". The model cannot be changed to rescue both theorems. If every operation
  applied to a base object counted towards its endurance (Definition 2.1 applied to the base CAS objects),
  Theorem 4.3 would fail instead: every FAI of Figure 1 starts with a CAS on `A[0]` (lines 3–5), so `A[0]`
  receives `T + 1` CASes within `T + 1` sequential FAIs. What we proved instead is the FAI case: every
  strictly linearizable, obstruction-free FAI implementation from `k` words has a sequential crash-free
  execution with `k·T + 1` FAIs that writes some word back `T + 1` times. So the counter's `k·T` is optimal,
  which is the claim of the introduction. (`theorem_4_4_false`, `tas_guarantees`; repaired:
  `theorem_4_4_fai`)
* **The wear model changes between the definition and the proof.** Definition 2.1 counts updates
  *invoked* on an object. For the base objects, the proof of Theorem 4.3 instead counts write-backs to
  persistent memory, under assumptions (1)–(3) and "a failed CAS does not dirty the line". The
  formalization uses the proof's model. Under it, Theorems 4.1–4.3 hold and Theorem 4.4 fails (first item).
* **Typos and slips.**
  - Proof of Theorem 4.1, crucial claim: `iter = ⌊ℓ/2^k⌋` and `index = ℓ mod 2^k` should be `⌊ℓ/k⌋` and
    `ℓ mod k` (with `ℓ` counted from 0). The rest of the proof uses the correct values.
  - Proof of Theorem 4.2: the value of `A[k−1]` is read at line 12, not line 13. The CAS on `A[k−1]` comes
    `k − 1` (not `k`) iterations later.
  - Proof of Theorem 4.3: when FAI `k·T + 1` takes effect, `A[0]` is *written back* for the `(T+1)`-st
    time. `A[0]` is *accessed* (CAS at line 5) by every FAI.
  - Theorem 4.2 implicitly assumes finitely many threads. Its proof needs a suffix without successful
    CAS, and with infinitely many threads each could perform one successful CAS and then stop.
* **Remark, not counted as a mistake: the exact endurance in Theorem 4.3 depends on the failure mode of a worn-out
  word.** The paper never says how a worn-out word fails; Definition 2.1 only says it loses "safety and liveness".
  If a worn-out word may stop responding (e.g. the `Flush` that performs its `(T+1)`-st write-back never
  completes, a non-responsive failure in the sense of Jayanti–Chandra–Toueg [4]), FAI `k·T + 1` never returns and
  the counter's endurance is exactly `k·T`, as stated. The same reading gives "a hardware FAI followed by a Flush
  provides endurance `T`". In the safety-only wear model formalized here (a worn-out write-back stores an arbitrary
  value, the word keeps responding), the exact value is `k·T + 1`. Definition 2.1 says endurance `T` means
  "correct in all executions with at most `T` updates, *but not in some execution with `T + 1`*". With `k`
  words of endurance `T`, the `(T+1)`-st write-back of `A[0]` happens only when all `k·T + 1` FAIs have
  already performed their successful CAS. After that, no thread reads or CASes the memory again: the
  pending operations only flush and return values already computed. A lost or corrupted write therefore
  becomes visible only through a crash *and* another FAI. So the counter is correct in **all** executions
  with `k·T + 1` FAIs, whatever a worn-out word stores. It fails with `k·T + 2`: `k·T + 1` sequential FAIs,
  a crash, one more FAI. If worn-out words keep their old value, the last FAI returns `k·T` a second time.
  So in this wear model the exact endurance is `k·T + 1`, because the counter has no read operation. The
  paper's argument ("`k·T` FAIs can be invoked before any element is updated more than `T` times") is right
  in every wear model. In this wear model the counter itself also exceeds the bound `k·T` of Theorem 4.4 by one.
  (`theorem_4_3`, `guarantees_kT_succ`, `not_safeUpTo_kT_add_two`, `hasEndurance_counter`,
  `not_hasEndurance_kT`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/Computability/Distributed/SharedMemory/Persistent/`, staged for CSLib).
* Asynchronous threads (any set `P`; finite for lock-freedom), adversarial schedules of events: invocation, one
  step of a thread, spontaneous eviction of a cache line, system-wide crash. Deterministic algorithms.
* `k` words of persistent memory behind a coherent, volatile write-back cache (one word = one cache line). Reads and
  CAS act on the cache. A successful CAS dirties the line, a failed one does not. `Flush` and eviction write a dirty
  line back and clean it, and do nothing on a clean line. A crash reloads the cache from persistent memory and
  abandons all running operations. These are assumptions (1)–(3) of the proof of Theorem 4.3.
* Each line of Figure 1 is one atomic step. The purely local lines 3, 10, 11 are merged with the neighbouring
  shared-memory step. Lines 12–13 are the same states as lines 1–2. Words hold unbounded naturals.
* Safety = strict linearizability (Aguilera–Frølund) of the history of invocations, responses and crashes w.r.t. a
  fetch-and-increment counter. An operation pending at a crash takes effect before the crash or never.
* Liveness = lock-freedom: in every infinite schedule with finitely many crashes in which running threads keep taking
  steps, responses keep occurring.
* Wear-out: a word survives `T` write-backs. Every later write-back stores an arbitrary value chosen by the
  adversary (`junk`); the cache is unaffected. Definition 2.1 is `HasEndurance`: safe and live in all executions with
  `≤ N` invocations for every `junk`, but not with `N + 1` for some `junk`. Non-responsive wear (a worn-out word that
  stops answering) is not modelled.

**Main results in Lean** (namespace `Podc.WearLeveling`).

| Paper | Lean | File |
|---|---|---|
| Representation invariant (§3), crucial claim of Thm 4.1's proof | `GInv`, `CInv.step_cas_succ` | `Safety.lean` |
| Theorem 4.1 (strict linearizability; unbounded words) | `theorem_4_1` | `Safety.lean` |
| Theorem 4.2 (lock-freedom, every wear model) | `theorem_4_2` | `LockFree.lean` |
| Theorem 4.3 (safe and live up to `k·T` FAIs; `≤ T` write-backs per word) | `theorem_4_3`, `wear_le`, `exec_eq_ideal` | `Endurance.lean` |
| Theorem 4.3, safety-only wear: also safe and live with `k·T + 1` FAIs | `guarantees_kT_succ`, `hist_eq_ideal_succ` | `Endurance.lean` |
| Theorem 4.3, safety-only wear: failure with `k·T + 2` FAIs; exact endurance `k·T + 1` | `not_safeUpTo_kT_add_two`, `hasEndurance_counter`, `not_hasEndurance_kT` | `Failure.lean` |
| Theorem 4.4 as stated: **false** (test-and-set) | `theorem_4_4_false`, `tas_guarantees` | `Tas.lean` |
| Theorem 4.4 as stated: also violated (by one) by the counter itself, in the safety-only wear model | `theorem_4_4_false_counter` | `Optimality.lean` |
| Theorem 4.4 for FAI (optimality of `k·T`) | `theorem_4_4_fai`, `counter_exceeds` | `Optimality.lean` |

**Not formalized.** The `b`-bit version of Theorem 4.1 (truncation of `iter + 1` and of the return value to `b` bits
under the paper's "no overflow during one FAI" assumption). We use unbounded words. The return value modulo
`2^b` is then `ℓ mod 2^b`, and the reduction is argued in [differencies.md](differencies.md).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `counter_exceeds` instantiates `theorem_4_4_fai` with the counter (its hypotheses are Theorems 4.1–4.2,
via `LockFree.obstructionFree`). The `k·T + 2` counterexample is an explicit execution (`failSched`) computed in
Lean. The CSLib sequential specifications `ObjSpec`/`tasObj` are used. The persistent-memory model, strict
linearizability and their generic lemmas are new (`Podc/Computability/Distributed/SharedMemory/Persistent/`;
CSLib candidates).
