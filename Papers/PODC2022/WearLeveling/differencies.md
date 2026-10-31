# Differences between the formalization and the paper

Paper: X. Liu, W. Golab, *Brief Announcement: Towards a Theory of Wear Leveling in Persistent Data Structures*,
PODC 2022 (proceedings version, 4 pages; proofs are sketches).

## Errors in the paper (statement level)

1. **Theorem 4.4 is false as stated** (rule R4: the paper explicitly claims generality, "any implemented
   object"; not R2, test-and-set is a standard object; R5: not a headline result, so ❌ rather than 🚨). The
   abstract's primary contributions are the problem formalization and the FAI implementation, and the
   introduction only claims optimality *of the counter*, which holds.
   *Counterexample* (`Tas.lean`): `tasAlg` = `CAS(A[0], false, true); Flush(A[0]); return ¬success`, with `k = 1`
   word. `tas_strictLin` shows it is strictly linearizable in every wear model with `T ≥ 1`. The invariant `TInv`
   says the word is written back at most once (`wear 0 = if pm 0 then 1 else 0`). `tas_lockFree` gives
   lock-freedom. Hence `tas_guarantees : GuaranteesUpTo tasAlg P 1 ⊤` (all executions, any number of updates),
   and `theorem_4_4_false : ¬ Theorem44Statement P`. `Theorem44Statement` is the paper's claim for
   implementations in our model: `¬ GuaranteesUpTo A P T (k·T + 1)` for every object, `k`, word type, algorithm
   and `T`.
   The paper's own counter also contradicts the statement, by one (`theorem_4_4_false_counter`, from
   `guarantees_kT_succ`; see item 2).
   *Where the proof breaks*: "each update operation on the implemented object must update at least one base
   object" is false for objects whose updates do not change the state (TAS after the first operation, max
   registers, consensus, …).
   *Why ❌ and not ⚠️ (R3)*: the intended scope (the counter / FAI) is recoverable from the sentence before the
   theorem ("the endurance bound stated in Theorem 4.3 is optimal"), but the statement explicitly claims "any
   implemented object" (R4 excludes explicit generality) and the proof argues with the general, false step, so
   R3 does not excuse it. The objects that violate it are exactly those whose sequential update sequences have a
   bounded number of distinguishable state changes (TAS, consensus, sticky bits, one-shot objects); for objects
   with unboundedly many (FAI, registers with alternating writes, max registers), the `pm_ne` argument of
   `Optimality.lean` adapts.
   *Robustness w.r.t. the wear model*: the TAS never performs a second write-back, so the refutation holds
   for every failure mode of worn-out words (wrong values, non-responsiveness). In the model where wear counts every update operation applied to a base
   object (Definition 2.1 literally applied to the base CAS words), the refutation by our TAS does not apply. But
   then Theorem 4.3 fails: every FAI starts with `CAS(A[0], …)` (lines 3–5), so `T + 1` sequential FAIs
   already apply `T + 1` updates to `A[0]`. This is not formalized (it is immediate from the pseudocode). Either
   way, Theorems 4.3 and 4.4 cannot both hold in one wear model.
   *Repaired version* (formalized): `theorem_4_4_fai` — for every implementation `A : Alg faiObj k V` of
   fetch-and-increment that is strictly linearizable and obstruction-free in the ideal model, and every `T`,
   there is a sequential, crash-free schedule of one thread with `k·T + 1` FAI invocations after which some word
   has been written back at least `T + 1` times. This is what the paper's proof sketch argues. The proof needs a
   real argument the paper omits: why "each update must update a base object" holds for FAI. Persistent memory
   must change during every FAI, otherwise crashing right after FAI `j` and right after FAI `j + 1` gives
   configurations that agree up to wear counters and operation identifiers (`Alg.Rel`, `pm_ne`). One more FAI
   then returns the same value in both, but strict linearizability forces `j` resp. `j + 1`
   (`resp_after_crash`). Non-vacuity: `counter_exceeds`.

2. **Theorem 4.3: exact endurance depends on how worn-out words fail** (not counted against the paper; at worst ⚠️
   under R4, so it does not affect the verdict). The paper never fixes the failure mode of a worn-out word;
   Definition 2.1 says it loses "safety and liveness". If a worn-out word may stop responding (the `Flush` that
   performs its `(T+1)`-st write-back never completes; a non-responsive failure in the sense of
   Jayanti–Chandra–Toueg, the paper's reference [4]), FAI `k·T + 1` of a sequential run never returns and the
   counter's endurance is exactly `k·T`, as the paper states; the paper's comparison "hardware FAI + Flush
   provides endurance `T`" uses the same reading. Non-responsive wear is not formalized (our `Wear` only has
   wrong values). In the formalized safety-only wear model, the exact value is `k·T + 1`, as follows.
   The paper's intended content, "`k·T` FAIs can be invoked before any element is updated more than `T`
   times", is true and formalized (`theorem_4_3`, `wear_le`, `exec_eq_ideal`). The exactness clause of
   Definition 2.1 ("but not in some execution where `T+1` updates are invoked") fails for `k·T`.
   `guarantees_kT_succ`: with `k·T + 1` FAIs the history is *equal* to the ideal-model history, whatever
   worn-out words store (`hist_eq_ideal_succ`, simulation `Diverged`). When the first worn-out write-back
   happens, all `k·T + 1` operations have done their successful CAS (`diverged_of_worn`: `|L| + 1 ≤ cnt` for
   any thread before its CAS), and afterwards threads only flush and return. `not_safeUpTo_kT_add_two`: with
   stuck-at words, `k·T + 1` sequential FAIs, a crash and one more FAI give two FAIs returning `k·T`
   (`hist_failSched`, `strictLin_res_inj`). Together: `hasEndurance_counter : HasEndurance (counter k) P T
   (k·T + 1)` and `not_hasEndurance_kT`.
   *Why not ❌*: the off-by-one stems from the convention (the counter has no read operation, so the
   damage of the `(k·T+1)`-st FAI is unobservable without one more FAI). The paper's own proof makes the intended
   meaning clear ("FAI `k×T+1` … exceeds its endurance limit, and this *may* cause the implemented object to
   lose correctness"). The same convention applied to a hardware FAI word ("provides endurance `T`") has the same
   off-by-one in the safety-only model. Since the paper's definitions also admit non-responsive wear, under which
   `k·T` is exact, this is a modelling-dependent remark rather than an error; if one insists on reading Theorem
   4.3 as "for *every* base object of endurance `T`" (including safety-only ones), it is a ⚠️-level imprecision
   (R4: the failure mode is an unstated assumption). Either way the verdict is decided by item 1.

## Proof gaps and typos (true statements)

3. Proof of Theorem 4.1, crucial claim: `iter = ⌊ℓ/2^k⌋`, `index = ℓ mod 2^k` should be `⌊ℓ/k⌋`, `ℓ mod k`
   (positions `ℓ` counted from 0; rendered page checked, not a `pdftotext` artefact). In Lean: `CInv.step_cas_succ`
   proves that a successful CAS with `iter, index` happens exactly when `|L| = iter·k + index` and all earlier CASes
   are persistent.
4. Proof of Theorem 4.1: the claim "the ℓ'th FAI in the candidate linearization is the one that executes the
   ℓ'th CAS that succeeds and whose updates are subsequently flushed" is made precise by the invariant: at most one
   successful CAS is not persistent (the last one), and its cache line is the only dirty one (`GInv.dirty_iff`).
   At a crash only that last operation is dropped from the linearization (`CInv.step_crash`). The paper's sketch
   argues order preservation with "the helping mechanism at line 9 / lines 2 and 13". Our local invariant makes
   this explicit (`LocInv`: a thread at line 5 with `iter, index` knows `iter·k + index ≤ m` persisted
   increments).
5. Proof of Theorem 4.2: "read a value `v` from `A[k−1]` at line 13" — line 12. "after performing `k` additional
   iterations" — `k − 1`. The proof also needs finitely many threads (R4, standard; `[Finite P]` in
   `theorem_4_2`): it uses a suffix without successful CAS, which exists because, without responses, each thread
   performs at most one successful CAS. Our proof (potential argument, `phi_step`, `done_step`) follows the
   paper's idea.
6. Proof of Theorem 4.3: "element `A[0]` is accessed `T+1` times" — it is *written back* `T + 1` times. Every FAI
   accesses `A[0]` (line 5).

## Modelling choices

7. **Words are unbounded naturals** (`b = ∞`). The paper's Theorem 4.1 is about a `b`-bit counter with values
   computed modulo `2^b`, under the assumption that "the implemented counter does not overflow during any one
   execution of the FAI operation". Not formalized. Informal reduction: under that assumption, at every CAS of
   line 5 the unbounded run has `0 ≤ A[index] − iter < 2^b`. Indeed `iter ≤ A[index]` by the invariant, and
   `A[index] − iter ≤ ⌈(k − 1 + D)/k⌉ < 2^b`, where `D < 2^b` is the number of increments since the
   invocation (for `k ≥ 2`, `b ≥ 1`). So the comparison modulo `2^b` gives the same result, and the `b`-bit run is
   the unbounded run modulo `2^b`. It returns `(index + iter·k) mod 2^b = ℓ mod 2^b`, matching footnote 2. The
   assumption `b ≥ ⌈log₂ k⌉` is not needed for this.
8. **Persistence model**: the assumptions (1)–(3) of the proof of Theorem 4.3 and "a failed CAS does not dirty the
   line" are built into the model and used for *all* theorems. One word per cache line. Write-backs happen only by
   `Flush` or spontaneous eviction (`Ev.evict`, at any time). A crash reloads the whole cache from persistent memory
   and abandons all running operations; there is no recovery code, and threads may invoke new operations after a
   crash. The cache is coherent and sequentially consistent (a single cached value per word). Memory barriers are
   ignored, as in the paper.
9. **Granularity**: each line of Figure 1 with a shared-memory access is one atomic step. Lines 3, 10, 11 (local) are
   merged into the preceding/following step. Lines 12–13 are the same program states as lines 1–2 (`CL.rd`,
   `CL.fl`), since `index = 0` afterwards in both cases.
10. **Strict linearizability**: formalized at the history level (`IsStrictLin`). An operation *ends* at its
    response or at the first crash after its invocation, and the linearization respects "ends before invoked".
    Operations pending at the end of the history may be included or not. Op ids are assigned at invocation;
    histories also record crashes.
11. **Lock-freedom**: every infinite schedule with finitely many crashes, in which threads with a pending operation
    take infinitely many steps, has infinitely many responses (`LockFreeOn`). It holds for every wear model
    (`theorem_4_2 W`), since the argument never reads persistent memory.
12. **Wear-out model**: a word survives `T` write-backs (`Wear.T`); each later write-back stores
    `junk i w old new`, adversarially chosen. The cache is not affected. Wear counts write-backs of dirty lines
    only (the proof's model). "Endurance" of the implemented object follows Definition 2.1 with updates =
    invocations (FAI and TAS have only update operations): `HasEndurance A T N := GuaranteesUpTo A T N ∧
    ¬ GuaranteesUpTo A T (N+1)`. `GuaranteesUpTo` quantifies over all `junk` (the paper: "maintains its safety
    and liveness"), and its negation exhibits one `junk` (`stuck`: worn-out words keep their old value).
13. **Theorem 4.4 statement**: formalized for implementations in our model (`Alg O k V`, any sequential object
    `O`, any word type `V`), with "endurance at most `k·T`" read as "not guaranteed for all executions with
    `k·T + 1` updates" (`Theorem44Statement`).
14. The FAI object is `faiObj` (operation `Unit`, response = old value, unbounded); the TAS object is CSLib's
    `tasObj`.
