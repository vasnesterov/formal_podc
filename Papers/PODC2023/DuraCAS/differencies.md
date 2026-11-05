# Differences between the formalization and the paper

Paper: Jayanti, Jayanti, Jayanti, *Brief Announcement: Efficient Recoverable Writable-CAS*, PODC 2023
(the "BA"); proofs from the full version *Durable Algorithms for Writable LL/SC and CAS with Dynamic
Joining*, arXiv:2302.00135v1 (the "FV").

## Statement-level issues (decide the verdict)

1. **Recovery discipline (Theorem 4.1(1), headline) — 🚨 (R4 not applicable, R5 headline).**
   The BA states the obligation of a crashed process per object: "when π subsequently restarts, it
   must execute `O.Recover()` before invoking any other operation on `O`". The DurEC handles (and
   their `Val`/`DetVal` fields) are shared by all objects of the type, as the BA requires ("whenever
   the process calls any method on any of the implemented objects of that type, it passes its handle
   h"). A process that crashed right after its install at line 10 of DurEC's `ECSC` on object `O₀` and
   then — legally under the BA's rule — invokes a `CAS` on `O₁` overwrites `h.Critical.Val` at
   line 7; a helper then forwards that value into `O₀`. `theorem_4_1_1_false` /
   `perObject_counterexample`: 2 processes, 2 objects, initial values 0; a `READ` of `O₀` returns 2,
   which only an operation on `O₁` ever proposed. R4 does not excuse it: the paper explicitly states the
   weaker discipline (and the FV's Appendix A.2/A.3 argue per object too: "W.RECOVER() or Z.RECOVER()
   is executed before any other operation is executed on W or Z"). Borderline aspect, recorded here:
   the FV's model section says "when p subsequently restarts, it is required to execute O.RECOVER()",
   which can be read as "immediately" (per-process); under that reading the theorem holds
   (`theorem_4_1_1`). Detectability fails under the per-object rule as well (a `DETECT` bracket of an
   operation then also covers the propagation of the earlier crashed install; found by the Python model
   checker, not formalized separately).
   Reviewer's weighing (recorded because the call is borderline): for ⚠️ speak the cited model
   (the BA adopts recoverable linearizability "as adapted to the individual crash model by [2]",
   Attiya–Ben-Baruch–Hendler's nesting-safe model, which is per-process), the per-handle `DETECT`
   contract (a bracket "just before … just after" an operation presupposes that the process runs
   nothing else in between) and the FV's model sentence. Against it: the BA states the per-object
   rule deliberately and twice ("before invoking any other operation *on O*"), handles are
   explicitly shared by all objects of the type, and the authors' own composition step needs and
   uses exactly the per-object rule at the DurEC level (DuraCAS's `RECOVER` runs `W.RECOVER` before
   `Z.RECOVER`, so strict per-process recovery would not even hold for `W`, `Z`); the correct
   discipline ("recover before any other non-`RECOVER` operation with the same handle") is stated
   nowhere. A user taking the BA at its word (lazy per-object recovery) gets another object's value
   — substantive (R4 "misled substantively"; R3 "the proof reasons with the wrong version"). So 🚨.

2. **Null dereference in `FORWARD` (Algorithm 1, lines 14 and 16) — ⚠️ (R3: missing case in
   pseudocode, evident fix).** `X` is initialised to `(null, 0)`; `RECOVER` (hence `FORWARD`) is called
   on objects that never had an install (e.g. DuraCAS lines 22–25 always recover both `W` and `Z`), and
   then `x.hndl.DetVal` and `x.hndl.Val` dereference null. We model the evident fix "if `x.hndl = null`
   then return" (then `x.seq = 0` and line 18 does nothing anyway).

3. **Lemma 4.4 / Lemma A.5(1) — ⚠️ (R3 typo).** "In the interval (t′, t), `X.hndl = h`, `h.Val = v`"
   should be `h′` (the installer's handle), not `h` (the mover's handle, which `FORWARD` ignores).
   As written it is false whenever another process moves.

4. **Lemma A.10(2) — ⚠️ (R3).** "If `h.DetVal` is changed … then `X.hndl = h` and `h.pc ∈ {13,14,15}`" is
   false as written: a helper can change `h.DetVal` while the installer is at line 11 (has installed,
   has not yet called `FORWARD`) or has crashed (its pc is lost / it is in `RECOVER`). The intended
   statement ("h's installing `ECSC` is not yet complete") is what the proof of A.10(3) uses. The
   invariant (statements 1–5) used to prove A.10, whose proof the paper omits, is also wrong as
   stated (statement 3 fails once a helper moves while the installer is still at line 13–15; statement 4
   fails when the handle is used on two DurEC objects, as DuraCAS does with `h.Critical` on `W` and
   `Z`). Lean: `lemmaA10_2_counterexample` (p₀ installs on `Z` and crashes; p₁'s `FORWARD` raises
   `(p₀,crit).DetVal` from 0 to 1 while p₀ has no active DurEC call); the corrected statement
   `detVal_help_pending` (a successful line-15 CAS writes the sequence number of the install that is
   currently pending on that object). Detectability (A.10.1, A.10.3, A.11) holds and is proved with a
   different invariant (`CInv.lean`; per-process uniqueness of pending installs replaces statement 4).
   In the paper's pseudocode there is also a crash-free counterexample (the installer sits at
   line 11, between its install and its call of `FORWARD`, while a hitchhiker's `FORWARD` executes
   line 15); our model merges line 11 into line 10, so the Lean witness uses a crash. Borderline
   ⚠️/❌ (a false numbered lemma of the FV whose repair adds the missing pc 11 and the crashed
   state); it does not affect the verdict, which is decided by item 1.

## Proof gaps (statements true under the per-process discipline)

5. **Composition "W and Z behave like atomic EC objects" (start of A.2 and A.3) — 🛠️.** Claimed
   without proof. It is true under the per-process discipline but only in a weaker sense than
   "atomic": a crashed `ECSC` may take effect *after* the crash (while the process is down or
   recovering), until the corresponding `RECOVER` completes. We formalize this as the A-level model
   (`AModel.lean`: atomic EC objects with *orphan* `ECSC`s) and prove the refinement
   (`reach_aReach`, `Refinement.lean`). The A.3 proof must then also handle orphans (an orphan install,
   imprint or move behaves like the corresponding poised operation).

6. **Linearization of hitchhiker `ECSC`s (Definition 4.6(2), main text) — typo.** "the earliest time t
   such that a move occurs at t" must be "… with t > α[6]" (as in Definition A.8); otherwise an `ECSC`
   that reads `Y.seq = s` after a move that set `Y.seq = s` would be linearized as failing in a state
   where it should succeed.

7. **Failing `CAS` and hitchhiking writes (Definitions A.42(3), A.43(2)).** "linearized at the earliest
   time when `Z.val ≠ old`" must be "the earliest such time in the operation's interval" (Lemma A.39
   provides one). Both linearization points are not determined forward in time (`Z.val` can go
   `old → x → old` during the first iteration while the `CAS` still succeeds in the second; a write
   may still install after the first move in its interval); the proof inserts these operations into the
   linearization retroactively at their witness step (`ALin.lean`, keys `4t + rank`). Lemma A.38 needs an
   extra ghost (whether the last change of `Z` was a move). No lemma of A.3 is false for the A-level
   model.

8. **DuraCAS's `W` initial value.** `W ← DurEC((0, 0))` uses the integer 0; for an arbitrary value
   type we initialise `W.val` with the object's initial value (never read before an install).

## Modelling choices

* Asynchronous shared memory (NVM), individual crash–restart failures, any number of crashes;
  read and CAS hardware primitives; DurEC code inlined into DuraCAS (one hardware operation per
  step). Arbitrary process type `P` (dynamic joining), arbitrary object type `K`, arbitrary values `V`.
* Handles: process `p` owns the DurEC handles `(p, crit)` and `(p, cas)`, present from the start with
  `DetVal = 0`, `Val` arbitrary (`hv0`). `CreateHandle` and object construction are pure allocation
  and not modelled as steps.
* `DETECT` is not a step: the history records its value `DetVal(h.Critical)` at every invocation and
  completion (`d₁`, `d₂`); its second component is always `true`.
* Durable linearizability (`DurLin`) and detectability (`Detectable`) are defined on histories with
  invocation, response, crash and recovery-completion events (`Spec.lean`); "safe to repeat" is
  formalized as "not linearized" for operations completed by `RECOVER` with `d₂ = d₁`.
* Most general client: an idle process may invoke any operation on any object; a crash of a busy
  process restarts it at `RECOVER` of the object of its operation (per-process discipline).
* Wait-freedom: an explicit bound of 54 own steps per operation or `RECOVER` (`waitFree`), counting
  every hardware access.
* Not formalized: the space bound `O(m + n)` (Theorem 4.1(4)) — immediate from the data layout (two
  words per handle, two DurEC objects of two words each per object); dynamic joining (4.1(3)) is
  reflected by the arbitrary process type only.
