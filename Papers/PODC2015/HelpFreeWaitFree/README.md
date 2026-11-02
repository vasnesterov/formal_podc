# Help! — PODC 2015

Keren Censor-Hillel, Erez Petrank, Shahar Timnat. *Help!* PODC 2015. DOI
[10.1145/2767386.2767415](https://doi.org/10.1145/2767386.2767415). Formalized version: the full version, Chapter 4 of
S. Timnat's PhD thesis (Technion, 2015) — no arXiv version exists; numbering (Definitions 4.4.x, 4.5.1, Claims 4.5.x,
Theorems 4.3, 4.7, 4.8, 4.11) follows the thesis. All findings below were checked against the PODC extended abstract
too (author copy, 10 pp.); its numbering: Definitions 3.2/3.3 = 4.4.2/4.4.3, Observation 3.4 = 4.4.4, Claim 3.5 =
4.4.5, Definition 4.1 = 4.5.1, Claims 4.2/4.3 = 4.5.2/4.5.3 (Remark 4.4 = the thesis remark on (3)), Claim 4.11 =
4.5.10, Theorem 4.18 = Theorem 4.3, Theorem 5.1 = Theorem 4.8 (Section 5 only sketches the single-scanner snapshot
case and defers the definition of global view types and the proof to the full paper), Claim 6.1 = 4.8.1, Figures 3/4
= 4.4/4.5. Theorem 4.11 appears in the PODC version only as a claimed result (Section 1.1 and Section 6.2), with the
proof deferred to the full paper.

**Verdict: ❌ False claim.** The claim that the stack is an exact order type (stated in the PODC version too) is
false, as V. Aksenov, P. Kuznetsov and A. Shalyto observed (*On Helping and Stacks*, NETYS 2018); a wait-free
help-free stack is still impossible by their direct proof. Theorem 4.3 (no
wait-free, linearizable, help-free implementation of an exact order type, e.g. a queue, from read/write/cas) holds
after a repair of Claim 4.5.10. Theorem 4.8 (global view types) is proved only when a view tells *which* competing
operations precede it: this covers snapshots (Theorem 4.7), but for fetch&increment and increment, claimed by the
paper, its proof has a gap. Claim 4.8.1 and the help-free wait-free set and max register hold. The proof of Theorem
4.11 (read/write max registers) has a gap we could not repair.

## Mistakes in the paper

### ❌ Examples after Definition 4.5.1 (the stack is an exact order type)
The stack is not an exact order type: a stack can hide the swap of `op` and `W_{n+1}`, so no
operation of `R(m)` tells the two executions apart (`stack_exists_equal`, `stack_not_exactOrder`,
`stack_not_exactOrderStrong`).

**Impact.** Theorem 4.3 therefore says nothing about stacks; the conclusion "no wait-free help-free
stack" remains true by the direct proof of V. Aksenov, P. Kuznetsov and A. Shalyto (*On Helping and
Stacks*, NETYS 2018), who observed the error. A false statement about an example; the queue is an
exact order type and Theorem 4.3 holds.

**Details.** The claim appears after Definition 4.5.1, in Sections 4.1 and 4.5.1, and in the PODC
version ("Natural examples of exact order types are FIFO queues and LIFO stacks" in Section 1.1 and
"Examples of such types are a queue, a stack, and the fetch-and-cons" after Definition 4.1). Exact
order types must tell apart *every* execution of `W(n+1) ∘ (R(m) + op?)` from every execution of
`W(n) ∘ op ∘ (R(m) + W_{n+1}?)` by the results of `R(m)`. Since `W_{n+1}` may be *moved* into
`R(m)`, a stack can hide the swap. For example, with `op = push(a)` and `W_{n+1} = push(b)`, compare
`W(n)∘push(b)∘push(a)∘R(m)` with `W(n)∘push(a)∘R(m)` where `push(b)` is re-inserted right after the
pop that removes `a`: all operations of `R(m)` return the same values. The other three
op/`W_{n+1}` cases are similar. This holds for every choice of `op, W, R, n, m`, so the stack is
not exact order in the paper's literal form nor in the weaker form.

### ❌ Theorem 4.8 for global view types as defined (fetch&increment, increment)
The proof of Theorem 4.8 (Claim 4.6.8) needs a view to tell *which* competing operation precedes
it, but Definition 4.6.18 only tells *how many*, so the paper's claimed instances fetch&increment
and increment are not covered (`fetchInc_not_strongGlobalView`).

**Impact.** Unestablished, not refuted: we have no counterexample. We prove Theorem 4.8 for *strong*
global view types (`theorem_4_8`), which covers snapshots (Theorem 4.7, `theorem_4_7`), but not
fetch&increment (`fetchInc_globalView`) or increment, which the paper explicitly claims.

**Details.** Definition 4.6.18 only requires a view's result to tell *how many* of `op₁` and the
next modifier `op₂` precede it, and the paper stresses that the proof "relies only on" this, so that
it covers increment and fetch&increment objects. But Claim 4.6.8 infers from "`op₁` is decided
before `op₃` in `h∘p₁∘p₃` but not in `h∘p₃∘p₁`" that a solo run of `p₃` returns different results
in the two histories. With three result classes both may fall in the middle class:
`op₁ ≺ op₃ ≺ op₂` in one, `op₂ ≺ op₃ ≺ op₁` in the other (for fetch&increment both views return the
same count). The same inference is used to exclude reads, failed cas and writes.

**Repair.** We prove Theorem 4.8 for *strong* global view types, where the view also tells *which*
operation precedes it. Snapshots are such types, so Theorem 4.7 holds (for snapshot implementations
correct in all executions). (`theorem_4_8`, `theorem_4_7`, `Ctx.caseA`)

### ⚠️ Theorem 4.11 (read/write max registers): unestablished
The proof (Claim 4.7.1, second case for lines 4/7) infers "`R₁` cannot possibly return a value
`≥ 3`, hence `R₁` is decided before `W₃`" for a *pending* `ReadMax` `R₁`, which is invalid
(`claim_4_7_1_inference_fails`).

**Impact.** We found no repair; whether Theorem 4.11 holds is open here. It is not formalized and
does not enter the verdict.

**Details.** A linearization function may leave a pending read out of the linearization until it
returns, so `R₁` is not decided before `W₃` although its result is fixed. Once `R₁` returns, it is
decided before `W₃`, but that decision is taken by `R₁`'s owner, which help-freedom allows, so the
intended contradiction disappears. Lean witness on the help-free CAS max register of Figure 4.5:
after `R₁` reads 0 and then `WriteMax(3)` completes, every extension makes `R₁` return 0, yet `R₁`
is not decided before `W₃` for a valid linearization function. (`claim_4_7_1_inference_fails`)

### Typos and slips
- Claim 4.8.1 needs that the linearization grows only by appending, that the implementation is
  obstruction-free and that processes can invoke operations (all true in the paper's uses).
- Observation 4.4.4 (2) and Claim 4.4.5 silently use solo termination.
- Claim 4.5.13 cites Claim 4.5.3 (2), but needs it for the *next* competition (`op₁` vs
  `W_{n+2}`), reached via Claim 4.4.5.
- "`op₂ ≺ op₁` in `f(s)`" is not defined when `op₁` is missing from `f(s)`. The paper's own proofs
  (Claims 4.5.2, 4.8.1) need it to count as true, and we use this reading.

## Proof gaps (statements true)

### 🛠️ Claim 4.5.10 (Theorem 4.3: eliminating reads and failed cas)
At the critical point the paper rules out that `p₁`'s next step is a read or a cas that changes
nothing by comparing `h∘p₁∘p₂` with `h∘p₂∘p₁` (Claim 4.5.3 (1)), but a cas of `p₁` that fails at
`h` may *succeed* after `p₂`'s step.

**Impact.** Statement true; repaired, and Theorem 4.3 is proved as stated, in fact for a weaker
notion of help-freedom (`Ctx.claim_4_5_10`, `theorem_4_3`).

**Details.** If `p₂` writes the expected value, `p₁`'s cas succeeds in `h∘p₂∘p₁`, and then the two
histories differ.

**Repair.** Compare `h` with `h∘p₁`, which `p₂` and `p₃` cannot tell apart, and use Claim 4.5.3
(2); symmetrically for `p₂` with Claim 4.5.3 (3). So the remark "(3) is not needed in the proof" is
wrong. Theorem 4.3 is proved for weak help-freedom: the deciding step must be taken by the owner of
the operation, not necessarily inside it. (`Ctx.claim_4_5_10`, `theorem_4_3`)

### 🛠️ Claim 4.6.12 (Theorem 4.8: `op_k` not decided before `op_j`)
"`op_k` is not decided before `op_j`, because `op_j` may still be before `op₃`, which may still be
before `op_k`" combines two different extensions and is unjustified.

**Impact.** Repaired by changing the construction, within our proof of Theorem 4.8 for strong
global view types (`Ctx.cas_move`).

**Repair.** When `p_k`'s step at line 25 would decide `op_k` before the next view, the next steps
of `p₁`, `p₂` are competing successful cas, and lines 17–20 are applied instead. (`Ctx.cas_move`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* CSLib asynchronous shared memory: deterministic processes, no crashes, adversarial scheduler, no randomness.
  Executions are label lists (`inv`, base-object step `tau`, `ret`). The set of histories `H` is the set of all finite
  executions with arbitrary invocations. Operation instances are `(process, index)`, which also names future
  operations.
* Help (Definitions 4.4.1–4.4.3): `DecidedBefore I f h a b` (no finite extension `s` has `b ≺ a` in `f (h ++ s)`,
  with operations missing from `f (h ++ s)` counted as last) and `HelpFree I`. Impossibility results are proved for
  the weaker `WeaklyHelpFree I` (the deciding step is taken by the owner), so they are stronger than the paper's.
* Theorems 4.3, 4.7, 4.8: base objects are read/write/cas registers (`casObject`, any value type per location), wait-freedom is
  CSLib's `WaitFree`, there are at least three processes, and every process may invoke every operation.
* Exact order types: `ExactOrderStrong` is the paper's literal Definition 4.5.1 and `ExactOrder` the weaker form of
  Aksenov et al. (`ExactOrderStrong.exactOrder`). Theorem 4.3 is proved for the weaker form, i.e. for more types.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 4.4.2, 4.4.3 | `DecidedBefore`, `HelpFreeWith`, `HelpFree`, `WeaklyHelpFree` | `Defs.lean` |
| Observation 4.4.4 | `decidedBefore_of_completed`, `Ctx.not_decidedBefore_cur` | `Defs.lean`, `Claims.lean` |
| Claim 4.4.5 | `Ctx.claim_4_4_5` | `Claims.lean` |
| Definition 4.5.1 | `ExactOrderStrong`, `ExactOrder` | `ExactOrder.lean` |
| queue is exact order | `queue_exactOrderStrong` | `Examples.lean` |
| stack is exact order (**false**) | `stack_exists_equal`, `stack_not_exactOrder`, `stack_not_exactOrderStrong` | `Examples.lean` |
| Claims 4.5.2, 4.5.3 (1)–(3) | `Ctx.claim_4_5_2`, `Ctx.claim_4_5_3_1`, `_2`, `_3` (core: `shape`, `Ctx.core`) | `Claims.lean`, `Shape.lean`, `Setting.lean` |
| Claims 4.5.7, 4.5.8 (inner loop) | `Ctx.Std.undecided`, `Ctx.loop_terminates` | `Loop.lean` |
| Claim 4.5.10, Corollary 4.1 | `Ctx.claim_4_5_10` | `Theorem43.lean` |
| Claims 4.5.11–4.5.14 | `Ctx.critical_step` | `Loop.lean` |
| Theorem 4.3 | `theorem_4_3` (weak help-freedom), `theorem_4_3_helpFree` | `Theorem43.lean` |
| Theorem 4.3 for queues | `queue_not_waitFree_helpFree` | `Theorem43.lean` |
| Definitions 4.6.16–4.6.18 | `gvSet`, `RS0`, `RS1`, `RS2`, `GlobalView`; stricter `StrongGlobalView` | `GVDefs.lean` |
| Theorem 4.8 (for strong global view types) | `theorem_4_8`, `theorem_4_8_helpFree` | `Theorem48.lean` (with `GVShape`, `GVClaims`, `GVCas`, `GVLoop`) |
| Theorem 4.7 (snapshot) | `snapshot_strongGlobalView`, `theorem_4_7` | `GVSnapshot.lean` |
| fetch&increment is a global view type | `fetchInc_globalView` (but `fetchInc_not_strongGlobalView`) | `GVDefs.lean` |
| Claim 4.8.1 | `claim_4_8_1`, `helpFree_of_linPointFun` | `LinPointHelpFree.lean` |
| Figure 4.4 (set) | `SetImpl.set_helpFree_waitFree` | `Set.lean` |
| Figure 4.5 (max register) | `MaxRegister.maxRegister_helpFree_waitFree` | `MaxRegister.lean` |
| gap in Claim 4.7.1 (Theorem 4.11) | `MaxRegister.claim_4_7_1_inference_fails` | `MaxRegGap.lean` |

**Not formalized.** Theorem 4.8 for (non-strong) global view types and its fetch&increment/increment instances, the
single-writer, single-scanner restriction of Theorem 4.7 (we prove it for multi-writer, multi-scanner implementations, a smaller class), Theorem 4.11 (proof gap above), Section 4.5.1 (fetch&add extension, only sketched in the paper),
Section 4.9 (universality of fetch-and-cons; CSLib has no composition of implementations).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: the hypotheses of Theorem 4.3 are met by the queue (`queue_exactOrderStrong`), and help-freedom is
satisfiable (the set and max register implementations). Generic pieces that could go to CSLib: `false_of_starving_chain`
(`Starvation.lean`: a chain where a process takes unboundedly many steps and never returns contradicts
wait-freedom) and `isLinearization_filter` (`MaxRegGap.lean`).
