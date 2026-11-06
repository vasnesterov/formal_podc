# Differences between the formalization and the paper

Paper: K. Censor-Hillel, E. Petrank, S. Timnat, *Help!*, PODC 2015. We use the full version, Chapter 4 of S. Timnat's
PhD thesis (Technion, 2015), and its numbering (Definitions 4.4.x, 4.5.1, Claims 4.5.x, Theorems 4.3, 4.7, 4.8, 4.11).

The PODC extended abstract (author copy) was checked as well. The PODC numbering maps to the thesis as follows:
Definitions 3.2/3.3 → 4.4.2/4.4.3, Observation 3.4 → 4.4.4, Claim 3.5 → 4.4.5, Definition 4.1 → 4.5.1, Claims
4.2/4.3 → 4.5.2/4.5.3, Remark 4.4 → the remark after 4.5.3, Claims 4.5–4.16 → 4.5.4–4.5.14 (Claim 4.11 → 4.5.10,
Corollary 4.12 → Corollary 4.1), Theorem 4.18 → Theorem 4.3, Theorem 5.1 → Theorem 4.8, Claim 6.1 → 4.8.1, Figures 3/4
→ 4.4/4.5. The PODC version states the same Definition 4.1 (∃ one operation of `R(m)` differing on all pairs), the
same stack claim (Section 1.1: "Natural examples of exact order types are FIFO queues and LIFO stacks"; after
Definition 4.1: "Examples of such types are a queue, a stack, and the fetch-and-cons"), and the same proof of Claim
4.11 (= 4.5.10) with Remark 4.4 ("(3.) is not needed in the proof"). It states Theorem 5.1 ("A global view type has no
linearizable, wait-free, help-free implementation") without defining global view types, lists "snapshot objects,
increment objects, and fetch&add" and "a fetch&increment object" as global view types (Section 1.1), and defers the
definition and the proof to the full paper; the read/write max-register result (Theorem 4.11) is claimed in Section
1.1 ("Theorems 4.18, 5.1 (rephrased)") with the proof deferred. So every statement-level finding below applies to the
PODC paper as published.

## Statement-level issues

1. **"The stack is an exact order type" is false** (examples after Definition 4.5.1; also Section 4.1 "exact order
   types (examples are the queue and the stack)" and Section 4.5.1). For every `op, W, R, n, m` there are
   sequences in `W(n+1) ∘ (R(m) + op?)` and in `W(n) ∘ op ∘ (R(m) + W_{n+1}?)` on which all of `R(m)` return the same
   results (`stack_exists_equal`, `stack_not_exactOrder`, `stack_not_exactOrderStrong`, `Examples.lean`; the argument
   is Theorem 1 of Aksenov–Kuznetsov–Shalyto, *On Helping and Stacks*, NETYS 2018). The definition allows *moving* `W_{n+1}` into `R(m)`, and a LIFO
   stack can hide the swap: e.g. for `op = push(a)`, `W_{n+1} = push(b)`, re-insert `push(b)` right after the pop
   that removes `a`. The conclusion drawn for stacks (no wait-free help-free stack) is nevertheless true (Aksenov et
   al. prove it directly); only the classification is wrong (❌). The definition is the
   paper's own and is used as stated.
2. **Theorem 4.3 holds** (`theorem_4_3_helpFree`, and the stronger `theorem_4_3`); its proof needed repairs (below).
3. **The queue is an exact order type** (`queue_exactOrderStrong`), with the paper's witnesses.
4. **Claim 4.8.1** holds under hypotheses the paper leaves implicit: the linearization function is built
   incrementally (each step appends at most its own operation; `LinPointFun`), the implementation is
   obstruction-free, and every process may invoke some operation (needed to run the owner of a *future* operation
   solo). These hold in every use in the paper (✏️). Figures 4.4 and 4.5 are wait-free,
   linearizable and help-free (`set_helpFree_waitFree`, `maxRegister_helpFree_waitFree`).
5. **Theorem 4.8 (global view types) is unestablished as stated; proved for strong global view types.** Gap in
   Claim 4.6.8 (see "Proof gaps" 4). We prove it for `StrongGlobalView` (the four result classes — none, `op` only,
   the next modifier only, both — are pairwise disjoint), which covers snapshots (`theorem_4_7`) but not
   fetch&increment (`fetchInc_globalView`, `fetchInc_not_strongGlobalView`) nor increment objects, which the paper
   explicitly lists as covered ("this way the proof also holds for an increment object"; "the fetch&increment type
   … the fetch-and-cons object … satisfies the condition in theorem 4.8"). Theorem 4.8 covers one of
   the two families of types requiring help; it is only *unestablished*, not refuted (⚠️).
6. **Theorem 4.7** is proved for snapshot implementations that are correct in all executions (multi-writer,
   multi-scanner; every process may invoke every operation). The paper's single-scanner, single-writer snapshot
   restricts scans to one process at a time and each component to its owner, so it allows more implementations; that
   stronger version is not formalized.
7. **Theorem 4.11 (max register from read/write) — proof gap, not repaired.** See "Proof gaps" (3). The theorem is not
   formalized (❌).

## Definitions and modelling choices

- **Model.** CSLib asynchronous shared memory (`Cslib.SharedMemory`): deterministic processes, executions are label
  lists; an invocation and a response are separate labels (`inv`, `ret`) besides base-object steps (`tau`). The paper
  couples the first primitive step with the invocation and the last with the result. Finer steps only add
  intermediate histories; all arguments go through (e.g. in Claim 4.5.10 an invocation or response step changes no
  memory and is excluded like a read).
- **The set of histories `H`** = all finite valid executions of the implementation with arbitrary invocations (all
  operations allowed for all processes, hypothesis `hall`). The paper's `H` also contains infinite histories, but it
  never defines linearizations of infinite histories; decided-before quantifies over finite extensions.
- **Operation instances** are `OpId = P × ℕ` (`(p, k)` = `k`-th operation of `p`), so operations not yet invoked have
  names (the paper speaks of "future operations").
- **"`op₂ ≺ op₁` in `f(s)`" when `op₁` is missing from `f(s)`** (linearizations may omit pending operations): we
  read it as true (`Prec`: missing operations come after all others). This is the reading the paper's own proofs
  use: Claim 4.8.1 ("a solo execution of the owner of `op₂` until the linearization of `op₂` would have linearized
  `op₂` before `op₁`", with `op₁` not linearized) and Claim 4.5.2 ("somewhere before them it must also include
  `op₁`", which follows only if `op₁` decided before `op₃` forces `op₁` into `f(s)`). With it, decided-before is
  transitive (`DecidedBefore.trans`).
- **"`γ` is a step in the execution of `op₁` by its owner"** = `curOp h γ.proc = op₁` (the current instance of the
  stepping process; for an invocation, the instance it starts).
- **Weak help-freedom.** The impossibility theorems are proved for `OwnerOnlyWith` (the deciding step is taken by the
  owner, possibly inside another of its operations), which is implied by the paper's help-freedom
  (`HelpFree.weaklyHelpFree`); the results are therefore stronger than stated.
- **Exact order types (Definition 4.5.1).** The paper: "for at least one operation in `R(m)`, the result it returns in
  any execution in A differs from the result in any execution in B" (∃ operation ∀ pairs) = `ExactOrderStrong`. We
  prove Theorem 4.3 for the weaker `ExactOrder` (∀ pairs ∃ operation, the form of Aksenov et al.), i.e. for a larger
  class (`ExactOrderStrong.exactOrder`). The stack fails both. `R` is an infinite sequence; a finite `R` can be padded,
  only prefixes `R(m)` matter. Sequences are tagged to know which results belong to `R(m)` (`taggedResps`).
- **Global view types (Definitions 4.6.16–4.6.18)** are stated on tagged sequences (`op`, `mod k`, `view k`), since
  the operations may coincide (for fetch&increment they are all equal): `gvSet i j o m` = interleavings of the first
  `i` modifiers (plus the `(i+1)`-st iff `m`) and the first `j` views in order, plus `op` iff `o`, ending with a view.
- **Base objects** of Theorems 4.3, 4.7, 4.8: registers supporting read, write and cas (CSLib `casObject`, one per location,
  arbitrary value type per location; `cas` returns a success flag, `write` an acknowledgement).
- **Number of processes.** Theorem 4.3 is stated for systems with three distinct processes `p₁ p₂ p₃` (other
  processes may exist), as in the proof ("Consider a system of three processes"); the paper's theorem statement does
  not mention it.
- **Progress.** The paper assumes lock-freedom inside the proof "for convenience"; we use CSLib's `WaitFree` directly
  (a process pending forever takes finitely many steps), and solo runs complete by wait-freedom.
- **Figure 4.5** uses natural numbers instead of `int` (initial value 0); **Figure 4.4** works for any key type.

## Proof gaps and repairs

1. **Claim 4.5.10 (next steps of `p₁`, `p₂` are cas to the same location).** The paper excludes a read and a cas that
   does not change memory using only Claim 4.5.3 (1) (`h∘p₁∘p₂` vs `h∘p₂∘p₁`). This fails when `p₁`'s cas fails at `h`
   but `p₂`'s step writes the expected value: then `p₁`'s cas succeeds in `h∘p₂∘p₁` and the two histories differ. Repair:
   compare `h` with `h∘p₁` (resp. `h∘p₂`), which agree on memory and on the other processes if the step changes no
   memory, and apply Claim 4.5.3 (2) (resp. (3)) (`claim_4_5_3_2`, `claim_4_5_3_3`, used in `Ctx.claim_4_5_10`). So the
   Remark "(3) is not needed in the proof" is wrong: (3) is needed (🔧).
2. **Claim 4.5.13** says the failed cas "contradicts Claim 4.5.3 (2)", but 4.5.3 (2) is about `op₁` vs `op₂`, whereas
   4.5.13 is about `op₁` vs `op₃`. We use 4.5.3 (2) at level `n + 1` for `op₁` vs the next operation of `p₂`, with
   Claim 4.4.5 to move between `op₃` and that operation (`critical_step`) (🔧).
3. **Theorem 4.11, Claim 4.7.1, second case for line 4 (and line 7).** "If `R₁` cannot possibly return a value `≥ 3`,
   then `R₁` is decided before `W₃`" is invalid for a *pending* `R₁`: a linearization function may leave a pending
   read out of the linearization until it returns, so `R₁` is not decided before `W₃` although its result is fixed.
   Lean witness on the help-free max register of Figure 4.5 with such a linearization function `lin'`:
   `claim_4_7_1_inference_fails` (`MaxRegGap.lean`). Once `R₁` returns, `R₁` *is* decided before `W₃`, but that
   decision is made by `R₁`'s owner, which help-freedom allows, so the intended contradiction is lost. We found no
   repair; the status of Theorem 4.11 is open in our formalization. (The case for line 10/13 is fine: there the
   reader `R₂` has completed.) A claim inside a proof of a non-formalized theorem (❌).
4. **Claim 4.6.8 (Theorem 4.8).** From "`op₁` decided before `op₃` in `h∘p₁∘p₃`, not in `h∘p₃∘p₁`" the paper concludes
   that `op₃` returns different results after a solo run of `p₃` ("because each operation by `p₁` changes the return
   value of `op₃`"). With the three classes of Definition 4.6.18 both results may lie in `RS1` (`op₁ ≺ op₃ ≺ op₂`
   versus `op₂ ≺ op₃ ≺ op₁`). The same step excludes reads and failed cas, and the exclusion of writes asserts without
   justification that `op₂` is not before `op₃` in the `p₁`-first run. Repaired only under `StrongGlobalView`: then
   whether `op₁`/`op₂` is decided before a view depends only on memory and `p₃` (`Ctx.kl`); reads and failed cas are
   excluded by comparing `h` with `h∘p₁` (as in item 1), writes by help-freedom (`Ctx.caseA`).
5. **Claim 4.6.12.** "`op_k` is not decided before `op_j` (because `op_j` may still be before `op₃`, which in turn may
   still be before `op_k`)" uses two different extensions; non-decidedness is not transitive. Repaired by changing
   the construction: if `p_k`'s step at line 25 would decide `op_k` before the next view, the next steps of `p₁` and
   `p₂` are competing successful cas on one location (`Ctx.race`, `Ctx.bbad`) and lines 17–20 are performed instead
   (`Ctx.cas_move`); otherwise line 25 is harmless (`Ctx.good_move`).
6. **Claim 4.6.2** needs Claim 4.4.5 for operations not yet started (`claim_4_4_5'`).
7. **Observation 4.4.4 (2) and Claim 4.4.5** silently use that the owner of an operation can run solo to completion
   (wait-/lock-freedom) and can invoke operations; formalized with these hypotheses (`not_decidedBefore_cur`,
   `claim_4_4_5`). Claim 4.4.5 is stated for "any future operation"; we prove it for every operation not invoked yet
   other than the current one of the process run solo.
8. **Claim 4.5.2's hypothesis** "the first `n` operations are already decided to be the first `n` operations of `p₂`"
   is formalized as `Std n h`: `p₂` completed `W(n)`, each decided before `op₁`, `p₂` invoked at most `W(n+1)`, `p₁` at
   most `op`, `p₃` and the other processes nothing. Its proof is formalized through `shape` (structure of any
   linearization) and `core`.

## Not formalized

- Section 4.5.1 (extension of Theorem 4.3 to fetch&add; the paper gives a sketch) and Definition 4.5.15.
- Theorem 4.11 (see gap 3).
- Theorem 4.8 for non-strong global view types (fetch&increment, increment); the single-scanner version of Theorem 4.7.
- Section 4.9 (universality of fetch-and-cons; needs composition of implementations, absent from CSLib).
- The intuitive discussion of Herlihy's universal construction (Section 4.4.2).
