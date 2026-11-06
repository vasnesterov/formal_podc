# Differences between the formalization and the paper

Bushkov, Guerraoui, *Safety-Liveness Exclusion in Distributed Computing*, PODC 2015 (authors' full
version, EPFL Infoscience 207929).

## Model (Section 2)

1. **Composition.** `Impl` is the paper's `A_{I₁} × … × A_{Iₙ} × A_B`. All processes share one type of
   local states, and the process index is an argument of the transitions. A communication action
   between `A_{Iᵢ}` and `A_B` becomes a single internal step `step i` that changes both `i`'s local
   state and the base objects. This is the hidden shared action of the composition, and it counts as
   an action of `A_{Iᵢ}` for fairness. Internal actions of `A_B` are `base`.
2. **Crashes.** The crashed state `s_crashed,i` is `none`. Every local state other than `none` has the
   `crash i` transition, and nothing is enabled for `i` at `none`. This is as in the paper.
3. **Input-enabledness** (`Impl.InputEnabled`). Literally, the paper requires `inv_i` to be enabled
   at *every* state at which `pᵢ` is not pending, where "pending at `s`" means "reachable by some
   history in which `pᵢ` is pending". Read this way, two things go wrong:
   - `inv_i` must be enabled at all unreachable states. Enabledness of `inv_i` depends only on `pᵢ`'s
     local state, so with well-formedness this forbids essentially every non-trivial implementation.
   - `inv_i` must be enabled at the crashed state, which contradicts "no action is enabled".

   We require it per execution: if a finite execution's history leaves `pᵢ` idle (not pending, not
   crashed), every invocation of `pᵢ` is enabled at its last state. This is the evident intent (✏️).
4. **Initial states.** `Impl.Valid` requires an initial state. Without one, an implementation has no
   history at all and ensures every safety and liveness property, so nothing excludes anything and
   Corollaries 4.5, 4.6, 4.10, 4.11 fail. The paper implicitly assumes non-empty `init(A)`.
5. **Well-formedness** (`WF`, `U`). Per process, invocations and responses alternate starting with an
   invocation, a crash happens at most once, and nothing follows a crash. The paper defines
   well-formedness only for inv/res sequences and does not say what may follow a crash.
   - This matters for Theorem 4.9. The history in which all processes crash is fair for every
     implementation. With our `U` it has no proper extension, so the assumption on `Lmax` forces it into
     `Lmax`.
   - If events after a crash counted as "histories", one could take `Lmax` = wait-freedom minus this
     history. Then `Lmax ∪ {it}` would be the strongest non-excluded property, a degenerate failure of
     Theorem 4.9. We consider our reading the intended one.
6. **Reactive implementations** (`Impl.Reactive`): no `step i` is enabled while `pᵢ` is idle. This is
   *not* part of the paper's formal model, and Theorem 4.9 needs it (item 13).
7. **Histories** are finite lists or functions `ℕ → Ext` (`Hist`). The history of an infinite execution
   is the limit of the histories of its prefixes (`InfExec.HasHist`); it may be finite. Prefix- and
   limit-closure (Definition 3.1) are `PrefixClosed`, `LimitClosed`. The paper's limit of a strictly
   growing chain is equivalent given prefix-closure.
8. **Fairness** (`Impl.FinFair`, `InfExec.Fair`) is the paper's (§3.2), with "enabled" meaning enabled
   in the composition. Inputs count as actions of `A_{Iᵢ}`, so, as in the paper, a correct idle process
   with an enabled invocation must keep acting in a fair execution.
9. **Implementation classes.** "Implementations from read/write registers" (Corollaries 4.5, 4.10) is
   modelled as an arbitrary class `𝓒` of implementations. `theorem_4_9` assumes that `𝓒` contains the
   silent implementation and the responders, which use no base objects.

## Sections 3–4

10. **Order on liveness properties.** We use inclusion: `L₁` stronger than `L₂` iff `L₁ ⊆ L₂`. This is
    what all the paper's proofs use. The paper defines the order semantically and claims the two
    coincide. That is false for reactive implementations (`weaker_iff_subset_false`). For the general
    (non-reactive) class we did not settle it: with idle steps every well-formed history is fair for
    some implementation, so the easy counterexample disappears.
    - *Label: 🔧.* The intended order is the one used throughout; the "it is easy to see" remark is
      false.
11. **Liveness properties, complements.** A liveness property is any `L ⊇ Lmax` of the history type,
    and "complement" is the complement in that type. The paper takes complements within the
    well-formed histories. For adversary sets (`F ⊆ S ⊆ U`) this makes no difference. The weakest
    excluded property becomes `Gmaxᶜ` instead of `U \ Gmax`, and the two have the same members
    among the well-formed histories.
12. **Theorem 4.4.** It is proved abstractly (`Setting.theorem_4_4`) from two facts:
    - fair histories of implementations ensuring `S` lie in `S`, which follows from limit closure;
    - some implementation ensures `S`, which follows from `S ≠ ∅` and implementability.

    Without the second fact the remark "`L` excludes `S` iff there is an adversary set" fails, and so
    does Theorem 4.4. The paper's assumptions provide it. The intersection over an empty family is the
    whole type, and the theorem remains true then.
13. **Theorem 4.9.**
    - *Statement.* True for reactive valid implementations (`theorem_4_9`, any class containing the
      trivial implementations). False for the paper's general I/O-automaton model, even with `Lmax` =
      wait-freedom (`Counterexample.theorem_4_9_false_waitFree`). A simpler counterexample uses `Lmax`
      = all well-formed histories except `crash₁ · inv₀` (`Counterexample.theorem_4_9_false`).
    - *Counterexample.* The safety property `S` constrains crash events, which Definition 3.1 allows
      (histories are over `ext(Tp)`, which contains `crashᵢ`). It satisfies all the paper's
      assumptions (`S_assumptions`), including that every history of `S`, finite or infinite, is a
      history of an implementation ensuring `S`. The implementation `Is` is valid, and its base objects
      form one single-writer register written by `p₁`.
    - *Padding.* `A_B` of `Is` has a stuttering internal action, used only to build executions with
      blocks of three actions. Without it `Is` would also have finite fair executions, and they would
      have the same histories (`Y` or wait-free).
    - *Implied or new assumption (borderline; label ✏️).* Reactivity as a new assumption: the paper's
      formal model is explicit and allows process automata with internal actions at any time;
      heartbeat-style protocols are common; the proof's commutation claim is simply false without the
      assumption. Reactivity as an implied assumption: §2 says "when process `pᵢ` invokes `invᵢ` on `I`, it executes
      algorithm `Iᵢ` with `invᵢ` as an input", the standard shared-memory convention is that processes
      take steps only within operations, and every implementation in the paper is reactive.
    - *Why idle steps are essential.* In a reactive implementation, `p₀`'s steps read only `p₀`'s
      local state and the base objects, and `crash₁` changes only `p₁`'s local state. So any run
      `inv₀ · … · res₀` with `p₁` idle can be replayed after `crash₁`, giving `crash₁ · inv₀ · res₀ ∉ S`.
      No reactive implementation ensuring `S` has the history `inv₀ · res₀ ∈ S`, so `S` violates the
      paper's implementability assumption for reactive classes. The heartbeat is exactly what makes
      `S` admissible.
    - *Robust to the order.* The counterexample does not depend on reading "stronger" as `⊆`
      (item 10). `Is` ensures `WaitFree ∪ Y` but not `WaitFree` (it has the fair history `h₀`), so
      the two properties are not even equivalent under the paper's semantic order.
    - *Our call.* We judge reactivity to be an assumption a competent reader would make (✏️). The
      counterexample is fully checked either way.
    - *Independent review.* Confirmed. The counterexample meets every formal definition of §2–3:
      general I/O automata with internal actions, crash actions in `ext(Tp)`, the fairness of §3.2,
      the two assumptions on `S` of §3.1, and the assumption on `Lmax`. The formal model does not
      forbid idle steps, but it does not claim them either. "A general shared memory system" refers
      to the choice of base objects. The prose of §2 ("when `pᵢ` invokes `invᵢ` … it executes
      algorithm `Iᵢ` with `invᵢ` as an input; when executing `Iᵢ`, `pᵢ` performs steps") fixes the
      reactive convention. Theorem 4.9 is the first of the two results in the introduction, so
      everything rests on that reading.
14. **Proof of Theorem 4.9** (🔧 for the reactive statement):
    - "Consider history `inv_l · res_l ∈ S`" is unjustified. The specific `res_l` comes from
      `h · res_l ∈ S`, and `S` need not contain `inv_l · res_l` (consensus validity).
    - The final paragraph needs a correct invoking process in `h`, and the all-crashed case is missing
      (✏️; handled by item 5).
    - "By Lemma 4.8, `Ls = Lmax ∪ fair(A_Is)`" also needs that `Ls` is strongest; this is routine.
    - The repaired proof uses the characterization `Setting.isStrongestNonExcl_iff`
      (`Ls = Lmax ∪ core`). It chooses the response from the paper's sequential assumption *before*
      choosing the implementation `I'`, and uses the frame lemma `Impl.Run.frame`. The commutation
      holds only for reactive `I'`.
15. **`Nonempty Inv`.** `theorem_4_9` assumes at least one invocation. With no invocations the empty
    history is fair for every reactive implementation, and an `Lmax` omitting it makes Theorem 4.9
    fail. This is a degenerate case (✏️).
16. **Corollaries 4.5, 4.6, 4.10, 4.11** are formalized as schemes. The concrete inputs are cited
    impossibility results and enter as hypotheses:
    - for 4.5–4.6, two disjoint adversary sets w.r.t. `Lmax`;
    - for 4.10–4.11, "`Lmax` excludes `S`", for a class satisfying the hypotheses of `theorem_4_9`.

    The consensus adversary set `F₁` of the paper lists histories that are never fair. For `n ≥ 3` the
    other processes must crash in it. This is a typo-level imprecision.

## Section 5

17. **Summaries.** `(l,k)`-freedom is defined on `LK.Summary`: correct processes, processes with
    infinitely many steps, and processes making progress, with `prog ⊆ inf ⊆ correct`. Definition 5.1
    depends only on these three sets. The order between `(l,k)`-freedom properties is implication over
    all summaries. Non-inclusions are witnessed by summaries that real executions realize; the paper's
    own §5.1 example uses the same ones.
18. **Theorems 5.2, 5.3** take the cited (im)possibilities as hypotheses:
    - for 5.2: `(1,1)` is implementable [20, 17] and `(1,2)` is excluded [5];
    - for 5.3: `(1,n)` is implementable [9] and `(2,2)` is excluded [4].

    The rest is order theory on `(l,k)` with `1 ≤ l ≤ k ≤ n` and `n ≥ 2`. For `n = 1` the property
    `(1,2)` does not exist (degenerate).
19. **Progress for TM** (✏️). "Good responses are those which do not abort transactions" (§5.1),
    together with no exclusion of parasitic processes, makes the hypotheses of Theorem 5.3 false.
    - *Good = non-abort.* The TM that aborts every `tryC` and answers everything else is opaque and
      makes every correct process progress.
    - *Good = commit.* A correct process that never calls `tryC` violates every `(1,k)`-freedom.

    The intended reading (commits, non-parasitic processes as in [4]) is recoverable from §4. Not
    formalized (no TM model).
20. **§5.3 / Lemma 5.4** are not formalized beyond the order theory (`LK.section_5_3` takes
    "`(2,2)`, `(1,3)` exclude `S`" and "`(1,2)` does not" as hypotheses). Points noticed:
    - requirement 2 of `S` must read "none of them commits" to be prefix-closed;
    - the `(1,3)` adversary argument checks condition (2) only for the committing transaction. If the
      other two transactions were aborted at `start` they never invoke `tryC`, so under the literal
      reading ("each `Tᵢ` invokes `tryC` after …") the requirement does not apply. The argument needs
      the reading "each `Tᵢ` that invokes `tryC`";
    - in the `(1,2)`-freedom proof of Lemma 5.4, aborts caused by frozen timestamps of crashed
      processes disappear only once the live processes' timestamps exceed them; the proof skips this
      routine point;
    - the same TM-progress caveat as item 19 applies.
21. **§5.1 remark** "`LF_l ∪ OF_k` is the set of `(l,k)`-free executions" is false (`LK.lf_union_of_not_iff`):
    only `(l,k)`-free ⊆ `LF_l ∪ OF_k` holds (`LK.lkFree_imp_lf_or_of`). The remark is unused (🔧).
