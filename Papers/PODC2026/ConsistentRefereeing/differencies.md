# Differences between the formalization and the paper

Paper: Attiya, Castañeda, Enea. *Impossibility Results for Strong Linearizability: The Difficulty of
Consistent Refereeing.* PODC 2026 (arXiv 2506.18401 v3, identical text). Classification in brackets.

## Model (all sections)

1. **Model.** CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): deterministic
   processes, atomic base objects with deterministic sequential specifications, executions = label lists
   (invocation / internal step / response). Responses are separate steps that do not access memory
   (harmless generalization). No crashes are modelled explicitly; a crashed process is one that stops
   taking steps, which the progress conditions on infinite executions cover. [modelling choice]
2. **Caller identity.** Objects cannot see the caller, so `compete` carries the caller's id
   (`ContestOp.compete i`, invoked by `i`); roles are enforced by the admissible executions and the
   implementation must allow the role operations (`hallow`). [modelling choice]
3. **Restricted hypotheses.** For the one-shot contest object, strong linearizability and lock-freedom
   are only assumed on *admissible* executions (`Adm`: each process invokes at most once, the operation of
   its role, the referee only after some `compete` completed — exactly the executions the proof of
   Theorem 5 considers). For the long-lived contest object, on executions where competitors only invoke
   `compete` and the referee invokes `decide` at most once (`LLAdm`). These are weaker hypotheses than the
   paper's, so the impossibilities are stronger; versions for the unrestricted notions are derived.
   [strengthening]
4. **Classes of base objects.** Instead of concrete objects we use semantic classes: Herlihy's
   *interfering* objects (per state: any two operations commute or one overwrites the other),
   *window-like* objects with window `w` (every operation is read-only or a blind write, any `w`
   consecutive non-read-only operations determine the state; `w`-window registers are window-like with
   any `w' ≥ w`), *stack-like* objects (isomorphic to a stack). `windowObj`, `stackObj` and registers are
   proved to belong to them. [generalization]

## Section 3–4 (one-shot contest, queues)

5. **Theorem 5: wait-free vs lock-free.** The statement of Theorem 5 says "no wait-free"; the abstract
   intro ("no lock-free", Section 1), Corollary 12 and the proof only use lock-freedom (and the proof's
   "due to wait-freedom" in Claims 6 and 10 needs only lock-freedom, since operations are one-shot). We
   prove the lock-free version and derive the wait-free one. On one-shot (admissible) executions the two
   notions coincide (finitely many operations), so the paper's two phrasings agree; `theorem5_lockFree`
   is stronger only for the unrestricted notions of our multi-shot model. [not an error; modelling remark]
6. **Theorem 5, stack case (4b/4c): "w.l.o.g. pushed values are distinct".** The paper modifies the
   algorithm by stamping pushed values (footnote 3: "does not affect A's correctness and progress
   properties"). Our proof needs no such assumption: it runs the canonical extension of `α·i·j` and of `α·j`
   in lock-step, tracking stack *positions*; at the first pop into the critical part the configurations
   `α·i·j·β·q` and `α·j·β·q·i` are literally equal. The paper's case split (i)–(iii) on what `p_k` and
   `p_0` pop is replaced by this single argument. Footnote 3 (stamping) is a standard, sound w.l.o.g.;
   we avoid it only because stamping is awkward for our semantic class of stack-like objects.
   [formalization route; the paper's step is fine]
7. **Theorem 5, case 4c description** ("conceive the next step of `p_i` as a push of `u_i`", `u_i` the top
   of `R` in `p_i(C)`) is hand-wavy: the two orders of the pop and the push leave `u_j·T` and `s₀·T`
   (`s₀·T` the stack in `C`), not the shapes of case 4b. Covered by the argument of item 6.
   [imprecise proof, statement true]
8. **Claim 10** also has to handle steps that are invocations or responses (the paper's processes take
   "steps" that may be invocations of `compete`); they do not change the memory and are handled like
   reads (case 3a). The case "both steps write the same window register" requires showing that every
   other competitor writes to it too; the paper does this via cases 1 and 3a, we via the full pair
   analysis (also covering interfering objects and stacks). [detail]
9. **Proposition 11.** The paper's "due to strong linearizability we can assume that `A` is an atomic
   base object" is a composition theorem not available in our framework; we prove the reduction
   concretely by translating executions label by label. The resulting contest implementation is
   wait-free only on one-shot executions, and its strong linearizability needs the referee to decide at
   most once; the reduction needs an injective encoding of process ids as queue values and the queue
   must allow those operations. The contest object is one-shot by definition (Section 4), so this is the
   paper's setting. [not an error; restriction needed only because our model is multi-shot]
10. **Theorem 4.** If competitors may invoke `compete` repeatedly, the paper's algorithm (write on every
    `compete`) overflows the `(n−1)`-window. Our implementation writes only on the first `compete` of
    each competitor (a persistent local bit), and is then strongly linearizable on *all* executions. The
    hypothesis `n ≥ 2` is not needed. On one-shot executions our algorithm coincides with the paper's;
    the contest object is one-shot by definition, so the paper's claim is correct as stated.
    [not an error; strengthening]
11. **Theorem 3.** We prove wait-freedom and linearizability for executions in which the referee decides
    at most once; with two `decide`s the algorithm is not linearizable. Decisive linearizability is not
    defined in our framework and is not formalized. (Two `decide`s are outside the paper's one-shot
    object.) [not formalized: decisive linearizability]
12. **Theorem 1** is obtained as a special case of Corollary 12 (base objects all interfering); its own
    proof (three enqueuers, one dequeuer) is not formalized separately. Through this route Theorem 1
    (like Corollary 12) assumes an injective encoding `P → V` of process ids as queue values, i.e. at
    least `n` values; the paper's own proof of Theorem 1 needs only 3. [route; slightly weaker]

## Section 5 (long-lived contest)

13. **Model.** Competitors-only extensions are schedules (`List P` / `ℕ → P`): in an admissible
    execution every process has at most one possible next label, so nothing is lost.
    Indistinguishability is agreement of the final configurations (memory, local state and pending
    operation of the observers, CSLib's `AgreeOn`). Invocations and responses are steps that do not
    access memory; the paper's case analyses (Lemmas 20, 23, 27, 28, Theorems 25, 30) omit them, ours
    treat them (like reads or as commuting steps). [under-specified case analyses]
14. **Long-lived contest specification** is nondeterministic (`decide` may return any `x` bounding all
    competitors' counts): `llSpec`, strong linearizability w.r.t. a nondeterministic specification
    (linearizations carry responses). [faithful]
15. **Lemma 17** needs `decide` to be pending in `α` (with configuration-based indistinguishability);
    in its proof the operations of `q` must be counted inside `β'` (`α'` may contain a different
    number of operations of `q`). [under-specified / proof detail]
16. **Lemmas 19, 22, 24, 28, 29: "due to wait-freedom"** means: in an infinite competitors-only
    extension some competitor is scheduled infinitely often and so completes infinitely many
    operations (`resps_unbounded`). [proof detail]
17. **Theorem 25, last paragraph** ("We have that αβp is closed. Otherwise, if … contradicting Lemma
    24(1)") is garbled; the intended argument (Lemma 23 contradicts Lemma 24(1) unless every competitor
    writes `R` and the referee reads `R`) is formalized. [typo-level]
18. **Theorem 30, case "all processes T&S the same object R": proof gap, statement true.** The paper
    claims that `αβγpγ′₁q′ᵏγ′₂` and `αβγ′₁q′ᵏγpγ′₂` have the same shared memory and are
    indistinguishable to any `q″ ≠ q, q′`. If `R` is still unset after `αβ`, `q` wins the test&set in
    the first execution and `q′` in the second; the `k` further steps of `q′` (and those of `γ′₂`)
    may then write different values elsewhere, which `q″` can read. Fixed by a new argument
    (`const_valency_contra`): once a competitor has set `R`, every later step of the referee on `R`
    leaves the memory unchanged and commutes with every competitor step, so by Lemma 17 the singleton
    valency `W(αβq·u·p)` does not depend on the competitors-only extension `u`; choosing `u` in which a
    competitor completes more than that value contradicts the specification. Lemma 29(2) is not
    needed for this case. [proof gap, statement true]
19. **Lemma 28, test&set case:** "αβq and αβq′ are closed" — `αβq′` is supervalent there; only `αβq`
    needs to be closed. **Lemma 29:** the last line cites Lemma 21 instead of 27. [typos]
20. **Lemma 29(2) for `w = 0`:** the required sequences (`|γ| = w`, `γ = qλ`) do not exist; we use
    window `max w 1` (a 0-window object is also 1-window-like). [false only in a degenerate case]
21. **Generality.** Theorem 25 holds for any base objects whose primitives are read-only or blind
    writes; Theorem 30 for any window-like (window `w`) and test&set-like objects (every primitive
    sets the object to a fixed state; readable test&set is not covered, as in the paper). [generalization]
22. **Lemma 14** is formalized for an atomic counter, max register and snapshot (the long-lived contest
    is implemented from one atomic object); the fetch&increment-only / fetch&add variants and the
    "from a strongly linearizable implementation" part are not. **Corollaries 26 and 31** are not
    formalized: they need a general composition theorem for strongly linearizable implementations,
    which the framework lacks (for queues we did the composition concretely, Proposition 11).
    [not formalized]
