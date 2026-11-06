# Differences between the formalization and the paper

Paper: Gay, Mostéfaoui, Perrin, *No Broadcast Abstraction Characterizes k-Set-Agreement in Message-Passing
Systems*, PODC 2024 brief announcement; extended version HAL hal-04571653v1 (numbering used here).

## Statement-level issues

1. **Lemma 9 is false** (`lemma9_false`, 🛠️). It is not the main result: the title and abstract claim Theorem 1,
   which is true.
   - The counterexample satisfies all of the paper's hypotheses. The abstraction `chainedBO k` is a set of
     executions satisfying the four BC properties (plus unique messages and well-formed invocations), defined
     "by a predicate on the relative order of emission and delivery events", which is exactly the class the
     paper says is compositional. It is compositional and content-neutral (`chainedBO_compositional`,
     `chainedBO_contentNeutral`).
   - The abstraction is not degenerate: it contains every uniform total-order execution (`totalOrder_mem`), so
     it is implementable from consensus, and the algorithm has admissible executions (`soloRun_admissible`).
   - The algorithm `algQ` is deterministic, well-formed (`algQ_wellFormed`), uses no point-to-point channel
     and proposes from `ℕ`. The counterexample works for every `k`, in particular `k > 1`, with `k + 1`
     processes as in the lemma.
   - There is no degenerate case, and no implicit assumption of the paper rules it out. Definition 5
     explicitly constrains only deliveries. The ordering predicate of `chainedBO` ("the sender had delivered one of
     its own messages before broadcasting") is of the same kind as causal broadcast's, which the paper lists among
     its examples; the abstraction never constrains invocations (it contains every total-order execution).
   - Lemma 9 might be rescued by strengthening Definition 5 to require that
     each `pᵢ`'s selected messages are `sync-broadcast` one after another (the shape Lemma 10's β has; `chainedBO`
     admits no such execution for `N ≥ 2`) and by making A' use `sync-broadcast`. This is not a local fix: it changes
     a definition, needs a proof step the paper does not have, and the "δ is finite" gap (item 3) remains.
2. **Theorem 1 is true; its proof is repaired** (🛠️). The paper derives it from the false Lemma 9. We prove it
   with a different adversary (README, item on Lemma 9), and in a stronger form: compositionality alone suffices
   (`theorem1`); `theorem1_paper` is the paper's form with content-neutrality as an (unused) hypothesis.

## Proof-level differences

3. **Lemma 9's proof**:
   - It fails at "αᵢ is indistinguishable from δ" (README).
   - δ is finite, and A' must be run "on δ" in an admissible execution in which A' may keep broadcasting after
     deciding; the paper does not address this.
   - The claim that A can be replaced by a broadcast-only A' ("send and receive can be trivially emulated using
     B") is unjustified: SR-Termination holds for crashed senders, BC-Global-CS-Termination does not. A claim
     inside a proof (⚠️); our model restricts A to broadcast-only algorithms anyway (item 8).
4. **Our adversary differs from Algorithm 1.**
   - The upper layer runs copies of A, not `sync-broadcast(synch)`. The phase of `pᵢ` ends when its current
     copy decides, not after `N` local deliveries.
   - A reset of `p_k` discards its current copy. A reset happens only while that copy is undecided, and the
     phase stops at its decision.
   - The messages `p_k` sent to `p_{k+1}` before its last reset are received by `p_{k+1}` at the beginning of
     its run, not at the reset times.
   - All other messages to `p_{k+1}` are received after `p_{k+1}`'s copy decided. The other processes crash at
     the end of their phase, so the execution is infinite and admissible; the paper's α is a finite prefix.
5. **Footnote 1 (SR-Termination for γ)** is not a gap of the paper. Lemma 10 only needs γ as a prefix of an
   admissible execution (safety), and Lemma 7 proves SR-Termination in the case where it is needed. The extension
   of a finite γ to an admissible execution is left implicit by the paper; our counterparts (`solo`, `gZ`) are
   infinite admissible executions.
6. **Lemmas 1–8 and 10** are not formalized for the paper's own adversary. Their content is reproved for our
   adversary: admissibility of concatenations of runs (`catRun_adm`), safety facts (`seg_deliver_own`,
   `MsS_inv_late`), termination of the phases (`early_copy`, `kk_copy`, `z_copy` via `fin_copy`).
7. **Reduction from `n` to `k + 1` processes** ("`CAMP_n[∅]` with `n − k − 1` initial crashes is functionally
   identical to `CAMP_{k+1}[∅]`"): not used. Our Theorem 1 is stated for `Fin n` directly; processes
   `k + 1, …, n − 1` never take a step.

## Modelling choices

8. **A uses only the broadcast abstraction** (no point-to-point channels), as the paper's A' does. The paper's
   `CAMP_n[B]` also has channels. **This weakens our Theorem 1** (`theorem1`, `theorem1_paper`) below the paper's
   claim: they exclude equivalences witnessed by a broadcast-only A, not by an A that also uses channels (the
   paper's reduction to broadcast-only A' is unjustified, item 3). Allowing them in A should not change the result: their messages can be held
   back until after the decisions and then simulated by the upper layer of `p_{k+1}`. This is not formalized.
9. **Messages are objects `(id, content)`**. Algorithms choose contents; identifiers are fresh. This is the
   paper's "each broadcast message is unique, regardless of having identical content". Content-neutrality
   renames message objects injectively, per sender (Definition 3's "injective functions r on the set of
   messages", applied to deliveries "from pᵢ").
10. **Algorithms are deterministic functions of local histories.** For A, the history is its invocations, returns,
    deliveries and decisions. For B, it is its own actions, the invocations, the receptions and the k-SA answers
    (Definition 1 and "deterministic reduction algorithms"). The upper layer of `CAMP_n[k-SA]` may take internal
    steps (`up`), invisible to B.
11. **Hypotheses made explicit in Theorem 1**:
    - A is well-formed (never invokes while an invocation is pending; Definition 1).
    - The proposal domain has at least `k + 1` values. Otherwise k-SA is trivial and the theorem is false.
    - B proposes at most once to each k-SA object (the standard assumption of Section 4.1).
    - `EquivalentToKSA` packages "some A solves k-SA on top of S" and "some B implements S in `CAMP_n[k-SA]`".
12. **Executions** are maps `ℕ → Option step` (stuttering allowed). An abstraction is a set of such executions
    (with the set of correct processes). Faulty processes take finitely many steps, in `CAMP_n[k-SA]` (`Adm.crash`)
    and in executions of A on top of S (`Admissible.crash`; added in review: without it `SolvesKSA` would also
    quantify over executions in which a faulty process keeps acting forever, a stronger hypothesis of Theorem 1). We do not impose "at least one
    correct process" (`t = n − 1`): this only adds executions, and our constructions always have one correct
    process.
13. **k-SA validity** for A requires the decided value to be the proposal of a process that took a step. This is
    the paper's notion: a process proposes by invoking `propose`, which is a step. It makes `algQ_solves`
    stronger; in Theorem 1 it is part of the hypothesis "A solves k-SA" and does not weaken the theorem relative
    to the paper.
14. **`N`-solo** (Definition 5) is formalized literally: `N` distinct messages broadcast by each process, each
    process delivering all its own selected messages before any selected message of another process.
15. **Non-vacuity**: no implementation `B` of an abstraction is exhibited in our `CAMP_n[k-SA]` model. Theorem 1 is
    a non-existence result; its proof does not use vacuity.
16. **Brief announcement vs extended version**: the BA states only the theorem and sketches the adversary ("it is
    easy to see that sufficiently large values of N inhibit A"); its slip "k = n … equivalent to Reliable
    Broadcast" (the extended version says Send-To-All) is irrelevant to the results.
