# Differences between the formalization and the paper

Paper: K. Brusse, F. Ellen, *Reductions and Extension-Based Proofs*, PODC 2021 (proceedings version; no arXiv
version). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Scope

1. **Theorem 1 is proved only for reductions with a communication-free `R₂`.** `theorem1` assumes
   `LocallySolvable R₂ h`: `h ∘ w ∈ R₂(w)` for every input vector `w` of `R₂`. `R₁` is arbitrary, and the
   identity task `R₂` is a special case. The paper's general case composes `A₂` after `A ∘ A₁` with the NIS
   composition of Section 6 (estimate vectors). That composition and its correctness ("A complete proof
   appears in the full version") are not formalized, and neither is the general case of the prover's
   assignment-query handling (see item 9). The verdict only concerns the checked statements (R1 of
   `verdicts.md`).
2. **Not formalized:**
   * Section 5 (no augmented EBP for `k`-set agreement); the paper only sketches its differences from
     [3] and defers the proof.
   * Corollary 2 (anonymous protocols; anonymity would need a separate state space and an extra winning
     condition).
   * The application in §8 to `k`-leader election, `k`-test-and-set, weak symmetry breaking and renaming
     (cited reductions plus Section 5).

   `no_augEBProof_of_reduction` is the abstract transfer step, for local `R₂`.

## Model and definitions

3. **Protocols are full-information decision functions.** This matches the paper's standard form (§3).
   * A state is `init i x`, `upd s` (`s·1`) or `scan s v`. The paper writes the post-scan state as
     `(i, v)`; we store the pre-scan state `s` instead of `i`. Since `v i` is the state written just
     before, the two carry the same information.
   * `δ` is consulted only on post-scan states (`decided`).
   * The memory is not stored. `Sₕ[j]` is read off `j`'s state (`hist`), as the paper notes ("a
     configuration ... is completely specified by the states of all the processes").
4. **Initial configurations.** A protocol over input type `X` has one initial configuration for every
   vector `P → X`. A task's input vectors `I ⊆ (P → X)` only restrict which runs must be correct.
   * The paper's proof needs this product structure: `D₀'` = `D₀` with one input changed must again be an
     initial configuration of `A`. A full-information protocol has initial state `(i, xᵢ)` for each
     possible input, so this is the natural reading.
   * Wait-freedom is required from every initial configuration.
   * Finiteness of input sets (paper: "a finite set of input vectors"): we need `Finite` on `X` only for
     the NIS→IS conversion and `Finite` on the output type of `S` for the candidate enumeration.
5. **Game formalization (§4).** The paper describes the interaction informally.
   * **Prover.** A deterministic strategy (function of the history). It must make legal moves; an illegal
     move makes it lose.
   * **Protocol.** A fixed decision function. Its answers to assignment queries are any correct answers
     (adversarial, possibly history-dependent): we quantify over all correct plays.
   * **Query responses.** They contain the new configuration and the decision values of all processes.
   * **Reached configurations.** In a phase they are `reinit base u`, which is the paper's `C₀' α(φ)` (the
     configuration determines the states of the processes that took steps), plus the query responses.
     `endPhase C` requires a response of the current phase, i.e. `C = C₀ α(φ) β` with `β ≠ []`.
   * **Winning.** (W1) reaching a configuration (start-of-phase or response) whose partial outputs violate
     the task: the input vector of `C` is an input of `T` and no valid output vector extends the outputs;
     (W2) infinitely many phases; (W3) from some point on every move is a query from the previous
     response.
   * **Reading of "finitely many chains of queries per phase".** W3 asks for one *consecutive* infinite
     chain. Interleaving two infinite chains, or interleaving infinitely many assignment queries, does not
     win. This is a strict reading, used on both sides of Theorem 1.
6. **Reductions (§3).** `IsReduction T S R₁ R₂` has the paper's conditions: `R₁`, `R₂` NIS-solvable and
   `R₂∘S∘R₁(x) ⊆ T(x)` for input vectors `x` of `T`. It also has three well-formedness conditions the
   paper leaves implicit:
   * inputs of `T` are inputs of `R₁`;
   * outputs of `R₁` are inputs of `S`;
   * outputs of `S` are inputs of `R₂`.

   The paper assumes the analogous condition for protocols in §6 ("each output from `A₁` is a valid input
   for `A₂`"). (R4: implied assumption.)
7. **IS protocols.** `IsIS δ t` is the normal form "a process terminates exactly after its `t`-th scan",
   imposed on all states. The paper says "in every schedule ... every process terminates in round `t`";
   `exists_isIS_of_solves` produces protocols in normal form from any NIS protocol.

## Proofs

8. **"W.l.o.g. `A₁` is an IS protocol" (cited from [8]).** Proved (`exists_isIS_of_solves`): a König
   argument gives a uniform round bound `N` for a wait-free protocol with finitely many inputs. A
   simulation protocol then runs until round `N + 1`, ignores processes that have already decided in the
   simulated protocol, and outputs the simulated decision.
9. **Assignment queries (§7) for the general composition.** Not formalized. Two problems:
   * The enumeration of "initial configurations `C₂` of `A₂` such that there is a `P'`-only schedule from
     `C₂` satisfying `f`" ignores the `A₂`-steps already taken during `γ`, including those of processes
     outside `P`. It can therefore drop the needed `g`. Enumerating all `g` repairs this (the later search
     for `μ₂` is exact).
   * The claim that the schedules of `A₂` simulable from `C μ₁ μ'` "do not depend on the particular
     schedule `μ'`" is not proved and is needed for completeness of the `None` answers.

   In the local case, which we formalize, `𝒫` enumerates the following, and both soundness and
   completeness are proved (`assign_sound`, `assign_complete`):
   * every `P`-only schedule `μ₁` of `A₁` (from the `A₁`-part) after which all of `P` has finished `A₁`
     (the paper's condition, needed so that `A`'s answer `μ'` contains only processes that finished `A₁`);
   * every `g` with `h ∘ g = f`.

   Completeness needs a reordering lemma: a composite schedule splits into an `A₁`-schedule and an
   `A`-schedule (`decompY`). It also needs extending the `A₁`-part so that all of `P` finishes
   (`exists_complete`). The candidate set is finite because IS schedules have bounded length
   (`candSet_finite`).
10. **Choice of `D₀` (§7, "Responding to queries" and "Why the prover wins").** Proof repair; it decides
    the 🛠️ verdict.
    * The paper keeps `D₀` arbitrary on processes that have not finished `A₁`. It changes `D₀` only at
      the final step of `A₁` of a process, by a chain re-reaching `D₀'γ'`.
    * Then "if `D₀γ'` satisfies `S` then `C` satisfies `R₂∘S∘R₁`" fails for configurations `C` in which
      some process has not finished `A₁`. The input vector of `D₀` need not be in `R₁(x)`, nor even an
      input vector of `S`.
    * We give the not-yet-finished processes the outputs of a fixed completion of the `A₁`-part as inputs
      (`ucan`, `toA`; `ucan_mem` shows `ucan C ∈ R₁(x)`). Since these inputs change whenever any process
      takes a step of `A₁`, `𝒫` re-reaches `toA (C q)` after every simulated `A₁`-step
      (`step_queryA1`).
    * The invariant "every configuration reached by `𝒫_T` has its `A`-part reached by `𝒫`"
      (`SimInv.reach`) is the paper's invariant with this canonical `D₀`.
    * If one reads "violates the specifications" as "final configuration with invalid outputs", the
      paper's argument works as written. We use the partial reading, which the paper's own wording
      ("reaches a configuration where the protocol violates the specifications") suggests.
11. **Infinitely many phases (§7, last paragraph).** "Because `A₁` and `A₂` are wait-free, `𝒫_T` can only
    end a finite number of phases by choosing a non-empty schedule during which processes only simulate
    `A₁` and `A₂`" is stated without argument; the phases need not be consecutive. Our proof for local
    `R₂` is a potential argument. After `𝒫`'s last phase end, the `A`-parts of the configurations chosen
    by `𝒫_T` all have the step count of `𝒫`'s base, so the `A₁`-part of `𝒫_T`'s base strictly increases
    at each of its phase ends. That part is bounded by `n·2t`. (`eventually_not_of_bounded` in
    `Main.lean`.)
12. **Handler programs start with a harmless move.** Each of `𝒫`'s answers to a move of `𝒫_T` begins with
    the assignment query `(base, ∅, ∅)`, except the single query answering a step of `A`. These harmless
    moves are finitely many in an infinite chain of `𝒫_T` (finitely many `A₁`-steps), so they do not
    affect W3. The paper's `𝒫` "does nothing" in some cases; our framework needs a non-empty answer.
13. **Knowledge of the decision function.** The paper says `𝒫` "can determine" the composite
    configuration `C q`. We make explicit that the decision values are read off earlier responses (`know`)
    and prove that every state of a reached configuration has been revealed (`SimInv.cover`).

## Statements

14. **Theorem 1:** proved for local `R₂` (`theorem1`). Our statement adds `[Finite XT]` (finite input set
    of `T`, needed for the NIS→IS conversion; the paper assumes finite input sets) and `[Finite ZS]`
    (finite output set of `S`). Both hold in the paper's setting.
15. **Section 4, "any task that has an extension-based impossibility proof also has an augmented
    extension-based impossibility proof":** proved as stated (`hasAugEBProof_of_hasEBProof`). Each output
    query `(C, P, y)` becomes the assignment queries `(C, P, {p ↦ y})`, `p ∈ P`, preceded by one harmless
    query, needed when `P = ∅`.
16. **Typos** (R3, no effect):
    * `R₂ ∘ S ∘ R₂` (§1) and `R₁ ∘ S ∘ R₂`, `R₂ ∘ S ∘ R₂` (§7) for `R₂ ∘ S ∘ R₁`;
    * `δ(sᵢ)` for `δ(s'ᵢ)` (§3, twice: "outputs `δ(sᵢ)`" and "if `δ(sᵢ) = ⊥`");
    * `α'(ϕ)` for `α'(φ)` (§7).

## Sanity checks of the definitions

17. **Soundness of the game.** Because the game (item 5) is our formalization of an informal interaction,
    we check that it is not too generous to the prover: if some protocol solves `T` (finite input type),
    no prover wins against it, so `T` has neither an extension-based nor an augmented extension-based
    proof (`not_hasProof_of_solves`, `not_hasAugEBProof_of_solves` in `NonVacuity.lean`). Hence the
    conclusion of `theorem1` is not vacuous. The strict W3 reading of item 5 is not checked to be
    equivalent to the paper's "finitely many chains per phase" reading; Theorem 1 is proved for the
    strict game on both sides (hypothesis and conclusion), not for the looser one.
