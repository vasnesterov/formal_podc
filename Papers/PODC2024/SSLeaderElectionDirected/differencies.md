# Differences between the formalization and the paper

Paper: Altisen, Cournier, Defalque, Devismes, *On Self-stabilizing Leader Election in Directed
Networks*, PODC 2024. Formalized from the full version
[hal-04434345v4](https://hal.science/hal-04434345v4). Each item has a classification.

## Errors in the paper

1. **Theorem 5 (and Lemmas 16, 19, Corollary 6) — false statement.** The unison algorithm
   `U(K) = U-DAG(K) ∘ PEL` relies on the claim "in a terminal configuration of PEL,
   `p.E.d = ‖ℓ, p‖`, and `ℓ` is the only process with `E.d = 0`". The paper attributes this claim to
   Theorem 1 (§5.3, proof of Lemma 16 Claim 3, Remark 3, proof of Lemma 19). It is false for
   `I_E(p) = (¬p.A.M, p.MI.M)`. In fact `p.E.d = Mind_E(p)`, and `Mind_E(q) = 0` for every `q` with
   `I_E(q) = (0, mid)`. This includes all of the source component and every process all of whose
   ancestors have identifiers `≥ mid`. Each such process increments its clock on its own.
   * Lean: `U.paper_ed_eq_zero` shows that `E.d = 0` holds at every process whose ancestors all
     have identifiers `≥ mid` (`U.LowAnc`).
   * `U.paper_unison_not_selfStab_gen`: `U(K)` is not self-stabilizing (for *any* set of
     legitimate configurations) as soon as two distinct processes satisfy `LowAnc`. This holds
     for all `K ≥ 2` and all `α ≥ MAD`.
   * Corollaries:
     * `U.paper_unison_not_selfStab`: the source component has ≥ 2 processes (any `ι`).
     * `U.paper_unison_not_selfStab_of_min`: the globally smallest identifier lies in the source
       component, so it fails on every network with `n ≥ 2` for such `ι`.
   * Concrete instances: `twoCycle_paper_unison_fails` (2-cycle) and `dipath_paper_unison_fails`
     (dipath `0 → 1`, whose source component is a single process).
   * Figures 5(c) and 6 are inconsistent with each other. Six processes have `E`-input `(0,4)`,
     yet Figure 6 shows distinct `E.d` values for them.
   * Repair: `I_E(p) = (¬p.A.M, p.Id)` (`fixed = true` in `PEL.next`). Leader election is
     unaffected (`PEL.lemma15` and `PEL.theorem3` are proved for both inputs). For unison we prove
     Theorem 5 with the paper's bound `3α + 4MAD + 6` (`U.theorem5`, `U.theorem5_time`). This
     requires *unique* identifiers, used to show that `ℓ` alone has input `(0, mid)`.
2. **Lemma 10 — typo.** The induction claim says "If `MinI(p) < i`"; it should be `Mind(p) < i`.
3. **Lemmas 5, 8, 9 — typos.** Lemma 5's proof has `q ∈ F_{i+1}(q)` for `F_{i+1}(p)`. Lemma 8 has
   `q ∉ F_j(q)` and `q ∈ F_j(q)` for `F_j(p)`. Lemma 9 has "`Mdf_{R(α+1)} q(p)`".
4. **Lemmas 9, 10 — imprecise indexing.** `R(i)` (end of the `i`-th round) is undefined when the
   finite execution ends earlier. Harmless: a terminal configuration is legitimate. In Lean, the
   `Ext∞` form makes every index meaningful.
5. **Theorem 4 — proof by reference only.** The paper cites [ACDD23]. We give a direct proof for
   arbitrary deterministic local algorithms with identifiers (`theorem4`). It is true for every
   period `K ≥ 2`; the hypothesis `K ≥ 2` is needed, since `K = 1` is trivially solvable.

## Modelling choices

6. **Atomic-state model, deterministic algorithms.** An algorithm is a function
   `next : (V → Q) → V → Q`, i.e. one action per process with the statement "assign `next γ p`". The
   paper allows several actions and a nondeterministic choice among the enabled ones. This loses
   nothing:
   * C-MAI has a single action.
   * In the compositions `E ∘ A ∘ MI` and `U-DAG ∘ PEL`, at most one action per process is enabled.
   * Lemma 12/13 in the paper are stated for deterministic algorithms.
   Trivial actions are excluded, as in the paper: a process is enabled iff `next γ p ≠ γ p`.
7. **Executions in `Ext∞` form.** `IsRun next e S` describes infinite sequences in which a nonempty
   set `S t` of enabled processes moves at every non-terminal configuration, and terminal
   configurations repeat. These are exactly the paper's infinite extensions of maximal executions
   under the distributed unfair daemon. Lemma 11 (`SP_L(e) ≡ SP_L(Ext∞(e))`) is therefore built in.
   Silence = every execution reaches a terminal configuration.
8. **Rounds.** The paper defines rounds with neutralization. `RoundDone e S s s'` says: "every
   process enabled at `s` is activated at some `u ∈ [s, s')` or is disabled at some `u + 1 ≤ s'`".
   This is equivalent to "executes an action or is neutralized during `[s, s']`", because a
   process that becomes disabled without being activated is neutralized at that step.
   * Upper bounds hold for *every* sequence of boundaries in which each interval contains a
     complete round (`RoundBounds`). This includes the paper's minimal rounds (`PaperRounds`, which
     exist for eventually terminal runs, `IsRun.exists_paperRounds`).
   * Under the synchronous daemon, `r = id`.
9. **`MAD`.** `MADLe G α` says that every ancestor is at distance `≤ α`, i.e. `α ≥ MAD`.
   `mad G` is the least such value. Time bounds are proved for every `m` with `MAD ≤ m ≤ α`
   (in particular `m = MAD`); `PEL.theorem3_time` is stated with `mad G`.
10. **Identifiers and `α`.**
    * Identifiers are an input assignment `ι : V → ID` (`ID` totally ordered), not a component of
      the state. The algorithm is a family indexed by `ι`, local by `IsLocal`.
    * "Insensitive to its inputs" becomes "self-stabilizing for every injective `ι`".
    * `α` is a fixed natural number known to the algorithm. The impossibility does not use `α`.
    * `|IDSET| > |V|` is an injection `Option V ↪ ID`. Lemma 13 uses only the existence of an
      unused identifier (`exists_fresh`).
    * `idset_card_needed` shows that Corollary 2 is false with `|IDSET| = |V|`. This is not an
      error, since the paper assumes `|IDSET| > |V|`.
11. **Leader output.** `L(p)` may depend on `p`'s identifier and state only (`LEAlg.local_out`), as
    in the paper ("a local function").
12. **Domains of variables.** A C-MAI state is a key with `d ≤ α` (`CState D α`), so arbitrary
    initial configurations respect the variable domains, as in the paper. The input `I_A` is a
    `Bool`; `B × IDSET` with `<_C` is `Bool ×ₗ ID`.
13. **Source components.** We use the paper's definition:
    * the induced subgraph is strongly connected and maximal,
    * the component is nonempty,
    * there are no predecessors outside.
    We add nonemptiness so that the empty digraph has no source component. The paper assumes
    `n ≥ 1` anyway, and the necessity results assume `V` nonempty where needed.
    `isSourceComponent_iff` relates this to "`S = Anc(r)` with `r` upstream of all its ancestors".
14. **Self-loops** are allowed in `Digraph` and do not affect any result. The counterexample
    `twoCycle` has none.

## Generalisations

15. **Lemma 4** is proved for runs with *eventually constant, time-dependent inputs* and arbitrary
    activation sets (`CMAI.Run.eventually_const`), not only for executions of C-MAI. This is what
    makes PEL's termination direct.
    * Proof: well-founded induction over the finitely many reachable keys ("freeze all keys
      `≤ k`").
    * The paper's proof uses limit inferiors. Its argument is correct; it is replaced, not repaired.
16. **Lemmas 5–9** are proved for fake keys at all processes, not only at ancestors of a fixed `p`.
    The restriction to `Anc(p)` is unnecessary.
17. **Theorem 3** does not need injectivity of the identifiers for the paper's PEL (the spec then
    still holds literally). The fixed variant needs injectivity only for the unison
    (`U.fixed_ed`).
18. **Theorem 5** (repaired) holds for every `K ≥ 1`. The paper's `K > 1` matters only for Claim 3
    of Lemma 16 in its formulation; the spec `SP_SU` is trivial for `K = 1`.

## Not formalized

19. Lemma 1 and Corollary 1 (generic hierarchical collateral composition of silent algorithms)
    are only used through their instances for PEL. We prove those directly: `PEL.silent` and
    `PEL.terminal_within`, via `PEL.runMI/runA/runE`.
20. Lemma 17 (no terminal configuration of `U(K)`) and Remark 3 are not needed in that form
    (Property 1 is `CMAI.target_le_succ_target`).
21. Space complexity `O(log α + B)` bits and `O(log α + B + log K)` bits is not formalized. It is
    evident from the state types `CState`, `PState`, `UState`.
