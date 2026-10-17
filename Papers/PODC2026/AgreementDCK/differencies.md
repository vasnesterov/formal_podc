# Differences between the formalization and the paper

Paper: David–Moses, *Brief Announcement: What is Agreement About if not Common Knowledge?*,
PODC 2026 (proceedings version; no full version available). The brief announcement states its
results without proofs, so **all proofs here are ours**.

## Errors and imprecisions in the paper

1. **Theorem 1.7, "for every run `r` of `P_A` and `v ∈ V_A` the nonfaulty processes decide `v` in
   `r` iff `r ⊨ θ_v`": false only in a degenerate case.** This fails in runs with `N(r) = ∅`. There
   "the nonfaulty processes decide `v`" (the paper's `all_decide(v)`) holds vacuously, while `θ_v`
   need not hold. By Θ-Exclusivity, `θ_v` can hold for at most one value. So the failure does not
   depend on how `P_A` is built (for `|V_A| ≥ 2`). The same degenerate case affects the paper's
   motivating example before Theorem 1.7: there `θ_v` := "the nonfaulty processes decide `v`", and
   in a run with `N(r) = ∅` both `θ_0` and `θ_1` hold, which violates Θ-Exclusivity and footnote 5
   (`θ_0 ⇔ ¬θ_1`). Our converse (item 2) uses "some nonfaulty process decides `v`" instead. Lean counterexample:
   `theorem_1_7_iff_false_without_nonfaulty`. It uses one run with no nonfaulty process and all
   `θ_v` false; all hypotheses of Theorem 1.7 hold. Repaired statement: `allDecide_newDec_iff`
   assumes `(S.nf r).Nonempty`. Without that assumption the two directions still hold in this form:
   `θ_v` implies that all nonfaulty processes decide `v`, and a decision on `v` by some nonfaulty
   process implies `θ_v` (`theorem_1_7`).
2. **Converse remark after Theorem 1.7 is imprecise; it needs recall of decisions.** The paper
   says "underlying the design of every AoN protocol is a set of facts Θ as described in
   Theorem 1.7". Read literally, the remark is trivial: Θ with all `θ_v` false satisfies (1)–(3).
   We read it as: there is Θ satisfying (1)–(3) whose `θ_v` holds exactly when `v` is decided.
   - We prove this reading when decisions are local, AoN holds for every value, Agreement and
     Validity hold, and nonfaulty processes remember their decisions (`Stable`). The proof takes
     `θ_v` = "some nonfaulty process decides `v`" and `𝛙(v) = 𝛅(v)` (`exists_theta_of_AoN`).
   - Without memory the reading is false: `no_theta_for_forgetful_protocol` gives a one-process,
     failure-free protocol that decides at time 1 and then forgets. The paper's standing assumption
     ("a process about to decide remains in such a state until it performs the action") does not
     rule this out, because it constrains states only before the decision.

   Classification: under-specified informal claim.

## Proofs supplied (no proof in the paper)

3. **Theorem 1.2** is cited from [29]; we prove it directly (`System.kop`, `theorem_1_2`). It needs
   only that `decideᵢ(v)` is `i`-local. The "conscious action" assumption is not needed.
4. **Theorem 1.5 and Corollary 1.6.** We prove one general lemma, `CN_of_precondition`: under
   `AoN(v)`, every precondition `φ` of deciding `v` satisfies `⊨ all_decide(v) → C^N@𝛅(v)(φ)`. The
   proof uses the induction rule `CN_of_EN_valid`. KoP then gives `KN_CN_of_precondition`.
   Theorem 1.5 takes `φ = all_decide(v)`. Corollary 1.6 takes `φ = valid(v)` and
   `φ = no_dec(w)`. This also proves the sentence before Corollary 1.6 ("for every precondition
   `φ_v` …").
5. **Theorem 1.7.** The paper does not say what `P_A` is. Our construction runs `P` unchanged and
   adds the decision rule `newDecᵢ(v) := ψᵢ(v) ∧ K_i(i ∈ N → θ_v)`. We prove that it is local, AoN
   for every value, satisfies Agreement and Validity, satisfies Decision when `⊨ ⋁ θ_v`, and that
   its decisions are stable for nonfaulty processes (`newDec_stable`).
   - The memory hypothesis is used only for stability ("conscious decisions"). All other conclusions
     hold without it.
   - Only `⊨ θ_v → E^N@𝛙(v)(θ_v)` is used. By the induction rule this is equivalent to the paper's
     `C^N` hypothesis (`sufficient_of_EN`, `CN_self_of_EN_self`).
   - The hypothesis "P solves A" is not used.

## Modelling choices

6. **Runs and time.** The system is an arbitrary type `R` of runs, standing for all runs of `P` in
   the model. Time is `ℕ`. The local state of `i` is `loc i r t : L i`. Knowledge quantifies over
   all points of all runs in `R`. `N(r)` is an arbitrary set `nf r`, as in the paper ("faulty" left
   abstract). Facts are `R → ℕ → Prop`. Run facts are `R → Prop`, lifted with `RunFact.lift` when
   they are nested.
7. **Decisions** are facts `dec i v : R → ℕ → Prop` ("`i` decides `v` at `(r, t)`"). The standing
   assumption that decisions depend on the local state is the hypothesis `DecLocal`. A process is
   not required to decide only once. Every property in the paper (AoN, Agreement, Validity,
   `all_decide`) speaks only of whether a decision happens in the run. In `P_A` a decision
   "happens" whenever the decision condition holds; the actual action can be taken the first time
   it holds. A faulty process may satisfy the condition for several values under our rule. This
   does not matter, because Agreement and Validity constrain only nonfaulty processes, as in the
   paper.
8. **"Extends `P` by adding new decision actions".** The new decisions are modelled as extra local
   facts on the same system. They are pure outputs: they do not change local states or messages. If
   a model records the decision in the local state, the runs, and hence the knowledge, of `P_A`
   would differ from those of `P`. We do not cover that variant.
9. **Definition 1.3.** `DK i ψ φ` is defined for every fact `ψ`. The paper requires `ψ` to be
   `i`-local, and we assume locality (`IsLocalProfile`) wherever it matters (Theorem 1.7, for the
   locality of `newDec`).
10. **Definition 1.4.** `EIter ψ φ m` is `E^{m+1}` (index shifted by one). `CN ψ φ r := ∀ m, EIter ψ φ m r`
    is exactly "`E^m` for all `m ≥ 1`".
11. **Validity condition** of a problem: a run fact `valid v` with `⊨ i ∈ N ∧ decideᵢ(v) → valid(v)`
    (`Validity`). `Agreement` and `Decision` are the usual properties for nonfaulty processes.
12. **Corollary 1.6** assumes `AoN(v)` for all `v ∈ V`. We assume it only for the decided value
    `v`, which is a stronger statement.
13. **Classical common knowledge** (`System.E`, `System.C`, used only in `Example.lean`) is among
    all processes. In the example every process is nonfaulty, so this is the classical notion that
    the paper contrasts with.

## Additional results (not in the paper as statements)

- `CN_iff_EN`: the fixed-point characterization `C^N@𝛙 φ ↔ E^N@𝛙 (φ ∧ C^N@𝛙 φ)`.
- `CN_of_EN_valid`: the induction rule.
- `CN.KN_CN`, `CN.eventually_KN`: the remark after Definition 1.4.
- `Example.lean`: an asynchronous two-process AoN protocol in which dynamic common knowledge of the
  decision holds in every run, while classical common knowledge (even `E²`) of the decided bit holds
  at no point.
