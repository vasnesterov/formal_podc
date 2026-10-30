# Differences between the formalization and the paper

Paper: Jaggard, Schapira, Wright, *Distributed computing with rules of thumb*, PODC 2011; full version
arXiv 0910.1585v2, *Distributed Computing with Adaptive Heuristics*. Numbering follows the arXiv version.

Each item is classified as one of: **false statement**, **proof gap (statement true / open)**,
**under-specified definition**, **typo**, or **modelling choice**. Statement-level items name the
`verdicts.md` rule that decides them.

## Model (Section 3)

1. **Modelling choice.** Nodes: any `Fintype ι`. Action spaces: arbitrary types `A i`; neither finiteness
   nor nonemptiness is assumed. Profiles are `(i : ι) → A i`.
2. **Modelling choice.** A history `h ∈ H_w` (`w ≥ 1`) is `Hist A`: the current profile `cur` and the
   earlier profiles `past`, most recent first, with `h.time = w`. The paper's `x|k` (last `k` coordinates)
   is `h.toList.take k`.
3. **Typo.** Section 3 types `f(i,t) : H_t → Δ(A_i)`, but the dynamics applies `f(i,w+1)` to
   `s⁰ ∈ H_w`. We type `f(i,t)` on `H_{t−1}`: `F.f i t h` is only used with `h.time = t − 1`. All
   restrictions are stated for these inputs only, which is the weakest reading.
4. **Modelling choice (restriction).** Reaction functions are deterministic (`F.f i t h : A i`), not
   distributions; see item 18 for the randomized claim.
5. **Modelling choice.** A schedule is `σ : ℕ → Finset ι` with every `σ t` nonempty (`IsSchedule`).
   `σ t` is used at absolute time step `t`, as in the paper, so `σ t` for `t ≤ w` is ignored.
   Requiring `σ 0` nonempty as well is harmless. `Fair σ`: every node is in `σ t` for infinitely many `t`.
6. **Modelling choice.** `ConvergesTo s⁰ σ a`: eventually the current profile is `a`. The paper writes
   `s(t) = a` for a history `s(t)` (**typo**). `Convergent`: for all initial histories (of any length
   `w ≥ 1`) and all fair schedules, the dynamics converges, exactly as in the paper.
7. **Under-specified definition (R3: evident intent, ⚠️).** Section 3 defines a stable state as a limit
   of the `(s⁰, σ)`-dynamics for a schedule `σ` that need not be fair. With this literal reading
   Theorem 4.1 is false (`stableState_literal_reading`): the constant system `fᵢ ≡ x` on two nodes is
   historyless, self-independent and convergent, but the dynamics activating only node 0 from `(x,y)`
   converges to `(x,y)`. The paper's remark that in the deterministic historyless case the stable states
   are exactly the fixed points shows the intended reading. We use it: `IsStableState a` means some
   *fair* dynamics converges to `a`. The literal one is `IsStableStateAny`.
8. **Modelling choice.** Restrictions:
   - `SelfIndependent`: `f(i,t)` depends only on the other nodes' coordinates of the history; we compare
     histories with `OthersEq i`.
   - `HasRecall i k`: for histories of equal length `≥ k`, equal last `k` profiles give equal reactions.
     This is the paper's "for every `t ≥ k` there is `g` with `f(i,t)(x) = g(x|k)`".
   - `Stationary i k`: there is one `g` with `f(i,t)(x) = g(x|k)` for all `t` and `x` with at least `k`
     entries.
   - `Historyless = Stationary i 1`.
   - Per-node bounds `k` are combined into one `K = max + 1` (`HasRecall.mono`, `Stationary.mono`).

## Theorem 4.1

9. **Statement restricted / proof gap (open part).** The main text claims Theorem 4.1 for bounded-recall
   self-independent reaction functions, "even if not stationary and randomized". Appendix F restates it
   with "stationary" and proves only that case, extending it by Theorem F.14 (1-recall, finite action
   spaces) and the F.8 sketch. We prove the following.
   - `System.theorem_4_1`: stationary bounded recall (any `k`), deterministic, any action spaces. This
     is Appendix F's version.
   - `System.theorem_4_1_oneRecall`: non-stationary 1-recall, deterministic, any action spaces. This is
     Theorem F.14 without finiteness.
   - `System.not_convergent_of_absorbing`: non-stationary `k`-recall, *provided* fair limits are
     eventually absorbing in convergent systems.

   The non-stationary `k ≥ 2` case is neither proved nor refuted. Exhaustive brute force over 2 nodes,
   binary actions, `k = 2`, period `≤ 2`, and random samples with periods `≤ 4` and `k = 3` found no
   convergent system with two stable states and no convergent system with a non-absorbing fair limit.
   Since the unproved part is not in the README table, it does not affect the verdict. It is recorded
   in the README as a proof gap.
10. **Proof gap (repaired for 1-recall).** In the valency argument (Theorem F.9 + the proof of Thm 4.1
    in F.6), a forever-bivalent fair run is non-convergent only if reaching a limit is a "decision":
    a run that converges to `c` must eventually reach a history from which `c` is the only reachable
    limit. For stationary functions this holds: `k` steps at `c` make `c` a fixed point
    (`absorbingAfter_of_stationary`, `subsingleton_lims_of_absorbing`). For non-stationary functions the
    paper does not address it. Theorem F.14 redefines a stable state as "a vector of actions and a time
    `t` such that after `t` the vector is a fixed point". That is a different notion from Section 3's,
    and with it "convergent" no longer guarantees that every history has a colour. We repair it with
    `absorbingAfter_of_oneRecall`: in a convergent 1-recall system every fair limit is eventually
    absorbing. Otherwise some node deviates infinitely often, and the deviation can be repeated fairly:
    follow the converging dynamics, let the node deviate, then activate it alone until a step at which
    it returns. That gives a fair non-convergent dynamics. This argument needs 1-recall: with
    `k`-recall the deviating node has to reproduce `c` at `k` consecutive steps to return.
11. **Proof gap (repaired).** The act-and-tell model of F.6 enables every event at every state,
    including `W` with nothing pending. That corresponds to a time step with an empty activation set,
    which Section 3 forbids. F.7's argument ("both paths take the same number of time steps") counts
    such steps. In `FLP.lean`, `W` (`ATStep.fire`) requires a nonempty pending set, and the extension
    lemma is proved with this restriction.
12. **Proof gap (minor, repaired).** Theorem F.14 assumes finite action spaces to pick "the largest
    `t` over all stable states". Our proof of the initial bivalence (`exists_biv_hist`) needs no
    finiteness: we compare the two converging dynamics at a common time step `T` and connect the two
    histories at time `T` by changing one node's column at a time (`mixH`).
13. **Different proof route (no gap).** We do not formalize the abstract Taubenfeld-style framework
    (Defs. F.1–F.6, IoD, Lemma F.7, Lemma F.8 in general). We prove the extension lemma directly for the
    act-and-tell model (`exists_bivalent_after`).
    - Case `e = W`: the colours of `W` after the pending sets `Q ⊇ P` are all equal. Adding one node `j`
      changes the resulting histories only in `j`'s action, and two such histories have a common colour.
    - Case `e = e_i`: the colour of `e_i(u)` is invariant along `e_i`-free paths. `e_j` commutes with
      `e_i`. For `W`, the "diamond" of Fig. 3 is again the adjacency of `step g (insert i P)` and
      `step g P` in node `i`.

    Both cases rest on one adjacency lemma: histories that differ only in node `j`'s actions become
    equivalent after `j` is activated alone `k` times (`equiv_run_single`). That lemma combines the
    paper's two colour equalities (Lemma F.11, and its `k`-recall form in F.8).
14. **Typo.** Proof of Lemma F.12, case `e = e_i`, `e' = W`: "By the second color equality" should be
    the first one.
15. **Proof gap (minor).** Lemma F.13 activates `v` once. For `k`-recall `v` must be activated `k`
    times, as F.8 notes; we do so (`lims_inter_nonempty`).
16. **Typo.** Def. F.4's "fair extension" is any finite extension; the fairness used later is the one
    in the proof of Lemma F.8 (all events). Our segments (`IsSegment` + the activation condition of
    `exists_segment`) activate the chosen node, and `exists_fair_of_segments` cycles through all
    nodes.
17. **Terminology.** "Safe" (Examples, Appendix F) means "convergent".
18. **Not formalized (under-specified claim).** "The result holds even if reaction functions are
    randomized": the paper never defines convergence or stable states for randomized dynamics (every
    realization vs. almost surely), and Appendix F treats only deterministic reactions (`e_i` is "the
    action of node `i` acting as dictated by `f_i`").

## Examples 4.2 and 4.3

19. **Modelling choice.** Nodes `1, 2` are `0, 1 : Fin 2`; `x = false`, `y = true`. In Example 4.2,
    "node 2's action changed from `x` to `y` in the past" means that two consecutive profiles of the
    history, the initial history included, show node 2 at `x` and then at `y` (`ChangedXY`).
20. **Correct.**
    - `example_4_2`: self-independent; node 0 has no bounded recall (`ex42_not_hasRecall`, for every
      `k`); stable states `(x,x)` and `(y,y)`; convergent. The stable state `(y,y)` needs an initial
      history that already records the change, e.g. `[(y,y), (x,x)]`.
    - `example_4_3`: historyless; not self-independent; the stable states are exactly the profiles
      other than `(x,x)`; convergent.

    The failure of self-independence (`ex43_not_selfIndependent`) is derived from Theorem 4.1.
21. **Not formalized.** Appendix A's remark that both examples have a bivalent initial state.

## Section 5 / Appendix B.1 (games)

22. **False statement (❌; R4 not applicable, R5: application, not headline).** Corollary 5.2
    ("two pure Nash equilibria ⇒ best-response dynamics with consistent tie-breaking can fail to
    converge") and Theorem B.2 are false: `corollary_5_2_false` (2×2 game with a weakly dominated
    equilibrium `(y,y)`, ties broken towards `x`). Theorem 5.1 ("all bounded-recall self-independent
    dynamics can oscillate") is false for the same reason: `theorem_5_1_false`. The proof applies
    Theorem 4.1 to the equilibria, but an equilibrium is a stable state of tie-broken best-response
    dynamics only if it is a fixed point of the tie-broken best-response map.
    *Borderline call.* Appendix B.1 explains consistent tie-breaking as "the best response is always
    unique, and depends only on the others' strategies". If "unique" is read as "the game has no
    ties", Corollary 5.2 is true (`corollary_5_2_of_unique`). We do not take this reading: the
    corollary and B.1 speak explicitly of tie-breaking rules, which would be vacuous without ties,
    and Theorem 5.1 / B.2 carry no such condition at all. The assumption fails in a natural,
    non-degenerate game, so R4 does not excuse it.
23. **Repaired statement.** `corollary_5_2`: two distinct pure Nash equilibria that are fixed points
    of the best-response map imply non-convergence. `corollary_5_2_of_unique` covers unique best
    responses. Best-response dynamics is modelled as `BRRule.sys` (historyless, self-independent, a
    fixed best reply `br i` depending only on the others' strategies).
24. **Not formalized.** Bounded-recall best-response dynamics of [35], and Theorems 5.3–5.6 / B.3–B.8
    (circuits, diffusion, BGP, congestion control). For these the same caveat applies: the
    "equilibria" must be stable states of the specific dynamics.

## Not formalized

25. Sections 6–8: `r`-convergence and Theorem 6.2 (snakes in boxes), Example 6.4 (randomness),
    Theorems 7.1 and 7.2 (communication complexity, PSPACE-completeness), and no-regret dynamics.
    Appendix G (consensus via IoD).
