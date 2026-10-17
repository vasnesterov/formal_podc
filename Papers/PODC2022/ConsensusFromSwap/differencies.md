# Differences between the formalization and the paper

Paper: Sean Ovens, *The Space Complexity of Consensus from Swap*, PODC 2022, arXiv 2305.06507 v2.

## Model

1. **Determinism (modelling restriction).** Only deterministic algorithms are modelled, so all lower bounds are for
   obstruction-free algorithms. The paper's lower bounds also cover nondeterministic solo-terminating algorithms,
   and hence randomized wait-free ones (Corollaries 11, 19, 23).
   * For Section 5 the paper itself relies on the Ellen–Gelashvili–Zhu transformation, which is not formalized.
2. **Inputs are part of the initial state** (as in the paper). Each process's input is in its initial local state;
   there are no invocations. A step of a process in an output state is a no-op (the paper's scheduler never picks
   decided processes, which is equivalent).
3. **One step = one operation plus local computation**, folded into the continuation. In Algorithm 1 the decision
   therefore happens in the step that swaps the last object of a conflict-free iteration. With this convention,
   Lemma 8's bound `8(n−k)` is correct.
4. **Objects.**
   * Swap objects store values of an arbitrary type, not only `ℕ`; Algorithm 1 stores (lap counter, identifier)
     pairs.
   * Initial object values are arbitrary (`Alg.mem₀`).
   * Section 4 is proved for every object type all of whose operations overwrite the value
     (`ObjSpec.OverwritesState`, CSLib), which generalizes swap.
   * Section 5 uses readable swap objects over one finite type `D` of size `b` (the paper's "WLOG").
   * The simulations of historyless objects ([14]) are not formalized, and neither are Corollaries 19 and 23.
5. **Correctness is relative to an input set `S`** (`SolvesSetAgreement A k S`, `ObstructionFree A S`). The
   paper's `(k+1)`-valued problem corresponds to any `S` with at least `k + 1` elements.
   * Validity is the paper's weak form: the decided value is the input of *some* process.
   * For Algorithm 1 we also prove the strong form: the decided value is the input of a process that took a step
     (`lemma7_validity_strong`).
6. **Section 5 assumptions** (`Setting C₀`): agreement and solo termination only for configurations reachable
   from one initial configuration `C₀`. The theorems derive them from `SolvesSetAgreement A 1 univ` and
   `ObstructionFree A univ` (`setting_of`).

## Definitions

7. **Valency (under-specified in the paper).**
   * `CanDec Q C v`: some `Q`-only execution from `C` leads to a configuration in which some process of `Q` *has
     decided* `v`. Decisions before `C` count.
   * `Biv Q C`: `CanDec Q C 0 ∧ CanDec Q C 1`; "univalent" means `¬ Biv`.
   * Why decisions before `C` must count: under the other reading (decision inside the execution), Lemma 13's
     proof breaks when both processes of `Q` decide within `α` (see README, item 2). With agreement, both readings
     agree on bivalence.
8. **Indistinguishability `α ∼_p α'`** (`Indist`): `p` has the same local state before each of its steps, and the
   same final local state. For deterministic processes this is the paper's "same sequence of steps", up to the
   responses, which `p` cannot observe beyond its state.
9. **"The value of `B` changes during `λ`"** (`Changes`): some configuration of `λ` (a prefix) has a value different
   from the initial one.
10. **Covering** (`Covering`, `Covers`): a list of (process, object) pairs with distinct processes, each poised on
    an operation that overwrites the object. Lemma 16 additionally keeps the objects distinct (`objs_nd`), and
    lists the covering process `p_i` first in `β_{i+1} = dβ_i`.

## Proofs

11. **Lemma 6 / Algorithm 1.**
    * **Modelling note: `k ≥ 1`.** `lemma6_agreement` assumes `1 ≤ k`, as the paper does throughout. For `k = 0`
      the statement fails (example in `Alg1Agree.lean`).
    * **Observation 4 false for `m = 1` (false only in a degenerate case).** Example in `Alg1Agree.lean`. Lemma 6
      does not need it in that case.
    * **Restructured proof.** It works with *any* `k + 1` decided values ordered by first decision time; "first
      decider" and "prefix with exactly `k + 1` values" are not needed.
    * **Lemma 5 as an invariant.** It is proved as a forward invariant (an injective "destroyer" map) instead of
      the paper's history argument. It also yields that the destroyers are undecided at `C`, which the paper argues
      inline.
    * **Missing case in Step 2.** The paper omits `C = C_t`; that case is trivial.
    * **Number of objects.** The proof works for any `N ≥ n − k` objects (`hN : n ≤ N + k`).
12. **Theorem 10.**
    * **Different induction (proof restructured).**
      * The paper's split: `R` = `⌈n(k−1)/k⌉` processes, applying the `(k−1)`-case to "the algorithm restricted to
        `R`".
      * Ours (`theorem10_gen`): we split off `#objects + 1` processes and use decisions *by processes of `R`*
        (`decBy`).
      * Our base case is `k = 0` and is trivial. The final bound is the same: `n ≤ k(#objects + 1)`, i.e.
        `⌈n/k⌉ − 1 ≤ #objects`. No hypothesis `n > k ≥ 1` is needed.
    * **Imprecision in the paper's restriction.** The restricted algorithm need not satisfy validity, because a
      decided value may be the input of a process outside `R`. Resetting the outside inputs (invisible to `R`)
      fixes this; we do so in the proof.
13. **Lemma 9** is stated for an arbitrary configuration `C` (the paper's `Cα`) and an arbitrary `D` (the paper's
    all-`v` initial configuration). The hypotheses are exactly the facts the proof uses: `k`-agreement from `C`,
    validity and solo termination from `D`.
14. **Lemma 13.** Proved with the inclusive valency of item 7. The proof is otherwise the paper's (two cases: the
    next step of `α` accesses a covered object or not), for arbitrary objects.
15. **Lemma 14 (proof gap; statement true).** `j` is chosen minimal over `(Q ∪ P_i)`-only executions; the paper's
    text quantifies over all executions, which does not give (a). We state Lemma 14 for an arbitrary set
    `R ⊇ Q` (the paper's `Q ∪ P_{i+1}`) and a process `p ∉ R`.
16. **Lemma 16, Case 2, (d) for `i + 1` (proof gap; statement true).**
    * **The gap.** From "`Q` univalent in `C_{i+1}λ'd`" the paper concludes "`Q` univalent in `C_{i+1}λ'dβ_i`",
      but univalence is not preserved by steps outside `Q`.
    * **Repair.** Case split. If `β_i` changes an object of `Y_i`, use the induction hypothesis (d); otherwise
      apply Observation 15.
17. **Lemma 20.**
    * **Case 1, choice of `S_{i+1}`.** We always remove the process covering `B*`, if any; the paper removes it
      only if it is poised to swap `v*`. Property (d) still holds: `f` gains 2 and `S` loses at most 1.
    * **Case 2.** The paper's `S_{i+1} = (S_i − {p}) ∪ {p_i}` and `S_i ∪ {p_i}` are implemented uniformly, as
      `(p_i, B*)` followed by the pairs of `S_i` not covering `B*`.
18. **Theorems 18/22.** The bounds are stated as `n − 2 ≤ #objects` and `n − 2 ≤ (3b + 1)·#objects`. They hold for
    all `n` (truncated subtraction), so the hypotheses `n ≥ 2` and `b ≥ 2` are not needed.

## Typos

19. Lemma 16, Case 2: "then `P` is univalent in `C_{i+1}λ'`" should be `Q`.
20. Section 5.2 (example for `i = 1`): "`S_1 = {p_1}` covers" should be `{p_0}`.
21. Lemma 6, Step 1: "`V_j[v_j] = ℓ_j > V_{k+1}[v_j] + 2`" should be `V_j[x_j] = ℓ_j > ℓ_{k+1} ≥ V_{k+1}[x_j] + 2`.
