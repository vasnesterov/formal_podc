# Differences between the formalization and the paper

Paper: Castañeda, Gonczarowski, Moses, *Unbeatable Set Consensus via Topological and Combinatorial
Reasoning*, PODC 2016, arXiv 1605.07354v1.

## Errors in the paper

1. **Lemma 1 is false as stated.** Counterexample with `n = 6`, `k = 2`, `t = 1`, `m = 1`, inputs in any
   `D ⊇ {0,1,2}` (`lemma1_paper_false`, `Counterexample.lean`). The protocol `cexProtocol` solves nonuniform
   2-set consensus with `t = 1`, and low processes decide at time 0. Hypotheses 1–4 of Lemma 1 hold for
   process `0` at time 1 with `v = 0`, but it decides `2`. The gap is in the "changes" of the combinatorial
   proof (and in the topological proof). A process `j_b` must receive no message carrying an already-used low
   value in round `m`. Messages carrying `v` from processes that do not crash in round `m` cannot be
   suppressed without exceeding `t` crashes.
   The failure is not tied to `t < k` (where `k`-set consensus is easy). Pen-and-paper variant for any
   `t ≥ 1`, `k ≥ 2`, `D = {0, …, k}` (e.g. `t = k = 2`, `n = 7`), not in Lean: take `Optmin[k]` and add the
   rule "at time 1, a process that was high at 0, whose only low value is `0` and that saw `0` from `≥ t + 1`
   processes decides `k`". Such a node proves that a correct process holds `0`. Then every process alive at
   time `≥ 1` is low with `Min = 0`, and the correct processes that decided at time 0 also have input `0`.
   So the correct decisions are in `{0, k}`. In runs without such a node the protocol behaves like `Optmin[k]`.
   With three carriers `x, y, w` of `0` and the same `i, z, j₁, j₂` as above, `i` decides `k`.
   *Fix:* hypothesis 5 (`Lemma1Hyp.lowCrash`): every process alive and low at `m − 1` crashes in round `m`.
   It holds when some process is high at time `m` (`crash_eq_of_low_of_high`). That covers both uses:
   Lemma 3, and the induction hypothesis inside Lemma 1 (where `i` is high at `m − 1`).
2. **Lemma 1, proof:** the induction hypothesis is applied to `i_w` "to decide by `m − 1`" after checking
   only hypothesis 3. We apply it at the first time `t₀ ≤ m − 1` at which `i_w` is low. We check
   hypotheses 1, 2 and 4 (the `j_b`, made correct, are hidden from `⟨i_w, t₀⟩` and high before) and 5.
3. **Lemma 5, `m = 0`:** "all initial values are 0" contradicts `r'_i(0) = r_i(0)` when `i`'s input is a
   low value other than `0`. We let all inputs equal `i`'s input.
4. **Theorem 3, proof:** "`K_j ∃correct(w)`" (= "`j` knows that `w` will persist") is used as "some
   correct process knows `w` at `m'_j`". We prove instead the persistence claim stated after Definition 3
   (`persist`), which suffices. We check that the `d` known failures are disjoint from the `t − d`
   carriers and from `j`.
5. Typo in the proof of Theorem 3: `v = Min⟨i, m'_i⟩ < k − 1` should be `≤ k − 1` (`< k`).

## Modelling choices

6. **Runs / adversaries** are CSLib `SyncCrash.Run P ℕ`: input vector, crash round `c ≥ 1`, and the set
   reached in round `c`. This is exactly the paper's crash failure pattern (correct before, partial in
   round `c`, silent after). `Adm t D r`: at most `t` crashes, inputs in `D`.
7. **Inputs** are natural numbers in a set `D` with `{0, …, k} ⊆ D` (hypothesis `hD`). This includes the
   paper's `{0, …, k}` and footnote 4 (`{0, …, d}`, `d ≥ k`), and also `D = ℕ`. "High" means `≥ k`. The
   paper's `n ≥ 2` and `t ≤ n − 1` are not needed.
8. **Protocols** are decision rules of full-information protocols: `dec r i m : Option ℕ`, invariant under
   equality of views (`SameView` = CSLib `FIIndist` on the communication graph `comm r`). The local state
   `⟨β, G_α(i, m)⟩` is represented by the view alone: `β` is a function of the views at earlier times,
   which the view at `m` determines. A process decides at the first time its rule fires while it is alive
   (`DecidesAt`). `LockStep.lean` shows that every deterministic message-passing protocol of CSLib's
   `SyncCrash` model is such a rule with the same first-decision times (`hist_eq_of_sameView`,
   `decidesAt_ofLockStep_iff`). Hence `theorem1_lockStep`. This is our proof of the paper's appeal to Coan.
9. **Views of crashed processes** are defined (the view a process would have). The paper does not
   define local states of crashed processes. Decisions require being alive. Hidden nodes may be nodes of
   processes that already crashed, as in the paper.
10. **Seen** = message chain (`DynNet.Journey` on `comm r`, with stays). **Guaranteed crashed**
    (`GuarCrashed`): `⟨i, m⟩` has seen a node `⟨h, s + 1⟩` with `s + 1 ≤ ℓ`, `h ≠ j`, that did not
    receive `j`'s round-`s + 1` message. This makes the paper's "`i` heard from someone who did not hear
    from `j` in some round `≤ ℓ`" precise (including `h = i`).
11. **`Vals⟨i, m⟩`** is defined as the set of seen inputs. The paper defines it by knowledge (`K_i ∃v`).
    The paper itself identifies the two; the direction used (decisions are seen values) is
    `decided_mem_vals`, our instance of Theorem 4 (KoP) for Validity. It needs two distinct values in `D`.
12. **Hidden capacity** `hc r i m` = minimum over `ℓ ≤ m` of the number of nodes at time `ℓ` hidden from
    `⟨i, m⟩` (Definition 2).
13. **Unbeatability** (Def. 1): `Unbeatable k t D P` = `P` solves the problem, and every solution `Q` with
    `Q ⪰ P` satisfies `P ⪰ Q`. This is equivalent to "no solution strictly dominates `P`". Domination is
    per process and per adversary, as in §2.2.
14. **Last-decider domination** (Def. 6): "the last decision" is read as the last decision of a correct
    process (as in [4]): `LDDominates Q P` iff, in every run, whenever all correct processes have decided
    by `m` in `P`, they have decided by `m` in `Q`. This is equivalent to comparing the times of the last
    correct decisions.
15. **Uniform `k`-set consensus** (`SolvesUniformSetConsensus`): Decision for correct processes,
    Validity, and at most `k` values decided by any processes.
16. **Definition 3:** "`i` knows of `d` failures at `m`" is read as `d` = number of processes `p` with
    `⟨p, m⟩` guaranteed crashed at `⟨i, m⟩` (`known`). The nodes `⟨j, m − 1⟩` "seen by `⟨i, m⟩` that have
    seen `v`" are `carriers`; for `m = 0` there are none. The condition "`i` is active at `m`" in the first
    bullet is not part of the rule: decisions are only taken by live processes.
17. **Protocol `u-Pmin[k]`**: the first condition is parsed `(low ∨ HC < k) ∧ persists` (checked on the
    rendered PDF).

## Statements

18. **Proposition 1:** "all processes decide by `⌊f/k⌋ + 1`" is stated for processes alive at that time
    (`optmin_decidesBy`); `f` is the number of crashes of the run.
19. **Lemma 1:** stated for a process `x` alive at `m` (implicit in the paper). Hypotheses 1 and 4 are
    vacuous at `m = 0` ("`⟨j, −1⟩` is high"). Hypothesis 5 is added (item 1). The conclusion is exactly
    `DecidesAt Q r x m v` (first decision at `m`, value `v`).
20. **Lemma 2** is not one theorem but the construction `chainRun` with the lemmas `ChainHyp.sameView`
    (`r'_i(m) = r_i(m)`), `.mem_vals` (a), `.vals_subset` (b), `.hidden_col` and `.hidden_of_not_w` (c).
    It is parametrized by the last time `L ≤ m` of the witness columns. Lemma 3 uses `L = m`; Lemma 1 uses
    `L = m − 1` and re-chooses the round-`m` messages (`lastRun`). The last column crashes in round `L + 1`
    sending nothing; making `i` and other processes correct ("w.l.o.g. never fail") is the separate
    operation `modify`. We assume `i` alive at `m` (the paper: active at `m − 1`).
21. **Lemma 3** is stated for live `⟨x, m⟩` and concludes `Q.dec r x m = none`: the rule does not fire,
    which is stronger than "does not decide at `m`".
22. **Lemma 1's sequence of changes** is processed in the order `b = 0, 1, …, k − 1` instead of
    `k, …, 1`; this is immaterial.
23. **Theorem 3:** the time bound is stated for processes alive at `min(⌊t/k⌋ + 1, ⌊f/k⌋ + 2)`.

## Not formalized

24. The topological proof of Lemma 1 (Appendix B.1, Sperner's lemma), Proposition 2 and its proof sketch
    (B.2), Conjecture 1, Lemma 6 (`O(n log n)`-bit implementation), the claims around Fig. 4
    (`u-Pmin[k]` strictly dominates earlier protocols), and Remark 2 except "domination implies
    last-decider domination" (`ldDominates_of_dominates`).
