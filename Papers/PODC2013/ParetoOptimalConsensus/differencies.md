# Differences between the formalization and the paper

Paper: Castañeda, Gonczarowski, Moses, *Pareto optimal solutions to consensus and set consensus* (BA, PODC 2013).
Full version: arXiv 1311.6902v1, *Good, Better, Best! — Unbeatable Protocols for Consensus and Set Consensus*.

## Errors in the paper

1. **Lemma 10 is false as stated** (`lemma10_false`, `SetConsensus.lean`). It is the same statement as Lemma 1 of
   the PODC 2016 version (the five conditions are hypotheses 1–4 of `Lemma1HypPaper` in
   `Papers/PODC2016/UnbeatableSetConsensus`). Counterexample there: `n = 6`, `k = 2`, `t = 1`, `V = {0, 1, 2}`.
   The 2016 folder also proves Lemma 10 with the extra hypothesis "every process alive and low at `m − 1` crashes
   in round `m`", which holds at every use, so Lemma 11 and Theorem 4 hold (`lemma11`, `theorem4`).
   *Rule:* R1: a false numbered lemma is a statement, and the instance is not degenerate (R2). Not excused by
   R3/R4: the fix adds a hypothesis that is not in the paper. This decides the verdict **❌** (not 🚨: Theorem 4 is
   true, R5).
2. **Lemma 6 is false when `d = t`** (`lemma6_literal_false`). Condition (b) holds vacuously for `t − d = 0`. With
   `n = 3`, `t = 1`, all inputs `1` and process `2` crashing silently in round 1, process `0` at time 1 satisfies
   (b) for `v = 0`, but `K_0 ∃correct(0)` fails. Proved version (`lemma6`): `K_i ∃correct(v)` iff `K_i ∃v` and
   ((a) or (b)), for `i` alive at `m` and `t < n`. *Rule:* R3 (⚠️). The proof sketch ("the number of distinct
   processes knowing `∃0`, including `i` itself") presupposes `K_i ∃v`, and the fix is local. The paper's
   statement "at time `t + 1`, `K_i ∃v` holds exactly if (a) or (b)" has the same issue.
3. **Corollary 1 (§3) needs `t ≥ 2`.** With `P0opt` read from the paper's description (item 12), `Opt0`
   strictly dominates `P0opt` when `t ≥ 2` and `n ≥ 4`, and when `2 ≤ n ≤ t + 1` (`corollary1`). For
   `n ≥ 3, t = 1`, and for `n ≥ 2, t = 0`, `P0opt` and `Opt0` make the same decisions (`p0opt_sameDecisions`), so
   `P0opt` is unbeatable (`p0opt_unbeatable`). *Rule:* borderline. Read as a universal statement over `(n, t)`,
   it is false for `t = 1`, which is not degenerate (R2). Read as the refutation of HMW's general claim, it is
   true, and the paper's own example needs two failures. We count it as ⚠️ (implied `t ≥ 2`, recoverable from the
   example, R3). It does not change the verdict, which item 1 decides.
4. **Lemma 15, proof.** (a) The inner induction measure `|C_i \ Z_i|` need not decrease: in Case II the paper
   notes `C_j ⊇ C_i`, and `j`, which does not see `⟨k, m⟩`, may know of fewer crashes, so `C_j ⊋ C_i` is possible.
   (b) The induction hypothesis is applied to `j ∈ Z_i` without checking its hypotheses: that `K_j ∃0` first holds
   at `m` (a `j` heard by `⟨i, m + 1⟩` may have known `0` at `m − 1`), and that `¬K_j ∃correct(0)` at `m`.
   (c) In the base case, `z ∈ C_i` needs an argument: a witness that `z` crashed would be a seen node that missed
   `z`'s message, so it would not be in `Z_i`.
   We prove Lemma 15 as stated, with an induction on `n − |Z_i|` (`ic`). Case C (`ic_caseC`): if `⟨z, m⟩` is
   hidden from `⟨i, m + 1⟩`, `z` survives round `m` in an indistinguishable run and decides `0` by the outer
   induction. Case II (`ic_caseII`): otherwise some `k` heard by `⟨i, m + 1⟩` missed `z`. We use runs
   `x ~_i x' ~_j x''`. In `x'`, `k` crashes in round `m + 1` reaching only `i`. `x''` is `x'` where `k` also
   receives `z`'s message. In `x''`, `Z_i` has grown by `k` and the hypothesis is applied to `i`. The paper's
   counting argument for Part 1 is not needed. Part 2 adds the case where `z` reached `⟨i, m + 1⟩` and the paper's
   "`Z_i = {i}`" argument (`g15_succ`). *Rule:* R1: claims inside a proof; the lemma is true, so 🛠️.
5. **Theorem 2, derivation.** "A precondition for deciding 1 is that no correct process ever decides 0" holds
   only for a correct decider. We make `i` correct in the run built from the hidden path
   (`exists_run_of_hiddenPath`). 🛠️-level, minor.
6. **Lemma 2, proof.** "Since `Q` dominates `P0`, `i` must decide by time `m`" needs `P0` to decide at `m`. This
   needs `m ≤ t + 1`, which holds because a value is first learnt by time `f + 1` (`first_le`). Minor gap.
7. **Typos.** Two different results are numbered "Corollary 1". In Lemma 15's last case, "j fails at `(r', m)`
   before sending any messages" must mean "`j`'s round-`m + 1` message reaches only `i`": `⟨j, m⟩` is seen by
   `⟨i, m + 1⟩`, as the construction of `r''` shows. In the same case, "the faulty processes in `r'` are those known
   by `⟨i, m⟩` to fail" should read `⟨i, m + 1⟩` (the count `F⟨i, m+1⟩ + 2` that follows uses it). We use the
   corrected versions.

## Modelling choices

8. **Model** (from `Papers/PODC2016/UnbeatableSetConsensus`): runs are `SyncCrash.Run P ℕ`; views are `SameView`
   (CSLib `FIIndist` on the communication graph); protocols are view-invariant decision rules; `DecidesAt` is the
   first firing while alive. Coan's reduction to full-information protocols is the companion's
   `theorem1_lockStep` (stated for `Optmin[k]`; the argument is generic).
9. **Inputs**: consensus and uniform consensus use `V = {0, 1}` (`bin`). The `k`-set part uses `V = {0, 1, 2}` for
   the counterexample and any `D ⊇ {0, …, k}` for Theorem 4.
10. **Knowledge** (`Knows`): `K_i φ` at `(r, m)` holds iff `φ` holds in every admissible run `r'` in which `i` is
    alive at `m` with the same view. The paper's local state is `⟨d(i, m), G_α(i, m)⟩` and `⊥` once `i` has
    crashed; the decision history is a function of the view. Restricting to live `i` is needed: our views of
    crashed processes keep growing. All knowledge statements are made for live processes, as in the paper.
11. **`∃correct(v)`** (`ExCorrect v r m`): some correct process knows `∃v` at time `m`. In Lemma 6 (b),
    "`K_i(K_j ∃v held at m − 1)`" is read as in the PODC 2016 version (Def. 3 there): `⟨j, m − 1⟩` is seen by
    `⟨i, m⟩` and has seen `v` (`carriers`). The number `d` of failures `i` knows of is `known r i m`, the processes
    `p` with `⟨p, m⟩` guaranteed crashed at `⟨i, m⟩`. For live `i` and `m > 0`, this is exactly Definition 3's
    `F⟨i, m⟩`, the processes `i` did not hear from in round `m` (`guarCrashed_now_iff`). At `m = 0` it is `0`, as in
    the paper.
12. **`P0opt`** of [HMW] is not defined in the paper. We use its one-line description: decide `0` when `K_i ∃0`;
    otherwise decide `1` at `m ≥ 1` if every process known at `m` to have crashed was already known to have
    crashed at `m − 1` (`NoNewFailure`). If HMW's actual protocol differs (e.g. only failures detected by missing
    messages count), the domination argument is unchanged (the condition still excludes hidden nodes at `m − 1`),
    but item 3's `t ≤ 1` analysis would need to be redone.
13. **Hidden path** (`HiddenPath`): `∃ b, ∀ ℓ ≤ m, ⟨b ℓ, ℓ⟩` hidden from `⟨i, m⟩`. This is equivalent to hidden
    capacity `≥ 1` (`hiddenPath_iff`), as the paper notes.
14. **`Maj`**: "`Maj = 0`" iff more than `n/2` inputs are `0`; "`Maj = 1`" iff at least `n/2` are `1` (`Thr`).
    `K_i(Maj = v)` is proved equivalent to the seen-count condition (`knows_maj_iff`). `Maj⟨i, m⟩` is `0` iff more
    than half of the seen inputs are `0`.
15. **Uniform consensus**: `SolvesUniformSetConsensus 1 t bin` from the companion (Decision for correct
    processes, Validity, at most one value decided by all deciders). `UUnbeatable` quantifies over uniform
    solutions.
16. **Generalizations**: Theorem 2, Lemma 2 and Lemma 3 are proved for both preferred values `a ∈ {0, 1}`
    (`Opt_a`), which gives `Opt1` for Theorem 3 with `n = 2`. Theorem 3 is proved for every `n ≥ 1` (the paper:
    `n > 2` by Lemma 8, plus `n ≤ 2` informally). Lemma 7 is derived from an abstract forcing lemma at time 1
    (`time1_forcing`), which also gives Lemma 14, Part 1.

## Statements

17. **Lemma 2** is stated for live `i` at the first time it knows `∃a`; it concludes `DecidesAt Q r i m a`.
18. **Lemma 3** is stated for live `i`, `never-known(∃a)` = "no correct process ever has `a` in its view".
19. **Lemmas 7, 8**: `i` alive at time `1` (Lemma 7). Lemma 8 concludes `¬ DecidesAt Q r i m v` for every `v`.
20. **Lemma 14, Part 2**: "`F⟨i,1⟩ < t`" is `known r i 1 < t`. **Lemma 15**: "`K_i ∃correct(0)` holds at `m + 1`
    for the first time" is `¬K_i ∃correct(0)` at `m` (it holds at `m + 1` by Lemma 6 (a)). Part 1 is stated with
    `m = M + 1` to avoid subtraction. Part 2 is also proved at `m = 0` (`g15_zero`, from Lemma 14).
21. **Theorems 5, 8**: "all decisions are made by time `f + 1` (resp. `f + 2`)" is stated for processes alive at
    that time. Theorem 8 is proved directly; the paper derives it from Theorem 6, which is not formalized.
22. **Lemma 16 / 17** conclude `¬ DecidesAt Q r i m v` for every `v`. Lemma 16 is stated with `0 < t` (and
    `t < n`), which the paper does not assume; for `t = 0` its hypotheses are contradictory (`K_i ∃0` implies
    `K_i ∃correct(0)` by Lemma 6), so nothing is lost. Theorem 5 covers `t = 0` through
    `uOpt0_eq_opt0` and Theorem 2, as the paper indicates.
23. **Corollary 1 (§3)** is stated as `¬ Unbeatable 1 t bin p0opt` under `(t ≥ 2 ∧ n ≥ 4) ∨ (2 ≤ n ≤ t + 1)`.
    Since `¬ Unbeatable` would also hold for a protocol that does not solve consensus, `p0opt_solves` proves
    that `P0opt` solves consensus for every `t` (a round without a new failure occurs by time `t + 1`).

## Not formalized

24. Theorem 1 (KoP) in general (we use its Validity instance `decided_mem_vals`); the topological proof of Lemma 10
    (Appendix B.1, Sperner) and the discussion B.2; `U-PROT_min-k` and Theorem 6; Theorem 7 and Lemma 19
    (last-decider unbeatability; the companion proves it for `Opt_min-k`); Lemma 20 (`O(n log n)`-bit
    implementations); the claim that `U-PROT_min-k` strictly dominates earlier uniform `k`-set protocols.
