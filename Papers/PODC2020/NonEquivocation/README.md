# Non-Equivocation in Synchronous Agreement — PODC 2020

Mads Frederik Madsen, Søren Debois. *On the Subject of Non-Equivocation: Defining Non-Equivocation in
Synchronous Agreement Systems.* PODC 2020. DOI
[10.1145/3382734.3405731](https://doi.org/10.1145/3382734.3405731). Formalized version: the PODC
proceedings version (no arXiv version; the online appendix with the full proofs was not available to
us). Numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The headline results hold. Under strong non-equivocation,
interactive consistency (IC) takes 1 round for any `n`, `t`. Under weak non-equivocation it takes
exactly `t + 1` rounds and `n > 2t` processes. Theorem 6.1 ("impossible for `n ≤ 2t`") is false for
`n ≤ 3`, and in that range it contradicts the paper's own Theorem 4.2. Under a reading in which `v`
ranges over values and `⊥`, Lemmas 4.7 and 4.8 are false, and a reading of line 8 of Algorithm 2
that allows `v = ⊥` breaks agreement. Algorithm 2 with `v ∈ V`, the type-consistent reading, is
correct. The authenticated Byzantine model of Section 7.2 is defined imprecisely. All these points
are repaired and proved.

## Mistakes in the paper

* **Theorem 6.1 is false for `n ≤ 3`; false only in degenerate cases.** The claim is: for `n ≤ 2t`,
  no algorithm solves IC under weak non-equivocation. But for `n = 2, t = 1` and `n = 3, t = 2` IC is
  solvable (`n = 1` is trivial). When at most one process is correct, only its own entry is
  constrained. So these cases reduce to `t = 0`, resp. `t = 1`, which Algorithm 2 solves. The proof
  needs four non-empty groups `O, Q, R, S`, i.e. `n ≥ 4`. The paper contradicts itself here: its own
  Theorem 4.2 ("solvable for any `n > 1` if `t ≤ 1`") covers `n = 2, t = 1`, which lies inside
  "`n ≤ 2t`". "WLOG `n = 2t`" with groups of size `t/2`
  hides this, and it does not fit odd `t` either. For `n ≥ 4` the four-run argument is correct. We
  prove the exact threshold: IC is solvable under weak non-equivocation iff `n > 2t` or `n ≤ 3`.
  (`theorem_6_1_false_n2`, `theorem_6_1_false_n3`, `theorem_6_1`, `icSolvable_wne_iff`)
* **Lemmas 4.7 and 4.8 are false when `v` ranges over `V ∪ {⊥}`.** The paper uses `V`
  inconsistently: line 2 of Algorithm 2 says "⊥ ∉ V", but Lemma 4.7 concludes "`v ≠ ⊥`" for
  `v ∈ V`, so there `⊥` counts as a value. Under that reading Lemma 4.7 ("no consistent majority for
  `⊥`") is false. Its proof claims that `Q` contains a correct process that reported `⊥`. That
  process may be the decider `p` itself, and by the convention `σ(p|p|q) = σ(p|q)` its "report" is
  the `⊥` it received. Instance: `n = 3`, `t = 1`, two rounds, and the faulty `q = 2` omits
  everything to `0` but otherwise behaves correctly. Then `{0, 2}` is a consistent `2`-majority for
  `⊥` at `0`, since the only admissible route is `0|2`. At `1`, `{1, 2}` is one for `v`.
  * Lemma 4.8 is false on the same instance: two correct processes have `2`-majorities for different
    values. Its proof appeals to Lemma 4.7, which is the failing step.
  * A reading of line 8 that allows `v = ⊥` then breaks agreement: `0` returns `⊥` and `1` returns
    `v`.
  * Algorithm 2 is not wrong as printed. Line 9 returns `v` into a vector of values, so the
    type-consistent reading is `v ∈ V`. Under it the lemmas hold (`lemma_4_8` for `Maj`) and the
    algorithm is correct.

  (`lemma_4_7_false`, `literal_line8_fails`, `theorem_5_1`)
* **The proof of Theorem 5.1 is only sketched; statement true.** The hard case is when one correct
  process has a consistent majority and another has none. The paper defers it to an appendix we
  could not access. We prove it as follows: every member of `Q \ {q}` gets value `v` in the
  recursive vector, which gives `≥ t` votes. Any competing value with `≥ t` votes comes from a
  correct process (only `t − 1` faulty ones remain). By weak non-equivocation of `q`'s first-round
  message it equals `v`. This also covers `v = ⟨⊥⟩`. (`psl_correct`)
* **The authenticated Byzantine model of Section 7.2 is defined imprecisely; the intent is clear.**
  As printed, `σ(w'|p|w) ∈ {σ(p|w), ⊥}` for correct `p`. This compares with what `p` *received*
  and forgets the `⟨⊥⟩` convention of Definition 2.1. A correct process that observes an omission
  reports `⟨⊥⟩ ≠ σ(p|w) = ⊥`. So with `k ≥ 2` rounds the literal definition excludes crash
  executions, and Fig. 4's "Omission ⊆ AB" fails for it. We use the intended model: absent, `p`'s
  report, or `⟨⊥⟩`. With it, all Fig. 4 relations hold. (Our first attempted repair, without
  `⟨⊥⟩`, fails for `k ≥ 3`; this concerns our repair, not the paper.)
  (`silentσ_not_authByzLiteral`, `authByz_of_omission`)
* **Smaller imprecisions.**
  * In Definitions 3.1 and 4.1, `r = p` must be excluded. Otherwise the convention
    `σ(p|p|w) = σ(p|w)` forces faulty processes to relay truthfully.
  * In Algorithm 1, line 5 `r` must range over processes other than `p` and `q`. Otherwise line 6
    returns `⊥`.
  * Line 20 of Algorithm 2 must make a deterministic choice.
  * Algorithm 2's recursion bottoms out at `t = 0`, not at `t = 1`.
  * Theorem 4.2 does not need `n > 1`, and the Section 3 algorithm does not need `n > t`.
  * Example (3) of §7.2 deduces "`t ≥ 2`, `n ≥ 5`" from an algorithmic criterion ("general-omission
    algorithms cannot solve agreement"). As a pure fault-space separation, a smaller witness exists:
    a single faulty process lying consistently about its own value (`n = 3`, `t = 1`) is in
    weak NE ∩ AB but not in Omission (`sne_inter_authByz_not_le_omission`). This reinterprets the
    claim; it does not refute it.
  * Section 3 has a truncated sentence ("a faulty process `q` may receive `v` from").

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** The paper's framework, formalized directly (`Model.lean`):
* `n` synchronous processes (`Fintype P`) with reliable channels run the full-information relay
  protocol of Pease–Shostak–Lamport for `k` rounds. The outcome is a message map
  `σ : List P → Option V` (`none` = `⊥`). `σ (p :: q :: w)` is what `q` told `p` in round
  `|w| + 1`, and `σ [p]` is `p`'s private value. Only routes without consecutive duplicates are
  constrained. `⟨⊥⟩` is a distinguished ordinary value (`OmitVal`).
* A fault model is a predicate on (rounds `k`, static faulty set `F`, `σ`). We define:
  * `byzantine` = Definition 2.1 only;
  * `wne` = Definition 2.1 + Definition 4.1;
  * `sne` = Definition 2.1 + Definition 3.1;
  * `omission`, `crash`, `authByz` (§7.2, Fig. 4).
* An algorithm is a deterministic function `A p (view k σ p) q`. Here `view` is `p`'s local view
  of the first `k` rounds. `SolvesIC M k t A` requires validity and agreement of IC for every
  admissible `σ` with `|F| ≤ t`; termination is implicit (decision after `k` rounds).
* Impossibility results quantify over all such algorithms. Their runs are built as families of
  full-information executions in which a faulty process imitates the correct behaviour of another
  "world" towards everybody it does not omit (`ExecSys`, FLM-style). So it never equivocates.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 2.1, 3.1, 4.1 | `NonFaulty`, `StrongNE`, `WeakNE`; models `wne`, `sne` | `Model.lean` |
| §3: IC in 1 round under SNE (`n > t`) | `sne_solvesIC` (any `n`, `t`); `sne_not_solvesIC_zero` (1 round optimal) | `Strong.lean` |
| Theorem 4.2 (Algorithm 1, `t ≤ 1`) | `theorem_4_2` | `Alg1.lean` |
| Def. 4.3, Lemmas 4.4, 4.5, 4.6, 4.8 | `Maj`, `lemma_4_4`, `lemma_4_5`, `lemma_4_6`, `lemma_4_8` | `Majority.lean` |
| Lemma 4.7 | `lemma_4_7_false`; repaired `lemma_4_7_repaired` | `Counterexamples.lean`, `Majority.lean` |
| Algorithm 2, Theorem 5.1 (`n > 2t`, `t + 1` rounds) | `psl`, `alg2`, `theorem_5_1` (via `psl_correct`) | `PSL.lean` |
| line 8 with `v = ⊥` allowed | `literal_line8_fails` | `Counterexamples.lean` |
| Theorem 6.1 (`n ≤ 2t` impossible) | `theorem_6_1` (`4 ≤ n ≤ 2t`), `not_solvesIC_of_groups`; false: `theorem_6_1_false_n2`, `theorem_6_1_false_n3` | `Tightness.lean` |
| exact resilience | `icSolvable_wne_iff` (`n > 2t ∨ n ≤ 3`) | `Tightness.lean` |
| §6: `t + 1` rounds necessary | `not_solvesIC_omission_of_le`, `not_solvesIC_wne_of_le` (`k ≤ t`, `n ≥ t + 2`) | `RoundLowerBound.lean` |
| abstract: "`t + 1` rounds, `n > 2t`" | `wne_rounds_exact` | `Main.lean` |
| §7.1: WNE gives crusader agreement in 1 round | `crusader1_solvesCA_wne`; fails under Byzantine: `crusader1_not_solvesCA_byzantine` | `Crusader.lean` |
| §3, §4, §7.2, Fig. 4 (fault model spaces) | `omission_of_crash`, `wne_of_omission`, `wne_of_sne`, `authByz_of_omission`, `crash_not_le_sne`, `sne_crash_silent`, `omission_not_le_crash`, `sne_not_le_crash`, `sne_inter_authByz_not_le_omission`, `sne_not_le_authByz`, `authByz_not_le_wne`, `paperEx3` | `FaultModels.lean` |
| §7.2 AB definition | `silentσ_not_authByzLiteral`, `silentσ_not_authByzRep` | `FaultModels.lean` |

**Not formalized.**
* The informal converses "Byzantine broadcast oracle ⇒ strong NE" (§3) and "crusader agreement
  oracle ⇒ weak NE" (§7.1), including Dolev's `t + 2`-round mapping.
* The "algorithms can / cannot solve agreement" reading of the §7.2 examples (only their fault-model
  memberships are proved).
* The consensus column of Table 1.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: the fault models are inhabited by fault-free and crash executions
(`ExecSys`, `mkσ`). Algorithm 2 and the Section 3 algorithm satisfy the solvability hypotheses
(`theorem_5_1`, `sne_solvesIC`). The model is self-contained (Mathlib, plus the shared vote counting `Finset.countEq` of
`Cslib/Foundations/Data/Finset/Quorum.lean`). `Model.lean` + `Exec.lean`
(PSL message maps, imitation-world executions) are CSLib candidates.
