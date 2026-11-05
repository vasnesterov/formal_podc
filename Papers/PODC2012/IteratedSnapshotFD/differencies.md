# Differences between the formalization and the paper

Paper: M. Raynal, J. Stainer, *Increasing the Power of the Iterated Immediate Snapshot Model with
Failure Detectors*, PODC 2012 (brief announcement). Formalized from the full version: IRISA research
report PI 1991, February 2012 (hal-00670154v1), whose numbering we follow.

## Modelling choices

- **IIS schedules** (`Model.lean`, `Schedule`). A round is the set of participants of `IS[r]` and their
  views, with self-inclusion, containment and immediacy as fields (`ISRound`). Participation is
  non-increasing (a process that skips a round has crashed). Rounds are numbered from `0` in `Schedule`
  (the paper starts at `1`); `Fig3*.lean` keep the paper's numbering and convert explicitly.
  Any number of crashes is allowed; nothing requires a correct process unless a theorem says so.
- **Strongly correct processes** (`Schedule.SCk`, `Schedule.SC`). Literal Section 2.6, with one change: in
  `SC₀` we also require that `i` writes in the round. The two definitions agree whenever some process is
  correct (the paper assumes this); without a correct process the paper's `SC₀` would contain every
  process because "`∀ j ∈ C`" is vacuous. `SC` is the union of the chain (the paper's `SC_K`, `K` the
  stabilization index; the same set since the chain is increasing, `SCk_mono`).
- **Algorithm of Figure 5** (`Consensus.lean`). The tuple `⟨est, r_leader, val_ld_seen, dec⟩` is `Loc`,
  `⊥` is `none`. Line 5 is `wr`. Lines 7–18 are the relation `Upd`, one constructor per branch. The
  choices "`∃ v`" at lines 12 and 15 are nondeterministic: `Upd` admits every witness, so all safety
  results hold for every resolution. The leader read at line 4 is an arbitrary function
  `ld : ℕ → P → P` (the failure-detector output). `Ω*` is used only for termination (`OmegaStar`: some
  strongly correct `ℓ` is output by every participant from some round on). Crashed processes keep their
  last state (`Exec.frozen`); a decision is `dec = true` with value `est` (`Exec.Decides`).
- **Simulation of Figure 3** (`Fig3.lean`, `Fig3Live.lean`). An operational semantics with atomic
  steps: one iteration of the repeat loop of lines 2–3 (collect + read of `C` + test of `PROP`), line 4,
  and lines 6–7 (`arw_write_snapshot`). `S[r].collect()` and `S[r].arw_write_snapshot()` are atomic: a
  sequential execution is one legal execution of these objects (Figure 4 run sequentially returns
  exactly the writers so far). Positive results proved in this model (Theorems 2 and 3) are therefore
  proved for the runs whose base objects behave atomically. A counterexample in it (Section 4.4) is a
  legal run of the paper's algorithm. A failure-detector history is a function `H i t` of the simulator
  and the global time. A simulator is correct iff it is scheduled infinitely often (`SCorrect`); a crash
  is the end of its steps. The output of the simulated `C*` at `q_i` in round `r` (`Cfg.out`) is
  `FD_VAL[i]` when `q_i` invokes `S[r].arw_write_snapshot()`. With the other natural convention (value at
  the *beginning* of round `r`, i.e. the value of round `r − 1`) the Section 4.4 counterexample is
  unchanged, since the outputs alternate.
- **`Ω_k`** (`IsOmegaK`): only "eventually all output the same `L` containing a correct process"; the
  constraint `|L| = k` is dropped (it is not used). **`◇P`** (`IsDiamondP`): eventually every
  simulator trusts exactly the correct simulators. **`Σ`** (`IsSigma`): only the intersection property;
  the completeness property is void in the failure-free run used.

## Statement-level issues (decided by `verdicts.md`)

- **Section 4.4 and Theorem 4 false for `Σ`** (`Fig3.sigma_simulation_false`). Two simulators,
  failure-free, a legal `Σ` history and a fair schedule. Figure 3 with `PROP_{◇P}` (the predicate
  Section 4.4 prescribes) yields an IIS execution in which `q_1` is weakly correct while the simulated
  `Σ*` outputs contain `q_1` forever, also at the strongly correct `q_0`. So the simulated failure
  detector is not in `Σ*` and the produced run is not an `IIS_2[Σ*]` run. Theorem 4 ("for the failure
  detector classes studied in this paper", `t = n − 1 = 1`, where the extra conjunct
  `|arw_view| ≥ n − t − 1 = 0` is void) is false for `Σ`. **Label ❌ (R1, R5).** The claim is a
  correctness claim about the paper's simulation and a numbered theorem, but not a headline: the
  headline equivalences, Theorem 2 / Corollary 1 (`Ω_k`) and Theorem 3 (`◇P`), are unaffected, and `Σ`,
  `S`, `◇S`, `S_x`, `◇S_x` are handled in a one-paragraph remark (Section 4.4) and in the `t`-resilience
  extension (Section 5). *Borderline:* the abstract says the simulations work "for a large family of
  failure detector classes". That claim stays true for `{Ω_k}_k`, `◇P`, `P`, so we do not count it as a
  false headline (R5). The introduction is more specific ("This simulation is generic in the sense that
  it works for any of the previously cited failure detectors", which include `Σ`), but the headline
  result, the equivalence of `ARW_n[C]` and `IIS_n[C*]`, is existential and is not refuted for `Σ`
  (only this simulation is); R5 then gives ❌, not 🚨 (reviewer's call). Not an implied-assumption or typo case (R3/R4): repairing it changes the
  simulation (e.g. `C*.read()` must return the value used at the last owned round), and even then the
  literal `Σ*` also constrains weakly correct processes, whose quorums need not consist of strongly
  correct processes (`q_1`'s quorum is `{q_0, q_1}` in our run).
  - The same history is also an `S` and a `◇S` history (`p_0` is never suspected), and the run violates
    the completeness of `S*` / `◇S*` (`q_1` is not permanently suspected by `q_0`). We did not formalize
    `S`, `◇S`, `S_x`, `◇S_x`.
- **Theorems 2 and 3 (`Ω_k`, `◇P`): true** in the atomic-step model (`Fig3Live.lean`): liveness, the
  correspondence between correct simulators and correct simulated processes, and the `Ω*_k` / `◇P*`
  properties of the simulated detector. The claim "produces an execution that could have been obtained
  in `IIS_n[C*]`" is checked through these properties plus the IS properties of `simSchedule`. The
  simulated algorithm `A` and the task are not modelled. Label ✅.
- **Theorem 5 / Lemmas 1–3 (consensus in `IIS_n[Ω*]`): true** (`theorem5`). Proof of Lemma 3 repaired, see
  below. Proofs of Lemmas 1 and 2 are fine up to routine details. **Label 🛠️ (R1).**

## Proof gaps

- **Claim C1 (inside the proof of Lemma 3, also used by Lemma 2).** The induction ("all the processes
  that write `⟨−, ℓ, true, false⟩` during round `r + 1` have adopted their estimate at line 13, so it
  is the only one present") ignores that line 13 may adopt the estimate of the leader `p_ℓ` itself
  (first disjunct of line 12) instead of the estimate of a `val_ld_seen = true` tuple (second disjunct).
  Both may be present in the same view, and line 12 does not say which one to take. The leader's own
  estimate may have changed since it was voted for (line 15 lets it adopt a value, or it may have
  followed another leader meanwhile). The last step of the proof of Lemma 3 ("in both cases they adopt
  `v`") has the same gap. Repair: the stronger invariant `Inv` adds (L), "the tuple written by the
  leader named by the `true` tuples carries the same estimate". Its preservation (`Exec.inv_succ`) is a
  case analysis using containment and **immediacy**: a process that sees `p_ℓ` in a uniform view
  forces `p_ℓ`'s view to be uniform as well. Agreement then holds for every resolution of the choices at
  lines 12 and 15 (`Exec.agreement`).
- **Lemma 2** (termination) is proved in the stronger form "every correct process decides"
  (`Exec.termination_correct`). Weakly correct processes decide too, because the decision of a strongly
  correct process reaches every correct process (`Exec.all_decide_of_SC`).
- The agreement and validity proofs do not use `Ω*` at all (arbitrary leader outputs).

## Other remarks

- **Not formalized:** Theorem 1 (simulation of `ARW_n[C]` in `IIS_n[C*]`, the Borowsky–Gafni
  simulation of Figure 2), Corollary 1 and the solvability equivalences (no task/solvability layer),
  Theorem 4 beyond the `Σ` counterexample and its round-level core `thm4b_core`.
- **Corollary 1 needs an argument the paper does not give.** The paper never defines solving a task in
  `IIS_n[C*]`. Lemma 2 suggests that only strongly correct processes must decide. Then the simulation
  of Theorem 2 leaves correct ARW simulators whose simulated process is weakly correct without a
  decision. Under the other reading (every correct IIS process decides), Theorem 1 leaves weakly correct
  IIS processes without a decision. For colorless tasks either gap closes by letting undecided processes
  adopt a decision written by another (in IIS weakly correct processes see the strongly correct ones
  forever; in ARW a simulator can read a shared decision register). This is the standard trick and
  presumably why Corollary 1 is restricted to colorless tasks, but "immediate consequence" omits it. Not
  formalized, so it does not affect the verdict.
- Section 2.6's informal claims are formalized: `SC₀ ≠ ∅` if some process is correct
  (`SCk_zero_nonempty`), `SC ⊆ C` (`correct_of_mem_SC`), the chain is increasing (`SCk_mono`), and after
  some round strongly correct processes see only strongly correct processes (`eventually_view_SC`,
  Section 3.2).
- Round-level cores of the strong-correctness arguments (`SimulationCores.lean`): `thm3_core`
  (Theorem 3), `thm2c_core` (Theorem 2(c)), `thm4b_core` (Theorem 4(b)).
