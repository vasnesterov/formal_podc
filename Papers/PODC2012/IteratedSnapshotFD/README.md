# Failure Detectors for the IIS Model — PODC 2012

Michel Raynal, Julien Stainer. *Brief Announcement: Increasing the Power of the Iterated Immediate
Snapshot Model with Failure Detectors.* PODC 2012. DOI
[10.1145/2332432.2332498](https://doi.org/10.1145/2332432.2332498). Formalized version: the full
version, IRISA research report PI 1991, February 2012 (hal-00670154v1); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The generic simulation of Figure 3 does **not** work for `Σ`, contrary to
Section 4.4 and Theorem 4: with two simulators it produces runs whose simulated failure detector is
not in `Σ*`. The headline simulations for `Ω_k` (Theorem 2) and `◇P` (Theorem 3) hold, and so does the
`Ω*`-based consensus algorithm (Theorem 5), whose agreement proof needed a repair.

## Mistakes in the paper

### ❌ Section 4.4 and Theorem 4 (Figure 3 simulates `IIS_n[Σ*]` in `ARW_n[Σ]`)
With two simulators, a legal `Σ` history and a fair failure-free schedule, Figure 3 with
`PROP_{◇P}` makes `q₁` weakly correct while the simulated quorums contain `q₁` forever, even at the
strongly correct `q₀`; so the simulated detector is not in `Σ*` (`Fig3.sigma_simulation_false`).

**Impact.** The claim that one predicate covers `P, Σ, S, ◇S, S_x, ◇S_x` fails for `Σ` (the same run
appears to break `S` and `◇S` too; not formalized); Theorem 4 ("for the failure detector classes studied in this paper", here
`t = n − 1`) is false for `Σ`. The `Ω_k` and `◇P` simulations (Theorems 2, 3, Corollary 1) are not
affected.

**Details.** `p₀` always executes its whole round before `p₁` starts. Then `p₀` never sees `p₁`, so
`SC = {q₀}` and `q₁` is weakly correct. The paper allows this: Section 4.4 itself notes that with `Σ`
not every correct simulator yields a strongly correct process. In the rounds `p₀` owns, its quorum is
`{p₀}`, so it does not wait. In the other rounds (line 4, no wait) its quorum is `{p₀, p₁}`. That is a
legal `Σ` history: every quorum contains `p₀`. `p₁`'s quorum is always `{p₀, p₁}` and, as owner, it
waits for `p₀`, which has already written. `C*.read()` returns `FD_VAL[i]`, the last value read, so
the simulated `Σ*` output of `q₀` is `{q₀, q₁}` in every odd round. `Σ*` requires quorums to
eventually contain only strongly correct processes. The proof in Section 4.4 ("can be easily
translated") only covers the values read in owned rounds, where the owner waited for its quorum.

**Repair.** Not formalized. Returning only values used in owned rounds would fix the outputs of
strongly correct processes, but the literal `Σ*` also constrains weakly correct processes, whose
quorums (here `{q₀, q₁}` at `q₁`) need not be strongly correct.

## Proof gaps (statements true)

### 🛠️ Lemma 3 / Claim C1 (agreement of the consensus algorithm of Figure 5)
The induction for Claim C1 ("all `val_ld_seen = true` tuples of a round carry the same estimate")
ignores that line 13 may adopt the leader's *own* estimate (first disjunct of line 12) rather than a
voted one, and both may be visible at once.

**Impact.** Statement true; repaired (`Exec.agreement`, `theorem5`), for every resolution of the
choices at lines 12 and 15 and for arbitrary leader outputs.

**Details.** The leader's estimate can change after it was voted for: line 15 lets it adopt a value
when its view is mixed, and it may have followed another leader meanwhile. The proof needs to know that
the leader named by the voted tuples writes the voted value. The final step of Lemma 3 ("in both cases
they adopt `v`") has the same gap.

**Repair.** A stronger invariant `Inv`: (C1) the `true`, undecided tuples of a round share estimate and
leader `ℓ`, and (L) `p_ℓ`'s own tuple (if undecided) carries the same estimate (`Exec.inv`). It is
preserved by a case analysis on containment and immediacy (`Exec.inv_succ`): a process seeing `p_ℓ`
in a view where all processes name `ℓ` as leader forces `p_ℓ`'s own view to be of that kind too.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *IIS* (`Model.lean`): an infinite schedule of one-shot immediate snapshot rounds (views satisfy
  self-inclusion, containment, immediacy), crash failures (non-increasing participation), any number of
  crashes, asynchrony (all view patterns allowed). Strongly correct processes `SC = ⋃ SC_k` literally as in
  Section 2.6 (with "`i` writes" added to `SC₀`, which only matters if nobody is correct).
- *Figure 5* (`Consensus.lean`): the failure-detector output read at line 4 is arbitrary; `Ω*` (some
  strongly correct `ℓ` is eventually output to everybody) is assumed only for termination. The "`∃ v`"
  choices at lines 12 and 15 are nondeterministic (`Upd` allows every witness).
- *Figure 3* (`Fig3.lean`, `Fig3Live.lean`): ARW simulators with atomic `collect` and
  `arw_write_snapshot` steps (a sequential run of these objects is a legal run), any fair schedule
  (correct = infinitely many steps, crash = no more steps), failure-detector histories `H i t` arbitrary
  up to the class properties (`Ω_k`: eventually the same set containing a correct process; `◇P`:
  eventually exactly the correct ones). The simulated IIS schedule is read off the run (`simSchedule`).
  Positive results are thus for runs whose base objects behave atomically.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (validity) | `Exec.validity` | `Consensus.lean` |
| Claim C1 (strengthened) | `Exec.inv` | `Consensus.lean` |
| Lemma 3 (agreement) | `Exec.agreement` | `Consensus.lean` |
| Lemma 2 (termination; every correct process decides) | `Exec.termination`, `Exec.termination_correct` | `Termination.lean` |
| Theorem 5 | `theorem5` | `Termination.lean` |
| Theorem 2 (b) (`Ω_k`: liveness, correct ↔ correct) | `Fig3.theorem2_live`, `Fig3.theorem2_correct_iff` | `Fig3Live.lean` |
| Theorem 2 (c) (`Ω*_k` holds) | `Fig3.theorem2_omegaStar` | `Fig3Live.lean` |
| Theorem 3 (`◇P`: liveness, all correct are strongly correct, `◇P*` holds) | `Fig3.theorem3_live`, `Fig3.theorem3_SC`, `Fig3.theorem3_diamondPStar` | `Fig3Live.lean` |
| Section 4.4 / Theorem 4 for `Σ` (false) | `Fig3.sigma_simulation_false` | `Fig3.lean` |
| Section 2.6 (`SC₀ ≠ ∅`, `SC ⊆ C`, chain increasing) | `Schedule.SCk_zero_nonempty`, `Schedule.correct_of_mem_SC`, `Schedule.SCk_mono` | `Model.lean` |
| Section 3.2 (SC eventually sees only SC) | `Schedule.eventually_view_SC` | `Model.lean` |
| Theorems 2(c), 3, 4(b), schedule-level cores | `Schedule.thm2c_core`, `Schedule.thm3_core`, `Schedule.thm4b_core` | `SimulationCores.lean` |

**Proof remarks.** Agreement and validity hold for arbitrary failure-detector outputs. Termination is
proved for every correct process, not only the strongly correct ones: a decision of a strongly correct
process reaches all correct processes (`Exec.all_decide_of_SC`).

**Not formalized.** Theorem 1 (Borowsky–Gafni simulation of `ARW_n[C]` in `IIS_n[C*]`, Figure 2),
Corollary 1 and all task-solvability statements, the remaining classes of Section 4.4, Theorem 4 for
`t < n − 1`. Corollary 1 also silently needs that undecided weakly correct processes (or the simulators of
weakly correct processes) adopt a decision of another process. This is fine for colorless tasks but not
argued (see [differencies.md](differencies.md)).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: the hypotheses of Theorems 2 and 3 hold in a run where a simulator crashes
(`Fig3.nonvacuous_crash`); every schedule and leader sequence has an execution of Figure 5
(`Exec.ofSchedule`), and in the failure-free synchronous schedule with a constant leader `Ω*` holds and
everybody decides (`theorem5_full`, `NonVacuity.lean`). Paper-local model; CSLib candidate: `Model.lean`
(IIS executions with crashes and strongly correct processes).
