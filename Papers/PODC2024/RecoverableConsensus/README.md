# Determining Recoverable Consensus Numbers

Sean Ovens (University of Waterloo). PODC 2024, pp. 3–13.
DOI [10.1145/3662158.3662775](https://doi.org/10.1145/3662158.3662775); full version arXiv
[2405.04775](https://arxiv.org/abs/2405.04775) (v1, used for the formalization). Local PDF:
`papers/2024/3662158.3662775_Determining_Recoverable_Consensus_Numbers.pdf`.

Main result (Theorem 13): if objects of deterministic types `T₀, T₁, …` (with registers) solve
recoverable wait-free consensus among `n ≥ 2` processes with individual crashes, then one of the
types is `n`-recording. With Delporte-Gallet–Fatourou–Fauconnier–Ruppert's sufficiency result
(PODC'22, Thm 8) this gives robustness of the recoverable consensus hierarchy of deterministic
readable types (Theorem 14). Section 4: for `n > n' ≥ 1` the type `T_{n,n'}` has consensus number
`n` and recoverable consensus number `n'`.

## Model (explicit choices)

Shared model `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean` (namespace `Cslib.SharedMemory.Recoverable`):

* **asynchronous shared memory**, `n` deterministic processes `Fin n` (identifier = position in
  `Fin n`, used by the crash budgets), arbitrary (possibly infinitely many) shared objects
  `T : ι → ObjSpec`, each with a deterministic sequential specification (CSLib `ObjSpec`); initial
  values chosen by the algorithm;
* a local state is either an **output state** (`Act.out v`; a step taken in it is a no-op) or
  poised to apply one operation to one object (`Act.access i o k`, continuing with `k response`);
  local computation is folded into the continuation;
* **individual crash-recovery**: the adversary schedules steps `Ev.step p` and crashes `Ev.crash p`;
  a crash **resets the local state of `p` (incl. program counter) to its initial state**, which is
  determined by its input; **shared objects keep their values** (non-volatile memory); after a crash
  the process recovers by running its algorithm again from the initial state;
* the system is deterministic: a finite execution is its event list (`run C α`);
* **binary consensus** (inputs/outputs in `Bool`; every process has an input from the start):
  agreement = all values output in an execution are equal (by all processes, also by one process in
  different incarnations), validity = every output is some process's input;
* **recoverable wait-freedom** (`RecConsensus`): in every infinite execution, a process that takes
  infinitely many steps and does not crash after time `N` is in an output state at some time `≥ N`
  (it outputs in its last incarnation); all crash patterns are allowed;
* **wait-free consensus** (crash-stop, for consensus numbers, `WFConsensus`): the same on
  crash-free executions (a crashed process of the crash-stop model is one that stops taking steps);
* no randomization; simultaneous crashes are not modelled (the paper only uses individual crashes);
* (recoverable) consensus numbers: `WFSolvable S n` / `RecSolvable S n` = solvable among `n`
  processes with objects of type `S` and read/write objects (`IsRW`: every operation is read-only or
  a blind write; registers are `IsRW`); `ConsensusNumber S n := WFSolvable S n ∧ ∀ m > n, ¬ …`.

Ovens' executions with bounded crashes: `InE z α` (`E_z`: every process `p` crashes at most `z n`
times the number of steps of processes with smaller identifiers; so `p₀` never crashes) and
`InEs z α` (`E*_z`: the same for every prefix). Valency (`UnivQ`, `Univ`, `Biv`, `Crit`, `Team`)
is defined w.r.t. `E*_z` from a base configuration, on executions (event lists), as in the paper.

## Results ↔ Lean

Namespace `Cslib.SharedMemory.Recoverable.Ovens` (paper folder) or `Cslib.SharedMemory.Recoverable`
(shared file `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`).

| Paper | Lean | File | Status |
|---|---|---|---|
| Def. `n`-discerning, `n`-recording (Sect. 2) | `IsDiscerning`, `IsRecording` (+ `apply`) | `Defs.lean` | definitions |
| Observation 1 | `biv_initial` | `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean` | proved |
| Observation 2 (⇒ direction, the one used) | `UnivQ.append`, `Univ.append` | same | proved |
| Observation 3 | `InEs.append`, `InE.append` | same | proved |
| Observation 4 | `InEs.append_crashFree` | same | proved |
| Observation 5 | `UnivQ.transfer` (needs: no process outside `P'` in an output state) | same | proved (hypothesis added) |
| Lemma 6 (a), (b) | `exists_crit`, `exists_stuck` (core: `no_chain`) | same | proved |
| Lemma 7 | `Crit.teams` | same | proved |
| Lemma 8 | `Crit.biv` | same | proved |
| Lemma 9 | `Crit.poised` | same | proved |
| Lemma 10 | `lemma10` | `Lemma12.lean` | proved |
| Def. `v`-hiding, `n`-recording configuration; Observation 11 | `Hiding`, `Recording`, `U`, `obs11`; recording configuration ⇒ recording type: `Recording.isRecording` | `Config.lean` | proved |
| Lemma 12 | `lemma12` (+ `after_crashes`) | `Lemma12.lean` | proved |
| **Theorem 13** | `theorem13` (invariant (a)–(f): `Stage`; steps `base_case`, `base_special`, `stage_step`, `final_of_stage`) | `Theorem13.lean` | **proved** |
| Theorem 14 (robustness) | `theorem14`, conditional on DFFR'22 Thm 8 (hypothesis `dffr`) | `Theorem13.lean` | proved modulo the cited theorem |
| Def. of `T_{n,n'}` (Sect. 4, Fig. 3) | `Tnn`, `tδ`, `TVal`, `TOp`, `TResp` | `Defs.lean` | definition |
| Lemma 15 (consensus number of `T_{n,n'}` is `n`) | `lemma15` (algorithm `Sec4.alg15_wfConsensus`; impossibility `Sec4.not_wfSolvable`, for all `m > n`) | `Sec4Lemma15.lean`, `Sec4Common.lean` | proved (one proof step repaired) |
| Lemma 16 (recoverable consensus number of `T_{n,n'}` is `n'`) | `lemma16` (algorithm `Sec4.alg16_recConsensus`; impossibility `Sec4.not_recSolvable`, for all `m > n'`, crash budget `z = n`) | `Sec4Lemma16.lean` | proved (proof repaired) |
| Golab (SPAA'20), cited in Sect. 1: test-and-set cannot solve recoverable 2-consensus | `tas_not_recSolvable` (derived from Theorem 13) | `Corollaries.lean` | proved |
| sanity: read/write objects | `IsRW.not_recording`, `rw_not_recSolvable` | `Corollaries.lean` | proved |
| remark on readability of `T_{n,n'}` | `not_readable_Tnn` (`n'+1<n`), `readable_Tnn_pred` (`n' = n-1`) | `Corollaries.lean` | proved |

All finished theorems use only `propext`, `Classical.choice`, `Quot.sound`.

### Not formalized

* DFFR'22 Theorem 8 (sufficiency of `n`-recording for readable types) — cited, used as a hypothesis
  of `theorem14`; Ruppert's characterization (`n`-discerning ⟺ consensus number `≥ n`) — cited,
  only the definition is given.
* The consequence for DFFR's type `X_n` (consensus number `n`, recoverable consensus number
  `n − 2`): it needs DFFR's definition of `X_n` and their proofs that `X_n` is `(n−2)`- but not
  `(n−1)`-recording.

## Status

**Complete.** All results of the paper that do not depend on cited external theorems are formalized
and proved, with no `sorry`/`axiom`: Observations 1–5, 11, Lemmas 6–10, 12, Theorem 13 (main
result), Lemmas 15–16; Theorem 14 is proved conditionally on the cited DFFR'22 Theorem 8. The
paper's main result is correct; the issues found (Section 3: missing reachability assumption, an
over-general Observation 5, typos; Section 4: a false claim in the proof of Lemma 15, a
non-symmetric "symmetric" case and off-by-one bookkeeping in Lemma 16) are listed in
`differencies.md`. Section 4 was formalized by a subagent (`Sec4*.lean`).

Non-vacuity: `lemma16` contains a concrete recoverable wait-free consensus algorithm
(`Sec4.alg16_recConsensus`), so the hypothesis `RecConsensus A` of Theorem 13 is satisfiable.

## Infrastructure built

* `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean` — crash-recovery shared-memory model, correctness notions,
  Ovens' bounded-crash execution sets, valency framework and the generic Lemmas 6–9 (CSLib
  candidate).
* `Defs.lean`, `Config.lean` — type-level conditions (`IsRecording`, `IsDiscerning`, `Readable`,
  `IsRW`), (recoverable) consensus numbers, configuration-level `U`-sets, hiding/recording
  configurations, crash blocks `λ_k`.

Moved to CSLib: `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean` (whole file). CSLib candidates: `IsRecording`/`IsDiscerning`/
`Readable`/`IsRW`, `WFSolvable`/`RecSolvable`/consensus numbers (`Defs.lean`) and
`not_recording_of_commute` (`Corollaries.lean`); generic helpers in `Sec4Common.lean`
(`prog_of_rank`, `absorb`/`contra_absorb`/`not_rw_obj`, `card_filter_change`).

## Sanity checks

A script (not kept in the repo) (Python, exhaustive over values/operations/teams): `T_{n,n'}` for `n ≤ 4` is
`k`-recording exactly for `2 ≤ k ≤ n − 1` when `n' ≥ 1, n ≥ 3` (none for `T_{2,1}`) and
`n`-discerning — consistent with Theorem 13 and Section 4 (e.g. `T_{3,1}` is 2-recording but has
recoverable consensus number 1: `n`-recording is not sufficient for non-readable types).
