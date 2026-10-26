# When Is Recoverable Consensus Harder Than Consensus? — PODC 2022

Carole Delporte-Gallet, Panagiota Fatourou, Hugues Fauconnier, Eric Ruppert. *When Is Recoverable Consensus
Harder Than Consensus?* PODC 2022. DOI [10.1145/3519270.3538418](https://doi.org/10.1145/3519270.3538418).
Formalized version: arXiv [2205.14213](https://arxiv.org/abs/2205.14213) v1 (with appendices).

**Verdict: 🛠️ Proof repaired.** All results of Section 3 hold and are formalized with the paper's proofs:
`n`-recording suffices for recoverable consensus (Theorem 8, with the algorithm of Figure 2 and the tournament
of Proposition 30), `(n-1)`-recording is necessary (Theorem 14), Theorem 16, Propositions 18, 19, 21, Corollaries
17, 20 and Theorem 22. Corollary 20 rests on an unproved claim (`cons(T_n) ≤ n`), which we prove; two
"commute or overwrite" steps in the proofs of Propositions 19 and 21 are false as stated but easily repaired.

## Mistakes in the paper

1. **Corollary 20: `cons(T_n) = n` is not proved (proof gap; statement true).** The paper derives
   `rcons(T_n) < cons(T_n) = n` "from Proposition 19 combined with Theorems 3 and 14". Proposition 19 gives
   `cons(T_n) ≥ n` (Theorem 3) and `rcons(T_n) ≤ n - 1` (Theorem 14), but `cons(T_n) ≤ n` needs that `T_n` is not
   `(n+1)`-discerning, which is nowhere shown. It is true: with `n + 1` processes one of the teams using `op_A`
   or `op_B` exceeds its counter (`⌊n/2⌋ + 1` resp. `⌈n/2⌉ + 1` processes), so a schedule of that team returns
   the object to `(⊥,0,0)`, after which a process of the other team cannot tell who went first; values other
   than `(⊥,0,0)` and read operations are excluded as in the paper (`TT.not_isDiscerning`, `corollary20`).
2. **Proposition 19, proof (false claim; statement true).** "If `q₀ ≠ (⊥,0,0)` then any pair of operations
   either commute or overwrite." From `q₀ = (w, ⌈n/2⌉−1, ⌊n/2⌋−1)` both `op_A` and `op_B` reset the object to
   `(⊥,0,0)`, and then neither commute (`op_A op_B` ends in `(B,0,0)`, `op_B op_A` in `(A,0,0)`) nor overwrite
   each other. The conclusion survives because the two single operations reach the same value, which already
   violates condition 1 of `2`-recording (`TT.pair_of_ne_bot`, `TT.not_isRecording`).
3. **Proposition 21, proof (gap; statement true).** The argument that `q₀` must be `(B,0)` uses only "operations
   of opposite teams cannot commute or overwrite". From `q₀ = (w, n−1)` the operations `op_A` and `op_B` neither
   commute nor overwrite each other but both lead to `(B,0)`; this is excluded by a third process `k` (the
   schedules `op_A op_k` and `op_B op_k` give `k` the same response and value) (`SS.pair_disc`,
   `SS.not_isDiscerning`). (A `Read` assigned to a process is excluded by the paper's overwrite argument: any
   operation overwrites `Read`.)
4. **Theorems 8 and 14: small gaps in otherwise correct proofs.** Lemma 13, Case 3, claims without justification
   that an earlier run of the single process of `B` finds `R_A = ⊥` at line 19 (true because `R_A` is never reset
   and that process later finds `⊥`). Lemma 11 uses "no update by the same process twice after `s''`" to show
   that `O` never returns to `q₀`, and conversely — a simultaneous induction. Lemma 7 needs the schedule to be
   nonempty. In Theorem 14, condition 3 in Case 2 is shown without using `|A| > 1`: no cycle starts on team `B`
   at all (we formalize this slightly stronger statement). Our proof of Theorem 8 replaces the execution-based
   Lemmas 9–13 by an invariant with ghost state (`InvV`), checked for every step and crash.
**Remark (not an error).** Theorem 22 and the "`rcons(T)` is `n` or `n + 1`" bound are not tight: by Ovens'
Theorem 13 (PODC'24, formalized in [`RecoverableConsensus`](../../PODC2024/RecoverableConsensus)) recoverable
consensus among `n` needs an `n`-recording type, so for readable types `rcons(T)` is exactly the largest `n` with
`T` `n`-recording and `rcons(𝒯) = max rcons(T)` (`theorem14_of_ovens`, `theorem22_ovens`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (CSLib `Cslib/Computability/Distributed/SharedMemory/Recoverable.lean`, as in the Ovens'24 folder).
- Asynchronous shared memory, `n` deterministic processes `Fin n`, **individual crashes and recoveries**: a crash
  resets the local state to the initial state with the same input, shared memory is non-volatile. Executions
  are arbitrary event sequences (any interleaving of steps and crashes).
- **Binary** recoverable consensus (`RecConsensus`): agreement among all outputs (also of different
  incarnations), validity, recoverable wait-freedom (a process taking infinitely many steps and eventually not
  crashing outputs in its last run). Wait-free consensus (`WFConsensus`) is the crash-free special case.
- Objects: deterministic sequential types; "with registers" = any read/write-like objects (`withRW`);
  unboundedly many objects (indexed by the nodes of the tournament tree). Readable = some read-only operation
  with injective responses (`ObjSpec.Readable`). `IsRecording`, `IsDiscerning`, `RecSolvable`, `WFSolvable`,
  `(Rec)ConsensusNumber` are those of the Ovens'24 folder.
- Theorem 14 uses Ovens' valency sets `E*_1` with the crashing process `c` = the largest identifier instead of
  the paper's `E_A` (only `c` crashes, at most as often as the others step); the proof only needs that one crash
  of `c` after any step of another process is admissible. This is internal to the proof: the statement of
  Theorem 14 quantifies over algorithms solving recoverable consensus on all executions, as in the paper.
- Binary consensus makes the necessity results (Theorems 14, 22, Ruppert's necessity, the upper bounds of
  Corollary 20 and Proposition 21) stronger than the paper's; the sufficiency results (Theorem 8 and its uses)
  are proved for binary consensus only (the algorithms carry values only through registers).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Observation 5, Observation 6, Lemma 7 | `isDiscerning_of_isRecording`, `IsRecording.pred`, `lemma7` | `Recording.lean` |
| Figure 2, Lemmas 9–13 (recoverable team consensus) | `fig2`, `fig2_safe`, `fig2_ranked` | `Fig2*.lean` |
| Proposition 30 (tournament) | `tournament`, `comp_safe` | `Podc/…/Recoverable/Composition.lean` |
| **Theorem 8** | `theorem8` | `Theorem8.lean` |
| Lemma 15, **Theorem 14** | `lemma15`, `theorem14_alg`, `theorem14` | `Theorem14.lean` |
| Theorem 14 strengthened (via Ovens'24) | `theorem14_of_ovens` | `Theorem14.lean` |
| Theorem 3 (Ruppert, cited) | `theorem3`, `isDiscerning_of_wfSolvable`, `theorem3_suff` | `RuppertNec.lean`, `RuppertSuff.lean` |
| Theorem 16, Proposition 18 | `theorem16`, `prop18`, `prop18_full` | `Recording.lean`, `Corollaries.lean` |
| Corollary 17 | `corollary17`, `corollary17_bounds` | `Corollaries.lean` |
| Proposition 19, Corollary 20 | `prop19`, `TT.isDiscerning`, `TT.not_isRecording`, `TT.not_isDiscerning`, `corollary20` | `TypeT.lean`, `Corollaries.lean` |
| Proposition 21 | `SS.isRecording`, `SS.not_isDiscerning`, `prop21` | `TypeS.lean`, `Corollaries.lean` |
| Theorem 22 | `theorem22`, `theorem22_ovens`, `recSolvableSet_of_recSolvable` | `Corollaries.lean` |
| Ovens'24 Theorem 14 without hypothesis | `ovens_theorem14` | `Corollaries.lean` |

**Not formalized.** Theorem 1 and Appendix A (simultaneous crashes), Section 4 (universal construction,
Theorem 23, Corollary 24), Appendix H (`rcons(stack) = 1`), multi-valued consensus.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `prop21` instantiates Theorem 8 with the concrete type `S_n` (and Theorem 14 / Ruppert's theorem
with algorithms that exist), `corollary20` uses the concrete `T_n`. Shared infrastructure staged for CSLib:
`Podc/Computability/Distributed/SharedMemory/Recoverable/{Safety,Composition}.lean` (safety from ghost
invariants, sequential composition of consensus with team consensus, the tournament).
