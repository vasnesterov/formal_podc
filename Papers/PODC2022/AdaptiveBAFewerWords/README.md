# Make Every Word Count: Adaptive BA with Fewer Words — PODC 2022

Shir Cohen, Idit Keidar, Alexander Spiegelman. *Brief Announcement: Make Every Word Count: Adaptive
Byzantine Agreement with Fewer Words.* PODC 2022. DOI
[10.1145/3519270.3538458](https://doi.org/10.1145/3519270.3538458). Formalized version: the full version, arXiv
[2202.09123v2](https://arxiv.org/abs/2202.09123v2) (January 2024, OPODIS 2022). Numbering follows it.

**Verdict: ❌ Intent lost.** The headline claim is the first Byzantine Broadcast with `O(n(f+1))` words for
`n = 2t + 1`. It rests on the adaptive weak BA of the full version (Section 6). The version cited by the BA
(v1) was withdrawn by the authors, and the corrected one (v2) violates **agreement**. Two independent attacks
break v2:

- an old commit certificate relayed by a Byzantine leader (two Byzantine processes; also when `f < (n−t−1)/2`);
- a decision obtained from a help answer that is never passed on to the fallback (one Byzantine process, `n = 3`).

What does hold:

- The BB-from-weak-BA reduction (Theorem 4), after a one-line fix of Algorithm 2.
- Its `O(n(f+1))` cost.
- The binary strong BA with `O(n)` words when `f = 0` (Theorem 7), modulo pseudocode slips.

**Which version is judged.** The label judges the claims of the PODC brief announcement (BA, 3 pages, June 2022).

- The BA claims "the first Byzantine Broadcast algorithm with `O(n(f+1))` word complexity" for `n = 2t + 1`
  (abstract, Section 3, Conclusions). It contains the definitions, the reduction BB → weak BA (Algorithms 1–2,
  identical to v2's, including line 23) and no proofs. The adaptive weak BA that the headline needs is "presented
  in the full version [7]" (arXiv 2202.09123), which at that time was **v1** (February 2022).
- v1's weak BA differs from v2's: it has no commit levels. A process commits to the first commit certificate it
  receives, but sends `decide` for every certificate a leader relays. It runs `t + 1` phases, and after the
  fallback it sets `decision ← ⊥` at processes that had already decided. Elsheimy et al. found an error in it,
  and the authors replaced it in **v2** (January 2024, "the weak BA algorithm has been corrected").
- We formalized v2, the authors' corrected version; the numbering follows it. The Lean counterexamples refute
  **v2**. For v1 we checked by hand (not in Lean) that both attacks below also apply; see the **v1** notes.
  So the headline of the BA rested on an algorithm the authors withdrew, and its replacement fails too.

## Mistakes in the paper

### ❌ Theorem 5 / Lemma 15 / Lemma 20 (Algorithms 3–4, agreement of weak BA)
Algorithm 3 violates agreement (`theorem5_false`). The run has `n = 5`, `t = 2`, Byzantine `p1` and `p2`, and the
fallback never runs:

- Byzantine `p1` (phase 1) forms `QC_commit(true)` at level 1 and keeps it.
- Byzantine `p2` (phase 2) collects votes for `false`, so it holds `QC_commit(false)` at level 2. It then relays
  the *old* level-1 certificate on `true`, finalizes `true`, and gives the finalize certificate to `p0` only.
- In phase 3 the correct leader `p3` receives the level-2 commit on `false` from `p1` and relays it as the highest
  level. Everybody accepts (`2 ≥ 1`), and `p3` and `p4` decide `false`.

**Impact.** The weak BA (Theorem 5) is refuted, so the paper's adaptive BB (Section 5 + Section 6) is not
established. The same attack works with `n = 11`, `t = 5` and only `f = 2 < (n−t−1)/2` Byzantine processes
(`theorem5_false_small_f`). This is the regime the paper calls adaptive. There the fallback can never repair
anything, because no correct process ever asks for help. The run works for `t + 1` or `n` phases and for both
readings of line 15 and of the leader guard.


**Details.** The proof of Lemma 15 says that the processes that send `decide` in phase `l` set
`commit_level = l`. Line 47, however, sets `commit_level` to the level of the certificate the leader relayed,
which can be older than certificates the adversary has formed in the meantime. Correct processes with
`commit = ⊥` vote in every phase. So a Byzantine leader can harvest a commit certificate of a higher level on
another value and withhold it. `lemma15_false` shows that two correct processes update `decision` in
`invokePhase` to different values, and that finalize certificates on both values can be formed.

Line 33 says "for the first time". We read it per phase, as the proof of Lemma 16 requires. If it means "vote
at most once in the whole run", this attack disappears, but then Lemma 16 and Lemma 6 fail: a Byzantine leader
spends everybody's only vote, and nobody ever decides in the phases
(`lemma16_lemma6_false_voteOnce`, `f = 1`). The attack of the next item breaks agreement under both readings.

**Repair.** We know no local fix. Setting `commit_level` to the current phase on acceptance blocks this attack,
but it makes correct processes hold commits of different levels. Then a correct leader's relay is rejected by
some of them, so Lemma 16 fails. A sound adaptive protocol for this setting is the subject of later work
(Elsheimy et al., SODA 2024); we did not formalize one.

**v1 (the version the BA cites; by hand, not in Lean).** v1 has no commit levels, and its line 43 sends
`decide` for every commit certificate the leader relays. So the attack is even simpler. Take `n = 7`, `t = 3`,
Byzantine `p1`, `p2`, `p4`, so `q = 6`; the `t + 1 = 4` phases are led by `p1`–`p4`.

1. `p1` and `p2` harvest `QC_commit(true)` and `QC_commit(false)` from the votes of phases 1 and 2.
2. `p2` relays `QC_commit(true)`, finalizes it with all `decide` messages, and gives it to `p0` only.
3. The correct leader `p3` of phase 3 gets only the 4 correct `decide` messages, fewer than 6.
4. `p4` relays `QC_commit(false)` in phase 4. All correct processes send `decide` again (v1 line 43 is
   unconditional), and `p4` finalizes `false` for `p3`, `p5`, `p6`.

This breaks v1's Lemma A.2, the counterpart of Lemma 15.

### ❌ Lemma 19 (Algorithm 3, hand-off of decisions to the fallback)
A decision taken at line 14, on a help answer, is never sent to the other processes with its proof. So the
fallback can contradict it (`lemma19_false`: `n = 3`, `t = 1`, one Byzantine process).

**Impact.** This is a second, independent agreement violation of Theorem 5. It holds for every reading of
lines 1, 15 and 33. The fix is probably local, but we did not prove a repaired Algorithm 3, since the previous
item refutes it anyway.


**Details.** The run proceeds as follows:

1. The Byzantine leader of phase 1 obtains `QC_finalized(true)` and keeps it.
2. Afterwards no quorum forms without it, and both correct processes ask for help.
3. Each correct process receives `t + 1` help requests, broadcasts its fallback certificate with
   `decision = undecided` (line 11), and so never echoes (line 21).
4. The Byzantine process answers only `p2`, with `⟨help, true, QC_finalized(true)⟩`, and `p2` decides `true`.
5. `p0` never sees `true` with a proof. It runs the fallback on its input `false` (or on `undecided`), while
   `p2` runs it on `true`.
6. Strong unanimity allows the output `false`, for example interactive consistency plus majority with the
   Byzantine input `false`, and `p0` decides `false`.

The proof claims that "in the 2δ window … they receive `v` from `p`". The code broadcasts the fallback message
before line 14, and a process that echoes later sends `bu_proof = ⊥`.

**Repair (not formalized).** After deciding at line 14, broadcast `⟨fallback, QC, v, decide_proof⟩` again.

**v1 (by hand).** Lines 5–24 of v1's Algorithm 3 are identical, and v1's Lemma A.6 has the same proof, so the
same run breaks v1. The phases play out the same way: commits only to the first certificate, which is the
same here, and `t + 1 = 2` phases. In v1, `p2` even ends with `⊥`, because v1's lines 25–28 set
`decision ← ⊥` at every process that had decided before the fallback.

### 🔧 Lemmas 9 and 11 (Algorithm 2, line 23)
A correct leader relays only a value signed by the sender. A correct process holding an idk certificate answers
with that certificate, which is neither sender-signed nor `idk`. So a correct leader may relay nothing, and
correct processes enter the weak BA with `⊥` (`lemma9_false`, `lemma11_false`: `n = 3`, `t = 1`, Byzantine
sender).

**Impact.** As printed, the precondition of the weak BA (valid inputs) fails, so the proof of Theorem 4 breaks.
The key fact of Section 5.1, that later correct-led phases are silent, also fails (`keyFact_false`, `n = 5`,
`f = 1`). A one-line fix saves everything.


**Repair.** Line 23 becomes "if received `⟨v′, j⟩` with `BB_valid(v′)`". With this rule we proved:

- Lemmas 9–12 (`lemma9`, `lemma10`, `lemma11`, `lemma12_values`, `lemma12_avail`);
- Theorem 4/13 for any black-box weak BA (`theorem13`);
- the `O(n(f+1))` bound `n(f + 4)` for round 1 and the phases (`BB.words_le`).

### 🔧 Lemma 16 (last clause)
"This decision is a proposal of a correct process" is false: a correct leader relays the highest commit it
receives, and that commit may be on a value proposed only by a Byzantine leader.

**Impact.** Nothing uses this clause. The rest of Lemma 16 is proved (`lemma16`, per-phase reading of line 33).

### ✏️ Slips
- Algorithm 3 line 1 runs `t + 1` phases, but the text, Lemma 6 and Section 6.1 say `n`. With `t + 1` phases
  Lemma 6 fails: `n = 7`, `f = 1`, and the fallback runs (`lemma6_false_printed_phases`). With `n` phases the
  same adversary is harmless (`lemma6_n_phases_ok`), and Lemma 6 is proved (`lemma6`). In v1, `t + 1`
  phases was the design (text and proof of v1's Lemma 6.2 say so), so the run of `lemma6_false_printed_phases` (one commit certificate, so v1 behaves the same) refutes
  v1's Lemma 6.2: there, the guaranteed correct leader may already have decided and stay silent.
- Algorithm 3 line 15 sets `bu_decision ← decision`, so undecided processes enter the fallback with
  `undecided`. Unique validity then fails with a single valid value (`lemma22_false`). The proof of Lemma 22
  assumes the inputs; with that reading the run is fine (`lemma22_intended_ok`).
- Algorithm 5 initializes `bu_decision = ⊥` and sets it to `decision` unconditionally (line 19). The proof of
  Lemma 28 uses the inputs. We formalize the inputs.
- Algorithm 5 line 26 echoes `bu_proof`, which is `⊥` for a decided process, so others cannot adopt its value.
  Agreement fails (`printed_noProof_disagreement`). The text says decided processes attach their proof.
- `while fallback_start > now` (Algorithm 5 line 20; Algorithm 3 line 16) drops a message arriving exactly at
  `fallback_start`. With all delays exactly `δ` this breaks agreement (`strictWindow_disagreement`). We process
  the closed window.
- The leader's rounds 3 and 5 of Algorithm 4 and round 3 of Algorithm 2 are not guarded by "the leader proposed
  / asked for help". A Byzantine process can then make every "silent" phase cost `Θ(n)` words
  (`unguarded_silent_phases_cost`: 132 words against the bound 49). The text says silent phases send nothing,
  and we formalize the guarded reading.
- `BB_valid(v)`, "signed by the sender or by `t + 1` processes", must mean "sender-signed or an idk
  certificate". Read literally, the weak BA's own certificates would be valid values.
- Definition 3 (weak BA) leaves implicit two assumptions that the reduction uses: correct inputs are valid, and
  decided values exist in the run.

### Typos
- Algorithm 3 line 2 does not pass `decide_proof` to `invokePhase` and overwrites it with later phases' results.
- Algorithm 3 line 11 sends an undefined `proof` (read as `decide_proof`). Algorithm 1's header has `vsenedr`.
- The proof of Lemma 27 speaks of a "certificate" that Algorithm 5 does not have. Lemma 25 has no proof
  ("similar to Lemma 17"); we proved it (`lemma25`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**

- **Processes and adversary.** Processes are `Fin n`, with `n = 2t + 1`; the reduction is proved for
  `n ≥ 2t + 1`. A static Byzantine set `F` has `|F| ≤ t`. All three algorithms are deterministic, so an adaptive
  adversary is simulated by corrupting the final faulty set from the start.
- **Rounds.** Synchronous lock-step rounds, with messages received in the round they are sent. Algorithm 5's
  fallback hand-off uses real discrete time instead: delays in `[0, δ]`, and first-hearing times computed by
  reachability.
- **Signatures.** Ideal (threshold) signatures are symbolic. Unforgeability is a validity condition on the
  adversary (`AdvValid`): a certificate can be used only if enough shares are available, either Byzantine or
  sent by correct processes. The adversary is rushing and eavesdropping. The counterexamples only use shares sent
  to Byzantine processes.
- **States.** Correct states are computed from the adversary's messages.
- **Black boxes.**
  - The weak BA in the reduction is specified by Agreement, Termination and Unique validity, plus "decided
    values exist" (`WeakBASpec`).
  - `A_fallback` is a strong BA: if all correct processes run it, their common output satisfies strong
    unanimity w.r.t. their inputs (`Admissible`, `FallbackSpec`).
- **Lemma 18 (re-synchronisation).** We prove its timing content (`lemma18`, `lemma18_processed`,
  `lemma18_alg5`). That the skewed run is "a correct run of `A`" is part of the black-box assumption. Two facts
  matter here: round windows overlap, so messages need round tags (`windows_overlap`); and a Byzantine process can
  see an early starter's round-`r+1` messages before its round-`r` message reaches a late starter
  (`skew_lookahead`). This adversary is stronger than a rushing lock-step adversary, and the paper does not
  argue that Momose–Ren tolerates it.
- **Word counts.** One word per message; messages to oneself are included.

**Main results in Lean** (namespace `Podc.AdaptiveBAFewerWords`).

| Paper | Lean | File |
|---|---|---|
| Theorem 5/24, Lemma 20 false (commit levels) | `WeakBA.Counterexample.theorem5_false`, `theorem5_false_small_f` | `WeakBACounterexample.lean` |
| Lemma 15 false | `WeakBA.Counterexample.lemma15_false` | `WeakBACounterexample.lean` |
| Lemma 19, Lemma 20 false (hand-off) | `WeakBA.Fallback.lemma19_false` | `WeakBAFallback.lean` |
| Lemma 22 false (printed line 15) | `WeakBA.Fallback.lemma22_false` | `WeakBAFallback.lean` |
| Lemma 16 | `WeakBA.lemma16` | `WeakBAAdaptive.lean` |
| Lemma 6 (`n` phases) | `WeakBA.lemma6` | `WeakBAAdaptive.lean` |
| Section 6.1 (`5n + 2nf` + `nf` words) | `WeakBA.words_le` | `WeakBAAdaptive.lean` |
| Lemma 6 false with `t + 1` phases | `WeakBA.PhaseCount.lemma6_false_printed_phases` | `WeakBAPhaseCount.lean` |
| Lemmas 16, 6 false ("vote once" reading) | `WeakBA.PhaseCount.lemma16_lemma6_false_voteOnce` | `WeakBAPhaseCount.lean` |
| Unguarded silent phases | `WeakBA.PhaseCount.unguarded_silent_phases_cost` | `WeakBAPhaseCount.lean` |
| Lemmas 9, 11 false (printed line 23) | `BB.Counterexample.lemma9_false`, `lemma11_false`, `keyFact_false` | `BBCounterexample.lean` |
| Lemmas 9–12 (fixed relay) | `BB.lemma9`, `BB.lemma10`, `BB.lemma11`, `BB.lemma12_values`, `BB.lemma12_avail` | `BBCorrect.lean` |
| Theorem 4/13 | `BB.theorem13` | `BBCorrect.lean` |
| Section 5.1 | `BB.silent_after`, `BB.nonSilent_unique`, `BB.words_le` | `BBComplexity.lean` |
| Lemmas 25–29, Theorem 7/30 | `StrongBA.lemma25` … `StrongBA.lemma29`, `StrongBA.theorem7` | `StrongBA.lean` |
| Lemma 8, Section 7.1 | `StrongBA.lemma8`, `StrongBA.words_le` | `StrongBA.lean` |
| Lemma 18 | `StrongBA.lemma18`, `lemma18_processed`, `lemma18_alg5`, `skew_lookahead` | `Resync.lean` |
| Slips of Algorithm 5 | `StrongBA.printed_noProof_disagreement`, `strictWindow_disagreement` | `StrongBAExamples.lean` |

**Not formalized.**

- Lemma 14 (decisions taken in the phases are valid). It is true, but irrelevant once agreement fails.
- A repaired weak BA.
- The `O(n²)` cost of the fallback itself.
- Momose–Ren's algorithm.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Counterexamples are checked by `decide +kernel` on executable models. Non-vacuity checks:

- `BB.Example.scG_decides`: the hypotheses of `theorem13` are satisfiable.
- `StrongBA.failureFree_decides`, `StrongBA.fallback_exists`.
- `lemma22_intended_ok`, `fixed_ok`, `intended_adopts`: the repaired readings behave correctly on the
  counterexample runs.
