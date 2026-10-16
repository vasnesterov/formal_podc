# Silence — PODC 2018

Guy Goren, Yoram Moses. *Silence.* PODC 2018. DOI
[10.1145/3212734.3212768](https://doi.org/10.1145/3212734.3212768). Formalized version: arXiv
[1805.07954](https://arxiv.org/abs/1805.07954) v1 (the only version, with Appendices A–D); numbering
follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Correct with fixes.** The Silent Choir Theorem, the lower bounds of Theorem 3 and the
three matching AC protocols (STEALTH, D2, D1f1) hold, and so do the Appendix D bounds. The fixes:
Lemma 2 and Corollary 2 are false when the receiver has itself crashed; Theorem 3 lacks the bound for
`D = 1`, which "completely characterize" needs; the protocol proofs treat the consensus sub-protocol as
a black box, which does not work. Under readings that the text allows, STEALTH and D2 are wrong; with
the intended reading and a concrete consensus they are correct. Appendix D's 1-bit encoding of `huh?`
does not say how it is decoded: one natural decoding breaks Agreement, and another works.

## Mistakes in the paper

* **STEALTH can fail under readings the text allows.** §4.2 has process 0 check only "`n − 1`
  first-round messages", ignoring its own vote. Then with `v₀ = 0` and no failures, everyone commits.
  Separately, suppose a choir member that sent `err` but received none still commits. With `n = 3`,
  `f = 1`, `v₂ = 0`, and process 0 crashing in round 3, process 1 commits. Both runs violate Commit
  Validity. Fig. 3 (D2) has the same self-message ambiguity. The intended reading is "sent or
  received", as the D2 prose says, and we verify that reading. These are inconsistent or
  under-specified descriptions, not wrong protocols.
  (`Stealth.literal0_not_solvesAC`, `Stealth.literalErr_not_solvesAC`)
* **The consensus is used as a black box, which does not work.** STEALTH, D2 and 1.5D call
  `B.1.Consensus(f − 1)`, which tolerates only `f − 1` crashes. The Commit Validity proofs (Lemmas 5,
  9, 17) need its Validity in runs where `f` crashes can happen during the consensus, e.g. when
  `v_j = 0` and nothing failed earlier. The Agreement proofs (Lemmas 8, 11, 18) never check the `f − 1`
  bound. With a concrete max-floodset everything works. Its validity holds for any number of crashes.
  When the inputs are mixed, a crash happened before the consensus, so its `f` rounds contain a round
  with no crash. Proof gap; the statements are true. (`Stealth.solvesAC`, `D2.solvesAC`)
* **The D2 agreement proof has a gap (Lemma 11).** The process `c_j` that received `j`'s vote need not
  "send `j`'s id to all": if it committed, it is silent in round 3. Agreement then follows from the
  biased-to-1 property instead. Proof gap; the statement is true. (`D2.solvesAC`)
* **The 1-bit encoding of `huh?` in 1.5D does not say how it is decoded** (Appendix D; the appendices
  appear only in the arXiv version). The paper sends `huh?` as "quiet to `{i+1..i+f}`, `1` to the rest",
  but never says how a receiver reads it.
  * **Decoding "a `1` from a non-predecessor means `huh?`" (silence from a predecessor ignored).**
    Agreement fails. Counterexample: `n = 5`, `f = 2`, all values `1`. Process 4 crashes in round 1
    reaching only processes 1 and 2; process 3 crashes silently in round 2. Processes 1 and 2 commit at
    time `1½` and halt, while process 0 runs the consensus alone and aborts.
  * **Decoding that also reads "no `all[1]` from a predecessor" as `huh?`.** The 1-bit protocol is
    correct.

  Under-specified encoding. (`MidRound.OneBit.oneBit_not_solvesACMid`;
  `MidRound.OneBitFixed.solvesACMid`; with `huh?` as a separate message:
  `MidRound.OnePointFive.solvesACMid`)
* **Lemma 2 and Corollary 2 fail when the receiver `i` has crashed by time `m`.** A crashed `i`
  "receives nothing", but its state is `⊥` and it knows nothing. Counterexample: `n = 3`, `f = 1`,
  `S = {1, 2}`, `φ = (v₁ = 1 ∨ v₂ = 1)`. Process 0 crashes in round 1, and every value is `1`. False
  only in this degenerate case. We prove both results for an `i` that is alive at time `m`; Lemma 1 is
  unaffected. (`corollary2_literal_false`; repaired: `lemma2`, `corollary2`, `lemma1`)
* **The claim to "completely characterize" the tradeoff is incomplete for `D = 1`.** §4.2 says the three
  protocols make the bounds of Theorem 3 tight. But for `f = 1` and `D = 1`, Theorem 3 gives only
  `M ≥ n`, while D1f1 uses `n² − n`. We close the gap with the missing bound: if all processes decide by
  time 1, then `M ≥ n(n − 1)`. It follows from the Silent Choir Theorem. Incomplete claim.
  (`theorem3_D1`)
* **Theorem 2's proof has a gap.** A process `h ∈ S_j^r(m−1)` may already have crashed in `r` before it
  is reached. Messages to crashed processes count in chains, so this can happen. The paper's `r′`
  makes `h` crash later, and then `h` behaves differently in `r′`. Fix: keep `h`'s earlier crash.
  Proof gap; the statement is true. (`silent_choir`)
* Typos: Theorem 2's proof says "`k_y < ℓ − 1`" where it needs `k_y ≤ ℓ − 1`. Theorem 3(c)'s proof says
  "chain from `j`" where it means "from `i`". Fig. 1 sends `all[1]` to `{0, …, f}` instead of
  `{1, …, f}`. The D1f1 prose (§4.2) says "`all[1]` message in the second round" where it means the
  third round.

Full list of differences, including modelling choices: [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/SyncCrash/Model.lean`; CSLib candidate, built on CSLib's `LockStep`).
* Network and timing: a complete network, synchronous rounds; round `t + 1` runs from time `t` to time
  `t + 1`.
* Protocols are deterministic and history based: the local state is (initial value, received inboxes).
  The state becomes `⊥` after a crash.
* Crashes: a run is given by its inputs and its crash pattern. A process crashing in round `c ≥ 1`
  reaches an arbitrary subset `reach p` in round `c` and nothing afterwards. `γ_f` allows at most `f`
  crashes.
* Decisions are taken at the start of a round from the current state; crashed processes do not decide.
* Knowledge is semantic: `K_i φ` holds iff `φ` holds in every admissible run where `i` has the same
  state.
* Messages are counted with `Set.encard`, so runs with infinitely many messages are included.
* There are no self-messages; protocols read their own state instead, and counts agree with the
  paper's.
* AC (`Defs.lean`): Decision, uniform Agreement, Commit Validity and Abort Validity on every admissible
  run. The common case is the nice run, where all values are 1 and nobody fails.
* Appendix D (`MidRound.lean`): the same runs, with mid-round decisions. Such a decision is performed
  only if the process finished its sending phase.
* Consensus inside the protocols: max-floodset (`Podc/SyncCrash/Floodset.lean`).

**Main results in Lean** (namespace `Papers.PODC2018.Silence`).

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (KoP) | `Podc.SyncCrash.kop` | `Podc/SyncCrash/Model.lean` |
| Lemma 1, Lemma 2, Corollary 2 (with `i` alive) | `lemma1`, `lemma2`, `corollary2` | `SilentBroadcast.lean` |
| Lemma 2 / Cor. 2 literal: counterexample | `corollary2_literal_false` | `SilentBroadcast.lean` |
| Theorem 2 (Silent Choir) | `silent_choir` (stronger: `silent_choir_at`) | `SilentChoir.lean` |
| Corollary 1, Lemma 3, Lemma 4 | `corollary1`, `lemma3`, `lemma4` | `LowerBounds.lean` |
| Theorem 3(a)–(d) | `theorem3a`, `theorem3b`, `theorem3c`, `theorem3d` | `LowerBounds.lean` |
| Missing case `D = 1`: `M ≥ n(n−1)` | `theorem3_D1` | `LowerBounds.lean` |
| Corollary 3 | `corollary3` | `LowerBounds.lean` |
| STEALTH: Claim 1, Claim 2 (`D = 3`, `M = n+f−1`) | `Stealth.nice_commit`, `Stealth.nice_msgs`, `Stealth.solvesAC` | `Stealth.lean` |
| STEALTH literal readings: counterexamples | `Stealth.literal0_not_solvesAC`, `Stealth.literalErr_not_solvesAC` | `StealthLiteral.lean` |
| D2: Claims 3, 4 (`D = 2`, `M = fn`) | `D2.nice_commit`, `D2.nice_msgs`, `D2.solvesAC` | `D2.lean` |
| D1f1: Claims 5, 6 (`f = 1`, `D = 1`, `M = n²−n`) | `D1f1.nice_commit`, `D1f1.nice_msgs`, `D1f1.solvesAC` | `D1f1.lean` |
| Lemma 16, Corollaries 5, 6 | `MidRound.lemma16a`, `lemma16b`, `corollary5`, `corollary6` | `MidRound.lean` |
| 1.5D: Claims 7, 8; Cor. 6 tight | `MidRound.OnePointFive.solvesACMid`, `nice_msgs`, `corollary6_tight` | `MidRound15D.lean` |
| 1-bit encoding of 1.5D, silence ignored: counterexample | `MidRound.OneBit.oneBit_not_solvesACMid` | `MidRound1Bit.lean` |
| 1-bit encoding of 1.5D, silence read as `huh?`: correct | `MidRound.OneBitFixed.solvesACMid` | `MidRound1BitFixed.lean` |

**Not formalized.** The rules S1–S3 appear only as Lemmas 1, 2 and Corollary 2. The remark that the
γ_f protocols are also correct in `γ̃_f` is not proved. The GW and Dwork–Skeen protocols are not
formalized.

**Trust.** There is no `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`
and `Quot.sound`. The lower bounds' hypotheses can be satisfied: STEALTH and D2 solve AC in `γ_f` for
every `1 ≤ f < n`, and D1f1 does so for `f = 1`. Each protocol is verified in all admissible runs, not
just the nice run. The model reuses CSLib `Cslib.Byzantine.LockStep` (`Protocol`, `hist`). The new
shared code is in `Podc/SyncCrash/`; its CSLib candidates are the crash model with knowledge and
message chains, and the floodset lemmas.
