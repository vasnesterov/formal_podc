# Byzantine Agreement with Homonyms — PODC 2011

Carole Delporte-Gallet, Hugues Fauconnier, Rachid Guerraoui, Anne-Marie Kermarrec, Eric Ruppert, Hung Tran-The.
*Byzantine Agreement with Homonyms.* PODC 2011. DOI
[10.1145/1993806.1993810](https://doi.org/10.1145/1993806.1993810). Formalized version: HAL
[hal-00580133v1](https://hal.science/hal-00580133v1) (PODC paper plus appendix with the detailed proofs); numbering
follows it.

**Verdict: 🛠️ Hard fix.** The whole characterization of Table 1 holds as stated, both directions in all six cells:
necessity (Props. 1, 4, 16, Thms. 19, 20) and sufficiency (Props. 2, 5, 18), including both partially synchronous
algorithms. The necessity proof of Theorem 19 rests on a non-WLOG assumption and needed a different argument, while
the other proof errors have local repairs. Lemma 34 is not established under the reading of the pseudocode that
Lemma 36 needs, but no result needs it.

## Mistakes in the paper

### ❌ Lemma 34 (Appendix A.3, "at most one lock pair at the end of each phase")
Lemma 34 is unestablished, not refuted: its proof assumes that the lock-removal test (lines 24–26 of Figure 7)
still sees the `n−t` witnesses of line 16, which fails under the per-superround witnesses that Lemma 36's proof
needs.

**Impact.** No other result depends on it. Prop. 39 cites it, but only needs that some lock `(v₁, ∗)` is held,
because line 6 then excludes every other value (`Restricted.decAt_agree`).

**Details.** The paper defines witnesses per superround, and line 25 does not say which superround's accepts it
uses. Lemma 36 needs the accepts of superround 4 of the current phase, which is the reading we formalize. Before T,
all echoes sent to `p` in that superround can be lost. A process locked on `(v′, ph′)` that locks `(v, ph)` in a
later phase then keeps both pairs: a hand-built run with `n = ℓ = 4`, `t = 1` works (not in Lean). The pseudocode is
ambiguous: under a cumulative reading of witnesses (all accepts so far), the paper's proof of Lemma 34 goes through.

### ✏️ Slips
- Proposition 26 (correctness of the broadcast with multiplicity, Appendix A.3.1): for α = 0 the statement asks every
  correct process to perform an `Accept(i, α′, m, r)` although nobody broadcast `m`, which Figure 6 never does.
  Degenerate case: Prop. 26 is only used with α ≥ 1, and the paper's own Lemma 24 separates the case α > 0. We prove
  the witness form (`Restricted.cc_le_witnesses`: the number of correct broadcasters is at most the number of
  witnesses after GST), which is trivially true for α = 0.
- Appendix A.4 (Thm. 19): "Assume that for ℓ < 3t" should be ℓ ≤ 3t; "a number of processes less than 3t" should be
  "at most 3t".
- Appendix A.4 (Thm. 19): "If ℓ ≥ t, the result is clear" should be ℓ ≤ t.
- Proof of Prop. 5 (termination): "(since n ≤ 2ℓ−3t)" needs the strict inequality, which the hypothesis gives.
- Proof of Prop. 5 (termination): acks are sent in "round 1 of superround 3", which should be superround 4. The
  overview of Section 4.2 has the same slip.

### Typos
- Proof of Lemma 33 cites "Lemma 22"; it means Lemma 32.

## Proof gaps (statements true)

### 🛠️ Theorem 19 (necessity, Appendix A.4)
The reduction to the classical `n ≤ 3t` bound assumes "w.l.o.g." that `q₀` (whose homonym group has `n−ℓ+1`
clones) is correct in the classical run, which is not without loss of generality.

**Impact.** Statement true; proved directly (`thm19_lower`).

**Details.** If `q₀` is Byzantine in the classical run, the paper's simulation would need all `n−ℓ+1` processes
with identifier 0 to be Byzantine. So the derived algorithm `A′` is only shown correct in runs where `q₀` is
correct. That weaker classical problem *is* solvable for any `ℓ` (everyone adopts `q₀`'s broadcast value), so no
contradiction with [9, 13] follows. A possible repair, not proved: per run, choose the identifier of the clone group
among the correct `qᵢ`. `A` must work for every identifier assignment, so this is allowed.

**Repair.** We reuse the covering system of Proposition 1 instead. The stacks of the hexagon are clones, so with
innumerate receivers a Byzantine process only needs to send one copy per identifier, and the scenarios become
restricted runs (`not_solves_three_t_innumerate`, `restricted_scenario_dedup`).

### 🔧 Lemma 12 (Prop. 5, Case 2) and Lemma 37 (Prop. 18, Case 2)
The case split "if there are t+1 correct processes with the same input value, that value will be in the proper
set of all correct processes" fails with homonyms (and should be on the current proper sets, not on inputs).

**Impact.** Statements true; repaired (`Psync.common_value`, `Restricted.common_proper`).

**Details.** In Prop. 5 the rule adds `v` when it is received from t+1 *different identifiers*. The t+1 correct
processes sharing an input may all have the same identifier. The right split is on the current proper sets: either
some value is in the proper sets of correct processes of t+1 distinct identifiers (in Prop. 18: of t+1 correct
messages), so it spreads to everyone after GST; or the ≥ 2t+1 Byzantine-free identifiers (correct messages)
witness the "add all values" rule at every correct process.

This second branch reads the rule "received proper sets from 2t+1 different identifiers and no value appears in
t+1 of them" **existentially**: *some* 2t+1 received sets with no value in t+1 of them. That is the literal
reading ("them" are the 2t+1 sets), and the paper's validity remark ("t+1 of the proper sets are from correct
processes") argues about such a subset, so we count it as the paper's rule, not as a change. Under the
universal reading (all received sets) a Byzantine process that sends each process its own input blocks both rules
forever. Example (Prop. 18 setting): n = 4, t = 1, correct inputs a, b, c; no common proper value ever appears and
no lock is ever requested. The existential reading keeps validity.

### 🔧 Lemma 36 and Prop. 40 (use of relay, Prop. 27)
Prop. 27 gives the relayed accepts only in superround max(r′, T)+1, but with per-superround witnesses Lemma 36 and
Prop. 40 need them in later superrounds as well.

**Impact.** Statements true: the proof of Prop. 27 gives relay in every later superround (`Restricted.thr_relay`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** (`Model.lean`)
- `n` processes (any finite type with `n` elements) share `ℓ` authenticated identifiers; the assignment is
  surjective and arbitrary (`Solves` quantifies over all of them). Algorithms are deterministic and identical
  within an identifier. A process sends one message per round to *all* processes with a given identifier
  (including itself) and receives the multiset of `(identifier, message)` pairs.
- Numerate algorithms see the multiset; innumerate algorithms (`Algorithm.Innumerate`) depend only on the set.
- Static Byzantine set, at most `t` processes, full information. Byzantine processes deliver arbitrary pairs tagged
  with their own identifiers. *Restricted* Byzantine processes deliver at most one pair per recipient and round
  (at most `#{Byzantine with identifier j}` pairs tagged `j`).
- Synchronous: lock-step rounds without loss (`gst = 0`). Partially synchronous: the basic model of Dwork, Lynch and
  Stockmeyer, in which messages between correct processes may be lost only before an unknown round `gst`. All
  processes start in round 0 and step every round.
- BA: termination, agreement (also for `p = q`, so decisions are stable) and validity (unanimous correct input).
  Lower bounds use two distinct values; algorithms work for any value type.
- The paper's standing assumptions `n > 3t`, `t > 0`, `ℓ ≥ 1` are explicit hypotheses where needed.

**Main results in Lean.** (namespace `Podc.HomonymsBA`)

| Paper | Lean | File |
|---|---|---|
| Prop. 1 (sync, ℓ ≤ 3t unsolvable, numerate) | `prop1` | `SyncLowerBound.lean` |
| "suffices to take ℓ = 3t" | `Solvable.mono_ids` | `Basic.lean` |
| Prop. 2 (sync, ℓ > 3t solvable, innumerate; transformation T(A)) | `prop2`, `TA_solves`, `Sim.st_simRun` | `SyncAlgorithm.lean` |
| Thm. 3 | `thm3` | `Main.lean` |
| Prop. 4 (psync, ℓ ≤ (n+3t)/2 unsolvable, numerate) | `prop4` | `PsyncLowerBound.lean` |
| Prop. 5 (psync, ℓ > (n+3t)/2 solvable, innumerate) | `Psync.prop5`, `Psync.alg_solves` | `PsyncLiveness.lean` |
| Prop. 6 (authenticated broadcast) | `Psync.unforgeable`, `Psync.bcast_correct`, `Psync.relay` | `PsyncBroadcast.lean` |
| Lemma 7 | `Psync.lemma7` | `PsyncBasic.lean` |
| Lemmas 8, 9, 10 | `Psync.vote_quorum`, `Psync.line22_agree`, `Psync.lemma10` | `PsyncSafety.lean` |
| Lemmas 11, 12 | `Psync.lemma11`, `Psync.common_value`, `Psync.leader_decides` | `PsyncLiveness.lean` |
| Thm. 13 | `thm13` | `Main.lean` |
| Thms. 14, 15 | `thm14`, `thm15` | `Main.lean` |
| Prop. 16 (ℓ ≤ t unsolvable, restricted, numerate) | `prop16` | `Valency.lean` |
| Lemmas 17, 21, 22 | `Valency.exists_common_dec`, `Valency.exists_multi_init`, `Valency.exists_multi_succ` | `Valency.lean` |
| Prop. 18 (psync, ℓ > t solvable, restricted, numerate) | `prop18`, `Restricted.alg_solves` | `RestrictedProp18.lean` |
| Lemmas 23, 30, 31; Props. 26 (witness form, α ≥ 1), 27, 28 | `Restricted.a_le`, `Restricted.lemma30`, `Restricted.lemma31`, `Restricted.cc_le_witnesses`, `Restricted.thr_relay`, `Restricted.thr_acc_le` | `RestrictedBroadcast.lean` |
| Lemmas 32, 33, 35; Props. 38, 39 | `Restricted.lemma32`, `Restricted.lemma33`, `Restricted.lemma35`, `Restricted.decAt_valid`, `Restricted.decAt_agree` | `RestrictedSafety.lean` |
| Lemmas 36, 37; Prop. 40 | `Restricted.lemma36`, `Restricted.common_propose`, `Restricted.decides_in_phase` | `RestrictedLiveness.lean` |
| Thm. 19 | `thm19`, `thm19_lower` | `Main.lean`, `SyncLowerBound.lean` |
| Thm. 20 | `thm20`, `thm20_lower` | `Main.lean`, `PsyncLowerBound.lean` |
| Intro: t = 1, ℓ = 4 solvable for n = 4, not for n = 5 | `intro_example_four`, `intro_example_five` | `Main.lean` |

**Remarks.**
- Prop. 1 and Thm. 19: one hexagon cover proves both, numerate/unrestricted and innumerate/restricted
  (`Cover.lean`: `scenario`, `st_scenario`). The case ℓ < 3t reduces to ℓ = 3t by merging identifiers. This needs
  n ≥ 3t, which the paper's standing assumption gives.
- Prop. 2: the classical black box is CSLib's synchronous model (`Cslib.Byzantine.PartialSync`, `gst = 0`, `δ = 0`).
  Classical BA for `ℓ > 3t` comes from CSLib's interactive consistency plus the containment condition
  (`ClassicalBA.lean`). `T(A)` latches the simulated decision and its own decision. `A` need not broadcast.
- Prop. 4 uses `t > 0`; the paper assumes it throughout. Prop. 5 does not need `n > 3t`.
- The algorithms of Props. 5 and 18 bundle each round's output in one record. Phases take 8 rounds. Echo tags and
  thresholds follow the paper, with harmless adaptations listed in [differencies.md](differencies.md).
- Several steps of the proofs of Props. 5 and 18 use slightly more than the cited lemma states, or rely on tight
  timing; all are handled in the Lean proofs (`Psync.alg_solves`, `Restricted.alg_solves`):
  - Lemma 10 is applied with A = the identifiers from which the leader received acks, some of which may be
    Byzantine. Its proof only needs that each identifier of A held by a single correct process acked
    (`Psync.lemma10` assumes exactly that).
  - Lemma 11 relies on relay arriving exactly in time for the lock release at the end of phase ph₃. The timing is
    tight (gst ≤ 8·ph₃ + 6) but works.
  - Prop. 18: Lemma 35 uses the `r ≤ r′` part of unforgeability, which Lemma 30 drops (`Restricted.lemma30` keeps
    it).
  - Prop. 18 termination: the leaders of the all-correct identifier may request different values. Correct processes
    must choose deterministically from the *set* of requested values, which relay makes common after GST.
  - Prop. 39 cites Lemma 34 ("at most one lock pair"), which is not needed (`Restricted.decAt_agree`; see the Lemma
    34 item above).

**Not formalized.** Lemma 34 (unestablished, not needed; see above). Under the cumulative reading of witnesses,
Lemma 30 and Lemma 36 should survive, but we did not formalize that variant. Proposition 25 (unicity) holds by construction and is
not stated separately. The equivalence of the basic partially synchronous model with the other DLS variants is
cited by the paper and not formalized.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The iff
theorems (`thm3`, `thm13`–`thm15`, `thm19`, `thm20`) show the model is not vacuous: each model has both solvable and
unsolvable instances. The classical model and black box come from CSLib (`Cslib.Byzantine.PartialSync`).
CSLib candidates (`-- CSLib candidate`): the homonym model `Model.lean`/`Basic.lean` and the cover lemma `Cover.lean`.
