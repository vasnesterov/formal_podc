# Internet Computer Consensus — PODC 2022

Jan Camenisch, Manu Drijvers, Timo Hanke, Yvonne-Anne Pignolet, Victor Shoup, Dominic Williams. *Internet Computer
Consensus.* PODC 2022. DOI [10.1145/3519270.3538430](https://doi.org/10.1145/3519270.3538430). Formalized version:
the PODC paper (Protocol ICC0, Figures 1–2, and the three lemmas of Section 4). The PODC version has no proofs; they
are deferred to the full version (IACR ePrint 2021/632), which we did not use. All proofs here are our own.

**Verdict: ⚠️ Minor statement issues.** Safety (Property P2) and Deadlock freeness (P1) of ICC0 hold as stated for
`t < n/3`, and so does the consistency of the honest outputs. Liveness under partial synchrony (P3) holds in the
intended sense: the honest leader's block is committed by every honest party. Read literally, its conclusion
("`B_Q` is in every honest pool as a *finalized* block") can fail because of Figure 2's `kmax` skipping. This is a
wording issue, and a borderline call (see below).

## Mistakes in the paper

* **Liveness lemma, conclusion too literal (wording; borderline).** The lemma promises that, once all round-`k`
  messages are delivered, every honest party has `Q`'s block `B_Q` "in its pool as a finalized block". By Section
  3.4 this means that a combined finalization is in the pool. But Figure 2 combines round-`k` finalization shares
  only if `k > kmax`. After the two synchronous instants of hypothesis (iv) the network is asynchronous. The
  adversary can deliver the round-`(k+1)` finalization shares before the round-`k` ones to every honest party.
  Then every honest party finalizes the round-`(k+1)` block first, jumps to `kmax = k + 1`, and outputs `B_Q`
  without ever forming a finalization of it. Nobody honest broadcasts one, so the literal conclusion fails. This
  counterexample is argued in words, not in Lean. What does hold, and what the paper means (P3 and its
  discussion), is that every honest party holds `n − t` finalization shares of `B_Q`, has `kmax ≥ k`, and has
  committed `B_Q`: the chain ending at `B_Q` is a prefix of its output. (`liveness`)
* **Typo.** Section 3.5 describes clause (c) with "at least `Δntry(t)` time units"; it should be `Δntry(r)`, as in
  Figure 1.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous interleaving transition system for ICC0 (`Model.lean`). Parties run Figure 1 and Figure 2
  concurrently, one clause per step, with arbitrary choice among enabled clauses.
* Byzantine faults: a static corrupt set `F` with `#F ≤ t` and `3t < n`. Corrupt parties are represented by
  everything the adversary can inject into honest pools.
* Cryptography is idealized:
  - collision resistance: a block contains its parent;
  - authenticators and shares cannot be forged;
  - a notarization or finalization exists iff `n − t` parties signed, corrupt parties signing anything (the ideal
    `(t, n−t, n)` threshold signature, CSLib `Byzantine.Certified`);
  - the unique random beacon gives a fixed rank function `rank k`, assumed injective for each round.
* Network: insecure broadcast. The adversary delivers any available message to any honest party at any time;
  self-delivery is immediate. No randomness is involved: the leader's honesty is a hypothesis.
* Time is discrete, with one global clock read by all parties. Safety is proved for all interleavings and clock
  behaviours. For liveness, runs follow the paper's "wait for" semantics: time advances only when no honest party
  has an enabled clause (`UStep`), and δ-synchrony at a time `T₀` is a property of the run (`SyncAt`).
* Stronger or weaker than the paper: ranks only injective (more general); `k ≥ 1` instead of `k > 1`; `δ ≥ 1`;
  arbitrary payloads. The deadlock lemma's "will have finished" is read as "in a state where no honest party in a
  round `≤ k` has an enabled Tree Building clause".

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma (Safety) / Property P2 | `safety` (signature level: `safety_cert`) | `Safety.lean` |
| Section 3.3: outputs are consistent (atomic broadcast safety) | `output_prefix` | `Safety.lean` |
| Lemma (Deadlock freeness) / Property P1 | `deadlock_freeness` | `Deadlock.lean` |
| Lemma (Liveness assuming partial synchrony) / Property P3, intended reading | `liveness` | `Liveness.lean` |
| Global invariant of reachable states | `inv_of_reachable` (`Inv`) | `Safety.lean`, `Invariants.lean` |

Key lemmas:
* `Inv.final_notar_eq`: a finalization and a notarization of the same round share an honest signer.
* `Inv.valid_of_auth`: every echoed block is valid once the honest messages are delivered.
* `Inv.D_corrupt`: disqualified ranks belong to corrupt parties.
* `Stuck.false`: the core of deadlock freeness.
* `Inv.advance`, `LiveHyp.entered_of_ge`: catching up to round `k` before `T + δ`.
* `LiveHyp.proposal`, `LiveHyp.share_eq_leader`, `LiveHyp.fshare_leader`.

**Not formalized.** Protocols ICC1 and ICC2, the message-complexity and latency analysis, the probabilistic round
complexity (random leader), and Section 5 (measurements).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `NonVacuity.liveHyp_nonvacuous` builds an explicit infinite run (one honest party, `k = 2`, `T = 1`,
`δ = 1`) that satisfies all hypotheses of `liveness`, including the final-state conditions, and applies the
theorem to it. With one party this is a degenerate instance, so it only shows the hypotheses are consistent. The model
reuses CSLib's threshold certificates (`Cslib/Computability/Distributed/Byzantine/Certificate.lean`) and quorum
arithmetic. Everything else is paper-local.
