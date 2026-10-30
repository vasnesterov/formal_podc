# Differences between the formalization and the paper

Paper: Camenisch, Drijvers, Hanke, Pignolet, Shoup, Williams. *Internet Computer Consensus.* PODC 2022
(DOI 10.1145/3519270.3538430). We used the PODC version. It states Protocol ICC0 (Figures 1–2) and the three
lemmas of Section 4 but contains no proofs; those are in the full version (IACR ePrint 2021/632), which was not
available to us. All proofs here were reconstructed from the protocol description.

## Statement-level issues (decide the verdict)

1. **Liveness lemma: "each honest party will have `Q`'s round-`k` block in its pool as a finalized block" is
   false as written; the intended "committed" reading holds (R3, ⚠️; borderline with ✅).**
   "Finalized for `P`" is defined in Section 3.4 as "valid, and a finalization (combined `S_final` signature) is in
   `P`'s pool". Figure 2 only combines finalization shares of a round-`k` block when `k > kmax`. After the two
   synchronous instants of hypothesis (iv) the network is asynchronous, so the adversary may deliver the round-`k`
   finalization shares to each honest party only after the round-`(k+1)` ones. Then every honest party first
   executes clause (ii) for the round-`(k+1)` block, sets `kmax = k + 1` and outputs both blocks. It never combines
   the round-`k` shares, so no honest party ever broadcasts a finalization of `B_Q`, and corrupt parties need not
   either. When all round-`k` messages are delivered, every honest pool contains `n − t` finalization shares of
   `B_Q`, but no finalization. This is an informal counterexample: it satisfies all hypotheses (i)–(v), but it is
   not machine-checked; a concrete run needs 3 rounds and 4 parties.
   Its fix is local, and the paper itself shows the intent: Property P3 ("the block … will be finalized") and the
   discussion after it ("each honest party will output this command in round `k`"). We prove the
   intended version (`liveness`): every honest party has `B_Q` valid with a full set of `n − t` finalization shares
   in its pool (so it can form the finalization), has `kmax ≥ k`, and has committed `B_Q` (the chain ending at
   `B_Q` is a prefix of its output). Borderline: a reader who takes "finalized" loosely as "committed" would rate
   the lemma ✅.

No other statement problem was found. Lemma (Safety) and Lemma (Deadlock freeness) hold as stated, under the
reading of "will have finished" described below. Their proofs are ours, since the paper gives none.

## Model and idealization (not statement issues)

* **Cryptography is idealized.**
  - The hash is injective: a block contains its parent block itself (`Block.mk k α parent payload`).
  - Signatures are unforgeable. The adversary can make an honest party receive: any block; an authenticator of a
    corrupt proposer, or one already broadcast by an honest party; shares of corrupt parties, or shares already
    broadcast; a notarization/finalization of `B` iff at least `n − t` parties signed it, corrupt parties counting
    as having signed everything (`Avail`, `NotarCert`, `FinalCert`).
  - This is the ideal functionality of a `(t, n − t, n)` threshold scheme. The paper's game-based definition
    (the adversary corrupts exactly `t` parties; a valid signature needs `≥ h − t` honest shares) gives the same
    safety argument; see the comment on approach (ii) in Section 2.3.
* **Random beacon.** The beacon signature is unique, so the permutation of round `k` is a fixed function
  `rank k : P → ℕ`. We only assume it is injective for each `k`, which is more general than a permutation onto
  `{0,…,n−1}`. Unpredictability of the beacon is irrelevant for P1–P3: P3 conditions on an honest leader. The
  beacon itself is modelled by its shares: a party starts round `k` after receiving `t + 1` round-`k` shares, and
  immediately broadcasts its round-`(k+1)` share, as in Figure 1.
* **Corruption.** Static set `F`, `#F ≤ t`, `3t < n`. Corrupt parties take no explicit steps; their behaviour is
  everything the adversary can inject (above). This is the full Byzantine power under idealized cryptography.
* **Network.** Every honest broadcast goes to the global set `sent` and into the sender's own pool (immediate
  self-delivery). The adversary delivers any available message to any honest pool at any time, in any order. This
  is the paper's insecure broadcast with adversarial scheduling. Self-delivery is immediate, whereas the paper
  only says "the pool contains messages received from all parties, including itself". We need it so that a party
  that finishes a round by combining shares keeps the combined notarization ("there will always be such a block",
  Section 3.5).
* **Time.** Discrete global time (`ℕ`), the same clock for every party (the paper's `clock()`), delays
  `Δprop, Δntry : ℕ → ℕ`. The paper uses `ℝ≥0` and local clocks. Its liveness lemma implicitly assumes local
  clocks run at real-time rate, which a global clock makes explicit.
* **"Wait for" semantics.** In the paper a clause executes as soon as its condition holds, choosing arbitrarily
  among enabled clauses. We formalize it in two ways:
  - Safety holds for *all* interleavings (`Step`, time advances arbitrarily). This is stronger than needed.
  - For liveness, runs use `UStep`: time advances only when no honest party has an enabled clause.
  - In the deadlock lemma "will have finished" is read as "in a state where no honest party (in a round `≤ k`) has
    an enabled Tree Building clause" (`TBSettled`).
* **Payloads.** `getPayload` is an arbitrary choice: any payload may be proposed. Application-specific validity is
  omitted. Outputs are blocks rather than their payloads. The deadlock and liveness theorems assume `Nonempty V`:
  with an empty payload type no block can be proposed.
* **Initialization.** All parties start at time `0` in round `1`, waiting for the round-`1` beacon. Their
  round-`1` beacon shares are broadcast initially. This covers "all honest parties have been initiated at time
  `T`".

## Formulation of the three lemmas

* **Safety** (`safety`): for any reachable state, honest `p`, `q`, if `B` is finalized for `p` and `B'` (same round
  `≥ 1`) is notarized for `q`, then `B' = B`. Stronger form `safety_cert`: at the level of signatures (a
  finalization of `B` and a notarization of `B'` can both exist). "Can be notarized" in the paper ranges over
  the future too; since sets only grow along an execution, a single state covers it.
* **Output consistency** (`output_prefix`): the outputs of two honest parties are prefixes of one another. This is
  the argument after Property P2 in Section 3.3, which the paper presents informally; it is an addition.
* **Deadlock freeness** (`deadlock_freeness`), for a reachable state and round `k`:
  - hypotheses: every honest message of a round `≤ k` is in every honest pool; every honest party that has started
    a round `≤ k` has all proposal and notarization delays elapsed; no honest party in a round `≤ k` has an enabled
    Tree Building clause;
  - conclusion: every honest party is past round `k`. Leaving a round is only possible through clause (a), i.e.
    with a valid round-`k` block that is notarized or has `n − t` notarization shares, whose notarization the party
    then broadcasts; `Inv.finished` records that a notarization of some round-`k` block has been broadcast. The
    Lean conclusion itself is only "past round `k`".

  Message rounds are `Msg.round`: a beacon share of round `j` counts as a round-`j` message.
* **Liveness** (`liveness`). Differences from the paper:
  - `k ≥ 1` instead of `k > 1` (more general);
  - `δ ≥ 1` (in discrete time a zero delay bound makes hypothesis (iv) contradictory);
  - `Δntry` non-decreasing, as required in Section 3.5;
  - (ii) is formalized as "no honest party has entered round `k` before time `T`, and some has by time `T`";
  - δ-synchrony at `T₀` is "every message broadcast by an honest party at a state of time `≤ T₀` is in every
    honest pool at every state of time `≥ T₀ + δ`" (`SyncAt`);
  - "when all round-`k` messages from honest parties have been delivered" is formalized as a state `j` where
    every honest round-`k` message is in every honest pool, every honest party is settled, and time is
    `≥ T + 2δ + Δprop(0)` and `≥ T + δ + Δntry(0)`. The time bounds make sure every round-`k` message that will
    ever be sent has been sent (the notarization delay for the leader's block has elapsed); the paper leaves this
    implicit.
  - Conclusion: see item 1.

## Proof notes (no gaps in the paper to report, since it has no proofs)

* Safety: an honest party casts a finalization share for `B` only if it cast no notarization share for another
  block of that round, and it casts no shares for round `k` after leaving it (`Inv.fshare`). Two `n − t`
  certificates share an honest signer since `3t < n` (`Inv.final_notar_eq`).
* Deadlock freeness:
  - Take an honest party in the smallest round `j`. If someone finished round `j`, its notarization arrives, and
    so does the chain below it, because every notarized block was echoed by an honest notarizer (`Inv.share`,
    `Inv.valid_of_auth`).
  - Otherwise every honest party has proposed and has cast a share for the valid, non-disqualified block of
    minimal rank. A disqualified rank always has two echoed blocks (`Inv.D_spec`), hence belongs to a corrupt
    party (`Inv.D_corrupt`). So all honest parties pick the same minimal rank and block (`Stuck.rmin_le_rmin`),
    and its `n − |F| ≥ n − t` shares finish the round (`Stuck.false`).
  - The beacon wait is handled with `t + 1 ≤ n − t` honest shares.
* Liveness:
  - Catch-up: everything the first party in round `k` used was broadcast by time `T`, so all honest parties are in
    round `k` before `T + δ` (`Inv.advance`, `LiveHyp.entered_of_ge`). This needs `t + 1` honest beacon shares of
    each round `≤ k`, which the notarizers of round `k − 1` provide (`Inv.beacon_cert`).
  - The leader proposes before `T + δ + Δprop(0)` (`LiveHyp.proposal`); its block is valid everywhere from
    `T + 2δ + Δprop(0) ≤ T + Δntry(1)` on (`LiveHyp.valid_leader`). Hence no honest party ever casts a share for
    another round-`k` block (`LiveHyp.share_eq_leader`), and every honest party leaves round `k` with `N ⊆ {B_Q}`,
    casting a finalization share for `B_Q` (`LiveHyp.fshare_leader`).

## Typos

* Section 3.5, prose for clause (c): "(iii) at least `Δntry(t)` time units have passed" should be `Δntry(r)`
  (Figure 1 has `Δntry(r)`).
