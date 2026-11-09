# Differences between the formalization and the paper

Paper: M. Bravo, A. Gotsman, *Reconfigurable Atomic Transaction Commit*, PODC 2019
(arXiv:1906.01365v1, extended version). Scope: §2 (TCS specification), §3 (Figure 1), §4 Theorem 4.1
and its proof in App. A (Invariants 1–12, Lemma A.1, Proposition A.2, Lemma A.3).

## Errors in the paper

1. ✏️ **Figure 1, lines 56–58: the check of `NEW_CONFIG` is only implicit.** The handler head is
   `NEW_CONFIG(new_epoch, M)` with the state variable `new_epoch` in the pattern, and line 58 uses
   an unbound `e`. The paper's convention is that such patterns are matches (lines 45, 51; App. C
   cites "the checks in lines 141 and 148", whose heads `NEW_CONFIG(new_epoch)`,
   `NEW_STATE(new_epoch, …)` carry no other precondition), so line 56 checks `e = new_epoch`: this
   is "the check in line 56" of the proof of Invariant 3. Read as a binder `NEW_CONFIG(e, M)` with
   no check, Theorem 4.1 is false: a delayed `NEW_CONFIG(1)` moves a process that already leads
   epoch 2 back to epoch 1, and two conflicting transactions commit in a FIFO, crash-free run of
   32 steps (`theorem_4_1_false_printed`, `Line56.acts`, `Line56.epoch_decreases`). We formalize
   the check as `e ≥ new_epoch` (`Params.fixNewConfig = true`); this admits every execution of
   the `e = new_epoch` protocol (the handlers are otherwise identical), so `theorem_4_1` covers the
   paper's protocol. The late message of the counterexample is rejected (`Line56.fixed_blocks`).
   Not a separate Lean statement: the inclusion of the `=` protocol's steps is immediate.
2. 🔧 **Conditions (1), (3)–(5) do not imply `fₛ({ε}, l) = commit`, and Theorem 4.1 / Lemma A.3
   need it.** (3) quantifies over all shards and projects payloads, so a committed transaction that
   does not touch `s` contributes `ε` to `L | s`. Counterexample with all stated conditions:
   `lemma_A_3_false` (spec level) and `theorem_4_1_false_eps` (a failure-free run of the
   protocol). Chockler–Gotsman (DISC 2018, condition (6)) project *transactions* on shards and do not
   have this problem. Our hypothesis: `EpsNeutral` (`fₛ({ε}, l) = commit`).
3. ✏️ **Figure 1, line 24** writes `(txn, payload, vote, phase)[next]`; must be `[k]` (followers do
   not maintain `next`; the proofs use slot `k`). Modelled as `[k]`.
4. 🔧 **Invariant 8** (`new_epoch ≥ epoch[s₀]`) is false: a fresh member gets `NEW_STATE(e)` with
   `new_epoch = 0` (`Inv8.invariant_8_false`, protocol with the line-56 check). Not needed; we use
   `new_epoch ≤ epoch[s₀]` for leaders/followers (`Inv.loc_newEpoch`).
5. ✏️ **Degenerate cases.** (a) A configuration with a single member (`f = 0`): the wait at line 26
   is vacuous for arbitrary `kₛ, dₛ`, and the coordinator commits unprepared conflicting
   transactions (`Single.single_member_unsafe`). The definition of `posₛ` in Lemma A.1 ("all
   followers ... received ACCEPT") is vacuous in the same case. (b) A transaction with
   `shards(t) = ∅` can be decided without being certified. We assume at least two members per
   configuration (`ValidInit`, and in `compute_membership`) and `shards(t) ≠ ∅`.

## Proof gaps (statements true)

6. 🔧 **Lemma A.1, (10)–(11).** The witness `Pₛ[t] = P \ {posₛ undefined}` violates (11) when a
   transaction of `P` (prepared with vote commit when `t`'s vote was computed) was later lost in a
   reconfiguration and re-prepared at a higher slot or with an `abort` vote. We filter `Pₛ[t]` by
   (11) and use monotonicity of `gₛ` (`Inv.tcsll`; witness `PsW` in `Safety.lean`).
7. **Lemma A.3** is only referred to "the proof of Theorem 1 in [5] with minimal adjustments". We
   prove it from scratch (`lemma_A_3`): order committed transactions topologically along
   `≺rt ∪ ≺dec` (acyclic by (13)), and check legality shard by shard with (4), (5), (7)–(10). It
   needs neither well-formedness of the history nor constraint (12), but it needs `EpsNeutral` (item 2).
8. **Invariant 2.** The paper only sketches the `NEW_CONFIG` transition. As a state invariant it must
   also survive acknowledgements and appends at an older epoch after a newer one was configured. We
   state it for every configured epoch `E` and its *candidate* state (base state if started,
   otherwise the frozen state of the chosen leader) and for slots that may still be accepted
   (`AliveK`). It needs extra invariants: `frz` (once `E` exists, some member of `E − 1` moved past
   it), `m_frozen` (a chosen leader is frozen until `NEW_CONFIG`), `cfg_mem` (the probing record of
   each configuration, from which Invariant 5 follows by induction: `Inv.inv5`). The core argument
   (`Inv.safe`) is the paper's case analysis on the new leader's epoch.
9. **Proposition A.2** is replaced by the ghost record `vinfo` of the vote context at line 12
   (slots of `L₁`, `L₂` and the history length) and the origin tag of each log entry (`elog`), from
   which (9), (10), (13) follow (`Inv.vote_ctx`, `Inv.edge` in `Safety.lean`).

## Modelling choices

- **Network.** Channels are lists per ordered pair; any message may be delivered (`deliver src dst
  i`), FIFO is the special case `i = 0`. Messages are delivered at most once, and a handler whose
  precondition fails leaves its message in the channel. The safety theorem quantifies over all
  executions, so it covers FIFO and non-FIFO channels.
- **Crashes** are not modelled (irrelevant for safety). Suspicions are arbitrary: `reconfigure`,
  `retry` may be called at any time by any process.
- **CS.** A reliable shared list of configurations per shard; `get_last`, `get`, `compare_and_swap`
  as in §3 (the new epoch is `recon_epoch = last + 1`). `CONFIG_CHANGE` notifications are modelled
  by an over-approximating step `configChange` (adopt any stored configuration of another shard with
  a higher epoch).
- **Buffered acknowledgements.** `ACCEPT_ACK` and `PROBE_ACK` messages are buffered at the receiver;
  the handlers at lines 26, 45, 51 fire on buffer contents (line 51 requires no buffered
  `PROBE_ACK(true)` for the current probing; line 45 does not check membership, as in the paper).
- **`compute_membership`** returns any `M` containing the new leader, with `|M| ≥ 2`, whose members
  belong to the shard and either have a buffered `PROBE_ACK` for this probing or are fresh (members
  of no stored configuration of the shard).
- **Arrays.** `txn`, `payload`, `vote` are always written together and are stored as one array of
  triples `ent`; arrays carry a length `len` so that `max{k | phase[k] ≠ start}` (line 59) is
  computable. Slots start at 1 (`next` starts at 0; the paper uses `next ∈ ℤ`).
- **Sends to "leader[s] for s ∈ shards(t)"** (lines 3, 29, 73) are realized as: each process `b`
  with `home b ∈ shards(t)` that the sender considers the leader (resp. a member) of its own shard
  receives the message for that shard. This is equivalent because replica groups are disjoint.
- **Clients** are not processes: `certify` is a step of the coordinator; `decide(t, d)` is
  appended to the history at the first `DECISION(t, d)` sent to `client(t)` (later ones carry the
  same `d`, `Inv.decided_unique`).
- **Specification.** Payload sets are `Finset`s. A legal linearization of `h | committed(h)` is
  given by the order of committed transactions (`IsLegalLinearization`), equivalent to the paper's
  sequential history. TCS-LL omits constraint (12) (not needed for Lemma A.3; not proved for the
  protocol). The positions/votes/payloads of TCS-LL are defined from accepted entries (all
  followers of an epoch acknowledged an entry of that epoch's leader log).
- **Ghost variables** (`hist`, `sent`, `started`, `elog` with origin tags, `base`, `vinfo`) are part
  of the state but never influence transitions.
- **Not formalized:** constraint (12), liveness (Theorems 4.2–4.4, App. B), the RDMA protocol (§5,
  App. C, Theorem C.1).
