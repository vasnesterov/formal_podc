# Reconfigurable Atomic Transaction Commit — PODC 2019

Manuel Bravo, Alexey Gotsman. *Reconfigurable Atomic Transaction Commit.* PODC 2019. DOI
[10.1145/3293611.3331590](https://doi.org/10.1145/3293611.3331590). Formalized version: arXiv
[1906.01365](https://arxiv.org/abs/1906.01365) v1 (extended version with Appendices A–C);
numbering follows it.

**Verdict: 🔧 Easy fix.** Theorem 4.1 (safety of the message-passing protocol) is false as stated:
conditions (3)–(5) do not force `fₛ({ε}, l) = commit`, and without it two independent shards
commit transactions that the global `f` forbids. Adding this one condition repairs it. With it,
the whole safety proof is formalized: Invariants 1–12 in inductive form, Lemma A.1 (TCS-LL),
Lemma A.3 and Theorem 4.1. Line 56 of Figure 1 must be read as a match on `new_epoch` (the
paper's own convention); read as a binder, the protocol is unsafe.

## Mistakes in the paper

### 🔧 Condition (3), §2 — missing `fₛ({ε}, l) = commit` (Theorem 4.1, Lemma A.3)
Conditions (1), (3)–(5) allow `fₛ({ε}, l) = abort`. Then a committed transaction that does not touch
shard `s` forbids, through (3), every later transaction on `s`. The protocol never compares the
two, so it commits both (`theorem_4_1_false_eps`, `lemma_A_3_false`).

**Impact.** Theorem 4.1 and Lemma A.3 are false as stated, for every protocol that does not
coordinate independent shards. The paper's serializability example satisfies the missing condition.
Chockler–Gotsman (DISC 2018), whose proof Lemma A.3 adapts, avoid the issue: their condition (6)
projects transactions on shards rather than payloads.

**Details.** Two shards, `t₁` on shard `false`, `t₂` on shard `true`, payloads `some s` (non-empty on shard
`s`) and `ε = none`. `fₛ(L, l) = commit` iff every `x ∈ L` is non-`ε` or `l = ε`;
`gₛ(L, l) = commit` iff every `x ∈ L` is non-`ε` and `l ≠ ε`; `f` is defined from `fₛ` by (3).
All of (1), (3), (4), (5) and `fₛ(L, ε) = commit` hold (`LemmaA3Counterexample.matching`). The
protocol commits `t₁` and then `t₂` in a failure-free run (`Eps.acts`). But
`f({l₁}, l₂) = f_{true}({ε}, l₂|true) = abort`, so the history is not correct.

**Repair.** Assume `EpsNeutral` (`fₛ({ε}, l) = commit`): `lemma_A_3`, `theorem_4_1`.

### 🔧 Invariant 8 (Figure 5) — `new_epoch ≥ epoch[s₀]` is false
A fresh process that joins a configuration receives `NEW_STATE` without any `PROBE`, and lines
61–66 do not update `new_epoch`, so it follows epoch 1 with `new_epoch = 0`
(`Inv8.invariant_8_false`, with the line-56 check).

**Impact.** No proof cites Invariant 8; the safety proof goes through without it
(`theorem_4_1`), using `new_epoch ≤ epoch[s₀]` at leaders and followers (`Inv.loc_newEpoch`).

### ✏️ Slips
- Figure 1, lines 56–58: the handler head `NEW_CONFIG(new_epoch, M)` puts the state variable
  `new_epoch` in the message pattern, and line 58 uses an unbound `e`. By the paper's convention
  (lines 45, 51; App. C cites "the checks in lines 141 and 148", which are such patterns) this is
  the check `e = new_epoch` that the proof of Invariant 3 cites as "the check in line 56". Read as
  a binder `NEW_CONFIG(e, M)` with no check, the protocol is unsafe: a delayed `NEW_CONFIG(1)`
  drags the leader of epoch 2 back to epoch 1, and two conflicting transactions commit in a FIFO,
  crash-free run of 32 steps (`theorem_4_1_false_printed`, `Line56.epoch_decreases`). We model
  the check as `e ≥ new_epoch` (`Params.fixNewConfig = true`), which allows more executions
  than `e = new_epoch`, so `theorem_4_1` covers the paper's protocol (`Line56.fixed_blocks`).
- Figure 1, line 24 writes the accepted entry at slot `next`; a follower never maintains `next`,
  and every proof uses slot `k`. We model `[k]`.
- Degenerate configurations. With a single member (`f = 0`), the wait of line 26 ("an `ACCEPT_ACK`
  from every follower") is vacuous for any `kₛ, dₛ`: a coordinator commits two conflicting
  transactions without preparing them (`Single.single_member_unsafe`). A transaction with
  `shards(t) = ∅` can likewise be decided without being certified. We assume configurations with at
  least one follower (`f ≥ 1`) and transactions with at least one shard.

## Proof gaps (statements true)

### 🔧 Lemma A.1, constraint (11) — the witness `Pₛ[t]`
The proof sets `Pₛ[t] = P \ {t' | posₛ[t'] undefined}`, but a `t'` in the prepared set `P` of the
vote may later be accepted at a *higher* slot, or with an `abort` vote. This happens when `t'` was
lost in a reconfiguration and re-prepared by the next leader, and then (11) fails for that witness.

**Impact.** Statement true. Filtering `Pₛ[t]` by (11) works, since `gₛ` is monotone; repaired
(`Inv.tcsll`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing. Each ordered pair of processes has a channel, and any message of a
  channel may be delivered when its handler's precondition holds. FIFO channels are the special case
  "deliver the head" (`Action.IsFIFO`): the safety proof covers all deliveries, the counterexamples
  only use FIFO ones. Messages are delivered at most once.
* Crash-stop failures need no modelling for safety (a crashed process takes no more steps). Failure
  suspicion is arbitrary: any process may call `reconfigure` or `retry` at any time.
* Shards with disjoint replica groups (`home`), epoch-indexed configurations at a reliable CS
  (`compare_and_swap` succeeds iff the last epoch is `recon_epoch − 1`). `CONFIG_CHANGE` is modelled
  as adopting any stored configuration of another shard with a higher epoch.
* `compute_membership`: the new leader plus processes that replied to this probing or are fresh
  (never members of a stored configuration of the shard), at least two members.
* Line 56 checks `e ≥ new_epoch` (`Params.fixNewConfig = true`), a relaxation of the paper's
  match `e = new_epoch`; `fixNewConfig = false` is the unchecked binder reading.
* Clients are not processes: `certify` is a step of the coordinator, and `decide(t, d)` is
  recorded at the first `DECISION(t, d)` sent to the client.
* The TCS specification (§2) is formalized literally, with linearizations of `h | committed(h)`
  given by the order of the committed transactions. TCS-LL is Figure 6 without (12).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4.1 (with `EpsNeutral`; line 56 checked) | `theorem_4_1` | `Main.lean` |
| Theorem 4.1 false if line 56 has no check | `theorem_4_1_false_printed` | `Counterexample.lean` |
| Theorem 4.1 false without `fₛ({ε}, l) = commit` | `theorem_4_1_false_eps` | `Counterexample.lean` |
| Lemma A.1 (without (12)) | `lemma_A_1`, `Inv.tcsll` | `Main.lean`, `Safety.lean` |
| Lemma A.3 | `lemma_A_3`; `lemma_A_3_false` | `LemmaA3.lean` |
| Invariant 2 (core: the new leader holds all acceptable entries) | `Inv.safe`, `Inv.inv2`, `Inv.accL_persist` | `Safe.lean`, `Inv.lean`, `Consequences.lean` |
| Invariant 5 | `Inv.inv5` | `Safe.lean` |
| Invariants 4, 11 | `Inv.decided_unique`, `Inv.accL_unique_slot`, `Inv.accL_unique_txn` | `Consequences.lean` |
| Invariant 8 false | `Inv8.invariant_8_false` | `Counterexample.lean` |
| The inductive invariant | `Inv`, `inv_init`, `Inv.step`, `inv_reachable` | `Inv.lean`, `Init.lean`, `Main.lean` |

**Not formalized.** Constraint (12) of TCS-LL, which Lemma A.3 does not need. The liveness Theorems
4.2–4.4 and the RDMA protocol (§5, App. C, Theorem C.1) are not covered.

**CSLib candidates.** The TCS specification (`Spec.lean`) and Lemma A.3 (`LemmaA3.lean`).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Counterexample executions are computed by `decide` on the executable step function.
`NonVacuity.theorem_4_1_nonvacuous` shows that the hypotheses of `theorem_4_1` hold for the
serializability instance and that the protocol commits transactions. The model and the
invariant are paper-local (no CSLib models apply).
