# Differences between the formalization and the paper

Paper: Kuznetsov, Tonkikh, Zhang, *Revisiting Optimal Resilience of Fast Byzantine Consensus*, PODC 2021
(arXiv:2102.12825v3, extended version; numbering follows it).

Summary: **the main results are correct.** Theorem 4.5 (lower bound `3f + 2t − 1`, tight `5f − 1`) is proved
for every `2 ≤ n ≤ 3f + 2t − 2`; the protocol's consistency (Theorems 3.6 / A.4) is proved for `n ≥ 3f + 2t − 1`, and a
concrete implementation in the same model is proved to be an `f`-resilient `t`-two-step consensus protocol (so the
bound is tight within one formal model, `Impl.tight_bound`).
We found one genuine gap in the protocol's safety proof (votes from "future" views; fixed by an explicit check),
two imprecisions, and one degenerate case of Theorem 4.5 outside the intended scope; plus modelling choices below.
The positive side (liveness, two-step) is proved in the drift-free, synchronized-clock PSync model, where no view
synchronizer is needed — friendlier than the paper's protocol section; the lower bound uses the same model (as does
the paper's, Section 4.1).

## 1. Gaps / imprecisions in the paper

1. **Genuine proof gap (not a protocol bug): votes from "future" views (Sections 3.2–3.3).** A vote `(x, u, σ, τ)`
   is "valid" if its certificates check out; nothing requires `u < v` for a vote sent to the leader of view `v`.
   In an asynchronous period a Byzantine voter can include a correctly certified proposal of a view `u ≥ v`
   (other processes may already be in higher views), pushing `w` (highest view in a valid vote) to `w ≥ v`; the
   proof's induction on views then cannot apply the hypothesis "certified ⇒ safe" to `w`. The same holds for the
   commit certificate in a vote (Appendix A). Safety of the unmodified protocol is likely still provable (e.g. by
   induction on certificate creation time), so this is a gap in the proof, not a bug. **Fix used here:**
   verifiers only accept votes for view `v` whose proposal view and commit-certificate view are `< v`
   (`ValidBallot`, `ValidCC`); correct processes only send such votes, so it costs nothing for liveness. The
   safety proof uses both conditions.
2. **Imprecision: commit certificates in votes (Appendix A, Theorem A.4 case (3)).** "If some value `x` had been
   decided in view `w` through the slow path, there would be a commit certificate for `x` in view `w` in votes′"
   relies on (i) a correct process committing a certificate only for its *current* view — this follows from the
   paper's rule (Lemma 3.1) that correct processes only send messages associated with their current view, so it is
   only an imprecision; and (ii) "the latest commit certificate" in a vote meaning the highest-view one — "latest"
   in time vs. highest view is a minor ambiguity (they coincide under (i)). We make both explicit (`Step.commit`
   only for the current view, `Local.cc` overwritten on each commit, views increasing).
3. **Degenerate case outside the intended scope: Theorem 4.5 at `f = 1`, `t = 0`** (`3f + 2t − 2 = 1`). With a
   single process, "decide your own input immediately" is an `f`-resilient `t`-two-step consensus protocol for every
   `f, t` (`single_fastConsensus`, `theorem_4_5_fails_f1_t0`). This is outside the paper's intended scope (§4.1
   assumes `|Π| ≥ 3f + 1`; the protocol section assumes `t ≥ 1`). We state Theorem 4.5 with `3f + 2t − 2 ≥ 2` and
   prove it for all `2 ≤ n ≤ 3f + 2t − 2` (`no_fastConsensus_of_le`).
4. **Lemma 4.4's hypotheses (not an error).** It uses `n ≥ 2t + 2` (follows from `|Π| ≥ 3f + 1`, assumed in §4.1)
   and at least two input values (standard non-triviality); both are explicit in Lean.

## 2. Model (lower bound)

1. **Shared partially synchronous model** `Cslib.Byzantine.PartialSync`: discrete time, every correct process takes one
   step per tick from time 0 (perfectly synchronized clocks — the paper also assumes this in Section 4.1),
   deterministic state machines, batched message delivery (all messages from one sender sent at one tick to one
   receiver are delivered together), a delivery-time function chosen by the adversary, `gst`, and a delay bound
   `δ` after GST (the paper's known `Δ`; we assume `0 < δ`). Infinite runs; "finite prefix + continuation" is
   expressed by agreement of runs up to a time `T`. Lemma 4.2 (indistinguishability ⇒ same decision) is the
   model's `Run.st_eq_of_inbox_eq` + determinism of states.
2. **Signatures.** The lower bound is proved in the *authenticated* model with ideal unforgeable signatures
   (`Auth`, `Algorithm.Unforging`, `Run.AuthValid`), which is the setting of the paper's protocol; the
   unauthenticated version is the special case `Auth.none` (`theorem_4_5_noAuth`). The paper does not discuss
   unforgeability in the lower-bound executions; it holds after two truncations: in `ρ₄`, `P₄` replays its `ρ₅`
   messages to `P₃` only during round 2, and its `ρ₃` messages to the others only up to time `T` (later
   messages could carry signatures of correct processes that were never emitted). Same for `p`. Neither
   truncation matters for the argument.
3. **`T`-faulty two-step execution is unique.** In the paper an execution includes a total order of simultaneous
   events and "there is a `T`-faulty two-step execution" quantifies over such orders. In our model simultaneous
   deliveries are processed in one atomic step, so `tsRun A δ I T` is the unique `T`-faulty two-step execution
   and the existential becomes a property of it. Consequently our notion of `t`-two-step is a (slightly)
   stronger requirement for protocols that would rely on a particular intra-instant ordering; the paper's proof
   itself uses the freedom of ordering only to make orders coincide across executions, which is automatic here.
4. **Timing of "two steps".** Round `i` is `[(i−1)δ, iδ)`; messages sent in round `i` are delivered at `iδ`
   (`nextRound`). "Decides not later than `2Δ`" means: decides in its state after processing the deliveries of
   time `2δ`, i.e. at some time `≤ 2δ + 1` (`Run.DecidesBy … (2δ+1)`). In the PSync model a process sends at time `τ`
   based on its state *before* the receptions of time `τ`, so a reply to a message received at `iδ` leaves at
   `iδ + 1`; this is still in round `i + 1` iff `δ ≥ 2`. For `δ = 1` our two-step requirement is therefore
   stronger than the paper's (replies would arrive one round late); the theorem holds for every `δ ≥ 1`, and is
   faithful for `δ ≥ 2`.
5. **Discrete clocks/timers.** Processes can only act at integer times; the paper's real-valued timers are
   discretized. Since this restricts protocols, impossibility in our model is formally weaker than in a dense-time
   model, but the proof is insensitive to it.
6. **Consensus.** Weak validity as a `ValidityProperty` (`weakValidity`); termination, agreement (also
   `p = q`, so decisions are stable) and validity in all valid, unforgeable runs (`SolvesConsensusAuth`).
   The paper's "consensus value `c(ρ)`" is replaced by decisions of individual processes plus agreement
   (`tsRun_agree`).

## 3. Proof of Theorem 4.5

1. **Range of `n`.** Proved for all `2 ≤ n ≤ 3f + 2t − 2` (paper: `n = 3f + 2t − 2`). Case `n ≤ 3f`: the classic
   bound, proved (not assumed) from Theorem 1 of *On the Validity of Consensus* (PODC 2023,
   `ValidityConsensus.trivial_of_solvesConsensus_auth`, authenticated) since weak validity is non-trivial
   (`not_solves_of_le_three_mul`). This covers the paper's case `t ≤ 1`. Case `n ≥ 3f + 1` (then `t ≥ 2`): the
   paper's chain, with groups `|P₁| = |P₅| = t`, `1 ≤ |P₃| ≤ f − 1`, `|P₂|, |P₄| ≤ f − 1` (for
   `n = 3f + 2t − 2` all three have size `f − 1` as in the paper).
2. **`ρ₃`** is fixed concretely: synchronous (`gst = 0`, every message delivered at the next round boundary),
   `p` and `P₃` Byzantine, following the protocol in round 1 (`p` with input `I'(p)` towards `P₁ ∪ P₂` and
   `I''(p)` towards `P₄ ∪ P₅`), silent afterwards. The paper leaves `p`'s behaviour after round 1 implicit and
   takes "an arbitrary continuation". `T` is the decision time of one chosen process of `P₁` (resp. `P₅`).
3. **`ρ₄`** (and `ρ₂` as its mirror image under relabelling `i ↦ 6 − i` and swapping the two inputs of `p`,
   so it needs no separate proof): `P₃` is correct but its messages from round 2 on reach processes *outside
   `P₃`* only after `T` (messages inside `P₃` are timely — the paper's "not received by any other process" is
   read this way; it is needed for `P₃` to reach its `ρ₅` state); `P₅`'s messages to `P₃` from round 2 on are
   delivered after `T`; GST is `T + 2δ + 1`. We prove: `ρ₄ ∼_{P₃} ρ₅` up to `2δ + 1`
   (`rho4_st_eq_rho5_P3`), `ρ₄ ∼_{P₁ ∪ P₂ ∪ P₅} ρ₃` up to `T` (`rho4_st_eq_rho3`), validity and unforgeability
   of `ρ₄`; then agreement in `ρ₄` links the decisions (`decision_eq_rho4`). The paper uses "`ρ₄ ∼_{P₁} ρ₃`"
   via "identical to ρ₃ until time T"; we do exactly this.
4. **Lemma 4.3** is proved with the "slow" execution `ρ'` with no Byzantine processes in which `T`'s messages
   from round 2 on are delayed past `2δ + 1`, as in the paper.

## 4. Protocol and its safety

1. **Asynchronous interleaving transition system instead of the timed model.** The protocol (generalized version,
   Appendix A; parameters `1 ≤ t ≤ f`, `n ≥ 3f + 2t − 1`) is modelled as a transition system (`Protocol.lean`):
   global set `E` of emitted *tokens* (ideal signatures / authenticated messages: `propose`, `ack`, `certAck`,
   `commit`, `vote`), local states (view, latest acknowledged proposal, latest commit certificate) of correct
   processes, Byzantine processes emit arbitrary tokens signed by themselves. Correct processes may take any
   enabled step at any time; enabling conditions are stated on `E` (all emitted tokens) instead of "received
   messages" — an over-approximation, so safety of this system implies safety of any implementation. Timing,
   the view synchronizer and the leader map are arbitrary (nondeterminism). Liveness and the two-step property
   are proved for the concrete implementation (§5 below).
2. **Certificates.** A vote carries the signed pair `(x, u)` of its proposal and `(x', u')` of its commit
   certificate; the attached certificates `σ`, `τ`, `cc` are self-certifying, so verifiers check their existence
   in `E` (`ValidBallot`: `propose(leader u, x, u)` and `f + 1` `CertAck(x, u)` tokens (none for the first view);
   `ValidCC`: `⌈(n+f+1)/2⌉` `ack(x', u')` tokens). Equivalent for safety.
3. **CertReq/CertAck.** A correct process signs `CertAck(x, v)` whenever it sees a valid vote set for `v` on which
   the selection may output `x` (`Selects`); the CertReq message and the leader's identity are abstracted away
   (over-approximation). The selection is a *relation*: ties in case (2) (two values with `f + t` votes, possible
   when `n > 3f + 2t − 1`) and "any value" in the all-nil case and case (3) are allowed — every allowed outcome is
   proved safe. The "restart" rule of the selection is subsumed (any vote set `S` with `|S \ {leader w}| ≥ n − f`).
4. **Proposals.** A correct leader proposes once per view, its input in the first view and otherwise a value with a
   progress certificate (abstraction of "selected and certified").
5. **Decisions** are a predicate on `E`: `n − t` acks (fast path) or `⌈(n+f+1)/2⌉` commits (slow path) for the same
   `(x, v)`. Consistency is proved for any two values having decision quorums in any reachable state — stronger
   than "two correct processes decide" (a correct process can only decide on a quorum it received).
6. **Acks** are treated as tokens (in the generalized protocol they are accompanied by a signature anyway).
7. **Views start at 0** (paper: 1).
8. **Vanilla protocol (Section 3, `n ≥ 5f − 1`).** Theorem 3.6 is derived from Theorem A.4 with `t = f`
   (`consistency_five_f`): vanilla executions are executions of the generalized system with `t = f` in which no
   correct process takes a `commit` step and all votes carry no commit certificate (then the selection rule
   coincides with the vanilla one: threshold `2f = f + t`, fast quorum `n − f = n − t`). This embedding is argued
   here, not formalized.
9. **Lemma numbering.** Lemmas 3.1–3.5 are proved in their generalized form (Appendix A, `f + t` instead of `2f`):
   3.1 `not_all_nil_of_decided`, 3.2 `decided_view_le`, 3.3 `safe_of_single`, 3.4 `safe_of_many_votes`,
   3.5 `not_decided_of_few_votes`; QI1–QI3 are instances of `Finset.exists_mem_inter_notMem_of_card_le`.

## 5. Concrete implementation (`Implementation.lean`, `Impl*.lean`) — not in the paper in this form

1. **Message pattern.** Instead of the paper's point-to-point messages (propose, ack, sig, vote, CertReq, CertAck,
   Commit), every process gossips its whole set of known signed tokens at every step. Certificates therefore travel
   with whatever needs them; the leader's own `CertAck(x, v)` plays the role of `CertReq(x, votes)` (verifiers check
   the selection on the vote set they know, which contains the leader's since the leader gossips everything).
   Message *size* is unbounded (the paper's bounded-certificate motivation for the CertAck round is not modelled);
   the round structure (votes → CertReq/CertAck → propose → ack → commit) is kept, so latencies match.
2. **View synchronizer.** The paper leaves it unspecified (any synchronizer from the literature). In the PSync model
   clocks are perfectly synchronized (all correct processes step every tick from time 0), so view `v` is simply
   `[vL, (v+1)L)` with `L ≥ 6δ + 12`, and the leader rotates (`rotLeader`; any map in which every process leads
   infinitely often). Termination: the first view starting after GST with a correct leader decides at every correct
   process (slow path) by `vL + 6δ + 11`.
3. **Two-step property** needs `δ ≥ 2` (replies leave one tick after reception, see §2.4) and `L ≥ 2δ + 2`
   (no view change before `2δ + 1`). In the `T`-faulty two-step execution the `n − t` correct processes ack the view-0
   proposal at time `δ` and every correct process sees the `n − t` acks at `2δ` (fast path).
4. **Selection by the leader** is a choice among allowed outcomes (`leaderChoice`: its input if allowed). Verifiers
   sign one value per step.
5. **Weak validity** needs `t < n` (otherwise `n − t = 0` acks form a fast quorum for every value; harmless since
   `n ≥ 3f + 2t − 1`, `t ≥ 1`). Extended validity is not proved.
6. **Tightness theorem** `tight_bound` quantifies over protocols with message/state/token types in `Type` (universe 0).

## 6. Not formalized

- Section 4.3 (weakening the assumptions: suspects `M`, `|M| ≥ 2t + 2`) and Section 4.4 (the `3f + 2t + 1` bound
  for protocols with disjoint proposers/acceptors).
- Extended validity of the protocol; bounded certificate size.
