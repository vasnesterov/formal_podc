# Differences between the formalization and the paper

Paper: Clement, Junqueira, Kate, Rodrigues, *On the (Limited) Power of Non-Equivocation*, PODC 2012
(8-page author copy with appendices).

## Errors in the paper

1. **Section 4 / Figure 2 / Appendix B: the translation is unsound (❌).**
   * **Claim.** "There exists a translation of a distributed protocol that can tolerate `f` crash
     faults into one that tolerates `f` Byzantine faults using the same number of processes"
     (§4). The abstract says "transform any protocol that works under the crash fault model into a
     protocol that tolerates Byzantine faults", and the introduction says "provides the same
     guarantees". The witness is Figure 2, argued in Appendix B.
   * **Counterexample.** `Translation.translation_unsafe`.
     * The protocol `grantProto` (`n = 3`) never lets server `0` record client `2`, in any crash
       execution (`crash_safe`).
     * Its translation reaches, with the single Byzantine process `2`, a configuration where the
       correct server has recorded `2` (`reach_c₄`, `c₄_served`).
     * The adversary is unforging (`Unforged`: every correct-signed tuple it uses was seen) and
       non-equivocating (`NonEquiv`).
   * **Cause.** Signed B-messages and the replay check carry no recipient information, so a
     Byzantine process may replay inputs that were addressed to others. The paper's Integrity
     requirement (§4.1) does not exclude this either. So the three requirements of §4.1 (Safety,
     Integrity, Consistency) do not suffice for "the same guarantees".
   * **Robustness.** The attack message equals what the translated code of a correct `2` would
     send after receiving the grant (`attack_eq_honest`). Its signed tuple equals that of the
     honest `u₁` of client `1`; only the signer differs. So every reading of the garbled check
     `kp = |Rp| = |Sp|` that accepts `u₁` accepts `u₂`. The only way to reject it is to check recipients. For a deterministic protocol, a verifier
     could recompute each replayed input's recipient set during the recursive replay (`grant`
     goes to `{1}`) and check that it contains the replayed process. Figure 2 does not do this:
     it compares only the payloads of `S` with the replay. §4.1 Integrity and Appendix B do not
     ask for it either. So this is a design change, not a typo with evident intent.
   * **Scope of the refutation.** The translation is a main claim of the abstract. But
     every place that states it is existential: the abstract says "it is possible to use
     non-equivocation to transform any protocol", §4 says "there exists a translation", and the
     introduction says "we show how we can … obtain a generic transformation". None of them names
     the Figure 2 compiler as the result. The counterexample refutes only the paper's witness. The
     existential statement is at worst unestablished. A repaired compiler
     also appears to exist: sign the recipient set (or recompute it by replay), check that every
     replayed input was addressed to the replayed process, and reject duplicated inputs.
     Ben-David–Chan–Shi (PODC 2022) give a corrected 1:1 compiler (PKI + non-equivocation,
     multicast model, f < n/2). We have not formalized a repaired translation.
2. **Claim 3.1: proof gap, statement true for `n ≥ 3` (🔧).**
   * **Gap.** Run 3 keeps the `A ↔ B` messages timely after time `t`, so `B` may diverge from
     Run 2 (where `A` crashed at `t`). The step "processes in `C` deliver `m'` by `t''`, since they
     cannot distinguish Run 3 from Run 2" then fails.
   * **Repair.** We also delay `A → B` messages sent after `T₁` until `H` (`Claim31.dl34`).
   * **Smaller imprecisions.** Run 1 cites "Liveness and Agreement" where L1, L2 and S2 are used.
     Run 2's "by Agreement" also needs L2 (Completeness).
3. **Claims 3.1 and 3.2 are false for `n ≤ 2` (🔧).**
   * **Why.** "W.l.o.g. `n = 3f`" fails: the three groups must be nonempty, which needs `n ≥ 3`.
     For `n ≤ 2`, r-broadcast is solvable for every `f` (`SmallCases.lean`, protocol `echo`).
   * **Lean.** `claim_3_1_false_small` (with `RespectsNE` for every key map) and
     `claim_3_2_false_small` (unauthenticated, hence trivially unforging). Our versions assume
     `3 ≤ n ≤ 3f`, i.e. `3 ≤ n < 3f + 1`.

## Modelling choices and differences

* **Time and asynchrony.**
  * We use CSLib's discrete-time model. Correct processes step at every tick, and messages of one
    (sender, time, receiver) batch are delivered together.
  * These restrictions only weaken the adversary, so the impossibility results transfer to the
    paper's asynchronous model.
  * The lower bounds are proved for `Run.Valid f δ`, partial synchrony with any `δ`. That is a
    subclass of `Run.AsyncValid f` (the paper's model, "messages are eventually delivered"), so
    the lower bounds are stronger than claimed. `claim_3_1_async` and `claim_3_2_async` are the
    literal asynchronous versions.
  * The positive results (`echo`, `relay`) are proved for `Run.AsyncValid f`.
* **Definition 1.**
  * "The sender sends `m`" is "the sender's input is `m`"; the sender broadcasts from time 0.
  * "`p` delivers `v`" is `Run.Decides`: the decision read from `p`'s state equals `v` at some time.
  * Integrity (S3) is "all delivered values are equal". This is weaker than "delivers at most
    once" (redelivering the same value is not counted), so the impossibility is stronger. Our
    protocols never change a decision once made.
  * The paper's "point-to-point authenticated links" are built into the model: inboxes are
    indexed by sender.
* **Non-equivocation (§2.4).**
  * Messages carry keys via an arbitrary key map `key : M → κ`. The paper's pairs `(k, m)` are
    `key = Prod.fst`, and messages without a key may use the identity.
  * Faulty processes never send two different messages with the same key (`NonEquivocating`).
  * Correct processes do not equivocate by assumption on the protocol (`RespectsNE`): the protocol
    uses the primitive as intended. The device would refuse equivocating correct sends; we did not
    model that refusal.
  * The predicate `valid_p(k, m)` is evaluated only by the direct recipient (it is part of the
    link). This is the paper's intended reading for Claim 3.1: "the valid predicate is generally
    realized using the verify predicate", and there is no transferable authentication. If `valid`
    were evaluable by third parties, it *would* be transferable authentication and Claim 3.1 would
    fail (see `NEPlusTA.lean`).
* **Imitating adversary (Claim 3.1).** `claim_3_1_imitating` holds against faulty processes that
  only send, per link and time, nothing or exactly their messages in some run where they are
  correct. This is the strongest form we prove. `claim_3_1` is the corollary for non-equivocating
  adversaries.
* **Signatures (Claim 3.2, §3 positive part).**
  * We use CSLib's abstract unforgeable tokens. Correct processes only emit own or received
    tokens. The adversary is rushing and eavesdropping: it may use tokens emitted by correct
    processes up to now.
  * For the positive result, messages are attestations `Att` (signer, key, value), and
    non-equivocation of attestations is `AttNonEquivocating` (faulty signers, messages shown to
    correct processes).
* **§3 positive part.** The paper says NE + transferable authentication "are sufficient to
  improve the resiliency bound to `n ≥ 2f + 1`" (via the translation). For r-broadcast we prove
  more: a direct relay protocol (`relay`) works for every `n` and `f`. This matches the crash
  bound `n ≥ f + 1` that the paper cites for Figure 3.
* **Section 4 model.**
  * Protocols (`Protocol`) have a start step (initial state and sends) and one transition per
    received message, with sends `(payload, recipients)`. The paper's model (§2.2) receives a
    *set* per step, and the paper does not model spontaneous initial sends, but its §4.1 mentions
    external inputs.
  * The check of Figure 2 is read as follows (`check`):
    1. the signer is the link sender;
    2. `k = |S| + 1`;
    3. `S` is signed by the sender;
    4. the payloads of `S` followed by `m` are a prefix of the outputs of replaying the sender's
       state machine on `R`;
    5. recursively, every message of `R` passes the checks.
  * The literal "`kp = |Rp| = |Sp|`" rejects every honest message (e.g. `u₁` has `k = 1`,
    `|R| = 1`, `|S| = 0`), so it cannot be meant literally. As explained above, the attack does
    not depend on this reading.
  * In Figure 2 the received message is added to `R` *after* the T-receive handler runs. We add it
    before, so that the outputs caused by a message are justified by an `R` containing it.
    Otherwise honest messages would fail the replay check. Appendix B confirms this intent: the
    receiver runs `R₁ … R_h` and checks that `m` "corresponds to the state `Σ_{p_s,h}`".
  * Crash executions (`CReach`) allow any delivery order, message loss, and crashes, which is a
    superset of the paper's crash model. The safety of `grantProto` is proved for all of them.
  * The Byzantine adversary of the translated system (`TStep.inject`) is weaker than a general
    one. It may only send unforged messages, i.e. every correct-signed tuple inside has been
    delivered to a Byzantine process, and it may not reuse one of its keys.
* **Not formalized.**
  * Consensus/SMR/VSS corollaries (§3) and "Byzantine agreement with `2f + 1` processes" (§4).
  * Liveness of the translation, which §4.1 deliberately excludes. A Byzantine process can also
    withhold a message from one recipient forever while continuing to send to it. Since
    `T-receive` delivers only the top-level payload, the recipient never gets the withheld
    message, which can hurt liveness of crash protocols that rely on eventual delivery of all
    messages of live processes. We did not formalize this.
  * Duplicate replay: with `R` a list, a Byzantine process can feed the same authentic input twice.
    With `R` a set, as the paper writes, this is impossible. We did not formalize this, since the
    recipient attack already refutes the claim under both readings.
