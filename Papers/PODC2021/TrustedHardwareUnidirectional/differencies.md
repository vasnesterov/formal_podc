# Differences between the formalization and the paper

Paper: Ben-David, Nayak, *Classifying Trusted Hardware via Unidirectional Communication*, PODC 2021 BA,
arXiv 2105.10566 v1.

## Model and definitions

1. **System model (§2).** The paper's model is informal: asynchronous, `n` processes, up to `f`
   Byzantine, unforgeable transferable signatures, plus a communication primitive. We use two explicit
   operational models.
   * SRB systems (`SRB.lean`).
   * SWMR shared memory (`SWMR.lean`).

   In both, protocols are deterministic state machines, scheduling is an arbitrary interleaving of
   atomic steps, and fairness is stated explicitly.
2. **SRB (Definition 1).** Properties 2–4 together with "unique sequence numbers" are modelled
   structurally:
   * Each sender has one log.
   * A correct process delivers the log entries in order.
   * The log of a correct sender is what it broadcast.

   Properties 1 and 2 (eventual delivery) are the fairness condition `SRBProtocol.Fair`. Two
   modelling choices:
   * Every process is the designated sender of its own SRB instance. The paper uses SRB this way in
     Theorem 1.
   * Messages carry no explicit sequence number; the log index plays that role.
3. **Signatures.** A message declares the signed messages of other processes that it relays
   (`relays`). A Byzantine process may relay `(q, m')` only if `q` is Byzantine or `m'` is already in
   `q`'s log. This models "correct processes sign exactly what they broadcast". It is weaker than
   real signatures for the adversary only in one respect: the Byzantine process need not have
   *received* `m'`. Correct processes are not constrained; the protocol is trusted.
4. **Definition 2 (unidirectional rounds).** The paper only says a system "can implement rounds"
   with the property. Our spec `RoundSystem.ImplementsUnidirectional` makes this precise and adds
   three requirements that the paper leaves implicit:
   * integrity: received messages from correct processes are genuine;
   * liveness: every correct process completes every round in fair executions;
   * immutability of completed rounds.

   Round messages are chosen by an arbitrary adaptive client. Every correct process sends a message
   to all in every round, so the hypothesis "both send a message to each other" always holds. For
   the refutation of §4.1 these extra requirements only make our positive result stronger. For §3.2
   they are additional facts proved.
5. **"Receive"** in Definition 2 is the round layer's output, not a network event. As in the paper's
   own Appendix A protocol, it may come from a relayed signed copy.

## Theorem 1 (SRB implements TrInc)

6. Algorithm 2 requires `CheckAttestation(a, q)` to return true for *every* attestation previously
   output by `T_q`. Over asynchronous SRB this holds only after delivery. The paper's proof shows the
   eventual property (1) and property (2), and so do we:
   * `accepted_complete` gives (1). Eventual delivery is SRB property 1 (`Fair`).
   * `accepted_sound` gives (2).
7. The implementation's `Attest` returns `(k, (c, m))` even when `c` is not larger than all
   previously used counters; Algorithm 2 requires `null` there. Such attestations are never valid
   (`attest_nonincreasing_invalid`). Completeness is proved for attesters using strictly increasing
   positive counters, i.e. with Algorithm 2's check added to `Attest`.
8. `k` is never incremented in the implementation, and the attestation lacks Algorithm 2's `prev`
   field. We use the SRB log index as `k`. We prove that the stored attestations form a chain with
   increasing counters (`accepted_prev`), so `prev` is determined.
9. We additionally prove consistency between checkers (`accepted_prefix`) and global
   non-equivocation (`eq_of_counter_eq`). Theorem 1 is formalized at the level of one sender's SRB
   log and a checker's delivered prefix, not as an operational client–object composition.

## Claim of §3.2 (SWMR ⇒ unidirectionality)

10. Objects are SWMR registers holding lists of `(round, message)`. "Append" is one atomic write of
    the extended list, and each read of one object is an atomic step. A process reads the objects in
    a fixed order (`Finset.univ.toList`). Any order works; the paper says `o₁ … oₙ`.
11. Byzantine processes may overwrite their own object arbitrarily, at any time, and there is no bound
    on their number. The paper does not discuss Byzantine writers, but the claim needs no bound.
12. When an object contains several `(r, m')` pairs (possible only for Byzantine owners), the reader
    picks one. The paper does not specify which.
13. The paper's claim covers all objects with ACLs, including PEATS and sticky bits. We formalize the
    SWMR-register case, which the paper's proof uses ("object `oᵢ` can be modified by `pᵢ`").

## Claim of §4.1 (SRB cannot implement unidirectionality) — refuted

14. `Claim_4_1` states the claim in our SRB model: for all process sets with `2f < n` and `f > 1`,
    all message/state types, and every protocol, the protocol does not implement unidirectional
    rounds. `claim_4_1_false` refutes it for `n = 5`, `f = 2`. `srb_implements_unidirectional` gives
    a protocol for every `n > 2f`.
15. Our spec includes multi-round operation with adaptive clients, integrity and liveness. So the
    refutation also holds against any weaker reading of "implements unidirectional rounds", for
    example one round only, or fixed messages.

## Claim of §4.2 (unidirectionality ⇒ SRB, Algorithm 3)

16. **Not an operational model.** We formalize one instance (sender `p`, sequence number `k`) at the
    level of its certificates (`Alg3.Inst`). The instance records:
    * the values signed by the sender;
    * the value each correct process forwarded;
    * what each process heard in its forwarding round before compiling its L1 proof;
    * who issued L1 proofs for which values.

    The constraints (`Valid`) are those guaranteed by the model: sender signatures on copies,
    genuine copies from correct processes, Byzantine L1 proofs only for sender-signed values, and
    unidirectionality of the forwarding round.
17. **L1 rule.** The text ("…and no other value") and the pseudocode (`validateValue` only filters)
    differ. We formalize both (`RuleText`, `RulePseudo`).
    * Agreement holds for the text (`agreement`).
    * Agreement fails for the pseudocode (`pseudo_disagreement`).
18. **Round instances.** We assume one unidirectional round instance per (sender, sequence number),
    in which all forwarders of that instance take part. The paper does not say which round is used.
19. Lemma 2 (validity) and Lemma 3 Case 2 (totality) are liveness properties. We prove only their
    combinatorial core (`validity_core`): with a correct sender and `n ≥ 2t+1`, the text's L1
    condition is met once the copies of the correct processes arrive, and the correct L1 proofs
    form an L2 proof. The relaying of L2 proofs (line 58) and the induction over sequence numbers
    are not formalized.
    * The count includes a process's own copy (`heard r r`), which Lemma 2 needs for `n = 2t+1`.
20. Lemma 1 (in-order delivery) holds by construction of `next_p` and is not formalized separately.
21. Lemma 4 is proved as "an L2-proved value was signed by the sender" (`l2_signed`). For a correct
    sender, the signed values are the broadcast ones.

## Claim of Appendix A (RB ⇒ unidirectionality for `f = 1`, `n ≥ 3`)

22. Formalized at the level of the end-of-round data (`AppendixRB.Round`):
    * the phase-1 senders received in phase 1;
    * the phase-2 senders received in phase 2;
    * the signer set of each process's phase-2 message.

    Reliable broadcast is modelled by one common content per process. Signatures (validity of
    contents) are not modelled; they are not needed for the timing argument. We assume:
    * a correct process forwards at least what it received in phase 1;
    * every valid phase-2 message has `≥ 2` signers.
23. Waiting for "`n − 1` distinct processes" is modelled as `≥ n − 1` elements, with or without the
    process itself. Both readings are covered.
24. The paper's proof has gaps (Byzantine member of `Q`; the w.l.o.g.). Our proof follows a different
    case split, `n ≥ 4` versus `n = 3`.
25. Liveness of the Appendix protocol is reduced to its counting core (`appendix_live_core`).

## Not formalized

26. Fig. 1's arrow "trusted logs → SRB" as a strict separation (the paper claims no proof of
    strictness).
27. Intro/abstract statements comparing with synchrony and with consensus solvability
    (cited results).
