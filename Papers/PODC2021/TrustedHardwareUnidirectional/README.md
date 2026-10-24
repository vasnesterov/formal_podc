# Classifying Trusted Hardware via Unidirectional Communication — PODC 2021

Naama Ben-David, Kartik Nayak. *Brief Announcement: Classifying Trusted Hardware via Unidirectional
Communication.* PODC 2021. DOI [10.1145/3465084.3467948](https://doi.org/10.1145/3465084.3467948).
Formalized version: arXiv [2105.10566](https://arxiv.org/abs/2105.10566) v1 (full version, 11 pp.);
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** **The Claim of §4.1 is false.** It says sequenced reliable broadcast (SRB)
cannot implement unidirectional rounds when `n > 2f` and `f > 1`. In fact a simple echo protocol
implements them over SRB for every `n > 2f`. So the paper's separation "shared memory ⊋
unidirectionality ⊋ SRB" (Fig. 1, abstract) collapses: for `n > 2f`, unidirectionality and SRB are
equivalent, using the Claim of §4.2 for the other direction. The positive claims hold. Theorem 1
holds in an eventual form. The §3.2 claim (SWMR objects give unidirectionality) holds as stated.
The Appendix A claim holds. The §4.2 construction is safe with the conflict check described in
the text; Algorithm 3's pseudocode omits that check and then violates agreement (a pseudocode slip).

## Mistakes in the paper

* **The Claim of §4.1 is false (main error).** Counterexample protocol (`Echo.echoProtocol`). In
  round `r`, each process SRB-broadcasts its signed message. Whenever it delivers some process's
  round-`r` message, it SRB-broadcasts an *echo* of it, i.e. relays the signed message. It ends round
  `r` once it has delivered echoes of its *own* message from `n − f` distinct senders. It has
  received `q`'s message if it delivered `q`'s message or any echo of it.
  - *Why it works.* Take two correct processes `p`, `q`. Their echo-sender sets have `n − f`
    elements each, so they share a sender `s` (possibly Byzantine), because `n > 2f`. SRB delivers
    `s`'s messages to everybody as prefixes of a single sequence. Whichever of `echo(p)`, `echo(q)`
    comes first in that sequence has been delivered by *both* `p` and `q` before they ended the
    round.
  - *Liveness.* The `≥ n − f` correct processes echo everything.
  - *Within the paper's model.* The protocol uses only what the paper itself assumes and uses:
    transferable signatures (§2), relayed signed messages counting as "received", and waiting for
    messages from `n − f` processes — exactly the ingredients of the paper's own Appendix A protocol
    for `f = 1`. Definition 2 puts no other constraint (e.g. wait-freedom) on how rounds end.
  - *What breaks in the paper's proof.* Scenario 1 asserts that `C₂` "must eventually start the
    next round since they are receiving all messages sent by correct processes". This is
    unjustified: a round may wait until its own messages have been echoed by `n − f` processes. In
    Scenarios 1–3, `C₁` and `C₂` do not end the round until their delayed messages reach `Q`, and
    then the scenarios are no longer indistinguishable.
  - *Lean.* We prove that the echo protocol satisfies Definition 2, plus integrity and liveness in
    every fair execution, against any SRB adversary with unforgeable signatures, for every
    `n > 2f`. The formal statement of the claim is refuted for `n = 5`, `f = 2`.
  - *Consequences.* The appendix "corner case" `f = 1` is not special, and the headline
    classification in the abstract and §1 does not follow from the paper. A remark we did **not**
    formalize: the same echo idea seems to work with TrInc-style attested logs. A receiver accepts
    the `k`-th attested message of `s` only after all earlier ones (Algorithm 2's `prev`), so
    "trusted logs do not give unidirectionality" is doubtful as well.
  (`claim_4_1_false`, `srb_implements_unidirectional`, `Echo.echoProtocol_implements`)
* **Algorithm 3 as printed violates agreement (property 2 of SRB).** The text of §4.2 says a
  process builds an L1 proof only if it sees `t+1` copies of its own value "*and no other value*".
  This check is what the Lemma 3 Case 1 argument uses. The pseudocode (lines 29–39,
  `validateValue`) merely ignores conflicting copies.
  - *Counterexample* (`n = 3`, `t = 1`). The sender `0` is Byzantine; it sends `m` to `1` and `m'`
    to `2`. In the forwarding round, `2` hears `1` (so unidirectionality holds), but `1` does not
    hear `2`. Each of `1` and `2` has two copies of its own value: its own and `0`'s. Under the
    printed rule both build L1 proofs.
  - *Result.* Process `0` builds L1 proofs for both values. So `{1, 0}` is an L2 proof of `m` and
    `{2, 0}` is an L2 proof of `m'`, and the correct processes `1` and `2` deliver different
    messages with the same sequence number.
  - *With the text's rule.* Agreement (Lemma 3 Case 1) and Lemma 4 are proved.
  - *Seriousness.* A pseudocode slip, not a flaw of the construction: the text states the intended
    rule, and the safety core of the Claim of §4.2 holds with it.
  (`Alg3.pseudo_disagreement`; repaired: `Alg3.agreement`)
* **Unidirectional rounds are under-specified for Algorithm 3.**
  - *The gap.* Definition 2 only relates messages sent in the *same* round `r`. Algorithm 3 uses
    "the unidirectional round" for every (sender, sequence number) instance without saying which
    round. Processes handle instances at different paces, and may skip one after seeing an L2
    proof. So a single round sequence cannot be aligned across processes.
  - *Fix.* The argument needs a separate round instance per (sender, sequence number), which
    tagging provides. Under-specified definition; harmless once fixed. Our `Alg3` model assumes
    this.
* **Theorem 1 is stated for the exact TrInc interface but proved only in an eventual form.**
  Algorithm 2 asks `CheckAttestation` to return true for every attestation previously output. The
  SRB implementation can only return true once the attestation has been delivered; the paper's
  proof shows exactly this eventual property (1). Further problems in the implementation:
  - `Attest` never returns `null` for a non-increasing counter. The returned "attestation" is
    simply never valid (`TrInc.attest_nonincreasing_invalid`).
  - `k` is never incremented.
  - The attestation omits `prev`.

  We prove consistency between checkers, non-equivocation (one valid attestation per counter),
  soundness (property (2)) and completeness for increasing counters (property (1)). Imprecise
  statement; the result holds in the eventual form.
* **Appendix A's proof has gaps; the statement is true.**
  - "All processes in `Q` must receive at least one of `p` or `p'`'s messages in phase 1" is false
    for a Byzantine member of `Q`.
  - "W.l.o.g. they receive `p`'s value" ignores that different members of `Q` may see different
    values.
  - "Valid phase-2 messages must contain `n − 1` values" contradicts the protocol's check
    `m ≥ 2`.
  - *Correct argument* (`AppendixRB.appendix_claim`). If `n ≥ 4`, `Q` contains a correct process.
    If `n = 3`, the `m ≥ 2` check and the non-equivocation of reliable broadcast force the
    Byzantine member's phase-2 message to contain `p`'s or `p'`'s value.
* **Typos and small slips.**
  - `validateL1Prf` is defined twice; the second definition should be `validateL2Prf`.
  - `maybeDeliver(val)` takes no parameter.
  - `key == k` refers to an undefined `key`.
  - Lemmas 2 and 3 speak of `last[p]`; the code has `next_p`.
  - "line ??" in Lemma 2.
  - `checkL2Proof` is called without a proof argument.
  - Lemma 2 needs a process to count its own copy, otherwise `n = 2t + 1` correct processes only
    produce `t` copies from others.
  - §3.1 says "but using" for "by using".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Round layer spec** (`Rounds.lean`, Definition 2). A system exposes, for each process, the list
  of completed rounds; entry `r` holds the round-`r` messages received before the round ended.
  Messages are chosen by an arbitrary adaptive *client* (round-`r` message = function of earlier
  receipts). `ImplementsUnidirectional` requires four properties:
  - completed rounds never change;
  - Definition 2 for all correct `p ≠ q`;
  - integrity: a message "received" from a correct `q` is `q`'s real round-`r` message;
  - liveness: every correct process completes every round in every fair execution.
* **SRB systems** (`SRB.lean`, Definition 1). Asynchronous; a set `F` of Byzantine processes,
  `|F| ≤ f`; one SRB instance per process.
  - SRB properties 2–4 mean the deliveries of correct processes are prefixes of one *log* per
    sender. A Byzantine sender appends arbitrary messages to its log.
  - Signatures are unforgeable and transferable. A message declares the signed messages it relays,
    and a Byzantine process may relay `(q, m')` only if `q` is Byzantine or `m'` is in `q`'s log.
  - Protocols are arbitrary deterministic message-driven state machines with arbitrary message and
    state types.
  - Scheduling is arbitrary. Fairness is exactly SRB properties 1 and 2. Fair executions exist for
    every protocol (round robin, `SRBProtocol.rrExec_fair`).
* **SWMR shared memory** (`SWMR.lean`, §3.2). Every access (append-write of the own object, read of
  one object) is an atomic step under an arbitrary interleaving. Byzantine processes overwrite their
  own objects arbitrarily; there is no bound on `|F|`. Fairness: correct processes take infinitely
  many steps. Fair executions exist.
* **Theorem 1** (`TrInc.lean`) is proved at the level of the SRB log of one sender. A correct
  checker's delivered messages form a prefix of that log; the stored attestations are a function of
  that prefix.
* **Claim of §4.2** (`Alg3.lean`) and **Appendix A** (`AppendixRB.lean`) are formalized at the
  level of the end-of-round data:
  - §4.2: who forwarded what, who heard whom before compiling L1 proofs, and who issued L1 proofs;
  - Appendix A: phase-1/phase-2 senders and phase-2 contents, with one common content per sender
    (reliable broadcast).

  These capture the safety arguments of Lemmas 3–4 and the Appendix exactly. Liveness (Lemmas 2 and
  3 Case 2) is formalized only through its counting core.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 1 (SRB), asynchronous Byzantine model | `SRBProtocol`, `SRBProtocol.Step`, `SRBProtocol.Fair` | `SRB.lean` |
| Definition 2 (unidirectional rounds) | `RoundSystem.ImplementsUnidirectional` | `Rounds.lean` |
| Theorem 1 (SRB implements TrInc), properties (1), (2) + non-equivocation | `TrInc.accepted_complete`, `TrInc.accepted_sound`, `TrInc.eq_of_counter_eq`, `TrInc.accepted_prefix` | `TrInc.lean` |
| Claim §3.2 (SWMR objects ⇒ unidirectionality) | `SWMR.swmr_implements` | `SWMR.lean` |
| Claim §4.1 (SRB cannot implement unidirectionality, `n > 2f`, `f > 1`) — **false** | `Claim_4_1`, `claim_4_1_false` | `Claim41.lean` |
| SRB implements unidirectionality for every `n > 2f` (new) | `srb_implements_unidirectional`, `Echo.echoProtocol_implements` | `Claim41.lean`, `EchoProof.lean` |
| Claim §4.2, Lemma 3 Case 1 (agreement, with the text's check) | `Alg3.agreement` | `Alg3.lean` |
| Claim §4.2, Algorithm 3 as printed — **agreement fails** | `Alg3.pseudo_disagreement` | `Alg3.lean` |
| Lemma 4 (integrity) | `Alg3.l2_signed` | `Alg3.lean` |
| Lemma 2 (validity), counting core | `Alg3.validity_core` | `Alg3.lean` |
| Claim of Appendix A (`f = 1`, `n ≥ 3`) | `AppendixRB.appendix_claim` | `AppendixRB.lean` |

**Not formalized.**
* Operational liveness of Algorithm 3 (Lemmas 2 and 3 Case 2 beyond their counting core); Lemma 1,
  which is immediate.
* Fig. 1's claim that trusted logs are *weaker* than SRB (only "SRB implements TrInc" is claimed and
  proved).
* The remark about attested logs above.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`.

Non-vacuity checks:
* `SRBProtocol.rrExec_fair` and `SWMR.rrExec_fair`: fair executions exist.
* `echo_fair_exec_exists`: a fair execution of the echo protocol with `n = 5`, `f = 2`, two
  Byzantine processes, in which all rounds complete.
* `Alg3.agreement_nonvacuous` and `AppendixRB.valid_nonvacuous`.

The model is self-contained (Mathlib only). CSLib candidates: the SRB model with signatures and its
round-robin fair executions (`SRB.lean`, `SRBFair.lean`), and the generic round-layer spec
(`Rounds.lean`).
