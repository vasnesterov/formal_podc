# VABA: Asymptotically Optimal Validated Asynchronous Byzantine Agreement — PODC 2019

Ittai Abraham, Dahlia Malkhi, Alexander Spiegelman. *Asymptotically Optimal Validated Asynchronous
Byzantine Agreement.* PODC 2019. DOI [10.1145/3293611.3331612](https://doi.org/10.1145/3293611.3331612).
Formalized version: arXiv [1811.01332](https://arxiv.org/abs/1811.01332) v1, the only arXiv version.
Numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The paper allows any `f < n/3`, but its thresholds are hard-coded as
`2f + 1`, which silently assumes `n = 3f + 1`. As a result, agreement (Lemma 13) and
PB-provability (Lemma 3) are false for `n > 3f + 1`: with `n = 5`, `f = 1`, honest parties decide
`true` and `false`. The protocol is correct when `n = 3f + 1`, and with thresholds `n − f` we prove
everything (agreement, validity, view completion, expected views `< 3/2`) for all `n > 3f`. Two
further fixes are needed: termination/efficiency need a halting rule, and Algorithm 6, line 4 has a
typo.

## Mistakes in the paper

* **The `2f + 1` thresholds are wrong unless `n = 3f + 1`.** Theorem 1 and the model allow any
  `f < n/3`, but signatures, skip shares and view-change waits all use `2f + 1`.
  - Lemma 3 (PB-provability) concludes that two sets of `2f + 1` signers share an honest party.
    That needs `n = 3f + 1`. Lemma 8 says "`2f + 1 = n − f`".
  - Take `n = 5`, `f = 1`. The corrupted party 4 is elected leader of view 1 and equivocates in
    every stage of its broadcast: 0 and 1 deliver `true`, 2 and 3 deliver `false`, and 4 signs
    both. The broadcasts of 0 and 1 complete normally, so the skip certificate forms, and honest
    parties 0 and 2 decide `true` and `false`.
  - This is a 58-step run of our model (`Counterexample.agreement_fails`).
  - Severity: Lemmas 3 and 13 (PB-provability, Agreement) are false for the algorithms as written
    whenever `n > 3f + 1`. The paper never restricts to `n = 3f + 1` (§2, §3 and Theorem 1 say
    `f < n/3`). Theorem 1 itself, an existence claim, survives: with threshold `n − f`, all our
    results hold for every `n > 3f`.
* **Termination is proved vacuously; Efficiency fails as stated.**
  - Algorithm 6 loops forever: deciding does not stop a party.
  - The proof of Lemma 20 says that honest parties never stop sending messages, "therefore,
    termination trivially follows". That uses the vacuity of "all messages have been delivered".
  - For the same reason honest parties send infinitely many messages, so Efficiency (Definition 4)
    fails. Lemma 24 only bounds the messages sent before everybody decides.
  - The real content is that every view completes (Lemma 19) and that each view decides with
    probability `≥ 2/3`. We prove both (`view_progress`, `card_undecided_le`).
  - A halting rule is missing. Note that a party cannot just halt after deciding: others may only
    be locked and still need its messages.
  - Severity: proof gap, under-specified protocol.
* **Typo in the key check (Algorithm 6, line 4): `j ≠ 1` must be `j ≠ 0`.**
  - Here `j` is the key's view, and the initial key is `⟨0, ⊥⟩`.
  - Read literally, every honest proposal of view 1 fails validation, so view 1 never completes.
    Keys of view 1 would also be accepted unchecked.
  - The proof of Lemma 15 reads `j` as the current view ("no key required in view 1"). That
    reading fails in view 2 whenever nobody got a key in view 1.
  - We use: the key view is `0`, or it carries a stage-1 certificate of that view's leader, and in
    both cases it is `≥ LOCK`.
* **View-change messages that arrive early.**
  - Algorithm 7 validates a view-change message against `L[j]`, which is `⊥` until the receiver's
    own `elect` returns.
  - Read literally, early messages lose their content but still count among the `2f + 1`.
  - Lemma 8 needs them buffered; our model buffers them.
  - Severity: under-specified. We did not check whether the literal reading breaks agreement.
* **Smaller gaps.**
  - Lemma 14 is stated only for a lock set *in* view `j`. Locks can be set later, and Lemma 15 needs
    the general form. That form is true: `Inv.key_of_lockQC`.
  - Lemma 6 is stated for stages 2–4 but used for stage 1 in Lemma 12; the proof works.
  - The Quality property of Definition 4 is never proved.
* **Typos.** Algorithm 3 has `return σ` for `σ_in`. Algorithm 7 has `lock` and `key.round` for
  `LOCK` and `KEY.view`, and forwards unvalidated skip messages. Lemma 21 has "`2f = 1`".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`):
* Protocol and parties.
  - Algorithms 1–7 form an interleaving transition system on `n = |P|` parties.
  - The 4-stage provable broadcasts are inlined: an honest party delivers stage `s` of proposer
    `k` iff the message passes `ex-sbc`/`ex-bc-validation` and the sender could have sent it. An
    honest proposer sends only its proposal.
* Asynchrony. The adversary schedules every enabled action in any order.
* Adversary. It corrupts up to `f` parties *adaptively*. A corrupted party's local state is frozen,
  and it signs anything.
* Threshold signatures are ideal: a certificate exists iff `Q` shares exist (`QC` is the shared
  `Cslib.Byzantine.Certified`, `Cslib/Computability/Distributed/Byzantine/Certificate.lean`). The paper's threshold
  is `2f + 1`; theorems take `n + f < 2Q` for safety and `Q + f ≤ n` for liveness, i.e. `Q = n − f`
  for any `n > 3f`.
* Common coin. It is ideal: a sequence of leaders, view `j`'s revealed at the first honest
  `elect(j)`.
* View-change messages.
  - They are buffered until the receiver knows the leader.
  - A corrupted sender can include any existing certificates.
* Probabilistic statements.
  - The adversary is a deterministic strategy on the full history of global states, which contain
    only revealed coins. That the adversary's "good set" of view `j` depends only on the coins of
    earlier views is *proved* (`good_congr`).
  - Probabilities are counts over uniform leader sequences, in the shared coin game
    `Cslib/Probability/CoinGame.lean` (also used for DAG-Rider).
* All cryptographic "except with negligible probability" qualifiers disappear with ideal
  functionalities.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 13 (Agreement), for all decisions of honest parties | `agreement`, `vaba_agreement` | `Safety.lean`, `Main.lean` |
| Corollary 16 (external Validity) | `validity`, `vaba_validity` | `Safety.lean`, `Main.lean` |
| Lemmas 3–6 (PB-provability, chains of certificates) | `Inv.qc_unique`, `Inv.qc_agree`, `Inv.qc_stage1` | `Safety.lean` |
| Lemmas 8, 9, 14 (lock / key after a certificate) | `Inv.lock_of_commitQC`, `Inv.key_of_lockQC` | `Safety.lean` |
| Lemma 12 (key safety) | `Inv.key_safety` | `Safety.lean` |
| Lemma 15 (honest proposals pass validation) | `proposal_valid` | `KeyInv.lean` |
| Lemmas 7, 17–19 (views complete; constructive) | `view_progress`, `vaba_view_progress` | `Liveness.lean`, `Main.lean` |
| Lemma 21 (skip ⇒ `Q` completed broadcasts) | `Inv.completed_of_skipQC`, `card_good` | `Safety.lean`, `ExpectedViews.lean` |
| Lemma 22 (completed leader ⇒ everyone decides) | `Inv.decide_of_completed`, `decided_of_hit` | `Safety.lean`, `ExpectedViews.lean` |
| Lemmas 23–24 (undecided after `k` views: prob. `≤ (f/n)^k < 3^{-k}`) | `card_undecided_le`, `prob_undecided_le` | `ExpectedViews.lean` |
| §3.3.1 (expected views `< 3/2`) | `expected_views_le`, `expected_views_lt` | `ExpectedViews.lean` |
| `n > 3f + 1` with threshold `2f + 1`: agreement fails | `Counterexample.agreement_fails`, `provability_fails` | `Counterexample.lean` |

**Not formalized.**
- Word/message complexity (`O(n²)` per view).
- The cryptographic implementations and the negligible-probability accounting (Definition 3,
  Lemma 1).
- Quality.
- The `Ω(n²)` lower bound of Appendix B, which reduces to a cited theorem.
- Liveness for *all* fair schedules; we prove that honest steps can always complete the view.

**Trust.**
- No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
- Non-vacuity:
  - `view_progress` shows that views always can complete, so the probability bounds are not
    vacuous.
  - The counterexample run shows that the model's guards are satisfiable all the way to decisions.
- The model is paper-local; quorum intersection and certificates come from the shared
  `Cslib/Foundations/Data/Finset/Quorum.lean` and `Cslib/Computability/Distributed/Byzantine/Certificate.lean`. The safety invariants (`Inv`, `KInv`, `LInv`) are proved action by
  action for every reachable state.
