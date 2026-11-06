# On the (Limited) Power of Non-Equivocation — PODC 2012

Allen Clement, Flavio Junqueira, Aniket Kate, Rodrigo Rodrigues. *On the (Limited) Power of
Non-Equivocation.* PODC 2012. DOI [10.1145/2332432.2332490](https://doi.org/10.1145/2332432.2332490).
Formalized version: the 8-page author copy (A. Kate's Purdue page; no arXiv version), which includes
the appendices. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Weakened.** The two lower bounds hold for `n ≥ 3`: Claim 3.1 says non-equivocation without transferable
authentication does not beat `n > 3f`, and Claim 3.2 says signatures without non-equivocation do not beat it either.
The positive direction holds for r-broadcast: with both primitives it works for every `n` and `f`. But the paper's
generic crash-to-Byzantine translation (Section 4, Figure 2, Appendix B) is **unsound**: a crash-safe 3-process protocol
becomes unsafe after translation with one Byzantine process, because a Byzantine process can replay messages that were
addressed to other processes, and no repaired compiler is proved.

## Mistakes in the paper

### ❌ Section 4, Figure 2, Appendix B (crash-to-Byzantine translation)
The translation does not preserve the guarantees of crash-tolerant protocols: a 3-process protocol in
which server `0` records only client `1` in every crash execution, once translated, lets a single
Byzantine client `2` replay the grant addressed to `1` and get itself recorded by the correct server
(`Translation.translation_unsafe`).

**Impact.** Refutes the paper's witness for the claim "it is possible to … transform" any crash-tolerant
protocol (abstract, intro, §4), which stays unestablished; a repaired compiler appears to exist. The
lower bounds of Section 3 are unaffected.

**Details.** Section 4 claims that Figure 2 turns any protocol tolerating `f` crashes into one
tolerating `f` Byzantine faults with the same number of processes ("provides the same guarantees",
abstract and introduction). A translated B-message `((k, m, R, S), σ)` carries the sender's received
messages `R` and sent messages `S`. The receiver replays the sender's state machine on `R`. Neither
the signed tuple nor the checks mention recipients. So a Byzantine process can feed its replayed
state machine an authentic message that a correct process sent to *someone else*, and everything it
then sends passes the checks. It learns such messages, signature included, from the `R` field of any
later message of their recipient. The paper's Integrity requirement (§4.1) has the same blind spot: a
valid message is "the output of applying a sequence of valid messages to the state machine", with no
condition on who those messages were sent to. So Appendix B's argument cannot exclude this attack.

Counterexample (`n = 3`, `f = 1`). Server `0` grants a token to client `1` only. A client granted by
`0` multicasts `use` to the two other processes, and the server records who sent `use`. In every
crash execution the server records only `1` (any crashes, losses, or orders). In the translated
system:
1. client `1` T-receives the grant `g` and multicasts `u₁ = ((1, use, [g], []), σ₁)`;
2. the Byzantine client `2` takes `g` out of `u₁` and sends `u₂ = ((1, use, [g], []), σ₂)` to the
   server;
3. `u₂` passes all checks, so the correct server records `2`.

The adversary signs only as `2`, relays `0`'s signature that it has seen, and uses key `1` once, so it
respects unforgeability and non-equivocation. `u₂` is exactly what the translated code of a correct
`2` would send after receiving `g`. Its signed contents equal those of the honest `u₁`; only the
signer differs. So every reading of the sloppy check `kp = |Rp| = |Sp|` that accepts `u₁` from `1`
also accepts `u₂` from `2`. A verifier could reject `u₂` by recomputing, during the recursive replay,
each input's recipient set (`grant` goes to `{1}`). But Figure 2 compares only payloads with `Sp`, and
neither §4.1 Integrity nor Appendix B asks for a recipient check. Adding one changes the protocol; it
is not a reading of it. So the failure is real, not just a gap. Every statement of the claim (abstract,
intro, §4) is existential ("it is possible to … transform", "there exists a translation"), not "Figure 2
is correct". The counterexample refutes only the paper's witness, and a repaired compiler appears to
exist. (`Translation.translation_unsafe`, `Translation.check_u₂`, `Translation.attack_eq_honest`)

**Repair.** One repair is to sign recipient sets, check that every replayed input was addressed to the
sender, and reject duplicate inputs. Ben-David, Chan and Shi (PODC 2022) give a corrected compiler in
a multicast model. We did not formalize a repaired translation.

### 🔧 Claims 3.1 and 3.2 for `n ≤ 2`
Both claims are stated for every `n < 3f + 1`, but for `n ≤ 2` r-broadcast is solvable for every `f`,
without signatures and against equivocation (`claim_3_1_false_small`, `claim_3_2_false_small`).

**Impact.** The added condition `3 ≤ n` saves the bound: both claims hold for `3 ≤ n ≤ 3f`
(`Claim31.claim_3_1`, `Claim32.claim_3_2`). The proof of Claim 3.2 is otherwise correct.

**Details.** Both proofs assume "w.l.o.g. `n = 3f`" with three nonempty groups. For `n ≤ 2`, the
sender delivers its message and keeps sending it, and the other process delivers the first message it
gets from the sender. Two distinct correct processes then include the sender.

### ✏️ Slips
- Figure 2, check `kp = |Rp| = |Sp|`: read literally, it rejects every honest message (for example `u₁` has `k = 1`,
  `|R| = 1`, `|S| = 0`). The key is the sender's sequence number, and Appendix B does not depend on the exact form;
  we read the check as `k = |S| + 1`.
- Figure 2, receive handler: the received message is added to `R` only after the T-receive handler runs, so outputs
  caused by it are not justified by `R` and honest messages fail the replay check. We add it before, the order
  Appendix B describes.

### Typos
- In Claim 3.1's proof, Run 2 says "by the Agreement property", but the step also needs Completeness (L2).

## Proof gaps (statements true)

### 🔧 Claim 3.1 (Run 3)
In Run 3, messages between `A` and `B` are "delivered in a timely fashion" throughout, but the
processes of `A` do not crash at time `t`, so after `t` the processes of `B` may act differently from
Run 2, and then `C` need not deliver `m'`, as the proof claims.

**Impact.** Statement true for `n ≥ 3`; repaired (`Claim31.claim_3_1`, `Claim31.claim_3_1_imitating`).

**Repair.** Also delay the `A → B` messages sent after `t`, like the other slow links. With this change
all four runs go through. They work even against an adversary that only *imitates* correct processes
of another run, and even in partially synchronous runs. (`Claim31.claim_3_1`,
`Claim31.claim_3_1_imitating`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model (Section 3).** CSLib's Byzantine message-passing model
(`Cslib.Byzantine.PartialSync`).
* Deterministic processes on authenticated point-to-point links.
* Runs are given by the adversary's data: faulty set, inputs, Byzantine messages, and delivery
  times.
* The lower bounds are proved for the runs `Run.Valid f δ` (partial synchrony, any `δ`). That is
  a smaller class than the paper's asynchronous one, so the results are stronger. The asynchronous
  corollaries use `Run.AsyncValid f`, where every message between correct processes is delivered
  at some finite time.
* Definition 1 (`IsRBroadcast`): the sender r-broadcasts its input, and "delivers `v`" means "its
  decision is `v` at some time".
* Non-equivocation: messages have keys (`key : M → κ`).
  * `NonEquivocating key R`: a faulty process never sends two different messages with the same key.
  * `RespectsNE A key`: the protocol uses the primitive as intended, so correct processes never
    equivocate.
* No transferable authentication: there are no tokens, so a relayed claim cannot be checked.
* Claim 3.1 is proved against the even weaker *imitating* adversary (`Imitating A R`). Every
  faulty process sends, on each link, nothing or exactly what it sends in some run in which it is
  correct.
* Transferable authentication: CSLib's ideal signatures (`Algorithm.Unforging`, `Run.AuthValid`).
  For the positive result, messages are transferable attestations `valid_p(k, v)` (`Att`), and
  `AttNonEquivocating` forbids two attestations of a faulty signer with one key.

**Model (Section 4).** A separate event-based model.
* Crash-model protocols (`Protocol`): deterministic automata with recipient lists.
* Crash executions (`CReach`): any delivery order, losses, crashes.
* The translation of Figure 2: `TMsg`, `check`, `tsend`, `trecv`.
* Executions of the translated system (`TReach`) with a static Byzantine set. The adversary may
  inject any message whose correct-signed parts it has seen (`Unforged`) and which never reuses
  one of its keys (`NonEquiv`).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definition 1 (r-broadcast) | `IsRBroadcast` | `Basic.lean` |
| Non-equivocation (§2.4) | `NonEquivocating`, `RespectsNE`, `Imitating.nonEquivocating` | `Basic.lean` |
| Claim 3.1 (`3 ≤ n ≤ 3f`) | `Claim31.claim_3_1`, `Claim31.claim_3_1_async`, `Claim31.claim_3_1_imitating` | `Claim31.lean` |
| Claim 3.2 (`3 ≤ n ≤ 3f`) | `Claim32.claim_3_2`, `Claim32.claim_3_2_async` | `Claim32.lean` |
| Claims 3.1/3.2 for `n ≤ 2` (false) | `claim_3_1_false_small`, `claim_3_2_false_small` | `SmallCases.lean` |
| §3: NE + transferable authentication suffice | `ne_plus_ta_rbroadcast` (every `n`, `f`) | `NEPlusTA.lean` |
| §4, Fig. 2, App. B (translation; false) | `Translation.translation_unsafe` | `Translation.lean` |

**Not formalized.** The extension to consensus, SMR and VSS ("stronger problems", §3) and the
claim that Byzantine agreement is solvable with `2f + 1` processes. The liveness of the
translation (the paper drops it on purpose, §4.1) and the duplicate-input variant of the replay
attack (see `differencies.md`).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The concrete attack trace is checked by `decide`. Non-vacuity:
* the echo protocol satisfies `RespectsNE` and `IsRBroadcast` for `n ≤ 2`;
* the relay protocol is unforging and satisfies `IsRBroadcast` under non-equivocation plus
  signatures;
* the translation accepts the honest messages of the trace (`TReach` steps `c₀ → c₁`).

The Section 3 model comes from CSLib
(`Cslib.Computability.Distributed.Byzantine.PartialSync.{Model,Auth,RunClasses}`, partition lemma
`Fintype.exists_fin_labelling_le`).
