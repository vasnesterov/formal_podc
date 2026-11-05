# No Broadcast Abstraction for k-Set Agreement — PODC 2024

Sylvain Gay, Achour Mostéfaoui, Matthieu Perrin. *Brief Announcement: No Broadcast Abstraction Characterizes
k-Set-Agreement in Message-Passing Systems.* PODC 2024. DOI
[10.1145/3662158.3662818](https://doi.org/10.1145/3662158.3662818). Formalized version: the extended version
(HAL hal-04571653v1, May 2024), which contains the proofs the brief announcement omits; numbering follows it. The
OPODIS 2024 version (hal-05521071, "No *Symmetric* Broadcast Abstraction …") has the same Lemma 9 (its Lemma 15)
with the same proof.

**Verdict: ❌ False claim.** Lemma 9 is false: a content-neutral, compositional broadcast abstraction on top of
which k-set agreement is solvable can still admit `N`-solo executions for every `N`. The headline Theorem 1 is
true as far as we checked, but the paper's proof rests on Lemma 9. We prove Theorem 1 with a repaired adversary,
which does not even need content-neutrality, for k-SA algorithms that communicate only through the broadcast
abstraction (the paper also lets them use point-to-point channels).

## Mistakes in the paper

### ❌ Lemma 9 (a k-SA-solving abstraction has no `N`-solo execution)
Lemma 9 fails for every `k`: "k-Bounded-Order broadcast restricted to *chained* messages" is content-neutral and
compositional, an algorithm solves k-set agreement on top of it with `k + 1` processes, and yet it admits an
`N`-solo execution for every `N` (`lemma9_false`).

**Impact.** The paper's proof of Theorem 1 is Lemma 9 plus Lemma 10, so the main result is not established by
the paper. Theorem 1 itself is true; see the repaired proof below.

**Details.** A message is *chained* if its sender had already delivered one of its own messages when it invoked
`broadcast` for it. The abstraction (`chainedBO`) requires that among any `k + 1` distinct chained messages, two
are delivered in the same order by every process.
- It contains every uniform total-order execution (`totalOrder_mem`), so it is implementable from consensus.
- The algorithm (`algQ`) works as follows. Broadcast a dummy message. Once it has returned and been delivered
  locally, broadcast the proposal; this message is chained. Decide the value of the first value message delivered.
- If `k + 1` distinct values were decided, the first-delivered value messages of the deciders would be `k + 1`
  chained messages from distinct senders. Two of them would be delivered in the same order by everybody, but each
  decider delivered its own decided message before the other one (`algQ_solves`, `algQ_wellFormed`; admissible
  executions exist: `soloRun_admissible`).
- The `N`-solo execution: every process invokes its `N` broadcasts (each returns at once), then delivers its own
  `N` messages, then everybody else's. No message is chained, so the ordering property is void (`soloExec_mem`,
  `soloExec_nSolo`).

The proof breaks at "αᵢ is indistinguishable from δ, as both executions involve identical B-broadcast and
B-delivery steps for pᵢ". Definition 5 constrains only the order of *deliveries*. Restricting and renaming an
`N`-solo execution cannot change when `pᵢ` *invokes* its broadcasts relative to its returns and deliveries, so
the local view of `pᵢ` in δ need not be its view in αᵢ. Two further steps of the proof are unjustified (they do
not matter for the counterexample):
- δ is finite, while running A' "on δ" needs an admissible continuation in which A' keeps acting, possibly
  broadcasting after it decided.
- "send and receive can be trivially emulated using B" overlooks that SR-Termination also holds for messages of
  crashed senders, while BC-Global-CS-Termination does not.

## Proof gaps (statements true)

### 🛠️ Theorem 1 (no content-neutral compositional abstraction is equivalent to k-SA)
The proof combines the false Lemma 9 with Lemma 10; we prove Theorem 1 with a different adversary
(`theorem1_paper`, `theorem1`).

**Impact.** Statement true; repaired. Our proof shows more: for `1 < k < n` no *compositional* broadcast abstraction
is equivalent to k-SA; content-neutrality is not needed. Caveat: in our Theorem 1 the k-SA algorithm A uses only the
broadcast abstraction. The paper's `CAMP_n[B]` also gives A point-to-point channels, so for such A the theorem is
not formalized (see [differencies.md](differencies.md), item 8).

**Details.** The paper runs the dummy loop `sync-broadcast(synch)` on top of B, then renames the `synch`
messages into A's messages. Lemma 9 shows that this does not reproduce A's local views. We keep the paper's
scheduler (Algorithm 1), but let the upper layer of each process run a *copy of A itself*. On top of B,
`pᵢ`'s copy invokes A's own messages at the times A wants. Its view is its own invocations, returns and
deliveries.

**Repair.** The execution `αS` (`Theorem1.lean`, names `p_1 … p_{k+1}` as in the paper):
1. Each `pᵢ`, `i < k`, runs alone until its copy decides. The k-SA objects answer its own proposals. A run alone
   is admissible (`solo_adm`), so B produces an execution of S. Restricted to the copy's messages, it is an
   execution of A on top of S in which `pᵢ` is the only participant. k-SA-Termination and k-SA-Validity of A
   then say that the copy decides, and decides `pᵢ`'s own proposal (`early_copy`, generic `fin_copy`).
2. `p_k` runs alone. A proposal to an object already decided by `p_1, …, p_{k-1}` (a *reset*) discards the
   current copy and starts a new one. There are finitely many resets: `p_1` decided finitely many objects, and
   proposals are one-shot. The copy started after the last reset decides `p_k`'s proposal (`kk_copy`).
3. `p_{k+1}` runs after `p_k`'s last reset. It first receives the messages `p_k` sent it before that reset. On
   objects decided by all of `p_1, …, p_k`, it adopts `p_k`'s value. Its copy decides its own proposal
   (`z_copy`, via the execution `gZ`).
4. In `αS` (`αS_adm`), `p_{k+1}` receives the other pending messages once its copy has decided. B produces an
   execution of S. By compositionality, its restriction to the messages of the final copies is an execution of A
   on top of S (`DS_adm`) in which `p_1, …, p_{k+1}` decide `k + 1` distinct values (`false_of`).

The paper's footnote 1 (SR-Termination is not proved for γ) is not a gap. Lemma 10 uses γ only as a prefix of an
admissible execution (BC-Validity), and Lemma 7 proves SR-Termination in the one case where it needs it. Our
counterparts of the γ executions (`solo`, `gZ`) are infinite admissible executions.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Broadcast abstractions* (`Spec.lean`). An execution of a broadcast abstraction is a time-indexed sequence of
  invocations, returns and deliveries, together with its set of correct processes. A broadcast abstraction is a set
  `S` of such executions. Each satisfies BC-Validity, BC-No-Duplication, BC-Local-Termination,
  BC-Global-CS-Termination, unique messages and well-formed invocations. Messages are objects `(id, content)`:
  algorithms choose contents, identities are fresh. Compositionality (Definition 2), content-neutrality
  (Definition 3, sender-wise injective renamings) and `N`-solo executions (Definition 5) follow the paper.
- *Algorithms on top of `S`* (`CAMP_n[S]`). A is deterministic: its next action (broadcast a content, decide, or
  wait) is a function of its proposal and local history. An execution is admissible if its broadcast events form an
  execution in `S`, A's steps follow A, correct processes take infinitely many steps of A, and faulty processes
  finitely many steps. A uses only the broadcast abstraction (like the paper's A'; this makes our Theorem 1 weaker
  than the paper's, whose A may also use channels), never invokes while an invocation is pending, and has at least
  `k + 1` possible proposals. k-SA: validity (a decided value was proposed by a participant), at most `k` decided
  values, termination of correct processes.
- *`CAMP_n[k-SA]`* (`Camp.lean`). Asynchronous processes; any number of crashes (faulty processes take finitely
  many steps, correct ones infinitely many). Channels are reliable and non-FIFO (SR-Validity, SR-No-Duplication,
  SR-Termination). There are any number of k-SA objects (validity, agreement, termination, one answer per
  proposal). B is deterministic and proposes at most once per object; the upper layer is arbitrary but
  well-formed. B implements `S` if the broadcast events of every admissible execution form an execution in `S`.
  The scheduler is adversarial; there is no randomness.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 2, 3, 5 | `Compositional`, `ContentNeutral`, `BExec.NSolo` | `Spec.lean` |
| Lemma 9 (false) | `lemma9_false` (statement `Lemma9`) | `Counterexample.lean` |
| the counterexample's abstraction and algorithm | `chainedBO_compositional`, `chainedBO_contentNeutral`, `algQ_solves`, `soloExec_nSolo`, `totalOrder_mem`, `soloRun_admissible` | `Counterexample.lean` |
| Theorem 1 | `theorem1_paper` (and the stronger `theorem1`) | `Theorem1.lean` |
| adversarial executions (role of Lemmas 1–8) | `catRun_adm`, `solo_adm`, `Ctx.gZ_adm`, `Ctx.αS_adm` | `Concat.lean`, `RunFacts.lean`, `Theorem1.lean` |
| restriction to the final copies (role of Lemma 9) | `derive_admissible`, `fin_copy` | `Derive.lean`, `Adversary.lean` |

**Not formalized.** The paper's Lemmas 1–8 and 10 for its own `sync-broadcast(synch)` adversary (we reprove their
content for the copy-of-A adversary). Neither is the remark "`CAMP_n[∅]` with `n − k − 1` initial crashes is
`CAMP_{k+1}[∅]`": we work with `n` processes directly, the extra ones never taking a step.

**Trust.** No `sorry`; `lemma9_false`, `theorem1`, `theorem1_paper` use only `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `algQ` has admissible executions on top of `chainedBO` (`soloRun_admissible`), and
`chainedBO` contains all uniform total-order executions. We do not exhibit an implementation `B` of some
abstraction in our `CAMP_n[k-SA]` model; no step of the proof of Theorem 1 relies on the hypotheses being vacuous.
Everything is paper-local (namespaces `Podc.NoBroadcastKSA`, `Podc.NoBroadcastKSA.Camp`).
