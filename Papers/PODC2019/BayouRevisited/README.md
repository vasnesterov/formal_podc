# Bayou Revisited / Acute Cloud Types — PODC 2019

Maciej Kokociński, Tadeusz Kobus, Paweł T. Wojciechowski. *On Mixing Eventual and Strong
Consistency: Bayou Revisited.* PODC 2019. DOI
[10.1145/3293611.3331583](https://doi.org/10.1145/3293611.3331583). Formalized version: the full
version *On Mixing Eventual and Strong Consistency: Acute Cloud Types*, arXiv
[1905.11762](https://arxiv.org/abs/1905.11762) v2 (Jan 2021); numbering follows it.

**Verdict: 🛠️ Proof repaired.** The headline impossibility result (Theorem 5) and Corollary 1 hold as
stated, for every number `n ≥ 2` of replicas. The proof needs two repairs. As written it applies the
strong-consistency guarantee to a run that is not stable. It also overlooks that a weak read's response
may depend on the replica's local clock. Theorems 1–4 (correctness of ANNC and AcuteBayou) were not
formalized.

## Mistakes in the paper

* **Theorem 5's proof uses a stronger hypothesis than the theorem states (proof gap; statement
  true).** The theorem assumes `SinOrd(strong) ∧ BEC(strong, F)` only in *stable* runs. The proof
  starts with "consider an implementation that satisfies … `BEC(weak) ∧ SinOrd(strong) ∧
  BEC(strong)` in both the asynchronous and stable runs" and needs it. In the final execution `H`,
  the messages that `R1` `TOB-cast` for its weak `append(a)` (`msgs_a^TOB`) are never
  `TOB-delivered`. Only `R2`'s outstanding messages are delivered after the partition heals. Hence
  `H` is not a stable run whenever `msgs_a^TOB ≠ ∅`, and the stable-run hypothesis does not apply
  to it. Repair: at the end, `TOB-deliver` everything at every replica, `R2`'s messages first and
  then `R1`'s. This keeps one total order, adds no new messages (after a replica becomes passive,
  op-driven messages forbid new casts), and makes `H` a fair stable run. (`main_contra`, `CH_stable`)
* **The indistinguishability steps ignore local clocks (proof gap; statement true).** The paper's
  replicas read a monotone local clock (Section 3.2.1), and invisible reads only fix the *state*
  after a weak read. So a weak read's response may depend on the clock, and "each read returns the
  same response as `e'_c`" (Claim 1) and "`rval(e_r) = v`" (main execution) do not follow from
  determinism. Repair: let the reads in `H'` continue and pick a *late* read of `R1` (or of `R2`, by
  symmetry) that sees both appends. Its value is fixed by the arbitration order. Then `H` replays
  `R1`'s local input sequence up to that read, including the earlier reads, so the clock values
  coincide. (`claim1`, `rvalOf_weak`)
* **Op-driven messages (restriction 3) contradicts the proof and AcuteBayou (imprecise
  definition).** As written, only "not read-only" operations may cause `RB/TOB-cast`s. Then a
  strong read could never synchronize. Yet the proof of Theorem 5 says strong reads "can cause `R2`
  to `RB-cast` and `TOB-cast` messages", and AcuteBayou `TOB-casts` strong read-only operations
  (Appendix A.5). We exempt only *weak* read-only operations. This allows more implementations and
  so strengthens Theorem 5.
* **Typos.**
  * In `F_seq` (Figure 3), `rank(appends(E), ar, e) = i` for `i ≤ n` is off by one, because `rank`
    counts strict predecessors and is therefore `0`-based. Also `n` is never defined; it should be
    `|appends(E)|`. Read literally, `read` has no value on a nonempty context. We use rank `i − 1`
    for `i = 1..n`.
  * "show how it can be easily to a system with `n > 2` replicas" (a word is missing).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `n ≥ 2` replicas, each a deterministic state machine (`Impl`) with arbitrary states, messages and
  internal events. A step gets the replica id, the local clock (the number of the replica's
  previous steps) and the input: an invocation `(op, level)`, `RB-deliver(sender, m)`,
  `TOB-deliver(sender, m)`, or an internal event. Internal events are enabled depending on the
  state only. Steps output responses `(request id, value)` and `RB`/`TOB` casts.
* Asynchronous message passing with `RB` and `TOB` as primitives. Deliveries need a prior cast and
  no earlier delivery. `TOB` delivery sequences of all replicas are prefixes of one total order.
  Liveness: every `RB` message is delivered to everyone; in asynchronous runs a `TOB` message
  delivered anywhere is delivered everywhere; in stable runs every `TOB`-cast message is delivered
  everywhere.
* Runs (`IsAsyncRun`, `IsStableRun`) are infinite and crash-free. In them every replica invokes
  infinitely often, is passive infinitely often, and receives all messages. Every invocation is its
  own client session. These are fair runs of the paper's model, and restricting the class of runs
  only strengthens an impossibility result.
* ACT restrictions (`IsACT`), quantified over reachable configurations: (1) invisible reads, (2)
  input-driven processing (no infinite internal-only computation), (3) op-driven messages, as above.
  Restrictions (4) and (5) (highly available weak and non-blocking strong operations) are *not*
  assumed: `BEC` itself forces every weak and strong operation to return. So the result covers more
  implementations than the paper's.
* History of a run: the events are the invocation steps; `rb` is real time on the global sequence.
  Abstract executions, `BEC(l, F)`, `SinOrd(l)` (and `FEC`, `SEQ`, `LIN`) follow Sections 4–5 literally,
  with `rval = none` for `∇`. In stable runs one abstract execution must satisfy `BEC(weak) ∧
  SinOrd(strong) ∧ BEC(strong)`; this is how the proof uses the hypothesis.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 5 (as stated: some ACT specification admits no such implementation) | `Podc.BayouRevisited.theorem5` | `Main.lean` |
| Theorem 5 for `F_seq` over any alphabet with two letters, any `n ≥ 2` | `Podc.BayouRevisited.theorem5_seq` | `Main.lean` |
| Corollary 1 | `Podc.BayouRevisited.corollary1` | `Main.lean` |
| Claim 1 (run `H'`, repaired) | `Impl.claim1` | `Claim1.lean` |
| Claim 2 (run `H''`) | `Impl.claim2` | `Claim2.lean` |
| Final run `H` and the `ar`-cycle | `Impl.main_contra` | `Theorem5.lean` |
| `F_seq` (Figure 3); `read` is read-only | `Fseq`, `Fseq_read_readOnly` | `Fseq.lean` |
| Correctness predicates of Sections 4–5 | `AbsExec.BEC`, `AbsExec.SinOrd`, `AbsExec.FEC`, `AbsExec.LIN`, … | `Framework.lean` |

**Not formalized.** Theorems 1–4 (ANNC and AcuteBayou correctness), the relations between
consistency criteria (`FEC < BEC`, etc.), and the related-work discussion.

**Trust.** No `sorry`. `theorem5`, `corollary1` and `isACT_trivialImpl` use only the axioms
`propext`, `Classical.choice`, `Quot.sound`. Non-vacuity: `isACT_trivialImpl` shows that the
restrictions `IsACT` are satisfiable for every specification. The three runs of the proof are
constructed explicitly and proved to be fair asynchronous or stable runs (`Cp_async`, `C2_stable`,
`CH_stable`), so the hypotheses are never applied to an empty class of runs. Everything is
self-contained: Mathlib only, nothing from CSLib. CSLib candidates: the consistency-model framework
(`Framework.lean`) and infinite runs as limits of chains (`limRun`, `IsChain`, `Runs.lean`).
