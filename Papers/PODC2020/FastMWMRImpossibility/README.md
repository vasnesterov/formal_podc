# Fast-write MWMR impossibility — PODC 2020

Kaile Huang, Yu Huang, Hengfeng Wei. *Fine-grained Analysis on Fast Implementations of Distributed
Multi-writer Atomic Registers.* PODC 2020. DOI
[10.1145/3382734.3405698](https://doi.org/10.1145/3382734.3405698). Formalized version: arXiv
[2001.07855](https://arxiv.org/abs/2001.07855) v6; numbering follows it.

**Verdict: ❌ False claim.** The fast-read (W2R1) algorithm of §5.2 / Appendix A is **not
atomic**. With `S = 4`, `t = 1`, one reader (so `R < S/t − 2` holds) and two writers, a read that
starts after `write(1)` has returned can return the initial value. So the sufficiency half of the
claimed tight condition for W2R1 is not established. The main result, Theorem 1 (no multi-writer
atomic register with one-round-trip writes and two-round-trip reads, for `t ≥ 1`, `W ≥ 2`, `R ≥ 2`),
is **true**; we prove it for every algorithm in the paper's round-trip model. Its proof has a real
gap: §4, which handles reads whose first round-trip changes server state, is not a proof. We close
the gap with a simpler construction that needs no sieving.

## Mistakes in the paper

* **The W2R1 algorithm (Algorithms 1–2) is not atomic; MWA2 / Lemma 5 is false.** Take `S = 4`,
  `t = 1`, `R = 1`, `W = 2`, initial value `0`.
  1. Both writers query and see timestamp 0, so `w₁` writes `(1, w₁)` (value 1) and `w₂` writes
     `(1, w₂)` (value 2).
  2. `(1, w₁)` reaches `s₀, s₁, s₂` and `write(1)` returns.
  3. Then the read starts, and `(1, w₂)` reaches `s₀, s₁`.
  4. The read hears from `s₀, s₂, s₃`.
     * `(1, w₂)` occurs in only one reply, so it is not admissible.
     * `(1, w₁)` occurs at `s₀` and `s₂`, but at `s₀` its `updated` set is just `{w₁}`. The
       server's current value there is `(1, w₂)`, so the reader is never recorded with `(1, w₁)`.
       The intersection is `{w₁}`, and degree 2 fails.
     * The read returns `0` although `write(1)` completed before it started.

  Lemma 5 claims that `(k, wᵢ)` is "admissible with degree 2" because the read sees it at
  `S − 2t` servers. It forgets that the `updated` sets must also contain the reader. In the
  single-writer algorithm this holds because the writer's value is always the current one. With
  several writers a concurrent larger value hides it. The counterexample holds both for the
  literal line 20 (record the reader only for the values in its `valQueue`) and for the
  single-writer-style reading (also record it with the server's current value). The second
  reading is the one that matters: under the literal one the algorithm already fails with a single
  writer, because a first read is never recorded with a new value, so a completed `write(1)` seen
  at only `S − 2t = 2` of the read's servers is never admissible. (`W2R1.w2r1_not_linearizable`)

  *Scope and further evidence (model checking, not in Lean).* A third reading records the reader
  with *every* value the server holds. It defeats this execution, but it fails too, with
  `S = 5`, `t = 1`, `R = 2` and a single writer. There a late (stale) read request records `r₂`
  with a value `r₂` never saw, so `r₁` returns the new value and a later read of `r₂` returns the
  old one (new–old inversion; Lemma 8's case (ii) is wrong). Only that reading *plus* per-reader
  read counters, which are in the single-writer original but not in the paper's pseudo-code,
  survived our exhaustive search at `S = 4` (and a non-exhaustive one at `S = 5, R = 2`). Even on
  correct runs, Lemma 2, Lemma 6 and Corollary 1 are false, so the proof of MWA3 (Lemma 7) does
  not stand either. Whether some repaired W2R1 algorithm exists for all `R < S/t − 2` is open
  here. Scripts and traces: [scripts/](scripts/).
* **§4 ("sieve-based construction", crucial-info model) does not prove what §3 needs.** The chain
  argument of §3 assumes that the first round-trip `R₂⁽¹⁾` of the second read does not change the
  value returned by the first read `R₁`. §3.3 uses this when it claims that `R₁` returns the same
  value in `β'₀` as in `α_{i₁−1}` ("appending `R₂` should not change the return value of an
  existing read"). But in `β'₀`, `R₂⁽¹⁾` reaches every server before `R₁⁽²⁾`, so `R₁` has not
  finished. §4 then argues in a "crucial-info model": a server only holds the order "12"/"21" of
  the two writes, and a first round-trip can only flip it. The "affected" servers are sieved out,
  and at least 3 servers are said to remain. A general algorithm's servers can store arbitrary
  information, so none of these steps follows. The statement is nevertheless true. **Fix:** the
  first round-trip of `R₂` is *blind*: it is `r₂`'s first action, so its messages are fixed.
  Include `R₂⁽¹⁾` (between `R₁⁽¹⁾` and `R₁⁽²⁾`) in every execution of chain `α`. In chains `β`,
  `γ` let `r₂` ignore the *reply* of the critical server in round one, while its *request* is
  still delivered. Then `R₁` behaves exactly as in chain `α`, and the zigzag chain of §3.4 goes
  through unchanged. This is a proof gap with a true statement. (`theorem_1`, `zigzag`)
* **Imprecise "skip".** "One round-trip skips server `s`" (§3.1) does not say whether the
  request or the reply is delayed. The argument needs the reply variant for `R₂⁽¹⁾` (see above).
* **Chain `α` and real time.** `α₀` is "W₁ precedes W₂" and `α_S` is "W₂ precedes W₁". From `α₂`
  on, the writes must be concurrent (two servers see `W₂` first, yet `W₁` waits for `S − 1`
  acknowledgements). Harmless: the end values come from sequential executions with the same server
  logs (`ret_seq`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous, reliable, unordered message passing between clients and `n` servers (`Fin n`),
  as CSLib `Cslib.AsyncMP.Protocol`. Servers do not talk to each other. Up to `t` servers may
  crash, so a client proceeds once it has `n − t` replies of the current round-trip. The
  scheduler chooses when, possibly after more replies arrived. Our counterexample executions are
  crash-free; `t` only matters through the quorum size.
* **All W1R2 algorithms** (`W1R2Alg`). A server replies immediately, by an arbitrary function of
  its log (all messages it processed, with senders), the sender and the message. This covers
  every deterministic server and is the paper's full-info model (§4.1).
  * A write sends one arbitrary message per server (a function of the writer's state, the value
    and the server) and returns after `n − t` replies.
  * A read does two such round-trips. Its round-two messages and its result are arbitrary
    functions of the replies, which are seen *in arrival order*.
  * Clients have arbitrary local states between operations.
  * Writers only write and readers only read.
* Atomicity is CSLib linearizability of every reachable history (`Protocol.Linearizable`) for
  `register V v₀`.
* Deterministic algorithms (as in the paper).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (W1R2 impossibility; any `n`, `t ≥ 1`, `W ≥ 2`, `R ≥ 2`, `|V| ≥ 2`) | `Podc.FastMWMR.theorem_1` | `Theorem1.lean` |
| §3.2–3.3 chains `α`, `β` (executions) | `W1R2Alg.reach_writes_conc`, `W1R2Alg.reach_write_solo`, `W1R2Alg.reach_reads` | `Executions.lean` |
| §3.4 zigzag chain (horizontal + diagonal links) | `W1R2Alg.zigzag` | `Theorem1.lean` |
| Indistinguishability for `R₁` / `R₂` | `W1R2Alg.ret₁_congr`, `W1R2Alg.ret₂_congr`, `W1R2Alg.ret₂_congr_log` | `Theorem1.lean` |
| "Both reads return the same value" / "the later write wins" (Def. 2.1) | `W1R2Alg.ret_agree`, `W1R2Alg.ret_seq` (from `resp_eq_linState`, `linState_eq_of_last_write`) | `Theorem1.lean`, `Lin.lean` |
| Round-trip model | `W1R2Alg`, `W1R2Alg.protocol` | `Model.lean` |
| §5.2 / App. A: Algorithms 1–2 atomic for `R < S/t − 2` — **false** | `Podc.FastMWMR.W2R1.w2r1_not_linearizable` | `W2R1.lean` |
| Sanity: `t ≥ 1` is needed (one server, `t = 0`: a fast-write algorithm is linearizable) | `Podc.FastMWMR.single_server_linearizable` | `Sanity.lean` |

Building blocks: `Steps.lean` (single steps, waves of requests, collecting replies, with frame
multisets).

**Not formalized.** The W2R1 impossibility for `R ≥ S/t − 2` (§5.1, a reduction to Dutta et al.)
and the W1Rk extension (`k ≥ 3`), which the paper only mentions. For the W2R1 algorithm we give
only the counterexample: `W2R1.lean` models Algorithms 1–2 concretely (`S = 4`, `t = 1`, `R = 1`,
`W = 2`) as a `Cslib.AsyncMP.Protocol` and checks the execution by `decide`. The other readings
were explored only by the model checker in `scripts/`.

**Trust.** No `sorry`. `theorem_1` uses only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity of the model: `single_server_linearizable` proves a fast-write algorithm
linearizable in the same model when `t = 0` (one server), so the impossibility really comes from
`t ≥ 1` and not from a degenerate model. The model is CSLib's `Cslib.AsyncMP` (asynchronous crash-prone message passing) with
CSLib linearizability (`Cslib.SharedMemory.IsLinearization`).
