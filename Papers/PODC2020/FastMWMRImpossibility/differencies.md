# Differences between the formalization and the paper

Paper: Huang, Huang, Wei, *Fine-grained Analysis on Fast Implementations of Distributed Multi-writer
Atomic Registers*, PODC 2020 (arXiv 2001.07855v6, used for the numbering).

## Theorem 1 (W1R2 impossibility)

### Proof

1. **The "sieve" of §4 is replaced by a different construction.** §3 assumes that the first
   round-trip of a read does not affect the value returned by another read (§3.1, "for the ease
   of presentation"). This is used in §3.3 ("appending the read operation `R₂` should not change
   the return value of an existing read") although `R₁` is *not* finished when `R₂⁽¹⁾` runs: in
   `β'₀`, `R₂⁽¹⁾` reaches every server before `R₁⁽²⁾`. §4 tries to lift the assumption with the
   "crucial-info model". That model assumes that the only relevant information on a server is the
   order "12"/"21" of the two writes, and that a first round-trip can only flip it. Servers that
   are "affected" are then eliminated, and `Σ₂` is claimed to contain at least 3 servers. None of
   this follows for an arbitrary algorithm, whose servers may store anything. So §4 is not a
   proof.
   **Fix used here.** The first round-trip of `R₂` is *blind*: `r₂` sends it before learning
   anything, so its messages are fixed. We put `R₂⁽¹⁾` into chain `α` already: every execution
   of chain `α` contains `R₁⁽¹⁾`, then `R₂⁽¹⁾`, then `R₁⁽²⁾`, at every server. `R₁` then returns
   the same value in `α_k` and in `β_0(α_k)`, and no sieving is needed.
2. **Meaning of "skip" for `R₂⁽¹⁾` at the critical server.** The paper lets `R₂` skip `s_{i₁}`
   in both round-trips without saying whether the request or the reply is delayed. For the fix
   above, `R₂⁽¹⁾`'s *request* is delivered to `s_{i₁}`, so `R₁⁽²⁾` sees the same log as in `α`.
   Only the *reply* of `s_{i₁}` to `r₂` is delayed until after the end of the execution. In round
   two, `R₂⁽²⁾`'s request to the skipped server is never delivered.
3. **Phase 3 (zigzag chain, §3.4) is formalized as in the paper** (`zigzag`): the horizontal link
   `β_k ≈ temp_k ≈ γ_k`, the diagonal link `β_{k+1} ≈ temp'_k ≈ γ'_k`, and `γ_k = γ'_k`. In our
   formalization `γ_k` and `γ'_k` are literally the same schedule, and the case `k + 1 = i₁` is
   trivial (`β_k = β_{k+1}`).
4. **Real time in chain `α`.** The paper's head `α₀` has `W₁` before `W₂` and the tail `W₂`
   before `W₁`, while the intermediate executions need concurrent writes (from `α₂` on, at least
   two servers see `W₂` first). We use concurrent writes for every element of the chains and two
   extra *sequential* executions (`ret_seq`), whose server logs equal those of `α₀` and `α_S`.
   This gives `F 0 = b` and `F n = a`.
5. **Atomicity facts** used by the paper are proved from linearizability (`Lin.lean`). When both
   writes return before both reads are invoked, every linearization makes both reads return the
   value of its last write. If moreover `W₁` precedes `W₂`, that value is `W₂`'s.

### Statement and model

6. **Model.** The paper's informal round-trip model (§2.2, and the "full-info model" of §4.1) is
   made precise as `W1R2Alg` + `W1R2Alg.protocol`. Communication is asynchronous, reliable and
   unordered (CSLib `Cslib.AsyncMP`). A server replies to every message immediately, by an
   arbitrary function of the messages it processed before (its log) and of the new message and
   its sender. Every deterministic server automaton has this form. A write sends one message to
   every server (contents arbitrary: functions of the writer's local state, the value and the
   server) and returns once it has `≥ n − t` replies. A read does this twice; the second-round
   messages and the return value are arbitrary functions of the replies received, *in arrival
   order*. Clients keep arbitrary local states between operations. The scheduler decides when a
   client with `≥ n − t` replies proceeds. Late replies of earlier round-trips are ignored.
   Crash steps exist in the CSLib model but are not needed: the counterexample executions are
   crash-free, and `t` enters only through the quorum size `n − t`.
7. **Generality of the statement.** The paper fixes `S ≥ 3`, `W = R = 2`, `t = 1` "w.l.o.g."
   (§3.1). `theorem_1` is stated directly for every number `n` of servers (including `n ≤ 2`),
   every `t ≥ 1`, all writer and reader sets with at least two elements, and every value type with
   at least two values. Writers only write and readers only read (as in §2.1).
8. **Atomicity** (Definition 2.1) is CSLib linearizability of the histories of all reachable
   configurations (`Protocol.Linearizable`). The induced protocol produces only well-formed
   histories, so restricting to well-formed executions changes nothing.
9. **Not formalized.** The extension to W1Rk, `k ≥ 3` (§2.2, end of §3 intro), stated without
   proof in the paper. The model fixes exactly two round-trips per read; a read that needs only
   one can send a dummy second round.

## Non-vacuity / sanity

10. The hypotheses of `theorem_1` are trivially satisfiable. To check that the model does not make
    linearizability impossible for a silly reason, `Sanity.lean` proves
    (`single_server_linearizable`) that with `t = 0` a single-server fast-write algorithm is
    linearizable in the same model (safety only; liveness not proved).

## Section 5 (W2R1)

11. **Algorithms 1–2 are not atomic** (`W2R1.w2r1_not_linearizable`). This refutes MWA2 /
    Lemma 5 and therefore the implementation claim of §5.2 ("W2R1 implementation when
    `R < S/t − 2`"). The model is concrete: `S = 4`, `t = 1`, `R = 1`, `W = 2`, register values
    in `ℕ` with initial value `0`, as a `Cslib.AsyncMP.Protocol`. Our readings of the pseudo-code:
    * Values are tagged `(ts, wid, v)` and compared by `(ts, wid)`.
    * A server's `valuevector` maps tagged values to `updated` lists. `update(val, c)` adds `c`,
      creating the entry if needed. This agrees with lines 8–15 whenever the paper's code is
      defined (line 14 on a missing entry is undefined in the paper).
    * The writer's `(read, maxTS)` query does not change server state and is answered with the
      timestamp of the current value. Recording the writer instead would not affect the
      execution: the queries happen before any write and only touch `(0, ⊥)`.
    * A READACK carries the server's whole `valuevector`.
    * `admissible` is implemented literally, over all subsets `μ` of the replies.
    * The read returns the largest admissible value; this is exactly what "remove `maxV` and
      repeat" computes.
    * Which values a read request records the reader with is a parameter `markCur`. With
      `false`, only the values of `valQueue` (literal line 20). With `true`, also the server's
      current value (the single-writer original). The counterexample holds for both. The literal
      reading is degenerate: it already fails with one writer (`w₁` writes `(1, w₁)` to
      `s₀, s₁, s₂` and returns; a first read hearing `s₀, s₂, s₃` sees `(1, w₁)` twice with
      `updated = {w₁}` and returns `0`). That single-writer trace is not a separate Lean theorem;
      the two-writer counterexample is what refutes the `markCur = true` reading.
12. A third reading (record the reader with every stored value) is refuted only by model checking
    (`scripts/scenario_late.py`, trace `scripts/cex_D2_late.txt`: `S = 5`, `t = 1`, `R = 2`, one
    writer, late read requests). Adding per-reader read counters, which are absent from the
    pseudo-code, avoids all violations we found. That variant is neither proved nor refuted.
13. Lemmas 2, 6 and Corollary 1 fail on executions found by the model checker
    (`scripts/lemmas.py`). The Lean file does not formalize these lemma failures.
14. Not formalized: §5.1 (impossibility for `R ≥ S/t − 2`, by reduction to Dutta et al.).
