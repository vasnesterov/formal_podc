# Differences between the formalization and the paper

Paper: V. R. Cadambe, Z. Wang, N. Lynch, *Information-Theoretic Lower Bounds on the Storage Cost of
Shared Memory Emulation*, PODC 2016 (arXiv:1605.06844v2). Numbering follows arXiv v2.

## Errors in the paper

1. **Theorems 4.1, 5.1, B.1 and Corollaries 4.2, 5.2, B.2 are false** for reliable FIFO channels,
   which is a legitimate reading of the paper's "point-to-point reliable, asynchronous channels".
   - *Counterexample.* The relay algorithm (`Relay.lean`) with quorum size `n − f`, `2f < n`:
     - The writer's write number `t` with value `v` sends `W t v` to all servers and waits for
       `n − f` acknowledgements `A t`.
     - A server receiving `W t v` sends `F t v` to the reader and `A t` to the writer. A server
       receiving `Q j` from the reader sends `D j` back. Servers never change their state.
     - The reader records the largest `t` received in an `F` message and its value. Read number
       `j` sends `Q j` to all servers, collects `n − f` answers `D j`, and returns the recorded
       value.
   - *What is proved.* The algorithm is atomic (`Relay.isAtomic`, via CSLib's SWSR reads-from
     criterion), regular (`Relay.isRegular`) and live with at most `f` server crashes and any
     client crashes (`Relay.isLive`). It has no gossip (`Relay.noGossip`), and its server state
     sets are singletons (`Relay.stateBound`). So every `log₂|S_i| = 0`. With `n = 5`, `f = 2`,
     `V = Fin 4` (`Refutation.lean`):
     - Theorem 4.1 claims `0 ≥ 2 + log₂3 − log₂3`.
     - Theorem 5.1 claims `0 ≥ 2 + log₂3 − 2log₂3 > 0`.
     - Theorem B.1 claims `0 ≥ 2`.
     - The corollaries claim `MaxStorage > 0`.

     All are refuted: `not_theorem41`, `not_corollary42`, `not_theorem51`, `not_corollary52`,
     `not_theoremB1`, `not_corollaryB2`.
   - *Where the proofs break.* Section 4.3.1 lets the readers and their channels perform no action
     during `α`, and Lemma 4.8(a) relies on it. This silently assumes that servers never send to the
     reader unless it asks. In the relay algorithm, the write cannot complete unless the
     server-to-reader channels accept the forwarded messages. These channels then carry the
     information about `(v₁, v₂)`, which the vector `S⃗` misses (Claim 4.9 fails). In Appendix B,
     "all the channels are empty" at `P^{(v)}` ignores the state of the (live) reader, which has
     already received the value.
   - *Model dependence.* FIFO is used: the reader must have received all `F` messages a server sent
     before its answer `D j`. Reliable FIFO is the standard channel of Lynch's I/O-automaton
     framework, which the paper's proofs use. We do not know a counterexample for non-FIFO
     channels. There the adversary could withhold the forwarded `F` messages during a valency read,
     so the bounds may well hold, though the written proofs do not handle these messages.
     The counterexample uses the single reader of the SWSR statements. Forwarding to every reader
     would handle any fixed finite reader set (not formalized), but not the "possibly infinite"
     set of read clients of Section 3. Multi-reader versions of the bounds are not refuted. In our
     model a step receives one message and may send several (CSLib `ChannelFailures`), so servers
     need no state at all. In the paper's I/O-automaton model each output is a separate action, so
     servers must hold pending outputs. This variant **is formalized**. `Stream.IOASends` says that
     a server step processing an input sends nothing and a spontaneous server step sends at most one
     message. The *streaming relay* (`Stream.lean`) satisfies it:
     - The writer streams value bits with stop-and-wait per server.
     - A server's state is pending bit × pending ack × pending answer × turn, 36 states. The turn
       makes the server's outputs fair.
     - The reader reassembles `B`-bit blocks and keeps one outstanding query per server.

     It is proved atomic (`Stream.isAtomic`, invariant in `StreamInv.lean` / `StreamSafe.lean`),
     live (`Stream.isLive`, `StreamLive.lean`) and gossip-free. With `n = 5`, `f = 2`,
     `V = Fin 16 → Bool` it refutes all six bounds restricted to such algorithms
     (`not_theorem41_ioa`, `not_corollary42_ioa`, `not_theorem51_ioa`, `not_corollary52_ioa`,
     `not_theoremB1_ioa`, `not_corollaryB2_ioa` in `RefutationIOA.lean`). The relevant inequalities are
     `65536·65535 > 3·36⁴`, `> 9·36⁵`, and `2¹⁶ > 36³`.

2. **Repaired Theorem 4.1 / Corollary 4.2 / Theorem B.1.** We add the hypothesis `ReaderQuiet`: in
   an execution in which the reader takes no step, no server has sent a message to the reader. It
   follows from the syntactic `RepliesOnly` (servers send to the reader only while processing a
   message from the reader; `readerQuiet_of_repliesOnly`). The proved statements:
   - `theorem41_count`: `|V|(|V|−1) ≤ (∏_{i∈𝒩}|S_i|) · ∑_{i∈𝒩}|S_i|` for every `𝒩` with at least
     `n − f` elements. This implies the paper's `∏ · (N−f) · max`.
   - `theorem41`: the logarithmic form, for `|𝒩| = n − f`, `f < n`.
   - `corollary42`: both bounds, for `1 ≤ f < n`.
   - `theoremB1_count`: `|V| ≤ ∏_{i∈𝒩}|S_i|`. It needs `NoGossip` in our proof, since the proof
     requires the server-to-server channels to be empty.

3. **Writer messages "delayed indefinitely" (Lemmas 4.4, 4.6, Definition 4.3).** The paper argues
   that the execution `β`, in which the writer's in-transit messages are never delivered, is
   indistinguishable from a fair execution in which the writer crashes "before sending or receiving
   the messages in its channels". But the messages were already sent. With channels reliable even
   from crashed senders, the liveness hypothesis does not cover `β`. Our model (CSLib
   `ChannelFailures`) requires delivery only between correct processes, so messages from a crashed
   process may be lost. This is the semantics the proof needs. Under it, the liveness hypothesis
   gives the finite read extensions used for valency (`exists_readExt`, via `exists_canon_ret`).

4. **Theorem 5.1's proof (gossip), additional gap; not formalized.** Definition 5.3 "delivers all
   the messages" of the server-to-server channels before the read. With gossip this process need
   not terminate. Also, at `R₂` a server `j ∉ {s, s'}` receives the messages that `s` and `s'` send
   during the delivery phase, and these differ from those in `β₁`. So `j`'s state at `R₂` is not the
   one at `R₁`, and the counting vector does not determine the reader-side configuration. The
   theorem is false anyway (item 1). We did not attempt a repaired version with gossip.

## Imprecise statements and minor slips

5. **`f ≥ 2` in Theorem 4.1 / Corollary 4.2 is unused.** The counting argument works for every `f`
   (`theorem41_count` has no assumption on `f`). Corollary 4.2's total-storage bound uses `f ≥ 1`,
   via `(f−1)·a ≥ (f−1)·c/(N−f+1)` (`corollary42` assumes `1 ≤ f`).
6. `N − f ≥ 1` (that is, `f < N`) is implicit in the statements (max over `𝒩`, `log(N−f)`). We
   assume `f < n` in `theorem41` / `corollary42`, and `𝒩` nonempty in `theorem41_count`.
7. Proof of Theorem 4.1, Case II: "the read operation in `γ` should return `v₂`" does not follow
   from 2-valency, which is existential. It follows from Lemma 4.5 (`v₂' ∈ {v₁, v₂}`) together with
   `Q₂` not being 1-valent, and the contradiction is that `Q₂` would be 1-valent. We use this
   argument.
8. The counting vector `S⃗ ∈ ∏ S_n × 𝒩 × ∪ S_n` is bounded by `∏|S_n| · (N−f) · max|S_n|` in the
   paper. The dependent pair (server index, state of that server) gives the sharper
   `∏|S_n| · ∑|S_n|`. Ours is stronger and implies the paper's.
9. Typos: in Definition 4.7 and Lemma 4.6, `i ∈ {0, 2, …, M−1}` should be `{0, 1, …, M−1}`;
   `P₁^{(v₁,v₁)}` should be `P₁^{(v₁,v₂)}` in Section 4.3.2; "Definition 6.8" in Theorem 5.1's
   Case (II) should be Definition 5.3.

## Modelling choices

10. **Model.** CSLib/Podc `Cslib.ChannelFailures`:
    - Deterministic event-driven processes. A step is an invocation, a spontaneous tick, or the
      reception of the head of a FIFO channel, and it may send any list of messages.
    - Crashes are not events: a crashed process takes finitely many steps.
    - Fairness: correct processes tick infinitely often, and channels between correct processes
      eventually deliver.

    The paper uses (possibly nondeterministic) I/O automata. Our positive theorems are proved for
    deterministic algorithms only. The counterexample is deterministic, so the refutations hold in
    any model that contains these algorithms.
11. **Clients.** Exactly one writer and one reader (`Node n`). The paper has a writer and possibly
    infinitely many readers, of which SWSR uses one. The SWSR environment (`EvOk`) restricts
    invocations to `write` at the writer and `read` at the reader.
12. **Regularity** (`Regular`). Every completed read `k` returns the value of write `m` (or the
    initial value for `m = 0`). Write `m` must not start after the read returns, and write `m + 1`
    must not complete before the read is invoked. This is Lamport's regularity in reads-from form.
    The counterexample is proved atomic (CSLib `IsLinearization`), which is stronger.
13. **Liveness** (`Live A f`). For every failure pattern without channel failures and with at most
    `f` servers allowed to crash (clients arbitrary), every fair execution of the SWSR environment
    is covered. In it, every operation invoked by a non-crashed process returns.
14. **Storage.** `StateBound A S`: in every reachable configuration, the state of server `i` lies in
    the finite set `S i`. Cost is `log₂|S i|`, with `maxStorage` the `iSup` over servers and
    `totalStorage` the sum. The paper's "the set of states of server `i`" is any such set.
15. **No gossip** (`NoGossip`). Server transitions never output messages to servers. Clients may
    in principle send to clients; the proof does not need to exclude it, because messages of the
    stopped writer are never delivered in valency executions.
16. **Valency** (`ReadExt C x`). From `C`, the reader invokes a read and only the reader and the
    servers of `𝒩` take steps, never receiving from the writer or from the other servers. The read
    returns `x`. This is Definition 4.3 with "delayed indefinitely" made explicit. The extension is
    finite, so the existential "execution that returns" is a finite execution.
17. The execution `α^{(v₁,v₂)}` is constructed with the canonical fair continuation (CSLib
    `canon`) under the failure pattern "reader and servers outside `𝒩` crashed". The paper's
    "take turns in a fair manner" is made precise this way (`exists_write`).
18. **Non-vacuity.** The hypotheses of the repaired theorems are shown satisfiable only for `n = 1`,
    `f = 0`: a single-server register (`Witness.lean`, `NonVacuity.lean`) that is atomic, live, has
    no gossip, satisfies `RepliesOnly` and has `|V|` server states. A finite-state witness with
    `f ≥ 1` (bounded-timestamp ABD) is not formalized.
