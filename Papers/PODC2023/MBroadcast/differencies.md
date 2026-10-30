# Differences between the formalization and the paper

Paper: Déprés, Mostéfaoui, Perrin, Raynal, *Brief Announcement: The MBroadcast Abstraction*, PODC 2023. For the
converse direction (MBroadcast from registers) the brief announcement gives no algorithm; we use Algorithm 2 and
App. A.1 of the extended version (DISC 2023). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

**Verdict call (borderline ✅ vs ⚠️, item 1).** The literal reading of the abstract's paraphrase of mutual ordering
makes Property 1 and Theorem 2 false. The main-text definition, read with the paper's own convention for "deliver
m′ before m" (FIFO and causal properties, Property 1), is the strong reading, under which every checked statement
holds. The definition is not a result claim and the intended meaning is fixed by the paper itself. So we grade ✅
and report the imprecision; a stricter grader could apply R3 and give ⚠️.

## Definitions (Section 3, `Spec.lean`)

1. **Mutual ordering: reading of "before".** The paper (main text): "it is not possible that p mdelivers m
   before m′ and p′ mdelivers m′ before m"; abstract/introduction: "it is not possible for p to deliver first
   (its message) m and then m′ while p′ delivers first m′ and then m". We formalize the reading used by the
   paper's own FIFO/causal definitions and by Property 1: "when p mdelivers m, it has not (yet, or ever)
   mdelivered m′" (`DelivBefore`). The literal reading of the abstract ("p mdelivers both, m first",
   `WeakMutualOrdering`) is strictly weaker, and with it Property 1 and Theorem 2 are false
   (`property1_false_weak`, `alg3_weak_not_linearizable`). Rule R3 (intent recoverable: Property 1, Fig. 1, the
   "p′ does not ignore p" remark of the introduction and the paper's usage of "deliver m′ before m" in the FIFO
   and causal properties all force the strong reading; local fix of one phrase). Borderline between ✅ and ⚠️:
   see README.
2. **Pairs with p = p′.** "For any pair of processes p and p′" — we quantify over all `(p, m) ≠ (p′, m′)`;
   the case `p = p′` holds automatically (`not_delivBefore_same`).
3. **All mbroadcast messages are different** (the paper's WLOG assumption). Messages are identified by
   (sender, message); `UniqueBc` = each pair is mbroadcast at most once. In Algorithm 3 messages carry the index
   of the sender's operation, which makes them distinct by construction (reads may otherwise rebroadcast the
   same `write(v, c)` twice).
4. **Liveness properties** (Local termination, Global CS-/CF-termination) are stated in each model file for
   its notion of correct process.
5. **FIFO / causal ordering** are formalized with the same reading of "before" (`FifoOrdering`,
   `CausalOrdering`); causal ordering is the paper's one-step version (transitivity follows).

## Algorithm 3 / Theorem 2 (`Register*.lean`)

6. **Model of `CAMP_{n,t}[MB-broadcast]`.** The MBroadcast layer is modelled by its specification: deliveries
   are unconstrained steps, and the safety theorem assumes the final MBroadcast trace is safe (prefix-closed, so
   every intermediate trace is). Liveness of the layer (Global CS-termination) is a hypothesis of the
   termination theorem. This quantifies over every implementation of MBroadcast, as the paper intends.
7. **Atomicity convention.** Each block between two `wait`s is atomic: line 1 (`invW`), lines 2–3 (`line2`),
   line 4 (`invR`), lines 5–6 (`line5`), returns, and the handler of line 8 atomically with the mdelivery. The end
   of a `wait` is a separate step (other deliveries may interleave), which is the general case.
   The convention matters for lines 5–6: `valᵢ` (line 5) and `clockᵢ` (line 6) must be read with no handler of
   line 8 in between, otherwise a read could mbroadcast a mismatched pair `write(v_old, c_new)`. This is the
   usual convention of the authors' pseudocode (handlers do not interrupt local code), not an error.
8. **Line 2** "let tᵢ such that ⟨tᵢ, i⟩ > clockᵢ": any such date is allowed (nondeterministic `d`).
9. **Timestamps** `WithBot (Lex (ℕ × P))`, `⊥` for the initial value `v₀` (the paper writes ⟨0, 0⟩); process
   identities form any linear order.
10. **Only validity and mutual ordering are used** for linearizability (`alg3_linearizable_of_validity_mutualOrdering`);
    no-duplication is not needed. No assumption on the number of crashes (paper's "Important remark").
11. **Termination** is proved for weakly fair executions (a continuously enabled end-of-wait step of a correct
    process is eventually taken) with Global CS-termination of the layer; only "a correct process eventually
    mdelivers its own messages" is used. Stated with the operation counter `k` (= number of responses,
    `Inv.resps`). No fair execution with a pending operation is constructed in Lean for this model (as for
    Algorithm 2 of the brief announcement, item 18). The hypotheses are evidently satisfiable, e.g. by a
    round-robin scheduler where every message is mdelivered to all processes right after it is mbroadcast.
12. **Proof of Theorem 2** (full version, App. A.2) is by a cycle-freeness argument on a relation →; we use the
    equivalent timestamp criterion (`TSLin`, writes ordered by timestamp, reads after the write they read from).
    The key step "→₁ implies ts(o₁) ≤ ts(o₂)" is Property 1 applied to the last message of o₁ and the `synch` of
    o₂ (`Inv.tok_le_clock`). No gap.

## Algorithm 2 of the brief announcement / Theorem 1 (`Causal*.lean`)

13. **Network model.** Reliable, unordered channels with causal delivery for `causal_broadcast` and `causal_send`
    together: a message is received only after every causally preceding message with the same destination
    (`CausalReady`, ghost causal past `dep`). This matches the paper's definition (one causal order, relations
    (i)–(iii)); the proof needs it (`ack(m′)` sent after receiving `init(m)` must arrive after `init(m)`).
14. **Self-delivery** of one's own `init(m)` is omitted (the handler does nothing for i = j, line 4).
15. **Atomic broadcast, no loss.** A causal broadcast is one atomic step and sent messages are never lost (also
    for crashed senders). For safety this covers the paper's crash in the middle of a broadcast (finite prefixes);
    for liveness, weak fairness makes every message to a correct process whose causal predecessors were received
    eventually received. The proofs use this only for messages in the causal past of a correct process's send,
    which a piggybacking causal-delivery layer provides.
16. **Threshold** `n − t − 1` acks (natural subtraction); safety needs only `2t < n`, for any number of actual
    crashes; validity and no-duplication need no bound. Liveness needs at most `t` crashes (no `2t < n`).
17. **Distinct messages** per sender (`invoke p m` enabled only if `p` never mbroadcast `m`); a process invokes
    `mbroadcast` only when idle.
18. **No proof in the brief announcement** ("proofs in the full version"; the HAL report was not accessible, and
    the DISC version cites the brief announcement for this algorithm). Our proof: quorum intersection of the two
    ack sets plus own processes, and a case analysis on the common process (other, p, or p′) using causal
    delivery. The existence of fair executions is not proved for this model (it is for the register model).

## MBroadcast from registers (`FromRegisters*.lean`)

19. **Atomic** SWMR registers (the brief announcement's claim). The full version claims the algorithm works with
    regular registers; not checked.
20. **Atomicity.** One step per register access: a read of `SENT[j]` together with the local lines 6–7; the
    invocation together with the write of line 1, enabled only when no `catch_up` runs (the routine is
    uninterruptible and the invocation has no effect before line 1).
21. **Fairness:** every correct process takes infinitely many local steps (its local step is always enabled); a
    round-robin fair execution exists (`exampleExec_delivers`).
22. **Properties proved:** unique broadcasts, Validity, No-duplication, Mutual ordering, FIFO, Local termination,
    Global CF- and CS-termination, for any number of crashes (the full version's "reliable-MBroadcast").
23. **Not causal.** The algorithm does not ensure causal ordering (`not_causalOrdering`, 3 processes); the paper
    does not claim it. The brief announcement's statement that the enriched variants (fifo-, causal-,
    reliable-MBroadcast) "do not change its computing power" is supported for the causal variant by an algorithm
    of ours (`FromRegisters.Causal.*`): each register entry carries the sender's delivery history, which a
    reader mdelivers first, stopping at its own pending message. Without that stop, mutual ordering fails: p
    could mdeliver its own pending m, found in another process's history, before reading SENT[p′].
24. **Same computability power** is not stated as a single simulation theorem; it is the conjunction of
    Theorem 2 and the register construction (both for any number of crashes).

## Not formalized

25. Message complexity ("O(n) implementation messages"); the remarks identifying reliable broadcast and causal
    broadcast with variants of MBroadcast (definitional).
