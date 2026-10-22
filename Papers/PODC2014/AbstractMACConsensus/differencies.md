# Differences between the formalization and the paper

Newport, *Consensus with an abstract MAC layer*, PODC 2014 (arXiv 1405.1382 v1; numbering as there).

## Model (`Podc/Computability/Distributed/AbstractMAC/Basic.lean`)

1. **Event-based model.** An execution is a sequence of blocks of events `recv u v` (v receives u's current
   message), `ack u`, `crash u`, `skip`; a disabled event is a no-op. The paper's guarantee "in the interval from
   `broadcast(m)` to the ack, every non-faulty neighbour receives `m`, and these are the only receive events for `m`"
   is the enabling condition of `ack u` (`got u` contains every neighbour) plus the fact that only the current message
   of `u` can be delivered, at most once per neighbour.
2. **Algorithms.** Deterministic: `init : I → Bool → S` (identity + input; `I = Unit` for anonymous algorithms, `I = ℕ`
   for unique ids), `recv`, `ack`, `bcast : S → Option M`, `out : S → Option Bool`. `bcast` is consulted only when the
   node is idle (initially, after its ack, or after a receive while idle); this models "messages broadcast before the
   ack are discarded". Local computation takes no time. Knowledge of `n`/`D` is implicit: the algorithm only has to
   work on the networks of the hypothesis.
3. **Nodes may be idle.** The paper assumes w.l.o.g. (Sections 3.1, 3.3) that nodes always broadcast. We do not need
   this: an idle node simply has no pending broadcast (its valid step is a no-op). Our impossibility results therefore
   cover all algorithms, without the (unproved) w.l.o.g. reduction.
4. **Decisions.** The irrevocable decide action is the first `some` value of `out`, recorded in `Node.dec`.
   Agreement compares all decisions ever made (including those of nodes that crash later), validity says every
   decision is some node's input, termination concerns nodes that never crash.
5. **Crashes.** A crashed node takes no further steps and its message is no longer delivered (also mid-broadcast).
   *Deliveries to a crashed node are kept as bookkeeping events that do not change its state, and acks wait for them.*
   In the paper acks need not wait for crashed neighbours; our executions are a subset of the paper's (drop the
   bookkeeping events), so "every algorithm has a bad execution in our model" implies the paper's statement.
6. **Time and `F_ack`.** `Timely σ T F`: configuration `i` exists at time `T i` (non-decreasing, `T 0 = 0`), and every
   broadcast is acknowledged — or its node crashes — at most `F` after it started. `SolvesConsensus A G id f` requires
   agreement, validity and termination in every timely execution (for any `F`) with **diverging time** and at most `f`
   crashes. The paper does not say whether time must diverge; requiring it only makes our impossibility results
   stronger. `Fair.exists_timely`: every fair execution (every broadcast eventually acked or crashed) is timely for
   `F = 2` with diverging time, so fair executions can be used as counterexamples.
7. The second timing parameter `F_prog` and unreliable links are omitted, as in the paper.

## Section 3.1 — Theorem 3.2, Lemma 3.1 (`ValidSteps.lean`, `FLP.lean`)

8. **Theorem 3.2 needs `n ≥ 2`** (not stated). For `n = 1` the node decides its own input and consensus is solvable
   with any number of crashes (`theorem_3_2_card_one`). Degenerate case; we prove `theorem_3_2` for `n ≥ 2`.
9. **Valid steps.** The paper delivers to "the smallest non-crashed node that has not received the message yet". We
   deliver to an arbitrary but deterministic node chosen from `got u` (`Classical.choose`), including crashed nodes (see
   item 5). Any deterministic choice depending only on `got u` works.
10. **Valency.** The paper's definition ("every extension of valid steps that leads to a decision leads to the same
    decision") makes a fragment with no deciding extension vacuously both 0- and 1-valent, and leaves open whether
    extensions may contain crashes. We use crash-free extensions by valid steps (`Val`, `Biv`); every reachable
    configuration has a possible decision (`exists_val`, from termination of a round-robin execution), and a
    configuration in which someone decided `b` cannot reach `!b` (`not_val_of_dec`).
11. **Lemma 3.1's case analysis.** Case 1 ("extend β₁ so that every node except w keeps taking valid steps … equivalent
    to a fair execution where w crashes") silently mixes a crash execution with valency defined by valid
    (crash-free) extensions. We make the transfer explicit: crash `w`, run the others fairly, get a decision by
    termination (`exists_decision_off`), and transfer it to the crash-free extension in which `w` is silent; both runs
    perform the same events and agree off `w` (`Rel`, `Rel.runV`) — this is where item 5 is used. Both of the paper's
    cases are handled at once by `stepV_comm` (the two orders agree off one node).
12. **Lemma 3.1's choice of `α*`.** The paper walks along the 1-valent extension until the fragment becomes 1-valent
    and argues the intermediate steps are not `s_u`; we take the first prefix where the valency of `α·s_u` changes
    (`Nat.find`), which also handles steps of `u` itself and idle nodes.
13. **FLP's Lemma 2 (bivalent initial configuration)** is cited by the paper; we prove it in this model
    (`exists_bivalent_init`) with the same crash argument.
14. Theorem 3.2 is for the clique (`⊤`), any identities `id : V → I`, tolerance `f = 1`.

## Section 3.2 — Theorem 3.3, Claim 3.4, Lemmas 3.5, 3.6 (`Networks.lean`, `Anonymous.lean`)

15. **Claim 3.4 is false for `D = 4`.** With `d = (D−2)/2 = 1` the gadget's node `a₂⁺` is at distance 2 from `c`
    (via `a₁` or `a₃⁺`), so network A has diameter `6 ≠ 4`; moreover `a_{d−1} = a₀`, to which the padding nodes
    `a*_j` are attached, does not exist. For `D ≥ 6` the paper's networks do have size `n'` and diameter `D` (checked
    numerically for `d ≤ 6`, `k ≤ 2`, not formalized).
16. **Different gadget.** We prove Theorem 3.3 for every even `D ≥ 4` with our own gadget (core `c, t, s, r, u, p`,
    padding twins of `p`, and a path of length `d − 1` below `t`; B is a 3-fold voltage cover), found by a computer
    search; the clique `C` of network A is replaced by a star around `q` (only its size matters). The paper's
    construction is not formalized.
17. **Constant `c`.** The paper says "some constant `c`"; we prove `n' ≤ 8 n` (with `n' = 3 (n + d + 5)`, not the
    smallest possible).
18. **Synchronous scheduler.** The paper delivers "all nodes' current messages, then all acks" without fixing the order
    in which a node receives the messages of one round; order matters for a deterministic algorithm, and Lemma 3.6
    needs corresponding nodes to receive them in the same order. We deliver them sorted by a fixed (arbitrary) linear
    order on messages, so a round depends only on the multiset of received messages (`inbox`, `roundLoc`). Nodes that
    start broadcasting during a round (only possible for idle nodes) are delivered in the next round.
19. **Lemma 3.6** is the general simulation lemma `syncLoc_comp` for a map `p : B → A` that is a bijection from the
    neighbours of `v'` onto the non-held neighbours of `p v'` (the paper's property (*)); `q` is held for `t` rounds
    (its message is neither delivered nor acked; it does receive). **Lemma 3.5** is `sync_decided`.
20. Anonymous = `I = Unit`. The theorem quantifies over all networks (`Fintype` vertex type, connected, `diam = D`,
    `card = n'`).
21. **Corollary 3.7** (the standard asynchronous broadcast model) is not formalized (different model).

## Section 3.3 — Theorem 3.9, Lemma 3.8 (`UnknownSize.lean`)

22. **Lemma 3.8** is stated for all `d ≥ 1` with one uniform `t`; the hypothesis only concerns networks of diameter
    `D`, so nothing is known for `d ≠ D`. Only `d = D` is used, and we prove only that (`lemma_3_8`). Typo: "all nodes
    begin with initial value 0" should be `b`.
23. `K_D` exactly as in the paper (`KD`, `kd_diam`: diameter `D` for `D ≥ 2`). Identities: any injective `ℕ`-valued
    ids; the two copies of `L_D` used in Lemma 3.8 carry the ids of `L¹_D`, resp. `L²_D`. In the semi-synchronous
    execution the endpoint `e` of `L_{D−1}` is held for `t` rounds while everything else runs synchronously.

## Section 3.4 — Theorem 3.10 (`TimeLB.lean`)

24. "No algorithm can guarantee to solve consensus in less than `⌊D/2⌋ F_ack` time" is formalized as: for every
    algorithm solving consensus on the line of `D + 1` nodes and every `F > 0` there is a timely crash-free execution
    (bound `F`, diverging time) in which some node has not decided before time `⌊D/2⌋ F`. The bound holds even for
    algorithms that only need to work on this single network (ids, `n`, `D` known). The paper's proof sketch (time
    `F` per synchronous step, partition at the middle) is made precise with `syncLoc_congr_of_walk`.

## Section 4 — upper bounds

25. **Theorem 4.1 is false for Algorithm 1 as written (pseudocode slip; the prose's rule is correct).** Line 23 looks for `⟨phase 2, *, decided(0)⟩` in `R2`
    only, but a phase-2 message received during phase 1 is stored in `R1` (line 6), and line 20 then does not wait
    for it again. Counterexample with two nodes (`twoPhaseLit_not_solvesConsensus`, schedule `cexSched`, timely with
    `F = 8`): `u` (id 0, input 0) completes phase 1 before hearing `x` (id 1, input 1) and becomes `decided(0)`; `x`,
    still in phase 1, receives `⟨p2, 0, decided(0)⟩` into `R1` and becomes bivalent; `u` decides 0; `x`'s witnesses
    are already covered by `R1 ∪ R2`, its `R2 = {⟨p2, 1, bivalent⟩}`, so it decides 1. The paper's proof ("it will
    therefore see that `u` has a status of decided(0)") assumes the check sees `R1` too. **Repair:** look in
    `R1 ∪ R2` (`TwoPhase.decRule`), which matches the prose ("if the set contains any message of the form decided"), line 20 (`R1 ∪ R2`) and
    line 8 (which already expects phase-2 messages in `R1`), so the intent is evident;
    the repaired algorithm solves consensus (`theorem_4_1`) and every node decides by time `2 F_ack`
    (`theorem_4_1_time`, the paper's "small constant (i.e., 2)").
26. Theorem 4.1 details: the state adds a program counter (phases 1–4) to the pseudocode's variables; after deciding
    a node ignores messages; in the loop of line 20 phase-1 messages are dropped (line 21); a node with status
    `decided` also goes through lines 19–27 (pseudocode), not "decide and terminate" (prose) — both decide the same
    value. Unique ids (`id` injective) are assumed for correctness (not for the time bound); no crashes (`f = 0`);
    single hop (`⊤`); no knowledge of `n`.
27. **wPAXOS (Lemmas 4.2–4.5, Theorem 4.6)** is not formalized.
