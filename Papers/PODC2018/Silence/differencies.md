# Differences between the formalization and the paper

Goren, Moses, *Silence*, PODC 2018 (arXiv 1805.07954v1, the only version).

## Model (§2.2)

1. **Runs as data.** A run is the triple (initial values, crash round of each process, set of processes
   reached in the crash round) (`Cslib.SyncCrash.Run`); the execution is computed from it with CSLib's
   lock-step semantics (`Cslib.Byzantine.LockStep.hist`) on the complete graph. Every execution of the
   paper's model `γ_f` arises in this way. Two data can describe the same execution (e.g. `reach` is
   irrelevant when nothing is sent); all facts we use (values, faultiness, chains, decisions) are
   functions of the execution, so knowledge of them is unaffected. *Modelling choice.*
2. **Local state** = (initial value, list of inboxes); the time is the length of the list, `⊥` is `none`.
   The paper also records the messages sent; for a deterministic protocol they are a function of the
   recorded data (and after a crash the state is `⊥` anyway), so indistinguishability is the same.
   *Modelling choice.*
3. **No self-messages.** The paper's protocols "send to all" / "send to `{i, …, i+f}`" including the
   sender, but count only messages to others. We have no self-messages (the complete `SimpleGraph` has
   no loops) and let protocols consult their own state instead; message counts agree with the paper's.
   *Modelling choice.*
4. **Decisions** are a function of the local state at time `m` (performed at the start of round `m+1`);
   crashed processes do not decide. A process may "decide" at several times; Agreement is required
   among all decision events of the run, so repeated decisions must agree. *Modelling choice.*
5. **Message counts** are `Set.encard` of the set of triples (sender, receiver, sending time), so runs
   with infinitely many messages are covered (`⊤`). *Modelling choice.*
6. `f` is arbitrary in the model; each theorem states the bounds on `f` and `n` it needs (the paper
   assumes `n > 2`, `1 ≤ f < n` throughout). Theorem 3(a) is false for `f = 0` (a protocol where
   processes with value `0` broadcast in round 1 and the others commit at time 1 uses no messages in the
   nice run), consistent with the paper's assumption `f ≥ 1`. *Not an error.*

## §3: silence

7. **Lemma 2 and Corollary 2 are false when `i` itself has crashed by time `m`.** "`i` does not receive a
   round-`m` message from `j`" is vacuously true for a crashed `i`, but then `i`'s state is `⊥` and it
   knows nothing. The proof step "`i` has the same local state at time `m` in both runs, and so it does
   not receive a message from `j` in round `m` of `r′`" fails for `⊥`. Counterexample
   (`corollary2_literal_false`): `n = 3`, `f = 1`, `S = {1, 2}`, `φ = (v₁ = 1 ∨ v₂ = 1)`; processes with
   value `0` send to process `0` in round 1; in the run where all values are `1` and process `0` crashes
   in round 1, process `0` gets nothing from `S` but does not know `φ` (nor `φ ∨ 1 is faulty`).
   We add the hypothesis "`i` is alive at time `m`" (`lemma2`, `corollary2`). Lemma 1 (`f = 0`) is
   unaffected (`lemma1`). *False only in a degenerate case.* (All uses of Lemma 2 / Corollary 2 in the
   paper are about non-crashed receivers.)
8. "`P` guarantees that if `¬K_j φ` at time `m − 1` then `j` sends a message to `i` in round `m`" is
   formalized as: in every admissible run where `j` is alive at time `m − 1` and `¬K_j φ`, the protocol
   *prescribes* a message to `i` (`Prescribes`); also `j ≠ i`. *Under-specified definition, natural
   reading.*

## Theorem 2 (Silent Choir)

9. **Construction of `r′` when a member of `S_j^r(m−1)` crashed early in `r`.** The paper lets every
   `h ∈ S_j^r(m − 1)` crash in round `k_h + 1` of `r′`. A process `h` that already crashed in `r` in a
   round `c ≤ k_h` can still be in `S_j^r(m − 1)` (messages sent to a crashed process count in message
   chains); then `h` would behave correctly in rounds `c, …, k_h` of `r′` but not in `r`, and the
   inductive claim fails. Fix: such an `h` keeps its crash from `r` (`choirRun`). *Proof gap, statement
   true.*
10. In the inductive step the paper says that `z` "receives no messages from a process `y ∈ S` for which
    `k_y < ℓ − 1`"; what is needed (and true) is `k_y ≤ ℓ − 1`. *Typo.*
11. The proof only uses that there is no message chain from `(j, 0)` to `(i, m)`; we prove this stronger
    version (`silent_choir_at`) and derive the paper's statement (`silent_choir`). It is used for the
    `D = 1` bound below. *Strengthening.*

## §4.1: lower bounds

12. **Lemma 3**: proved for every run (also with infinitely many messages) with a different argument
    (choose the process whose first message is sent last instead of a process of minimal rank) and the
    extra assumption `n ≥ 1` (for `n = 0` the bound `n + k − 1` is false; irrelevant here).
    *Proof variant.*
13. **Theorem 3(b)** is proved in the stronger form "no process decides before time 2 in the nice
    run" (`theorem3b`). Needs `2 ≤ f < n`. *Strengthening.*
14. **Theorem 3(c)**: in the last sentence of the proof, "a message chain from `j` to a correct process"
    should be "from `i`". We prove: if all processes decide by time 2, each sends messages to at least
    `f` processes in rounds 1–2 (`card_T2`), hence `M ≥ fn`. In our run `r′`, `i` crashes right after its
    decision time (`1` or `2`). *Typo.*
15. **Theorem 3(d)** is stated as: `f ≥ 2`, `M ≤ n + f − 1` and all processes decide by time `D` imply
    `D ≥ 3` (`theorem3d`). *Faithful.*
16. **The "complete characterization" claim is incomplete for `D = 1`.** The paper claims that the
    protocols of §4.2 make *all* bounds of Theorem 3 tight and "completely characterize the tradeoff".
    For `f = 1` and `D = 1` Theorem 3 only gives `M ≥ n`, while D1f1 uses `n² − n`. The missing lower bound `M ≥ n(n − 1)` for `D = 1` (any
    `f ≥ 1`) follows easily from the Silent Choir Theorem (a process deciding at time 1 must hear
    directly from everybody in round 1): `decide_time1_receives`, `theorem3_D1`. With it the
    characterization is indeed complete. *Incomplete claim, true after adding the bound.*
17. **Corollary 3** ("must make use of silence") is formalized as: in the nice run of an AC protocol with
    `M ≤ n + f − 1` and `f < n − 1`, some process commits although there is no message chain from some
    `j` to it (`corollary3`). *Formalization of an informal notion.*

## §4.2 and Appendices A–C: protocols

General (all three protocols are formalized as concrete history-based protocols on `Fin n` and verified
in **all** admissible runs of `γ_f`):

18. **B.1.Consensus as a black box is not enough.** STEALTH, D2 and 1.5D call
    `B.1.Consensus(f − 1, ·)`, a consensus tolerating `f − 1` crashes, run for `f` rounds. The proofs of
    Commit Validity (Lemmas 5, 9, 17) use its Validity in runs where no crash precedes the consensus
    (e.g. `v_j = 0`, no failure), so up to `f` crashes may happen during it — outside its specification;
    an `(f − 1)`-tolerant consensus may output `1` there. The Agreement proofs (Lemmas 8, 11, 18, case
    "all decisions via consensus") never check that at most `f − 1` crashes occur during the
    consensus. We instantiate the consensus concretely as a *max-floodset* (a participant holding `1`
    sends to all; bit = initial bit ∨ received something; decide after `f` rounds;
    `Cslib/Computability/Distributed/SyncCrash/Floodset.lean`). Its validity and biased-to-1 property hold for any number of
    crashes, and in every run where consensus inputs are mixed a crash happened before the consensus
    (process `0` in round ≤ 2 for STEALTH, a round-1 crash for D2 / 1.5D), so the `f` rounds contain a
    crash-free round (pigeonhole, `exists_clean_round`), which gives uniform agreement. *Proof gap;
    protocols correct with this instantiation.*
19. **Self-messages.** The figures say "send to all", "if did not receive any `err`", "if no `huh?`
    received then halt", "received `f + 1` messages of `1`" (D2). Read without self-delivery several of
    these break the protocols (items 20–22); the §4.2 prose ("(sent or) received", "received all `f`
    possible messages") gives the intended reading, which we formalize: a process counts its own vote
    and its own `err` / `huh?` / id set. *Under-specified.*
20. **STEALTH, process 0's own vote.** §4.2 says the choir member `0` sends `err` if it did not receive
    "`n − 1` first-round messages", i.e. process `0` ignores its own value. Then with `v₀ = 0` and all
    other values `1`, no failures, process `0` sends `all[1]`, nobody sends `err`, and everybody commits:
    Commit Validity fails (`StealthLiteral.literal0_not_solvesAC`, `n = 3`, `f = 1`). Fix: process 0 also
    needs `v₀ = 1` (as Fig. 1's "received '1' from all", with the self-message, suggests).
    *False statement under the text's reading; inconsistent with Fig. 1.*
21. **STEALTH, own `err` not counted.** If "did not receive any `err`" ignores the process's own `err`,
    Commit Validity fails: `n = 3`, `f = 1`, `v₂ = 0`, process `0` crashes in round 3 before sending its
    `err`; process `1` sends `err`, receives none and commits (`StealthLiteral.literalErr_not_solvesAC`).
    Similarly, if a process that sent `huh?` but received none halts, a correct process can halt
    undecided (Decision fails): with `f ≥ 2`, process 0 crashes in round 2 sending `all[1]` to every
    choir member except `c`; `c` crashes in round 3 sending `err` only to a correct non-choir process
    `i`; `i` sends `huh?`, everybody else commits at time 3, and `i`, having received no `huh?`, halts. D2 has the same
    issues in Fig. 3 (without self-delivery, "fewer than `f + 1` messages of `1`" is always true and no
    process ever commits; a process with value 0 that sent `err` but received none would commit).
    *Under-specified (self-messages).*
22. **STEALTH, minor.** Fig. 1 round 2 sends `all[1]` to `{0, 1, …, f}` (including itself); the text and
    the count use `{1, …, f}`. In Lemma 8, `v̂₀` is "received `all[1]` or performed commit" although `0`
    never receives `all[1]`; we let `0` use its own round-1 information. Consensus deciders decide at
    time `f + 4` (the paper: last halt at `f + 5`). *Typos / under-specified.*
23. **D2, Lemma 11 (case "some process commits at time 2").** The paper argues that the correct
    `c_j ∈ {j, …, j + f}` that received `1` from `j` "succeeds in sending `j`'s id to all in round 3",
    so all processes start the consensus with `1`. This is false when `c_j` itself committed (it is
    silent in round 3); then uncommitted processes may start with `0`. The statement holds: a correct
    committed process takes part in the consensus with `v̂ = 1` (it receives the round-3 message of any
    uncommitted process that will decide) and biased-to-1 forces `1`; otherwise every `c_j` broadcasts
    its ids. *Proof gap, statement true.*
24. **D2, Lemma 11 (case "no decision before round 4")** uses uniform agreement of the consensus
    without showing that at most `f − 1` crashes occur during it. True (see item 18). *Proof gap.*
25. **Identifiers / rounds.** D2 uses successors `{i + 1, …, i + f} mod n` on `Fin n`; its consensus
    runs in rounds `4 … f + 3` and decides at time `f + 3`; message type `Finset (Fin n)` (the bit
    messages are `∅`). STEALTH messages are all one bit (`Unit`), confirming the paper's 1-bit claim for
    STEALTH. *Modelling choices.*
26. **D1f1** (Fig. 4) is formalized literally (generic process set) and is correct in `γ_1`; with our
    `D = 1` lower bound (item 16) it is message-optimal among protocols deciding at time 1. The §4.2
    prose says a non-committed process commits at time 3 "if it received an `all[1]` message in the
    second round"; it is the third round (as in Fig. 4). *Typo.*

## Appendix D: committing in mid-round (`γ̃_f`)

27. **Model.** `γ̃_f` runs are the runs of `γ_f`; a *mid-round* decision at time `m + ½` is a function of
    the state at time `m` and is performed only if the process completed its round-`m + 1` sending
    phase (all prescribed messages delivered) (`MidRound.DecidesMid`, `SolvesACMid`). KoP does not apply
    to such decisions (performing them depends on the crash pattern, not only on the local state), so
    Lemma 4's analogue is proved at run level via the Silent-Choir construction
    (`chain_to_correct_mid`). *Modelling choice.*
28. **Lemma 16** is proved as stated (`lemma16a`, `lemma16b`; part (a) already for `f ≥ 1`, and the
    decision is necessarily at time `1½`); part (b) needs `f > 1` (D1f1 commits at time 1 without
    round-2 messages). Corollaries 5 and 6 hold (`corollary5`, `corollary6`), and the bound
    `n² + fn − n` is tight (`OnePointFive.corollary6_tight`). *Faithful.*
29. **The 1-bit encoding of 1.5D does not say how it is decoded.** The paper claims that all messages of
    1.5D are single bits, with `huh?` encoded as "quiet to `{i+1, …, i+f}`, `1` to the rest", but it
    never says how a receiver decodes `huh?`.
    * Decoding "`huh?` = a `1` from a process whose successor set I am not in" (silence from a
      predecessor is ignored): 1.5D violates Agreement. Run: `n = 5`, `f = 2`, all values `1`;
      process 4 crashes in round 1 reaching only `{1, 2}`, process 3 crashes in round 2 sending
      nothing. Processes 1, 2 hear from everybody and commit at time `1½`. Process 0 does not; its
      `1`s reach only 3 and 4 (crashed), and 1 and 2 ignore its silence, so they halt. Process 0 gets
      no `all[1]`, runs the consensus alone with `0` and aborts (`OneBit.oneBit_not_solvesACMid`).
    * Decoding that also reads silence from a predecessor (no `all[1]` where an `ok` predecessor would
      have sent one) as `huh?`: the 1-bit protocol solves AC in `γ̃_f` (`OneBitFixed.solvesACMid`).

    With `huh?` a distinct message sent to all, 1.5D is correct as well (`OnePointFive.solvesACMid`,
    `nice_msgs`: exactly `n² − n + nf` messages, commit at time `1½`). *Under-specified encoding;
    correct with the silence-as-`huh?` decoding.* (Appendix D is in the arXiv full version only.)

30. **Lemma 18** (agreement of 1.5D): "this correct process will start the consensus protocol with
    `v̂ = 1`" assumes it takes part in the consensus; it does because any uncommitted process that later
    decides reaches everybody with its `huh?` (exactly what fails with the first decoding of item 29).
    Same consensus gap as item 18. *Proof gap, statement true.*
31. **Not formalized:** the remark "`γ̃_f` is a particular case of `γ_f`, so our protocols are also
    correct in `γ̃_f`".
