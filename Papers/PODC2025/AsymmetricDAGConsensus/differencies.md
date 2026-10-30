# Differences between the formalization and the paper

Paper: Amores-Sesar, Cachin, Villacis, Zanolini, *DAG-based Consensus with Asymmetric Trust*, PODC 2025,
arXiv:2505.17891v1. Rules R1–R6 refer to the verdict scale (`.claude/skills/formalize-paper/verdicts.md`).

## Statement-level issues

1. **Appendix A, "the common core property can be obtained in `log n − 1` rounds" — false.**
   `log_rounds_claim_false`: an 8-process `B³` system (`ex8`, canonical single quorums) and a fault-free run of
   the 2-round quorum-replacement gather in which all processes ag-deliver and no quorum's pairs are in all
   outputs. `log₂ 8 − 1 = 2` exactly. `ex8_three_rounds_core`: with 3 rounds there is a core.
   *Rule:* R1 (explicit claim of a result in the main text/appendix), not excused by R2 (n = 8 is not
   degenerate), R3 (the fix would change the bound, which is the claim), R4. Not a headline (R5) → ❌.
   *Borderline (R6), recorded:* the claim is a remark, and the round count is not defined. We count
   rounds as the paper does for Algorithm 2 ("the 3 rounds of Algorithm 2"; Algorithm 1 "consists of three
   rounds of broadcasting and collecting values"): one round = waiting for a quorum and sending on. Other
   readings: with `⌊log₂ n⌋ − 1`, the paper's own Figure 1 refutes the claim (`⌊log₂ 30⌋ − 1 = 3`,
   `lemma_3_2`). With natural logarithms the bound is even smaller. Only if the arb-broadcast round is not
   counted (Algorithm 2 = 2 rounds) would our examples not apply. The paper never counts that way: §3.2 even
   says "four rounds" once (presumably counting the input broadcast), which makes the bound stricter.
   `ex5` makes the refutation robust to rounding: for `n = 5`, `log₂ 5 − 1 ≈ 1.32`, so 2 rounds
   should suffice under the floor, ceiling and real readings, yet `two_rounds_five_processes` gives a
   2-round run without core. The main text says instead "would require `log n` rounds" (§3) and "a
   logarithmic number of rounds" (§3.2). We do not count these as refuted: "require" reads as a lower bound,
   "logarithmic" is asymptotic, and `⌈log₂ n⌉` rounds is consistent with all our examples. (Under the floor
   reading `⌊log₂ 5⌋ = 2`, `ex5` refutes the §3 sentence too.) The paper's internal inconsistency (`log n` vs
   `log n − 1`; "16 ↔ 3 rounds" vs "`2ⁿ` ↔ `n` rounds") does not make "`log n`" the evident intent under R3:
   the "16 ↔ 3 rounds" sentence supports `log n − 1`, and R3 does not excuse changing a round bound that is
   itself the claim. Reviewer check: the "Tusk" remark of §3.2 (Figure 1 also has no core after 2 rounds) is
   consistent with the canonical run (checked numerically, not in Lean). Figure 1 does have a core after 4 rounds.
2. **§3.2, "3 rounds suffice for fewer than 16 processes; `n` rounds for fewer than `2ⁿ`".** Not formalized
   as a theorem (neither proved nor refuted). The two sentences contradict each other (3 rounds ↔ 16 vs
   `2³ = 8`); the literal second reading for `r = 2` (fewer than 4 processes) agrees with our SAT search.
   `two_rounds_five_processes` refutes the extrapolation "`r` rounds suffice below `2^(r+1)` processes" at
   `r = 2` (5 processes). We only report it as evidence against the heuristic, not as a paper error.
   Exhaustive SAT: no single-quorum fault-free counterexample to the 3-round claim with `n ≤ 7`.
3. **Lemma 3.5, "the processes in one of the quorums `Qᵢ`".** True only for the *correct* members of `Qᵢ`
   (Byzantine members' "receiving before sending" is meaningless). We prove the correct-members version,
   plus the consequence used later: every `DISTRIBUTET` set of a correct member contains `Sᵢ`. Evident intent
   (R3) → no verdict impact.
4. **Definition 3.1 lacks termination.** As written it is satisfied by a protocol that never delivers. We add
   termination (`Gather3.termination`) to Lemma 3.8. Intent evident from Lemma 3.7 ("all processes in the
   maximal guild will have …") (R4) → no verdict impact; the formal statement is stronger than the paper's.
5. **Definition 3.1, "values ag-proposed by the processes of a quorum".** For Byzantine members "ag-proposed"
   is undefined. Our `ExecCommonCore` asks for a set `S` containing *some* pair `(s, v)` for every `s` of a
   quorum of a guild member, contained in all outputs of guild members (any time). Validity separately
   pins down the values of wise senders. For the counterexamples (fault-free runs) this is the paper's
   notion, and the negation we prove is as strong as possible.

## Proof-level issues (statements true)

6. **Lemma 3.5's proof** goes from "a wise process sent `CONFIRM`" to Lemma 3.4, which needs a maximal-guild
   member. Repaired: a quorum of a guild member contains a guild member
   (`IsGuild.exists_mem_guild_of_quorum`, by consistency against the actual faulty set with the member's
   quorum inside the guild). The same fact replaces "Lemma 7 of [3]" at the two other places (the `READY`
   quorum). → 🛠️.
7. **Lemma 3.7's proof** uses an arbitrary process of `Qᵢ ∩ Qⱼ`, possibly Byzantine. Repaired: wise `pᵢ`, `pⱼ`
   both foresee `F`, so consistency gives a correct process in the intersection
   (`IsQuorumSystem.exists_mem_inter_notMem`). → 🛠️.
8. **Lemma 3.3/3.6 liveness** silently need the totality of the reliable broadcast (a guild member can ACK
   `DISTRIBUTES S` and use `DISTRIBUTET T` only once it has arb-delivered all of `S`/`T`). The model also
   needs weak fairness for state-dependent messages. We prove that the arb-delivered and acknowledged
   sets of a guild member stabilize (`dl_stable`, `acked_stable`; they have at most one pair per sender by
   RBC consistency), so the guard of a fixed message eventually holds forever. Routine.
9. **Appendix A's "easy way to observe"** the missing core is not a valid argument (see README). The
   conclusion is checked directly (`fig1_no_core`).

## Modelling choices

10. **Model:** `Cslib.Byzantine.AsyncBroadcast` (asynchronous, interleaving, authenticated channels, Byzantine,
    adaptive corruption with budget `t`; for asymmetric trust take `t = n`). The paper has a static faulty set
    `F`. Ours is the set of processes ever corrupted, and the results hold for every execution, hence
    also for static corruption.
11. **Point-to-point `ACK`** is a broadcast `GMsg.ack j S` carrying the addressee `j` and the acknowledged set
    `S`. Only `j` uses it. `S` records which `DISTRIBUTES` message was acknowledged (needed for "`Tᵢ` =
    union of the acknowledged sets").
12. **Asymmetric reliable broadcast** of the inputs = the `val` message + hypotheses `RBC` (consistency and
    totality towards the guild). For correct senders, validity and integrity follow from the model and
    fairness. In fault-free executions `RBC` holds automatically (`rbc_of_bad_empty`), and every
    arb-delivery order is possible there, so the counterexample runs are runs of the real protocol stack.
13. **Kernels:** `KSays` quantifies over all sets meeting every quorum of `p`. If the kernel system consists
    of the minimal such sets, "all members of some kernel sent `CONFIRM`" is equivalent.
14. **Handlers** fire at any time after their condition holds. `DISTRIBUTES`/`DISTRIBUTET` are sent once,
    with the current `Sᵢ` resp. `Tᵢ`. The ag-delivered `U` is any set containing the `T_q` of the triggering
    quorum and contained in the union of received `DISTRIBUTET` sets `T ⊆ Sᵢ`. This covers every
    scheduling of line 60 before line 62. Line 62 counts only `DISTRIBUTET` messages that line 60 has
    processed (`QualT`). We did not analyse the alternative reading, which counts raw receptions.
15. **Guilds:** Lemmas 3.3–3.8 are proved for every nonempty guild `G` with `RBC` for `G`. The paper's
    maximal guild is a special case (`lemma_3_8_maxGuild`). The guild must be nonempty (Lemma 3.3 is false
    for the empty guild, R2).
16. **Algorithm 2's `r`-round generalization** (`RoundGather.protocol Qs r`; `r = 3` is Algorithm 2) is our
    reading of "modified to have `n` rounds" / "rounds of the type of communication used here".
17. **Processes** are `Fin n`; the paper's process `i` is `i − 1`. Figure 1 = Listing 1, cross-checked
    against the rendered figure.
18. **Not formalized:** Section 4 (Algorithms 4–6, Lemmas 4.2–4.10, Definition 4.1); Theorem 2.4 (cited). See
    the README for unchecked remarks on Section 4.
