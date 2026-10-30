# Differences between the formalization and the paper

D'Amato, Losa, Zanolini, *Asynchrony-Resilient Sleepy Total-Order Broadcast Protocols*, PODC 2024,
arXiv:2309.05347v2. The verdict rules R1–R6 are from the project's verdict scale.

## Statement-level issues (and the rule deciding each)

1. **Algorithm 1, lines 6–7, input rule of `GA_{v,1}`: "not conflicting with `L_{v-1}`".** With this
   rule Algorithm 1 is unsafe. A Byzantine VRF winner proposes a strict prefix of the decided log, all
   honest processes input it, and a conflicting log is decided two views later. This happens in a
   fully synchronous execution with 1 Byzantine process out of 4 that satisfies η-sleepiness,
   Equations 4–5 and `π < η` (`algorithm_1_literal_unsafe`; `theorem_1_false_for_literal_algorithm`
   with `π = 0`; `theorem_2_false_for_literal_algorithm`). So Lemma 3, Theorem 1 (safety) and
   Theorem 2 are false for the printed algorithm. The printed algorithm also has no fallback when no
   proposal qualifies. (The gaps in the line numbering, 4 and 11 in v2 and 10 in v1, are probably
   typesetting artefacts. They are not evidence of a dropped line.) The wording is consistent:
   arXiv v1 says "not conflicting with `L_{v-1}`" in the pseudocode, in the prose and in the proof of
   its Proposition 1, and v2 says it in the pseudocode and the prose. So this is not a one-off typo.
   *Decision: R3, ⚠️ (borderline with 🚨; reviewer endorses ⚠️).* The paper presents Algorithm 1 as [MMR]'s protocol ("We
   recall the total-order broadcast protocol proposed by [MMR]", and its correctness is delegated to
   [MMR]'s Lemmas 6–7). [MMR] requires the proposal to *extend* `L_{v-1}` and inputs `L_{v-1}`
   otherwise. The paper's proofs reason with that version: Lemma 2 ("outputs `Λ` with grade 1, and
   thus multi-casts a vote message for an extension of it"), Lemma 3's inductive step, and Theorem 2
   ("deciding `Λ'` would imply multi-casting a vote for an extension of `Λ'`"). The fix is one word
   plus a missing case in pseudocode. Had the fix been judged a protocol design change, the verdict
   would be 🚨 (R5: Theorem 2 names Algorithm 1). The R3 call rests on the paper's own proofs and on
   its attribution to [MMR]. The [MMR] ePrint could not be retrieved during the review, so its exact
   wording was not re-checked. We formalize the "extends" rule (`Exec.Follows`), and show that it is
   a special case of the printed rule (`Exec.Follows.followsLiteral`).
2. **Definition 4, integrity: "there exists a well-behaved process that inputs the log".** Taken
   literally, this is false for every graded agreement with validity (`integrity_literal_false`), so
   Lemma 1's claim "satisfies the original properties" is literally false. *Decision: R3, ⚠️.* The
   proof of Lemma 1 proves, and [MMR] states, "some honest input extends the log". We formalize that.
3. **Lemma 1 / clique validity: hypotheses too narrow for its uses.** Stated for
   `H' ⊆ H_r ∪ H_{r+1}` and receivers in `H' ∩ H_{r+1}`. Lemma 2 applies it with
   `H' = H_ra \ B_r'`, which may contain processes asleep in rounds `r'` and `r'+1`. Theorem 2 needs
   it for all receivers of round `ra+π+1`. *Decision: proof repair (🛠️), R1.* The statement as
   written is true (`lemma_1_clique_validity`). The general form (`H'` disjoint from `B_r`, any
   receiver whose `M0` contains the clique's votes) has the same proof (`clique_validity`).
4. **Lemma 3, base case.** "Follows from graded consistency": insufficient, since graded consistency
   yields only grade ≥ 0, and a longer conflicting grade-0 output may exist
   (`graded_consistency_insufficient`). *Decision: proof repair (🛠️).* Repaired with [MMR]'s
   argument: integrity of `GA_{v-1,2}` plus uniqueness of `GA_{v-1,1}`
   (`Exec.Follows.decision_lock`). This uses the synchrony and η-sleepiness of rounds `r-2`, `r-1`.
   In the paper's network model (Section 2.1: in a synchronous round every awake honest receiver gets
   *all* messages sent so far, gossip included), the receivers of a synchronous round have the same
   messages and hence the same tally. So the conclusion also follows directly in the paper's model.
   `graded_consistency_insufficient` shows that the cited GA property alone does not justify it.
   That example lets Byzantine processes send different votes to different receivers, which an
   abstract GA allows.

## Implicit assumptions made explicit

5. **Synchronous-round assumption.** Section 2.3 states Equations 1 (churn) and 2 (failure ratio
   `β̃`). Section 3.3 and the proofs use η-sleepiness (Equation 3). We assume Equation 3 in every
   round outside `[ra+1, ra+π+1]` (where Equation 4 replaces it). We prove that Equations 1 and 2
   imply 3 for `0 ≤ γ < β < 1` (`Exec.sleepy_of_churn_of_failure`), and that the paper's `β̃` makes
   the worst-case bound exact (`betaTilde_identity`). The paper does not state this implication; it
   is consistent with Figure 1. The "must have" (necessity) of `β̃` is not formalized.
6. **Lemma 2** uses validity at round `ra`, so round `ra` must be η-sleepy (assumed). We also assume
   `ra ≥ 1`: in round 0 nobody votes, and the round-1 vote is unconstrained (degenerate case, R2).
7. **Lemma 3** needs synchrony (automatic for rounds `≤ ra`) and η-sleepiness of all rounds in
   `[r-2, ra]` (assumed for all rounds `≤ ra`). The hypothesis `r ≤ ra` is dropped (vacuous).
8. **Theorem 2** additionally needs η-sleepiness in rounds `≥ ra+π+2` for the synchronous
   induction after the asynchronous period ("apply the same inductive reasoning of MMR").
9. **Lemma 1, original properties**: hold in synchronous rounds. The paper states this only in the
   proof ("for all properties other than clique validity, network synchrony is assumed").

## Modelling choices

10. **Rounds and receivers.** `H_{r+1}` (awake at the beginning of `r+1`) are exactly the receivers
    of round `r`, as in the paper. Received messages are kept across sleep (`rcv_mono`); a process
    that wakes up in a synchronous round receives everything sent so far.
11. **Byzantine messages.** Arbitrary sets of messages with sender in `B_t`, sent in round `t`, with
    arbitrary round tags (back-dating allowed). The sender of every received message tagged `s`
    lies in `O_s` (honest) or in `B_r` (Byzantine), so senders of unexpired messages lie in
    `O_{r-η,r}`, as the paper uses.
12. **Equivocation.** A sender whose latest unexpired messages carry different logs is discarded
    entirely, for the round-`r` messages and for `M0` alike, as in Figure 3. No fallback to an
    older message.
13. **Proposals and VRF.** Not modelled. The odd-round vote of an honest process is required only to
    extend some longest output `L_{v-1}` of the previous GA. This over-approximates every outcome of
    the VRF lottery, including Byzantine winners, so the safety theorems hold for all outcomes. In the
    counterexample the votes are realised by concrete proposals: a Byzantine view-0 proposal `[1]`
    winning view 1 (honest view-0 proposals are the genesis log), the Byzantine proposal `[]` (genesis,
    the same log honest processes propose in view 0) in round 3, and the honest proposal
    `b‖C_2 = [2]` in round 5. Shifting the run by one view (honest genesis votes in view 1, honest
    proposal `[1]` in view 2, Byzantine `[]` in view 3, honest `[2]` in view 4) needs a single
    Byzantine lottery win (argued on paper, not formalized).
14. **Even rounds without a grade-1 output** (possible only under asynchrony): the vote is
    unconstrained (the paper leaves this undefined).
15. **View 1.** Round 1 votes are unconstrained (any proposal extends genesis), and decisions start
    in round 3 (`GA_{0,2}` does not exist; see the typo list).
16. **Validity** is stated for every common prefix of the honest inputs. It is equivalent to the
    paper's "the longest common prefix is output with grade 1", because grade-1 outputs are
    prefix-closed.
17. **Bounded divergence** is formalized as "any pairwise conflicting family of output logs has at
    most 2 members".
18. **`P0` in the bridge** (`Exec.ga`) is taken to be `O_{r-η,r}`, a superset of the actual senders
    of `M0`. The quorum hypothesis of Lemma 1 then is exactly η-sleepiness, the step argued in
    Section 3.3.
19. **Logs** are `List α` with the prefix order; the genesis block is the empty log `[]`.
20. **Thresholds**: `β = 1/3` (decision threshold `2/3`) in Sections 3.x, as in the paper;
    Section 2.3 results are for general real `β, γ`.

## Typos / small slips (no effect)

21. Proof of Theorem 2: `|H_ra \ H_{ra+π+1}|` should be `|H_ra \ B_{ra+π+1}|`.
22. Proof of Lemma 2: `|S_r' ∪ P0|` should be `|O_r' ∪ P0|`. The claim that the latest messages in
    `M0` are "all from rounds no later than `ra`" is inaccurate (later honest votes may be latest),
    but those votes extend `Λ` by the induction hypothesis, which is how we prove it.
23. Algorithm 1, line 1 for `v = 1` refers to `GA_{0,2}`, which does not exist.

## Not formalized

* Theorem 1, liveness half (probabilistic, VRF-based, deferred to [MMR]'s Lemma 7).
* Theorem 3 (healing after asynchrony), informal two-line proof about liveness.
* Necessity of `β̃` (Figure 1 caption, Section 2.3 "must").
