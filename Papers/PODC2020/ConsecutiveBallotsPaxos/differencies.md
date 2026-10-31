# Differences between the formalization and the paper

Paper: E. Goldweber, N. Zhang, M. Kapritsos, *On the Significance of Consecutive Ballots in Paxos*, PODC 2020
(brief announcement); full version arXiv:2006.01885v1.

## Errors in the paper

1. **Lemmas 4.2′ and 4.3′ are false for the literal Definition 6** (`Counterexample.lean`:
   `lemma_4_3'_literal_false`, `lemma_4_2'_literal_false`). In Definition 6,
   `Chosen(i, v) ≡ ∃Qᵢ. CQ(Qᵢ, v) ∧ ∃α ∈ Qᵢ. accept(i, v)_α ∈ sent_α`, the ballot-`i` accept is not required
   to be one of the accepts `accept(x_k, v)_{α_k}` of Definition 5 that form the consecutive set. Counterexample
   (5 acceptors, majority quorums, Classic Paxos, reachable; actions in `cexActs`):
   - ballot 3: `A, B, C` promise (`⊥`); `x` is proposed; `A` accepts;
   - ballot 5: `B, C, D` promise (`⊥`); `y` is proposed; `D` accepts;
   - ballot 9: `A (3,x)`, `B ⊥`, `C ⊥` promise; `x` is proposed; `A, B, C` accept.

   `x` is CQ-chosen "in ballot 3" (`cex_chosen_3`), yet `y` is proposed and accepted in ballot 5.
   **Rule R3 → ⚠️.** The intended version is recoverable: the proof of Lemma 4.3′ speaks of "the acceptor in
   `Qᵢ` that accepted `v` in ballot `i`" as a member of the CQ. The fix is local (`x_α = i`; our `CQChosen'`).
   Under it both lemmas are proved (`lemma_4_3'`, `lemma_4_2'`), and `x` is not chosen in ballot 3
   (`cex_not_chosen'_3`). The paper's proof reasons with the intended version, in fact with "`i` is the largest
   CQ ballot". These are numbered lemmas, so the issue is statement-level (R1), not a proof repair. Under the
   literal definition, Lemmas 4.1–4.3, 4.1′ and Theorems 3.1/3.2 remain true. We prove them for the literal
   Definition 6, which is weaker than the intended one (`CQChosen'.cqChosen`).
   Borderline note (reviewer): the TLA+ `AgreedConsecQ(v, b)` of Appendix B has the same looseness
   (`∃ a ∈ Q : Sent2b(a, v, b)` is not tied to the ballots of `ConsecQ`), so the literal reading is
   not a one-off slip of Definition 6. We still apply R3, because the paper's own proof of Lemma 4.3′
   reasons with the intended version (the ballot-`i` accept is a member's CQ accept), and the fix is
   local and does not change Theorems 3.1/3.2.

2. **Missing case in the proof of Lemma 4.3′** (statement true for the intended definition; 🛠️ level, dominated
   by item 1). The base case and the inductive step assume that the intersecting acceptor's CQ ballot is `≤ i`.
   They also assume implicitly that its promise for `j` came after its accept, so the promise reports a ballot
   `≥` its CQ ballot. Both fail when `i` is not the largest ballot of the CQ. Repair (`propose_eq_of_interval`):
   strong induction on `j ≥ lo`, where `[lo, hi]` is the CQ's ballot span. Ballots in `[lo, hi]` carry `v`
   because some CQ member accepted `v` there and there is one proposal per ballot. For `j > hi` the intersecting
   acceptor's CQ ballot is `< j`. So it accepted before promising `j` (the protocol forbids accepting below a
   promised ballot), and the highest reported ballot lies in `[lo, j)`.

3. **Appendix B (TLA+) is vacuous as printed** (`TLAAppendix.lean`: `tla_agreedConsecQ_false`).
   `ConsecQ(Q, b, v) ≜ ∀ r ∈ Acceptor : ∧ NotIn(Q, r) ∧ ∃ m ∈ msgs : …`. Rendered from the PDF (page 18),
   `NotIn(Q, r)` is a top-level conjunct, so `ConsecQ` is false for every nonempty `Q`. `AgreedConsecQ` is then
   never true, and `SafeValue` holds trivially. Also `∃ m ∈ msgs : (type = 2b ∧ acc = r) ⟹ …` is satisfied by
   any message that is not a 2b of `r`, so `∀` was presumably meant. Even with these fixes, `ConsecQ` (no
   outside 2b ballot interleaves with all of `Q`'s) does not express Definition 5. **Not a verdict item.**
   Section 6.2 says "both in TLA+ and with Formal Verification we showed the correctness". This is a claim
   about the authors' verification artifacts, not a mathematical statement (R1), and the correctness itself
   holds (`theorem_3_2` with `cp = true`). The typeset appendix may differ from the file actually model-checked;
   we only judge the printed text. The IronFleet/Dafny proof was not inspected.

4. **Typos / slips.**
   - Lemma 4.1′ proof: "at least one acceptor that has accepted *v* in ballot *j*" should say *w*.
   - Appendix A writes `Chosen(v, i)` (argument order swapped w.r.t. Definition 6) and `i, j ∈ ℤ⁺`. Section 3
     uses ballots in `ℕ`; the TLA+ uses `Int`.
   - Definitions 7–9 are protocol properties, not definitions. Definition 7 holds by Definition 6; Definition 8
     is an invariant (`accept_implies_propose`); Definition 9 is their composition.
   - Definition 5 reuses `n` (the number of quorum members) as a ballot name from Definition 1.

## Modelling choices

- **Protocol model.** Interleaving transition system over the set of all sent messages, as in the paper's
  TLA+: `maxBal : A → WithBot ℕ` (TLA+ `-1` = `⊥`) and `last : A → Option (ℕ × V)` (TLA+ `maxVBal/maxVal`).
  - Phase 1b fires iff `maxBal a < b` (strict, as in TLA+ `Phase1b`); the prose "if `n` is the greatest ballot
    α has promised" is ambiguous between `<` and `≤`.
  - Phase 2b fires iff `maxBal a ≤ b`.
  - Phase 2a requires that no proposal exists yet for the ballot (TLA+), the paper's "different proposals have
    different ballots".
- **Phase 1a** is a separate `prepare` message as in TLA+; it has no effect on safety.
- **Receiving.** Proposers' guards (Definitions 10–12) and learners' criteria refer to the paper's `msgs_π` /
  `msgs_l`. We let proposers use all sent messages (more behaviours, so the safety results are stronger).
  Learners are arbitrary subsets of the sent messages (`theorem_3_1` takes `L ⊆ s.msgs`).
- **Normal Proposal (Definition 10)** is transcribed as TLA+ `Clause1`. A quorum `Q` has each sent a promise
  for `b`, and either all promises from `Q` for `b` report `⊥`, or `v` is reported with a maximal ballot among
  them. The paper's Definition 10 has the same content.
- **Consecutive Proposal (Definitions 11–12)** for ballot `c + 1`: a promise for `c + 1` reporting `(c, v)`, or
  `accept(c, v)` from any acceptor. Ballot 0 has no consecutive proposal. The TLA+ `ConsecProposal =
  ¬Clause1 ∧ Clause2` is used only disjunctively with `NormalProposal`, so it is equivalent to our
  `Clause1 ∨ Clause2`. Enabled by the flag `cp`.
- **Quorums**: any intersecting family (`QuorumSystem`), as in the TLA+ `QuorumAssumption`. The paper's
  "`|Q| ≥ f + 1` of `2f + 1`" is `QuorumSystem.majority` (`card A < 2 |Q|`). All examples use 5 acceptors.
- **Definition 5 (CQ).** "`∃accept(x₁, v)_{α₁} ∧ … ∧ ConsecutiveSet({x₁,…,xₙ})`" is formalized as a
  function `x : A → ℕ` with `accept(x a, v)` sent by each `a ∈ Q` and `ConsecutiveSet (x '' Q)`. Definition 2
  uses `IsLeast S n` for `n = min(S)`.
- **Theorem 3.1.** The paper's `Learned` is for one learner `l`. We prove the stronger statement for any two
  learners, and across two states of one execution (`theorem_3_1_execution`; messages are never removed).
- **Section 4.2 (liveness).** Only the argument given is checked: the executions are unchanged, and Classic
  Chosen/Learned implies CQ Chosen/Learned. Liveness itself (partial synchrony, leader election) is not
  modelled.
- **Section 5 (Consecutive Proposals).** The paper gives only an "intuition", not a statement. Section 6.2
  claims safety of the combination, which we prove (`cp = true`). The proof goes through the same induction as
  Lemma 4.3′: a Consecutive Proposal in `c + 1` copies the proposal of ballot `c`.
- **Not formalized**: the IronRSL/Multi-Paxos refinement (Section 6) and Section 4.3 (informal).
