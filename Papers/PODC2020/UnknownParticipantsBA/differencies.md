# Differences between the formalization and the paper

Paper: P. Khanchandani, R. Wattenhofer, *Brief Announcement: Byzantine Agreement with Unknown
Participants and Failures*, PODC 2020 (the "BA"). Full version: *Byzantine Agreement with Unknown
Participants and Failures*, arXiv:2102.10442v1 (the "full version"). Numbering: BA Lemmas 1–4 and
Theorem 1 are full-version Lemmas 2, 4, 6, 7 and Theorem 2. BA Section 5 (consensus) is
full-version Section VII (Algorithm 3, Lemmas 8–11, Theorem 3).

## Errors in the paper

1. **BA Lemma 4 (full Lemma 7) is false.** *False statement.*
   Claim: with `n > 3f`, every correct node witnesses a good round before it terminates. A good
   round is an iteration in which all correct nodes select the same correct coordinator.
   Counterexample with `n = 7`, `f = 2` (`Counterexample.lean`, `Cex.lemma4_false`):
   - Correct nodes `2,…,6`, Byzantine nodes `0, 1`.
   - Both Byzantine nodes make themselves known to everybody in round 1, so `n_v = 7`. The
     thresholds are therefore 3 copies (`n_v/3`) and 5 copies (`2n_v/3`).
   - Round 1: node `1` sends `init` to `2, 3, 4`; node `0` sends `init` to `3, 4`.
   - Round 2: both Byzantine nodes send `echo(1)` to node `2`; node `1` sends `echo(0)` to
     `3, 4, 5`.
   - Round 3: both Byzantine nodes send `echo(0)` to node `2`.

   What happens:
   - Iteration 0: node `2` adds `1` to `C_2` and selects `C_2[0] = 1`. The others select `2`.
   - Iteration 1: the others add `1` and select `C[1] = 2` again. Node `2` adds `0` and selects
     `C_2[1] = 1` again.
   - So every correct node breaks in iteration 1. Neither iteration was good
     (`Cex.no_good`: no iteration is ever good). No correct node ever accepts any opinion
     (`Cex.no_accept`).

   The proof fails in its last step. It says a reselected node must lie in
   `{C_v[r mod |C_v|] : r < r_c}` and so needs `r > |C_v|`. This treats `C_v` as a fixed set. In
   fact `C_v` grows in sorted order, and inserting a smaller identifier shifts the index back onto
   the previous coordinator. The rest of the counting (`n_ns ≤ 2f`, `|C_v| > r_c`) is fine.
   A bounded search over abstract schedules finds no violation of Lemma 4 for `f = 1`
   (`g ∈ {3, 4, 5}`), and finds `n = 7`, `f = 2` (`modelcheck/rotor_game.py lemma4`). The search
   uses only the constraints of Lemmas 1–3. The Lean run confirms that the schedule is realizable
   with the real thresholds.

2. **BA Theorem 1 (full Theorem 2) is false.** *False statement.*
   Claim: there is a round in which every correct node accepts the opinion of a common correct
   coordinator. Formalized as `Cex.Theorem1Claim`. It is refuted by the `n = 7` run above
   (`Cex.theorem1_false`). It is also refuted for the smallest admissible system `n = 4`, `f = 1`
   (`Cex4.theorem1_false`):
   - Byzantine node `0` sends `init` to `1, 2`, and `echo(0)` to `1` only.
   - Iteration 0: node `1` adds `0` and selects it; nodes `2, 3` select `1`.
   - Iteration 1: everybody has `C = {0,1,2,3}` and selects `C[1] = 1`, so this is a good round
     (`Cex4.good_one`).
   - Nodes `2, 3` are reselecting `1`, so they break in this very iteration. They never accept
     `1`'s opinion, which would only arrive in iteration 2.

   So there is a second gap, independent of Lemma 4. (This instance uses the literal reading
   "every correct node", including those that already terminated: in iteration 2 the only running
   node, `1`, does accept `1`'s opinion. The `n = 7` run refutes Theorem 1 under either reading,
   since no correct node ever accepts anything.) The proof of Theorem 1 says the node "accepts
   the corresponding opinion in the next round (Line 17)", but by then the node may have
   terminated.
   *What does hold:* the termination half of Theorem 1, i.e. every correct node breaks within
   `n` iterations (`paper_terminates`).
   *Repair:* replace line 19 by "break once `2r > n_v`" (`fixedRule`). Then:
   - some iteration `r ≤ f` is good, and in iteration `r + 1` every correct node accepts exactly
     the coordinator's opinion;
   - every correct node terminates in an iteration `r` with `f + 1 ≤ r ≤ ⌊n/2⌋ + 1`.

   This is `rotor_fixed`, i.e. `O(n)` rounds as the paper claims. The bound "good round within
   `f + 1` iterations" is tight: the abstract search (`modelcheck/rotor_worst2.py`) finds worst
   case exactly `f` for `f ≤ 3`, `g = 2f + 1`.

3. **Full version, Algorithm 3: the "fill rule" breaks agreement.** *Under-specified algorithm*
   (not a refutation of Algorithm 3 verbatim: the witness adds our reading of the rule to our own
   phase layout).
   The rule says: if `u` heard from `v` during initialization but receives nothing from `v` later,
   `u` assumes that `v` sent what `u` itself sent in the previous round. Algorithm 5 states the
   same rule more explicitly ("substitutes the message of type `m'` that it sent most recently").
   The rule is meant for terminated nodes. In Algorithm 3, however, correct nodes are also silent
   whenever they miss a threshold: `prefer` and `strongprefer` are sent only conditionally. Their
   silence is then counted as support for the receiver's own value.

   Counterexample with `n = 4`, `f = 1` (`FillRule.lean`, `FillCex.fill_rule_breaks_agreement`):
   - Correct nodes `1, 2, 3` with inputs `0, 0, 1`; Byzantine node `0` is the coordinator of
     phase 0.
   - Phase 0: node `1` alone sends `prefer(0)`. It counts the silent nodes `2, 3` as `prefer(0)`
     and then as `strongprefer(0)`, and decides `0`.
   - Nodes `2, 3` see only one `strongprefer(0)` and adopt the Byzantine coordinator's `1`.
   - Phase 1: node `1` is silent in the `prefer` round and is counted as `prefer(1)`, so node `2`
     decides `1`.

   The Lean witness adds the fill rule to *our* phase layout (`fillExt`). Silence is judged per
   round on consensus messages, because in Algorithm 3 the consensus rounds carry no rotor
   messages. The same adversary is harmless without the fill rule (`FillCex.without_fill`).
   Algorithm 5 avoids the problem with explicit `nopreference`/`nostrongpreference` messages.
   Algorithm 3 does not.

4. **Full version, Algorithm 3 / Theorem 3: other gaps.** *Proof gaps and under-specified
   algorithm; statement true.*
   - (a) Theorem 3 relies on Theorem 2, which is false (item 2). Its "within `O(f)` rounds … a
     correct coordinator gets picked" is exactly the missing good-round lemma.
   - (b) "Execute a round of rotor-coordinator" accepts the opinion that the *previous*
     iteration's coordinator broadcast, i.e. one from the previous phase. Lemma 11 needs the
     coordinator's opinion *after* line 9 of the current phase. The phase timing is inconsistent.
   - (c) What happens when the embedded rotor executes `break` is not specified.
   - (d) Lemma 10 + Lemma 8 ("terminate with the same output by the next round") need the nodes
     that already terminated to keep sending. This is why the unsound fill rule exists.

   We verify a repaired Algorithm 3 (see "Consensus" below): agreement, validity, and termination
   within `3f + 7` rounds (`consensus_correct`). So the BA's claim that consensus with `n > 3f` is
   solvable in `O(n)` rounds in the id-only model is **true**, and so is the full version's
   `O(f)`.

5. **Minor.**
   - *Typo-level slip.* The proof of BA Lemma 1 garbles the inequality chain ("`G > 2(f − f_v')/3`
     or at least one"). What is needed is `n_v/3 − f_v'' ≥ (g − 2f_v')/3 > 0`, i.e. `g > 2f_v'`
     (`lemma1_arith`).
   - *Under-specified; true while everyone runs.* BA Lemma 3 (relay) holds only while all correct
     nodes are still running. A terminated node no longer echoes. Our `relay` assumes all correct
     nodes are alive up to the later step.
   - *Imprecise.* Lemma 2 needs only `g ≥ 2f`; `g > 2f` gives it with strict inequality
     (`lemma2_arith`).

## Modelling choices (not errors)

- **Model** (`Model.lean`).
  - Rounds are synchronous lock-step. Identifiers come from an arbitrary type (`ℕ` in the
    examples); the existing nodes are `G ∪ F` (finite, disjoint).
  - A protocol is one state machine parameterised only by the node's own id and input, so `n` and
    `f` are unknown by construction.
  - Correct nodes *broadcast* a finite set of messages per round, including to themselves. The
    paper's "send to a specific node that sent a message before" is never used by the algorithms.
  - Receivers see `(true sender, message)` pairs. Duplicates within a round collapse by set
    semantics.
  - Byzantine nodes send arbitrary per-receiver message sets, may stay silent towards some nodes,
    and may mention arbitrary, even non-existent, identifiers. A Byzantine node cannot use several
    identities: no Sybil, no forging of the direct sender. This is the paper's "cannot forge its
    identifier when communicating directly".
- **Selection rule.** We follow line 14 of the pseudocode, `p ← C_v[r mod |C_v|]`, which the
  proof of Lemma 4 also uses explicitly ("`r_c mod |C_v| = r_c`"). The prose describes it as
  "selects the coordinator with the next larger identifier"; under that different rule (successor
  of the previous coordinator in the current `C_v`) both counterexample runs are no longer
  counterexamples, and we have not analysed it.
- **`n_v`.** `n_v` is the number of nodes heard from so far, *including* the current round. The
  paper's "until the round `r`" is ambiguous. In both counterexamples all nodes are heard from in
  round 1, so they work under either reading.
- **Accepting.** The rotor's "accept `x`" records the set of opinions received from the previous
  coordinator (a singleton for a correct coordinator). `Accepts v r x` means `x` is in that set
  and `v` was running at the start of iteration `r`.
- **Termination.** Termination (`break`) freezes the node and silences it. On `break`, `B_v` is not
  broadcast, matching the pseudocode.
- **Consensus algorithm** (`Consensus.lean`; repaired Algorithm 3).
  - The candidate-set layer runs in every round; the paper runs one rotor iteration per phase.
    Relay is then faster, which is harmless.
  - The coordinator of phase `k` is `C_v[k mod |C_v|]`, chosen in the `prefer`-receiving step.
  - Phases have 3 rounds:
    - end of step `3k+1`: broadcast `input`;
    - step `3k+2`: `prefer`;
    - step `3k+3`: adopt a value with `≥ n_v/3` `prefer`s; send `strongprefer`; the coordinator
      broadcasts its *current* opinion;
    - step `3k+4`: decide on `≥ 2n_v/3` `strongprefer(x_v)`; adopt the coordinator's opinion on
      `< n_v/3` `strongprefer(x_v)`; broadcast the next `input`.
  - The paper writes "`strongprefer(x)`" for some `x`. We use `x_v`; this is equivalent, because
    `n_v/3` copies of `strongprefer(x)` force `x_v = x` (`lock`, `adopt`).
  - When several values have `≥ n_v/3` `prefer`s, the minimum is taken. This never happens
    (`adopt`).
  - `n_v` is cumulative rather than frozen after initialization. There is no fill rule.
  - Decided nodes keep participating and never halt. "Termination" means that every correct node
    has decided by round `3f + 7`. Halting one phase after deciding would also be safe, but this is
    not formalized.
  - Opinions are in any linear order `X`. Validity is stated as "unanimous input `y` ⇒ only `y` is
    decided" (the full version's formulation for real inputs). For `Bool` we derive the BA's form
    "the output is an input of some correct node" (`consensus_validity_bool`).
- **Rounds vs. steps.** Step `s + 1` receives the messages of round `s + 1` and computes the
  messages of round `s + 2`. The rotor's loop iteration `r` is step `r + 2` (round `r + 3`).

## Not formalized

- Reliable broadcast (full version Section V, Theorem 1) as a separate algorithm with payloads.
  Its mechanism is exactly the candidate-set layer (full Lemma 6 says so). The layer's properties
  are proved:
  - correctness: `G_sub_C`;
  - unforgeability: `C_origin` / `E_origin`, i.e. a candidate `p` itself sent `init` to a correct
    node;
  - relay: `relay`.
- Approximate agreement (Section VIII), the asynchronous and semi-synchronous impossibility
  results (Section IX), parallel consensus and dynamic networks (Sections X–XI).
