# Differences between the formalization and the paper

Paper: T.-L. Breitkopf, J. Dallot, A. El-Hayek, S. Schmid, *Ranking Opinions with Few States in
Population Protocols*, PODC 2026 (arXiv:2605.18707v1).

## Model

1. **Agents are labelled**: a configuration is a function `A → Q` (`A` a finite type), not a multiset.
   Brakets are also viewed as a multiset (`brakets C = univ.val.map C`) where the paper does so.
2. **Weak fairness** (Def. 2.1, "every pair of agents interacts infinitely often") is formalized for
   *unordered* pairs: for all `a ≠ b`, infinitely often `(a,b)` or `(b,a)` is scheduled. This is the
   weaker hypothesis, so our theorems are (slightly) stronger than the ordered reading.
3. **Global fairness** (Def. 2.2) is formalized on labelled configurations (as in Angluin et al.). The paper
   views configurations as multisets; global fairness on labelled configurations is a slightly *stronger*
   hypothesis than on multisets, so `ranking_correct` is slightly weaker than the paper's claim.
4. "Stabilizes / eventually outputs": we prove "there is `T` such that for all `t ≥ T` all agents output
   the right value"; for Theorem 1.1 we additionally prove *output stability* (no configuration reachable
   from time `T` has a different output).
5. Interactions require two distinct agents; an execution is a sequence of configurations plus a schedule
   (`PopulationProtocol.Protocol.Execution`).

## Section 3 (Circles, Theorem 1.1)

6. **Weight**: defined by an explicit natural-number formula; `w_eq_sub` proves it equals the paper's
   `k` / `(j - i) mod k`.
7. **Greedy independent sets** (Def. 3.1) are defined directly as `G_p = {c | p ≤ x_c}`. The paper's
   greedy construction produces exactly these sets (each round takes one copy of every remaining color);
   we did not formalize the greedy procedure itself.
8. **Circle braket sets** (Def. 3.6) use the cyclic successor `nxt G g = argmin_{h ∈ G} w(g,h)` instead of
   "sorted list, consecutive pairs, wrap around". These coincide (the minimizer of the clockwise distance
   is the next element in cyclic order; for `G = {g}` it is `g` itself), but the equivalence with the
   sorted-list formulation is not formalized.
9. **Termination** (Thm 3.4): the ordinal potential `ω^{n-1}w_1 + … + w_n` is replaced by the natural
   number `Φ = ∑_a 3^(k − w(a))`, which strictly increases at every ket exchange and is bounded by
   `n·3^k`. As in the paper, this holds for *every* execution, without fairness.
10. Lemma 3.2 is stated in two forms: as in the paper (`greedy_majority`) and as the characterization
    actually used: `⟨i|i⟩ ∈ ⋃ f(G_p)` iff `0 < x_i` and `x_c < x_i` for all `c ≠ i` (`diag_mem_layers_iff`).
11. Lemma 3.7 is proved for any *stable* multiset with the right bra/ket counts (no execution needed);
    the induction peels off the circle `f(G_1)` and recurses on the counts `x_c − 1` (equivalent to the
    paper's induction on `r`). The paper's Case 1/Case 2 distinction is unnecessary (the argument of
    Case 2 works uniformly). No gap found in the paper's proof.
12. Theorem 1.1's statement "agents `⟨i|i⟩` exist iff `i` is the majority color" is formalized as: in the
    stable configuration, `∃ a, braket a = ⟨i|i⟩` iff `0 < x_i ∧ ∀ c ≠ i, x_c < x_i`. In the output part
    a unique majority color (with at least one supporter) is assumed, as in the paper. The "k³ states"
    claim is `card_CState`.
13. Step (2) of Circles (output propagation) is applied to the brakets *after* step (1), as the paper's
    "two successive operations" suggests.

## Section 4.1 (TieReport, Theorem 4.1) — **the theorem is false as stated**

14. The paper's rules are ambiguous in two respects; we parametrize them (`TRVariant`):
    `onlyNoTie` — does rule 2 (tie spreading) affect every non-diagonal agent (literal text) or only agents
    at `no_tie` (suggested by the proof of Lemma 8.1)? Rules are applied in the order 1, 2, 3, each
    condition reading the current values.
15. **Counterexample, no-tie case** (both readings): `tieReport_counterexample_noTie`. `k = 3`, four agents
    with colors `0,0,1,2` (unique majority `0`). Schedule `(1,2)`, `(0,3)`, `(0,2)`: agent 0 decays from
    `⟨0|0⟩` to `⟨0|2⟩` (becomes `tie_spreader` by rule 1, possibly `tie` by rule 2) and then recombines to
    `⟨0|0⟩`. The brakets `⟨0|0⟩,⟨0|1⟩,⟨1|2⟩,⟨2|0⟩` are now stable (= `⋃ f(G_p)`), and agent 0 is the
    *only* diagonal agent; rule 3 lets a diagonal agent reset only *other* agents, so agent 0 is never
    reset to `no_tie` and outputs "tie" forever, under any (weakly fair) continuation. The proof of
    Lemma 8.1 overlooks the remaining `⟨μ|μ⟩` agent itself.
16. **Counterexample, tie case — ambiguity-dependent** (literal reading of rule 2 *and* rule 2 applied in
    both directions simultaneously, i.e. each agent's update reads the partner's status after rule 1 but
    before the partner's own rule-2 update, `TieReport.lean` `tsUpd`): `tieReport_counterexample_tie`.
    With one direction applied first (sequentially), model checking finds no tie-case failure; so this is
    a consequence of an ambiguous reading, not a definite error (unlike item 15). `k = 2`, colors
    `0,0,1,1`, schedule `(0,2)`, `(0,1)`, `(1,2)`, `(1,3)`: two fresh spreaders meet and turn each other
    into `tie`; afterwards there is neither a spreader nor a diagonal agent, and agents 0 and 2 stay at
    `no_tie`, outputting a color forever although there is a tie. (With the `onlyNoTie` reading the tie
    case is fine.)
17. **Fix** (`fixedV`: `onlyNoTie` + `selfReset`, i.e. additionally an agent `⟨i|i⟩` resets *itself* to
    `no_tie`): `tieReport_fixed_correct` proves Theorem 4.1 for the fixed protocol (same state count `3k³`).
    The tie case needs an invariant not in the paper: at every time there is a diagonal agent or a
    `tie_spreader` (`diag_or_spreader`).
18. The claim "4k² states if only win/lose output" is not formalized.

## Section 4.2 (TieSharing, Theorem 4.2)

19. *(Clarification, not an error.)* Rule application order matters: if all status rules read the *pre-interaction* statuses, the theorem
    fails already for `k = 2`, colors `0,0,1` (model checker, `tools/tieshare_pre.py`). With rules applied
    sequentially in the listed order, each in both orientations and reading current values, no
    counterexample was found by exhaustive model checking (k=2,3: n ≤ 7; k=4: n ≤ 6; k=5: n ≤ 5; k=6,7: n ≤ 4).
    Lean: `tieShare_pre_counterexample` (pre-interaction reading, k=2, colors 0,0,1: the unique `⟨0|0⟩` agent
    is a loser forever) and `tieShare_correct` (Theorem 4.2 for the sequential reading). The simultaneous
    reading is the less natural one ("follows the following rules" in order), so we classify this as a
    clarification.
19c. **Output of winners.** `tieShare_correct` uses the output map `tsOut`: winners/winner spreaders output
    their own bra (= initial color), losers output `out`. If instead every agent outputs its `out` variable
    (Circles' "Output: return out", not redefined in Section 4.2), the claim "the output of every winner or
    winner_spreader is its initial color" is **false** even for the sequential reading:
    `OutCounterexample.tieShare_out_counterexample` (k = 2, colors 0,0,1,1, schedule (0,2),(0,1),(1,2),(1,3),
    (1,2),(3,2): a fixed configuration in which agent 2, color 1, a winner spreader, has `out = 0` forever;
    the reviewer's model check also finds four k = 3 inputs). Which reading is intended: the theorem itself
    distinguishes "output of a winner" (its initial color) from "output of a loser" (a winning color), the
    section intro says "agents with a winning color output their color", rules (i)/(ii) only make sense for
    losers, and the 3k² variant outputs win/lose from the status alone — all consistent with an output map
    that depends on the status. We therefore take `tsOut` as the intended reading (an output map costs no
    extra states); under the literal `out` reading the theorem is wrong.
    Interpretation: status ∈ {winner_spreader, winner, loser}; z ∈ [x,y]_k iff (z−x) mod k ≤ (y−x) mod k
    (so [i,i] = {i}); ⊆ is set inclusion plus the paper's extra condition x≠y' ∨ y≠x' (needed for Claim 2:
    otherwise ⟨a|a+1⟩ ⊆ ⟨a+1|a⟩ would mix sectors); winners output their own color, losers `out`.
19a. Lemma 8.2 (r = 1) ignores tokens still alive after stabilization (they can demote majority agents or
    promote others); a separate token-extinction argument is needed (`extinction`).
19b. Lemma 8.3's proof is a sketch: Claim 3 only holds once all agents of color μ_s have their final braket
    (`witness`); "token ascent until attached" is replaced by "tokens not on a top braket ⟨μ_s|μ_{s+1}⟩ die out"
    (`no_spurious`) and "the set of token holders is eventually constant" (`ws_const`); the induction needs
    a starting token from the last ket exchange (`tok_at_T0`). "Exactly one token per sector" is not
    formalized (not needed for Theorem 4.2).

## Section 4.3 (TieBreak, Theorem 4.3)

20. Token transfer for agents with equal weight *and* equal bra is unspecified in the paper; we keep the
    token where it is. (If it were passed, e.g. always to the responder, an adversarial weakly fair
    scheduler could keep two tokens circulating among ≥3 agents with identical brakets forever; the
    output would still converge, but Lemma 8.4's "eventually only one holds the token" would fail.)
21. The proof of Lemma 8.4 claims "the maximum weight is obtained in `f(G_q)` because `G_1 ⊇ … ⊇ G_q`";
    this is true but needs an argument (an arc of `G_p` lies inside an arc of `G_q`, strictly shorter if
    its start is not in `G_q`): `w_add_of_closest`, `exists_key_gt`. Also needed and not in the paper: if no
    ket exchange ever happens, the initial configuration is stable, so all agents have the same color.
22. "3k² states with binary output" is not formalized.

## Section 5 (unordered setting: Ordering, Ord-Circles; Theorems 5.1, 5.2)

23. Colors are an arbitrary type `Col` with decidable equality only; labels are `Fin k`; we assume at most
    `k` colors occur (`(colors input).card ≤ k`; needed, implicit in the paper). `k = 1` handled separately.
24. **Orientation of weak fairness (ambiguity / clarification).** Section 2.1 models the population as a
    *directed* interaction graph `E ⊆ A × A`, so Def. 2.1 most naturally means ordered pairs; under that
    reading the results hold. The unordered-pair counterexamples below are clarifications of what the
    asymmetric protocols need, not errors. Ordering and Ord-Circles are asymmetric (in most rules only the
    initiator changes: a non-leader copies its leader's label, a pending agent re-initializes, only as
    initiator). With Def. 2.1 read for *unordered* pairs, both theorems fail:
    `ordering_not_weaklyFair` (k = 2, colors 0,0,1) and `ordCircles_not_weaklyFair` (k = 2, colors 0,0,1:
    agent 2 outputs 1 forever although 0 is the unique majority). They are proved for *ordered-pair*
    fairness (`Execution.OrderedFair`: every agent initiates with every other agent infinitely often):
    `ordering_correct`, `ordCircles_ordering` (Lemma 8.13), `ordCircles_correct` (Thm 5.2). Alternatively,
    the symmetrized protocols (`Protocol.symm`: apply `δ` in both role assignments) are correct under
    unordered weak fairness: `orderingSymm_correct`, `ordCirclesSymm_correct`. The same orientation issue
    affects the proofs of Lemmas 8.5 and 8.12 and of Theorem 5.1 ("copy").
25. **Proof gap in Lemma 8.11.** The lemma's statement (finitely many ordering-state changes) holds, but a
    step of its proof, "once a label is used by some leader it never becomes free again", is false: a
    label used only by leaders in state `I` left over from before leader stability can be freed (reachable
    for k = 3, colors 0,0,1,1; `tools/unordered/freed.py`). Finiteness of ordering-state changes still holds;
    the proof uses the labels of `U`-leaders, a cyclic-distance potential and a non-leader rank potential
    instead of the paper's `R`.
26. Steps (1)+(4) can change `U` into `U` with bra+1 within a single interaction, so "the ordering state
    changes finitely often" has to be read for the pair (ordering state, bra).
27. "Pending agents do not interact otherwise" must also exclude the Circles step (5) for an agent that
    became pending in step (4) of the same interaction; otherwise Invariant 3.3 (Lemma 8.9) breaks (model
    checker, even under ordered fairness).
28. Interpretation: Ordering follows the pseudocode of 8.6 literally; Ord-Circles steps (1)–(5) sequentially
    with `a` = initiator (`step1_eq_seq` shows our closed form of step (1) equals the sequential reading);
    re-initialization sets `⟨l|l⟩`, `os = U`, `out = ic`; the output copies the initial color of the
    diagonal agent. State counts: Ordering `|Col|·2·k ≤ 2k²`, Ord-Circles `≤ 8k⁴` (paper: `O(k⁴)`).

## Section 6 (Ranking, Theorem 1.2) — **the protocol as written is incorrect**

29. Interpretation: cases are the bullets of rules (2)–(7) in order, each tried as (initiator, responder)
    then (responder, initiator); the first (case, orientation) that changes something is applied; ranking
    increments are mod `k`; output = bra ranking. Rule 7b follows the formal bullet (no "𝔧, 𝔩 ≠ 0").
30. **Counterexample** (`Counterexample.literal_not_correct`, globally fair execution built explicitly):
    k = 2, three agents with colors 0,1,1 (all colors present, no tie). After 9 steps the configuration
    `⟨0,1|0,1⟩, ⟨1,0|1,0⟩*, ⟨1,1|0,1⟩*` is reached, which no interaction changes, and agent 2 outputs
    ranking 1 instead of 0. Cause: an agent holding the token of its *own* bra color cannot update its own
    bra ranking (rule (4) only updates *other* agents); Lemma 6.10's proof overlooks this. The literal
    protocol also fails for counts (1,2), (2,3), (3,2), (1,4) (k = 2) and (1,2,3) (k = 3), under all
    orientation readings (model checker, `tools/ranking/`).
31. **Fix**: after every interaction, an agent with a token and `bc = kc` sets `br := kr`. The fixed protocol
    is proved correct under global fairness: `ranking_correct` (Theorem 1.2, `2k⁴` states `card_RState`),
    via `final_closed` (Lemma 6.5), `reach_final` (Prop. 6.6), phases `phase1`–`phase5` (Lemmas 6.8–6.12,
    each by a decreasing measure instead of "follow Circles' fair stabilization sequence").
32. X (Def. 6.4) is closed only as a *set* of configurations: rule (6a) moves the top color's token between
    identical diagonal agents.
33. Note: Lemma 6.2 (backward direction) and Lemma 6.12 use the no-tie assumption, which is the standing
    assumption of Section 6 (Def. 6.1); Lemma 6.2 read without it fails (k = 2, counts (1,1)); Lemma 6.7(2) needs every color present (Def. 6.1). Indexing in the
    proof of Lemma 6.12 is off by one (ranks `0..ℓ−1` vs. "ℓ−1 most popular colors").
34. Remark 1 (unordered ranking) is not formalized.
