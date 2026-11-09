# Differences between the formalization and the paper

Paper: Nisan, Schapira, Valiant, Zohar, *Best-Response Mechanisms* (ICS 2011, full version; PODC 2011 brief
announcement *Incentive-compatible distributed greedy protocols*). Numbering follows the full version.

## Section 2 (framework, Theorem 2.7)

### Mistakes

- 🔧 **Theorem 2.7 (2), number of rounds.** The theorem claims incentive compatibility for every activation order with
  at least `T = e_G` rounds. False: `Counterexamples.theorem_2_7_false` (4 players, binary strategies, strict utilities,
  `e_G = 2`, clear outcome; after 2 rounds of round robin the deviator ends with utility 2 instead of 1). Under the
  alternative reading of Definition 2.4 with one player per elimination step, `Counterexamples.theorem_2_7_false_single_steps`
  (`e_G ≤ 4`, deviation pays after 4 rounds). The proof shows that the deviator `i` is confined after `tᵢ` rounds, `tᵢ`
  being the index of the clear-outcome witness for `i`, and `tᵢ` can exceed `e_G`. Repair (proved):
  `theorem_2_7_incentive_compatible` with `≥ max(e_G, tᵢ)` rounds; `informal_theorem`: `Σᵢ|Sᵢ| - n` rounds (the bound of
  the informal theorem of Section 1.3, which is correct) via `ClearWitness.exists_short`.
- 🔧 **Extension (1) after Theorem 2.7 (outdated information).** With the paper's definition of a round ("each player
  is active at least once"), convergence fails when best responses are computed from outdated information:
  `Counterexamples.outdated_information_false` (every player best-responds at every step, to information from time 0;
  the run never converges). Repair (proved): rounds measured by information freshness, `AsyncRounds` (from the end of
  round `k+1` on, every current strategy is a best response to information produced since the start of round `k+1`);
  `converges`, `deviator_utility_le`.
- ✏️ **Remark after Definition 2.3** ("elimination of NBR strategies has a unique order-independent outcome, that is a
  pure Nash equilibrium"). False for infinite strategy spaces, which the paper explicitly allows:
  `Counterexamples.nbr_outcome_not_unique` (one player, `S = ℕ`, `u(x) = x`: every `x` is a one-step outcome and none is
  an equilibrium). True when tie-broken best responses exist (`HasBR`; automatic for finite games with strict total
  orders, `hasBR_of_finite`): `Solves.unique`, `Solves.isNash`. Every best-response mechanism presupposes `HasBR`
  (implied assumption).

### Modelling choices and imprecisions

- **Ex post, one realization.** Incomplete information enters only through "for every realization of `(u₁,…,uₙ)`".
  We fix one realization: a `TieBreakGame` (utilities and tie-breaking orders); all theorems are for an arbitrary game,
  hence for every realization. Uncoupledness of tie-breaking (it may depend only on `uᵢ`) plays no role in the proofs.
- **Utilities** take values in an arbitrary linear order `R` (paper: reals); the `lim sup` version uses `ℝ` and assumes
  utilities bounded below (needed for `lim sup` in `ℝ` to be meaningful; true in finite games).
- **Tie-breaking** (Def. 2.1, "a full order"): the definitions take an arbitrary relation `prec`; total strict order is
  assumed only where needed (`hasBR_of_finite`). Def. 2.2 is literal (`u(sᵢ) < u(s'ᵢ) ∨ (= ∧ sᵢ ≺ s'ᵢ)`).
- **Subgames** are products of strategy sets; an elimination step removes, simultaneously for any set of players,
  strategies that are NBR in the current subgame (Def. 2.4's "removal of sets of NBR strategies"). NBR is evaluated
  in the current subgame (both the opponents' profiles and the beating strategy range over the subgame), as in the paper.
- **Clear outcome** (Def. 2.6): `ClearWitness s i E r k` asks for an index `k` with `E k i = Sᵢ` and `s` globally optimal
  for `i` in `E k`; the paper takes `k` = first step that eliminates a strategy of `i`. Equivalent: optimality is
  inherited by smaller subgames (`ClearWitness.of_le`). The order must end at `s*` (the paper: "order of elimination",
  which in finite games always ends at `s*`).
- **Globally optimal** (Def. 2.5) is relative to the current subgame, as the paper uses it.
- **Best-response mechanism.** `Mechanism` = starting profile + adaptive activation rule (a set of active players,
  possibly several, as a function of the whole history). A repeated-game strategy of a player maps histories to
  announcements; the best-response strategy announces `br i (current profile)` for a fixed tie-broken best-response
  selection `br` (`IsBRRule`). Total utility: last-stage utility at a horizon `N` (`IsIncentiveCompatible`), or
  `lim sup` (`theorem_2_7_limsup`). IC = repeated best response is a pure Nash equilibrium of the repeated game, quantified
  over all repeated-game strategies of the deviator (any history dependence).
- **Rounds** (`HasRounds`): consecutive windows `[T k, T (k+1))` in each of which every player is active, with `T m ≤ N`.
  Since activation may be adaptive, the round count is a hypothesis on every run (`∀ σ, HasRounds (M.acts σ) N m`); for
  round robin it holds for all runs (`roundRobin_hasRounds`).
- **Extension (3)** (stop when all players pass) is formalized statically: a profile where all pass is `s*`
  (`eq_of_all_pass`), and a profile where all players but `i` pass gives `i` at most `uᵢ(s*)` (`utility_le_of_others_pass`);
  no round bound is needed for it.
- **Extension (2)** (adaptive orders) is built into `Mechanism.active` and the per-run `AsyncRounds`.
- **Proof of Theorem 2.7.** Convergence: as in the paper, via the survival of tie-broken best responses
  (`IsElimSeq.mem_of_isBR`), stated for an arbitrary NBR sequence of length `r` (paper: `r = e_G`). IC: the paper's
  argument ("after `tᵢ − 1` rounds the game is effectively `G_{tᵢ}`") is correct for `tᵢ` rounds (`deviator_utility_le`);
  only the final round count is wrong (see above).
- The paper's examples: Figure 1 (`figure_1`: NBR-solvable, not IC with round robin), Figure 3 (`figure_3`: NBR-solvable
  with clear outcome, both players prefer `(C, C)`; collusion-proofness is not defined formally beyond this example).
- Section 4 (collusion-proofness of the applications) and Section 3.4 (TCP games, Theorem 3.9) are not formalized.

## Section 3.2 (cost sharing, Theorems 3.3, 3.4)

- ✏️ **Tie-breaking rule** "if `|s − vᵢ| ≤ |t − vᵢ|` then `t ≺ᵢ s`" is reflexive, so by Def. 2.2 every bid is NBR in
  every subgame (`gameLit_isNBR`) and every profile is a one-step outcome (`gameLit_solves`). Repaired to "strictly closer
  to `vᵢ` wins; at equal distance the lower bid wins" (`Closer`, a strict total order).
- 🔧 (proof gap, statement true) **`e_G ≤ n`**: the paper's elimination has 3 steps, so it only gives `e_G ≤ 3`; for
  `n = 1, 2` we give separate sequences (`elimParam_le_card`).
- The serviced set is defined as the union of all feasible sets; `serviced_unique_maxCard` shows it is the unique
  maximum-cardinality feasible set, so the paper's lexicographic tie-breaking among such sets never applies.
- The paper's `vᵢ > 0` is not needed. Cost shares are `ℝ≥0`-valued, cross-monotonic (`CostSharingRule`).
- "Reasonable cost shares as in the Moulin mechanism": Moulin's mechanism (iteratively drop users with `vᵢ < cᵢ(S)`) is
  formalized (`moulinSet`); `moulinSet_eq` shows its set is the serviced set at `b = v`; the outcome `s*` services exactly
  that set and charges `cⱼ(R_v) ≤ vⱼ` (`theorem_3_3`).
- Clear outcome: the player-specific order is ours (others first drop bids above their values; then `s*` is optimal for
  `i`, witness index 1, `clearWitness`); the paper's description of this order is garbled but the idea is the same.
- Theorem 3.4: the mechanism's bid rule is a tie-broken best response (`isBR_mechBid`); the round-robin mechanism with
  `n²` steps (`n` rounds) is IC and outputs `s*` (`Applications.theorem_3_4`), via the corrected Theorem 2.7
  (`e_G ≤ n`, witness index `1 ≤ n`).

## Section 3.1 (stable roommates, Theorems 3.1, 3.2)

- ✏️ (implied assumption) **Theorem 3.1, intern–hospital case.** The paper's game lets every student propose to every other student
  (`Sᵢ = {j ≠ i}`), and intern–hospital markets are "the special case where all hospitals have the same ranking of
  interns". Such markets need not be cycle-free (interns may rank interns cyclically), and the theorem fails:
  `internHospital_counterexample` (3 interns with cyclic preferences, 1 hospital ranked last by everybody): not
  cycle-free, not NBR-solvable for any irreflexive tie-breaking, no stable matching (engine:
  `subset_elimSeq_of_isBR`, `not_nbrSolvable_of_isBR`: a product subgame in which every strategy is a best response to
  something survives every elimination). Repair (proved): bipartite strategy spaces (interns propose to hospitals and vice
  versa), `cycleFree_of_bipartite`, `theorem_3_1_internHospital`; this is what the paper's cycle argument ("any cycle
  must include a hospital placed after a desired intern and before a less desired one") presupposes.
  Labeled ✏️ rather than 🔧 (review): intern–hospital matching is bipartite by definition (interns have no
  preferences over interns), the counterexample uses intern–intern preferences, and the paper's proof presupposes the
  bipartite structure.
- ✏️ **"G's unique PNE"**: for an odd number of students the last student has all strategies at utility 0, and there
  are several PNEs (`exists_two_nash`, a 3-student correlated market). The PNE is unique only *under tie-breaking*
  (`theorem_3_1`: the outcome of every NBR elimination), and all PNEs found have the same matching (not formalized in
  general).
- 🔧 (proof gap) **Clear outcome.** Theorem 3.1 does not state, and the proof does not argue, that the outcome is a clear
  outcome, which Theorem 3.2 needs; it holds with the same elimination sequence (`theorem_3_1`, `clearWitness_of_good`).
- Model: acceptability relation `acc` (symmetric, irreflexive; paper: `acc = (≠)`), ranks `α i j > 0` injective on
  acceptable partners (paper: ranks `1, 2, …`; only order and positivity matter). Utility exactly as in the paper
  (footnote 5's game). The matching of a profile = mutual proposals (`matchingOf`); stability: no acceptable pair
  preferring each other to their matches, unmatched = worst.
- `CycleFree` follows the paper but quantifies only over cycles of *distinct* students (a weaker hypothesis, so a
  stronger theorem).
- Correlated markets: weights `w` symmetric with values in any linear order, ranks order-compatible with `w`
  (`cycleFree_of_correlated`, `theorem_3_1_correlated`).
- `e_G ≤ n`: our sequence fixes a pair (or a student without acceptable partners left) per step, `≤ n` steps.
- Theorem 3.2: the announcement rule ("most preferred student to whom I can make a better offer") is a tie-broken best
  response whenever a better offer exists (`mechanism_isBR`); when none exists the paper leaves the announcement
  unspecified, so Theorem 3.2 is stated for any tie-broken best-response rule (`Applications.theorem_3_2`: round robin,
  `n²` steps, IC, final matching stable). The mechanism's output (pairs announcing each other) is `matchingOf`.

## Section 3.3 (BGP, Theorems 3.5, 3.6)

- ✏️ **Theorem 3.6 omits "No Dispute Wheel"**, which the proof uses ("which we assumed is not contained in the graph")
  and the surrounding text states. Without it the theorem is false: BAD GADGET has no pure Nash equilibrium, hence is
  not NBR-solvable (`badGadget_noNash`, `badGadget_noNash'`, `badGadget_not_NBRSolvable`).
- ✏️ **Connectivity** of the graph is implicit (a node without any route has all actions at utility 0: ties); assumed.
- 🔧 (proof gap) **"If no such node exists, a₀ can guarantee its most preferred route."** Not as stated: downstream
  unfixed nodes on `R₀` may deviate. It is the *last* unfixed node on `R₀` that can guarantee its route. Our
  `exists_guarantee` takes `a_{j+1}` := last unfixed node on `R(a_j)` and derives a dispute wheel from a cycle.
- Model: `SimpleGraph V`, destination `d`, players = `{v // v ≠ d}`, strategies = neighbours; the route of `i` under `f`
  follows next hops and exists iff `d` is reached without repetition; ranks positive and injective on simple routes
  (paper: ranks `1, 2, …`). A dispute wheel requires pivots `≠ d` and `RᵢQᵢ₊₁` to be a simple route (rankings are only
  defined on simple routes); this makes `NoDisputeWheel` weaker and the theorem stronger.
- All eliminations are strict, so Theorem 3.6 holds for every tie-breaking rule, and the PNE is unique outright
  (`theorem_3_6`); "stable routing tree" = every node has a route (`IsRoutingTree`) and the profile is a PNE.
- Theorem 3.5 ([7]) is derived from Theorems 3.6 and 2.7 (corrected) for best-response mechanisms with `≥ n` rounds
  (`Applications.theorem_3_5`); the asynchronous, outdated-information BGP model of [7] is covered by `AsyncRounds`
  (`converges`, `deviator_utility_le`) with rounds defined by information freshness.

## Not formalized

- Section 3.4 (TCP games, Theorem 3.9; Theorems 3.7, 3.8 are cited from [5]).
- Section 4 (collusion-proofness of the stable-roommates, BGP and TCP mechanisms); only Figure 3's example.
