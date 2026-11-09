# Best-Response Mechanisms — PODC 2011

Noam Nisan, Michael Schapira, Gregory Valiant, Aviv Zohar. *Brief announcement: Incentive-compatible distributed greedy
protocols.* PODC 2011. DOI [10.1145/1993806.1993871](https://doi.org/10.1145/1993806.1993871). Formalized version: the
full version *Best-Response Mechanisms* (ICS 2011, 12 pp., author copy https://www.cs.yale.edu/homes/schapira/BRM.pdf);
numbering follows it. The brief announcement has no proofs.

**Verdict: 🔧 Easy fix.** The main theorem (Theorem 2.7) holds with a different round bound. Best-response mechanisms for
NBR-solvable games with a clear outcome converge within `e_G` rounds, but incentive compatibility needs more rounds than
`e_G`. The bound of the paper's own informal theorem, `Σᵢ|Sᵢ| − n`, is enough. The outdated-information extension needs
rounds counted by how fresh the information is. The applications hold: stable roommates (correlated markets, and
intern–hospital markets once proposals are bipartite, as intern–hospital matching means), cost sharing and BGP (with
its missing No-Dispute-Wheel hypothesis restored), and so does the incentive compatibility of their mechanisms. TCP games
(Section 3.4) and Section 4 were not checked.

## Mistakes in the paper

### 🔧 Theorem 2.7 (2) (incentive compatibility after `e_G` rounds)
With exactly `e_G` rounds the best-response mechanism need not be incentive compatible. In a 4-player game with binary
strategies, strict utilities, `e_G = 2` and a clear outcome, a player who never best-responds ends 2 rounds of round
robin with utility 2 instead of 1 (`Counterexamples.theorem_2_7_false`).

**Impact.** Local: the theorem holds with `max(e_G, tᵢ)` rounds, where `tᵢ` is the step of the clear-outcome order at
which `i` is first restricted. It also holds with the `Σᵢ|Sᵢ| − n` rounds of the informal theorem in §1.3. The mechanisms
of Section 3 run `n` rounds, which is enough for all of them.

**Details.** The deviator `i` is confined to the subgame `G_{tᵢ}` of its player-specific elimination order only after
`tᵢ` rounds, and `tᵢ` can exceed `e_G`. In the example, `i` has the dominant strategy `0`. Player `k` plays `1` iff
`i = 1` and `j₂ = 1`, `j₂` copies `j₁`, and `j₁` has the dominant strategy `0`. The fast elimination uses `i`'s
dominance to fix `k` in two steps. Player `i`'s own clear-outcome order must first fix `j₁`, `j₂` and `k` (`tᵢ = 3`).
Started at `(1,1,1,1)` with order `i, k, j₂, j₁`, the deviation keeps `k = 1` for two rounds, so `(i,k) = (1,1)` gives
`i` utility 2. If Definition 2.4 is read as "one player per step", `e_G = 4` there. A second game with a 6-step
"ladder" defeats that reading as well, since the deviation still pays after 4 rounds
(`Counterexamples.theorem_2_7_false_single_steps`).

**Repair.** `theorem_2_7_incentive_compatible` proves the theorem with `≥ max(r, tᵢ)` rounds in every run. It covers
adaptive activation orders and simultaneous moves. `theorem_2_7_limsup` gives the `lim sup` version.
`informal_theorem` proves it with `Σᵢ|Sᵢ| − n` rounds, using `ClearWitness.exists_short`.

### 🔧 Theorem 2.7, extension (1) (outdated information)
With outdated information, "a round = every player is active at least once" does not give convergence. In a two-step
game, every player can best-respond at every step to information from time 0, and the run never converges
(`Counterexamples.outdated_information_false`).

**Impact.** Local: rounds must be counted by how fresh the information is. Then both convergence and the
incentive-compatibility bound hold.

**Repair.** `AsyncRounds`: from the end of round `k+1` on, every current strategy is a best response to information
produced in round `k+1` or later. Under it, `converges` proves Theorem 2.7 (1) and `deviator_utility_le` proves the core
of Theorem 2.7 (2). Both allow simultaneous moves, outdated information and adaptive orders.

### ✏️ Slips
- Theorem 3.6 omits the hypothesis "No Dispute Wheel". The proof and the text use it, and without it the theorem is
  false: BAD GADGET has no pure Nash equilibrium, so it is not NBR-solvable (`BGP.badGadget_not_NBRSolvable`). Connectivity
  of the network is also implicit.
- Remark after Definition 2.3: "NBR elimination has a unique order-independent outcome, a PNE". This fails for infinite
  strategy spaces, which the paper allows. With one player, `S = ℕ` and `u(x) = x`, every `x` is a one-step outcome and
  none is an equilibrium (`Counterexamples.nbr_outcome_not_unique`). The remark holds when tie-broken best responses
  exist, as every best-response mechanism presupposes (`Solves.unique`, `Solves.isNash`).
- §3.2 tie-breaking "if `|s − vᵢ| ≤ |t − vᵢ|` then `t ≺ᵢ s`" is reflexive. Under Definition 2.2 every bid is then NBR in
  every subgame (`CostSharing.CostSharingRule.gameLit_isNBR`, `gameLit_solves`). We repaired it to "strictly closer wins,
  and at equal distance the lower bid wins".
- Theorem 3.1, intern–hospital matchings: the paper's game lets every student propose to every other student, so
  interns may rank interns. With three interns ranking each other cyclically and one hospital, the market is not
  cycle-free, not NBR-solvable, and has no stable matching (`StableRoommates.internHospital_counterexample`). This is
  an implied assumption: intern–hospital matching is bipartite, and the paper's cycle argument ("any cycle must
  include a hospital placed after a desired intern and before a less desired one") assumes it. With bipartite proposals
  the case is cycle-free and Theorem 3.1 holds (`theorem_3_1_internHospital`).
- Theorem 3.1 "G's unique PNE": for an odd number of students the PNE is unique only under tie-breaking. A 3-student
  correlated market has two PNEs (`StableRoommates.exists_two_nash`).

## Proof gaps (statements true)

### 🔧 Theorem 3.6 (BGP, finding a node that can guarantee its route)
"If no such node exists, `a₀` can guarantee its most preferred route" is wrong as stated: unfixed nodes further down
`R₀` may still deviate.

**Impact.** Statement true (with No Dispute Wheel and connectivity). The last unfixed node on `R₀` can guarantee its route
(`BGP.exists_guarantee`, `BGP.theorem_3_6`).

### 🔧 Theorem 3.3 (`e_G ≤ n`)
The paper's elimination has 3 steps, so it gives `e_G ≤ 3`, which says nothing for `n ≤ 2`.

**Impact.** Statement true. The cases `n = 1, 2` have separate sequences (`CostSharing.CostSharingRule.elimParam_le_card`).

### 🔧 Theorems 3.1/3.2 (clear outcome)
Theorem 3.1 neither states nor proves that the stable-roommates outcome is a clear outcome, which Theorem 3.2 needs.

**Impact.** Statement true. The same elimination sequence witnesses it (`StableRoommates.theorem_3_1`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Game theory, no network model. The theorems are ex post, so we fix one realization of the private utilities: a
  normal-form game `TieBreakGame ι S R` with arbitrary strategy types, utilities in a linear order and tie-breaking
  relations (`Podc/Foundations/GameTheory/NeverBestResponse.lean`). Definitions 2.2–2.6 are literal. Subgames are
  products, and an elimination step removes NBR strategies of any set of players at once.
* Dynamics, first form: arbitrary runs with `AsyncRounds`. This covers sequential, simultaneous, adaptive and
  outdated-information activations.
* Dynamics, second form: a repeated-response mechanism (`Mechanism`) with a start profile and an activation rule that
  depends on the whole history. A player's repeated-game strategy maps histories to announcements. The best-response
  strategy announces `br i (current profile)` for a tie-broken best-response rule `br`.
* Incentive compatibility means that repeated best response is a pure Nash equilibrium of the repeated game, against
  every history-dependent deviation. Total utility is the last-stage utility at a horizon (`IsIncentiveCompatible`), or
  the `lim sup` (`theorem_2_7_limsup`). No randomness.
* The "pass" termination rule (extension 3) is checked statically, with no round bound needed: `eq_of_all_pass`,
  `utility_le_of_others_pass`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Defs. 2.1–2.6 | `Cslib.GameTheory.TieBreakGame.{IsNBR, Solves, NBRSolvable, elimParam, GloballyOptimal, HasClearOutcome}` | `Podc/Foundations/GameTheory/NeverBestResponse.lean` |
| Remark after Def. 2.3 (with best responses) | `Solves.unique`, `Solves.isNash`, `hasBR_of_finite` | same |
| Remark after Def. 2.4 (`e_G ≤ Σ\|Sᵢ\| − n`) | `Solves.exists_short` | same |
| Thm 2.7 (1), all extensions | `converges`, `theorem_2_7_convergence` | `Mechanism.lean` |
| Thm 2.7 (2), corrected | `deviator_utility_le`, `theorem_2_7_incentive_compatible`, `theorem_2_7_limsup`, `utility_le_of_others_pass` | `Mechanism.lean` |
| Informal theorem of §1.3 | `informal_theorem` | `Mechanism.lean` |
| Thm 2.7 (2) with `e_G` rounds: **false** | `theorem_2_7_false`, `theorem_2_7_false_single_steps` | `Counterexamples.lean` |
| Extension (1), plain rounds: **false** | `outdated_information_false` | `Counterexamples.lean` |
| Figures 1, 3 | `figure_1`, `figure_3` | `Counterexamples.lean` |
| Thm 3.1 (cycle-free; correlated; bipartite intern–hospital) | `StableRoommates.theorem_3_1`, `theorem_3_1_correlated`, `theorem_3_1_internHospital` | `StableRoommates.lean` |
| Thm 3.1, intern–hospital in the paper's game: **false** | `StableRoommates.internHospital_counterexample` | `StableRoommates.lean` |
| Thm 3.2 | `StableRoommates.theorem_3_2`, `mechanism_isBR` | `Applications.lean`, `StableRoommates.lean` |
| Thm 3.3 | `CostSharing.CostSharingRule.theorem_3_3`, `moulinSet_eq`, `clearWitness` | `CostSharing.lean` |
| Thm 3.4 | `CostSharing.CostSharingRule.theorem_3_4`, `isBR_mechBid` | `Applications.lean`, `CostSharing.lean` |
| Thm 3.6 (with No Dispute Wheel) | `BGP.theorem_3_6` (unique PNE for every tie-breaking) | `BGP.lean` |
| Thm 3.6 without No Dispute Wheel: **false** | `BGP.badGadget_noNash`, `BGP.badGadget_not_NBRSolvable` | `BGP.lean` |
| Thm 3.5 ([7]) | `BGP.theorem_3_5` | `Applications.lean` |

Theorem 3.6 needs no tie-breaking, since all its eliminations are strict. Theorem 3.3 does not need `vᵢ > 0`.

**Not formalized.** Section 3.4 (TCP games, Theorem 3.9) and Section 4 (collusion-proofness of the applications). Only
Figure 3 is formalized from Section 4.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
counterexamples on concrete finite games are checked with `decide`. Hypotheses are shown satisfiable: the
counterexample games satisfy every hypothesis of Theorem 2.7, `equalSplit` is a cross-monotonic cost-sharing rule, a
3-student correlated market satisfies Theorem 3.1, and `BGP.fin2_noDisputeWheel` gives a network without dispute
wheels. The generic NBR-elimination library is staged in `Podc/Foundations/GameTheory/NeverBestResponse.lean` (CSLib
candidate).

CSLib candidates (marked `-- CSLib candidate`):
- the whole `NeverBestResponse.lean`;
- `CostSharing.elimStep_of_isBR`, `CostSharing.elimParam_le`;
- `StableRoommates.{subset_elimSeq_of_isBR, not_nbrSolvable_of_isBR, exists_max_of_isStrictTotalOrder}`;
- `BGP.{isChain_imp_of_mem, exists_split_last}`.
