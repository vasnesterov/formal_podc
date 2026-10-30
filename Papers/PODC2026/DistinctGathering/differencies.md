# Differences between the formalization and the paper

Source: PODC 2026 proceedings version (8 pages). The full arXiv version announced as ref. [17] was not found.
All proofs in the paper are sketches. The Lean proofs of Theorems 1 and 4 are our own; they follow the ingredients
of the sketches.

## Statement-level issues (verdict rules from `verdicts.md`)

1. **Conjecture 3 is printed with "Gathering"** (§3: "Every algorithm that solves Gathering under RoundRobin is a
   rapid-gathering algorithm"). §1 and the end of §4.1 claim that the paper disproves it. As printed, it is
   vacuously true for every `n ≥ 3` by the paper's own Theorem 1 (`conjecture_3_as_stated`), so it cannot be
   disproved. The intended version is "Distinct Gathering": the preceding sentence says "any algorithm solving this
   problem" about Distinct Gathering, and Definition 5 uses distinct initial configurations.
   Rule: **R3** (typo with evident intent; local fix) → ⚠️.
   Borderline: this misquotes a *conjecture*, and the paper never states it as a theorem. We still count
   "we disprove both conjectures" as an explicit claim of a result (R1), so the label is ⚠️ rather than ✅.
   We did not check the disproof of the intended version for `n ≥ 4`. It needs Theorem 5 plus Défago et al.,
   Thm. 16 (rapid-gathering algorithms cannot solve Distinct Gathering), and neither is formalized.

No other checked statement has an issue. Theorems 1 and 4, the `n = 2` claim and the three-point remark are true
as stated.

## Proofs

2. **Theorem 4: only a sketch in the paper; full proof supplied.** The sketch says to consider the last transition
   from a 3-point to a 2-point configuration, normalized views, and `I′` as an alternative initial configuration
   with another schedule. It also uses "the fact that the algorithm does not revert to a three-point configuration
   multiple times". Our proof uses the same ingredients but needs no claim about non-reversion:
   * `exists_fixed_view`: a gathering execution contains a step where a lone robot lands on the other point. Its
     view is `{0, w}` for some `w ≠ 0`, and the algorithm maps `{0, w}` to `w`.
   * The adversary rotates and scales every two-point view to `{0, w}`, using frames
     `Frame.ofCoef (w / (other − self))`. So every activated robot in a two-point configuration jumps onto the
     other point (`step_normFrame`).
   * `exists_merge`: otherwise distinct configurations would stay distinct forever. So in some distinct `C`, some
     robot `x`, with some frame, lands exactly on another robot `y`.
   * From `C` with the order `x, y, z`, the robots swap sides forever, and the activated robot is always
     accompanied (`run_cycle`, `cfg_not_gathered`).
   This is a complete proof of a true statement, not a repair.
3. **Theorem 1:** our proof follows the paper's re-proof. In the Lean version the robot alone at the start is
   `σ 1` and the order is `σ 0, σ 1, …`; the paper uses `r1` alone and the order `r2, r1, r3, …`, which is the same
   up to relabelling. We use the rigid execution with the global frame to find the two-point configuration `I′`.
   The paper takes it from an arbitrary execution, which makes no difference.

## Modelling choices

4. **Plane = `ℂ`; frames = similarities** `v ↦ a·v` or `v ↦ a·conj v`. "Arbitrarily scale, rotate and mirror upon
   each activation" (variable disorientation) is `frameOK = True`. A consistent unit length is
   `Frame.UnitLength` (`‖a‖ = 1`); a common chirality is `Frame.Chiral`.
5. **Strengthenings.** Theorem 4 is proved for every frame class that contains all orientation-preserving
   similarities, so it also holds with a common chirality (`theorem_4_chiral`). Theorem 1 is proved for every
   frame class that contains the unit-length rotations (consistent unit length plus chirality). Both are proved for
   *every* movement model in which a robot may reach its target, rigid included. The paper's default assumption is
   non-rigid movement; impossibility under rigid movement is stronger, because the non-rigid adversary may always
   choose not to stop a robot.
6. **Algorithms** are deterministic functions `Finset ℂ → (ℝ → ℂ)`: snapshot → trajectory, target = value at 1.
   We put no continuity or "starts at the origin" condition on trajectories. For impossibility results this
   quantifies over more algorithms and is therefore stronger. Randomized algorithms are not considered; the paper
   does not consider them either.
7. **Snapshot** = the `Finset` of positions in local coordinates, so multiplicities are invisible, including at the
   robot's own location. This matches "No Multiplicity Detection".
8. **Scheduler.** Centralized: one robot per step, and its Look-Compute-Move cycle is atomic.
   `IsRoundRobin act` = `act` is `n`-periodic and injective on `[0, n)`, i.e. a fixed order of all robots repeated
   forever. This matches Definition 3, including that the order is unknown to the robots.
9. **Adversary.** Adaptive: it picks the frame and the stopping point from the step number and the current
   configuration. `Legal` restricts its choices only along the execution. The counterexample executions use a
   frame sequence that could be fixed in advance.
10. **Non-rigid movement** (`Movement.nonrigid δ`): the robot may be stopped at parameter `s` once the arc length
    of its global trajectory on `[0, s]` (`eVariationOn`) is at least `δ`. All robots share one `δ`; the paper uses
    a common `δ` for lower bounds. The impossibility theorems do not depend on this definition. It is used only for
    the positive `n = 2` result.
11. **Solving** = every legal execution eventually stays gathered forever (Definition 1: "all robots stay co-located
    in a single point"). The counterexamples never gather, not even for a moment.
12. **Definition 5 (rapid-gathering)** leaves the adversary unspecified. We use the weakest reading (`∃` a legal
    adversary). The vacuity results do not depend on this choice.
13. **`n = 2` claim.** The paper states it for Round-Robin (citing Défago et al., Lem. 4). We prove it for every
    centralized schedule, from every initial configuration, with variable disorientation and non-rigid movement
    with unknown `δ > 0`, using straight moves toward the other observed point.

## Not formalized

14. Theorem 5 (algorithm for `n ≥ 4`), Theorems 6 and 7 (`n = 3` with a self-consistent unit length or compass),
    and the "paradox" discussion. Their algorithms and proofs are only in the unavailable full version.
