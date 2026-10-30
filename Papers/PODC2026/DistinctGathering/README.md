# Distinct Gathering under Round-Robin — PODC 2026

Fabian Frei, Koichi Wada. *Distinct Gathering and the Virtue of Self-Consistency.* PODC 2026, pp. 239–246. DOI
[10.1145/3796701.3815962](https://doi.org/10.1145/3796701.3815962). Formalized version: the 8-page proceedings
version. The announced full arXiv version (ref. [17], "arXiv:xxxx.xxxxx") could not be found, so the proceedings
version is all there is; it gives only proof sketches.

**Verdict: ⚠️ Minor statement issues.** The impossibility results are correct. Theorem 4 (no algorithm gathers 3
robots from distinct positions under Round-Robin) and Theorem 1 (no algorithm gathers `n ≥ 3` robots from arbitrary
positions, even with a shared unit length) are proved in Lean. Both are proved in a stronger form: they hold with
rigid movement and a common chirality too. The only statement-level slip is that Conjecture 3 is printed with
"Gathering" instead of "Distinct Gathering". In that form, Theorem 1 makes it vacuously true, so the claim
"we disprove both conjectures" fails for it as printed. The intended version is clear from the context.

## Mistakes in the paper

* **Conjecture 3 is misquoted, so it cannot be "disproved" as printed.** §3 states Conjecture 3 (after Défago et
  al., Conj. 1) as "every algorithm that solves *Gathering* under RoundRobin is a rapid-gathering algorithm". §1
  and §4.1 then say Theorem 5 disproves it. But by the paper's own Theorem 1, no algorithm solves Gathering under
  Round-Robin for any `n ≥ 3`. So the conjecture as printed is vacuously true for every `n ≥ 3` and cannot be
  disproved. The intended reading is clear: the sentence before it speaks of "any algorithm solving this
  problem", meaning Distinct Gathering, and Definition 5 starts from distinct positions. This is a typo with
  evident intent. For `n = 3` the intended version holds vacuously by Theorem 4, which agrees with the paper's
  remark "confirming Conjectures 2 and 3 in this case". We did not check the disproof for `n ≥ 4`; it rests on
  Theorem 5 together with Défago et al., Thm. 16. (`conjecture_3_as_stated`, `conjecture_3_distinct_three`)
* **Theorem 4 has only a sketch, but a short complete proof exists, and it works under rigid movement.** The paper
  defers the rigorous proof to the full version. Its sketch mentions the last 3→2-point transition and "the fact
  that the algorithm does not revert to a three-point configuration multiple times". Our proof is short and does
  not need non-rigid movement.
  (1) The step that first gathers is a lone robot jumping onto the point of the other two. The adversary can
  rotate and scale every two-point view to the same view `{0, w}`, so *every* robot seeing a two-point
  configuration jumps onto the other point.
  (2) Robots starting at distinct positions must eventually collide. So in some distinct configuration `C`, some
  robot `x` jumps exactly onto some robot `y`.
  (3) Start from `C` with the Round-Robin order `x, y, z`. After `x` joins `y`, the activated robot is always
  accompanied, and the robots swap between the two points forever.
  The theorem is true as stated; this is not an error, only a missing proof. (`theorem_4`)

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/Computability/Distributed/MobileRobots/Model.lean`, namespace `Cslib.MobileRobots`).
* `n` point robots in the plane `ℂ`. They are oblivious, anonymous and uniform, and the algorithm is
  deterministic. An algorithm is any function from the snapshot to a trajectory (`Finset ℂ → (ℝ → ℂ)`, target =
  value at 1). The snapshot is the *set* of robot positions in the robot's local frame, with the robot at the
  origin, so there is no multiplicity detection.
* **Variable disorientation:** at every activation an adaptive adversary picks the frame, a similarity
  `v ↦ a·v` or `v ↦ a·conj v` with `a ≠ 0` (scale, rotation, mirror). The theorems take a frame restriction
  `frameOK`. Theorem 4 needs only that all orientation-preserving similarities are allowed. Theorem 1 needs only
  that all rotations with the true unit length are allowed.
* **Scheduler:** centralized, one robot per step, so each Look-Compute-Move cycle is atomic. `IsRoundRobin` means a
  fixed order of all `n` robots, repeated forever; every order is allowed.
* **Movement:** an abstract `Movement` model fixes which stopping points the adversary may choose. The only
  requirement is that reaching the target is always allowed. Instances are `Movement.rigid` and
  `Movement.nonrigid δ`: stop at any point once the travelled arc length (`eVariationOn`) is at least `δ`.
  Both impossibility theorems hold for *every* movement model, which covers the paper's default (non-rigid,
  with `δ` known or unknown).
* **Problem:** `Solves n A sched frameOK M init` means every legal execution from an initial configuration
  satisfying `init` eventually stays gathered. Gathering uses `init = True`; Distinct Gathering uses
  `init = Injective`. The counterexample executions never gather, not even for a moment.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (Gathering impossible, `n ≥ 3`, even with a consistent unit length) | `theorem_1` (unit length), `theorem_1_default`, `theorem_1_general` | `Impossibility.lean` |
| Theorem 4 (Distinct Gathering impossible, `n = 3`, default model) | `theorem_4`; with common chirality `theorem_4_chiral`; general `theorem_4_general` | `Impossibility.lean` |
| Conjecture 2 holds for `n = 3` (§4.1) | `conjecture_2_three` | `Conjectures.lean` |
| Conjecture 3 as printed is vacuous for `n ≥ 3`; the intended version holds for `n = 3` | `conjecture_3_as_stated`, `conjecture_3_distinct_three` | `Conjectures.lean` |
| §4.1: a distinct `n ≥ 3` configuration must pass through a three-point configuration before gathering | `exists_three_point` | `Conjectures.lean` |
| §1/§3: gathering `n = 2` robots is trivial (move toward the other robot; Défago et al., Lem. 4) | `twoAlg_solves_nonrigid`, `twoAlg_solves_rigid`, `distinctGathering_two_solvable` | `TwoRobots.lean` |

Proof ingredients are in `TwoPoint.lean`. `exists_fixed_view` shows that some view `{0, w}` is answered by jumping
onto the other point. `step_normFrame` covers the normalizing frames. `run_cycle` is the swapping execution, with
the closed form "robot `σ i` is at `v` at time `t` iff `[i = 1] xor [⌊t/n⌋ odd] xor [i < t mod n]`".

**Not formalized.** Theorem 5 (`n ≥ 4`, the nine-phase algorithm) and Theorems 6 and 7 (`n = 3` with a
self-consistent unit length or compass). Their algorithms and proofs appear only in the unavailable full
version.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity check: `twoAlg` solves (Distinct) Gathering of two robots in the full default model (variable
disorientation, non-rigid movement with unknown `δ > 0`, any schedule), so `Solves` is satisfiable. The robot
model is new; it is staged in `Podc/` as a CSLib candidate (`-- CSLib candidate` header).
