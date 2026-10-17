import Papers.PODC2026.ContentObliviousCounting.BitSending
import Cslib.Computability.Distributed.ContentOblivious.Splice
import Cslib.Computability.Distributed.ContentOblivious.Staged
import Mathlib

/-!
# Theorem 17 with a relay leader: composing two rounds gives wrong outputs

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026 (arXiv 2603.28260), Lemma 16 / Theorem 17: "the combined execution of
CCWBitSending/CCWBitRelay has the composable ending property", explicitly also when the leader is a
relay ("If the leader is a CCWBitRelay it will be the last process to terminate"; lines 2–3 and 6
of Algorithm 8 exist only for a relay leader). By Theorem 9 it could then be followed by any
procedure.

Counterexample: ring of 3 processes, process `0` is the leader and a relay, processes `1` and `2`
are active. Every process runs two CCW bit rounds back to back (round 1: both active processes
send `⊥`; round 2: process `1` sends `0`, process `2` sends `⊥`). Process `2`'s clockwise active
neighbour is `1`, so it should obtain `[⊥, 0]`. There is an execution (16 deliveries) that ends in
a final, quiescent configuration in which process `2` has obtained `[0, ⊥]`: the relay leader,
still in round 1, consumes a round-2 pulse of process `1`, which then is counted as part of round 1.
Each round alone is correct (`BitSending.returns` holds for any leader position).
-/

namespace Podc.ContentOblivious.BitSending

open Cslib.ContentOblivious

/-- Input for two rounds: leader flag, active flag, bit of round 1, bit of round 2. -/
abbrev Input2 := Bool × Bool × Option Bool × Option Bool

/-- Two CCW bit rounds back to back; the local state records the results obtained so far. -/
def twoDriver : Driver Input2 (Bool × Bool × Option Bool) (Option Bool)
    (Input2 × List (Option Bool)) where
  start i := ((i, []), some (i.1, i.2.1, i.2.2.1))
  next d r := ((d.1, d.2 ++ [r]), if d.2 = [] then some (d.1.1, d.1.2.1, d.1.2.2.2) else none)

/-- The composed program. -/
abbrev twoRounds : Proc Input2 (Input2 × List (Option Bool)) := proc.staged twoDriver

/-- The inputs of the counterexample (`some false` = bit `0`). -/
def xTwo : ZMod 3 → Input2 :=
  ![(true, false, none, none), (false, true, none, some false), (false, true, none, none)]

/-- The 16 deliveries of the bad execution (node, port). -/
def badSteps : List (ZMod 3 × Bool) :=
  [(1, false), (2, false), (0, false), (1, false), (0, true), (2, true), (0, false), (1, false),
   (2, false), (0, false), (1, false), (2, false), (0, false), (1, false), (2, false), (0, false)]

instance (c : Config (ZMod 3) twoRounds.State) (v : ZMod 3) (j : Bool) :
    Decidable (Enabled (oriented 3) twoRounds.toAlgo c v j) := by
  unfold Enabled; infer_instance

instance decValidSteps : ∀ (c : Config (ZMod 3) twoRounds.State) (l : List (ZMod 3 × Bool)),
    Decidable (ValidSteps (oriented 3) twoRounds.toAlgo c l)
  | _, [] => isTrue trivial
  | c, p :: l =>
    have := decValidSteps (deliver twoRounds.toAlgo c p.1 p.2) l
    inferInstanceAs (Decidable (_ ∧ _))

/-- The final configuration of the bad execution. -/
def cBad : Config (ZMod 3) twoRounds.State :=
  runSteps twoRounds.toAlgo (twoRounds.initCfg xTwo) badSteps

lemma badSteps_valid : ValidSteps (oriented 3) twoRounds.toAlgo (twoRounds.initCfg xTwo) badSteps := by
  decide

lemma cBad_reach : twoRounds.Reach (oriented 3) xTwo cBad :=
  Prog.Reach.trans_steps (Prog.Reach.init xTwo) badSteps_valid.reflTransGen

lemma cBad_final : twoRounds.Final (oriented 3) cBad := by
  intro v j
  revert v j
  decide

lemma cBad_quiescent : twoRounds.Quiescent (oriented 3) cBad := by
  intro p
  revert p
  decide

lemma cBad_out : (cBad.st 2).1.2 = [some false, none] ∧ (cBad.st 2).2 = none ∧
    (cBad.st 1).1.2 = [none, none] ∧ (cBad.st 1).2 = none := by
  decide

/-- The clockwise active neighbour of process `2` is process `1`. -/
lemma next_two : next (fun v => (xTwo v).2.1) 2 = 1 := by
  have hact : ∃ u, (fun v => (xTwo v).2.1) u = true := ⟨1, rfl⟩
  obtain ⟨h0, h1, h2⟩ := dist_spec hact 2
  have hd : dist (fun v => (xTwo v).2.1) 2 = 2 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have : dist (fun v => (xTwo v).2.1) 2 = 1 := by omega
      rw [this] at h1; revert h1; decide
    · have := h2 2 (by omega) hgt; revert this; decide
  rw [next, hd]; decide

/-- **Theorem 17 / Lemma 16 are false for a relay leader.** Running two CCW bit rounds back to
back on a 3-process ring whose leader is a relay can end in a final, quiescent configuration in
which process `2` has obtained the bits `[0, ⊥]` of its clockwise active neighbour `1`, although
`1` sent `⊥` in round 1 and `0` in round 2: the round-2 bit was attributed to round 1. -/
theorem relay_leader_composition_wrong :
    ∃ c, twoRounds.Reach (oriented 3) xTwo c ∧ twoRounds.Final (oriented 3) c ∧
      twoRounds.Quiescent (oriented 3) c ∧
      next (fun v => (xTwo v).2.1) 2 = 1 ∧
      (c.st 2).2 = none ∧
      (c.st 2).1.2 = [(xTwo 1).2.2.2, (xTwo 1).2.2.1] ∧
      (c.st 2).1.2 ≠ [(xTwo 1).2.2.1, (xTwo 1).2.2.2] :=
  ⟨cBad, cBad_reach, cBad_final, cBad_quiescent, next_two, cBad_out.2.1,
    by rw [cBad_out.1]; rfl, by rw [cBad_out.1]; decide⟩

end Podc.ContentOblivious.BitSending
