import Papers.PODC2026.ContentObliviousCounting.LowerBound
import Papers.PODC2026.ContentObliviousCounting.AnonCountingCompose
import Cslib.Computability.Distributed.ContentOblivious.Hom
import Mathlib

/-!
# Non-vacuity of the lower bound (Theorem 3)

The anonymous counting algorithm of §5 (Theorem 4), run with IDs that it ignores, is a correct
uniform counting algorithm in the sense of `Counting.CountingCorrect`; so the hypothesis of the
lower bound `Counting.count_lower_bound` is satisfiable, and the lower bound `Ω(n log n)` and the
upper bound `O(n^{1.5})` (`AnonCounting.totalPulses_le_sqrt`) apply to the same algorithm.
-/

namespace Podc.ContentOblivious.Counting

open Cslib.ContentOblivious AnonCounting

/-- The anonymous counting algorithm with inputs `(ID, isLeader)`; the ID is ignored. -/
def liftedCount : Proc (ℕ × Bool) (ℕ × ℕ) where
  State := anonCount.State
  init a := anonCount.init a.2
  recv := anonCount.recv
  ready := anonCount.ready
  terminated := anonCount.terminated
  result := anonCount.result
  terminated_eq := anonCount.terminated_eq

/-- Forgetting the IDs. -/
def forgetIds : liftedCount.Hom anonCount where
  f := id
  g := Prod.snd
  h := id
  init _ := rfl
  recv _ _ := rfl
  ready _ _ := rfl
  result s := by simp; rfl

/-- The leader's output: the computed ring size. -/
def countOut (s : liftedCount.State) : Option ℕ := (liftedCount.result s).map Prod.fst

/-- The counting algorithm of Theorem 4 satisfies the hypothesis of the lower bound. -/
theorem countingCorrect_anonCount : CountingCorrect liftedCount.toProg countOut := by
  intro n hn x ℓ hx c hc m hm
  have : NeZero n := ⟨by omega⟩
  have hin : (fun v => forgetIds.g (x v)) = leaderInput ℓ := by
    funext v
    simp only [forgetIds, leaderInput]
    have := hx.2 v
    cases h : (x v).2 <;> simp_all
  have hr : anonCount.Reach (oriented n) (fun v => forgetIds.g (x v)) (forgetIds.cfg c) :=
    (forgetIds.reach_iff x _).2 ⟨c, hc, rfl⟩
  rw [hin] at hr
  obtain ⟨a, ha⟩ : ∃ a, liftedCount.result (c.st ℓ) = some a := by
    revert hm; simp only [countOut]; cases liftedCount.result (c.st ℓ) <;> simp
  have := (anonCount_composable ℓ).result_eq (anonCount_returns ℓ) hr (v := ℓ) (a := a) ha
  simp only [countOut, ha, Option.map_some, Option.some.injEq] at hm
  rw [← hm, this]

/-- Theorem 3 applied to the algorithm of Theorem 4: every execution in which the leader has
counted sends at least `(n·⌊log₂ n⌋ − 4n)/14` pulses (and the algorithm never sends more than
`12·n·⌊√n⌋ + 14·n`). -/
theorem anonCount_lower_bound {n : ℕ} [NeZero n] {x : ZMod n → ℕ × Bool} {ℓ : ZMod n}
    (hx : Admissible x ℓ) {c : Config (ZMod n) liftedCount.State}
    (hc : liftedCount.Reach (oriented n) x c) {m : ℕ} (hm : countOut (c.st ℓ) = some m) :
    n * Nat.log 2 n ≤ 14 * totalRecvd c + 4 * n :=
  count_lower_bound countingCorrect_anonCount hx hc hm

end Podc.ContentOblivious.Counting
