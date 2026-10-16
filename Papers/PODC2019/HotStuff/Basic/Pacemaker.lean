import Mathlib

/-!
# The exponential back-off pacemaker of Section 4.4 does not by itself synchronize views

The paper suggests (Section 4.4) to implement `nextView` by a timer whose interval is doubled
whenever it expires without a decision, and argues: "Since the interval is doubled at each time,
the waiting intervals of all correct replicas will eventually have at least `T_f` overlap in
common".

This file shows that the argument is not valid as stated: two replicas whose timers are offset
by one view keep an overlap of exactly `α` in *every* view, forever, however long the run.
Such an offset arises, e.g., when a Byzantine leader of view `1` sends its `decide` message only to
replica `A` at time `α`: `A` moves to view `2` without doubling its interval `α`, while `B` times
out at the same moment and doubles its interval to `2α`. From then on (no decisions), `A` is in
view `k + 2` during `[2^k α, 2^(k+1) α)` and `B` during `[(2^(k+1) − 1) α, (2^(k+2) − 1) α)`.
If `α < T_f`, no view ever gets `T_f` time with both replicas in it, so (with `n = 4`, `f = 1` and a
silent Byzantine replica, where every QC needs all three correct replicas) no decision is reached
in any later view. This is the well-known *view synchronization* gap; the paper's Algorithm 5 later
simply *assumes* "synchronized leadership after GST".

Only the timer arithmetic is formalized here.
-/

namespace HotStuff.Pacemaker

/-- Timer schedule of a replica that times out in every view: `sched e I k` is the pair
(entry time, interval) of the `k`-th view after the one entered at time `e` with interval `I`;
on expiry the next view is entered and the interval doubled. -/
def sched (e I : ℕ) : ℕ → ℕ × ℕ
  | 0 => (e, I)
  | k + 1 => ((sched e I k).1 + (sched e I k).2, 2 * (sched e I k).2)

theorem sched_A (α k : ℕ) : sched α α k = (2 ^ k * α, 2 ^ k * α) := by
  induction k with
  | zero => simp [sched]
  | succ k ih => simp only [sched, ih, Prod.mk.injEq]; constructor <;> ring

theorem sched_B (α k : ℕ) : sched α (2 * α) k = ((2 ^ (k + 1) - 1) * α, 2 ^ (k + 1) * α) := by
  induction k with
  | zero => simp [sched]
  | succ k ih =>
    simp only [sched, ih, Prod.mk.injEq]
    have h : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    constructor
    · rw [pow_succ 2 (k + 1)]
      zify [h, show 1 ≤ 2 ^ (k + 1) * 2 by omega]
      ring
    · ring

/-- Replica `A` (decided in view `1`, interval `α`) and replica `B` (timed out, interval `2α`) are
simultaneously in the same view for exactly `α` time units, in every view. -/
theorem overlap_constant (α k : ℕ) :
    min (sched α α (k + 1)).1 (sched α (2 * α) (k + 1)).1 =
      max (sched α α k).1 (sched α (2 * α) k).1 + α := by
  rw [sched_A, sched_A, sched_B, sched_B]
  have h1 : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by
    rw [pow_succ]; have := Nat.one_le_two_pow (n := k); omega
  have h2 : 2 ^ (k + 1) ≤ 2 ^ (k + 1 + 1) - 1 := by
    rw [pow_succ 2 (k + 1)]; have := Nat.one_le_two_pow (n := k + 1); omega
  rw [min_eq_left (Nat.mul_le_mul_right α h2), max_eq_right (Nat.mul_le_mul_right α h1)]
  have h3 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  zify [h3]
  ring

end HotStuff.Pacemaker
