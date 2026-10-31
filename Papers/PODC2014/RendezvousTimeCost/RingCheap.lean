import Papers.PODC2014.RendezvousTimeCost.LowerBoundCost

/-!
# Simultaneous-start Algorithm Cheap in the oriented ring (non-vacuity and tightness of Thm 3.1)

The simultaneous-start version of Algorithm Cheap (Section 2): agent with (0-based) label `x`
waits `x E` rounds and then explores the ring clockwise for `E = n - 1` rounds. In the oriented
ring it is a correct rendezvous algorithm of cost at most `E` and time at most `(L - 1) E`.
So the hypotheses of `thm_3_1_explicit` are satisfiable (with `φ = 0`), and its `Ω(E L)` bound is
tight up to a constant factor.
-/

namespace Podc.RendezvousTimeCost

open Finset

namespace RingCheap

/-- Simultaneous-start Cheap in the oriented `n`-ring, labels `Fin L` (label `x` stands for the
paper's label `x + 1`). -/
def cheapRing (n L : ℕ) : Behaviour L := fun x j =>
  if x.val * (n - 1) ≤ j ∧ j < (x.val + 1) * (n - 1) then 1 else 0

lemma disp_cheapRing (n L : ℕ) (x : Fin L) (t : ℕ) :
    disp (cheapRing n L x) t = ((min (t - x.val * (n - 1)) (n - 1) : ℕ) : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [disp_succ, ih]
    unfold cheapRing
    split_ifs with h
    · have : min (t + 1 - x.val * (n - 1)) (n - 1) = min (t - x.val * (n - 1)) (n - 1) + 1 := by
        rw [Nat.add_mul, one_mul] at h; omega
      rw [this]; simp
    · have : min (t + 1 - x.val * (n - 1)) (n - 1) = min (t - x.val * (n - 1)) (n - 1) := by
        rw [Nat.add_mul, one_mul] at h; omega
      rw [this]; simp

lemma moves_cheapRing (n L : ℕ) (x : Fin L) (t : ℕ) :
    moves (cheapRing n L x) t = min (t - x.val * (n - 1)) (n - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [moves_succ, ih]
    unfold cheapRing
    split_ifs with h
    · simp only [SignType.coe_one, Int.natAbs_one]
      rw [Nat.add_mul, one_mul] at h; omega
    · simp only [SignType.coe_zero, Int.natAbs_zero, add_zero]
      rw [Nat.add_mul, one_mul] at h; omega

/-- The execution with `x < y` meets at round `x E + k` (`k` the clockwise distance from `x` to
`y`), with cost at most `E`. -/
lemma meets_lt {n L : ℕ} [NeZero n] {x y : Fin L} (hxy : x.val < y.val) {px py : ZMod n}
    (hp : px ≠ py) :
    ∃ t, Meets n (cheapRing n L) x px y py t ∧ t ≤ (x.val + 1) * (n - 1) ∧
      moves (cheapRing n L x) t + moves (cheapRing n L y) t ≤ n - 1 := by
  set k := (py - px).val
  have hk : k < n := ZMod.val_lt _
  have hk0 : k ≠ 0 := by
    intro h; apply hp
    have : py - px = 0 := (ZMod.val_eq_zero _).1 h
    exact (sub_eq_zero.1 this).symm
  have hy : (x.val + 1) * (n - 1) ≤ y.val * (n - 1) := Nat.mul_le_mul_right _ hxy
  refine ⟨x.val * (n - 1) + k, ?_, ?_, ?_⟩
  · unfold Meets
    rw [disp_cheapRing, disp_cheapRing]
    have h1 : min (x.val * (n - 1) + k - x.val * (n - 1)) (n - 1) = k := by omega
    have h2 : min (x.val * (n - 1) + k - y.val * (n - 1)) (n - 1) = 0 := by
      rw [Nat.add_mul, one_mul] at hy; omega
    rw [h1, h2]
    rw [Int.cast_natCast, Int.cast_natCast]
    simp only [Nat.cast_zero, add_zero, k, ZMod.natCast_zmod_val]
    ring
  · rw [Nat.add_mul, one_mul]; omega
  · rw [moves_cheapRing, moves_cheapRing]
    rw [Nat.add_mul, one_mul] at hy; omega

/-- Simultaneous-start Cheap is a correct rendezvous algorithm in the oriented ring. -/
theorem cheapRing_correct (n L : ℕ) [NeZero n] : IsRendezvous n (cheapRing n L) := by
  intro x y hxy px py hp
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
  · obtain ⟨t, ht, -⟩ := meets_lt h hp
    exact ⟨t, ht⟩
  · obtain ⟨t, ht, -⟩ := meets_lt h (Ne.symm hp)
    exact ⟨t, (meets_comm _ _ _ _ _ _).1 ht⟩

/-- Simultaneous-start Cheap has cost at most `E = n - 1` (the paper: "cost exactly `E`"). -/
theorem cheapRing_cost (n L : ℕ) [NeZero n] : CostLE n (cheapRing n L) (n - 1) := by
  intro x y hxy px py hp
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
  · obtain ⟨t, ht, -, hc⟩ := meets_lt h hp
    have hle := meetTime_le ht
    unfold execCost
    have := moves_mono (cheapRing n L x) hle
    have := moves_mono (cheapRing n L y) hle
    omega
  · obtain ⟨t, ht, -, hc⟩ := meets_lt h (Ne.symm hp)
    rw [execCost_comm]
    have hle := meetTime_le ht
    unfold execCost
    have := moves_mono (cheapRing n L x) hle
    have := moves_mono (cheapRing n L y) hle
    omega

/-- Simultaneous-start Cheap has time at most `(L - 1) E`. -/
theorem cheapRing_time (n L : ℕ) [NeZero n] : TimeLE n (cheapRing n L) ((L - 1) * (n - 1)) := by
  intro x y hxy px py hp
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
  · obtain ⟨t, ht, ht', -⟩ := meets_lt h hp
    refine (meetTime_le ht).trans (ht'.trans (Nat.mul_le_mul_right _ ?_))
    have := y.isLt; omega
  · obtain ⟨t, ht, ht', -⟩ := meets_lt h (Ne.symm hp)
    rw [meetTime_comm]
    refine (meetTime_le ht).trans (ht'.trans (Nat.mul_le_mul_right _ ?_))
    have := x.isLt; omega

/-- Non-vacuity and tightness of Theorem 3.1: an algorithm of cost `E` exists (so the hypotheses
of `thm_3_1_explicit` hold with `φ = 0`), its time is at most `(L-1)E`, and Theorem 3.1 shows that
some execution of it lasts at least `(⌈L/2⌉ - 1) ⌊n/2⌋ / 2` rounds. -/
theorem thm_3_1_tight (n L : ℕ) [NeZero n] (hn : 2 ≤ n) (hL : 2 ≤ L) :
    IsRendezvous n (cheapRing n L) ∧ CostLE n (cheapRing n L) (n - 1 + 0) ∧
      TimeLE n (cheapRing n L) ((L - 1) * (n - 1)) ∧
      ∃ x y px py, x ≠ y ∧ px ≠ py ∧
        ((L + 1) / 2 - 1) * (n / 2) ≤ 2 * meetTime n (cheapRing n L) x px y py := by
  refine ⟨cheapRing_correct n L, cheapRing_cost n L, cheapRing_time n L, ?_⟩
  simpa using thm_3_1_explicit (φ := 0) hn hL _ (cheapRing_correct n L) (cheapRing_cost n L)
    (by omega)

end RingCheap

end Podc.RendezvousTimeCost
