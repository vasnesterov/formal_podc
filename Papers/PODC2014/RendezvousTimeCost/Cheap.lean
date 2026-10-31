import Papers.PODC2014.RendezvousTimeCost.Segments

/-!
# Algorithm Cheap (Section 2 of Miller–Pelc): Proposition 2.1

* `cheapSim ℓ` : the version for simultaneous start (wait `(ℓ-1)E` rounds, explore once);
  `cheapSim_bounds`: time `≤ min(ℓA, ℓB) · E ≤ (L-1)E`, cost `≤ E`.
* `cheap ℓ` : Algorithm 1 (explore, wait `2ℓE` rounds, explore);
  `prop_2_1`: time `≤ (2L+1)E`, cost `≤ 3E` for arbitrary wake-up times
  (`prop_2_1_min`: time `≤ (2 min(ℓA, ℓB) + 3)E`).
-/

namespace Podc.RendezvousTimeCost.Upper

variable {V : Type*} [DecidableEq V] {E : ℕ}

lemma replicate_false_append_getD (n i : ℕ) :
    (List.replicate n false ++ [true]).getD i false = decide (i = n) := by
  induction n generalizing i with
  | zero => cases i <;> simp
  | succ n ih => cases i <;> simp [List.replicate_succ, ← ih, List.getD_eq_getElem?_getD]

/-! ### Simultaneous start -/

/-- Algorithm Cheap for simultaneous start (Section 2): wait `(ℓ - 1)E` rounds, then explore
once. -/
def cheapSim (ℓ : ℕ) : List Bool := List.replicate (ℓ - 1) false ++ [true]

lemma cheapSim_core (X : Explore V E) {ℓP ℓQ : ℕ} (hP : 1 ≤ ℓP) (hlt : ℓP < ℓQ) (vP vQ : V) :
    ∃ r ≤ ℓP * E, MeetsAt X ⟨cheapSim ℓP, vP, 0⟩ ⟨cheapSim ℓQ, vQ, 0⟩ r ∧
      moveCount (pos X ⟨cheapSim ℓP, vP, 0⟩) r + moveCount (pos X ⟨cheapSim ℓQ, vQ, 0⟩) r
        ≤ E := by
  set P : Agent V := ⟨cheapSim ℓP, vP, 0⟩
  set Q : Agent V := ⟨cheapSim ℓQ, vQ, 0⟩
  have hidle := pos_idle_range X Q (i := 0) (j := ℓQ - 1) (Nat.zero_le _) (fun k _ hk => by
    simp only [Q, cheapSim, replicate_false_append_getD]; simp; omega)
  have hexp := pos_explore X P (i := ℓP - 1)
    (by simp only [P, cheapSim, replicate_false_append_getD]; simp)
  have h1 : (ℓP - 1) * E + E = ℓP * E := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hP]
  have h2 : ℓP * E ≤ (ℓQ - 1) * E := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨r, hr1, hr2, hm⟩ := meet_of_window (segTraj X Q.bits Q.start (0 * E)) hidle hexp
    (by simp [Q]) (by simp [Q, P]; omega)
  simp only [P, zero_add] at hr2
  refine ⟨r, by omega, hm.symm, ?_⟩
  have hPm : moveCount (pos X P) r ≤ E := by
    rw [moveCount_pos]
    refine (moveCount_segTraj X _ _ _).trans ?_
    simp [P, cheapSim, List.count_replicate]
  have hQm : moveCount (pos X Q) r = 0 :=
    moveCount_const _ (fun t ht => hidle t (by simp [Q]) (by simp [Q]; omega))
  omega

/-- Algorithm Cheap with **simultaneous start** (Section 2, and the abstract: "a version of
Algorithm Cheap … has cost exactly `E`"): for distinct labels in `[1, L]` the agents meet within
`min(ℓA, ℓB) · E ≤ (L - 1)E` rounds, at cost at most `E`. -/
theorem cheapSim_bounds (X : Explore V E) {L ℓA ℓB : ℕ} (hA : ℓA ∈ Set.Icc 1 L)
    (hB : ℓB ∈ Set.Icc 1 L) (hne : ℓA ≠ ℓB) (vA vB : V) :
    (∃ r, MeetsAt X ⟨cheapSim ℓA, vA, 0⟩ ⟨cheapSim ℓB, vB, 0⟩ r) ∧
      meetTime X ⟨cheapSim ℓA, vA, 0⟩ ⟨cheapSim ℓB, vB, 0⟩ ≤ min ℓA ℓB * E ∧
      min ℓA ℓB * E ≤ (L - 1) * E ∧
      cost X ⟨cheapSim ℓA, vA, 0⟩ ⟨cheapSim ℓB, vB, 0⟩ ≤ E := by
  obtain ⟨hA1, hAL⟩ := hA
  obtain ⟨hB1, hBL⟩ := hB
  have hmin : min ℓA ℓB * E ≤ (L - 1) * E := Nat.mul_le_mul_right _ (by omega)
  rcases lt_or_gt_of_ne hne with h | h
  · have := bounds_of_meet X (cheapSim_core X hA1 h vA vB)
    rw [min_eq_left h.le]; rw [min_eq_left h.le] at hmin
    exact ⟨this.1, this.2.1, hmin, this.2.2⟩
  · have := bounds_of_meet X (exists_meet_swap X (cheapSim_core X hB1 h vB vA))
    rw [min_eq_right h.le]; rw [min_eq_right h.le] at hmin
    exact ⟨this.1, this.2.1, hmin, this.2.2⟩

/-! ### Arbitrary wake-up times -/

/-- **Algorithm 1** `Cheap(ℓ)`: execute EXPLORE once, wait `2ℓE` rounds, execute EXPLORE once. -/
def cheap (ℓ : ℕ) : List Bool := true :: (List.replicate (2 * ℓ) false ++ [true])

lemma cheap_getD (ℓ i : ℕ) : (cheap ℓ).getD i false = decide (i = 0 ∨ i = 2 * ℓ + 1) := by
  cases i with
  | zero => simp [cheap]
  | succ i => rw [cheap, List.getD_cons_succ, replicate_false_append_getD]; simp

lemma cheap_count (ℓ : ℕ) : (cheap ℓ).count true = 2 := by
  simp [cheap, List.count_replicate]

lemma cheap_take_count (ℓ : ℕ) : ((cheap ℓ).take (2 * ℓ + 1)).count true = 1 := by
  simp [cheap, List.count_replicate]

/-- Core of Proposition 2.1: the earlier agent `P` (delay `0`) and the later agent `Q`
(delay `τ`). -/
lemma cheap_core (X : Explore V E) {ℓP ℓQ : ℕ} (hP : 1 ≤ ℓP) (hQ : 1 ≤ ℓQ) (hne : ℓP ≠ ℓQ)
    (vP vQ : V) (τ : ℕ) :
    ∃ r ≤ (2 * min ℓP ℓQ + 3) * E, MeetsAt X ⟨cheap ℓP, vP, 0⟩ ⟨cheap ℓQ, vQ, τ⟩ r ∧
      moveCount (pos X ⟨cheap ℓP, vP, 0⟩) r + moveCount (pos X ⟨cheap ℓQ, vQ, τ⟩) r
        ≤ 3 * E := by
  set P : Agent V := ⟨cheap ℓP, vP, 0⟩
  set Q : Agent V := ⟨cheap ℓQ, vQ, τ⟩
  have hPtot : ∀ r, moveCount (pos X P) r ≤ 2 * E := fun r => by
    rw [moveCount_pos]
    refine (moveCount_segTraj X _ _ _).trans ?_
    simp [P, cheap_count, mul_comm]
  have hQtot : ∀ r, moveCount (pos X Q) r ≤ 2 * E := fun r => by
    rw [moveCount_pos]
    refine (moveCount_segTraj X _ _ _).trans ?_
    simp [Q, cheap_count, mul_comm]
  by_cases hτ : E ≤ τ
  · -- the later agent is still asleep during the first exploration of the earlier one
    obtain ⟨s, hs, h⟩ := pos_explore X P (i := 0) (by simp only [P, cheap_getD]; simp) vQ
    simp only [P, zero_mul, add_zero, zero_add] at h
    have hQs : ∀ t ≤ s, pos X Q t = vQ := fun t ht => pos_of_le_delay X Q (by simp [Q]; omega)
    refine ⟨s, hs.trans (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
    · show pos X P s = pos X Q s
      rw [h, hQs s le_rfl]
    · rw [moveCount_const vQ hQs]
      have := moveCount_le_self (pos X P) s
      omega
  · push Not at hτ
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `ℓP < ℓQ`: `Q` waits while `P` performs its second exploration
      have hidle := pos_idle_range X Q (i := 1) (j := 2 * ℓQ + 1) (by omega) (fun k hk1 hk2 => by
        simp only [Q, cheap_getD]; simp; omega)
      have hexp := pos_explore X P (i := 2 * ℓP + 1) (by simp only [P, cheap_getD]; simp)
      have e1 : (2 * ℓP + 3) * E ≤ (2 * ℓQ + 1) * E := Nat.mul_le_mul_right _ (by omega)
      have e2 : 3 * E ≤ (2 * ℓP + 1) * E := Nat.mul_le_mul_right _ (by omega)
      obtain ⟨r, hr1, hr2, hm⟩ := meet_of_window _ hidle hexp
        (by simp only [Q, P]; rtc_omega)
        (by simp only [Q, P]; rtc_omega)
      simp only [P, zero_add] at hr1 hr2
      refine ⟨r, ?_, hm.symm, ?_⟩
      · rw [min_eq_left hlt.le]; rtc_omega
      · have hQm : moveCount (pos X Q) r ≤ E := by
          rw [moveCount_pos]
          refine (moveCount_segTraj_take X _ _ (k := 2 * ℓQ + 1) ?_).trans ?_
          · simp only [Q]; rtc_omega
          · simp [Q, cheap_take_count]
        have := hPtot r
        omega
    · -- `ℓQ < ℓP`: `P` waits while `Q` performs its second exploration
      have hidle := pos_idle_range X P (i := 1) (j := 2 * ℓP + 1) (by omega) (fun k hk1 hk2 => by
        simp only [P, cheap_getD]; simp; omega)
      have hexp := pos_explore X Q (i := 2 * ℓQ + 1) (by simp only [Q, cheap_getD]; simp)
      have e1 : (2 * ℓQ + 3) * E ≤ (2 * ℓP + 1) * E := Nat.mul_le_mul_right _ (by omega)
      obtain ⟨r, hr1, hr2, hm⟩ := meet_of_window _ hidle hexp
        (by simp only [Q, P]; rtc_omega)
        (by simp only [Q, P]; rtc_omega)
      simp only [Q] at hr1 hr2
      refine ⟨r, ?_, hm, ?_⟩
      · rw [min_eq_right hgt.le]; rtc_omega
      · have hPm : moveCount (pos X P) r ≤ E := by
          rw [moveCount_pos]
          refine (moveCount_segTraj_take X _ _ (k := 2 * ℓP + 1) ?_).trans ?_
          · simp only [P]; rtc_omega
          · simp [P, cheap_take_count]
        have := hQtot r
        omega

/-- **Proposition 2.1** (stronger form, from its proof): Algorithm Cheap completes rendezvous for
arbitrary wake-up times, within `(2 min(ℓA, ℓB) + 3)E` rounds of the earlier wake-up, with cost at
most `3E`. (The starting nodes need not even be distinct.) -/
theorem prop_2_1_min (X : Explore V E) {ℓA ℓB : ℕ} (hA : 1 ≤ ℓA) (hB : 1 ≤ ℓB) (hne : ℓA ≠ ℓB)
    (vA vB : V) {δA δB : ℕ} (hδ : δA = 0 ∨ δB = 0) :
    (∃ r, MeetsAt X ⟨cheap ℓA, vA, δA⟩ ⟨cheap ℓB, vB, δB⟩ r) ∧
      meetTime X ⟨cheap ℓA, vA, δA⟩ ⟨cheap ℓB, vB, δB⟩ ≤ (2 * min ℓA ℓB + 3) * E ∧
      cost X ⟨cheap ℓA, vA, δA⟩ ⟨cheap ℓB, vB, δB⟩ ≤ 3 * E := by
  apply bounds_of_meet
  rcases hδ with rfl | rfl
  · exact cheap_core X hA hB hne vA vB δB
  · apply exists_meet_swap
    rw [min_comm]
    exact cheap_core X hB hA hne.symm vB vA δA

/-- **Proposition 2.1** of [Miller–Pelc]: Algorithm Cheap completes rendezvous with cost at most
`3E` and in time at most `(2L+1)E`, for any two distinct labels in `[1, L]`, any starting nodes
and any wake-up times (`δA = 0 ∨ δB = 0`: time is counted from the earlier wake-up). -/
theorem prop_2_1 (X : Explore V E) {L ℓA ℓB : ℕ} (hA : ℓA ∈ Set.Icc 1 L)
    (hB : ℓB ∈ Set.Icc 1 L) (hne : ℓA ≠ ℓB) (vA vB : V) {δA δB : ℕ} (hδ : δA = 0 ∨ δB = 0) :
    (∃ r, MeetsAt X ⟨cheap ℓA, vA, δA⟩ ⟨cheap ℓB, vB, δB⟩ r) ∧
      meetTime X ⟨cheap ℓA, vA, δA⟩ ⟨cheap ℓB, vB, δB⟩ ≤ (2 * L + 1) * E ∧
      cost X ⟨cheap ℓA, vA, δA⟩ ⟨cheap ℓB, vB, δB⟩ ≤ 3 * E := by
  obtain ⟨h1, h2, h3⟩ := prop_2_1_min X hA.1 hB.1 hne vA vB hδ
  refine ⟨h1, h2.trans (Nat.mul_le_mul_right _ ?_), h3⟩
  have := hA.2; have := hB.2
  omega

end Podc.RendezvousTimeCost.Upper
