import Papers.PODC2010.KBakery.Fife

/-!
# RMR complexity in the DSM model (Lemma 7 of the paper; Lemmas 5.8 and 5.19 of the thesis)

In the DSM model `Ticket[p]`, `Want[i][p]` and `Capture[i][p]` are in `p`'s memory module, so
the waiting loop is local. A passage makes exactly `4(N − 1)` RMRs (unshaded algorithm) or
`5(N − 1)` RMRs (full algorithm), and every prefix of a passage makes at most that many:
`Θ(N)`.
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ}

/-- RMRs of a complete passage in the DSM model. -/
def dsmTotal (fife : Bool) (N : ℕ) : ℕ := (if fife then 5 else 4) * (N - 1)

/-- Remaining DSM RMRs of the passage of `p` from location `c`. -/
def dsmRem (fife : Bool) (N : ℕ) (p : P) : PC P → ℕ
  | .ncs => 0
  | .d14 rem => rem.card + 2 * (N - 1) + (if fife then 2 else 1) * (N - 1)
  | .d15 _ rem => (rem.erase p).card + (N - 1) + (if fife then 2 else 1) * (N - 1)
  | .d16 rem => rem.card + (if fife then 2 else 1) * (N - 1)
  | .head _ _ | .scan _ _ | .chk _ _ _ => (if fife then 2 else 1) * (N - 1)
  | .cap23 rem => (rem.erase p).card + (N - 1)
  | .cs => N - 1
  | .ex rem => (rem.erase p).card

/-- `p` never writes its own `Want[p][p]` at lines 14 and 16. -/
def NotSelf (p : P) : PC P → Prop
  | .d14 rem | .d16 rem => p ∉ rem
  | _ => True

lemma dsm_step {s : Cfg P} {p i : P} (ha : Admissible s p i) (hn : s.pc p ≠ .ncs)
    (hns : NotSelf p (s.pc p)) :
    (if rmrDSM s p i then 1 else 0) + dsmRem fife (Fintype.card P) p ((stepAt fife k s p i).pc p) =
      dsmRem fife (Fintype.card P) p (s.pc p) ∧ NotSelf p ((stepAt fife k s p i).pc p) := by
  have he : (univ.erase p).card = Fintype.card P - 1 := by rw [card_erase_of_mem (mem_univ p), card_univ]
  have h2 : ∀ rem : Finset P, i ∈ rem →
      (if i ≠ p then 1 else 0) + ((rem.erase i).erase p).card = (rem.erase p).card := by
    intro rem hi
    by_cases hip : i = p
    · subst hip; simp
    · rw [if_pos hip, erase_right_comm, add_comm,
        card_erase_add_one (mem_erase.2 ⟨hip, hi⟩)]
  have hrem : ∀ rem : Finset P, i ∉ rem → (s.pc p).rem = rem → rem = ∅ := by
    intro rem hi h
    have := admissible_of_not_mem ha (by rw [h]; exact hi)
    rwa [h] at this
  rw [stepAt_pc]
  have hL : ∀ x y : ℕ, (if fife then x else y) = (if fife then x else y) := fun _ _ => rfl
  clear hL
  rcases hpc : s.pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc, NotSelf] at hn hns <;>
    simp only [hpc, PC.rem] at hrem
  · exact absurd rfl hn
  · -- line 14
    by_cases hi : i ∈ rem'
    · have hip : i ≠ p := fun h => hns (h ▸ hi)
      have := card_erase_add_one hi
      simp [core, hpc, hi, rmrDSM, access, Var.owner, hip, dsmRem, NotSelf]
      exact ⟨by omega, fun _ h => hns h⟩
    · have := hrem rem' hi rfl; subst this
      simp [core, hpc, rmrDSM, access, dsmRem, NotSelf, he]; omega
  · -- line 15
    by_cases hi : i ∈ rem'
    · have := h2 rem' hi
      simp [core, hpc, hi, rmrDSM, access, Var.owner, dsmRem, NotSelf]
      by_cases hip : i = p <;> simp [hip] at this ⊢ <;> omega
    · have := hrem rem' hi rfl; subst this
      simp [core, hpc, rmrDSM, access, dsmRem, NotSelf, Var.owner, he]
  · -- line 16
    by_cases hi : i ∈ rem'
    · have hip : i ≠ p := fun h => hns (h ▸ hi)
      have := card_erase_add_one hi
      simp [core, hpc, hi, rmrDSM, access, Var.owner, hip, dsmRem, NotSelf]
      exact ⟨by omega, fun _ h => hns h⟩
    · have := hrem rem' hi rfl; subst this
      simp [core, hpc, rmrDSM, access, dsmRem, NotSelf]
  · -- line 19
    have hacc : access s p i = none := by simp [access, hpc]
    simp only [core, hpc, rmrDSM, hacc]
    cases fife <;> split_ifs <;> simp_all [dsmRem, NotSelf, he] <;> omega
  · -- lines 20–21
    by_cases hi : i ∈ rem'
    · simp only [core, hpc, hi, if_true, rmrDSM, access, Var.owner]
      split_ifs <;> simp_all [dsmRem, NotSelf]
    · simp only [core, hpc, hi, if_false, rmrDSM, access]
      cases fife <;> simp [dsmRem, NotSelf]
  · -- line 22
    by_cases hi : i ∈ rem'
    · simp [core, hpc, hi, rmrDSM, access, Var.owner, dsmRem, NotSelf]
    · simp [core, hpc, hi, rmrDSM, access, dsmRem, NotSelf]
  · -- line 23
    by_cases hi : i ∈ rem'
    · have := h2 rem' hi
      simp [core, hpc, hi, rmrDSM, access, Var.owner, dsmRem, NotSelf]
      by_cases hip : i = p <;> simp [hip] at this ⊢ <;> omega
    · have := hrem rem' hi rfl; subst this
      simp [core, hpc, rmrDSM, access, dsmRem, NotSelf]
  · -- CS
    simp [core, hpc, rmrDSM, access, dsmRem, NotSelf, he]
  · -- line 25
    by_cases hi : i ∈ rem'
    · have := h2 rem' hi
      simp [core, hpc, hi, rmrDSM, access, Var.owner, dsmRem, NotSelf]
      by_cases hip : i = p <;> simp [hip] at this ⊢ <;> omega
    · have := hrem rem' hi rfl; subst this
      simp [core, hpc, rmrDSM, access, dsmRem, NotSelf]

/-- Number of RMRs (in the model given by `isRMR`) made by `p` in the time interval `[t₀, t₁)`. -/
def Run.rmrs {fife : Bool} (r : Run fife k P) (isRMR : Cfg P → P → P → Bool) (p : P)
    (t₀ t₁ : ℕ) : ℕ :=
  ((Finset.Ico t₀ t₁).filter fun u => r.sched u = p ∧ isRMR (r.s u) p (r.choice u) = true).card

lemma Run.rmrs_succ (r : Run fife k P) (isRMR : Cfg P → P → P → Bool) (p : P) {t₀ t : ℕ}
    (h : t₀ ≤ t) : r.rmrs isRMR p t₀ (t + 1) = r.rmrs isRMR p t₀ t +
      if r.sched t = p ∧ isRMR (r.s t) p (r.choice t) = true then 1 else 0 := by
  unfold Run.rmrs
  rw [Nat.Ico_succ_right_eq_insert_Ico h, filter_insert]
  split_ifs with hs
  · rw [card_insert_of_notMem (by simp)]
  · rfl

/-- **Lemma 7 (DSM)**: a passage of `p` that starts with the step at time `t₀` (leaving the NCS)
and has not returned to the NCS before time `t₁` makes exactly
`dsmTotal − dsmRem (pc at t₁)` RMRs in `[t₀, t₁)`. -/
theorem rmr_dsm_eq (r : Run fife k P) (p : P) {t₀ t₁ : ℕ} (hp : (r.s t₀).pc p = .ncs)
    (hs : r.sched t₀ = p) (h₀₁ : t₀ < t₁) (hin : ∀ t, t₀ < t → t < t₁ → (r.s t).pc p ≠ .ncs) :
    r.rmrs rmrDSM p t₀ t₁ + dsmRem fife (Fintype.card P) p ((r.s t₁).pc p) =
      dsmTotal fife (Fintype.card P) := by
  have he : (univ.erase p).card = Fintype.card P - 1 := by
    rw [card_erase_of_mem (mem_univ p), card_univ]
  have key : ∀ t, t₀ + 1 ≤ t → t ≤ t₁ →
      r.rmrs rmrDSM p t₀ t + dsmRem fife (Fintype.card P) p ((r.s t).pc p) =
        dsmTotal fife (Fintype.card P) ∧ NotSelf p ((r.s t).pc p) := by
    intro t h1 h2
    induction t, h1 using Nat.le_induction with
    | base =>
      have hpc : (r.s (t₀ + 1)).pc p = .d14 (univ.erase p) := by
        rw [r.step t₀, hs, stepAt_pc]; simp [core, hp]
      have hr : rmrDSM (r.s t₀) p (r.choice t₀) = false := by simp [rmrDSM, access, hp]
      rw [r.rmrs_succ _ _ le_rfl, hpc]
      simp only [Run.rmrs, Ico_self, filter_empty, card_empty, hs, hr, true_and]
      refine ⟨?_, by simp [NotSelf]⟩
      cases fife <;> simp [dsmRem, dsmTotal, he] <;> omega
    | succ t ht ih =>
      obtain ⟨h1, h3⟩ := ih (by omega)
      rw [r.rmrs_succ _ _ (by omega)]
      by_cases hst : r.sched t = p
      · have hadm := r.adm t
        rw [hst] at hadm
        obtain ⟨h4, h5⟩ := dsm_step (fife := fife) (k := k) hadm (hin t (by omega) (by omega)) h3
        have hst' := r.step t
        rw [hst] at hst'
        simp only [hst, true_and]
        rw [hst']
        refine ⟨?_, h5⟩
        split_ifs at h4 ⊢ <;> omega
      · rw [r.pc_succ_of_ne hst, if_neg (by simp [hst])]
        exact ⟨by simpa using h1, h3⟩
  exact (key t₁ h₀₁ le_rfl).1

/-- **Lemma 7 (DSM), upper bound**: every (possibly incomplete) passage makes at most
`4(N − 1)` (unshaded algorithm) or `5(N − 1)` (full algorithm) RMRs. -/
theorem rmr_dsm_le (r : Run fife k P) (p : P) {t₀ t₁ : ℕ} (hp : (r.s t₀).pc p = .ncs)
    (hs : r.sched t₀ = p) (h₀₁ : t₀ < t₁) (hin : ∀ t, t₀ < t → t < t₁ → (r.s t).pc p ≠ .ncs) :
    r.rmrs rmrDSM p t₀ t₁ ≤ dsmTotal fife (Fintype.card P) := by
  have := rmr_dsm_eq r p hp hs h₀₁ hin
  omega

/-- **Lemma 7 (DSM), complete passages**: a complete passage makes exactly `4(N − 1)` (unshaded)
or `5(N − 1)` (full algorithm) RMRs. -/
theorem rmr_dsm_complete (r : Run fife k P) (p : P) {t₀ t₁ : ℕ} (hp : (r.s t₀).pc p = .ncs)
    (hs : r.sched t₀ = p) (h₀₁ : t₀ < t₁) (hin : ∀ t, t₀ < t → t < t₁ → (r.s t).pc p ≠ .ncs)
    (hend : (r.s t₁).pc p = .ncs) :
    r.rmrs rmrDSM p t₀ t₁ = dsmTotal fife (Fintype.card P) := by
  have := rmr_dsm_eq r p hp hs h₀₁ hin
  rw [hend] at this
  simpa [dsmRem] using this

end Podc.KBakery
