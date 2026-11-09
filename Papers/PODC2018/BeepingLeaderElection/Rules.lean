import Papers.PODC2018.BeepingLeaderElection.Forms

/-!
# The rules as abstract actions

`actOf` classifies the update of `ruleStep` as an abstract action (`Act`), and we characterize the
rule predicates (`branchLow`, `amt1`, `amt2`, `chgBy`) in terms of word decompositions.
-/

namespace Podc.BeepingLeaderElection

/-! ### Longest common prefix -/

@[simp] theorem lcpLen_nil_left (y : Word) : lcpLen [] y = 0 := by cases y <;> rfl
@[simp] theorem lcpLen_nil_right (x : Word) : lcpLen x [] = 0 := by cases x <;> rfl

@[simp] theorem lcpLen_cons_cons (a b : Bool) (x y : Word) :
    lcpLen (a :: x) (b :: y) = if a = b then lcpLen x y + 1 else 0 := rfl

@[simp] theorem lcpLen_append_left (z a b : Word) :
    lcpLen (z ++ a) (z ++ b) = z.length + lcpLen a b := by
  induction z with
  | nil => simp
  | cons c z ih => simp [ih]; omega

@[simp] theorem lcpLen_self_append (x w : Word) : lcpLen x (x ++ w) = x.length := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih]

@[simp] theorem lcpLen_append_self (x w : Word) : lcpLen (x ++ w) x = x.length := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih]

theorem lcpLen_le_left (x y : Word) : lcpLen x y ≤ x.length := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih => cases y with
    | nil => simp
    | cons b y => simp only [lcpLen_cons_cons, List.length_cons]; split_ifs <;> simp [ih]

theorem take_lcpLen (x y : Word) : x.take (lcpLen x y) = y.take (lcpLen x y) := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih => cases y with
    | nil => simp
    | cons b y =>
      simp only [lcpLen_cons_cons]
      split_ifs with h
      · subst h; simp [ih]
      · simp

/-! ### Rule predicates -/

theorem branchLow_eq_true_iff {x y : Word} :
    branchLow x y = true ↔ ∃ z w y', x = z ++ false :: w ∧ y = z ++ true :: y' := by
  constructor
  · intro h
    simp only [branchLow, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hx, hy⟩ := h
    set ℓ := lcpLen x y
    refine ⟨x.take ℓ, x.drop (ℓ + 1), y.drop (ℓ + 1), ?_, ?_⟩
    · obtain ⟨hl, hx'⟩ := List.getElem?_eq_some_iff.1 hx
      conv_lhs => rw [← List.take_append_drop ℓ x]
      rw [List.drop_eq_getElem_cons hl, hx']
    · obtain ⟨hl, hy'⟩ := List.getElem?_eq_some_iff.1 hy
      conv_lhs => rw [← List.take_append_drop ℓ y]
      rw [take_lcpLen x y, List.drop_eq_getElem_cons hl, hy']
  · rintro ⟨z, w, y', rfl, rfl⟩
    simp [branchLow]

theorem amt2_eq {z w y' : Word} : amt2 (z ++ false :: w) (z ++ true :: y') = w.length := by
  simp [amt2, branchLow]

theorem amt2_pos_iff {x y : Word} :
    0 < amt2 x y ↔ ∃ z w y', x = z ++ false :: w ∧ y = z ++ true :: y' ∧ w ≠ [] := by
  constructor
  · intro h
    unfold amt2 at h
    split_ifs at h with hb
    · obtain ⟨z, w, y', rfl, rfl⟩ := branchLow_eq_true_iff.1 hb
      refine ⟨z, w, y', rfl, rfl, ?_⟩
      simp at h; rintro rfl; simp at h
    · simp at h
  · rintro ⟨z, w, y', rfl, rfl, hw⟩
    rw [amt2_eq]; exact List.length_pos_of_ne_nil hw

theorem chgBy_eq_true_iff {x y : Word} :
    chgBy x y = true ↔ ∃ z y', x = z ++ [false] ∧ y = z ++ true :: y' := by
  constructor
  · intro h
    simp only [chgBy, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hb, hl⟩ := h
    obtain ⟨z, w, y', rfl, rfl⟩ := branchLow_eq_true_iff.1 hb
    simp at hl
    subst hl
    exact ⟨z, y', rfl, rfl⟩
  · rintro ⟨z, y', rfl, rfl⟩
    simp [chgBy, branchLow]

theorem amt1_pos_iff {x : Word} {m : Word × Bool} :
    0 < amt1 x m ↔ m.2 = true ∧ m.1 <+: x ∧ m.1.length < x.length := by
  unfold amt1
  split_ifs with h
  · simp only [h, and_self, iff_true]; omega
  · simp only [lt_self_iff_false, false_iff]; exact h

theorem amt1_le_three (x : Word) (m : Word × Bool) : amt1 x m ≤ 3 := by
  unfold amt1; split_ifs <;> omega

theorem amt1_le_length (x : Word) (m : Word × Bool) : amt1 x m ≤ x.length := by
  unfold amt1; split_ifs <;> omega

theorem amt2_le_length (x y : Word) : amt2 x y ≤ x.length := by
  unfold amt2; split_ifs <;> omega

/-! ### Abstract action of a rule step -/

/-- The abstract action performed by `ruleStep`. -/
def actOf (pr : Priority) (Y : Word) (s : NState) (R : Finset (Word × Bool)) : Act :=
  let x := s.pre
  let d := delAmount pr x R
  if 0 < d then .del d
  else if ∃ m ∈ R, chgBy x m.1 = true then .chg
  else if ∃ m ∈ R, x ++ [true] <+: m.1 then .app true
  else if ∃ m ∈ R, x ++ [false] <+: m.1 then .app false
  else if s.cand = true ∧ x.length < Y.length then .app (Y.getD x.length false)
  else .null

theorem ruleStep_pre (pr : Priority) (Y : Word) (s : NState) (R : Finset (Word × Bool)) :
    (ruleStep pr Y s R).pre = (actOf pr Y s R).apply s.pre := by
  unfold ruleStep actOf
  dsimp only
  split_ifs <;> rfl

theorem ruleStep_susp (pr : Priority) (Y : Word) (s : NState) (R : Finset (Word × Bool)) :
    (ruleStep pr Y s R).susp = (actOf pr Y s R).isDel := by
  unfold ruleStep actOf
  dsimp only
  split_ifs <;> rfl

end Podc.BeepingLeaderElection
