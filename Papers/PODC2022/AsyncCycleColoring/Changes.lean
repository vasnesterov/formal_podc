import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting the changes of a sequence

`chg f T` is the number of times `t < T` with `f (t + 1) ≠ f t`. The termination proof of
Algorithm 1 bounds the number of failed rounds of a process by the number of changes of its
colour, and bounds those changes by propagating along monotone chains of identifiers.
-/

namespace AsyncCycle

open Classical in
/-- Number of changes of `f` on `[0, T]`. -/
noncomputable def chg {β : Type*} (f : ℕ → β) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => f (t + 1) ≠ f t)).card

variable {β γ : Type*}

lemma chg_zero (f : ℕ → β) : chg f 0 = 0 := by simp [chg]

open Classical in
lemma chg_succ (f : ℕ → β) (T : ℕ) :
    chg f (T + 1) = chg f T + if f (T + 1) ≠ f T then 1 else 0 := by
  unfold chg
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma chg_succ_le (f : ℕ → β) (T : ℕ) : chg f (T + 1) ≤ chg f T + 1 := by
  classical
  rw [chg_succ]; split_ifs <;> omega

lemma chg_succ_of_eq {f : ℕ → β} {T : ℕ} (h : f (T + 1) = f T) : chg f (T + 1) = chg f T := by
  classical
  rw [chg_succ, ite_eq_right (not_not.2 h)]; rfl

lemma chg_succ_of_ne {f : ℕ → β} {T : ℕ} (h : f (T + 1) ≠ f T) : chg f (T + 1) = chg f T + 1 := by
  classical
  rw [chg_succ, ite_eq_left h]

lemma chg_mono (f : ℕ → β) {T T' : ℕ} (h : T ≤ T') : chg f T ≤ chg f T' := by
  classical
  unfold chg
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

lemma chg_comp_le (h : β → γ) (f : ℕ → β) (T : ℕ) : chg (fun t => h (f t)) T ≤ chg f T := by
  classical
  unfold chg
  apply Finset.card_le_card
  intro t; simp only [Finset.mem_filter]
  rintro ⟨h1, h2⟩; exact ⟨h1, fun e => h2 (by rw [e])⟩

lemma chg_pair_le (f : ℕ → β) (g : ℕ → γ) (T : ℕ) :
    chg (fun t => (f t, g t)) T ≤ chg f T + chg g T := by
  classical
  unfold chg
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro t; simp only [Finset.mem_filter, Finset.mem_union, ne_eq, Prod.mk.injEq]
  rintro ⟨h1, h2⟩
  by_cases hf : f (t + 1) = f t
  · exact Or.inr ⟨h1, fun hg => h2 ⟨hf, hg⟩⟩
  · exact Or.inl ⟨h1, hf⟩

lemma chg_eq_zero_of_const {f : ℕ → β} {c : β} (h : ∀ t, f t = c) (T : ℕ) : chg f T = 0 := by
  classical
  unfold chg
  simp [h]

/-- Indicator of `x ≠ y`. -/
def ind [DecidableEq β] (x y : β) : ℕ := if x = y then 0 else 1

lemma ind_tri [DecidableEq β] (x y z : β) : ind x z ≤ ind x y + ind y z := by
  unfold ind; split_ifs <;> simp_all

lemma ind_symm [DecidableEq β] (x y : β) : ind x y = ind y x := by
  unfold ind; split_ifs <;> simp_all

lemma ind_le_one [DecidableEq β] (x y : β) : ind x y ≤ 1 := by
  unfold ind; split_ifs <;> simp

lemma chg_succ_ind [DecidableEq β] (f : ℕ → β) (T : ℕ) :
    chg f (T + 1) = chg f T + ind (f (T + 1)) (f T) := by
  unfold ind
  by_cases e : f (T + 1) = f T
  · rw [chg_succ_of_eq e, ite_eq_left e]; rfl
  · rw [chg_succ_of_ne e, ite_eq_right e]

/-- The "lag" lemma: if at every step `f` either keeps its value or takes the value `h t`, then
`f` changes at most once more than `h` (precisely: `ind (f 0) (h 0)` more). -/
lemma chg_lag_aux [DecidableEq β] {f h : ℕ → β}
    (hfh : ∀ t, f (t + 1) = f t ∨ f (t + 1) = h t) (T : ℕ) :
    chg f T + ind (f T) (h T) ≤ ind (f 0) (h 0) + chg h T := by
  induction T with
  | zero => simp [chg_zero]
  | succ T ih =>
    have hh := chg_succ_ind h T
    have hf := chg_succ_ind f T
    have t1 := ind_tri (f T) (h T) (h (T + 1))
    have t2 := ind_symm (h (T + 1)) (h T)
    rcases hfh T with e | e
    · rw [e] at hf ⊢
      have : ind (f T) (f T) = 0 := by simp [ind]
      omega
    · rw [e] at hf ⊢
      have t3 := ind_symm (h T) (f T)
      omega

lemma chg_lag [DecidableEq β] {f h : ℕ → β} (hfh : ∀ t, f (t + 1) = f t ∨ f (t + 1) = h t)
    (T : ℕ) : chg f T ≤ 1 + chg h T := by
  have := chg_lag_aux hfh T
  have := ind_le_one (f 0) (h 0)
  omega

lemma chg_lag_of_eq [DecidableEq β] {f h : ℕ → β}
    (hfh : ∀ t, f (t + 1) = f t ∨ f (t + 1) = h t) (h0 : f 0 = h 0) (T : ℕ) :
    chg f T ≤ chg h T := by
  have := chg_lag_aux hfh T
  have : ind (f 0) (h 0) = 0 := by simp [ind, h0]
  omega

/-- The "follow" lemma: if `f` starts at `g 0` and at every step either keeps its value or takes
the current value of `g`, then `f` changes at most as often as `g`. -/
lemma chg_follow [DecidableEq β] {f g : ℕ → β} (h0 : f 0 = g 0)
    (hfg : ∀ t, f (t + 1) = f t ∨ f (t + 1) = g (t + 1)) (T : ℕ) : chg f T ≤ chg g T := by
  have key : ∀ T, chg f T + ind (f T) (g T) ≤ chg g T := by
    intro T
    induction T with
    | zero => simp [chg_zero, ind, h0]
    | succ T ih =>
      have hg := chg_succ_ind g T
      have hf := chg_succ_ind f T
      have t1 := ind_tri (f T) (g T) (g (T + 1))
      have t2 := ind_symm (g (T + 1)) (g T)
      rcases hfg T with e | e
      · rw [e] at hf ⊢
        have : ind (f T) (f T) = 0 := by simp [ind]
        omega
      · rw [e] at hf ⊢
        have : ind (g (T + 1)) (g (T + 1)) = 0 := by simp [ind]
        have t3 := ind_tri (g (T + 1)) (g T) (f T)
        have t4 := ind_symm (g T) (f T)
        omega
  have := key T
  omega

end AsyncCycle
