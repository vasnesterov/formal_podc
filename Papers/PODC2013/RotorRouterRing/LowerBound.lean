import Papers.PODC2013.RotorRouterRing.Ring

/-!
# Theorem 3.7: a lower bound `Ω((n/k)²)` on the cover time for every initial placement

Klasing, Kosowski, Pająk, Sauerwald, PODC 2013, Theorem 3.7: for any initial locations of the `k`
agents there is a pointer initialization of the ring for which the cover time is `Ω((n/k)²)`.

The paper's proof relies on the agent-domain Lemmas 2.5/2.6, whose proofs are sketchy. We give a
different, self-contained proof with explicit constants, based on the potential identity
`potential_run` (a rotor-router analogue of the optional stopping argument for random walks):

* all pointers point **away from a node `v`** (`awayPtr v`), so the pointer part of the
  potential of any radially non-increasing `h` can only grow;
* *hit lemma* (`hit_lemma`, parabola `(R - d)²`): if no agent starts within distance `R` of `v`,
  then before `v` is reached the agents must spend at least `R²` agent-rounds within distance
  `R` of `v`;
* *scale step* (`scale_step`, a smooth bump of radius `2R`): the number of agents within distance
  `R` of `v` at time `s` is at most `2 N_{2R}(0) + (1/R²) Σ_{s' < s} N_{2R}(s')`;
* iterating the scale step over the radii `2^m R₀` (`multiscale`) and choosing `v` by counting
  (`exists_good_center`) so that few agents start near `v` at every scale gives
  `n² < 8192 k² T` for every `T` at which the ring is covered (`theorem_3_7`).

Our hypothesis is `n ≥ 8k` (the paper assumes `n ≥ 440 k²`).
-/

open Finset

namespace Podc.RotorRouterRing

open RotorGraph

variable {n : ℕ} [NeZero n]

set_option linter.unusedSectionVars false

/-! ### Radial test functions -/

/-- The smooth bump of radius `2R`: `2R² - d²` for `d ≤ R`, `(2R - d)²` for `R ≤ d ≤ 2R`. -/
def bump (R : ℕ) (d : ℕ) : ℤ :=
  if d ≤ R then 2 * (R : ℤ) ^ 2 - (d : ℤ) ^ 2 else if d ≤ 2 * R then (2 * (R : ℤ) - d) ^ 2 else 0

/-- The parabola `(R - d)²` on `d ≤ R`. -/
def para (R : ℕ) (d : ℕ) : ℤ := if d ≤ R then ((R : ℤ) - d) ^ 2 else 0

lemma bump_antitone (R : ℕ) : Antitone (bump R) := by
  intro a b hab
  simp only [bump]
  split_ifs <;> push_cast <;> first | nlinarith | (exfalso; omega)

lemma para_antitone (R : ℕ) : Antitone (para R) := by
  intro a b hab
  simp only [para]
  split_ifs <;> push_cast <;> first | nlinarith | (exfalso; omega)

lemma bump_eq_zero (R d : ℕ) (h : 2 * R ≤ d) : bump R d = 0 := by
  unfold bump
  split_ifs with h1 h2
  · obtain ⟨rfl, rfl⟩ : R = 0 ∧ d = 0 := by omega
    simp
  · obtain rfl : d = 2 * R := by omega
    push_cast; ring
  · rfl

lemma para_eq_zero (R d : ℕ) (h : R ≤ d) : para R d = 0 := by
  unfold para
  split_ifs with h1
  · obtain rfl : d = R := by omega
    ring
  · rfl

lemma bump_nonneg (R d : ℕ) : 0 ≤ bump R d := by
  unfold bump
  split_ifs with h1 h2
  · have : (d : ℤ) ≤ R := by exact_mod_cast h1
    nlinarith [Nat.cast_nonneg (α := ℤ) d]
  · positivity
  · rfl

lemma para_nonneg (R d : ℕ) : 0 ≤ para R d := by
  unfold para; split_ifs <;> first | positivity | rfl

lemma bump_le (R d : ℕ) : bump R d ≤ 2 * (R : ℤ) ^ 2 := by
  unfold bump
  split_ifs with h1 h2
  · nlinarith [sq_nonneg (d : ℤ)]
  · have : (d : ℤ) ≤ 2 * R := by exact_mod_cast h2
    have : (R : ℤ) < d := by exact_mod_cast (by omega : R < d)
    nlinarith
  · positivity

lemma bump_ge (R d : ℕ) (h : d ≤ R) : (R : ℤ) ^ 2 ≤ bump R d := by
  unfold bump
  rw [if_pos h]
  have : (d : ℤ) ≤ R := by exact_mod_cast h
  nlinarith [Nat.cast_nonneg (α := ℤ) d]

lemma bump_second_diff (R d : ℕ) (hd : d ≤ 2 * R) :
    bump R (d + 1) + bump R (if d = 0 then 1 else d - 1) - 2 * bump R d
      ≤ if R < d ∧ d ≤ 2 * R then 2 else 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · simp only [bump]; split_ifs <;> push_cast <;> first | nlinarith | (exfalso; omega)
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [bump, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    split_ifs <;> push_cast <;> first | nlinarith | (exfalso; omega)

lemma para_second_diff (R d : ℕ) (hR : 1 ≤ R) :
    para R (d + 1) + para R (if d = 0 then 1 else d - 1) - 2 * para R d
      ≤ if 1 ≤ d ∧ d ≤ R then 2 else 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · simp only [para]; split_ifs <;> push_cast <;> first | nlinarith | (exfalso; omega)
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [para, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    split_ifs <;> push_cast <;> first | nlinarith | (exfalso; omega)

/-! ### Laplacians of radial functions -/

lemma lap_radial (f : ℕ → ℤ) (v x : ZMod n) (hx : 2 * ringDist v x + 2 ≤ n) :
    lap (fun y => f (ringDist v y)) x = f (ringDist v x + 1)
      + f (if ringDist v x = 0 then 1 else ringDist v x - 1) - 2 * f (ringDist v x) := by
  unfold lap
  dsimp only
  rcases ringDist_neighbors v x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring

lemma lap_radial_far (f : ℕ → ℤ) (K : ℕ) (hf : ∀ d, K ≤ d → f d = 0) (v x : ZMod n)
    (hx : K + 1 ≤ ringDist v x) : lap (fun y => f (ringDist v y)) x = 0 := by
  unfold lap
  dsimp only
  have h1 := ringDist_succ_ge v x
  have h2 := ringDist_pred_ge v x
  rw [hf _ (by omega), hf _ (by omega), hf _ (by omega)]; ring

lemma lap_bump_le (R : ℕ) (v x : ZMod n) (hn : 4 * R + 2 ≤ n) :
    lap (fun y => bump R (ringDist v y)) x
      ≤ if R < ringDist v x ∧ ringDist v x ≤ 2 * R then 2 else 0 := by
  rcases le_or_gt (ringDist v x) (2 * R) with h | h
  · rw [lap_radial _ v x (by omega)]; exact bump_second_diff R _ h
  · rw [lap_radial_far _ (2 * R) (fun d hd => bump_eq_zero R d hd) v x (by omega), if_neg (by omega)]

lemma lap_para_le (R : ℕ) (hR : 1 ≤ R) (v x : ZMod n) (hn : 2 * R + 2 ≤ n) :
    lap (fun y => para R (ringDist v y)) x
      ≤ if 1 ≤ ringDist v x ∧ ringDist v x ≤ R then 2 else 0 := by
  rcases le_or_gt (ringDist v x) R with h | h
  · rw [lap_radial _ v x (by omega)]; exact para_second_diff R _ hR
  · rw [lap_radial_far _ R (fun d hd => para_eq_zero R d hd) v x (by omega), if_neg (by omega)]

/-! ### Pointers pointing away from `v` -/

/-- The initial pointer of `x` points to the neighbour of `x` farther from `v`. -/
def awayPtr (v : ZMod n) (x : ZMod n) : ℕ := if ringDist v (x - 1) ≤ ringDist v (x + 1) then 0 else 1

lemma away_min (f : ℕ → ℤ) (hf : Antitone f) (v x : ZMod n) :
    f (ringDist v ((ring n).target x (awayPtr v x)))
      ≤ f (ringDist v ((ring n).target x (awayPtr v x + 1))) := by
  simp only [awayPtr]
  split_ifs with h
  · simp only [ring_target]; norm_num; exact hf h
  · simp only [ring_target]; norm_num; exact hf (by omega)

/-- The radial potential inequality for the undelayed system started with pointers pointing
away from `v`. -/
lemma radial_ineq (pos₀ : ZMod n → ℕ) (v : ZMod n) (f : ℕ → ℤ) (hf : Antitone f) (L : ℕ → ℤ)
    (hL : ∀ x, lap (fun y => f (ringDist v y)) x ≤ L (ringDist v x)) (t : ℕ) :
    2 * ∑ u, ((((ring n).run ⟨pos₀, awayPtr v⟩ undelayed t).pos u : ℕ) : ℤ) * f (ringDist v u)
      ≤ 2 * ∑ u, (pos₀ u : ℤ) * f (ringDist v u)
        + ∑ x, ((ring n).exits ⟨pos₀, awayPtr v⟩ undelayed t x : ℤ) * L (ringDist v x) := by
  have hpot := potential_run (fun y => f (ringDist v y)) ⟨pos₀, awayPtr v⟩ undelayed t
  have hptr := ptr_term_ge (fun y => f (ringDist v y)) ⟨pos₀, awayPtr v⟩ undelayed
    (fun x => away_min f hf v x) t
  have hsum : ∑ x, ((ring n).exits ⟨pos₀, awayPtr v⟩ undelayed t x : ℤ)
        * lap (fun y => f (ringDist v y)) x
      ≤ ∑ x, ((ring n).exits ⟨pos₀, awayPtr v⟩ undelayed t x : ℤ) * L (ringDist v x) := by
    gcongr with x
    exact hL x
  simp only [potential] at hpot
  linarith

/-! ### Counting agents near `v` -/

/-- Number of agents within distance `R` of `v` at time `s` (undelayed system). -/
def nearCount (pos₀ : ZMod n → ℕ) (v : ZMod n) (R s : ℕ) : ℕ :=
  ∑ x, if ringDist v x ≤ R then ((ring n).run ⟨pos₀, awayPtr v⟩ undelayed s).pos x else 0

lemma nearCount_zero (pos₀ : ZMod n → ℕ) (v : ZMod n) (R : ℕ) :
    nearCount pos₀ v R 0 = ∑ x, if ringDist v x ≤ R then pos₀ x else 0 := rfl

lemma sum_exits_near (pos₀ : ZMod n → ℕ) (v : ZMod n) (R t : ℕ) :
    ∑ x, (if ringDist v x ≤ R then (ring n).exits ⟨pos₀, awayPtr v⟩ undelayed t x else 0)
      = ∑ s ∈ range t, nearCount pos₀ v R s := by
  simp only [exits_undelayed, nearCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  split_ifs <;> simp

/-- **Scale step.** `R² N_R(s) ≤ 2R² N_{2R}(0) + Σ_{s' < s} N_{2R}(s')`. -/
lemma scale_step (pos₀ : ZMod n → ℕ) (v : ZMod n) (R : ℕ) (hn : 4 * R + 2 ≤ n) (s : ℕ) :
    R ^ 2 * nearCount pos₀ v R s
      ≤ 2 * R ^ 2 * nearCount pos₀ v (2 * R) 0 + ∑ s' ∈ range s, nearCount pos₀ v (2 * R) s' := by
  have key := radial_ineq pos₀ v (bump R) (bump_antitone R)
    (fun d => if R < d ∧ d ≤ 2 * R then 2 else 0) (fun x => lap_bump_le R v x hn) s
  set c := (ring n).run ⟨pos₀, awayPtr v⟩ undelayed s
  have hlow : ((R ^ 2 * nearCount pos₀ v R s : ℕ) : ℤ)
      ≤ ∑ u, ((c.pos u : ℕ) : ℤ) * bump R (ringDist v u) := by
    simp only [nearCount, Finset.mul_sum, mul_ite, mul_zero]; push_cast
    apply Finset.sum_le_sum; intro u _
    split_ifs with h
    · have := bump_ge R _ h
      nlinarith [Nat.cast_nonneg (α := ℤ) (c.pos u)]
    · exact mul_nonneg (Nat.cast_nonneg _) (bump_nonneg _ _)
  have hinit : ∑ u, (pos₀ u : ℤ) * bump R (ringDist v u)
      ≤ ((2 * R ^ 2 * nearCount pos₀ v (2 * R) 0 : ℕ) : ℤ) := by
    simp only [nearCount_zero, Finset.mul_sum, mul_ite, mul_zero]; push_cast
    apply Finset.sum_le_sum; intro u _
    split_ifs with h
    · have := bump_le R (ringDist v u)
      nlinarith [Nat.cast_nonneg (α := ℤ) (pos₀ u)]
    · rw [bump_eq_zero R _ (by omega), mul_zero]
  have hexit : ∑ x, ((ring n).exits ⟨pos₀, awayPtr v⟩ undelayed s x : ℤ)
        * (if R < ringDist v x ∧ ringDist v x ≤ 2 * R then 2 else 0)
      ≤ 2 * ((∑ s' ∈ range s, nearCount pos₀ v (2 * R) s' : ℕ) : ℤ) := by
    rw [← sum_exits_near]; push_cast; rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    have := Nat.cast_nonneg (α := ℤ) ((ring n).exits ⟨pos₀, awayPtr v⟩ undelayed s x)
    split_ifs with h1 h2 h2
    · linarith
    · exact absurd h1.2 h2
    · linarith
    · simp
  have : ((R ^ 2 * nearCount pos₀ v R s : ℕ) : ℤ)
      ≤ ((2 * R ^ 2 * nearCount pos₀ v (2 * R) 0 : ℕ) : ℤ)
        + ((∑ s' ∈ range s, nearCount pos₀ v (2 * R) s' : ℕ) : ℤ) := by linarith
  exact_mod_cast this

/-- **Hit lemma.** If no agent starts within distance `R` of `v` and an agent is on `v` at time
`T`, then `R² ≤ Σ_{s < T} N_R(s)`. -/
lemma hit_lemma (pos₀ : ZMod n → ℕ) (v : ZMod n) (R : ℕ) (hR : 1 ≤ R) (hn : 2 * R + 2 ≤ n)
    (h0 : nearCount pos₀ v R 0 = 0) (T : ℕ)
    (hT : 0 < ((ring n).run ⟨pos₀, awayPtr v⟩ undelayed T).pos v) :
    R ^ 2 ≤ ∑ s ∈ range T, nearCount pos₀ v R s := by
  have key := radial_ineq pos₀ v (para R) (para_antitone R)
    (fun d => if 1 ≤ d ∧ d ≤ R then 2 else 0) (fun x => lap_para_le R hR v x hn) T
  set c := (ring n).run ⟨pos₀, awayPtr v⟩ undelayed T
  have hlow : (R : ℤ) ^ 2 ≤ ∑ u, ((c.pos u : ℕ) : ℤ) * para R (ringDist v u) := by
    have hnn : ∀ u, 0 ≤ ((c.pos u : ℕ) : ℤ) * para R (ringDist v u) := fun u =>
      mul_nonneg (Nat.cast_nonneg _) (para_nonneg _ _)
    refine le_trans ?_ (Finset.single_le_sum (fun u _ => hnn u) (Finset.mem_univ v))
    simp only [ringDist_self, para, zero_le, if_true, Nat.cast_zero, sub_zero]
    have : (1 : ℤ) ≤ c.pos v := by exact_mod_cast hT
    nlinarith [sq_nonneg (R : ℤ)]
  have hinit : ∑ u, (pos₀ u : ℤ) * para R (ringDist v u) = 0 := by
    apply Finset.sum_eq_zero; intro u _
    rw [nearCount_zero, Finset.sum_eq_zero_iff] at h0
    have := h0 u (Finset.mem_univ u)
    split_ifs at this with h
    · simp [this]
    · rw [para_eq_zero R _ (by omega), mul_zero]
  have hexit : ∑ x, ((ring n).exits ⟨pos₀, awayPtr v⟩ undelayed T x : ℤ)
        * (if 1 ≤ ringDist v x ∧ ringDist v x ≤ R then 2 else 0)
      ≤ 2 * ((∑ s ∈ range T, nearCount pos₀ v R s : ℕ) : ℤ) := by
    rw [← sum_exits_near]; push_cast; rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    have := Nat.cast_nonneg (α := ℤ) ((ring n).exits ⟨pos₀, awayPtr v⟩ undelayed T x)
    split_ifs with h1 h2 h2
    · linarith
    · exact absurd h1.2 h2
    · linarith
    · simp
  have : (R : ℤ) ^ 2 ≤ ((∑ s ∈ range T, nearCount pos₀ v R s : ℕ) : ℤ) := by linarith
  exact_mod_cast this

end Podc.RotorRouterRing
