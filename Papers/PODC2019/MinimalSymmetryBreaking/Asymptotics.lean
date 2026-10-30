import Mathlib
import Cslib.Foundations.Data.Nat.LogStar

/-!
# Asymptotics of the speedup bound

Pure arithmetic needed for the `Ω(log* n)` lower bound: the palette of the 0-round algorithm
obtained by `t` speedup rounds grows like a tower of height `2t + O(1)` (`palT_bound`), hence the
lower bound `qT k t` on the local failure probability of a `t`-round weak 2-colouring algorithm is
still much larger than `1 / Kn k n` (the inverse radius of the identifier region) as long as
`2t + C ≤ log* n` (`qT_mul_large`).

The proofs only use crude "tower arithmetic": for `x, y ≤ tower m` (`m ≥ 2`) we have
`x + y, x * y ≤ tower (m + 1)` and `x ^ y ≤ tower (m + 2)`.
-/

namespace Podc.MinimalSymmetryBreaking

open Nat

/-- Palette growth of one full speedup round (node c-colouring → edge 2^(2c) → node
2^(2k·2^(2c))). -/
def pal (k c : ℕ) : ℕ := 2 ^ (2 * k * 2 ^ (2 * c))

/-- Palette of the 0-round algorithm obtained from a t-round weak 2-colouring algorithm. -/
def palT (k t : ℕ) : ℕ := (pal k)^[t] 2

/-- Lower bound on the local failure probability of t-round weak 2-colouring algorithms. -/
noncomputable def qT (k t : ℕ) : ℝ :=
  (1 / ((2 * k + 1) * (palT k t : ℝ) ^ (2 * k + 1))) ^ ((2 * k + 1) ^ (2 * t + 1))

/-- Radius of the identifier region in an n-node instance. -/
def Kn (k n : ℕ) : ℕ := Nat.log (2 * k + 1) n / 3

/-! ### Tower arithmetic -/

lemma lt_tower (m : ℕ) : m < tower m := by
  induction m with
  | zero => simp
  | succ m ih => rw [tower_succ]; have := Nat.lt_two_pow_self (n := tower m); omega

lemma four_le_tower {m : ℕ} (hm : 2 ≤ m) : 4 ≤ tower m :=
  calc 4 = tower 2 := rfl
    _ ≤ tower m := tower_mono hm

lemma le_tower_of_le {m m' x : ℕ} (hx : x ≤ tower m) (hm : m ≤ m') : x ≤ tower m' :=
  hx.trans (tower_mono hm)

private lemma mul_self_le_two_pow {x : ℕ} (hx : 4 ≤ x) : x * x ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih => rw [pow_succ]; nlinarith

private lemma add_two_le_two_pow {a : ℕ} (ha : 2 ≤ a) : a + 2 ≤ 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih => rw [pow_succ]; omega

lemma tower_mul {m x y : ℕ} (hm : 2 ≤ m) (hx : x ≤ tower m) (hy : y ≤ tower m) :
    x * y ≤ tower (m + 1) := by
  rw [tower_succ]
  exact (Nat.mul_le_mul hx hy).trans (mul_self_le_two_pow (four_le_tower hm))

lemma tower_add {m x y : ℕ} (hm : 2 ≤ m) (hx : x ≤ tower m) (hy : y ≤ tower m) :
    x + y ≤ tower (m + 1) := by
  have h4 := four_le_tower hm
  have := tower_mul hm (le_refl (tower m)) (le_refl (tower m))
  nlinarith

lemma tower_pow {m x y : ℕ} (hm : 2 ≤ m) (hx : x ≤ tower m) (hy : y ≤ tower m) :
    x ^ y ≤ tower (m + 2) :=
  calc x ^ y ≤ (2 ^ x) ^ y := Nat.pow_le_pow_left Nat.lt_two_pow_self.le y
    _ = 2 ^ (x * y) := (pow_mul 2 x y).symm
    _ ≤ 2 ^ tower (m + 1) := Nat.pow_le_pow_right (by norm_num) (tower_mul hm hx hy)
    _ = tower (m + 2) := rfl

/-! ### Growth of the palette -/

lemma palT_zero (k : ℕ) : palT k 0 = 2 := rfl

lemma palT_succ (k t : ℕ) : palT k (t + 1) = pal k (palT k t) :=
  Function.iterate_succ_apply' _ _ _

/-- One speedup round adds two levels to the tower (with the invariant `2P + 2k + 1 ≤ tower M`). -/
lemma pal_step {k P M : ℕ} (hk : 1 ≤ k) (h : 2 * P + 2 * k + 1 ≤ tower M) :
    2 * pal k P + 2 * k + 1 ≤ tower (M + 2) := by
  have ha : 2 * k + 2 ≤ 2 ^ (2 * k) := add_two_le_two_pow (by omega)
  have h1 : pal k P ≤ 2 ^ (2 ^ (2 * P + 2 * k)) := by
    unfold pal
    apply Nat.pow_le_pow_right (by norm_num)
    rw [pow_add, mul_comm (2 ^ (2 * P))]
    exact Nat.mul_le_mul_right _ (by omega)
  have h2 : 2 ^ (2 ^ (2 * P + 2 * k)) * 2 ^ (2 ^ (2 * P + 2 * k)) ≤ tower (M + 2) := by
    rw [← pow_add, show tower (M + 2) = 2 ^ 2 ^ tower M from rfl]
    apply Nat.pow_le_pow_right (by norm_num)
    rw [← two_mul, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 * k + 3 ≤ 2 ^ (2 ^ (2 * P + 2 * k)) := by
    have := Nat.lt_two_pow_self (n := 2 ^ (2 * P + 2 * k))
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 2 * k ≤ 2 * P + 2 * k by omega)
    omega
  nlinarith

/-- `palT k t` is at most a tower of height `2t + 2k + 5`. -/
lemma palT_bound (k : ℕ) (hk : 1 ≤ k) (t : ℕ) :
    2 * palT k t + 2 * k + 1 ≤ tower (2 * t + (2 * k + 5)) := by
  induction t with
  | zero => rw [palT_zero]; have := lt_tower (2 * 0 + (2 * k + 5)); omega
  | succ t ih =>
    rw [palT_succ, show 2 * (t + 1) + (2 * k + 5) = 2 * t + (2 * k + 5) + 2 by ring]
    exact pal_step hk ih

/-- The natural-number form of the main estimate: `2 b^(2t+2) Q + t + 1 ≤ tower (2t + 2k + 12)`,
where `b = 2k + 1` and `Q = 1 / qT k t`. -/
lemma main_nat_bound (k : ℕ) (hk : 1 ≤ k) (t : ℕ) :
    2 * (2 * k + 1) ^ (2 * t + 2) *
        ((2 * k + 1) * palT k t ^ (2 * k + 1)) ^ ((2 * k + 1) ^ (2 * t + 1)) + (t + 1) ≤
      tower (2 * t + (2 * k + 5) + 7) := by
  set M := 2 * t + (2 * k + 5) with hMdef
  have hM : 2 ≤ M := by omega
  have hinv : 2 * palT k t + 2 * k + 1 ≤ tower M := palT_bound k hk t
  have hTM := lt_tower M
  have hP : palT k t ≤ tower M := by omega
  have hb : 2 * k + 1 ≤ tower M := by omega
  have h2t1 : 2 * t + 1 ≤ tower M := by omega
  have h2t2 : 2 * t + 2 ≤ tower M := by omega
  have hPb : palT k t ^ (2 * k + 1) ≤ tower (M + 2) := tower_pow hM hP hb
  have hbPb : (2 * k + 1) * palT k t ^ (2 * k + 1) ≤ tower (M + 2 + 1) :=
    tower_mul (by omega) (le_tower_of_le hb (by omega)) hPb
  have he : (2 * k + 1) ^ (2 * t + 1) ≤ tower (M + 2 + 1) :=
    le_tower_of_le (tower_pow hM hb h2t1) (by omega)
  have hQ := tower_pow (by omega) hbPb he
  have hb22 : (2 * k + 1) ^ (2 * t + 2) ≤ tower (M + 2) := tower_pow hM hb h2t2
  have h2b : 2 * (2 * k + 1) ^ (2 * t + 2) ≤ tower (M + 2 + 1) :=
    tower_mul (by omega) (le_tower_of_le (show 2 ≤ tower M by omega) (by omega)) hb22
  have hprod := tower_mul (m := M + 2 + 1 + 2) (by omega) (le_tower_of_le h2b (by omega)) hQ
  have ht : t + 1 ≤ tower (M + 2 + 1 + 2 + 1) := le_tower_of_le (show t + 1 ≤ tower M by omega)
    (by omega)
  exact le_tower_of_le (tower_add (by omega) hprod ht) (by omega)

/-- If `tower (m + 3) ≤ n` then `tower m ≤ Kn k n`. -/
lemma tower_le_Kn {k n m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hb : 2 * k + 1 ≤ tower m)
    (h : tower (m + 3) ≤ n) : tower m ≤ Kn k n := by
  unfold Kn
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  apply Nat.le_log_of_pow_le (by omega)
  have h4 := four_le_tower hm
  have h3 : tower m * 3 ≤ tower (m + 1) := tower_mul hm le_rfl (by omega)
  exact (tower_pow (by omega) (le_tower_of_le hb (by omega)) h3).trans h

/-! ### The failure-probability bound -/

lemma qT_eq (k t : ℕ) : qT k t =
    1 / ((((2 * k + 1) * palT k t ^ (2 * k + 1) : ℕ) : ℝ) ^ ((2 * k + 1) ^ (2 * t + 1))) := by
  unfold qT; rw [one_div_pow]; push_cast; ring

lemma palT_pos (k t : ℕ) : 0 < palT k t := by
  rcases t with _ | t
  · simp [palT_zero]
  · rw [palT_succ]; unfold pal; positivity

lemma qT_pos (k t : ℕ) : 0 < qT k t := by
  have := palT_pos k t
  unfold qT; positivity

lemma qT_le_one (k t : ℕ) : qT k t ≤ 1 := by
  rw [qT_eq]
  apply div_le_one_of_le₀ _ (by positivity)
  apply one_le_pow₀
  have : 1 ≤ (2 * k + 1) * palT k t ^ (2 * k + 1) := by
    apply Nat.one_le_iff_ne_zero.2
    apply mul_ne_zero (by omega)
    apply pow_ne_zero
    induction t with
    | zero => simp [palT_zero]
    | succ t _ => rw [palT_succ]; unfold pal; positivity
  exact_mod_cast this

/-- The asymptotic estimate behind the `Ω(log* n)` lower bound: there is a constant `C`
(explicitly `C = 2k + 15`) such that whenever `2t + C ≤ log* n`, the identifier radius
`Kn k n` is at least `3` and `2 (2k+1)^(2t+2) ≤ qT k t · (Kn k n - t - 1)`. -/
theorem qT_mul_large (k : ℕ) (hk : 1 ≤ k) : ∃ C N₀ : ℕ, ∀ n ≥ N₀, ∀ t : ℕ,
    2 * t + C ≤ Nat.logStar n →
    3 ≤ Kn k n ∧ 2 * ((2 * k + 1 : ℝ) ^ (2 * t + 2)) ≤ qT k t * ((Kn k n : ℝ) - t - 1) := by
  refine ⟨2 * k + 15, 1, fun n hn t ht => ?_⟩
  have hnat := main_nat_bound k hk t
  set M := 2 * t + (2 * k + 5) with hMdef
  have htow : tower (M + 7 + 3) ≤ n := (le_logStar_iff (by omega)).1 (by omega)
  have hb : 2 * k + 1 ≤ tower (M + 7) := (lt_tower (M + 7)).le.trans' (by omega)
  have hK := tower_le_Kn hk (by omega) hb htow
  constructor
  · have := four_le_tower (m := M + 7) (by omega); omega
  · have hle := hnat.trans hK
    rw [qT_eq, div_mul_eq_mul_div, one_mul]
    have hQpos : (0 : ℝ) <
        (((2 * k + 1) * palT k t ^ (2 * k + 1) : ℕ) : ℝ) ^ ((2 * k + 1) ^ (2 * t + 1)) := by
      have : 0 < palT k t := by
        rcases t with _ | t
        · simp [palT_zero]
        · rw [palT_succ]; unfold pal; positivity
      positivity
    rw [le_div_iff₀ hQpos]
    have := (Nat.cast_le (α := ℝ)).2 hle
    push_cast at this ⊢
    linarith

end Podc.MinimalSymmetryBreaking
