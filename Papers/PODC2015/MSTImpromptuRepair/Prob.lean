import Cslib.Probability.Finite.Uniform

/-!
# Small facts about uniform finite probability

* `uprob_prod_and` — independence of the two coordinates of a product sample space
  (`Pr[A(ω₁) ∧ B(ω₂)] = Pr[A] Pr[B]`). -- CSLib candidate: `Cslib/Probability/Finite/Uniform.lean`
* `card_mul_eq_iff_uprob_eq` — the counting form `r · #E = |Ω|` of `Pr[E] = 1/r`.
* `one_sub_pow_le_of_le_log` — `(1 - 1/16)^K ≤ ε` once `K ≥ 16 ln(1/ε)` (the repetition count of
  `FindAny`).
-/

namespace Podc.MSTImpromptuRepair

open Finset Cslib.Probability

/-- Independence of the coordinates of a product of finite uniform sample spaces. -/
theorem uprob_prod_and {α β : Type*} [Fintype α] [Fintype β] (A : α → Prop) (B : β → Prop) :
    uprob (fun p : α × β => A p.1 ∧ B p.2) = uprob A * uprob B := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter, uprob_eq_card_filter]
  have : (univ.filter fun p : α × β => A p.1 ∧ B p.2) = (univ.filter A) ×ˢ (univ.filter B) := by
    ext p; simp
  rw [this, card_product, Fintype.card_prod]
  push_cast
  rw [div_mul_div_comm]

/-- Counting form of `Pr[E] = 1/r`. -/
theorem card_mul_eq_iff_uprob_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop)
    [DecidablePred E] {r : ℕ} (hr : 0 < r) :
    r * #(univ.filter E) = Fintype.card Ω ↔ uprob E = 1 / r := by
  rw [uprob_eq_card_filter]
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [div_eq_div_iff hΩ.ne' hr'.ne', one_mul]
  constructor
  · intro h; rw [← h]; push_cast; ring
  · intro h; exact_mod_cast (by linarith : (r : ℝ) * #(univ.filter E) = Fintype.card Ω)

/-- `(1 - 1/16)^K ≤ ε` as soon as `K ≥ 16 ln(1/ε)` (and `0 < ε`). -/
theorem one_sub_pow_le_of_le_log {ε : ℝ} (hε : 0 < ε) {K : ℕ}
    (hK : 16 * Real.log (1 / ε) ≤ K) : (1 - 1 / 16 : ℝ) ^ K ≤ ε := by
  have h1 : (1 - 1 / 16 : ℝ) ≤ Real.exp (-(1 / 16)) := by
    have := Real.add_one_le_exp (-(1 / 16 : ℝ)); linarith
  calc (1 - 1 / 16 : ℝ) ^ K ≤ Real.exp (-(1 / 16)) ^ K :=
        pow_le_pow_left₀ (by norm_num) h1 K
    _ = Real.exp (-(K / 16)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-Real.log (1 / ε)) := Real.exp_le_exp.2 (by linarith)
    _ = ε := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

end Podc.MSTImpromptuRepair
