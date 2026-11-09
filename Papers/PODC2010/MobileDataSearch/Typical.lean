import Papers.PODC2010.MobileDataSearch.Basic

/-!
# Typical tokens and load balancing (Section 4, up to Lemma 3)

Bar-Noy, Cheilaris, Feng, Levin, *Finding mobile data under delay constraints with searching costs*,
PODC 2010, Section 4.

A *typical* token has `p = w` (after normalization), with `∑ p = 1`.

* Proposition 3: `cost(A) = 1/2 + 1/2 ∑_d P_d²` (`prop3`).
* Definition 1: the `L₂` load balancing objective `lbCost p A = ∑_d P_d²`.
* Lemma 3: a `(1+ε)`-approximation for load balancing is a `(1+ε')`-approximation for the
  typical-token search problem with `ε' = ε · O/(1+O) ≤ ε/2` (`lemma3`, `lemma3_half`,
  `lemma3_lt_half`), where `O` is the optimal load balancing value; `1/D ≤ O` gives
  `O/(1+O) ≥ 1/(D+1)` (`one_div_le_lbCost`, `lemma3_ratio_ge`), and the ratio identity
  `lemma3_ratio_eq` shows that this bound is attained when the load balancing ratio is attained.

The paper writes "`X = (1 + Y)/2`" with `X` the load balancing goal and `Y` the search goal; by
Proposition 3 it is `Y = (1 + X)/2` (the letters are swapped, a typo).
-/

namespace Podc.MobileDataSearch

open Finset

variable {n D : ℕ}

/-- Definition 1 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010]: the `L₂` load balancing
objective of an allocation of tasks (boxes) with processing times `p` to `D` machines (rounds),
`∑_d (∑_{i ∈ M_d} p_i)²`. -/
def lbCost (p : Fin n → ℝ) (A : Strategy n D) : ℝ := ∑ d, (roundSum p A d) ^ 2

/-- The round sums add up to the total. -/
lemma sum_roundSum (f : Fin n → ℝ) (A : Strategy n D) : ∑ d, roundSum f A d = ∑ i, f i := by
  simp only [roundSum]
  exact Finset.sum_fiberwise univ A f

/-- Round form of the cost: `cost(A) = ∑_{e,f} [f ≤ e] P_e W_f`. -/
lemma cost_eq_rounds (p w : Fin n → ℝ) (A : Strategy n D) :
    cost p w A = ∑ e, ∑ f, if f ≤ e then roundSum p A e * roundSum w A f else 0 := by
  rw [prop1_eq1]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

/-- Proposition 3 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010]: for a typical token
(`w = p`, `∑ p = 1`), `cost(A) = 1/2 + 1/2 ∑_d P_d²`. -/
theorem prop3 (p : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (A : Strategy n D) :
    cost p p A = 1 / 2 + 1 / 2 * ∑ d, (roundSum p A d) ^ 2 := by
  rw [cost_eq_rounds]
  set P := roundSum p A
  have hP : ∑ d, P d = 1 := by rw [sum_roundSum, hp1]
  -- `[f ≤ e] + [e ≤ f] = 1 + [e = f]`
  have hsym : ∀ e f : Fin D, (if f ≤ e then P e * P f else 0) + (if e ≤ f then P f * P e else 0)
      = P e * P f + (if e = f then P e * P f else 0) := by
    intro e f
    rcases lt_trichotomy e f with h | rfl | h
    · simp [h.le, not_le.2 h, h.ne, mul_comm]
    · simp
    · simp [h.le, not_le.2 h, h.ne']
  have h2 : 2 * ∑ e, ∑ f, (if f ≤ e then P e * P f else 0) =
      ∑ e, ∑ f, (P e * P f + if e = f then P e * P f else 0) := by
    simp_rw [← hsym, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun e f => if e ≤ f then P f * P e else 0)]
    ring
  have h3 : ∑ e, ∑ f, (P e * P f + if e = f then P e * P f else 0) = 1 + ∑ d, P d ^ 2 := by
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul_sum, hP, Finset.sum_ite_eq univ]
    simp [sq]
  linarith

/-- Proposition 3 in terms of the load balancing objective. -/
lemma cost_typical_eq (p : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (A : Strategy n D) :
    cost p p A = (1 + lbCost p A) / 2 := by
  rw [prop3 p hp1, lbCost]; ring

lemma lbCost_nonneg (p : Fin n → ℝ) (A : Strategy n D) : 0 ≤ lbCost p A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `O ≤ 1`: for a normalized non-negative token the load balancing objective is at most `1`. -/
lemma lbCost_le_one (p : Fin n → ℝ) (hp : 0 ≤ p) (hp1 : ∑ i, p i = 1) (A : Strategy n D) :
    lbCost p A ≤ 1 := by
  have hP : ∑ d, roundSum p A d = 1 := by rw [sum_roundSum, hp1]
  have hnn : ∀ d, 0 ≤ roundSum p A d := fun d =>
    Finset.sum_nonneg fun i _ => hp i
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := univ) (f := roundSum p A) (fun d _ => hnn d)
  rw [lbCost]; rw [hP] at this; simpa using this

/-- `1/D ≤ O`: by Cauchy–Schwarz the load balancing objective is at least `1/D`. -/
lemma one_div_le_lbCost (p : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (hD : 0 < D) (A : Strategy n D) :
    1 / (D : ℝ) ≤ lbCost p A := by
  have hP : ∑ d, roundSum p A d = 1 := by rw [sum_roundSum, hp1]
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin D))) (f := roundSum p A)
  rw [hP, card_univ, Fintype.card_fin] at this
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_le_iff₀ hD', lbCost]
  simpa [mul_comm] using this

/-- An `lbCost`-minimizing allocation is an optimal search strategy for a typical token. -/
theorem isOptimal_of_lbCost_min (p : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (O : Strategy n D)
    (hO : ∀ B : Strategy n D, lbCost p O ≤ lbCost p B) : IsOptimal p p O := by
  intro B
  rw [cost_typical_eq p hp1, cost_typical_eq p hp1]
  linarith [hO B]

/-- Ratio identity behind Lemma 3: `A'/O' = 1 + (A - O)/(1 + O)` where `A, O` are load balancing
values and `A', O'` search costs. -/
theorem lemma3_ratio_eq (p : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (A O : Strategy n D) :
    cost p p A / cost p p O = 1 + (lbCost p A - lbCost p O) / (1 + lbCost p O) := by
  have h := lbCost_nonneg p O
  rw [cost_typical_eq p hp1, cost_typical_eq p hp1]
  field_simp
  ring

/-- Lemma 3 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010]: if `A` is a `(1+ε)`-approximation
of an optimal load balancing allocation `O` (typical normalized token), then `O` is an optimal
search strategy and `A` is a `(1 + ε · O/(1+O))`-approximation for the search problem, where
`O = lbCost p O`. -/
theorem lemma3 (p : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (A O : Strategy n D)
    (hO : ∀ B : Strategy n D, lbCost p O ≤ lbCost p B) (ε : ℝ)
    (hA : lbCost p A ≤ (1 + ε) * lbCost p O) :
    IsOptimal p p O ∧
      cost p p A ≤ (1 + ε * (lbCost p O / (1 + lbCost p O))) * cost p p O := by
  refine ⟨isOptimal_of_lbCost_min p hp1 O hO, ?_⟩
  have h := lbCost_nonneg p O
  rw [cost_typical_eq p hp1, cost_typical_eq p hp1]
  have h1 : (0 : ℝ) < 1 + lbCost p O := by linarith
  have e : (1 + ε * (lbCost p O / (1 + lbCost p O))) * ((1 + lbCost p O) / 2) =
      (1 + lbCost p O + ε * lbCost p O) / 2 := by
    field_simp
  rw [e]
  linarith

/-- Lemma 3 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010], upper bound: `O/(1+O) ≤ 1/2`, so a
`(1+ε)`-approximation for load balancing is a `(1 + ε/2)`-approximation for searching a typical
token. -/
theorem lemma3_half (p : Fin n → ℝ) (hp : 0 ≤ p) (hp1 : ∑ i, p i = 1) (A O : Strategy n D)
    (hO : ∀ B : Strategy n D, lbCost p O ≤ lbCost p B) {ε : ℝ} (hε : 0 ≤ ε)
    (hA : lbCost p A ≤ (1 + ε) * lbCost p O) :
    lbCost p O / (1 + lbCost p O) ≤ 1 / 2 ∧ cost p p A ≤ (1 + ε / 2) * cost p p O := by
  have h0 := lbCost_nonneg p O
  have h1 := lbCost_le_one p hp hp1 O
  have hpos : (0 : ℝ) < 1 + lbCost p O := by linarith
  have hhalf : lbCost p O / (1 + lbCost p O) ≤ 1 / 2 := by
    rw [div_le_iff₀ hpos]; linarith
  refine ⟨hhalf, (lemma3 p hp1 A O hO ε hA).2.trans ?_⟩
  have hc : 0 ≤ cost p p O := by rw [cost_typical_eq p hp1]; linarith
  have : ε * (lbCost p O / (1 + lbCost p O)) ≤ ε / 2 := by nlinarith
  nlinarith

/-- Lemma 3 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010], strict form `ε' < ε/2` claimed in the
paper: for `ε > 0`, the search ratio is strictly below `1 + ε/2`. -/
theorem lemma3_lt_half (p : Fin n → ℝ) (hp : 0 ≤ p) (hp1 : ∑ i, p i = 1) (A O : Strategy n D)
    (hO : ∀ B : Strategy n D, lbCost p O ≤ lbCost p B) {ε : ℝ} (hε : 0 < ε)
    (hA : lbCost p A ≤ (1 + ε) * lbCost p O) :
    cost p p A < (1 + ε / 2) * cost p p O := by
  have h0 := lbCost_nonneg p O
  have h1 := lbCost_le_one p hp hp1 O
  have hA1 := lbCost_le_one p hp hp1 A
  have hOA := hO A
  rw [cost_typical_eq p hp1, cost_typical_eq p hp1]
  -- if `O < 1` the bound `A ≤ (1+ε)O` is strictly below `1 + ε/2` times; if `O = 1` then `A = O`
  rcases h1.lt_or_eq with hlt | heq
  · nlinarith
  · rw [heq] at hOA ⊢
    nlinarith

/-- Lemma 3 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010], lower bound: since `1/D ≤ O`,
`ε · O/(1+O) ≥ ε/(D+1)`; by `lemma3_ratio_eq`, on an instance where the load balancing ratio
`1 + ε` is attained the search ratio is exactly `1 + ε · O/(1+O) ≥ 1 + ε/(D+1)`. -/
theorem lemma3_ratio_ge (p : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (hD : 0 < D) (O : Strategy n D)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ε / ((D : ℝ) + 1) ≤ ε * (lbCost p O / (1 + lbCost p O)) := by
  have hO := one_div_le_lbCost p hp1 hD O
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h0 := lbCost_nonneg p O
  have hpos : (0 : ℝ) < 1 + lbCost p O := by linarith
  have hDO : 1 ≤ (D : ℝ) * lbCost p O := by
    rw [div_le_iff₀ hD'] at hO; linarith
  have hr : 1 / ((D : ℝ) + 1) ≤ lbCost p O / (1 + lbCost p O) := by
    rw [div_le_div_iff₀ (by linarith) hpos]; linarith
  calc ε / ((D : ℝ) + 1) = ε * (1 / ((D : ℝ) + 1)) := by ring
    _ ≤ ε * (lbCost p O / (1 + lbCost p O)) := mul_le_mul_of_nonneg_left hr hε

/-- Lemma 3, attained case: if `lbCost A = (1+ε) · lbCost O`, the search ratio is exactly
`1 + ε · O/(1+O)`, hence at least `1 + ε/(D+1)`. -/
theorem lemma3_tight (p : Fin n → ℝ) (hp1 : ∑ i, p i = 1) (hD : 0 < D) (A O : Strategy n D)
    {ε : ℝ} (hε : 0 ≤ ε) (hA : lbCost p A = (1 + ε) * lbCost p O) :
    cost p p A / cost p p O = 1 + ε * (lbCost p O / (1 + lbCost p O)) ∧
      1 + ε / ((D : ℝ) + 1) ≤ cost p p A / cost p p O := by
  have h := lemma3_ratio_eq p hp1 A O
  have e : (lbCost p A - lbCost p O) / (1 + lbCost p O) =
      ε * (lbCost p O / (1 + lbCost p O)) := by
    rw [hA]; ring
  rw [e] at h
  exact ⟨h, h ▸ by linarith [lemma3_ratio_ge p hp1 hD O hε]⟩

end Podc.MobileDataSearch
