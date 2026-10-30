import Papers.PODC2012.CollaborativeSearchPlane.Phases

/-!
# Summing the expected time of a phased search

The analyses of Theorem 3.1 and Theorem 3.3 share one pattern: from block `s` on, every block
`s + m` contains `m + 1` (or more) "good" phases, each of which ends the search with probability
bounded away from `0`, so `Pr[not found before block s + m] ≤ exp(-β m(m+1)/2)`; since block `b`
lasts `O(2^b + B 4^b)`, the expected time is `O(2^s + B 4^s)`.

* `prob_notFound_le` — the product bound for `Pr[not found before block b]`;
* `tsum_le_of_gauss` — the summation `∑_b (A 2^b + B 4^b) e^{-β m_b(m_b+1)/2} ≤ (A 2^s + B 4^s)(1 + G β)`
  with `m_b = b - s` and the constant `G β = ∑_ℓ 4^ℓ e^{-βℓ(ℓ+1)/2}`.
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset Filter
open scoped ENNReal

/-- `∑_ℓ 4^ℓ e^{-βℓ(ℓ+1)/2}`. -/
noncomputable def gaussConst (β : ℝ) : ℝ := ∑' ℓ : ℕ, (4 : ℝ) ^ ℓ * Real.exp (-β * (ℓ * (ℓ + 1) / 2))

theorem summable_gauss {β : ℝ} (hβ : 0 < β) :
    Summable fun ℓ : ℕ => (4 : ℝ) ^ ℓ * Real.exp (-β * (ℓ * (ℓ + 1) / 2)) := by
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
    (Eventually.of_forall fun ℓ => by positivity) ?_
  have e : ∀ ℓ : ℕ, ‖(4 : ℝ) ^ (ℓ + 1) * Real.exp (-β * (((ℓ + 1 : ℕ) : ℝ) * ((ℓ + 1 : ℕ) + 1) / 2))‖
      / ‖(4 : ℝ) ^ ℓ * Real.exp (-β * ((ℓ : ℝ) * (ℓ + 1) / 2))‖ = 4 * Real.exp (-β * (ℓ + 1)) := by
    intro ℓ
    have hx : -β * (((ℓ + 1 : ℕ) : ℝ) * ((ℓ + 1 : ℕ) + 1) / 2)
        = -β * ((ℓ : ℝ) * (ℓ + 1) / 2) + -β * (ℓ + 1) := by push_cast; ring
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), hx,
      Real.exp_add, div_eq_iff (by positivity), pow_succ]
    ring
  simp_rw [e]
  have : Tendsto (fun ℓ : ℕ => -β * ((ℓ : ℝ) + 1)) atTop atBot := by
    have h1 : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.const_mul_atTop_of_neg (by linarith)
  have h2 := (Real.tendsto_exp_atBot.comp this).const_mul 4
  simpa using h2

theorem gaussConst_nonneg (β : ℝ) : 0 ≤ gaussConst β :=
  tsum_nonneg fun ℓ => by positivity

-- CSLib candidate
/-- Summation of block durations against the Gaussian-type tail. -/
theorem tsum_le_of_gauss {β : ℝ} (hβ : 0 < β) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (s : ℕ)
    (f : ℕ → ℝ≥0∞)
    (hf : ∀ b, f b ≤ ENNReal.ofReal ((A * 2 ^ b + B * 4 ^ b) *
      Real.exp (-β * (((b - s : ℕ) : ℝ) * ((b - s : ℕ) + 1) / 2)))) :
    ∑' b, f b ≤ ENNReal.ofReal ((A * 2 ^ s + B * 4 ^ s) * (1 + gaussConst β)) := by
  set g : ℕ → ℝ := fun b => (A * 2 ^ b + B * 4 ^ b) *
      Real.exp (-β * (((b - s : ℕ) : ℝ) * ((b - s : ℕ) + 1) / 2))
  have hg0 : ∀ b, 0 ≤ g b := fun b => by positivity
  -- domination of the tail by the Gaussian series
  have htail : ∀ ℓ, g (ℓ + s) ≤ (A * 2 ^ s + B * 4 ^ s) *
      ((4 : ℝ) ^ ℓ * Real.exp (-β * (ℓ * (ℓ + 1) / 2))) := by
    intro ℓ
    simp only [g, Nat.add_sub_cancel]
    have h2 : (2 : ℝ) ^ (ℓ + s) ≤ 2 ^ s * 4 ^ ℓ := by
      rw [pow_add, mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ)
        (by positivity)
    have h4 : (4 : ℝ) ^ (ℓ + s) = 4 ^ s * 4 ^ ℓ := by rw [pow_add, mul_comm]
    have hE := Real.exp_pos (-β * ((ℓ : ℝ) * (ℓ + 1) / 2))
    rw [h4]
    have : A * 2 ^ (ℓ + s) + B * (4 ^ s * 4 ^ ℓ) ≤ (A * 2 ^ s + B * 4 ^ s) * 4 ^ ℓ := by
      nlinarith
    nlinarith
  have hsumm_tail : Summable fun ℓ => g (ℓ + s) :=
    Summable.of_nonneg_of_le (fun ℓ => hg0 _) htail ((summable_gauss hβ).mul_left _)
  have hsumm : Summable g := (summable_nat_add_iff s).1 hsumm_tail
  have hhead : ∑ b ∈ range s, g b ≤ A * 2 ^ s + B * 4 ^ s := by
    have : ∀ b ∈ range s, g b ≤ A * 2 ^ b + B * 4 ^ b := by
      intro b hb
      have hbs : b - s = 0 := by have := mem_range.1 hb; omega
      simp [g, hbs]
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h2 : ∑ b ∈ range s, (2 : ℝ) ^ b ≤ 2 ^ s := by
      have := geom_sum_mul (2 : ℝ) s; norm_num at this; linarith
    have h4 : ∑ b ∈ range s, (4 : ℝ) ^ b ≤ 4 ^ s := by
      have := geom_sum_mul (4 : ℝ) s; norm_num at this
      have : (0 : ℝ) ≤ ∑ b ∈ range s, (4 : ℝ) ^ b := by positivity
      nlinarith
    nlinarith
  have htail' : ∑' ℓ, g (ℓ + s) ≤ (A * 2 ^ s + B * 4 ^ s) * gaussConst β := by
    rw [gaussConst, ← tsum_mul_left]
    exact hsumm_tail.tsum_le_tsum htail ((summable_gauss hβ).mul_left _)
  calc ∑' b, f b ≤ ∑' b, ENNReal.ofReal (g b) := ENNReal.tsum_le_tsum hf
    _ = ENNReal.ofReal (∑' b, g b) := (ENNReal.ofReal_tsum_of_nonneg hg0 hsumm).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [← hsumm.sum_add_tsum_nat_add s]
        nlinarith

-- CSLib candidate
/-- If from block `s` on the blocks' "not found" factors are at most `exp(-β(b - s + 1))` (and
at most `1` always), then `∏_{b' < b} Q b' ≤ exp(-β m(m+1)/2)`, `m = b - s`. -/
theorem prod_le_gauss {β : ℝ} (s : ℕ) (Q : ℕ → ℝ≥0∞) (hQ1 : ∀ b, Q b ≤ 1)
    (hQ : ∀ b, s ≤ b → Q b ≤ ENNReal.ofReal (Real.exp (-β * ((b - s : ℕ) + 1)))) (b : ℕ) :
    ∏ b' ∈ range b, Q b' ≤
      ENNReal.ofReal (Real.exp (-β * (((b - s : ℕ) : ℝ) * ((b - s : ℕ) + 1) / 2))) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [prod_range_succ]
    rcases lt_or_ge b s with hbs | hbs
    · have e1 : b + 1 - s = 0 := by omega
      have e2 : b - s = 0 := by omega
      rw [e1]; rw [e2] at ih
      calc (∏ b' ∈ range b, Q b') * Q b ≤ (∏ b' ∈ range b, Q b') * 1 := by gcongr; exact hQ1 b
        _ ≤ _ := by simpa using ih
    · have e1 : b + 1 - s = (b - s) + 1 := by omega
      calc (∏ b' ∈ range b, Q b') * Q b
          ≤ ENNReal.ofReal (Real.exp (-β * (((b - s : ℕ) : ℝ) * ((b - s : ℕ) + 1) / 2)))
            * ENNReal.ofReal (Real.exp (-β * ((b - s : ℕ) + 1))) := by
            gcongr
            exact hQ b hbs
        _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, e1]
            congr 2
            push_cast
            ring

variable {P : ℕ → Type} [∀ b, Fintype (P b)]

/-- If in the phases `G` of block `b` every agent succeeds with probability `≥ q`, the block's
"not found" factor is at most `exp(-q k |G|)`. -/
theorem blockFail_le_exp {k : ℕ} (σ : ℕ) (R : (Σ b, P b) → ℕ) (t : Fin k × (Σ b, P b) → ℕ)
    (τ : Node) (b : ℕ) (G : Finset (P b)) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ p ∈ G, ∀ a, ENNReal.ofReal q ≤ uniformBall (R ⟨b, p⟩) (spiralSucc σ τ (t (a, ⟨b, p⟩)))) :
    blockFail σ R t τ b ≤ ENNReal.ofReal (Real.exp (-(q * k * G.card))) := by
  unfold blockFail
  calc ∏ p : P b, ∏ a : Fin k, uniformBall (R ⟨b, p⟩) (spiralSucc σ τ (t (a, ⟨b, p⟩)))ᶜ
      ≤ ∏ p ∈ G, ∏ a : Fin k, uniformBall (R ⟨b, p⟩) (spiralSucc σ τ (t (a, ⟨b, p⟩)))ᶜ :=
        Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ G)
          fun _ _ _ => Finset.prod_le_one fun _ _ => prob_le_one
    _ ≤ ∏ _p ∈ G, ∏ _a : Fin k, ENNReal.ofReal (1 - q) := by
        gcongr with p hp a
        rw [prob_compl_eq_one_sub ((spiralSucc σ τ _).to_countable.measurableSet),
          ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
        exact tsub_le_tsub_left (h p hp a) 1
    _ = ENNReal.ofReal ((1 - q) ^ (k * G.card)) := by
        rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
          ENNReal.ofReal_pow (by linarith), mul_comm]
    _ ≤ ENNReal.ofReal (Real.exp (-(q * k * G.card))) := by
        apply ENNReal.ofReal_le_ofReal
        calc (1 - q) ^ (k * G.card) ≤ Real.exp (-q) ^ (k * G.card) := by
              gcongr
              · linarith [Real.add_one_le_exp (-q)]
          _ = _ := by rw [← Real.exp_nat_mul]; push_cast; ring_nf

end Podc.CollaborativeSearchPlane
