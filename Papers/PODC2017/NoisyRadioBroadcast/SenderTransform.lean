import Papers.PODC2017.NoisyRadioBroadcast.SenderTransformAux

/-!
# Lemma 25: faultless routing schedules can be made robust to sender faults

The transformation itself and its round-level analysis are in `SenderTransformAux`
(`SenderTransform.routingRounds_le`). Here we choose the parameters (`x = m b` sub-messages per
message and meta-rounds of `L = m a` rounds with `b / a < 1 - p`, `m → ∞`) and pass to the
throughput.
-/

namespace Podc.NoisyRadioBroadcast

open Finset Filter
open scoped ENNReal Topology

namespace SenderTransform

/-- A parameter for the Chernoff bound: if `b < a q` then `(1 - (1 - λ) q)^a < λ^b` for some
`0 < λ ≤ 1`. -/
theorem exists_lambda {a b : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hb : 1 ≤ b)
    (hab : (b : ℝ) < a * q) : ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ (1 - (1 - l) * q) ^ a < l ^ b := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have ha : (0 : ℝ) < a := by
    by_contra h
    have : (a : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg a)
    rw [this, zero_mul] at hab; linarith
  set d : ℝ := a * q - b with hd
  have hd0 : 0 < d := by linarith
  have hpos : 0 < 2 * a * b * q := by positivity
  set ε : ℝ := d / (2 * a * b * q) with hε
  have hεd : ε * (2 * a * b * q) = d := by rw [hε]; field_simp
  have hε0 : 0 < ε := div_pos hd0 hpos
  have hε1 : ε ≤ 1 / 2 := by
    rw [hε, div_le_iff₀ hpos]
    nlinarith
  refine ⟨1 - ε, by linarith, by linarith, ?_⟩
  rw [show 1 - (1 - (1 - ε)) * q = 1 - ε * q by ring]
  have hεq : ε * q ≤ 1 / 2 := by nlinarith
  have hεq0 : 0 < ε * q := mul_pos hε0 hq0
  have hA0 : 0 ≤ (1 - ε * q) ^ a := pow_nonneg (by linarith) a
  have h2 : (1 - ε * q) ^ a * (1 + ε * q) ^ a ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 1 + a * (ε * q) ≤ (1 + ε * q) ^ a := one_add_mul_le_pow (by linarith) a
  have h4 : 1 + b * (-ε) ≤ (1 + -ε) ^ b := one_add_mul_le_pow (by linarith) b
  have h5 : 1 < (1 - b * ε) * (1 + a * (ε * q)) := by
    have : (1 - b * ε) * (1 + a * (ε * q)) = 1 + ε * d / 2 := by
      have : a * b * q * ε ^ 2 = ε * d / 2 := by
        rw [← hεd]; ring
      rw [hd]; nlinarith [this]
    rw [this]; nlinarith
  have h6 : (1 - ε * q) ^ a * (1 + a * (ε * q)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h3 hA0).trans h2
  have h7 : (1 - ε * q) ^ a < 1 - b * ε := by
    have hpos' : 0 < 1 + a * (ε * q) := by positivity
    exact lt_of_mul_lt_mul_right (h6.trans_lt h5) hpos'.le
  calc (1 - ε * q) ^ a < 1 - b * ε := h7
    _ = 1 + b * (-ε) := by ring
    _ ≤ (1 + -ε) ^ b := h4
    _ = (1 - ε) ^ b := by ring

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : V)

/-- If the faultless static schedule `b` delivers `k` messages within `R` rounds, then for every
`c < (1 - p) k / R` there are arbitrarily large `k'` with `c ≤ k' / routingRounds k'` in the
sender faults model. -/
theorem frequently_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) {k R : ℕ} (b : StaticSchedule V k)
    (hb : Delivered (run G s .receiver b.toAdaptive (fun _ _ => true) R)) {c : ℝ≥0∞}
    (hc : c < ENNReal.ofReal (1 - p) * ((k : ℝ≥0∞) / (R : ℝ≥0∞))) :
    ∃ᶠ k' : ℕ in atTop, c ≤ (k' : ℝ≥0∞) / (routingRounds G s .sender p k' : ℝ≥0∞) := by
  rw [frequently_atTop]
  intro N
  set q : ℝ := 1 - p with hq
  have hq0 : 0 < q := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hc
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hV : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨s⟩
  have hctop : c ≠ ⊤ := ne_top_of_lt hc
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · -- the faultless schedule needs no round: neither does the transformed one
    refine ⟨k * (N + 1), by nlinarith [Nat.one_le_iff_ne_zero.2 hk], ?_⟩
    have h := routingRounds_le G s b hp0 hp1.le hb (x := N + 1) (L := 1) one_pos le_rfl
      (by simp only [CharP.cast_eq_zero, zero_mul]; positivity)
    simp only [zero_mul, Nat.cast_zero, nonpos_iff_eq_zero] at h
    rw [h]
    simp only [ENat.toENNReal_zero]
    rw [ENNReal.div_zero (by simp [hk])]
    exact le_top
  -- the real target ratio
  set c₀ := c.toReal with hc₀
  have hc₀0 : 0 ≤ c₀ := ENNReal.toReal_nonneg
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hkr : (0 : ℝ) < k := by linarith
  have hc' : c₀ < q * k / R := by
    have : ENNReal.ofReal q * ((k : ℝ≥0∞) / (R : ℝ≥0∞)) = ENNReal.ofReal (q * k / R) := by
      rw [mul_div_assoc, ENNReal.ofReal_mul hq0.le, ENNReal.ofReal_div_of_pos hRr,
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [this] at hc
    exact (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 hc
  set θ : ℝ := c₀ * R / k with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθq : θ < q := by
    rw [hθ, div_lt_iff₀ hkr]
    rw [lt_div_iff₀ hRr] at hc'
    linarith
  -- rational approximation `θ ≤ b / a < q`
  obtain ⟨a, ha⟩ := exists_nat_gt (1 / (q - θ))
  have ha' : 1 < a * (q - θ) := by
    rwa [div_lt_iff₀ (by linarith)] at ha
  set bb : ℕ := ⌊θ * a⌋₊ + 1 with hbb
  have hbb1 : 1 ≤ bb := by omega
  have hbbθ : θ * a < bb := by
    rw [hbb]; push_cast; exact Nat.lt_floor_add_one _
  have hbbq : (bb : ℝ) < a * q := by
    have := Nat.floor_le (show 0 ≤ θ * a by positivity)
    rw [hbb]; push_cast; nlinarith
  obtain ⟨l, hl0, hl1, hlab⟩ := exists_lambda hq0 hq1 hbb1 hbbq
  set γ : ℝ := 1 - (1 - l) * q with hγ
  have hγ0 : 0 ≤ γ := by
    have : (1 - l) * q ≤ 1 := by nlinarith
    linarith
  set β : ℝ := γ ^ a / l ^ bb with hβ
  have hβ0 : 0 ≤ β := div_nonneg (pow_nonneg hγ0 _) (pow_nonneg hl0.le _)
  have hβ1 : β < 1 := (div_lt_one (pow_pos hl0 _)).2 hlab
  set C : ℝ := R * Fintype.card V * k * bb with hC
  have hCpos : 0 < C := by
    have : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
    have : (0 : ℝ) < bb := by exact_mod_cast hbb1
    positivity
  have hev := ((tendsto_self_mul_const_pow_of_lt_one hβ0 hβ1).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / C by positivity))).and (eventually_ge_atTop (N + 1))
  obtain ⟨m, hm, hmN⟩ := hev.exists
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.le_add_left 1 N).trans hmN
  -- the parameters `x = m * bb`, `L = m * a`
  have hm0 : (0 : ℝ) < m := by linarith
  have hbound : (R * Fintype.card V : ℝ) * ((l ^ (m * bb - 1))⁻¹ * γ ^ (m * a)) ≤
      1 / ((k * (m * bb) : ℕ) : ℝ) := by
    have h1 : (l ^ (m * bb - 1))⁻¹ * γ ^ (m * a) ≤ β ^ m := by
      have : (l ^ (m * bb - 1))⁻¹ ≤ (l ^ (m * bb))⁻¹ :=
        inv_anti₀ (pow_pos hl0 _) (pow_le_pow_of_le_one hl0.le hl1 (Nat.sub_le _ _))
      calc (l ^ (m * bb - 1))⁻¹ * γ ^ (m * a) ≤ (l ^ (m * bb))⁻¹ * γ ^ (m * a) :=
            mul_le_mul_of_nonneg_right this (pow_nonneg hγ0 _)
        _ = β ^ m := by
            rw [hβ, div_pow, ← pow_mul, ← pow_mul, mul_comm a m, mul_comm bb m]
            ring
    have h2 : (R * Fintype.card V : ℝ) * β ^ m * ((k * (m * bb) : ℕ) : ℝ) < 1 := by
      have : (R * Fintype.card V : ℝ) * β ^ m * ((k * (m * bb) : ℕ) : ℝ) = C * (m * β ^ m) := by
        rw [hC]; push_cast; ring
      rw [this]
      calc C * (m * β ^ m) < C * (1 / C) := mul_lt_mul_of_pos_left hm hCpos
        _ = 1 := by field_simp
    have hkx : (0 : ℝ) < ((k * (m * bb) : ℕ) : ℝ) := by
      have : 0 < k * (m * bb) := Nat.mul_pos (Nat.pos_of_ne_zero hk) (Nat.mul_pos (by omega) (by omega))
      exact_mod_cast this
    rw [le_div_iff₀ hkx]
    calc (R * Fintype.card V : ℝ) * ((l ^ (m * bb - 1))⁻¹ * γ ^ (m * a)) *
          ((k * (m * bb) : ℕ) : ℝ) ≤ (R * Fintype.card V : ℝ) * β ^ m * ((k * (m * bb) : ℕ) : ℝ) := by
          gcongr
      _ ≤ 1 := h2.le
  have hrr := routingRounds_le G s b hp0 hp1.le hb (x := m * bb) (L := m * a) hl0 hl1 hbound
  refine ⟨k * (m * bb), ?_, ?_⟩
  · calc N ≤ m := by omega
      _ ≤ m * bb := Nat.le_mul_of_pos_right m hbb1
      _ ≤ k * (m * bb) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hk)
  · have hle : ((k * (m * bb) : ℕ) : ℝ≥0∞) / ((R * (m * a) : ℕ) : ℝ≥0∞) ≤
        ((k * (m * bb) : ℕ) : ℝ≥0∞) / (routingRounds G s .sender p (k * (m * bb)) : ℝ≥0∞) := by
      refine ENNReal.div_le_div_left ?_ _
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hrr
    refine le_trans ?_ hle
    have ha0 : (0 : ℝ) < a := by
      have : (0 : ℝ) < a * (q - θ) := by linarith
      by_contra h
      have : (a : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg a)
      simp_all
    have hden : (0 : ℝ) < ((R * (m * a) : ℕ) : ℝ) := by
      push_cast; positivity
    rw [← ENNReal.ofReal_toReal hctop, ← ENNReal.ofReal_natCast (k * (m * bb)),
      ← ENNReal.ofReal_natCast (R * (m * a)), ← ENNReal.ofReal_div_of_pos hden]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hden]
    have : θ * k = c₀ * R := by rw [hθ]; field_simp
    push_cast
    have : c₀ * R * a ≤ k * bb := by nlinarith
    nlinarith

end SenderTransform

/-- **Lemma 25** of the paper: a set of (faultless) routing schedules with throughput `τ` can be
transformed into adaptive routing schedules with throughput `τ (1 - p)` in the sender faults
model. Stated for the optimal faultless schedules. -/
theorem lemma25 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : V) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ENNReal.ofReal (1 - p) * faultlessThroughput G s ≤ routingThroughput G s .sender p := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  refine le_limsup_of_frequently_le ?_
  have hc' : c < ⨆ k : ℕ, ENNReal.ofReal (1 - p) * ((k : ℝ≥0∞) / (faultlessRounds G s k : ℝ≥0∞)) :=
    by
    rw [← ENNReal.mul_iSup]
    exact hc.trans_le (mul_le_mul_right limsup_le_iSup _)
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hc'
  by_cases hex : ∃ R, ∃ b : StaticSchedule V k,
      Delivered (run G s .receiver b.toAdaptive (fun _ _ => true) R)
  · classical
    have hF : faultlessRounds G s k = (Nat.find hex : ℕ∞) :=
      le_antisymm (by unfold faultlessRounds; exact iInf₂_le (Nat.find hex) (Nat.find_spec hex))
        (by unfold faultlessRounds; exact le_iInf₂ fun R hR => Nat.cast_le.2 (Nat.find_min' hex hR))
    obtain ⟨b, hb⟩ := Nat.find_spec hex
    rw [hF, ENat.toENNReal_coe] at hk
    exact SenderTransform.frequently_le G s hp0 hp1 b hb hk
  · have hF : faultlessRounds G s k = ⊤ := by
      unfold faultlessRounds
      exact iInf₂_eq_top.2 fun R hR => absurd ⟨R, hR⟩ hex
    rw [hF] at hk
    simp at hk

end Podc.NoisyRadioBroadcast
