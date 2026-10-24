import Papers.PODC2025.RendezvousLabeledLine.Analysis

/-!
# In-sync rendezvous (Section 4.4): Lemmas 4.4–4.7

To treat both agents symmetrically, an agent is given by its start `v`, its frame orientation `ε`
and its wake-up round `d`; its global position is `P v ε d t = X v ε (t - d)`. In the paper
`α = (vα, εα, 0)` and `β = (vβ, εβ, τ)`.
-/

namespace Podc.RendezvousLabeledLine

open Function

variable {κ : ℕ} (Rl : ColRuling κ) {ℓ : ℤ → ℕ} (hℓ : Injective ℓ)

/-- Global position of an agent started at `v` with orientation `ε` and woken up in round `d`. -/
noncomputable abbrev P (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (d : ℕ) : ℕ → ℤ := delayed d (X Rl ℓ v ε)

/-- The plan of that agent in iteration `k`. -/
noncomputable abbrev pl (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (k : ℕ) : Option (ℕ × ℤ × ℕ) :=
  plan Rl (ℓ ∘ frame v ε) (2 ^ k)

lemma frame_add (v : ℤ) (ε : ℤˣ) (a b : ℤ) : frame v ε (a + b) = frame (frame v ε a) ε b := by
  simp only [frame]; ring

lemma P_at (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (d T : ℕ) (t : ℕ) :
    P Rl ℓ v ε d (d + t) = X Rl ℓ v ε t := by
  simp [P, delayed]

include hℓ

lemma lip_P (v : ℤ) (ε : ℤˣ) (d : ℕ) : Lip (P Rl ℓ v ε d) :=
  Algo.lip_delayed ((alg5 Rl).lip_traj hℓ v ε) d

lemma inj_frame (v : ℤ) (ε : ℤˣ) : Injective (ℓ ∘ frame v ε) := hℓ.comp (frame_injective v ε)

/-- Position during the searching phase with plan `some (R, r, c)`. -/
lemma P_search {v : ℤ} {ε : ℤˣ} {d k R : ℕ} {r : ℤ} {c : ℕ}
    (hp : pl Rl ℓ v ε k = some (R, r, c)) (u : ℕ) (hu : u < 24 * 2 ^ k) :
    P Rl ℓ v ε d (d + (iterStart k + (4 * 2 ^ k + u))) = frame v ε (sw (2 ^ k) R r c u) := by
  rw [P_at Rl ℓ v ε d 0, X_apply, pos5_some Rl hp _ (by omega) (by omega)]
  congr 2; omega

/-- During the searching phase the agent is within `10 R - 1` of its start (`0` with no plan). -/
lemma P_search_near {v : ℤ} {ε : ℤˣ} {d k : ℕ} (t : ℕ) (ht : d + iterStart k + 4 * 2 ^ k ≤ t)
    (ht' : t < d + iterStart k + 28 * 2 ^ k) :
    |P Rl ℓ v ε d t - v| ≤ (match pl Rl ℓ v ε k with
      | none => 0 | some (R, _, _) => 10 * (R : ℤ) - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = d + (iterStart k + s) := ⟨t - d - iterStart k, by omega⟩
  rw [P_at Rl ℓ v ε d 0, abs_X_sub]
  rcases hp : pl Rl ℓ v ε k with _ | ⟨R, r, c⟩
  · rw [pos5_none Rl hp s (by omega) (by omega)]; simp
  · exact abs_pos5_some_le Rl (inj_frame hℓ v ε) hp s (by omega) (by omega)

/-! ### Lemma 4.4 -/

/-- **Lemma 4.4.** If `L = 2^k ≥ 8 κ D log* ℓ(u₀) + 128 D` for a node `u₀` within distance `2D`
of the agent's start (e.g. within `D` of one of the two starts), the agent finds a plan with
`R* ≥ 2D`. -/
theorem lemma_4_4 (v : ℤ) (ε : ℤˣ) (k D : ℕ) (hD : 1 ≤ D) (u₀ : ℤ) (hu₀ : |u₀ - v| ≤ 2 * D)
    (hL : 8 * κ * D * lstar (ℓ u₀) + 128 * D ≤ 2 ^ k) :
    ∃ R r c, pl Rl ℓ v ε k = some (R, r, c) ∧ 2 * D ≤ R := by
  set RD := 4 ^ Nat.clog 4 (2 * D)
  have h1 : 2 * D ≤ RD := Nat.le_pow_clog (by norm_num) _
  have h2 : RD < 4 * (2 * D) := Nat.pow_clog_lt_mul (by norm_num) (by omega)
  set u := (ε : ℤ) * (u₀ - v)
  have hfu : frame v ε u = u₀ := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [frame, u]
  have hu : |u| = |u₀ - v| := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [u, abs_sub_comm]
  have hgood : Good κ (ℓ ∘ frame v ε) (2 ^ k) RD := by
    refine ⟨⟨_, rfl⟩, by omega, u, ?_, ?_⟩
    · rw [hu]; push_cast; omega
    · have : κ * RD * lstar (ℓ u₀) ≤ 8 * κ * D * lstar (ℓ u₀) := by
        have := Nat.mul_le_mul_right (κ * lstar (ℓ u₀)) (show RD ≤ 8 * D by omega)
        nlinarith
      have hN : 2 * D + κ * RD * lstar (ℓ u₀) ≤ 2 ^ k := by linarith
      have hN' : ((2 * D + κ * RD * lstar (ℓ u₀) : ℕ) : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) :=
        by exact_mod_cast hN
      simp only [comp_apply, hfu, hu]
      push_cast at hN' ⊢; linarith
  rcases hp : pl Rl ℓ v ε k with _ | ⟨R, r, c⟩
  · exact absurd hgood (plan_none Rl hp RD)
  · obtain ⟨-, hmax, -⟩ := plan_some Rl (inj_frame hℓ v ε) hp
    exact ⟨R, r, c, rfl, le_trans h1 (hmax RD hgood)⟩

/-! ### Lemma 4.5: mismatched ruling sets -/

/-- **Lemma 4.5** (generic form). Agent 1 has the plan `some (R, r, c)` with `R ≥ D`, agent 2 has
no plan or a plan with a smaller `R'`, and the wake-up rounds differ by at most `L`. Then the
agents meet or cross during the `ZWalk(8R)` of agent 1 around its ruling-set node, i.e. by round
`d₁ + T_L + 5L + 24R`. -/
theorem lemma_4_5_gen {v₁ v₂ : ℤ} {ε₁ ε₂ : ℤˣ} {d₁ d₂ k R : ℕ} {r : ℤ} {c : ℕ}
    (hp₁ : pl Rl ℓ v₁ ε₁ k = some (R, r, c)) (hD : (v₁ - v₂).natAbs ≤ R)
    (hp₂ : pl Rl ℓ v₂ ε₂ k = none ∨ ∃ R' r' c', pl Rl ℓ v₂ ε₂ k = some (R', r', c') ∧ R' < R)
    (hd₁ : d₂ ≤ d₁ + 2 ^ k) (hd₂ : d₁ ≤ d₂ + 2 ^ k) :
    MeetOrCrossIn (P Rl ℓ v₁ ε₁ d₁) (P Rl ℓ v₂ ε₂ d₂)
      (d₁ + (iterStart k + (4 * 2 ^ k + (2 ^ k + 8 * R))))
      (d₁ + (iterStart k + (4 * 2 ^ k + (2 ^ k + 24 * R)))) := by
  obtain ⟨hR, hL, hr⟩ := plan_some_bounds Rl (inj_frame hℓ v₁ ε₁) hp₁
  have hrz : |r| ≤ 2 ^ k := by
    have : (16 * R : ℤ) ≤ 2 ^ k := by exact_mod_cast hL
    omega
  have e1 := P_search Rl hℓ (d := d₁) hp₁ (2 ^ k + 8 * R) (by omega)
  have e2 := P_search Rl hℓ (d := d₁) hp₁ (2 ^ k + 24 * R) (by omega)
  rw [sw_of_zwalk (by omega) (by omega), Nat.add_sub_cancel_left, zw_L] at e1
  have hz3 : zw (8 * R) (24 * R) = -((8 * R : ℕ) : ℤ) := by
    rw [show 24 * R = 3 * (8 * R) by ring, zw_three]
  rw [sw_of_zwalk (by omega) (by omega), Nat.add_sub_cancel_left, hz3] at e2
  rw [frame_add] at e1 e2
  refine sweep (lip_P Rl hℓ v₁ ε₁ d₁) (lip_P Rl hℓ v₂ ε₂ d₂) le_rfl (by omega) (by omega) le_rfl
    e1 (by rw [e2]) ?_
  intro t ht ht'
  have hnear := P_search_near Rl hℓ (v := v₂) (ε := ε₂) (d := d₂) (k := k) t (by omega) (by omega)
  -- agent 2 is within `10 R' - 1 ≤ 5R/2` of `v₂`
  have h2 : |P Rl ℓ v₂ ε₂ d₂ t - v₂| ≤ 3 * (R : ℤ) := by
    rcases hp₂ with hp₂ | ⟨R', r', c', hp₂, hlt⟩
    · rw [hp₂] at hnear; exact hnear.trans (by positivity)
    · rw [hp₂] at hnear
      have := (plan_some Rl (inj_frame hℓ v₂ ε₂) hp₂).1.1.four_mul_le
        (plan_some Rl (inj_frame hℓ v₁ ε₁) hp₁).1.1 hlt
      simp only at hnear
      have : (4 * R' : ℤ) ≤ R := by exact_mod_cast this
      omega
  have h12 : |v₂ - v₁| ≤ (R : ℤ) := by
    rw [abs_sub_comm]; have : (((v₁ - v₂).natAbs : ℕ) : ℤ) ≤ R := by exact_mod_cast hD
    rwa [Int.natCast_natAbs] at this
  have h3 : |frame v₁ ε₁ r - v₁| = |r| := abs_frame_sub _ _ _
  push_cast
  calc |P Rl ℓ v₂ ε₂ d₂ t - frame v₁ ε₁ r|
      = |(P Rl ℓ v₂ ε₂ d₂ t - v₂) + (v₂ - v₁) - (frame v₁ ε₁ r - v₁)| := by ring_nf
    _ ≤ |(P Rl ℓ v₂ ε₂ d₂ t - v₂) + (v₂ - v₁)| + |frame v₁ ε₁ r - v₁| := abs_sub _ _
    _ ≤ |P Rl ℓ v₂ ε₂ d₂ t - v₂| + |v₂ - v₁| + |frame v₁ ε₁ r - v₁| := by
        gcongr; exact abs_add_le _ _
    _ ≤ 8 * (R : ℤ) := by omega

/-! ### Lemma 4.6: the same ruling-set node -/

/-- **Lemma 4.6** (generic form). Both agents chose the same ruling-set node (in global
coordinates) and their wake-up rounds differ by at most `14 R`: they meet there before either of
them starts its `ZWalk(8R)`. -/
theorem lemma_4_6_gen {v₁ v₂ : ℤ} {ε₁ ε₂ : ℤˣ} {d₁ d₂ k R : ℕ} {r₁ r₂ : ℤ} {c₁ c₂ : ℕ}
    (hp₁ : pl Rl ℓ v₁ ε₁ k = some (R, r₁, c₁)) (hp₂ : pl Rl ℓ v₂ ε₂ k = some (R, r₂, c₂))
    (hr : frame v₁ ε₁ r₁ = frame v₂ ε₂ r₂) (hd₁ : d₂ ≤ d₁ + 14 * R) (hd₂ : d₁ ≤ d₂ + 14 * R) :
    ∃ t ≤ min d₁ d₂ + (iterStart k + 5 * 2 ^ k), P Rl ℓ v₁ ε₁ d₁ t = P Rl ℓ v₂ ε₂ d₂ t := by
  obtain ⟨hR, hL, hr₁⟩ := plan_some_bounds Rl (inj_frame hℓ v₁ ε₁) hp₁
  obtain ⟨-, -, hr₂⟩ := plan_some_bounds Rl (inj_frame hℓ v₂ ε₂) hp₂
  have ha₁ : (r₁.natAbs : ℤ) = |r₁| := Int.natCast_natAbs r₁
  have ha₂ : (r₂.natAbs : ℤ) = |r₂| := Int.natCast_natAbs r₂
  have hb₁ : r₁.natAbs + 1 ≤ 2 * R := by omega
  have hb₂ : r₂.natAbs + 1 ≤ 2 * R := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = max (d₁ + r₁.natAbs) (d₂ + r₂.natAbs) := ⟨_, rfl⟩
  refine ⟨m + (iterStart k + 4 * 2 ^ k), by omega, ?_⟩
  have e1 := P_search Rl hℓ (d := d₁) hp₁ (m - d₁) (by omega)
  have e2 := P_search Rl hℓ (d := d₂) hp₂ (m - d₂) (by omega)
  rw [sw_of_le (by omega), moveTo_of_le r₁ _ (by push_cast; omega)] at e1
  rw [sw_of_le (by omega), moveTo_of_le r₂ _ (by push_cast; omega)] at e2
  rw [show m + (iterStart k + 4 * 2 ^ k) = d₁ + (iterStart k + (4 * 2 ^ k + (m - d₁))) by omega,
    e1, hr, ← e2]
  congr 1; omega

/-! ### Lemma 4.7: distinct ruling-set nodes -/

omit hℓ in
lemma sw_bit_set {L R : ℕ} {r : ℤ} {c i : ℕ} (hR : 1 ≤ R) (hi : i < 5) (hb : c.testBit i = true)
    (j s : ℕ) (hj : j ≤ 1) (hs : s < 32 * R) (hpos : 0 < 32 * R * j + s) :
    sw L R r c (L + 32 * R + (64 * R * i + (32 * R * j + s))) = r + zw (8 * R) s := by
  have hi' : 64 * R * i ≤ 64 * R * 4 := Nat.mul_le_mul_left _ (by omega)
  have hj' : 32 * R * j ≤ 32 * R := by nlinarith
  rw [sw_of_bits (by omega) (by omega), Nat.add_sub_cancel_left]
  have hdiv : (64 * R * i + (32 * R * j + s)) / (64 * R) = i := by
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm i]; omega
    · rw [add_mul, one_mul, mul_comm i]; omega
  have hmod : (64 * R * i + (32 * R * j + s)) % (32 * R) = s := by
    rw [show 64 * R * i + (32 * R * j + s) = s + 32 * R * (2 * i + j) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  rw [hdiv, hmod, ite_eq_left hb]

omit hℓ in
lemma sw_bit_unset {L R : ℕ} {r : ℤ} {c i : ℕ} (hR : 1 ≤ R) (hi : i < 5)
    (hb : c.testBit i = false) (o : ℕ) (ho : 64 * R * i < o) (ho' : o < 64 * R * i + 64 * R) :
    sw L R r c (L + 32 * R + o) = r := by
  have hi' : 64 * R * i ≤ 64 * R * 4 := Nat.mul_le_mul_left _ (by omega)
  rw [sw_of_bits (by omega) (by omega), Nat.add_sub_cancel_left]
  have hdiv : o / (64 * R) = i := by
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm i]; omega
    · rw [add_mul, one_mul, mul_comm i]; omega
  rw [hdiv, hb]; simp

/-- **Lemma 4.7** (generic form). Both agents have plans with the same `R`, agent 1's colour has
bit `i` set and agent 2's has it unset, the two ruling-set nodes are within `8R` of each other and
the wake-up rounds differ by less than `32 R`. Then the agents meet or cross while agent 1 runs
one of its two `ZWalk(8R)` of bit `i` and agent 2 waits at its ruling-set node. -/
theorem lemma_4_7_gen {v₁ v₂ : ℤ} {ε₁ ε₂ : ℤˣ} {d₁ d₂ k R : ℕ} {r₁ r₂ : ℤ} {c₁ c₂ i : ℕ}
    (hp₁ : pl Rl ℓ v₁ ε₁ k = some (R, r₁, c₁)) (hp₂ : pl Rl ℓ v₂ ε₂ k = some (R, r₂, c₂))
    (hi : i < 5) (hb₁ : c₁.testBit i = true) (hb₂ : c₂.testBit i = false)
    (hr : |frame v₂ ε₂ r₂ - frame v₁ ε₁ r₁| ≤ 8 * R) (hd₁ : d₁ < d₂ + 32 * R)
    (hd₂ : d₂ < d₁ + 32 * R) :
    ∃ W W', W' ≤ max d₁ d₂ + (iterStart k + (5 * 2 ^ k + (32 * R + (64 * R * i + 56 * R)))) ∧
      MeetOrCrossIn (P Rl ℓ v₁ ε₁ d₁) (P Rl ℓ v₂ ε₂ d₂) W W' := by
  obtain ⟨hR, hL, hr₁⟩ := plan_some_bounds Rl (inj_frame hℓ v₁ ε₁) hp₁
  have hi' : 64 * R * i ≤ 64 * R * 4 := Nat.mul_le_mul_left _ (by omega)
  have hz1 : zw (8 * R) (8 * R) = ((8 * R : ℕ) : ℤ) := zw_L _
  have hz3 : zw (8 * R) (24 * R) = -((8 * R : ℕ) : ℤ) := by
    rw [show 24 * R = 3 * (8 * R) by ring, zw_three]
  -- `j = 0`: first ZWalk of bit `i` (if agent 1 woke up later), `j = 1`: the second one
  obtain ⟨j, hj, hjd⟩ : ∃ j, j ≤ 1 ∧ (j = 0 → d₂ ≤ d₁) ∧ (j = 1 → d₁ ≤ d₂) := by
    rcases le_total d₂ d₁ with h | h
    · exact ⟨0, by omega, fun _ => h, by omega⟩
    · exact ⟨1, le_rfl, by omega, fun _ => h⟩
  have hjR : 32 * R * j ≤ 32 * R := by nlinarith
  have hjR' : j = 0 ∨ j = 1 := by omega
  set t₀ := d₁ + (iterStart k + (4 * 2 ^ k + (2 ^ k + 32 * R + (64 * R * i + (32 * R * j)))))
  have e1 := P_search Rl hℓ (d := d₁) hp₁ (2 ^ k + 32 * R + (64 * R * i + (32 * R * j + 8 * R)))
    (by omega)
  have e2 := P_search Rl hℓ (d := d₁) hp₁ (2 ^ k + 32 * R + (64 * R * i + (32 * R * j + 24 * R)))
    (by omega)
  rw [sw_bit_set hR hi hb₁ j _ hj (by omega) (by omega), hz1, frame_add] at e1
  rw [sw_bit_set hR hi hb₁ j _ hj (by omega) (by omega), hz3, frame_add] at e2
  refine ⟨t₀ + 8 * R, t₀ + 24 * R, ?_, sweep (lip_P Rl hℓ v₁ ε₁ d₁) (lip_P Rl hℓ v₂ ε₂ d₂)
    le_rfl (by omega) (by omega) le_rfl (by rw [← e1]; congr 1; omega)
    (by rw [← e2]; congr 1; omega) ?_⟩
  · have := le_max_left d₁ d₂
    rcases hjR' with rfl | rfl <;> simp only [t₀] <;> omega
  intro t ht ht'
  -- agent 2 waits at its ruling-set node during its bit `i`
  obtain ⟨u, hu⟩ : ∃ u, t = d₂ + (iterStart k + (4 * 2 ^ k + (2 ^ k + 32 * R + u))) :=
    ⟨t - (d₂ + (iterStart k + (4 * 2 ^ k + (2 ^ k + 32 * R)))), by
      rcases hjR' with rfl | rfl <;> simp only [t₀] at ht <;> omega⟩
  have hu1 : 64 * R * i < u := by
    rcases hjR' with rfl | rfl <;> simp only [t₀] at ht ht' <;> omega
  have hu2 : u < 64 * R * i + 64 * R := by
    rcases hjR' with rfl | rfl <;> simp only [t₀] at ht ht' <;> omega
  have e3 := P_search Rl hℓ (d := d₂) hp₂ (2 ^ k + 32 * R + u) (by omega)
  rw [sw_bit_unset hR hi hb₂ u hu1 hu2] at e3
  rw [hu, e3]
  push_cast; exact hr

omit hℓ in
/-- Two distinct colours `< 17` differ in one of their five bits. -/
lemma exists_testBit_ne {a b : ℕ} (ha : a < 17) (hb : b < 17) (hab : a ≠ b) :
    ∃ i < 5, a.testBit i ≠ b.testBit i := by
  by_contra h
  push Not at h
  apply hab
  apply Nat.eq_of_testBit_eq
  intro i
  rcases lt_or_ge i 5 with hi | hi
  · exact h i hi
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (by
      calc 17 ≤ 2 ^ 5 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (by
      calc 17 ≤ 2 ^ 5 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi))]

end Podc.RendezvousLabeledLine
