import Papers.PODC2025.RendezvousLabeledLine.Algorithm
import Cslib.Foundations.Data.Nat.Log

/-!
# Analysis of Algorithm 5 (Section 4.2–4.5)

Agent `α` starts at `vα` (frame orientation `εα`) and wakes up in round `0`; agent `β` starts at
`vβ` (orientation `εβ`) and wakes up in round `τ`. `x t` and `y t` are their global positions
(`y t = Xβ (t - τ)`), `D = |vα - vβ|`. Iteration `k` of agent `α` starts in round
`T_{α,L} = iterStart k = 28 (L - 1)` (`L = 2^k`), that of `β` in round `T_{α,L} + τ`
(Proposition 4.1). Rendezvous counts simultaneous edge crossings (`MeetOrCross`); Theorem 3.1
(`thm_3_1`) removes this assumption at the price of a factor `4` (`thm_1_1`).
-/

namespace Podc.RendezvousLabeledLine

open Function

variable {κ : ℕ} (Rl : ColRuling κ)

/-! ### One agent, in its own frame -/

section Frame

variable {μ : ℤ → ℕ}

lemma pos5_disc (μ : ℤ → ℕ) (k s : ℕ) (hs : s < 4 * 2 ^ k) :
    pos5 Rl μ (iterStart k + s) = zw (2 ^ k) s := by
  rw [pos5_iter Rl μ k s (by omega), phasePos_lt _ _ hs]

lemma pos5_none {k : ℕ} (hp : plan Rl μ (2 ^ k) = none) (s : ℕ) (hs : 4 * 2 ^ k ≤ s)
    (hs' : s < 28 * 2 ^ k) : pos5 Rl μ (iterStart k + s) = 0 := by
  rw [pos5_iter Rl μ k s hs', hp, phasePos_none _ _ hs]

lemma pos5_some {k R : ℕ} {r : ℤ} {c : ℕ} (hp : plan Rl μ (2 ^ k) = some (R, r, c)) (s : ℕ)
    (hs : 4 * 2 ^ k ≤ s) (hs' : s < 28 * 2 ^ k) :
    pos5 Rl μ (iterStart k + s) = sw (2 ^ k) R r c (s - 4 * 2 ^ k) := by
  rw [pos5_iter Rl μ k s hs', hp, phasePos_some _ _ _ _ _ hs]

/-- During iteration `k` the agent stays within `2^k` of its start. -/
lemma abs_pos5_le_iter (hμ : Injective μ) (k s : ℕ) (hs : s < 28 * 2 ^ k) :
    |pos5 Rl μ (iterStart k + s)| ≤ 2 ^ k := by
  by_cases h4 : s < 4 * 2 ^ k
  · rw [pos5_disc Rl μ k s h4]; push_cast; exact abs_zw_le _ _ h4.le
  rcases hp : plan Rl μ (2 ^ k) with _ | ⟨R, r, c⟩
  · rw [pos5_none Rl hp s (by omega) hs]; simp
  · obtain ⟨hR, hL, hr⟩ := plan_some_bounds Rl hμ hp
    rw [pos5_some Rl hp s (by omega) hs]
    have := abs_sw_le (2 ^ k) R r c (s - 4 * 2 ^ k) hR
    have hL' : (16 * R : ℤ) ≤ 2 ^ k := by exact_mod_cast hL
    omega

/-- Before iteration `k` the agent stays within `2^(k-1)` of its start (first part of
Proposition 4.2). -/
lemma two_mul_abs_pos5_le_of_lt (hμ : Injective μ) (k t : ℕ) (ht : t < iterStart k) :
    2 * |pos5 Rl μ t| ≤ 2 ^ k := by
  obtain ⟨h1, h2⟩ := iterOf_spec t
  generalize iterOf t = k' at h1 h2
  have hk : k' < k := by
    by_contra hk
    have : iterStart k ≤ iterStart k' := by
      simp only [iterStart]; have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.1 hk)
      have := Nat.one_le_two_pow (n := k); omega
    omega
  rw [iterStart_succ] at h2
  obtain ⟨s, rfl⟩ : ∃ s, t = iterStart k' + s := ⟨t - iterStart k', by omega⟩
  have := abs_pos5_le_iter Rl hμ k' s (by omega)
  have : (2 : ℤ) * 2 ^ k' ≤ 2 ^ k := by
    have := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by norm_num) (show k' + 1 ≤ k by omega)
    rw [pow_succ] at this; linarith
  linarith

/-- In the searching phase with plan `some (R, r, c)` the agent stays within `10 R - 1` of its
start. -/
lemma abs_pos5_some_le (hμ : Injective μ) {k R : ℕ} {r : ℤ} {c : ℕ}
    (hp : plan Rl μ (2 ^ k) = some (R, r, c)) (s : ℕ) (hs : 4 * 2 ^ k ≤ s)
    (hs' : s < 28 * 2 ^ k) : |pos5 Rl μ (iterStart k + s)| ≤ 10 * (R : ℤ) - 1 := by
  obtain ⟨hR, hL, hr⟩ := plan_some_bounds Rl hμ hp
  rw [pos5_some Rl hp s hs hs']
  have := abs_sw_le (2 ^ k) R r c (s - 4 * 2 ^ k) hR
  omega

end Frame

/-! ### Global trajectories -/

/-- Global trajectory of an agent running Algorithm 5. -/
noncomputable abbrev X (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) : ℕ → ℤ := (alg5 Rl).traj ℓ v ε

lemma X_apply (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (t : ℕ) :
    X Rl ℓ v ε t = frame v ε (pos5 Rl (ℓ ∘ frame v ε) t) := rfl

lemma abs_X_sub (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (t : ℕ) :
    |X Rl ℓ v ε t - v| = |pos5 Rl (ℓ ∘ frame v ε) t| := by
  rw [X_apply, abs_frame_sub]

/-- **Proposition 4.1.** Iteration `k` (parameter `L = 2^k`) lasts `28 L` rounds and both the
discovery and the searching phase have fixed lengths: it starts in round `28 (L - 1)` of the
agent's clock, at the start node. -/
theorem prop_4_1 (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (k : ℕ) :
    iterStart k = 28 * (2 ^ k - 1) ∧ iterStart (k + 1) = iterStart k + 28 * 2 ^ k ∧
      X Rl ℓ v ε (iterStart k) = v := by
  refine ⟨rfl, iterStart_succ k, ?_⟩
  rw [X_apply, show iterStart k = iterStart k + 0 from rfl, pos5_disc Rl _ k 0 (by positivity),
    zw_zero]
  simp [frame]

/-- **Proposition 4.2 (1).** Up to round `T_{α,L} + L/2`, the agent is within `L/2` of its start. -/
theorem prop_4_2_1 {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) (v : ℤ) (ε : ℤˣ) (k t : ℕ)
    (ht : 2 * t ≤ 2 * iterStart k + 2 ^ k) : 2 * |X Rl ℓ v ε t - v| ≤ 2 ^ k := by
  rw [abs_X_sub]
  have hμ : Injective (ℓ ∘ frame v ε) := hℓ.comp (frame_injective v ε)
  by_cases h : t < iterStart k
  · exact two_mul_abs_pos5_le_of_lt Rl hμ k t h
  obtain ⟨s, rfl⟩ : ∃ s, t = iterStart k + s := ⟨t - iterStart k, by omega⟩
  have hs : 2 * s ≤ 2 ^ k := by omega
  have := Nat.one_le_two_pow (n := k)
  rw [pos5_disc Rl _ k s (by omega), zw_small _ _ (by omega)]
  simp only [Nat.abs_cast]; exact_mod_cast hs

/-- **Proposition 4.2 (2)** (endpoint form): the discovery `ZWalk(L)` is at the two ends
`v ± L` of `[v - L, v + L]` in rounds `T_{α,L} + L` and `T_{α,L} + 3L`. -/
theorem prop_4_2_2 (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (k : ℕ) :
    X Rl ℓ v ε (iterStart k + 2 ^ k) = frame v ε (2 ^ k) ∧
      X Rl ℓ v ε (iterStart k + 3 * 2 ^ k) = frame v ε (-2 ^ k) := by
  rw [X_apply, X_apply, pos5_disc Rl _ k _ (by have := Nat.one_le_two_pow (n := k); omega),
    pos5_disc Rl _ k _ (by have := Nat.one_le_two_pow (n := k); omega), zw_L, zw_three]
  push_cast; simp

/-- **Proposition 4.2 (2)** (as stated): every node of `[v - L, v + L]` is visited in rounds
`[T_{α,L}, T_{α,L} + 3L]`. -/
theorem prop_4_2_2' (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (k : ℕ) (z : ℤ) (hz : |z - v| ≤ 2 ^ k) :
    ∃ t, iterStart k ≤ t ∧ t ≤ iterStart k + 3 * 2 ^ k ∧ X Rl ℓ v ε t = z := by
  have hz' : |(ε : ℤ) * (z - v)| ≤ ((2 ^ k : ℕ) : ℤ) := by
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using hz
    · simpa [abs_sub_comm] using hz
  obtain ⟨s, hs, e⟩ := zw_surj (2 ^ k) _ hz'
  refine ⟨iterStart k + s, by omega, by omega, ?_⟩
  rw [X_apply, pos5_disc Rl _ k s (by have := Nat.one_le_two_pow (n := k); omega), e]
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [frame]

/-- A sweep: `x` is at `c + ε ρ` and at `c - ε ρ` inside a window in which `y` stays within `ρ`
of `c`; then the agents meet or cross in the window (Proposition 3.2 (2)). -/
lemma sweep {x y : ℕ → ℤ} (hx : Lip x) (hly : Lip y) {c : ℤ} {ε : ℤˣ} {ρ : ℤ} {W W' t₁ t₂ : ℕ}
    (h1 : W ≤ t₁) (h1' : t₁ ≤ W') (h2 : W ≤ t₂) (h2' : t₂ ≤ W') (hx1 : x t₁ = frame c ε ρ)
    (hx2 : x t₂ = frame c ε (-ρ)) (hy : ∀ t, W ≤ t → t ≤ W' → |y t - c| ≤ ρ) :
    MeetOrCrossIn x y W W' := by
  have hy' : ∀ t, W ≤ t → t ≤ W' → c - ρ ≤ y t ∧ y t ≤ c + ρ := fun t h h' => by
    have := abs_le.1 (hy t h h'); constructor <;> linarith
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp only [frame, Units.val_one, one_mul] at hx1 hx2
    exact prop_3_2_scan' hx hly h2 h2' h1 h1' hx2 (by rw [hx1]) hy'
  · simp only [frame, Units.val_neg, Units.val_one, neg_mul, one_mul, neg_neg] at hx1 hx2
    exact prop_3_2_scan' hx hly h1 h1' h2 h2' (by rw [hx1]; ring) hx2 hy'

/-! ### The setting of Section 4 -/

section Setting

variable {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) (vα vβ : ℤ) (εα εβ : ℤˣ) (τ : ℕ)

/-- Position of agent `α` (woken up first, in round `0`). -/
noncomputable abbrev xα : ℕ → ℤ := X Rl ℓ vα εα
/-- Position of agent `β` (woken up in round `τ`). -/
noncomputable abbrev yβ : ℕ → ℤ := delayed τ (X Rl ℓ vβ εβ)

include hℓ

lemma lip_xα : Lip (xα Rl vα εα (ℓ := ℓ)) := (alg5 Rl).lip_traj hℓ vα εα
lemma lip_yβ : Lip (yβ Rl vβ εβ τ (ℓ := ℓ)) := Algo.lip_delayed ((alg5 Rl).lip_traj hℓ vβ εβ) τ

/-- **Lemma 4.3.** Let `L = 2^(⌈log D⌉ + 1)`. Either `τ < 5L/2 ≤ 10 D`, or the agents meet (or
cross) by round `T_{α,L} + 3L = O(D)`. -/
theorem lemma_4_3 (hD : vα ≠ vβ) :
    let D := (vα - vβ).natAbs
    let k := Nat.clog 2 D + 1
    (2 * τ < 5 * 2 ^ k ∧ 5 * 2 ^ k ≤ 20 * D) ∨
      MeetOrCrossIn (xα Rl vα εα (ℓ := ℓ)) (yβ Rl vβ εβ τ (ℓ := ℓ)) 0 (iterStart k + 3 * 2 ^ k) := by
  intro D k
  have hD1 : 1 ≤ D := by have := Int.natAbs_pos.2 (sub_ne_zero.2 hD); omega
  have hk1 : D ≤ 2 ^ Nat.clog 2 D := Nat.le_pow_clog (by norm_num) D
  have hk2 : 2 ^ Nat.clog 2 D < 2 * D := Nat.pow_clog_lt_mul (by norm_num) (by omega)
  have hL : 2 ^ k = 2 * 2 ^ Nat.clog 2 D := by simp only [k, pow_succ]; ring
  by_cases hτ : 2 * τ < 5 * 2 ^ k
  · left; exact ⟨hτ, by omega⟩
  right
  have hLD : (2 * D : ℤ) ≤ 2 ^ k := by
    have : 2 * D ≤ 2 ^ k := by omega
    exact_mod_cast this
  obtain ⟨hx1, hx2⟩ := prop_4_2_2 Rl ℓ vα εα k
  refine (sweep (lip_xα Rl hℓ vα εα) (lip_yβ Rl hℓ vβ εβ τ) (ρ := (2 : ℤ) ^ k)
    (W := iterStart k + 2 ^ k)
    (W' := iterStart k + 3 * 2 ^ k) (t₁ := iterStart k + 2 ^ k) (t₂ := iterStart k + 3 * 2 ^ k)
    le_rfl (by omega) (by omega) le_rfl hx1 hx2 ?_).mono (by omega) le_rfl
  intro t ht ht'
  -- `β` is still within `L/2` of `vβ`
  have hβ := prop_4_2_1 Rl hℓ vβ εβ k (t - τ) (by omega)
  push_cast at hβ
  have hDv : |vβ - vα| = (D : ℤ) := by
    rw [abs_sub_comm]; simp [D, Int.natCast_natAbs]
  simp only [yβ, delayed]
  calc |X Rl ℓ vβ εβ (t - τ) - vα| = |(X Rl ℓ vβ εβ (t - τ) - vβ) + (vβ - vα)| := by ring_nf
    _ ≤ |X Rl ℓ vβ εβ (t - τ) - vβ| + |vβ - vα| := abs_add_le _ _
    _ ≤ (2 : ℤ) ^ k := by rw [hDv]; omega

end Setting

end Podc.RendezvousLabeledLine
