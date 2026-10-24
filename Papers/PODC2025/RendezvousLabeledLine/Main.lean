import Papers.PODC2025.RendezvousLabeledLine.InSync

/-!
# Lemmas 4.5–4.7 for the two agents and Theorem 1.1

Agent `α` starts at `vα` and wakes up in round `0`, agent `β` starts at `vβ` and wakes up in
round `τ`; `D = |vα - vβ|`, `L = 2^k`, `T_{α,L} = iterStart k`.
-/

namespace Podc.RendezvousLabeledLine

open Function

variable {κ : ℕ} (Rl : ColRuling κ) {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) (vα vβ : ℤ) (εα εβ : ℤˣ)
  (τ : ℕ)

lemma P_zero (v : ℤ) (ε : ℤˣ) : P Rl ℓ v ε 0 = X Rl ℓ v ε := by
  funext t; simp [P, delayed]

/-- `R*` of a plan, `0` for `⊥`. -/
def rOf : Option (ℕ × ℤ × ℕ) → ℕ
  | none => 0
  | some (R, _, _) => R

lemma abs_sub_eq_natAbs (a b : ℤ) : |a - b| = ((a - b).natAbs : ℤ) := (Int.natCast_natAbs _).symm

include hℓ

/-- Agent `α` has the larger ruling-set distance. -/
lemma lemma_4_5_α {k R : ℕ} {r : ℤ} {c : ℕ} (hτ : τ < 10 * (vα - vβ).natAbs)
    (hpα : pl Rl ℓ vα εα k = some (R, r, c)) (hD : (vα - vβ).natAbs ≤ R)
    (hpβ : pl Rl ℓ vβ εβ k = none ∨ ∃ R' r' c', pl Rl ℓ vβ εβ k = some (R', r', c') ∧ R' < R) :
    ∃ t ≤ iterStart k + 8 * 2 ^ k, MeetOrCross (X Rl ℓ vα εα) (delayed τ (X Rl ℓ vβ εβ)) t := by
  obtain ⟨hR, hL, -⟩ := plan_some_bounds Rl (inj_frame hℓ vα εα) hpα
  have h := lemma_4_5_gen Rl hℓ (d₁ := 0) (d₂ := τ) hpα hD hpβ (by omega) (by omega)
  rw [P_zero] at h
  obtain ⟨t, ht, h⟩ := h.meetOrCross
  exact ⟨t, by omega, h⟩

/-- Agent `β` has the larger ruling-set distance. -/
lemma lemma_4_5_β {k R : ℕ} {r : ℤ} {c : ℕ} (hτ : τ < 10 * (vα - vβ).natAbs)
    (hpβ : pl Rl ℓ vβ εβ k = some (R, r, c)) (hD : (vα - vβ).natAbs ≤ R)
    (hpα : pl Rl ℓ vα εα k = none ∨ ∃ R' r' c', pl Rl ℓ vα εα k = some (R', r', c') ∧ R' < R) :
    ∃ t ≤ iterStart k + 8 * 2 ^ k, MeetOrCross (X Rl ℓ vα εα) (delayed τ (X Rl ℓ vβ εβ)) t := by
  obtain ⟨hR, hL, -⟩ := plan_some_bounds Rl (inj_frame hℓ vβ εβ) hpβ
  have hD' : (vβ - vα).natAbs ≤ R := by rwa [← Int.natAbs_neg, neg_sub]
  have h := (lemma_4_5_gen Rl hℓ (d₁ := τ) (d₂ := 0) hpβ hD' hpα (by omega) (by omega)).symm
  rw [P_zero] at h
  obtain ⟨t, ht, h⟩ := h.meetOrCross
  exact ⟨t, by omega, h⟩

/-- **Lemma 4.5.** If the two agents computed different ruling-set distances in iteration `L`
(`⊥` counting as `0`) and the larger one is at least `D`, they meet or cross by round
`T_{α,L} + 8L` (assuming `τ < 10 D`, the other case being Lemma 4.3). The paper claims
`T_{α,L} + 7L`; see `differencies.md`. -/
theorem lemma_4_5 (hτ : τ < 10 * (vα - vβ).natAbs) (k : ℕ)
    (hne : rOf (pl Rl ℓ vα εα k) ≠ rOf (pl Rl ℓ vβ εβ k))
    (hmax : (vα - vβ).natAbs ≤ max (rOf (pl Rl ℓ vα εα k)) (rOf (pl Rl ℓ vβ εβ k))) :
    ∃ t ≤ iterStart k + 8 * 2 ^ k, MeetOrCross (X Rl ℓ vα εα) (delayed τ (X Rl ℓ vβ εβ)) t := by
  rcases hpα : pl Rl ℓ vα εα k with _ | ⟨Rα, rα, cα⟩ <;>
    rcases hpβ : pl Rl ℓ vβ εβ k with _ | ⟨Rβ, rβ, cβ⟩ <;>
    rw [hpα, hpβ] at hne hmax <;> simp only [rOf] at hne hmax
  · exact absurd rfl hne
  · exact lemma_4_5_β Rl hℓ vα vβ εα εβ τ hτ hpβ (by omega) (Or.inl hpα)
  · exact lemma_4_5_α Rl hℓ vα vβ εα εβ τ hτ hpα (by omega) (Or.inl hpβ)
  · rcases lt_or_gt_of_ne hne with h | h
    · exact lemma_4_5_β Rl hℓ vα vβ εα εβ τ hτ hpβ (by omega) (Or.inr ⟨_, _, _, hpα, h⟩)
    · exact lemma_4_5_α Rl hℓ vα vβ εα εβ τ hτ hpα (by omega) (Or.inr ⟨_, _, _, hpβ, h⟩)

/-- **Lemma 4.6.** Same ruling-set distance `R ≥ D` and same ruling-set node: the agents meet by
round `T_{α,L} + 5L`. -/
theorem lemma_4_6 (hτ : τ < 10 * (vα - vβ).natAbs) {k R : ℕ} {rα rβ : ℤ} {cα cβ : ℕ}
    (hpα : pl Rl ℓ vα εα k = some (R, rα, cα)) (hpβ : pl Rl ℓ vβ εβ k = some (R, rβ, cβ))
    (hD : (vα - vβ).natAbs ≤ R) (hr : frame vα εα rα = frame vβ εβ rβ) :
    ∃ t ≤ iterStart k + 5 * 2 ^ k, X Rl ℓ vα εα t = delayed τ (X Rl ℓ vβ εβ) t := by
  obtain ⟨t, ht, h⟩ := lemma_4_6_gen Rl hℓ (d₁ := 0) (d₂ := τ) hpα hpβ hr (by omega) (by omega)
  rw [P_zero] at h
  exact ⟨t, by simpa using ht, h⟩

omit hℓ in
/-- The ruling-set node chosen by an agent, in global coordinates, is a ruling-set node of the
labelled line, and the colour it uses is that node's colour. -/
lemma plan_global (hℓ : Injective ℓ) {v : ℤ} {ε : ℤˣ} {k R : ℕ} {r : ℤ} {c : ℕ}
    (hp : pl Rl ℓ v ε k = some (R, r, c)) :
    Rl.inS R ℓ (frame v ε r) ∧ c = Rl.col R ℓ (frame v ε r) ∧ |frame v ε r - v| ≤ 2 * (R : ℤ) - 1 := by
  obtain ⟨hg, -, hm, hc⟩ := plan_some Rl (inj_frame hℓ v ε) hp
  obtain ⟨-, -, hr⟩ := plan_some_bounds Rl (inj_frame hℓ v ε) hp
  obtain ⟨-, -, -, hS⟩ := hm.spec Rl (inj_frame hℓ v ε) hg.1.one_le
  refine ⟨(Rl.inS_frame R ℓ v ε r).1 hS, by rw [hc, Rl.col_frame], ?_⟩
  rwa [abs_frame_sub]

/-- **Lemma 4.7.** Same ruling-set distance `R ≥ D`, different ruling-set nodes: these are within
`5R - 2 ≤ 9R - 1`, hence have different colours, and the agents meet or cross while processing a
bit where the colours differ, by round `T_{α,L} + 28L`. -/
theorem lemma_4_7 (hτ : τ < 10 * (vα - vβ).natAbs) {k R : ℕ} {rα rβ : ℤ} {cα cβ : ℕ}
    (hpα : pl Rl ℓ vα εα k = some (R, rα, cα)) (hpβ : pl Rl ℓ vβ εβ k = some (R, rβ, cβ))
    (hD : (vα - vβ).natAbs ≤ R) (hr : frame vα εα rα ≠ frame vβ εβ rβ) :
    ∃ t ≤ iterStart k + 28 * 2 ^ k,
      MeetOrCross (X Rl ℓ vα εα) (delayed τ (X Rl ℓ vβ εβ)) t := by
  obtain ⟨hR, hL, -⟩ := plan_some_bounds Rl (inj_frame hℓ vα εα) hpα
  obtain ⟨hSα, hcα, hrα⟩ := plan_global Rl hℓ hpα
  obtain ⟨hSβ, hcβ, hrβ⟩ := plan_global Rl hℓ hpβ
  have hDz : |vα - vβ| ≤ (R : ℤ) := by rw [abs_sub_eq_natAbs]; exact_mod_cast hD
  have hdist : |frame vβ εβ rβ - frame vα εα rα| ≤ 5 * (R : ℤ) - 2 := by
    calc |frame vβ εβ rβ - frame vα εα rα|
        = |(frame vβ εβ rβ - vβ) - (frame vα εα rα - vα) - (vα - vβ)| := by ring_nf
      _ ≤ |(frame vβ εβ rβ - vβ) - (frame vα εα rα - vα)| + |vα - vβ| := abs_sub _ _
      _ ≤ |frame vβ εβ rβ - vβ| + |frame vα εα rα - vα| + |vα - vβ| := by
          gcongr; exact abs_sub _ _
      _ ≤ 5 * (R : ℤ) - 2 := by omega
  have hcol : cα ≠ cβ := by
    rw [hcα, hcβ]
    exact Rl.proper R hR ℓ hℓ _ _ hSα hSβ hr (by rw [abs_sub_comm]; omega)
  obtain ⟨i, hi, hbit⟩ := exists_testBit_ne (hcα ▸ Rl.col_lt _ _ _) (hcβ ▸ Rl.col_lt _ _ _) hcol
  have hi' : 64 * R * i ≤ 64 * R * 4 := Nat.mul_le_mul_left _ (by omega)
  have hτR : τ < 10 * R := by omega
  cases hb : cα.testBit i
  · -- `β` has bit `i` set, `α` waits
    have hb' : cβ.testBit i = true := by rw [hb] at hbit; simpa using hbit.symm
    obtain ⟨W, W', hW', h⟩ := lemma_4_7_gen Rl hℓ (d₁ := τ) (d₂ := 0) hpβ hpα hi hb' hb
      (by rw [abs_sub_comm]; omega) (by omega) (by omega)
    rw [P_zero] at h
    obtain ⟨t, ht, h'⟩ := h.symm.meetOrCross
    refine ⟨t, ?_, h'⟩
    simp only [max_eq_left (Nat.zero_le τ)] at hW'
    omega
  · have hb' : cβ.testBit i = false := by rw [hb] at hbit; simpa using hbit.symm
    obtain ⟨W, W', hW', h⟩ := lemma_4_7_gen Rl hℓ (d₁ := 0) (d₂ := τ) hpα hpβ hi hb hb'
      (by omega) (by omega) (by omega)
    rw [P_zero] at h
    obtain ⟨t, ht, h'⟩ := h.meetOrCross
    refine ⟨t, ?_, h'⟩
    simp only [max_eq_right (Nat.zero_le τ)] at hW'
    omega

/-- The constant of Theorem 1.1 (model with edge-crossing detection). -/
def C₁ (κ : ℕ) : ℕ := 896 * κ + 14336

/-- **Theorem 1.1** (model where simultaneous edge crossings count as rendezvous). With any
early-stopping coloured ruling-set rule of commitment time `κ R log* ℓ(u)` (Lemma 3.5),
Algorithm 5 achieves rendezvous within `C₁ κ · D · log* ℓ(u₀)` rounds of the first wake-up, for
every node `u₀` within distance `D` of one of the two starting nodes (in particular for the one of
smallest label, `ℓ_min`), every wake-up delay `τ` and all port orientations. -/
theorem thm_1_1_cross (u₀ : ℤ)
    (hu₀ : |u₀ - vα| ≤ (vα - vβ).natAbs ∨ |u₀ - vβ| ≤ (vα - vβ).natAbs) :
    ∃ t ≤ C₁ κ * (vα - vβ).natAbs * lstar (ℓ u₀),
      MeetOrCross (X Rl ℓ vα εα) (delayed τ (X Rl ℓ vβ εβ)) t := by
  set D := (vα - vβ).natAbs with hDdef
  have hls := one_le_lstar (ℓ u₀)
  have hDl : D ≤ D * lstar (ℓ u₀) := Nat.le_mul_of_pos_right D hls
  -- `D = 0`: the agents start at the same node
  rcases Nat.eq_zero_or_pos D with hD0 | hD1
  · refine ⟨0, Nat.zero_le _, Or.inl ?_⟩
    have : vα = vβ := by have := Int.natAbs_eq_zero.1 hD0; omega
    simp [delayed, Algo.traj_zero, this]
  have hvne : vα ≠ vβ := by intro h; simp [D, h] at hD1
  have hDz : |vα - vβ| = (D : ℤ) := abs_sub_eq_natAbs _ _
  -- out of sync (Lemma 4.3)
  rcases lemma_4_3 Rl hℓ vα vβ εα εβ τ hvne with ⟨hτ1, hτ2⟩ | hmeet
  swap
  · obtain ⟨t, ht, h⟩ := hmeet.meetOrCross
    have hb : iterStart (Nat.clog 2 D + 1) + 3 * 2 ^ (Nat.clog 2 D + 1) ≤
        C₁ κ * D * lstar (ℓ u₀) := by
      have hk2 : 2 ^ Nat.clog 2 D < 2 * D := Nat.pow_clog_lt_mul (by norm_num) (by omega)
      simp only [iterStart, pow_succ]
      have : C₁ κ * D * lstar (ℓ u₀) = 896 * κ * (D * lstar (ℓ u₀)) +
          14336 * (D * lstar (ℓ u₀)) := by simp only [C₁]; ring
      omega
    exact ⟨t, le_trans ht hb, h⟩
  have hτ : τ < 10 * D := by omega
  -- in sync: the iteration `L ≥ 8 κ D log* ℓ(u₀) + 128 D`
  set N := 8 * κ * D * lstar (ℓ u₀) + 128 * D with hN
  set k := Nat.clog 2 N
  have hk1 : N ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) N
  have hk2 : 2 ^ k < 2 * N := Nat.pow_clog_lt_mul (by norm_num) (by omega)
  have hα0 : |u₀ - vα| ≤ 2 * (D : ℤ) := by
    rcases hu₀ with h | h
    · omega
    · calc |u₀ - vα| = |(u₀ - vβ) - (vα - vβ)| := by ring_nf
        _ ≤ |u₀ - vβ| + |vα - vβ| := abs_sub _ _
        _ ≤ 2 * (D : ℤ) := by omega
  have hβ0 : |u₀ - vβ| ≤ 2 * (D : ℤ) := by
    rcases hu₀ with h | h
    · calc |u₀ - vβ| = |(u₀ - vα) + (vα - vβ)| := by ring_nf
        _ ≤ |u₀ - vα| + |vα - vβ| := abs_add_le _ _
        _ ≤ 2 * (D : ℤ) := by omega
    · omega
  obtain ⟨Rα, rα, cα, hpα, hRα⟩ := lemma_4_4 Rl hℓ vα εα k D hD1 u₀ hα0 hk1
  obtain ⟨Rβ, rβ, cβ, hpβ, hRβ⟩ := lemma_4_4 Rl hℓ vβ εβ k D hD1 u₀ hβ0 hk1
  -- the bound: `T_{α,L} + 28 L ≤ 56 L ≤ 112 N ≤ C₁ κ D log* ℓ(u₀)`
  have hfin : iterStart k + 28 * 2 ^ k ≤ C₁ κ * D * lstar (ℓ u₀) := by
    have : C₁ κ * D * lstar (ℓ u₀) = 112 * (8 * κ * D * lstar (ℓ u₀)) +
        14336 * (D * lstar (ℓ u₀)) := by simp only [C₁]; ring
    simp only [iterStart]; omega
  suffices h : ∃ t ≤ iterStart k + 28 * 2 ^ k,
      MeetOrCross (X Rl ℓ vα εα) (delayed τ (X Rl ℓ vβ εβ)) t by
    obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht.trans hfin, h⟩
  by_cases hR : Rα = Rβ
  · subst hR
    by_cases hr : frame vα εα rα = frame vβ εβ rβ
    · obtain ⟨t, ht, h⟩ := lemma_4_6 Rl hℓ vα vβ εα εβ τ hτ hpα hpβ (by omega) hr
      exact ⟨t, by omega, Or.inl h⟩
    · exact lemma_4_7 Rl hℓ vα vβ εα εβ τ hτ hpα hpβ (by omega) hr
  · obtain ⟨t, ht, h⟩ := lemma_4_5 Rl hℓ vα vβ εα εβ τ hτ k
      (by rw [hpα, hpβ]; exact hR) (by rw [hpα, hpβ]; simp only [rOf]; omega)
    exact ⟨t, by omega, h⟩

/-- **Theorem 1.1.** The algorithm `care(Algorithm 5)` achieves rendezvous **at a node** within
`4 C₁ κ · D · log* ℓ(u₀)` rounds after the first wake-up, for every node `u₀` within distance `D` of
one of the starting nodes, every delay `τ`, every labelling and every port orientation. -/
theorem thm_1_1 (u₀ : ℤ)
    (hu₀ : |u₀ - vα| ≤ (vα - vβ).natAbs ∨ |u₀ - vβ| ≤ (vα - vβ).natAbs) :
    ∃ t ≤ 4 * (C₁ κ * (vα - vβ).natAbs * lstar (ℓ u₀)),
      (algFinal Rl).traj ℓ vα εα t = delayed τ ((algFinal Rl).traj ℓ vβ εβ) t :=
  thm_3_1 (alg5 Rl) hℓ vα vβ εα εβ _
    (fun τ' => thm_1_1_cross Rl hℓ vα vβ εα εβ τ' u₀ hu₀) τ

end Podc.RendezvousLabeledLine
