import Papers.PODC2013.RotorRouterRing.LowerBound

/-!
# Theorem 3.7: assembling the multi-scale argument

See `LowerBound.lean` for the overview. Main result: `theorem_3_7`.
-/

open Finset

namespace Podc.RotorRouterRing

open RotorGraph

set_option linter.unusedSectionVars false

/-! ### Generic facts about runs -/

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V] (G : RotorGraph V)

/-- Agents are neither created nor destroyed. -/
lemma sum_pos_step (c : Config V) (d : V → ℕ) : ∑ u, (G.step c d).pos u = ∑ u, c.pos u := by
  simp only [step, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [G.sum_sent]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _; omega

lemma sum_pos_run (c₀ : Config V) (D : ℕ → V → ℕ) (t : ℕ) :
    ∑ u, (G.run c₀ D t).pos u = ∑ u, c₀.pos u := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [run]; rw [sum_pos_step, ih]

/-- A node with a positive visit count has been occupied at some time. -/
lemma exists_pos_of_visits (c₀ : Config V) (D : ℕ → V → ℕ) (t : ℕ) (u : V)
    (h : 0 < G.visits c₀ D t u) : ∃ s ≤ t, 0 < (G.run c₀ D s).pos u := by
  induction t with
  | zero => exact ⟨0, le_rfl, by simpa [visits, run] using h⟩
  | succ t ih =>
    by_cases h' : 0 < G.visits c₀ D t u
    · obtain ⟨s, hs, hpos⟩ := ih h'
      exact ⟨s, by omega, hpos⟩
    · refine ⟨t + 1, le_rfl, ?_⟩
      have hv : G.visits c₀ D (t + 1) u = G.visits c₀ D t u +
          ∑ w, G.sent w ((G.run c₀ D t).ptr w) (G.moved c₀ D t w) u := by
        simp only [visits, Finset.sum_range_succ]; ring
      simp only [run, step]
      simp only [moved] at hv
      omega

end Generic

/-! ### The multi-scale recursion (pure arithmetic) -/

lemma four_pow_eq (m : ℕ) : (2 ^ m) ^ 2 = 4 ^ m := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- Downward induction over the scales `R_m = 2^m R₀`. -/
lemma multiscale (S N0 : ℕ → ℕ) (R0 T k M : ℕ)
    (hstep : ∀ m < M, (2 ^ m * R0) ^ 2 * S m ≤ 2 * (2 ^ m * R0) ^ 2 * T * N0 (m + 1) + T * S (m + 1))
    (htop : S M ≤ k * T) (hN : ∀ m < M, N0 (m + 1) ≤ 4 ^ (m + 1)) (hk : k ≤ 16 * 4 ^ M)
    (hT : 32 * T < R0 ^ 2) : ∀ m ≤ M, S m ≤ 16 * 4 ^ m * T := by
  have hR0 : 0 < R0 := by
    rcases Nat.eq_zero_or_pos R0 with h | h
    · subst h; simp at hT
    · exact h
  suffices H : ∀ j ≤ M, S (M - j) ≤ 16 * 4 ^ (M - j) * T by
    intro m hm
    have := H (M - m) (by omega)
    rwa [show M - (M - m) = m by omega] at this
  intro j
  induction j with
  | zero => intro _; simpa using htop.trans (Nat.mul_le_mul_right T hk)
  | succ j ih =>
    intro hj
    set m := M - (j + 1) with hm
    have hm1 : M - j = m + 1 := by omega
    have ih' := ih (by omega)
    rw [hm1] at ih'
    have hs := hstep m (by omega)
    have hN' := hN m (by omega)
    set Q := (2 ^ m * R0) ^ 2 with hQ
    have hQ' : Q = 4 ^ m * R0 ^ 2 := by rw [hQ, mul_pow, four_pow_eq]
    have hQpos : 0 < Q := by rw [hQ']; positivity
    have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by ring
    -- `T * S (m+1) ≤ 2 Q T`
    have h1 : T * S (m + 1) ≤ 2 * Q * T := by
      calc T * S (m + 1) ≤ T * (16 * 4 ^ (m + 1) * T) := Nat.mul_le_mul_left T ih'
        _ = 4 ^ m * (64 * T * T) := by rw [h4]; ring
        _ ≤ 4 ^ m * (2 * R0 ^ 2 * T) := by
            apply Nat.mul_le_mul_left; nlinarith
        _ = 2 * Q * T := by rw [hQ']; ring
    have h2 : 2 * Q * T * N0 (m + 1) ≤ 2 * Q * T * (4 * 4 ^ m) := by
      rw [← h4]; exact Nat.mul_le_mul_left _ hN'
    have h3 : Q * S m ≤ Q * (16 * 4 ^ m * T) := by
      calc Q * S m ≤ 2 * Q * T * N0 (m + 1) + T * S (m + 1) := hs
        _ ≤ 2 * Q * T * (4 * 4 ^ m) + 2 * Q * T := add_le_add h2 h1
        _ ≤ Q * (16 * 4 ^ m * T) := by
            have : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
            have h5 := Nat.mul_le_mul_left (Q * T) (show 2 ≤ 8 * 4 ^ m by omega)
            have e1 : Q * (16 * 4 ^ m * T) = Q * T * (8 * 4 ^ m) + Q * T * (8 * 4 ^ m) := by ring
            have e2 : 2 * Q * T * (4 * 4 ^ m) = Q * T * (8 * 4 ^ m) := by ring
            have e3 : 2 * Q * T = Q * T * 2 := by ring
            omega
    exact Nat.le_of_mul_le_mul_left h3 hQpos

/-- If `2^m a_m ≤ B` for `m = 1, …, M`, then `Σ_{m=1}^M a_m ≤ B`. -/
lemma sum_geom_le (a : ℕ → ℕ) (B M : ℕ) (h : ∀ m ∈ Icc 1 M, 2 ^ m * a m ≤ B) :
    ∑ m ∈ Icc 1 M, a m ≤ B := by
  suffices H : 2 ^ M * ∑ m ∈ Icc 1 M, a m + B ≤ 2 ^ M * B by
    have : 1 ≤ 2 ^ M := Nat.one_le_two_pow
    nlinarith
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := ih (fun m hm => h m (by simp at hm ⊢; omega))
    have h2 := h (M + 1) (by simp)
    rw [pow_succ] at h2 ⊢
    nlinarith

/-! ### Choosing the centre `v` -/

variable {n : ℕ} [NeZero n]

/-- Number of agents initially within distance `r` of `v`. -/
def initCount (pos₀ : ZMod n → ℕ) (v : ZMod n) (r : ℕ) : ℕ :=
  ∑ x, if ringDist v x ≤ r then pos₀ x else 0

lemma nearCount_zero_eq (pos₀ : ZMod n → ℕ) (v : ZMod n) (r : ℕ) :
    nearCount pos₀ v r 0 = initCount pos₀ v r := rfl

lemma sum_initCount_le (pos₀ : ZMod n → ℕ) (r : ℕ) :
    ∑ v, initCount pos₀ v r ≤ (∑ x, pos₀ x) * (2 * r + 1) := by
  simp only [initCount]
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_le_sum; intro x _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  exact Nat.mul_le_mul_left _ (card_ball_le x r)

lemma card_filter_le_sum {α : Type*} [Fintype α] (f : α → ℕ) (c : ℕ) :
    (univ.filter (fun v => c < f v)).card * (c + 1) ≤ ∑ v, f v := by
  calc (univ.filter (fun v => c < f v)).card * (c + 1)
      = ∑ v ∈ univ.filter (fun v => c < f v), (c + 1) := by simp
    _ ≤ ∑ v ∈ univ.filter (fun v => c < f v), f v := Finset.sum_le_sum (fun v hv => by
        simp only [Finset.mem_filter] at hv; omega)
    _ ≤ ∑ v, f v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

/-- There is a centre `v` with no agent within distance `R₀` and at most `4^m` agents within
distance `2^m R₀` for `m = 1, …, M`. -/
lemma exists_good_center (pos₀ : ZMod n → ℕ) (k R0 M : ℕ) (hsum : ∑ x, pos₀ x = k)
    (hcount : 2 * k * (2 * R0 + 1) < n) :
    ∃ v : ZMod n, initCount pos₀ v R0 = 0 ∧
      ∀ m ∈ Icc 1 M, initCount pos₀ v (2 ^ m * R0) ≤ 4 ^ m := by
  set B0 := univ.filter (fun v : ZMod n => 0 < initCount pos₀ v R0)
  set Bm := fun m => univ.filter (fun v : ZMod n => 4 ^ m < initCount pos₀ v (2 ^ m * R0))
  have hB0 : B0.card ≤ k * (2 * R0 + 1) := by
    have h1 : B0.card * (0 + 1) ≤ ∑ v, initCount pos₀ v R0 :=
      card_filter_le_sum (fun v => initCount pos₀ v R0) 0
    have h2 := sum_initCount_le pos₀ R0
    rw [hsum] at h2; omega
  have hBm : ∀ m ∈ Icc 1 M, 2 ^ m * (Bm m).card ≤ k * (2 * R0 + 1) := by
    intro m _
    have h1 := card_filter_le_sum (fun v => initCount pos₀ v (2 ^ m * R0)) (4 ^ m)
    have h2 := sum_initCount_le pos₀ (2 ^ m * R0)
    rw [hsum] at h2
    have h3 : (Bm m).card * 4 ^ m ≤ k * (2 * (2 ^ m * R0) + 1) := by
      simp only [Bm]; nlinarith
    have h4 : k * (2 * (2 ^ m * R0) + 1) ≤ 2 ^ m * (k * (2 * R0 + 1)) := by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      nlinarith
    have h5 : 2 ^ m * (2 ^ m * (Bm m).card) ≤ 2 ^ m * (k * (2 * R0 + 1)) := by
      rw [← four_pow_eq] at h3
      calc 2 ^ m * (2 ^ m * (Bm m).card) = (Bm m).card * (2 ^ m) ^ 2 := by ring
        _ ≤ _ := h3.trans h4
    exact Nat.le_of_mul_le_mul_left h5 (by positivity)
  have hsumB := sum_geom_le (fun m => (Bm m).card) _ M hBm
  have hcard : (B0 ∪ (Icc 1 M).biUnion Bm).card < Fintype.card (ZMod n) := by
    rw [ZMod.card]
    calc (B0 ∪ (Icc 1 M).biUnion Bm).card ≤ B0.card + ((Icc 1 M).biUnion Bm).card :=
          Finset.card_union_le _ _
      _ ≤ B0.card + ∑ m ∈ Icc 1 M, (Bm m).card := by
          gcongr; exact Finset.card_biUnion_le
      _ < n := by nlinarith
  obtain ⟨v, hv⟩ : ∃ v, v ∉ B0 ∪ (Icc 1 M).biUnion Bm := by
    by_contra hcon
    push Not at hcon
    have : B0 ∪ (Icc 1 M).biUnion Bm = univ := Finset.eq_univ_iff_forall.mpr hcon
    rw [this, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  simp only [Finset.mem_union, Finset.mem_biUnion, not_or, not_exists, not_and] at hv
  refine ⟨v, ?_, fun m hm => ?_⟩
  · have := hv.1; simp only [B0, Finset.mem_filter, Finset.mem_univ, true_and] at this; omega
  · have := hv.2 m hm; simp only [Bm, Finset.mem_filter, Finset.mem_univ, true_and] at this; omega

/-! ### The theorem -/

/-- **Theorem 3.7** (with explicit constants and the weaker hypothesis `n ≥ 8k` instead of
`n ≥ 440k²`). For every placement of `k ≥ 1` agents on the `n`-node ring there is a node `v` such
that, with all initial pointers pointing away from `v`, the ring is not covered before time
`n² / (8192 k²)`: every `T` at which all nodes have been visited satisfies `n² < 8192 k² T`.
In particular the cover time is `Ω((n/k)²)`. -/
theorem theorem_3_7 (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (hn : 8 * k ≤ n) (pos₀ : ZMod n → ℕ)
    (hsum : ∑ u, pos₀ u = k) :
    ∃ v : ZMod n, ∀ T, (ring n).Covered ⟨pos₀, awayPtr v⟩ undelayed T →
      n ^ 2 < 8192 * k ^ 2 * T := by
  set R0 := n / (8 * k) with hR0def
  set M := Nat.log 4 k
  have hR0 : 1 ≤ R0 := by
    rw [hR0def, Nat.le_div_iff_mul_le (by omega)]; omega
  have h8 : 8 * k * R0 ≤ n := by rw [hR0def]; exact Nat.mul_div_le n (8 * k)
  have h8' : n < 8 * k * (R0 + 1) := by
    rw [hR0def]
    have := Nat.lt_mul_div_succ n (show 0 < 8 * k by omega)
    linarith
  have hcount : 2 * k * (2 * R0 + 1) < n := by nlinarith
  obtain ⟨v, hv0, hvm⟩ := exists_good_center pos₀ k R0 M hsum hcount
  refine ⟨v, fun T hcov => ?_⟩
  -- the scales fit in the ring
  have h4M : 4 ^ M ≤ k := Nat.pow_log_le_self 4 (by omega)
  have hkM : k < 4 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hwrap : 8 * (2 ^ M * R0) ≤ n := by
    have hsq : (8 * (2 ^ M * R0)) ^ 2 ≤ n ^ 2 := by
      calc (8 * (2 ^ M * R0)) ^ 2 = 64 * 4 ^ M * R0 ^ 2 := by rw [← four_pow_eq]; ring
        _ ≤ 64 * k * R0 ^ 2 := by gcongr
        _ ≤ (8 * k * R0) ^ 2 := by nlinarith
        _ ≤ n ^ 2 := by gcongr
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hsq
  have hRM : ∀ m ≤ M, 2 ^ m * R0 ≤ 2 ^ M * R0 := fun m hm =>
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hm)
  -- `R0² ≤ 32 T`
  have key : R0 ^ 2 ≤ 32 * T := by
    by_contra hT
    push Not at hT
    set S := fun m => ∑ s ∈ range T, nearCount pos₀ v (2 ^ m * R0) s
    have hstep : ∀ m < M, (2 ^ m * R0) ^ 2 * S m
        ≤ 2 * (2 ^ m * R0) ^ 2 * T * initCount pos₀ v (2 ^ (m + 1) * R0) + T * S (m + 1) := by
      intro m hm
      have h2R : 2 * (2 ^ m * R0) = 2 ^ (m + 1) * R0 := by ring
      have hwr : 4 * (2 ^ m * R0) + 2 ≤ n := by
        have := hRM (m + 1) (by omega); rw [← h2R] at this; omega
      simp only [S, Finset.mul_sum]
      calc ∑ s ∈ range T, (2 ^ m * R0) ^ 2 * nearCount pos₀ v (2 ^ m * R0) s
          ≤ ∑ s ∈ range T, (2 * (2 ^ m * R0) ^ 2 * nearCount pos₀ v (2 * (2 ^ m * R0)) 0
              + ∑ s' ∈ range s, nearCount pos₀ v (2 * (2 ^ m * R0)) s') :=
            Finset.sum_le_sum (fun s _ => scale_step pos₀ v _ hwr s)
        _ ≤ ∑ s ∈ range T, (2 * (2 ^ m * R0) ^ 2 * initCount pos₀ v (2 ^ (m + 1) * R0)
              + ∑ s' ∈ range T, nearCount pos₀ v (2 ^ (m + 1) * R0) s') := by
            apply Finset.sum_le_sum; intro s hs
            rw [h2R, nearCount_zero_eq]
            gcongr
            exact (Finset.mem_range.mp hs).le
        _ = 2 * (2 ^ m * R0) ^ 2 * T * initCount pos₀ v (2 ^ (m + 1) * R0)
              + T * ∑ s' ∈ range T, nearCount pos₀ v (2 ^ (m + 1) * R0) s' := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_range,
              smul_eq_mul, smul_eq_mul]; ring
        _ = _ := by simp only [Finset.mul_sum]
    have htop : S M ≤ k * T := by
      simp only [S]
      calc ∑ s ∈ range T, nearCount pos₀ v (2 ^ M * R0) s ≤ ∑ s ∈ range T, k := by
            apply Finset.sum_le_sum; intro s _
            rw [← hsum, ← sum_pos_run (ring n) ⟨pos₀, awayPtr v⟩ undelayed s]
            simp only [nearCount]
            apply Finset.sum_le_sum; intro x _; split_ifs <;> simp
        _ = k * T := by simp [mul_comm]
    have hN : ∀ m < M, initCount pos₀ v (2 ^ (m + 1) * R0) ≤ 4 ^ (m + 1) :=
      fun m hm => hvm (m + 1) (by simp; omega)
    have hk16 : k ≤ 16 * 4 ^ M := by rw [pow_succ] at hkM; omega
    have hS0 := multiscale S (fun m => initCount pos₀ v (2 ^ m * R0)) R0 T k M hstep htop hN hk16
      hT 0 (Nat.zero_le _)
    simp only [S, pow_zero, one_mul, mul_one] at hS0
    -- the hit lemma
    obtain ⟨s, hsT, hpos⟩ := exists_pos_of_visits (ring n) _ _ T v (hcov v)
    have hhit := hit_lemma pos₀ v R0 hR0 (by have := hRM 0 (Nat.zero_le _); simp at this; omega)
      (by rw [nearCount_zero_eq]; exact hv0) s hpos
    have hmono : ∑ s' ∈ range s, nearCount pos₀ v R0 s' ≤ ∑ s' ∈ range T, nearCount pos₀ v R0 s' :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hsT)
        (fun _ _ _ => Nat.zero_le _)
    omega
  -- conclusion
  have h16 : n < 16 * k * R0 := by nlinarith
  calc n ^ 2 < (16 * k * R0) ^ 2 := by gcongr
    _ = 256 * k ^ 2 * R0 ^ 2 := by ring
    _ ≤ 256 * k ^ 2 * (32 * T) := by gcongr
    _ = 8192 * k ^ 2 * T := by ring

end Podc.RotorRouterRing
