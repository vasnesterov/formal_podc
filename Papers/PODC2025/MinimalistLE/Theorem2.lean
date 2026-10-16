import Papers.PODC2025.MinimalistLE.Main
import Papers.PODC2025.MinimalistLE.Window

/-!
# Theorem 2: `O(D² log n)` rounds with high probability, for every fixed `p ∈ (0, 1)`

While `u` and `v` are both leaders, `(phase u, phase v, N(u) − N(v))` follows the pair chain
(`pchain_couple`, the paper's coupling with independent chains). By Lemma 11, `|N(u) − N(v)| ≤ D`
while both are leaders, so both stay leaders for `T₂ = ⌈(D+2)²(1+2p)³/(p(1−p)) + 4⌉` rounds only if
the pair chain stays in the strip, which has probability `≤ 1/2` (`Window.lean`). Hence
`P(u, v both leaders at k·T₂) ≤ 2^{-k}`, and a union bound over pairs gives the theorem.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory unitInterval

namespace MinimalistLE

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {init : V → St}

/-- A node that is a leader in round `s+1` moved along the leader chain with its own coin. -/
theorem leader_phase_step {c : ℕ → V → Bool} {s : ℕ} {w : V}
    (h : (exec G init c (s + 1) w).leader = true) :
    (exec G init c (s + 1) w).phase = cstep (exec G init c s w).phase (c s w) := by
  have h0 := leader_of_succ h
  rw [exec_succ] at h ⊢
  rcases hp : (exec G init c s w).phase
  · rw [next_of_W hp] at h ⊢
    split_ifs at h ⊢ with h1 h2 <;> simp_all [cstep]
  · simp [hp, cstep]
  · simp [hp, cstep]

variable (G init) in
/-- The observed state of the pair `(u, v)` in round `t`. -/
def obs (ω : ℕ × V → Bool) (t : ℕ) (u v : V) : PS :=
  ((exec G init (field ω) t u).phase, (exec G init (field ω) t v).phase,
    (nbeep G init (field ω) t u : ℤ) - nbeep G init (field ω) t v)

/-- **Coupling.** While `u` and `v` are leaders, the pair chain started from the observed state at
time `t` is the observed state. -/
theorem pchain_couple (ω : ℕ × V → Bool) (t : ℕ) (u v : V) (j : ℕ)
    (hu : (exec G init (field ω) (t + j) u).leader = true)
    (hv : (exec G init (field ω) (t + j) v).leader = true) :
    pchain t u v (obs G init ω t u v) ω j = obs G init ω (t + j) u v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc] at hu hv ⊢
    have hu' := leader_phase_step hu
    have hv' := leader_phase_step hv
    have e : pchain t u v (obs G init ω t u v) ω (j + 1) =
        pstep (pchain t u v (obs G init ω t u v) ω j) (ω (t + j, u)) (ω (t + j, v)) := rfl
    rw [e, ih (leader_of_succ hu) (leader_of_succ hv)]
    simp only [pstep, obs]
    simp only [field] at hu' hv'
    rw [← hu', ← hv', nbeep_succ, nbeep_succ]
    simp only [Prod.mk.injEq, true_and, Beeps, ind]
    push_cast
    split_ifs <;> ring

/-- The window length `T₂(p, D) = ⌈(D+2)²(1+2p)³/(p(1−p)) + 4⌉`. -/
noncomputable def T2 (p : ℝ) (D : ℕ) : ℕ :=
  ⌈((D : ℝ) + 2) ^ 2 * (1 + 2 * p) ^ 3 / (p * (1 - p)) + 4⌉₊

theorem alive_half (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {t : ℕ} {u v : V} (huv : u ≠ v)
    {D : ℕ} {y0 : PS} (hy0 : |y0.2.2| ≤ D) :
    (coinP p).real (Alive t u v y0 D (T2 p D)) ≤ 1 / 2 := by
  have hb := alive_bound (t := t) p hp0 hp1 huv hy0 (T2 p D)
  have hl := lyap_le hp0 hp1 D y0
  have h1 : 0 < 1 - (p : ℝ) := by linarith
  set G := ((D : ℝ) + 2) ^ 2 * (1 + 2 * (p : ℝ)) ^ 3 / (2 * p * (1 - p)) + 2
  have hG : 0 < G := by positivity
  have hT : 2 * G ≤ (T2 p D : ℝ) := by
    refine le_trans (le_of_eq ?_) (Nat.le_ceil _)
    simp only [G]; field_simp; ring
  have hP := measureReal_nonneg (μ := coinP p) (s := Alive t u v y0 D (T2 p D))
  have : (T2 p D : ℝ) * (coinP p).real (Alive t u v y0 D (T2 p D)) ≤ G := hb.trans hl
  by_contra hc
  push Not at hc
  nlinarith

theorem determined_obs (t : ℕ) (u v : V) (y : PS) :
    Determined {ω | obs G init ω t u v = y} (past t) := fun ω ω' h => by
  simp only [obs, Set.mem_ofPred_eq, exec_congr (field_eq_of h), nbeep_congr (field_eq_of h)]

theorem disjoint_past_wc (t T : ℕ) (u v : V) : Disjoint (past (V := V) t) (wc t u v T) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [past, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at hi
  simp only [wc, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hi'
  rcases hi' with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩ <;> simp at hi

/-- **One window of length `T₂`.** -/
theorem both_step2 (hconn : G.Connected) (hW : ∀ v, (init v).phase = .W) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {D : ℕ} (hD : ∀ a b, G.dist a b ≤ D) {u v : V}
    (huv : u ≠ v) (t : ℕ) :
    (coinP p).real (Both G init (t + T2 p D) u v) ≤ 1 / 2 * (coinP p).real (Both G init t u v) := by
  classical
  set A := Both G init t u v
  have hA : Determined A (past t) := determined_both t u v
  have hobs_mem : ∀ ω ∈ A, obs G init ω t u v ∈ Ys D := by
    intro ω hω
    rw [mem_Ys]
    have := lemma11 (c := field ω) hconn hW u v t
    have := hD u v
    simp only [obs]; omega
  have hsub : Both G init (t + T2 p D) u v ⊆
      ⋃ y ∈ Ys D, (A ∩ {ω | obs G init ω t u v = y}) ∩ Alive t u v y D (T2 p D) := by
    rintro ω ⟨hu, hv⟩
    have hA' : ω ∈ A := ⟨leader_anti (by omega) hu, leader_anti (by omega) hv⟩
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_prop]
    refine ⟨_, hobs_mem ω hA', ⟨hA', rfl⟩, fun i hi => ?_⟩
    have hui := leader_anti (show t + i ≤ t + T2 p D by omega) hu
    have hvi := leader_anti (show t + i ≤ t + T2 p D by omega) hv
    rw [pchain_couple ω t u v i hui hvi]
    have := lemma11 (c := field ω) hconn hW u v (t + i)
    have := hD u v
    simp only [obs]; omega
  calc (coinP p).real (Both G init (t + T2 p D) u v)
      ≤ ∑ y ∈ Ys D, (coinP p).real ((A ∩ {ω | obs G init ω t u v = y}) ∩ Alive t u v y D (T2 p D)) :=
        (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
    _ = ∑ y ∈ Ys D, (coinP p).real (A ∩ {ω | obs G init ω t u v = y}) *
          (coinP p).real (Alive t u v y D (T2 p D)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [coinP_real_inter p ((hA.inter (determined_obs t u v y)).mono (by simp))
          (determined_alive (T2 p D)) (disjoint_past_wc t (T2 p D) u v)]
    _ ≤ ∑ y ∈ Ys D, (coinP p).real (A ∩ {ω | obs G init ω t u v = y}) * (1 / 2) := by
        refine Finset.sum_le_sum fun y hy => ?_
        exact mul_le_mul_of_nonneg_left (alive_half p hp0 hp1 huv (mem_Ys.1 hy)) measureReal_nonneg
    _ = 1 / 2 * (coinP p).real A := by
        rw [← Finset.sum_mul, ← coinP_real_partition p hA _ (determined_obs t u v) _ hobs_mem,
          mul_comm]

theorem both_le2 (hconn : G.Connected) (hW : ∀ v, (init v).phase = .W) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {D : ℕ} (hD : ∀ a b, G.dist a b ≤ D) {u v : V}
    (huv : u ≠ v) (k : ℕ) :
    (coinP p).real (Both G init (k * T2 p D) u v) ≤ (1 / 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, pow_succ]
    calc _ ≤ 1 / 2 * (coinP p).real (Both G init (k * T2 p D) u v) :=
          both_step2 hconn hW p hp0 hp1 hD huv _
      _ ≤ 1 / 2 * (1 / 2) ^ k := by gcongr
      _ = _ := by ring

/-- **Theorem 2 (time bound, explicit).** For every `p ∈ (0,1)` and every `D ≥` the diameter,
`P(no single leader from round k·T₂(p,D) on) ≤ n²·2^{-k}`, where
`T₂(p,D) = ⌈(D+2)²(1+2p)³/(p(1−p)) + 4⌉ = O(D²)`. -/
theorem theorem2_time (hconn : G.Connected) (hI : GoodInit init) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {D : ℕ} (hD : ∀ a b, G.dist a b ≤ D) (k : ℕ) :
    (coinP p).real {ω | ¬ UniqueFrom G init (k * T2 p D) ω} ≤
      (Fintype.card V : ℝ) ^ 2 * (1 / 2) ^ k := by
  classical
  have hsub : {ω | ¬ UniqueFrom G init (k * T2 p D) ω} ⊆
      ⋃ x : V × V, if x.1 = x.2 then ∅ else Both G init (k * T2 p D) x.1 x.2 := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_iUnion, not_exists] at hn
    refine hω (unique_forever hI fun a b ha hb => ?_)
    by_contra hab
    have := hn (a, b)
    simp only [hab, ↓reduceIte] at this
    exact this ⟨ha, hb⟩
  calc _ ≤ ∑ x : V × V, (coinP p).real
        (if x.1 = x.2 then ∅ else Both G init (k * T2 p D) x.1 x.2) :=
        (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)
    _ ≤ ∑ _x : V × V, ((1 : ℝ) / 2) ^ k := by
        gcongr with x
        split_ifs with h
        · simp
        · exact both_le2 hconn hI.waiting p hp0 hp1 hD h k
    _ = _ := by simp [Fintype.card_prod, sq]

/-- **Theorem 2 (w.h.p. form).** For every `p ∈ (0,1)`, with probability at least `1 - 1/n²` a single
leader is elected by round `⌈6 ln n⌉ · T₂(p, D)`, i.e. within `O(D² log n)` rounds. -/
theorem theorem2_whp (hconn : G.Connected) (hI : GoodInit init) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {D : ℕ} (hD : ∀ a b, G.dist a b ≤ D) :
    (coinP p).real
        {ω | ¬ UniqueFrom G init (⌈6 * Real.log (Fintype.card V)⌉₊ * T2 p D) ω} ≤
      1 / (Fintype.card V : ℝ) ^ 2 := by
  set n : ℝ := (Fintype.card V : ℝ)
  have hn : 1 ≤ n := by
    obtain ⟨v, -⟩ := hI.leader
    have := Fintype.card_pos_iff.2 ⟨v⟩
    simp only [n]; exact_mod_cast this
  set k := ⌈6 * Real.log n⌉₊
  refine (theorem2_time hconn hI p hp0 hp1 hD k).trans ?_
  have hk : 6 * Real.log n ≤ k := Nat.le_ceil _
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  have hl2 := Real.log_two_gt_d9
  have h1 : ((1 : ℝ) / 2) ^ k = Real.exp (-(k * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]; simp
  have h2 : Real.exp (-(k * Real.log 2)) ≤ Real.exp (-(4 * Real.log n)) := by
    apply Real.exp_le_exp.2; nlinarith
  have h3 : Real.exp (-(4 * Real.log n)) = 1 / n ^ 4 := by
    rw [Real.exp_neg, show (4 : ℝ) * Real.log n = (4 : ℕ) * Real.log n by norm_num,
      Real.exp_nat_mul, Real.exp_log (by linarith), one_div]
  have hn2 : 0 < n ^ 2 := by positivity
  calc n ^ 2 * (1 / 2) ^ k ≤ n ^ 2 * (1 / n ^ 4) := by
        gcongr; rw [h1]; exact h2.trans h3.le
    _ = 1 / n ^ 2 := by field_simp

end MinimalistLE
