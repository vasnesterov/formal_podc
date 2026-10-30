import Papers.PODC2012.CollaborativeSearchPlane.Theorem41

/-!
# The trivial lower bound `Ω(D + D²/k)` (§2 and footnote 2)

§2 states: "it is easy to see that the expected running time is `Ω(D + D²/k)`, even if the number of
agents `k` is known to all agents" (footnote 2). The argument of footnote 2 (Markov plus counting)
is `sq_div_le`: if every node within distance `D` is found in expected time `≤ T`, then
`D²/(8k) ≤ T + 1`. It needs no assumption on the agents (they need not even be identical). The
`Ω(D)` part needs that agents walk on the grid from the source (`IsWalk`): then no node at distance
`D` is found before time `D`. Together (`footnote_2`): for every `k ≥ 1` agents walking on the
grid and every `D ≥ 1`, some treasure at distance `≤ D` has expected finding time
`≥ (D + D²/k)/20`.

The bound is over treasures at distance *at most* `D`, as in the footnote's proof; for a fixed
exact distance `D` it is false in general (agents that walk to distance `D` and then around the
sphere of radius `D` find every treasure at distance exactly `D` in time `O(D)`), which is harmless
because competitiveness is required for all `D`.
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset
open scoped ENNReal

/-- Footnote 2 (counting part): for *any* `k ≥ 1` agents with laws `ν`, if every node within
distance `D` is found in expected time `≤ T`, then `D²/(8k) ≤ T + 1`. -/
theorem sq_div_le {k : ℕ} (hk : 1 ≤ k) (ν : Fin k → Measure Traj)
    [∀ a, IsProbabilityMeasure (ν a)] (D : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hE : ∀ u : Node, dist u ≤ D → expectedTime ν u ≤ ENNReal.ofReal T) :
    (D : ℝ) ^ 2 / (8 * k) ≤ T + 1 := by
  set N := ⌈2 * T⌉₊
  have hN1 : 2 * T ≤ (N : ℝ) + 1 := by have := Nat.le_ceil (2 * T); linarith
  have hN2 : (N : ℝ) + 1 ≤ 2 * T + 2 := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * T); linarith
  have hT' : 2 * ENNReal.ofReal T ≤ (N : ℝ≥0∞) + 1 := by
    have : ENNReal.ofReal (2 * T) ≤ ENNReal.ofReal ((N : ℝ) + 1) := ENNReal.ofReal_le_ofReal hN1
    rw [ENNReal.ofReal_mul (by norm_num)] at this
    simpa [ENNReal.ofReal_add, ENNReal.ofReal_natCast] using this
  -- each node within distance `D`: the visit probabilities of the agents sum to `≥ 1/2`
  have hu : ∀ n ∈ range (D + 1), ∀ q ∈ antidiagonal n,
      (1 / 2 : ℝ) ≤ ∑ a, (ν a (visitedBy N (quad q))).toReal := by
    intro n hn q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h := half_le_sum_visit ν (quad q) _ N
      (hE _ (by rw [dist_quad, hq]; exact Nat.lt_succ_iff.1 (mem_range.1 hn))) hT'
    have h' := ENNReal.toReal_mono (by simp [measure_ne_top]) h
    rw [ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)] at h'
    simpa using h'
  have hsum : ∑ n ∈ range (D + 1), ((n : ℝ) + 1) / 2 ≤ k * ((N : ℝ) + 1) := by
    calc ∑ n ∈ range (D + 1), ((n : ℝ) + 1) / 2
        = ∑ n ∈ range (D + 1), ∑ _q ∈ antidiagonal n, (1 / 2 : ℝ) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring
      _ ≤ ∑ n ∈ range (D + 1), ∑ q ∈ antidiagonal n, ∑ a, (ν a (visitedBy N (quad q))).toReal :=
          Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun q hq => hu n hn q hq
      _ = ∑ n ∈ range (D + 1), ∑ a, diagMass (ν a) N n :=
          Finset.sum_congr rfl fun n _ => Finset.sum_comm
      _ = ∑ a, ∑ n ∈ range (D + 1), diagMass (ν a) N n := Finset.sum_comm
      _ ≤ ∑ _a : Fin k, ((N : ℝ) + 1) := Finset.sum_le_sum fun a _ => sum_diagMass_le (ν a) _ N
      _ = k * ((N : ℝ) + 1) := by simp; ring
  have hgauss : (D : ℝ) ^ 2 / 2 ≤ ∑ n ∈ range (D + 1), ((n : ℝ) + 1) := by
    have h := sum_Ico_ge 0 D (Nat.zero_le _)
    simp only [zero_add, Nat.cast_zero] at h
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [Nat.cast_zero, zero_add]
    have : (0 : ℝ) ≤ (D : ℝ) ^ 2 := by positivity
    linarith
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_div] at hsum
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- A trajectory is a walk on the grid from the source: it starts at `(0,0)` and at each step moves
to a neighbour or stays. -/
def IsWalk (ω : Traj) : Prop := ω 0 = 0 ∧ ∀ t, dist (ω (t + 1) - ω t) ≤ 1

theorem IsWalk.dist_le {ω : Traj} (h : IsWalk ω) (t : ℕ) : dist (ω t) ≤ t := by
  induction t with
  | zero => simp [h.1, dist]
  | succ t ih =>
    have hs := h.2 t
    have e : ω (t + 1) = ω t + (ω (t + 1) - ω t) := by abel
    have h1 : dist (ω (t + 1)) ≤ dist (ω t) + dist (ω (t + 1) - ω t) := by
      rw [e]
      simp only [dist, Prod.fst_add, Prod.snd_add, add_sub_cancel_left]
      have := Int.natAbs_add_le (ω t).1 ((ω (t + 1)).1 - (ω t).1)
      have := Int.natAbs_add_le (ω t).2 ((ω (t + 1)).2 - (ω t).2)
      simp only [Prod.fst_sub, Prod.snd_sub] at *
      omega
    omega

/-- Agents walking on the grid from the source need time `≥ d(s, u)` to find `u`. -/
theorem dist_le_expectedTime {k : ℕ} (ν : Fin k → Measure Traj) [∀ a, IsProbabilityMeasure (ν a)]
    (hw : ∀ a, ∀ᵐ ω ∂(ν a), IsWalk ω) (u : Node) : (dist u : ℝ≥0∞) ≤ expectedTime ν u := by
  have hae : ∀ᵐ ω ∂(Measure.pi ν), ∀ a, IsWalk (ω a) := by
    rw [ae_all_iff]
    intro a
    exact (measurePreserving_eval ν a).quasiMeasurePreserving.ae (hw a)
  have hae' : ∀ᵐ ω ∂(Measure.pi ν), (dist u : ℝ≥0∞) ≤ findTime ω u := by
    filter_upwards [hae] with ω hω
    simp only [findTime, le_iInf_iff]
    intro a t ht
    have := (hω a).dist_le t
    rw [ht] at this
    exact_mod_cast this
  calc (dist u : ℝ≥0∞) = ∫⁻ _, (dist u : ℝ≥0∞) ∂(Measure.pi ν) := by simp
    _ ≤ expectedTime ν u := lintegral_mono_ae hae'

/-- **§2, footnote 2**: for `k ≥ 1` agents walking on the grid from the source (not necessarily
identical, knowing `k` or not) and every `D ≥ 1`, some treasure at distance at most `D` has expected
finding time at least `(D + D²/k)/20`; i.e. the running time is `Ω(D + D²/k)`. -/
theorem footnote_2 {k : ℕ} (hk : 1 ≤ k) (ν : Fin k → Measure Traj)
    [∀ a, IsProbabilityMeasure (ν a)] (hw : ∀ a, ∀ᵐ ω ∂(ν a), IsWalk ω) {D : ℕ} (hD : 1 ≤ D) :
    ∃ τ : Node, dist τ ≤ D ∧
      ENNReal.ofReal (((D : ℝ) + (D : ℝ) ^ 2 / k) / 20) ≤ expectedTime ν τ := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set T : ℝ := ((D : ℝ) + (D : ℝ) ^ 2 / k) / 20
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hT : 0 ≤ T := by positivity
  have h1 := sq_div_le hk ν D T hT fun u hu => (hcon u hu).le
  -- the node `(D, 0)` at distance `D`
  have hd : dist ((D : ℤ), (0 : ℤ)) = D := by simp [dist]
  have h2 := (dist_le_expectedTime ν hw ((D : ℤ), 0)).trans_lt (hcon _ hd.le)
  rw [hd, ← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h2
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set x : ℝ := (D : ℝ) ^ 2 / k
  have hx : (D : ℝ) ^ 2 / (8 * k) = x / 8 := by simp only [x]; field_simp
  rw [hx] at h1
  simp only [T] at h1 h2
  linarith

end Podc.CollaborativeSearchPlane
