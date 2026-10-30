import Papers.PODC2012.CollaborativeSearchPlane.Theorem42

/-!
# Non-vacuity: competitive algorithms exist

The hypotheses `IsCompetitive μ φ` (Theorem 4.1) and `IsCompetitiveAdvice A ε φ` with `φ` monotone
(Theorem 4.2) are satisfiable: a single deterministic agent that enumerates `ℤ²` via `Nat.pair`
visits every node `u` by time `(2 d(u) + 1)² ≤ 9 d(u)²`, so it is `9k`-competitive (for the trivial
reason `D² ≤ k · D²/k`). This enumeration teleports, which our model allows (the lower bounds do not
need the grid-walk restriction); for grid walks the paper's Theorem 3.3 gives non-vacuity.
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset
open scoped ENNReal

/-- If agent `a` is at `u` at time `t` almost surely, the expected running time is at most `t`. -/
theorem expectedTime_le_of_ae {k : ℕ} (ν : Fin k → Measure Traj) [∀ a, IsProbabilityMeasure (ν a)]
    (a : Fin k) (u : Node) (t : ℕ) (h : ν a {ω | ω t = u}ᶜ = 0) : expectedTime ν u ≤ t := by
  have hm : MeasurableSet {ω : Traj | ω t = u} :=
    (show MeasurableSet ((fun ω : Traj => ω t) ⁻¹' {u}) from
      (measurable_pi_apply t) (measurableSet_singleton u))
  have h0 : Measure.pi ν ((Function.eval a) ⁻¹' {ω : Traj | ω t = u}ᶜ) = 0 := by
    rw [(measurePreserving_eval ν a).measure_preimage hm.compl.nullMeasurableSet, h]
  have hae : ∀ᵐ ω ∂(Measure.pi ν), findTime ω u ≤ t := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.eval, Set.mem_compl_iff] at hω ⊢
    intro hat
    exact hω (iInf₂_le_of_le a t (iInf_le_of_le hat le_rfl))
  calc expectedTime ν u ≤ ∫⁻ _, (t : ℝ≥0∞) ∂(Measure.pi ν) := lintegral_mono_ae hae
    _ = t := by simp

/-- Decoding `ℕ → ℤ`: `2n ↦ n`, `2n + 1 ↦ -(n+1)`. -/
def decInt (n : ℕ) : ℤ := if n % 2 = 0 then (n / 2 : ℕ) else -(((n + 1) / 2 : ℕ) : ℤ)

/-- Encoding `ℤ → ℕ`, inverse to `decInt`. -/
def encInt (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.natAbs else 2 * z.natAbs - 1

theorem decInt_encInt (z : ℤ) : decInt (encInt z) = z := by
  unfold decInt encInt
  split_ifs with h1 h2 h2 <;> omega

theorem encInt_le (z : ℤ) : encInt z ≤ 2 * z.natAbs := by
  unfold encInt; split_ifs <;> omega

/-- The enumeration trajectory: at time `t = pair(m, n)` the agent is at `(decInt m, decInt n)`. -/
def enumTraj : Traj := fun t => (decInt (Nat.unpair t).1, decInt (Nat.unpair t).2)

/-- The time at which `enumTraj` is at `u`. -/
def enumTime (u : Node) : ℕ := Nat.pair (encInt u.1) (encInt u.2)

theorem enumTraj_enumTime (u : Node) : enumTraj (enumTime u) = u := by
  simp [enumTraj, enumTime, Nat.unpair_pair, decInt_encInt]

theorem enumTime_le (u : Node) : (enumTime u : ℝ) ≤ 9 * (dist u : ℝ) ^ 2 := by
  have h1 := Nat.pair_lt_max_add_one_sq (encInt u.1) (encInt u.2)
  have h2 : max (encInt u.1) (encInt u.2) ≤ 2 * dist u := by
    have := encInt_le u.1; have := encInt_le u.2; unfold dist; omega
  rcases Nat.eq_zero_or_pos (dist u) with h0 | h0
  · have hu : u.1 = 0 ∧ u.2 = 0 := by unfold dist at h0; omega
    have : enumTime u = 0 := by
      simp [enumTime, hu.1, hu.2, encInt, Nat.pair]
    simp [this]
  · have h3 : enumTime u < (2 * dist u + 1) ^ 2 :=
      lt_of_lt_of_le h1 (Nat.pow_le_pow_left (by omega) 2)
    have h4 : (2 * dist u + 1) ^ 2 ≤ 9 * dist u ^ 2 := by nlinarith
    exact_mod_cast (h3.trans_le h4).le

/-- **Non-vacuity of Theorem 4.1**: the enumeration agent is a `9k`-competitive uniform algorithm. -/
theorem isCompetitive_enum :
    IsCompetitive (Measure.dirac enumTraj) (fun k => 9 * (k : ℝ)) := by
  intro k hk τ _
  have ht := expectedTime_le_of_ae (fun _ : Fin k => Measure.dirac enumTraj) ⟨0, hk⟩ τ
    (enumTime τ) (by
      rw [Measure.dirac_apply]
      simp [enumTraj_enumTime])
  refine ht.trans ?_
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ((enumTime_le τ).trans ?_)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold optBound
  have e : 9 * (k : ℝ) * ((dist τ : ℝ) + (dist τ : ℝ) ^ 2 / k)
      = 9 * k * dist τ + 9 * (dist τ : ℝ) ^ 2 := by field_simp
  simp only [e]
  have : (0 : ℝ) ≤ 9 * k * dist τ := by positivity
  linarith

/-- **Non-vacuity of Theorem 4.2**: ignoring the advice, the enumeration agent is a `9k`-competitive
algorithm with advice, and `k ↦ 9k` is non-decreasing. -/
theorem isCompetitiveAdvice_enum (ε : ℕ → ℝ) :
    IsCompetitiveAdvice (fun _ => Measure.dirac enumTraj) ε (fun k => 9 * (k : ℝ)) ∧
      Monotone (fun k : ℕ => 9 * (k : ℝ)) :=
  ⟨fun k hk _ _ τ hτ => isCompetitive_enum k hk τ hτ, fun a b h => by
    simp only; have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith⟩

end Podc.CollaborativeSearchPlane
