import Mathlib

/-!
# Throughput of NAB: eq. (6)/(24)–(28) and Theorem 3 (Liang–Vaidya, PODC 2012)

The paper bounds the time of `Q` instances of NAB by (eq. (24))
`t(Q) ≤ Q (L/γ* + L/ρ* + a) + b` (`a = O(n^α)`: the 1-bit broadcasts of step 2.2; `b = f(f+1)·O(L n^β)`:
at most `f(f+1)` dispute-control phases), and derives `T_NAB = γ* ρ* / (γ* + ρ*)` as `Q → ∞`, then
`L → ∞`. Theorem 3 compares `T_NAB` with the upper bound `C_BB ≤ min(γ*, 2ρ*)` of Theorem 2.
Theorem 2 (an information-theoretic capacity bound) is not formalized; it enters Theorem 3 as the
hypothesis `hC`.
-/

namespace Podc.ByzantineLinearCoding

open Filter Topology

/-- Eqs. (25)–(26): with the time bound (24), the throughput over `Q` instances tends to
`L / (L/γ + L/ρ + a)` as `Q → ∞`. -/
theorem tendsto_throughput_Q {γ ρ a b L : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hL : 0 < L) :
    Tendsto (fun Q : ℕ => L * Q / (Q * (L / γ + L / ρ + a) + b)) atTop
      (𝓝 (L / (L / γ + L / ρ + a))) := by
  have hd : 0 < L / γ + L / ρ + a := by positivity
  have h1 : Tendsto (fun Q : ℕ => L / ((L / γ + L / ρ + a) + b / Q)) atTop
      (𝓝 (L / (L / γ + L / ρ + a))) := by
    refine Tendsto.div tendsto_const_nhds ?_ hd.ne'
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat b)
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [show (Q : ℝ) * (L / γ + L / ρ + a) + b = (L / γ + L / ρ + a + b / Q) * Q by
    field_simp, mul_div_mul_right _ _ hQ'.ne']

/-- Eqs. (24)–(26): if `Q` instances take time `t Q ≤ Q (L/γ + L/ρ + a) + b`, the throughput
`L Q / t Q` is eventually at least `L / (L/γ + L/ρ + a) - ε`, for every `ε > 0`. -/
theorem throughput_eventually_ge {γ ρ a b L : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) (ha : 0 ≤ a)
    (hL : 0 < L) (t : ℕ → ℝ) (ht0 : ∀ Q, 0 < t Q)
    (ht : ∀ Q : ℕ, t Q ≤ Q * (L / γ + L / ρ + a) + b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, L / (L / γ + L / ρ + a) - ε ≤ L * Q / t Q := by
  have h := (tendsto_throughput_Q (b := b) hγ hρ ha hL).eventually
    (Ioi_mem_nhds (show L / (L / γ + L / ρ + a) - ε < L / (L / γ + L / ρ + a) by linarith))
  filter_upwards [h] with Q hQ
  refine (le_of_lt hQ).trans ?_
  exact div_le_div_of_nonneg_left (by positivity) (ht0 Q) (ht Q)

/-- Eqs. (27)–(28): `L / (L/γ + L/ρ + a) → γρ/(γ+ρ) = T_NAB` as `L → ∞`. -/
theorem tendsto_throughput_L {γ ρ a : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) :
    Tendsto (fun L : ℝ => L / (L / γ + L / ρ + a)) atTop (𝓝 (γ * ρ / (γ + ρ))) := by
  have h0 : Tendsto (fun L : ℝ => a / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hd : (1 / γ + 1 / ρ : ℝ) ≠ 0 := by positivity
  have h1 : Tendsto (fun L : ℝ => 1 / (1 / γ + 1 / ρ + a / L)) atTop
      (𝓝 (1 / (1 / γ + 1 / ρ))) := by
    refine Tendsto.div tendsto_const_nhds ?_ hd
    simpa using tendsto_const_nhds.add h0
  have heq : 1 / (1 / γ + 1 / ρ) = γ * ρ / (γ + ρ) := by field_simp; ring
  rw [← heq]
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  field_simp

/-- **Theorem 3** of [Liang–Vaidya, PODC 2012] (Appendix G): with `T_NAB = γρ/(γ+ρ)` and the
capacity bound `C_BB ≤ min(γ, 2ρ)` of Theorem 2, `T_NAB ≥ min(γ, 2ρ)/3 ≥ C_BB/3`, and, when
`γ ≤ ρ`, `T_NAB ≥ min(γ, 2ρ)/2 ≥ C_BB/2`. -/
theorem theorem_3 {γ ρ C : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) (hC : C ≤ min γ (2 * ρ)) :
    (min γ (2 * ρ) / 3 ≤ γ * ρ / (γ + ρ) ∧ C / 3 ≤ min γ (2 * ρ) / 3) ∧
    (γ ≤ ρ → min γ (2 * ρ) / 2 ≤ γ * ρ / (γ + ρ) ∧ C / 2 ≤ min γ (2 * ρ) / 2) := by
  have hs : 0 < γ + ρ := by positivity
  refine ⟨⟨?_, by linarith⟩, fun h => ⟨?_, by linarith⟩⟩
  · rw [le_div_iff₀ hs]
    rcases le_total γ (2 * ρ) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rw [min_eq_left (by linarith), le_div_iff₀ hs]; nlinarith

end Podc.ByzantineLinearCoding
