import Papers.PODC2023.PPDoubleExpThresholds.Totals

/-!
# Lemma 11(c) is false

Lemma 11(c) claims that `IncrPair(x, y)` is `j`-robust for all `j ≤ i`. For `j = i` this fails:
with one level (`n = i = 1`, `N₁ = 1`) the configuration `x₁ = 0, x̄₁ = 1, y₁ = 1, ȳ₁ = 0` is
`1`-high (and weakly `1`-proper), but `IncrPair(x̄₁, ȳ₁)` increments the counter
`ctr_{x̄,ȳ} = 2` to `3`, i.e. returns `x̄₁ = ȳ₁ = 1, x₁ = y₁ = 0`, which is `1`-proper and hence
not `1`-high. (In general: any weakly `i`-proper, not `i`-proper configuration whose counter is
one step before the `i`-proper value.) The paper's proof of 11(c) overlooks that lines 3, 5–7
of `IncrPair` change level-`i` registers. Lemma 11(c) is used (only) in the proof of Lemma 12(c)
for `j = i − 1`; Lemma 12(c) remains true (`large_robust_mid`, proved by a symmetry argument).
-/

namespace Podc.PPDoubleExpThresholds

open Program

/-- The counterexample configuration: `x₁ = 0, x̄₁ = 1, y₁ = 1, ȳ₁ = 0, R = 0`. -/
def cex11c : Reg 1 → ℕ := mk (fun _ k => if k = 1 ∨ k = 2 then 1 else 0) 0

theorem cex11c_high : High cex11c 1 := by
  refine ⟨fun l hl hl0 => by omega, fun h => ?_, ?_, ?_⟩
  · have := (h 1 le_rfl le_rfl).2.2.1
    simp [cex11c, mk_reg (n := 1) _ _ le_rfl le_rfl] at this
  all_goals simp [psum, bar, cex11c, mk_reg (n := 1) _ _ le_rfl le_rfl, N]

/-- **Lemma 11(c) is false** (for `j = i`): `IncrPair(x̄₁, ȳ₁)` is not `1`-robust. -/
theorem lemma_11c_false : ¬ RobustOn 1 (fun j => j ≤ 1) (.incrPair 1 true true) := by
  intro h
  obtain ⟨hT, hR⟩ := h 1 le_rfl le_rfl le_rfl cex11c false cex11c_high
  have hW : WProper cex11c 1 := ⟨fun l hl hl0 => by omega,
    by simp [psum, bar, cex11c, mk_reg (n := 1) _ _ le_rfl le_rfl, N],
    by simp [psum, bar, cex11c, mk_reg (n := 1) _ _ le_rfl le_rfl, N]⟩
  have hA := (levels 1 le_rfl le_rfl).incrA true true cex11c false hW
  rcases hT.returns_or_restarts with ⟨C', OF', b, hret⟩ | hrst
  · obtain ⟨-, -, ⟨-, h0, h2⟩, -, hctr⟩ := (hA.1 C' OF' b).1 hret
    have hH := (hR C' OF' b hret).2
    apply hH.2.1
    simp only [ctr, kx, ky, if_true, cex11c, mk_reg (n := 1) _ _ le_rfl le_rfl, N] at hctr
    simp only [psum, bar, N] at h0 h2
    intro l hl hl1
    obtain rfl : l = 1 := by omega
    simp only [N]
    norm_num at hctr
    omega
  · exact hA.2.1 hrst

end Podc.PPDoubleExpThresholds
