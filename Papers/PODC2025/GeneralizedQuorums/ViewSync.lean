import Mathlib

/-!
# Proposition 2 (view synchronization by growing timeouts, §7)

A process spends time `v · C` in view `v` (it enters view `v + 1` when the timer set at line 29
expires). After GST clocks do not drift, so in real time process `p` is in view `v` exactly during
`[a p + C·v(v-1)/2, a p + C·v(v+1)/2)` for a constant `a p` (its start time minus its clock offset),
for all large enough `v`. We state Proposition 2 in this form: for every duration `d` (and every
time `T`, e.g. GST) there is a view `V` such that for every `v ≥ V` all processes are in view `v`
during a common interval of length `d` starting after `T`. The paper gives no proof.
-/

namespace Podc.GeneralizedQuorums

/-- **Proposition 2.** -/
theorem proposition_2 {P : Type} [Fintype P] [Nonempty P] (a : P → ℝ) {C : ℝ} (hC : 0 < C)
    (d T : ℝ) :
    ∃ V : ℕ, ∀ v ≥ V, ∃ x, T ≤ x ∧ ∀ p, a p + C * (v * (v - 1) / 2) ≤ x ∧
      x + d ≤ a p + C * (v * (v + 1) / 2) := by
  obtain ⟨p₀⟩ := ‹Nonempty P›
  let M := Finset.univ.sup' ⟨p₀, Finset.mem_univ _⟩ a
  let m := Finset.univ.inf' ⟨p₀, Finset.mem_univ _⟩ a
  have hM : ∀ p, a p ≤ M := fun p => Finset.le_sup' a (Finset.mem_univ p)
  have hm : ∀ p, m ≤ a p := fun p => Finset.inf'_le a (Finset.mem_univ p)
  obtain ⟨V, hV⟩ := exists_nat_ge ((|T - M| + (M - m) + |d|) / C + 2)
  refine ⟨V, fun v hv => ⟨M + C * (v * (v - 1) / 2), ?_, fun p => ⟨by linarith [hM p], ?_⟩⟩⟩
  · have hv' : ((|T - M| + (M - m) + |d|) / C + 2 : ℝ) ≤ v := hV.trans (by exact_mod_cast hv)
    have h1 : |T - M| + (M - m) + |d| ≤ C * (v - 2) := by
      rw [div_add' _ _ _ hC.ne', div_le_iff₀ hC] at hv'; nlinarith
    have hMm : 0 ≤ M - m := by linarith [hM p₀, hm p₀]
    have hv2 : (2 : ℝ) ≤ v := by
      have : 0 ≤ (|T - M| + (M - m) + |d|) / C := by positivity
      linarith
    have : C * (v - 2) ≤ C * (v * (v - 1) / 2) := by
      apply mul_le_mul_of_nonneg_left _ hC.le; nlinarith
    linarith [le_abs_self (T - M), abs_nonneg d]
  · have hv' : ((|T - M| + (M - m) + |d|) / C + 2 : ℝ) ≤ v := hV.trans (by exact_mod_cast hv)
    have h1 : |T - M| + (M - m) + |d| ≤ C * (v - 2) := by
      rw [div_add' _ _ _ hC.ne', div_le_iff₀ hC] at hv'; nlinarith
    have : C * (v * (v + 1) / 2) - C * (v * (v - 1) / 2) = C * v := by ring
    nlinarith [hm p, le_abs_self d, abs_nonneg (T - M)]

end Podc.GeneralizedQuorums
