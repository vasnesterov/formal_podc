import Mathlib

-- CSLib candidate (paper-local for now)

/-!
# Rank one: the kernel of an irreducible "flow" system is a line

The linear-algebra core of the positive half of Theorem 4.1 (Section 4.2). For the minimum base of
the network, the fibre cardinalities `z` satisfy eq. (1): `b_C z_C = ∑_{C'} d_{C,C'} z_{C'}`. The
paper shows with a Perron–Frobenius argument that the solution space `ker M` is one-dimensional.
We give the elementary maximum-principle proof: if `z > 0` is a solution and the support graph of
`d` is strongly connected, every solution `y` is a multiple of `z`. (Take `r = max y/z`; then
`w = r z - y ≥ 0` is a solution vanishing somewhere, and the equations propagate the zeros along
the edges.)
-/

namespace Podc.KnowYourAudience

open Finset

/-- **Rank-one lemma.** Let `S` be finite, `e : α → α → ℕ` (edge multiplicities) and
`b : α → ℕ`. If `z` is a positive solution of `b_c y_c = ∑_{c' ∈ S} e_{c c'} y_{c'}` (`c ∈ S`) and
the graph `c → c'` (`e_{c c'} > 0`) is strongly connected on `S`, then every solution `y` is a
rational multiple of `z`. -/
theorem exists_eq_mul_of_irreducible {α : Type*} (S : Finset α) (e : α → α → ℕ) (b : α → ℕ)
    (y z : α → ℚ)
    (hy : ∀ c ∈ S, (b c : ℚ) * y c = ∑ c' ∈ S, (e c c' : ℚ) * y c')
    (hz : ∀ c ∈ S, (b c : ℚ) * z c = ∑ c' ∈ S, (e c c' : ℚ) * z c')
    (hzpos : ∀ c ∈ S, 0 < z c)
    (hconn : ∀ c ∈ S, ∀ c' ∈ S,
      Relation.ReflTransGen (fun a a' => a ∈ S ∧ a' ∈ S ∧ 0 < e a a') c c') :
    ∃ r : ℚ, ∀ c ∈ S, y c = r * z c := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp⟩
  obtain ⟨c₀, hc₀, hmax⟩ := Finset.exists_max_image S (fun c => y c / z c) hne
  set r := y c₀ / z c₀
  set w : α → ℚ := fun c => r * z c - y c with hw_def
  have hw0 : w c₀ = 0 := by
    simp only [hw_def, r]; field_simp [(hzpos c₀ hc₀).ne']; ring
  have hwnn : ∀ c ∈ S, 0 ≤ w c := by
    intro c hc
    have := hmax c hc
    rw [div_le_iff₀ (hzpos c hc)] at this
    simp only [hw_def]; linarith
  have hweq : ∀ c ∈ S, (b c : ℚ) * w c = ∑ c' ∈ S, (e c c' : ℚ) * w c' := by
    intro c hc
    simp only [hw_def, mul_sub, Finset.sum_sub_distrib]
    rw [← hy c hc]
    have : ∑ c' ∈ S, (e c c' : ℚ) * (r * z c') = r * ∑ c' ∈ S, (e c c' : ℚ) * z c' := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [this, ← hz c hc]; ring
  have hprop : ∀ a a', a ∈ S ∧ a' ∈ S ∧ 0 < e a a' → w a = 0 → w a' = 0 := by
    rintro a a' ⟨ha, ha', he⟩ hwa
    have hsum := hweq a ha
    rw [hwa, mul_zero, eq_comm, Finset.sum_eq_zero_iff_of_nonneg] at hsum
    · have := hsum a' ha'
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by exact_mod_cast he.ne')
      · exact h
    · intro c hc; exact mul_nonneg (by positivity) (hwnn c hc)
  refine ⟨r, fun c hc => ?_⟩
  have : w c = 0 := by
    have hpath := hconn c₀ hc₀ c hc
    induction hpath with
    | refl => exact hw0
    | tail _ hab ih => exact hprop _ _ hab (ih hab.1)
  simp only [hw_def] at this
  linarith

end Podc.KnowYourAudience
