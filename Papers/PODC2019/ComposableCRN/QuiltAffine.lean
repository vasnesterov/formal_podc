import Papers.PODC2019.ComposableCRN.Automaton

/-!
# Lemma 6.1: quilt-affine functions are obliviously-computable

The CRN of the paper: a leader tracks `x mod p` (states `L_a`, `a ∈ (ℤ/pℤ)^d`) and on every input
molecule `X_i` outputs the periodic finite difference
`δ_{a,i} = ∇g · eᵢ + B(a + eᵢ) - B(a)`; this is the leader-automaton construction with
`h x = x mod p`.
-/

namespace Podc.ComposableCRN

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Lemma 6.1: every quilt-affine function `g : ℕ^d → ℕ` is obliviously-computable. -/
theorem lemma_6_1 (g : (ι → ℕ) → ℕ) (hg : IsQuiltAffine (fun x => (g x : ℤ))) :
    ObliviouslyComputable g := by
  obtain ⟨hmono, p, hp, grad, B, -, hform⟩ := hg
  have : NeZero p := ⟨hp.ne'⟩
  have hmono' : ∀ c i, g c ≤ g (c + Pi.single i 1) := fun c i => by
    have : c ≤ c + Pi.single i 1 := le_add_of_nonneg_right (fun _ => Nat.zero_le _)
    have := hmono this
    simp only at this
    exact_mod_cast this
  let h : (ι → ℕ) → (ι → ZMod p) := fun x i => (x i : ZMod p)
  -- the finite difference along `eᵢ` only depends on `x mod p`
  have key : ∀ c i, ((g (c + Pi.single i 1) - g c : ℕ) : ℚ) =
      grad i + B (h (c + Pi.single i 1)) - B (h c) := fun c i => by
    rw [Nat.cast_sub (hmono' c i)]
    have h1 := hform (c + Pi.single i 1)
    have h2 := hform c
    push_cast at h1 h2
    have hsum : ∑ j, grad j * ((((c + Pi.single i 1 : ι → ℕ)) j : ℕ) : ℚ) =
        ∑ j, grad j * (c j : ℚ) + grad i := by
      simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply]
    rw [h1, h2, hsum]
    ring
  have hstep : ∀ c i, h (c + Pi.single i 1) = h c + h (Pi.single i 1) := fun c i => by
    funext j; simp [h]
  refine obliviouslyComputable_of_automaton g h hmono' fun c c' hcc' i => ⟨?_, ?_⟩
  · have := key c i
    rw [hstep, hcc', ← hstep, ← key c' i] at this
    exact_mod_cast this
  · rw [hstep, hcc', ← hstep]

/-- Example of §5 (Fig. 3a): `⌊3x/2⌋ = (3/2) x + B(x mod 2)` with `B(0) = 0`, `B(1) = -1/2` is
quilt-affine, hence obliviously-computable. -/
theorem floor_three_halves_obliviouslyComputable :
    ObliviouslyComputable (fun x : Fin 1 → ℕ => 3 * x 0 / 2) := by
  refine lemma_6_1 _ ⟨fun x y h => by have : x 0 ≤ y 0 := h 0; simp only; omega, 2, two_pos,
    fun _ => 3 / 2, fun a => if a 0 = 0 then 0 else -1 / 2, fun _ => by norm_num, fun x => ?_⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    ZMod.natCast_eq_zero_iff_even]
  rcases Nat.even_or_odd (x 0) with ⟨k, hk⟩ | ⟨k, hk⟩
  · have he : Even (x 0) := ⟨k, hk⟩
    simp only [he, ↓reduceIte]
    rw [hk, show 3 * (k + k) / 2 = 3 * k by omega]
    push_cast; ring
  · have he : ¬ Even (x 0) := Nat.not_even_iff_odd.mpr ⟨k, hk⟩
    simp only [he, ↓reduceIte]
    rw [hk, show 3 * (2 * k + 1) / 2 = 3 * k + 1 by omega]
    push_cast; ring

end Podc.ComposableCRN
