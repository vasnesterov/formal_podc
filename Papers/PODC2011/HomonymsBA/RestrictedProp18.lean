import Papers.PODC2011.HomonymsBA.RestrictedLiveness

/-!
# Proposition 18

Partially synchronous Byzantine agreement is solvable with numerate processes against restricted
Byzantine processes if `ℓ > t` (standing assumption `n > 3t`), by the algorithm of Appendix A.3
(`Restricted.alg`).
-/

namespace Podc.HomonymsBA

open Finset Restricted

/-- The algorithm `Restricted.alg` solves Byzantine agreement in the partially synchronous model
with restricted Byzantine processes when `n > 3t` and `ℓ > t`. -/
theorem Restricted.alg_solves {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : t < ℓ) (V : Type) :
    Solves .psync .restricted n t (alg n t (show 0 < ℓ by omega) V) := by
  intro P _ _ hP R hR
  have hℓ0 : 0 < ℓ := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- termination (Proposition 40)
    intro p hp
    -- an identifier held by correct processes only
    have hlt : (R.byz.image R.id).card < (univ : Finset (Fin ℓ)).card := by
      rw [card_univ, Fintype.card_fin]
      exact card_image_le.trans_lt (hR.1.card_byz.trans_lt hℓ)
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hk' : ∀ b ∈ R.byz, R.id b ≠ k := fun b hb e => hk (mem_image.2 ⟨b, hb, e⟩)
    set e := ℓ * (R.gst + 1) + k.val - 1 with he
    have hpos : 1 ≤ ℓ * (R.gst + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hlead : leader hℓ0 (e + 1) = k := by
      ext
      simp only [leader, he]
      rw [show ℓ * (R.gst + 1) + k.val - 1 + 1 = k.val + ℓ * (R.gst + 1) by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt]
    have hge : R.gst ≤ 8 * e + 6 := by
      have : R.gst + 1 ≤ ℓ * (R.gst + 1) := Nat.le_mul_of_pos_left _ hℓ0
      omega
    obtain ⟨v, hv⟩ := decides_in_phase R hn hP hR hge (hlead ▸ hk') (R.inp p) hp
    exact ⟨v, 8 * (e + 1) + 7, hv⟩
  · -- agreement (Proposition 39)
    rintro p hp q hq v w ⟨r, hr⟩ ⟨r', hr'⟩
    obtain ⟨ph, -, h⟩ := decided_spec R r p v hr
    obtain ⟨ph', -, h'⟩ := decided_spec R r' q w hr'
    exact decAt_agree R hn hP hR h h'
  · -- validity (Proposition 38)
    rintro v hv p hp w ⟨r, hr⟩
    obtain ⟨ph, -, h⟩ := decided_spec R r p w hr
    exact decAt_valid R hn hR hv h

/-- **Proposition 18** of [Delporte-Gallet et al., PODC 2011]: partially synchronous Byzantine
agreement is solvable with numerate processes against restricted Byzantine processes if `ℓ > t`
(and `n > 3t`). -/
theorem prop18 {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : t < ℓ) (V : Type) :
    Solvable .psync .restricted .numerate n ℓ t V :=
  ⟨Msg ℓ V, St ℓ V, alg n t (by omega) V, trivial, Restricted.alg_solves hn hℓ V⟩

end Podc.HomonymsBA
