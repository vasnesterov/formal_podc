import Papers.PODC2019.HardnessOptimization.HamPathGraph

/-!
# A concrete wheel assignment

For `k = 2 ^ (L + 1)` (`L + 1` bits), line `q` of box `c` has `k` positions. Position `d < k / 2`
holds the `A`-row, position `d ≥ k / 2` the `B`-row (of layer `layer c`) whose index is obtained by
inserting the bit `q` at position `bit c` into the `L`-bit string `bitsEquiv (d mod k/2)`.
So, as in the paper, the first half of every line consists of the `A`-rows whose bit `bit c` is
`q` and the second half of the corresponding `B`-rows; inside a half we use the order given by
`bitsEquiv` instead of the paper's "increasing index" order (irrelevant for the proofs).
-/

namespace HardnessOptimization.HamPath

open HV

/-- `L`-bit strings enumerated by `[2 ^ L]`. -/
def bitsEquiv (L : ℕ) : Fin (2 ^ L) ≃ Idx L :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv)

/-- The concrete wheel assignment for `L + 1` bits. -/
def hamWheel (L : ℕ) : Wheel (L + 1) := fun c q d =>
  (decide (2 ^ L ≤ d.val),
    Fin.insertNth (α := fun _ => Bool) (bit c) q
      (bitsEquiv L ⟨d.val % 2 ^ L, Nat.mod_lt _ (Nat.two_pow_pos L)⟩))

variable {L : ℕ}

lemma hamWheel_side (c q d) : (hamWheel L c q d).1 = decide (2 ^ L ≤ d.val) := rfl

lemma hamWheel_bit (c q d) : (hamWheel L c q d).2 (bit c) = q := by
  simp [hamWheel]

lemma hamWheel_inj (c q) : Function.Injective (hamWheel L c q) := by
  intro d d' h
  simp only [hamWheel, Prod.mk.injEq, decide_eq_decide] at h
  obtain ⟨h1, h2⟩ := h
  rw [Fin.insertNth_eq_iff] at h2
  obtain ⟨-, h2⟩ := h2
  have h3 : bitsEquiv L ⟨d.val % 2 ^ L, Nat.mod_lt _ (Nat.two_pow_pos L)⟩ =
      bitsEquiv L ⟨d'.val % 2 ^ L, Nat.mod_lt _ (Nat.two_pow_pos L)⟩ := by
    rw [h2]; funext j; simp [Fin.removeNth]
  have h4 := congrArg Fin.val ((bitsEquiv L).injective h3)
  simp only at h4
  have hd : d.val < 2 * 2 ^ L := by have := d.isLt; have e := pow_succ 2 L; omega
  have hd' : d'.val < 2 * 2 ^ L := by have := d'.isLt; have e := pow_succ 2 L; omega
  have e1 := Nat.div_add_mod d.val (2 ^ L)
  have e2 := Nat.div_add_mod d'.val (2 ^ L)
  have hM := Nat.two_pow_pos L
  have q1 : d.val / 2 ^ L < 2 := (Nat.div_lt_iff_lt_mul hM).2 hd
  have q2 : d'.val / 2 ^ L < 2 := (Nat.div_lt_iff_lt_mul hM).2 hd'
  have m1 := Nat.mod_lt d.val hM
  have m2 := Nat.mod_lt d'.val hM
  ext
  have hq1 : d.val / 2 ^ L = 0 ∨ d.val / 2 ^ L = 1 := by
    generalize d.val / 2 ^ L = t at q1; omega
  have hq2 : d'.val / 2 ^ L = 0 ∨ d'.val / 2 ^ L = 1 := by
    generalize d'.val / 2 ^ L = t at q2; omega
  rcases hq1 with h5 | h5 <;> rcases hq2 with h6 | h6 <;>
    (rw [h5] at e1; rw [h6] at e2; simp at e1 e2; omega)

lemma hamWheel_surj (c q s) (i : Idx (L + 1)) (hi : i (bit c) = q) :
    ∃ d, hamWheel L c q d = (s, i) := by
  have hM := Nat.two_pow_pos L
  let m := (bitsEquiv L).symm (Fin.removeNth (bit c) i)
  refine ⟨⟨s.toNat * 2 ^ L + m.val, ?_⟩, ?_⟩
  · have := m.isLt; have e := pow_succ 2 L; cases s <;> simp <;> omega
  · have hmod : (s.toNat * 2 ^ L + m.val) % 2 ^ L = m.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt m.isLt]
    simp only [hamWheel, Prod.mk.injEq]
    constructor
    · have := m.isLt; cases s <;> simp
    · rw [Fin.insertNth_eq_iff]
      refine ⟨hi.symm, ?_⟩
      have : (⟨(s.toNat * 2 ^ L + m.val) % 2 ^ L, Nat.mod_lt _ hM⟩ : Fin (2 ^ L)) = m :=
        Fin.ext hmod
      rw [this]
      simp [m]

end HardnessOptimization.HamPath
