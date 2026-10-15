import Papers.PODC2021.ThinUnison.Defs

/-!
# AlgAU has `4k - 2` states

The state space of AlgAU with parameter `k ≥ 1` consists of `2k` able turns and `2k - 2` faulty
turns: `Fintype.card (Turn k) = 4k - 2` (`= 12D + 6` for `k = 3D + 2`, i.e. `O(D)`).
-/

namespace ThinUnison

/-- The valid (level, faulty) pairs. -/
def turnSet (k : ℕ) : Finset (ℤ × Bool) :=
  ((Finset.Icc (1 : ℤ) k ∪ Finset.Icc (-(k : ℤ)) (-1)) ×ˢ {false}) ∪
    ((Finset.Icc (2 : ℤ) k ∪ Finset.Icc (-(k : ℤ)) (-2)) ×ˢ {true})

theorem mem_turnSet {k : ℕ} {p : ℤ × Bool} :
    p ∈ turnSet k ↔ IsLevel k p.1 ∧ (p.2 = true → 2 ≤ p.1 ∨ p.1 ≤ -2) := by
  obtain ⟨l, b⟩ := p
  cases b <;> simp [turnSet, IsLevel]; omega

/-- Turns are the valid pairs. -/
def turnEquiv (k : ℕ) : Turn k ≃ {p : ℤ × Bool // p ∈ turnSet k} where
  toFun ν := ⟨(ν.lvl, ν.faulty), mem_turnSet.2 ⟨ν.isLevel, ν.faulty_two⟩⟩
  invFun p := ⟨p.1.1, p.1.2, (mem_turnSet.1 p.2).1, (mem_turnSet.1 p.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (k : ℕ) : Fintype (Turn k) := Fintype.ofEquiv _ (turnEquiv k).symm

theorem card_turnSet {k : ℕ} (hk : 1 ≤ k) : (turnSet k).card = 4 * k - 2 := by
  unfold turnSet
  rw [Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
    Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · simp only [Int.card_Icc, Finset.card_singleton]; omega
  all_goals
    first
    | (rw [Finset.disjoint_left]; intro a ha hb; simp only [Finset.mem_Icc] at ha hb; omega)
    | (rw [Finset.disjoint_left]; intro a ha hb; simp only [Finset.mem_product,
        Finset.mem_singleton] at ha hb; rw [ha.2] at hb; exact Bool.false_ne_true hb.2)

/-- AlgAU with parameter `k ≥ 1` has exactly `4k - 2` states. -/
theorem card_turn {k : ℕ} (hk : 1 ≤ k) : Fintype.card (Turn k) = 4 * k - 2 := by
  rw [Fintype.card_congr (turnEquiv k), Fintype.card_coe, card_turnSet hk]

end ThinUnison
