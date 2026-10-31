import Mathlib

/-!
# The Cayley tree of the free group

The universal cover of a PO-graph with `k` edge colours is a subtree of the Cayley graph of the free
group `F_k = FreeGroup (Fin k)` (the infinite `2k`-regular `k`-edge-coloured PO-tree `T` of
Section 5.3). Here: letters (`ltr`), the word length `FreeGroup.norm` as the distance to `1`, the
unique parent, balls, and the "shadow" lemma used in the propagation argument of Lemma 7.
-/

namespace Podc.LinearInDeltaLB

open FreeGroup

/-- The free group on `k` generators. -/
abbrev FG (k : ℕ) := FreeGroup (Fin k)

variable {k : ℕ}

/-- The group element of a letter: `(c, true)` is the generator `c`, `(c, false)` its inverse. -/
def ltr (l : Fin k × Bool) : FG k := FreeGroup.mk [l]

/-- The inverse letter. -/
def linv (l : Fin k × Bool) : Fin k × Bool := (l.1, !l.2)

@[simp] theorem linv_linv (l : Fin k × Bool) : linv (linv l) = l := by
  simp [linv]

theorem linv_ne (l : Fin k × Bool) : linv l ≠ l := by
  rcases l with ⟨a, b⟩; cases b <;> simp [linv]

@[simp] theorem ltr_inv (l : Fin k × Bool) : (ltr l)⁻¹ = ltr (linv l) := by
  simp [ltr, linv, FreeGroup.inv_mk, FreeGroup.invRev]

@[simp] theorem ltr_mul_ltr_linv (l : Fin k × Bool) : ltr l * ltr (linv l) = 1 := by
  rw [← ltr_inv, mul_inv_cancel]

@[simp] theorem ltr_linv_mul_ltr (l : Fin k × Bool) : ltr (linv l) * ltr l = 1 := by
  rw [← ltr_inv, inv_mul_cancel]

@[simp] theorem mul_ltr_mul_ltr_linv (w : FG k) (l : Fin k × Bool) :
    w * ltr l * ltr (linv l) = w := by
  rw [mul_assoc, ltr_mul_ltr_linv, mul_one]

theorem toWord_ltr (l : Fin k × Bool) : (ltr l).toWord = [l] := by
  simp [ltr, FreeGroup.toWord_mk, FreeGroup.reduce]

theorem ltr_injective : Function.Injective (ltr : Fin k × Bool → FG k) := by
  intro a b h
  have := congrArg FreeGroup.toWord h
  simpa [toWord_ltr] using this

theorem mul_ltr_injective (w : FG k) : Function.Injective (fun l => w * ltr l) := by
  intro a b h
  exact ltr_injective (mul_left_cancel h)

@[simp] theorem norm_ltr (l : Fin k × Bool) : norm (ltr l) = 1 := by
  simp [FreeGroup.norm, toWord_ltr]

theorem ltr_ne_one (l : Fin k × Bool) : ltr l ≠ 1 := by
  intro h; have := norm_ltr l; rw [h] at this; simp at this

theorem mul_ltr_ne_self (w : FG k) (l : Fin k × Bool) : w * ltr l ≠ w := by
  intro h; exact ltr_ne_one l (by simpa using h)

theorem toWord_mul_ltr (w : FG k) (l : Fin k × Bool) :
    (w * ltr l).toWord =
      if w.toWord.getLast? = some (linv l) then w.toWord.dropLast else w.toWord.concat l := by
  rcases l with ⟨a, b⟩
  exact FreeGroup.toWord_mul_mk_eq a b w

theorem norm_mul_ltr (w : FG k) (l : Fin k × Bool) :
    norm (w * ltr l) = if w.toWord.getLast? = some (linv l) then norm w - 1 else norm w + 1 := by
  unfold FreeGroup.norm
  rw [toWord_mul_ltr]
  split_ifs <;> simp

theorem norm_mul_ltr_lt_iff (w : FG k) (l : Fin k × Bool) :
    norm (w * ltr l) < norm w ↔ w.toWord.getLast? = some (linv l) := by
  rw [norm_mul_ltr]
  split_ifs with h
  · simp only [h, iff_true]
    have : w.toWord ≠ [] := by intro h'; simp [h'] at h
    have : 0 < norm w := by
      unfold FreeGroup.norm; exact List.length_pos_of_ne_nil this
    omega
  · simp [h]

theorem norm_mul_ltr_le (w : FG k) (l : Fin k × Bool) : norm (w * ltr l) ≤ norm w + 1 := by
  rw [norm_mul_ltr]; split_ifs <;> omega

theorem le_norm_mul_ltr (w : FG k) (l : Fin k × Bool) : norm w ≤ norm (w * ltr l) + 1 := by
  rw [norm_mul_ltr]; split_ifs <;> omega

theorem norm_mul_ltr_of_not_lt {w : FG k} {l : Fin k × Bool} (h : ¬ norm (w * ltr l) < norm w) :
    norm (w * ltr l) = norm w + 1 := by
  rw [norm_mul_ltr_lt_iff] at h
  rw [norm_mul_ltr]; simp [h]

/-- The parent of a node is unique. -/
theorem eq_of_norm_mul_ltr_lt {w : FG k} {l l' : Fin k × Bool} (h : norm (w * ltr l) < norm w)
    (h' : norm (w * ltr l') < norm w) : l = l' := by
  rw [norm_mul_ltr_lt_iff] at h h'
  rw [h] at h'
  have := Option.some.inj h'
  rw [← linv_linv l, this, linv_linv]

theorem norm_mul_ltr_linv_lt {w : FG k} {l : Fin k × Bool} (h : ¬ norm (w * ltr l) < norm w) :
    norm (w * ltr l * ltr (linv l)) < norm (w * ltr l) := by
  rw [mul_ltr_mul_ltr_linv, norm_mul_ltr_of_not_lt h]; omega

/-- If the product `a * w` has no cancellation, it ends with the last letter of `w`. -/
theorem toWord_mul_of_norm_eq {a w : FG k} (h : norm (a * w) = norm a + norm w) :
    (a * w).toWord = a.toWord ++ w.toWord := by
  apply (FreeGroup.toWord_mul_sublist a w).eq_of_length
  simpa [FreeGroup.norm] using h

/-- The "shadow" lemma: if `a * w` has no cancellation and `w ≠ 1` grows by the letter `l`, then
so does `a * w`. -/
theorem norm_mul_mul_ltr {a w : FG k} {l : Fin k × Bool} (h : norm (a * w) = norm a + norm w)
    (hw : w ≠ 1) (hl : ¬ norm (w * ltr l) < norm w) :
    norm (a * w * ltr l) = norm (a * w) + 1 := by
  apply norm_mul_ltr_of_not_lt
  rw [norm_mul_ltr_lt_iff] at hl ⊢
  rw [toWord_mul_of_norm_eq h, List.getLast?_append]
  have : w.toWord ≠ [] := by rwa [Ne, FreeGroup.toWord_eq_nil_iff]
  rw [List.getLast?_eq_some_getLast this] at hl ⊢
  simpa using hl

theorem norm_mul_mul_ltr_eq {a w : FG k} {l : Fin k × Bool} (h : norm (a * w) = norm a + norm w)
    (hw : w ≠ 1) (hl : ¬ norm (w * ltr l) < norm w) :
    norm (a * (w * ltr l)) = norm a + norm (w * ltr l) := by
  rw [← mul_assoc, norm_mul_mul_ltr h hw hl, norm_mul_ltr_of_not_lt hl, h]; ring

/-! ### Balls -/

/-- The ball of radius `R` around `1`. -/
def ballF (k R : ℕ) : Set (FG k) := {w | norm w ≤ R}

theorem ballF_finite (R : ℕ) : (ballF k R).Finite := by
  have : {L : List (Fin k × Bool) | L.length ≤ R}.Finite := List.finite_length_le _ R
  refine (this.preimage (FreeGroup.toWord_injective.injOn)).subset ?_
  intro w hw; exact hw

theorem mem_ballF {R : ℕ} {w : FG k} : w ∈ ballF k R ↔ norm w ≤ R := Iff.rfl

theorem norm_mul_le' (a b : FG k) : norm (a * b) ≤ norm a + norm b := FreeGroup.norm_mul_le a b

end Podc.LinearInDeltaLB
