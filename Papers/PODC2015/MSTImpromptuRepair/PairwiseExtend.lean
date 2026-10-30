import Papers.PODC2015.MSTImpromptuRepair.Isolation
import Papers.PODC2015.MSTImpromptuRepair.Prob

/-!
# Extending a pairwise independent family to a larger domain

If `h₀ : Ω₀ → U → ℕ` is pairwise independent into `[r]` on the keys `W`, then giving every key
outside `W` an independent uniform value yields a family on `Ω₀ × (U → Fin r)` that is pairwise
independent on *all* keys (`IsPairwiseIndep.extend`). This lets a family with a prescribed
behaviour on a few keys (the counterexample of `FindAnyCounterexample.lean`) be used as a hash
function on the whole range `[1, maxEdgeNum]`. -- CSLib candidate (together with `IsPairwiseIndep`)
-/

namespace Podc.MSTImpromptuRepair

open Finset Cslib.Probability

variable {U : Type*} [Fintype U] [DecidableEq U] {r : ℕ}

theorem uprob_fin_val_eq {a : ℕ} (ha : a < r) :
    uprob (fun c : Fin r => (c : ℕ) = a) = 1 / r := by
  classical
  rw [uprob_eq_card_filter, Fintype.card_fin]
  have : (univ.filter fun c : Fin r => (c : ℕ) = a) = {⟨a, ha⟩} := by
    ext c; simp [Fin.ext_iff]
  rw [this, card_singleton]; simp

/-- A uniform random function `g : U → Fin r` takes the value `a` at `x` with probability `1/r`. -/
theorem uprob_fun_eq (x : U) {a : ℕ} (ha : a < r) :
    uprob (fun g : U → Fin r => (g x : ℕ) = a) = 1 / r := by
  have e : (fun g : U → Fin r => (g x : ℕ) = a) =
      fun g : U → Fin r => ∀ i, (fun i (c : Fin r) => i = x → (c : ℕ) = a) i (g i) := by
    funext g; apply propext; constructor
    · intro h i hi; subst hi; exact h
    · intro h; exact h x rfl
  rw [e]
  refine (uprob_pi (α := fun _ : U => Fin r) (fun i (c : Fin r) => i = x → (c : ℕ) = a)).trans ?_
  rw [Fintype.prod_eq_single x]
  · simpa using uprob_fin_val_eq ha
  · intro i hi
    have : (fun c : Fin r => i = x → (c : ℕ) = a) = fun _ => True := by
      funext c; simp [hi]
    rw [this, uprob_true]; simp; omega

/-- Two different values of a uniform random function are independent. -/
theorem uprob_fun_eq_eq {x y : U} (hxy : x ≠ y) {a b : ℕ} (ha : a < r) (hb : b < r) :
    uprob (fun g : U → Fin r => (g x : ℕ) = a ∧ (g y : ℕ) = b) = 1 / r * (1 / r) := by
  have e : (fun g : U → Fin r => (g x : ℕ) = a ∧ (g y : ℕ) = b) =
      fun g : U → Fin r => ∀ i, (fun i (c : Fin r) => (i = x → (c : ℕ) = a) ∧
        (i = y → (c : ℕ) = b)) i (g i) := by
    funext g; apply propext; constructor
    · rintro ⟨h1, h2⟩ i; exact ⟨fun hi => hi ▸ h1, fun hi => hi ▸ h2⟩
    · intro h; exact ⟨(h x).1 rfl, (h y).2 rfl⟩
  rw [e]
  refine (uprob_pi (α := fun _ : U => Fin r) (fun i (c : Fin r) => (i = x → (c : ℕ) = a) ∧
    (i = y → (c : ℕ) = b))).trans ?_
  rw [Fintype.prod_eq_mul x y hxy]
  · congr 1
    · have : (fun c : Fin r => (x = x → (c : ℕ) = a) ∧ (x = y → (c : ℕ) = b)) =
          fun c : Fin r => (c : ℕ) = a := by funext c; simp [hxy]
      rw [this, uprob_fin_val_eq ha]
    · have : (fun c : Fin r => (y = x → (c : ℕ) = a) ∧ (y = y → (c : ℕ) = b)) =
          fun c : Fin r => (c : ℕ) = b := by funext c; simp [Ne.symm hxy]
      rw [this, uprob_fin_val_eq hb]
  · rintro i ⟨hix, hiy⟩
    have : (fun c : Fin r => (i = x → (c : ℕ) = a) ∧ (i = y → (c : ℕ) = b)) = fun _ => True := by
      funext c; simp [hix, hiy]
    rw [this, uprob_true]; simp; omega

variable {Ω₀ : Type*} [Fintype Ω₀] [Nonempty Ω₀]

/-- The extension of `h₀` (pairwise independent on `W`) by independent uniform values outside
`W`. -/
def extendHash (W : Finset U) (h₀ : Ω₀ → U → ℕ) (ω : Ω₀ × (U → Fin r)) (x : U) : ℕ :=
  if x ∈ W then h₀ ω.1 x else ω.2 x

/-- **Extension lemma.** `extendHash W h₀` is pairwise independent on all keys. -/
theorem IsPairwiseIndep.extend {W : Finset U} {h₀ : Ω₀ → U → ℕ} (hr : 0 < r)
    (hp : IsPairwiseIndep r W h₀) : IsPairwiseIndep r univ (extendHash (r := r) W h₀) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have single : ∀ x ∈ W, ∀ a < r, uprob (fun ω => h₀ ω x = a) = 1 / r := fun x hx a ha =>
    (card_mul_eq_iff_uprob_eq _ hr).1 (hp.1 x hx a ha)
  have pair : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∀ a < r, ∀ b < r,
      uprob (fun ω => h₀ ω x = a ∧ h₀ ω y = b) = 1 / r * (1 / r) := by
    intro x hx y hy hxy a ha b hb
    have := hp.2 x hx y hy hxy a ha b hb
    have h := (card_mul_eq_iff_uprob_eq (fun ω => h₀ ω x = a ∧ h₀ ω y = b)
      (Nat.mul_pos hr hr)).1 this
    rw [h]; push_cast; ring
  have hT0 : uprob (fun _ : Ω₀ => True) = 1 := by rw [uprob_true]; simp [Fintype.card_ne_zero]
  have hT1 : uprob (fun _ : U → Fin r => True) = 1 := by
    rw [uprob_true]; simp [Fintype.card_ne_zero]; omega
  constructor
  · intro x _ a ha
    rw [card_mul_eq_iff_uprob_eq _ hr]
    by_cases hx : x ∈ W
    · have e : (fun ω : Ω₀ × (U → Fin r) => extendHash W h₀ ω x = a) =
          fun ω => h₀ ω.1 x = a ∧ (fun _ : U → Fin r => True) ω.2 := by
        funext ω; simp [extendHash, hx]
      rw [e, uprob_prod_and (fun ω₀ => h₀ ω₀ x = a) (fun _ => True), single x hx a ha, hT1, mul_one]
    · have e : (fun ω : Ω₀ × (U → Fin r) => extendHash W h₀ ω x = a) =
          fun ω => (fun _ : Ω₀ => True) ω.1 ∧ ((ω.2 x : ℕ) = a) := by
        funext ω; simp [extendHash, hx]
      rw [e, uprob_prod_and (fun _ => True) (fun g : U → Fin r => (g x : ℕ) = a), uprob_fun_eq x ha, hT0,
        one_mul]
  · intro x _ y _ hxy a ha b hb
    rw [card_mul_eq_iff_uprob_eq _ (Nat.mul_pos hr hr)]
    push_cast
    rw [one_div_mul_one_div] at *
    by_cases hx : x ∈ W <;> by_cases hy : y ∈ W
    · have e : (fun ω : Ω₀ × (U → Fin r) => extendHash W h₀ ω x = a ∧ extendHash W h₀ ω y = b) =
          fun ω => (h₀ ω.1 x = a ∧ h₀ ω.1 y = b) ∧ (fun _ : U → Fin r => True) ω.2 := by
        funext ω; simp [extendHash, hx, hy]
      rw [e, uprob_prod_and (fun ω₀ => h₀ ω₀ x = a ∧ h₀ ω₀ y = b) (fun _ => True),
        pair x hx y hy hxy a ha b hb, hT1]; ring
    · have e : (fun ω : Ω₀ × (U → Fin r) => extendHash W h₀ ω x = a ∧ extendHash W h₀ ω y = b) =
          fun ω => h₀ ω.1 x = a ∧ ((ω.2 y : ℕ) = b) := by
        funext ω; simp [extendHash, hx, hy]
      rw [e, uprob_prod_and (fun ω₀ => h₀ ω₀ x = a) (fun g : U → Fin r => (g y : ℕ) = b),
        single x hx a ha, uprob_fun_eq y hb]; ring
    · have e : (fun ω : Ω₀ × (U → Fin r) => extendHash W h₀ ω x = a ∧ extendHash W h₀ ω y = b) =
          fun ω => h₀ ω.1 y = b ∧ ((ω.2 x : ℕ) = a) := by
        funext ω; simp [extendHash, hx, hy, and_comm]
      rw [e, uprob_prod_and (fun ω₀ => h₀ ω₀ y = b) (fun g : U → Fin r => (g x : ℕ) = a),
        single y hy b hb, uprob_fun_eq x ha]; ring
    · have e : (fun ω : Ω₀ × (U → Fin r) => extendHash W h₀ ω x = a ∧ extendHash W h₀ ω y = b) =
          fun ω => (fun _ : Ω₀ => True) ω.1 ∧ ((ω.2 x : ℕ) = a ∧ (ω.2 y : ℕ) = b) := by
        funext ω; simp [extendHash, hx, hy]
      rw [e, uprob_prod_and (fun _ => True)
        (fun g : U → Fin r => (g x : ℕ) = a ∧ (g y : ℕ) = b), uprob_fun_eq_eq hxy ha hb, hT0]; ring

end Podc.MSTImpromptuRepair
