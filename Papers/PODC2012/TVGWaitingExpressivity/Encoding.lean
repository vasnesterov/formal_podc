import Papers.PODC2012.TVGWaitingExpressivity.Basic
import Mathlib.Tactic.Linarith

/-!
# The base-`b` encoding `φ` of words (Section 3)

For a word `w = a₀ … a_k` over `Fin q`, the paper sets `φ(w) = q^{k+1} + Σ_j a_j q^{k-j}`, the
integer written `1.w` in base `q`, with the convention `φ(ε) = 0`. We allow any base `b ≥ 2` with
`q ≤ b`; the paper's encoding is `b = q`, which needs `q ≥ 2` (for `q = 1` it is not injective).
-/

namespace Podc.TVGWaitingExpressivity

variable {q : ℕ} (b : ℕ)

/-- The value of the base-`b` numeral `1.w`. -/
def numeral (w : List (Fin q)) : ℕ := w.foldl (fun n a => b * n + a) 1

/-- The encoding `φ`: `φ(ε) = 0` and `φ(w) = 1.w` read in base `b` otherwise. -/
def phi (w : List (Fin q)) : ℕ := if w = [] then 0 else numeral b w

/-- `φ⁻¹`, defined on the image of `φ` (junk value `ε` elsewhere). -/
noncomputable def phiInv (t : ℕ) : List (Fin q) :=
  open Classical in if h : ∃ w, phi (q := q) b w = t then h.choose else []

variable {b}

@[simp] theorem numeral_nil : numeral (q := q) b [] = 1 := rfl

theorem numeral_append_singleton (w : List (Fin q)) (a : Fin q) :
    numeral b (w ++ [a]) = b * numeral b w + a := by
  simp [numeral, List.foldl_append]

theorem numeral_pos (hb : 1 ≤ b) (w : List (Fin q)) : 1 ≤ numeral b w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rw [numeral_append_singleton]
    nlinarith

theorem numeral_injective (hb : 2 ≤ b) (hq : q ≤ b) :
    Function.Injective (numeral (q := q) b) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro w' h
    induction w' using List.reverseRecOn with
    | nil => rfl
    | append_singleton w' a _ =>
      rw [numeral_append_singleton, numeral_nil] at h
      have := numeral_pos (by omega) w' (b := b)
      nlinarith
  | append_singleton w a ih =>
    intro w' h
    induction w' using List.reverseRecOn with
    | nil =>
      rw [numeral_append_singleton, numeral_nil] at h
      have := numeral_pos (by omega) w (b := b)
      nlinarith
    | append_singleton w' a' _ =>
      rw [numeral_append_singleton, numeral_append_singleton] at h
      have ha : (a : ℕ) < b := lt_of_lt_of_le a.2 hq
      have ha' : (a' : ℕ) < b := lt_of_lt_of_le a'.2 hq
      have h1 : (a : ℕ) = a' := by
        have := congrArg (· % b) h
        simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
        exact this
      have h2 : numeral b w = numeral b w' := by
        have := congrArg (· / b) h
        rwa [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt ha,
          Nat.div_eq_of_lt ha', Nat.add_zero, Nat.add_zero] at this
      rw [ih h2, Fin.ext h1]

@[simp] theorem phi_nil : phi (q := q) b [] = 0 := rfl

theorem phi_of_ne_nil {w : List (Fin q)} (hw : w ≠ []) : phi b w = numeral b w := by simp [phi, hw]

theorem phi_injective (hb : 2 ≤ b) (hq : q ≤ b) : Function.Injective (phi (q := q) b) := by
  intro w w' h
  by_cases hw : w = [] <;> by_cases hw' : w' = []
  · rw [hw, hw']
  · rw [hw, phi_nil, phi_of_ne_nil hw'] at h
    have := numeral_pos (by omega) w' (b := b); omega
  · rw [hw', phi_nil, phi_of_ne_nil hw] at h
    have := numeral_pos (by omega) w (b := b); omega
  · rw [phi_of_ne_nil hw, phi_of_ne_nil hw'] at h
    exact numeral_injective hb hq h

theorem phiInv_phi (hb : 2 ≤ b) (hq : q ≤ b) (w : List (Fin q)) : phiInv b (phi b w) = w := by
  have h : ∃ w', phi (q := q) b w' = phi b w := ⟨w, rfl⟩
  simp only [phiInv, h, dite_true]
  exact phi_injective hb hq h.choose_spec

/-- `φ` strictly increases when a letter is appended. -/
theorem phi_lt_phi_append (hb : 2 ≤ b) (w : List (Fin q)) (a : Fin q) :
    phi b w < phi b (w ++ [a]) := by
  rw [phi_of_ne_nil (by simp : w ++ [a] ≠ []), numeral_append_singleton]
  by_cases hw : w = []
  · subst hw; simp only [phi_nil, numeral_nil]; omega
  · rw [phi_of_ne_nil hw]
    have := numeral_pos (by omega) w (b := b)
    nlinarith

end Podc.TVGWaitingExpressivity
