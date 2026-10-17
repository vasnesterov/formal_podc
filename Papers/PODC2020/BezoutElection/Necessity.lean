import Papers.PODC2020.BezoutElection.LowerBound

/-!
# Necessity parts of Corollaries 1–3

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Section 6. The "necessary" directions of the three
corollaries follow from Theorem 1 (`theorem_1_1`, `theorem_1_2`); they hold for read-modify-write
registers with atomic snapshots, hence a fortiori for read/write registers.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

variable {Id V S : Type} {m : ℕ} [MulAction (Equiv.Perm Id) V] [MulAction (Equiv.Perm Id) S]
  {A : SymAlg (elecObj Bool) Id m V S} {P : Type} [Fintype P] [DecidableEq P]

/-- **Corollary 1, necessity**: a symmetric (terminating) leader election algorithm for `n`
processes on `m` anonymous registers exists only if `gcd(m, n) = 1`. -/
theorem corollary_1_necessity (hA : A.Symmetric) (ids : P → Id) (hid : Function.Injective ids)
    (h : ∀ π, Terminates (A.impl ids π) ∧ DElection 1 (A.impl ids π)) :
    Nat.gcd m (Fintype.card P) = 1 := by
  obtain ⟨π, α, hval, h1, hret, c, hc⟩ := exists_elected_mul hA ids hid (fun π => (h π).1)
  have := (h π).2 α hval h1 hret
  rw [hc] at this
  obtain ⟨h₁, h₂⟩ := this
  have hc0 : c ≠ 0 := by rintro rfl; simp at h₁
  have hg0 : Nat.gcd m (Fintype.card P) ≠ 0 := by rintro h0; simp [h0] at h₁
  have : Nat.gcd m (Fintype.card P) ≤ 1 :=
    le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hc0)) h₂
  omega

/-- **Corollary 2, necessity**: `gcd(m, n) ≤ d` is necessary for symmetric `d`-election. -/
theorem corollary_2_necessity (hA : A.Symmetric) (ids : P → Id) (hid : Function.Injective ids)
    (d : ℕ) (h : ∀ π, Terminates (A.impl ids π) ∧ DElection d (A.impl ids π)) :
    Nat.gcd m (Fintype.card P) ≤ d :=
  theorem_1_1 hA ids hid d h

/-- **Corollary 3, necessity**: `gcd(m, n) ∣ d` is necessary for symmetric exact `d`-election. -/
theorem corollary_3_necessity (hA : A.Symmetric) (ids : P → Id) (hid : Function.Injective ids)
    (d : ℕ) (h : ∀ π, Terminates (A.impl ids π) ∧ ExactElection d (A.impl ids π)) :
    Nat.gcd m (Fintype.card P) ∣ d :=
  theorem_1_2 hA ids hid d h

end BezoutElection
