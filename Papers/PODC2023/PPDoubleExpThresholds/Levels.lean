import Papers.PODC2023.PPDoubleExpThresholds.Construction
import Mathlib.Tactic.FinCases

/-!
# Types of configurations (Appendix A, "Definitions")

For `C ∈ ℕ^Q` and a level `i`:
* `Proper C i` (*i-proper*): `C(xⱼ) = C(yⱼ) = 0`, `C(x̄ⱼ) = C(ȳⱼ) = Nⱼ` for `j ≤ i`;
* `WProper C i` (*weakly i-proper*): `(i−1)`-proper and `C(x) + C(x̄) = Nᵢ` for `x ∈ {xᵢ, yᵢ}`;
* `Low C i` (*i-low*): `(i−1)`-proper, not `i`-proper, `C(x) = 0` and `C(x̄) ≤ Nᵢ`;
* `High C i` (*i-high*): `(i−1)`-proper, not `i`-proper, `C(x) + C(x̄) ≥ Nᵢ`;
* `Empty C i` (*i-empty*): all registers of levels `i, …, n + 1` are empty.

We also use `Geq C i`: `(i−1)`-proper and `C(x) + C(x̄) ≥ Nᵢ` (this is the hypothesis of
Lemmas 10(b), 11(b)); `Geq = High ∪ Proper` at level `i`.

Register `k` of level `i` is `reg n i k` (`k = 0, 1, 2, 3` for `x, x̄, y, ȳ`).
-/

namespace Podc.PPDoubleExpThresholds

variable {n : ℕ}

/-- The level of a register (`R` has level `n + 1`). -/
def Reg.lvl : Reg n → ℕ
  | .r i _ => i.1 + 1
  | .R => n + 1

/-- The index of a register within its level. -/
def Reg.idx : Reg n → Fin 4
  | .r _ k => k
  | .R => 0

theorem reg_of_le {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : Fin 4) :
    reg n i k = .r ⟨i - 1, by omega⟩ k := by
  simp [reg, show i - 1 < n by omega]

@[simp] theorem lvl_reg {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : Fin 4) : (reg n i k).lvl = i := by
  rw [reg_of_le hi hin]; simp [Reg.lvl]; omega

@[simp] theorem idx_reg {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : Fin 4) : (reg n i k).idx = k := by
  rw [reg_of_le hi hin]; rfl

theorem reg_inj {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) {k l : Fin 4} :
    reg n i k = reg n j l ↔ i = j ∧ k = l := by
  rw [reg_of_le hi hin, reg_of_le hj hjn]
  simp only [Reg.r.injEq, Fin.mk.injEq]
  omega

theorem reg_ne_R {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : Fin 4) : reg n i k ≠ .R := by
  rw [reg_of_le hi hin]; simp

/-- Every register is `R` or some `reg n i k` with `1 ≤ i ≤ n`. -/
theorem Reg.eq_reg (z : Reg n) : z = .R ∨ ∃ i k, 1 ≤ i ∧ i ≤ n ∧ z = reg n i k := by
  cases z with
  | R => exact .inl rfl
  | r i k => exact .inr ⟨i.1 + 1, k, by omega, i.2, by rw [reg_of_le (by omega) i.2]; simp⟩

@[simp] theorem bar_bar (k : Fin 4) : bar (bar k) = k := by fin_cases k <;> rfl

@[simp] theorem bar_ne (k : Fin 4) : bar k ≠ k := by fin_cases k <;> decide

@[simp] theorem ne_bar (k : Fin 4) : k ≠ bar k := fun h => bar_ne k h.symm

theorem reg_ne_bar {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : Fin 4) : reg n i k ≠ reg n i (bar k) := by
  rw [Ne, reg_inj hi hin hi hin]; simp

/-- `{k, bar k}` is `{0, 1}` or `{2, 3}`. -/
theorem pair_cases (k : Fin 4) : (k = 0 ∧ bar k = 1) ∨ (k = 1 ∧ bar k = 0) ∨ (k = 2 ∧ bar k = 3) ∨
    (k = 3 ∧ bar k = 2) := by fin_cases k <;> simp [bar]

variable (C : Reg n → ℕ)

/-- `C(x) + C(x̄)` for the pair `{k, bar k}` of level `i`. -/
def psum (i : ℕ) (k : Fin 4) : ℕ := C (reg n i k) + C (reg n i (bar k))

theorem psum_bar (i : ℕ) (k : Fin 4) : psum C i (bar k) = psum C i k := by
  simp [psum, add_comm]

/-- *i-proper*. -/
def Proper (i : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ i → C (reg n j 0) = 0 ∧ C (reg n j 1) = N j ∧ C (reg n j 2) = 0 ∧
    C (reg n j 3) = N j

/-- *Weakly i-proper*. -/
def WProper (i : ℕ) : Prop := Proper C (i - 1) ∧ psum C i 0 = N i ∧ psum C i 2 = N i

/-- *i-low*. -/
def Low (i : ℕ) : Prop :=
  Proper C (i - 1) ∧ ¬ Proper C i ∧ C (reg n i 0) = 0 ∧ C (reg n i 2) = 0 ∧
    C (reg n i 1) ≤ N i ∧ C (reg n i 3) ≤ N i

/-- *i-high*. -/
def High (i : ℕ) : Prop := Proper C (i - 1) ∧ ¬ Proper C i ∧ N i ≤ psum C i 0 ∧ N i ≤ psum C i 2

/-- *i-empty*. -/
def Empty (i : ℕ) : Prop := (∀ j, i ≤ j → j ≤ n → ∀ k, C (reg n j k) = 0) ∧ C .R = 0

/-- `(i − 1)`-proper with pair sums at least `Nᵢ` on level `i`. -/
def Geq (i : ℕ) : Prop := Proper C (i - 1) ∧ N i ≤ psum C i 0 ∧ N i ≤ psum C i 2

/-- The effect of `Large(x)` when it returns `true`: `N` units of `x` are moved to `x̄`, then
`x` and `x̄` are swapped. -/
def lg (x xb : Reg n) (m : ℕ) : Reg n → ℕ :=
  Function.update (Function.update C x (C xb + m)) xb (C x - m)

/-- The two-digit counter `ctr_{x,y}(C) = C(x)·(Nᵢ + 1) + C(y)` used by `IncrPair`. -/
def ctr (i : ℕ) (kx ky : Fin 4) : ℕ := C (reg n i kx) * (N i + 1) + C (reg n i ky)

/-- `C'` agrees with `C` outside level `i`. -/
def Off (C' : Reg n → ℕ) (i : ℕ) : Prop := ∀ z : Reg n, z.lvl ≠ i → C' z = C z

end Podc.PPDoubleExpThresholds
