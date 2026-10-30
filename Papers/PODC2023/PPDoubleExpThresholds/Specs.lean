import Papers.PODC2023.PPDoubleExpThresholds.Lemma8

/-!
# Specifications of the procedures (statements of Lemmas 9–12)

`Robust p` (Appendix A): for every `j`-high `C` (`1 ≤ j ≤ n`), the call of `p` terminates (no `⊥`),
and every return is `j`-high again (restarts are allowed). `RobustLt p i` is `j`-robustness for all
`j < i`.
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable (n : ℕ)

/-- `j`-robustness of `p` for all `j` satisfying `J`. -/
def RobustOn (J : ℕ → Prop) (p : Proc) : Prop :=
  ∀ j, 1 ≤ j → j ≤ n → J j → ∀ (C : Reg n → ℕ) (OF : Bool), High C j →
    (prog n).Terminates p C OF ∧
      ∀ C' OF' b, (prog n).Returns p C OF C' OF' b → OF' = OF ∧ High C' j

/-- *Robust*: `j`-robust for all `j`. -/
def Robust (p : Proc) : Prop := RobustOn n (fun _ => True) p

/-- `post(C, p) = {(C, b)}` and more generally: `p` returns exactly as described by `Q`, never
restarts and always terminates. -/
def Spec (p : Proc) (C : Reg n → ℕ) (OF : Bool) (Q : (Reg n → ℕ) → Bool → Prop) : Prop :=
  (∀ C' OF' b, (prog n).Returns p C OF C' OF' b ↔ OF' = OF ∧ Q C' b) ∧
    ¬ (prog n).Restarts p C OF ∧ (prog n).Terminates p C OF

/-- Lemma 12(b) for `Large(x)` at level `i`, `x` = register `k`. -/
def LargeB (i : ℕ) : Prop :=
  ∀ k (C : Reg n → ℕ) OF, Proper C (i - 1) → Spec n (.large i k) C OF fun C' b =>
    (b = false ∧ C' = C) ∨
      (b = true ∧ N i ≤ C (reg n i k) ∧ C' = lg C (reg n i k) (reg n i (bar k)) (N i))

/-- Lemma 10(b) for `Zero(x)` at level `i`. -/
def ZeroB (i : ℕ) : Prop :=
  ∀ k (C : Reg n → ℕ) OF, Proper C (i - 1) → N i ≤ psum C i k → Spec n (.zero i k) C OF fun C' b =>
    (b = false ∧ C' = C ∧ 0 < C (reg n i k)) ∨
      (b = true ∧ N i ≤ C (reg n i (bar k)) ∧ C' = lg C (reg n i (bar k)) (reg n i k) (N i))

/-- Lemma 10(c) for `Zero(x)` at level `i`. -/
def ZeroC (i : ℕ) : Prop :=
  ∀ k (C : Reg n → ℕ) OF C' OF', (prog n).Returns (.zero i k) C OF C' OF' false → 0 < C' (reg n i k)

/-- Lemma 9(a) for `AssertProper(i)`. -/
def APA (i : ℕ) : Prop :=
  ∀ (C : Reg n → ℕ) OF, Proper C i ∨ Low C i → Spec n (.assertProper i) C OF fun C' b =>
    C' = C ∧ b = false

/-- Lemma 9(b) for `AssertProper(i)`. -/
def APB (i : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ i → ∀ (C : Reg n → ℕ) OF, High C j → (prog n).Restarts (.assertProper i) C OF

/-- Lemma 9(c) for `AssertProper(i)`. -/
def APC (i : ℕ) : Prop :=
  ∀ (C : Reg n → ℕ) OF, Proper C (i - 1) → ∀ k ∈ ({0, 2} : Finset (Fin 4)),
    0 < C (reg n i k) ∨ N i < C (reg n i (bar k)) → (prog n).Restarts (.assertProper i) C OF

/-- Lemma 11(a) for `IncrPair(x, y)` at level `i`. -/
def IncrA (i : ℕ) : Prop :=
  ∀ bx by' (C : Reg n → ℕ) OF, WProper C i → Spec n (.incrPair i bx by') C OF fun C' b =>
    b = false ∧ WProper C' i ∧ Off C C' i ∧
      ctr C' i (kx bx) (ky by') = (ctr C i (kx bx) (ky by') + 1) % N (i + 1)

/-- Lemma 11(b) for `IncrPair(x, y)` at level `i`: reversibility. -/
def IncrB (i : ℕ) : Prop :=
  ∀ bx by' (C : Reg n → ℕ) OF C' OF' b, Geq C i →
    (prog n).Returns (.incrPair i bx by') C OF C' OF' b →
      (prog n).Returns (.incrPair i (!bx) (!by')) C' OF' C OF' false ∧ Off C C' i

/-- `IncrPair` terminates on `Geq` configurations and keeps them (the property that the proof of
Lemma 12(c) actually needs). -/
def IncrG (i : ℕ) : Prop :=
  ∀ bx by' (C : Reg n → ℕ) OF, Geq C i → (prog n).Terminates (.incrPair i bx by') C OF ∧
    ¬ (prog n).Restarts (.incrPair i bx by') C OF ∧
    ∀ C' OF' b, (prog n).Returns (.incrPair i bx by') C OF C' OF' b →
      OF' = OF ∧ b = false ∧ Geq C' i ∧ Off C C' i

end Podc.PPDoubleExpThresholds
