import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Order.Interval.Finset.Defs

/-!
# Binary words, shifts and superpositions (Section 2.1 of the paper)

Dufoulon, Burman, Beauquier. *Can Uncoordinated Beeps tell Stories?* PODC 2020.

A binary word of length `n` is a function `Fin n → Bool`; our position `i : Fin n` is the paper's
position `i + 1` (the paper indexes from `1`). For proofs we embed words into `ℤ`-indexed words
(`Word.getZ`), where a word sits at positions `0, …, n - 1` and is `0` elsewhere.

* `shift x t` is the paper's *shifted word* `σ(x, t)` (length `|x|`):
  `σ(x,t)[i] = x[i - t]` if `i - t ∈ {1, …, |x|}` and `0` otherwise.
* `extShift x t` is the *extended shifted word* `σ̄(x, t) = 0^{|x|-1+t} x 0^{|x|-1-t}`
  (length `3|x| - 2`).
* `superpose X f` is the bitwise OR of the words `f a`, `a ∈ X`; applied to shifted words it is the
  paper's (extended) uncoordinated superposition.
* `y.Contains x` (`y` *contains* / *covers* `x`): every `1` of `x` is a `1` of `y`.
-/

namespace Podc.UncoordinatedBeeps

/-- A finite binary word of length `n`. Position `i : Fin n` is the paper's position `i + 1`. -/
abbrev Word (n : ℕ) := Fin n → Bool

namespace Word

variable {n : ℕ}

/-- The bit of `x` at integer position `j` (0-based), `false` outside `{0, …, n - 1}`. -/
def getZ (x : Word n) (j : ℤ) : Bool :=
  if h : 0 ≤ j ∧ j < n then x ⟨j.toNat, by omega⟩ else false

/-- `y` contains (covers) `x`: `x[i] = 1 → y[i] = 1` for all positions `i`. -/
def Contains (y x : Word n) : Prop := ∀ i, x i = true → y i = true

theorem getZ_eq_true {x : Word n} {j : ℤ} :
    x.getZ j = true ↔ ∃ h : 0 ≤ j ∧ j < n, x ⟨j.toNat, by omega⟩ = true := by
  unfold getZ; split_ifs with h <;> simp [h]

theorem getZ_eq_true_bounds {x : Word n} {j : ℤ} (h : x.getZ j = true) : 0 ≤ j ∧ j < n := by
  obtain ⟨h, -⟩ := getZ_eq_true.1 h; exact h

@[simp] theorem getZ_natCast (x : Word n) (i : Fin n) : x.getZ (i : ℕ) = x i := by
  simp [getZ]

end Word

open Word

/-- The paper's *shifted word* `σ(x, t)`: `x` moved `t` positions to the right, truncated to the
window `{1, …, |x|}` (missing bits are `0`). -/
def shift {l : ℕ} (x : Word l) (t : ℤ) : Word l := fun i => x.getZ ((i : ℕ) - t)

/-- The paper's *extended shifted word* `σ̄(x, t) = 0^{|x|-1+t} x 0^{|x|-1-t}`, of length `3|x| - 2`
(for shifts `t ∈ {-|x|+1, …, |x|-1}`). -/
def extShift {l : ℕ} (x : Word l) (t : ℤ) : Word (3 * l - 2) :=
  fun j => x.getZ ((j : ℕ) - ((l : ℤ) - 1 + t))

/-- The bitwise OR superposition of the words `f a`, `a ∈ X`. -/
def superpose {ι : Type*} {n : ℕ} (X : Finset ι) (f : ι → Word n) : Word n :=
  fun i => decide (∃ a ∈ X, f a i = true)

theorem superpose_eq_true {ι : Type*} {n : ℕ} {X : Finset ι} {f : ι → Word n} {i : Fin n} :
    superpose X f i = true ↔ ∃ a ∈ X, f a i = true := by
  simp [superpose]

/-- Admissible shifts: `t ∈ {-l + 1, …, l - 1}`. -/
def InShiftRange (l : ℕ) (t : ℤ) : Prop := -(l : ℤ) + 1 ≤ t ∧ t ≤ (l : ℤ) - 1

/-- `σ(x, 0) = x`. -/
@[simp] theorem shift_zero {l : ℕ} (x : Word l) : shift x 0 = x := by
  funext i; simp [shift]

end Podc.UncoordinatedBeeps
