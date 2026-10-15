import Mathlib
import Cslib.Computability.Distributed.Local.OnlineLocal

/-!
# Basic definitions: `a`-values on colours, proper colourings, grids

Chang–Mishra–Nguyen–Yang–Yeh, PODC 2024, §2.1 and Definition 3.1. Colours are `Fin 3 = {0,1,2}`;
our colour `2` plays the role of the paper's colour `3` (and `0, 1` of the paper's `1, 2`).
-/

namespace Papers.PODC2024.OnlineLocalGrids

open SimpleGraph

/-- **Definition 3.1** (`a`-value), on colours: `x - y` if neither colour is the special colour
`2`, else `0`. -/
def aval (x y : Fin 3) : ℤ := if x ≠ 2 ∧ y ≠ 2 then (x : ℤ) - y else 0

/-- The indicator `i(u)` of the special colour. -/
def ind (x : Fin 3) : ℤ := if x = 2 then 1 else 0

lemma aval_antisymm (x y : Fin 3) : aval y x = - aval x y := by
  unfold aval; split_ifs <;> omega

lemma abs_aval_le (x y : Fin 3) : |aval x y| ≤ 1 := by
  fin_cases x <;> fin_cases y <;> decide

/-- **Lemma 3.3** on colours: around a properly coloured 4-cycle the `a`-values cancel. -/
lemma aval_cell (x y z w : Fin 3) (h1 : x ≠ y) (h2 : y ≠ z) (h3 : z ≠ w) (h4 : w ≠ x) :
    aval x y + aval y z + aval z w + aval w x = 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;> simp_all [aval]

/-- The base case of Lemma 3.5 on colours. -/
lemma aval_parity (x y : Fin 3) (h : x ≠ y) : aval x y ≡ ind x + ind y + 1 [ZMOD 2] := by
  fin_cases x <;> fin_cases y <;> simp_all [aval, ind] <;> decide

variable {V : Type*}

/-- A colouring is proper for `G`. -/
def IsProper (G : SimpleGraph V) (c : V → Fin 3) : Prop := ∀ x y, G.Adj x y → c x ≠ c y

/-- The `a × b` (simple) grid: rows `Fin a`, columns `Fin b`; `(i, j) ~ (i', j')` iff
`|i - i'| + |j - j'| = 1`. -/
abbrev grid (a b : ℕ) : SimpleGraph (Fin a × Fin b) := pathGraph a □ pathGraph b

end Papers.PODC2024.OnlineLocalGrids
