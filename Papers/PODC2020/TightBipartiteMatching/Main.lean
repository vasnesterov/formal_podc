import Papers.PODC2020.TightBipartiteMatching.Degenerate
import Papers.PODC2020.TightBipartiteMatching.Bridge
import Papers.PODC2020.TightBipartiteMatching.UpperBound

/-!
# Main results

Brandt–Olivetti, *Truly Tight-in-Δ Bounds for Bipartite Maximal Matching and Variants*,
PODC 2020 (arXiv 2002.08216).

* `theorem_4_5_PN`: the lower bound for genuine (CSLib) port-numbering algorithms: for every
  `t < T_Δ(x, y)` and every `t`-round algorithm there is a port numbering of the infinite
  2-coloured `Δ`-regular tree on which it fails.
* `theorem_1_2`: bipartite `x`-maximal `y`-matching has white complexity exactly `T_Δ(x, y)`
  (`1 ≤ y ≤ Δ - 1`, `0 ≤ x ≤ Δ`), both in the view model and for CSLib algorithms.
-/

namespace TightBipartiteMatching

open Cslib.PortNumbering

variable {d : ℕ}

/-- **Theorem 4.5** for genuine message-passing algorithms in the port-numbering model: for
`Δ = d + 1`, `0 ≤ x ≤ Δ`, `1 ≤ y ≤ Δ - 1` and every `t < T_Δ(x, y)`, every `t`-round algorithm
(input: the colour) fails to solve bipartite `x`-maximal `y`-matching `Φ^W_Δ(x, y)` on some port
numbering of the infinite 2-coloured `Δ`-regular tree. -/
theorem theorem_4_5_PN {x y : ℕ} (hy : 1 ≤ y) (hy' : y ≤ d) (hx : x ≤ d + 1) {t : ℕ}
    (ht : t < Tval (d + 1) x y) (A : Algorithm Bool (ℕ → Lab)) :
    ∃ arr c, ¬ SolvesOn d A t (treeGraph d arr) (treeCol d c) (Phi d x y).W (Phi d x y).B := by
  by_contra h
  push_neg at h
  exact theorem_4_5 hy hy' hx ht (solves_of_solvesOn_trees A t _ _ h)

/-- **Theorem 1.2** (deterministic, port-numbering model, 2-coloured `Δ`-regular trees): for
`Δ = d + 1`, `0 ≤ x ≤ Δ` and `1 ≤ y ≤ Δ - 1`, bipartite `x`-maximal `y`-matching has white
round complexity exactly `T_Δ(x, y)`:
1. a CSLib algorithm solves it in `T_Δ(x, y)` rounds on every `Δ`-regular properly 2-coloured
   port-numbered graph (in particular on all port numberings of the tree), and hence also in the
   view model;
2. no algorithm solves it in fewer rounds, in the view model and for CSLib algorithms. -/
theorem theorem_1_2 {x y : ℕ} (hy : 1 ≤ y) (hy' : y ≤ d) (hx : x ≤ d + 1) :
    (∃ A : Algorithm Bool (ℕ → Lab), ∀ (V : Type) (G : PNGraph V) (col : V → Bool),
      (∀ v, G.deg v = d + 1) → (∀ v (i : ℕ), i < d + 1 → col (G.nbr v i) = !col v) →
      SolvesOn d A (Tval (d + 1) x y) G col (Phi d x y).W (Phi d x y).B) ∧
    (Phi d x y).WhiteIn d (Tval (d + 1) x y) ∧
    (∀ t < Tval (d + 1) x y, ¬ (Phi d x y).WhiteIn d t) ∧
    (∀ t < Tval (d + 1) x y, ∀ A : Algorithm Bool (ℕ → Lab),
      ∃ arr c, ¬ SolvesOn d A t (treeGraph d arr) (treeCol d c) (Phi d x y).W (Phi d x y).B) := by
  obtain ⟨A, hA⟩ := upper_bound (d := d) hy hy' hx
  have hA' : ∀ (V : Type) (G : PNGraph V) (col : V → Bool), (∀ v, G.deg v = d + 1) →
      (∀ v (i : ℕ), i < d + 1 → col (G.nbr v i) = !col v) →
      SolvesOn d A (Tval (d + 1) x y) G col (Phi d x y).W (Phi d x y).B :=
    fun V G col hG hcol => hA G col hG hcol
  exact ⟨⟨A, hA'⟩, solves_of_solvesOn_all A _ _ _ hA', fun t ht => theorem_4_5 hy hy' hx ht,
    fun t ht A => theorem_4_5_PN hy hy' hx ht A⟩

end TightBipartiteMatching
