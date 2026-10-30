import Papers.PODC2019.MinimalSymmetryBreaking.Theorem6
import Papers.PODC2019.MinimalSymmetryBreaking.Subtree
import Papers.PODC2019.MinimalSymmetryBreaking.WeakColoring
import Papers.PODC2019.MinimalSymmetryBreaking.PointerProblem
import Papers.PODC2019.MinimalSymmetryBreaking.PointerUpper

/-!
# Balliu, Hirvonen, Olivetti, Suomela — Hardness of minimal symmetry breaking (PODC 2019)

Main results (see `README.md` for the model and the differences from the paper):

* Lemma 2 (`lemma_2`): distance-`k` weak `c`-colouring → weak 2-colouring in `k + 2c` rounds.
* Lemmas 7/8/14/15 (`lemma_14`, `lemma_15`, and the inequalities `speedup1_ineq`,
  `speedup2_ineq`), Claims 11/16 (`claim_16`), Claim 10 (`succProb_le`).
* Theorems 6/13 (`theorem_6`, `theorem_13`): weak 2-colouring on even-degree trees needs
  `Ω(log* n)` rounds.
* Theorem 4 (`theorem4`, from `lemma17` and `lemma18`): the pointer problem `P*` has complexity
  `Θ(log n)`; Lemma 3 with a repaired algorithm (`lemma3_repaired`).
-/

namespace Podc.MinimalSymmetryBreaking

/-- The instances of Theorem 6 exist for every `n ≥ 1`: an `n`-node subtree of the oriented
`2k`-regular tree containing the ball of radius `Kn k n`. -/
theorem theorem_6_instances (hk : 0 < k) (n : ℕ) (hn : 1 ≤ n) :
    ∃ V : Finset (Tree k), IsSubtree V ∧ Ball (Kn k n) ⊆ V ∧ V.card = n := by
  apply exists_subtree hk
  refine (card_Ball_le _).trans ?_
  refine (Nat.pow_le_pow_right (by omega) (Nat.div_le_self _ 3)).trans ?_
  exact Nat.pow_log_le_self _ (by omega)

/-- **Theorem 13** (`Δ = 4`): solving weak 2-colouring with global success probability at least
`1/2` requires `Ω(log* n)` rounds. -/
theorem theorem_13 : ∃ C N₀ : ℕ, ∀ n ≥ N₀, ∀ t : ℕ, 2 * t + C ≤ Nat.logStar n →
    ∀ [NeZero n] (Ω : Type) [Fintype Ω] [Inhabited Ω] (μ : FinDist Ω) (V : Finset (Tree 2)),
      Ball (Kn 2 n) ⊆ V → V.card = n → ∀ A : IdAlg 2 n Ω t,
        ∃ id : Tree 2 → Fin n, Set.InjOn id V ∧ A.succProb μ V id < 1 / 2 :=
  theorem_6 (by norm_num)

end Podc.MinimalSymmetryBreaking
