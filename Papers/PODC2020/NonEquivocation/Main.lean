import Papers.PODC2020.NonEquivocation.Tightness
import Papers.PODC2020.NonEquivocation.RoundLowerBound
import Papers.PODC2020.NonEquivocation.Strong

/-!
# Main results (summary)

Madsen–Debois, *On the Subject of Non-Equivocation*, PODC 2020. The abstract's headline:
"1 round, `n > t` for strong non-equivocation; `t + 1` rounds, `n > 2t` for weak
non-equivocation". In the formalization:

* strong non-equivocation: `sne_solvesIC` (one round, every `n`, `t`) and `sne_not_solvesIC_zero`;
* weak non-equivocation: `wne_rounds_exact` (for `n > 2t ≥ 2`, exactly `t + 1` rounds) and the
  resilience threshold `icSolvable_wne_iff` (`n > 2t` **or `n ≤ 3`** — Theorem 6.1 as stated fails
  for `n ≤ 3`).
-/

namespace NonEquivocation

variable {P V : Type*} [Fintype P] [DecidableEq P] [OmitVal V]

/-- Weak non-equivocation with `n > 2t`, `t ≥ 1`: Algorithm 2 solves interactive consistency in
`t + 1` rounds (Theorem 5.1), and no algorithm does with `t` rounds or fewer (Section 6). -/
theorem wne_rounds_exact [Nontrivial V] {t : ℕ} (ht : 1 ≤ t) (hn : 2 * t < Fintype.card P) :
    SolvesIC wne (t + 1) t (alg2 (P := P) (V := V) t) ∧
      ∀ k ≤ t, ∀ A : Alg P V, ¬ SolvesIC wne k t A :=
  ⟨theorem_5_1 hn, fun _ hk A => not_solvesIC_wne_of_le hk (by omega) A⟩

end NonEquivocation
