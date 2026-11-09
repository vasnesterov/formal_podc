import Papers.PODC2020.SelfStabHighDynamics.Section3
import Papers.PODC2020.SelfStabHighDynamics.Unbounded
import Papers.PODC2020.SelfStabHighDynamics.Counterexamples
import Papers.PODC2020.SelfStabHighDynamics.Remark3
import Papers.PODC2020.SelfStabHighDynamics.Alg1Closure
import Papers.PODC2020.SelfStabHighDynamics.Alg2.Main
import Papers.PODC2020.SelfStabHighDynamics.Alg3.Main

/-!
# Altisen, Devismes, Durand, Johnen, Petit — Self-stabilizing Systems in Spite of High Dynamics

PODC 2020 (brief announcement); full version Theoretical Computer Science 2023 (HAL hal-04109662).
See `README.md` for the list of results and where they are proved.
-/

namespace Podc.SelfStabHighDynamics

open StabilizingLEDynamic (JssQ)

variable {ι : Type*} [LinearOrder ι]

/-- Non-vacuity of the hypothesis `Invariant` of Theorem 2 / Corollary 2: Algorithm 2 satisfies
it, so Corollary 2 applies to Algorithm 2. -/
theorem alg2_invariant (Δ : ℕ) : Invariant (Alg2.alg (ι := ι) Δ) (JssQ Δ) :=
  fun _ _ hG _ hγ t => Alg2.cfg_invariant hG.1 hγ t

example (Δ : ℕ) {V : Finset ι} (hV : V.Nonempty) :
    ∃ L, IsLegit (Alg2.alg Δ) (JssQ Δ) (spLE (Alg2.alg Δ)) V L ∧ Closed (Alg2.alg Δ) (JssQ Δ) V L :=
  corollary_2 (alg2_invariant Δ) Alg2.theorem_5 hV

/-- Non-vacuity of `SizeOnly` (Theorem 6, Lemma 13): the three algorithms of the paper satisfy
it, so Corollaries 8 and 9 apply to Algorithms 2 and 3. -/
theorem alg1_sizeOnly (Δ : ℕ) (hΔ : 0 < Δ) : SizeOnly (Alg1.alg (ι := ι) Δ hΔ) :=
  fun _ _ _ _ _ _ => rfl

theorem alg2_sizeOnly (Δ : ℕ) : SizeOnly (Alg2.alg (ι := ι) Δ) :=
  fun _ _ h _ _ _ => by simp only [Alg2.alg, h]

theorem alg3_sizeOnly : SizeOnly (Alg3.alg (ι := ι)) :=
  fun _ _ h _ _ _ => by simp only [Alg3.alg, h]

end Podc.SelfStabHighDynamics
