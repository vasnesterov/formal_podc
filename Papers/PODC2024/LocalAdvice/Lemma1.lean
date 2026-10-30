import Podc.Probability.Finite.LocalLemma

/-!
# Lemma 1 (the Lovász Local Lemma) as stated in the paper

The paper states the symmetric local lemma with the condition `e·p·d ≤ 1`. For `d = 0` this is
false: a single event of probability 1 depends on no other event, `e·1·0 = 0 ≤ 1`, but it always
occurs. The standard condition `e·p·(d + 1) ≤ 1`
(`Cslib.Probability.exists_forall_not_of_symmetric`) is what the paper's application (Lemma 32)
satisfies and what we use.
-/

namespace Podc.LocalAdvice

open Cslib.Probability

/-- The symmetric Lovász Local Lemma with the paper's condition `e·p·d ≤ 1` (Lemma 1), in the
variable setting on a uniform finite product space. -/
def Lemma1AsStated : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Ω : ι → Type) [∀ i, Fintype (Ω i)]
    [∀ i, Nonempty (Ω i)] (E : Type) [Fintype E] [DecidableEq E]
    (A : E → (∀ i, Ω i) → Prop) (vbl : E → Finset ι),
    (∀ e σ τ, (∀ i ∈ vbl e, σ i = τ i) → (A e σ ↔ A e τ)) →
    ∀ (p : ℝ) (d : ℕ), (∀ e, uprob (A e) ≤ p) → (∀ e, (dependencyNbhd vbl e).card ≤ d) →
      Real.exp 1 * p * d ≤ 1 → ∃ σ : ∀ i, Ω i, ∀ e, ¬ A e σ

/-- **Lemma 1 as stated is false for `d = 0`**: one sure event (`p = 1`) with no dependencies. -/
theorem lemma_1_as_stated_false : ¬ Lemma1AsStated := by
  intro h
  obtain ⟨σ, hσ⟩ := h Unit (fun _ => Unit) Unit (fun _ _ => True) (fun _ => ∅)
    (fun _ _ _ _ => Iff.rfl) 1 0 (fun _ => uprob_le_one _)
    (fun e => by simp [dependencyNbhd]) (by simp)
  exact hσ () trivial

end Podc.LocalAdvice
