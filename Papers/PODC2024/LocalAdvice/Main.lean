import Papers.PODC2024.LocalAdvice.Theorem34
import Papers.PODC2024.LocalAdvice.Lemma32LLL

/-!
# Theorem 30: 3-colouring 3-colourable graphs with one bit of advice per node

Model: LOCAL with unique identifiers. The nodes of every graph are the elements of a fixed finite
linearly ordered type `V` (the identifiers); an `R`-round algorithm is a function
`SimpleGraph V → (V → Bool) → V → Fin 3` whose output at `u` only depends on the radius-`R` view
of `u` (CSLib `Cslib.Local.IsLocal R`); the advice is one bit per node (`V → Bool`). The algorithm
knows the degree bound `Δ`.
-/

namespace Podc.LocalAdvice

open SimpleGraph Cslib.Local

/-- **Theorem 30**, with the explicit algorithm: the decoder `A = decode Δ` of Appendix D is one
definition, uniform in the node set `V` (it does not depend on `n` or on the identifier set), runs in
`8000Δ⁹ + 3` rounds, and with suitable advice (one bit per node) outputs a proper 3-colouring of
every 3-colourable graph of maximum degree `≤ Δ`. -/
theorem theorem_30_decode {V : Type*} [Fintype V] [LinearOrder V] (Δ : ℕ) :
    IsLocal (8000 * Δ ^ 9 + 3) (decode (V := V) Δ) ∧
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (∀ v, G.degree v ≤ Δ) → G.Colorable 3 →
        ∃ b : V → Bool, ∀ u v, G.Adj u v → decode Δ G b u ≠ decode Δ G b v := by
  refine ⟨decode_isLocal, fun G _ hdeg h3 => ?_⟩
  obtain ⟨φ, hφ⟩ := exists_isGreedy G h3
  rcases Nat.eq_zero_or_pos Δ with rfl | hΔ
  · -- no edges
    refine ⟨fun _ => false, fun u v huv => absurd (hdeg u) ?_⟩
    rw [← card_neighborFinset_eq_degree, Nat.le_zero, Finset.card_eq_zero]
    exact Finset.ne_empty_of_mem (mem_neighborFinset G u v |>.2 huv)
  obtain ⟨σ⟩ := lemma_32 hφ hdeg hΔ
  exact ⟨σ.bit, (theorem_34 hφ hΔ σ).1⟩

/-- **Theorem 30** of [Balliu et al., arXiv:2405.04519]. For every `Δ` there is an algorithm `A`
running in `8000Δ⁹ + 3 = Δ^{O(1)}` rounds such that every 3-colourable graph of maximum degree
`≤ Δ` admits an assignment of one bit per node with which `A` outputs a proper 3-colouring
(a uniform fixed-length `(G, Π, 1, Δ^{O(1)})`-advice schema for 3-colouring). The node type `V` is
fixed before `A`; `theorem_30_decode` shows that the witness `decode Δ` is uniform in `V`. -/
theorem theorem_30 {V : Type*} [Fintype V] [LinearOrder V] (Δ : ℕ) :
    ∃ A : SimpleGraph V → (V → Bool) → V → Fin 3, IsLocal (8000 * Δ ^ 9 + 3) A ∧
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj], (∀ v, G.degree v ≤ Δ) → G.Colorable 3 →
        ∃ b : V → Bool, ∀ u v, G.Adj u v → A G b u ≠ A G b v :=
  ⟨decode Δ, theorem_30_decode Δ⟩

/-- The round bound of Theorem 30 is `O(Δ⁹)`. -/
lemma round_bound {Δ : ℕ} (hΔ : 1 ≤ Δ) : 8000 * Δ ^ 9 + 3 ≤ 8003 * Δ ^ 9 := by
  have := Nat.one_le_pow 9 Δ hΔ
  omega

end Podc.LocalAdvice
