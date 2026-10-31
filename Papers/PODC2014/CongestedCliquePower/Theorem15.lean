import Papers.PODC2014.CongestedCliquePower.Cliques
import Papers.PODC2014.CongestedCliquePower.Lemma13

/-!
# Theorem 15: `K_ℓ`-detection in CLIQUE-BCAST needs `Ω(n / b)` rounds

Drucker–Kuhn–Oshman, PODC 2014, Theorem 15: for every fixed `ℓ ≥ 4`, `K_ℓ`-subgraph detection in
CLIQUE-BCAST_{n,b} requires `Ω(n / b)` rounds. Proof: Lemma 14 with `N = ⌊(n - ℓ)/4⌋ + 1` gives a
`(K_ℓ, K_{N,N})`-lower bound graph on `n` nodes; `K_{N,N}` has `N² = Θ(n²)` edges; Lemma 13.
-/

namespace Podc.CongestedCliquePower

open SimpleGraph Cslib.CongestedClique

lemma card_edgeSet_completeBipartiteGraph (N : ℕ)
    [Fintype (completeBipartiteGraph (Fin N) (Fin N)).edgeSet] :
    Fintype.card (completeBipartiteGraph (Fin N) (Fin N)).edgeSet = N * N := by
  have h := encard_edgeSet_completeBipartiteGraph (W₁ := Fin N) (W₂ := Fin N)
  rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_card] at h
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h
  exact_mod_cast h

/-- **Theorem 15 (deterministic).** For `ℓ ≥ 4` and `n ≥ ℓ`, every deterministic CLIQUE-BCAST
algorithm on `n` nodes with `b`-bit messages that decides `K_ℓ`-freeness in `T` rounds satisfies
`N² ≤ T · n · b + 2` with `N = ⌊(n - ℓ)/4⌋ + 1`. -/
theorem theorem_15 (ℓ n : ℕ) (hℓ : 4 ≤ ℓ) (hn : ℓ ≤ n) {σ : Type} {b : ℕ}
    (A : Bcast.Algorithm (Fin n) (Fin n → Bool) σ b) (T : ℕ)
    (hA : ∀ G : SimpleGraph (Fin n), A.Accepts (adjInput G) T ↔ (⊤ : SimpleGraph (Fin ℓ)).Free G) :
    ((n - ℓ) / 4 + 1) ^ 2 ≤ T * (n * b) + 2 := by
  classical
  set N := (n - ℓ) / 4 + 1
  obtain ⟨G', ⟨L⟩⟩ := lemma_14 ℓ N n hℓ (by omega)
  have := L.lemma_13_bcast A T hA
  rw [card_edgeSet_completeBipartiteGraph, Fintype.card_fin] at this
  rw [sq]; exact this

/-- **Theorem 15**, `Ω(n / b)` form: for `n ≥ 2ℓ`, `T · b ≥ n / 64 - 2 / n`. -/
theorem theorem_15_real (ℓ n : ℕ) (hℓ : 4 ≤ ℓ) (hn : 2 * ℓ ≤ n) {σ : Type} {b : ℕ}
    (A : Bcast.Algorithm (Fin n) (Fin n → Bool) σ b) (T : ℕ)
    (hA : ∀ G : SimpleGraph (Fin n), A.Accepts (adjInput G) T ↔ (⊤ : SimpleGraph (Fin ℓ)).Free G) :
    (n : ℝ) / 64 - 2 / n ≤ T * b := by
  have h := theorem_15 ℓ n hℓ (by omega) A T hA
  have hN : n ≤ 8 * ((n - ℓ) / 4 + 1) := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : ((n : ℝ)) ^ 2 ≤ 64 * (T * (n * b) + 2) := by
    have : n ^ 2 ≤ 64 * (T * (n * b) + 2) := by
      calc n ^ 2 ≤ (8 * ((n - ℓ) / 4 + 1)) ^ 2 := Nat.pow_le_pow_left hN 2
        _ = 64 * ((n - ℓ) / 4 + 1) ^ 2 := by ring
        _ ≤ 64 * (T * (n * b) + 2) := Nat.mul_le_mul_left _ h
    exact_mod_cast this
  have e : (n : ℝ) / 64 - 2 / n = ((n : ℝ) ^ 2 - 128) / (64 * n) := by
    field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith

open Classical in
/-- **Theorem 15 (randomized).** With the randomized disjointness bound `RandDisjLB` for
`N² = ((n - ℓ)/4 + 1)²` elements as hypothesis (`C = Ω(N²)` by Razborov), every randomized
CLIQUE-BCAST algorithm deciding `K_ℓ`-freeness with error `≤ ε` in `T` rounds has
`C ≤ T · n · b + 2`. -/
theorem theorem_15_rand (ℓ n : ℕ) (hℓ : 4 ≤ ℓ) (hn : ℓ ≤ n) {σ ρ : Type} [Fintype ρ] [Nonempty ρ]
    {b : ℕ} (A : Bcast.Algorithm (Fin n) ((Fin n → Bool) × ρ) σ b) (T : ℕ) (ε : ℝ)
    (hA : ∀ G : SimpleGraph (Fin n), (A.randErr (adjInput G) T
      (by classical exact decide ((⊤ : SimpleGraph (Fin ℓ)).Free G)) : ℝ) ≤
        ε * Fintype.card (Fin n → ρ))
    (C : ℕ) (hC : LowerBoundGraph.RandDisjLB
      (completeBipartiteGraph (Fin ((n - ℓ) / 4 + 1)) (Fin ((n - ℓ) / 4 + 1))).edgeSet ε C) :
    C ≤ T * (n * b) + 2 := by
  classical
  obtain ⟨G', ⟨L⟩⟩ := lemma_14 ℓ ((n - ℓ) / 4 + 1) n hℓ (by omega)
  have := L.lemma_13_bcast_rand A T ε hA C (by convert hC)
  simpa using this

end Podc.CongestedCliquePower
