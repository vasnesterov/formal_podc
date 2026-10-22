import Papers.PODC2018.SparseColoringLB.Model
import Papers.PODC2018.SparseColoringLB.Klein

/-!
# Theorem 2.5: 3-colouring the planar triangle-free graph `H_k` needs `k/2` rounds

`H_k = C₅ □ P_k` (`hGraph k`): `k` nested 5-cycles, consecutive ones joined by a perfect matching
(Figure 2, right, of the paper, where it is drawn for `k = 2ℓ = 4`). It is planar and triangle-free.

The paper derives Theorem 2.5 from Observation 2.4 with the Klein bottle grid `G_{5,2ℓ+1}`, whose
balls of radius `< ℓ` look like balls of `H_{2ℓ}`. Since `G_{5,2ℓ+1}` has *more* vertices than
`H_{2ℓ}` (`10ℓ + 5 > 10ℓ`), Observation 2.4 does not literally apply, and it would only give
`r ≤ ℓ - 2`. We use the Klein bottle grid `klein 5 k` with the *same* vertex set as `H_k`: `H_k` is
`klein 5 k` with the twisted wrap-around edges deleted, and the column shift `kshift` (an automorphism
of `klein 5 k`) moves any edge to the middle of `H_k`, where the deleted edges are invisible within
radius `r` as soon as `2r + 2 ≤ k`. This gives exactly the paper's bound `r < k/2` for even `k`.
-/

namespace Podc.SparseColoringLB

open SimpleGraph

/-- `H_k = C₅ □ P_k`: `k` nested 5-cycles (Figure 2, right; the paper's `H_{2ℓ}` is `hGraph (2ℓ)`). -/
abbrev hGraph (k : ℕ) : SimpleGraph (Fin 5 × Fin k) := cyl 5 k

/-- **Theorem 2.5 (general form).** If `2r + 2 ≤ k`, no `r`-round algorithm (in the paper's model:
the output of a node depends on its labelled ball of radius `r`; identifiers are the elements of
`V`, with `|V| = 5k`) 3-colours `H_k`. -/
theorem hGraph_not_colours {k r : ℕ} (hk : 2 * r + 2 ≤ k) {V : Type*} [Fintype V]
    (hV : Fintype.card V = 5 * k) {A : SimpleGraph V → V → Fin 3} (hA : BallLocal r A) :
    ¬ ColoursGraph A (hGraph k) := by
  have e₂ : (Fin 5 × Fin k) ≃ V := Fintype.equivOfCardEq (by simp [hV])
  refine not_colours_of_views hA (klein_not_colorable (m := 5) (by decide) (by norm_num) (by omega))
    e₂.toEmbedding fun x y hxy => ?_
  have key : ∀ p q, (klein 5 k).Adj p q → (p.2 = q.2 ∨ q = kshift p) →
      ∃ (e : (Fin 5 × Fin k) ≃ V) (x' y' : Fin 5 × Fin k), (hGraph k).Adj x' y' ∧
        e x' = e₂ p ∧ e y' = e₂ q ∧
        BallAgree ((hGraph k).map e.toEmbedding) ((klein 5 k).map e₂.toEmbedding) (e₂ p) r ∧
        BallAgree ((hGraph k).map e.toEmbedding) ((klein 5 k).map e₂.toEmbedding) (e₂ q) r := by
    intro p q hpq hcase
    obtain ⟨σ, hH, -, -, h1, h2⟩ := cyl_view hk e₂.toEmbedding hpq hcase
    exact ⟨σ.symm.trans e₂, σ p, σ q, hH, by simp, by simp, h1, h2⟩
  rcases klein_adj_cases hxy with h | h | h
  · exact key _ _ hxy (Or.inl h)
  · exact key _ _ hxy (Or.inr h)
  · obtain ⟨e, x', y', hH, h1, h2, h3, h4⟩ := key _ _ hxy.symm (Or.inr h)
    exact ⟨e, y', x', hH.symm, h2, h1, h4, h3⟩

/-- **Theorem 2.5** of the paper: no distributed algorithm can 3-colour `H_k` (`k = 2ℓ`) in less
than `k/2 = ℓ` rounds. -/
theorem theorem_2_5 {ℓ r : ℕ} (hr : r < ℓ) {V : Type*} [Fintype V]
    (hV : Fintype.card V = 5 * (2 * ℓ)) {A : SimpleGraph V → V → Fin 3} (hA : BallLocal r A) :
    ¬ ColoursGraph A (hGraph (2 * ℓ)) :=
  hGraph_not_colours (by omega) hV hA

/-- **Theorem 2.5, second sentence** ("no distributed algorithm can 3-colour every planar
triangle-free graph on `n` vertices in `o(n)` rounds"), with explicit constants: for every
`r`-round algorithm on `n ≥ 10(r + 1)` identifiers there is an `n`-node network on which it fails,
namely a copy of `H_{2(r+1)}` (planar and triangle-free) plus isolated nodes. Hence `3`-colouring
all `n`-node planar triangle-free graphs needs more than `n/10 - 1` rounds. -/
theorem theorem_2_5_family {n r : ℕ} (hn : 10 * (r + 1) ≤ n) {V : Type*} [Fintype V]
    (hV : Fintype.card V = n) {A : SimpleGraph V → V → Fin 3} (hA : BallLocal r A) :
    ∃ G : SimpleGraph V, IsCopyOf (hGraph (2 * (r + 1))) G ∧
      ∃ u v, G.Adj u v ∧ A G u = A G v := by
  by_contra hcon
  push Not at hcon
  set k := 2 * (r + 1) with hk
  obtain ⟨e₂⟩ : Nonempty ((Fin 5 × Fin k) ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  have := coloring_of_views_family hA (𝒢 := {G | IsCopyOf (hGraph k) G})
    (fun G hG u v huv => hcon G hG u v huv) e₂ (K := klein 5 k) fun x y hxy => ?_
  · exact (klein_not_colorable (m := 5) (by decide) (by norm_num) (by omega)).false this.some
  have key : ∀ p q, (klein 5 k).Adj p q → (p.2 = q.2 ∨ q = kshift p) →
      ∃ G ∈ {G | IsCopyOf (hGraph k) G}, G.Adj (e₂ p) (e₂ q) ∧
        BallAgree G ((klein 5 k).map e₂) (e₂ p) r ∧
        BallAgree G ((klein 5 k).map e₂) (e₂ q) r := by
    intro p q hpq hcase
    obtain ⟨σ, hH, -, -, h1, h2⟩ := cyl_view (k := k) (r := r) (by omega) e₂ hpq hcase
    refine ⟨_, ⟨_, rfl⟩, ?_, h1, h2⟩
    have := (map_adj_apply (f := σ.symm.toEmbedding.trans e₂)).2 hH
    simpa using this
  rcases klein_adj_cases hxy with h | h | h
  · exact key _ _ hxy (Or.inl h)
  · exact key _ _ hxy (Or.inr h)
  · obtain ⟨G, hG, hadj, h3, h4⟩ := key _ _ hxy.symm (Or.inr h)
    exact ⟨G, hG, hadj.symm, h4, h3⟩

end Podc.SparseColoringLB
