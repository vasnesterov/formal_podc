import Papers.PODC2014.CongestedCliquePower.Lemma13

/-!
# Theorem 22 is false for `ℓ = 1`: stars are detected in one round

Theorem 22 of Drucker–Kuhn–Oshman (PODC 2014) states: "For any `ℓ, m ≥ 1`, `K_{ℓ,m}`-subgraph
detection in CLIQUE-BCAST_{n,b} requires `Ω(√n / b)` rounds." For `ℓ = 1` the graph `K_{1,m}` is a
star, and `G` contains `K_{1,m}` iff some node has degree `≥ m`, which every node knows locally:
one round with one-bit messages suffices (`starAlg`). Lemma 21, on which Theorem 22 rests, assumes
`ℓ, m ≥ 2`; the intended statement is evidently `ℓ, m ≥ 2`.
-/

namespace Podc.CongestedCliquePower

open SimpleGraph Cslib.CongestedClique

/-- The star `K_{1,m}`. -/
abbrev star (m : ℕ) : SimpleGraph (Fin 1 ⊕ Fin m) := completeBipartiteGraph (Fin 1) (Fin m)

/-- `G` contains `K_{1,m}` iff some vertex has degree at least `m`. -/
theorem star_isContained_iff {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) : star m ⊑ G ↔ ∃ v, m ≤ G.degree v := by
  constructor
  · rintro ⟨f⟩
    refine ⟨f (Sum.inl 0), ?_⟩
    rw [← card_neighborFinset_eq_degree]
    have hinj : Function.Injective fun j : Fin m => f (Sum.inr j) :=
      fun a b h => Sum.inr_injective (f.injective h)
    calc m = (Finset.univ.map ⟨_, hinj⟩).card := by simp
      _ ≤ _ := Finset.card_le_card fun w hw => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hw
        rw [mem_neighborFinset]
        exact f.toHom.map_adj (by simp)
  · rintro ⟨v, hv⟩
    rw [← card_neighborFinset_eq_degree] at hv
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hv
    let e : Fin m ≃ s := (s.equivFinOfCardEq hcard).symm
    let g : Fin 1 ⊕ Fin m → V := Sum.elim (fun _ => v) (fun j => (e j).1)
    have hmem : ∀ j, G.Adj v (e j).1 := fun j => (mem_neighborFinset _ _ _).1 (hs (e j).2)
    refine ⟨⟨⟨g, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
    · rcases a with a | a <;> rcases b with b | b <;> simp at hab
      · exact hmem b
      · exact (hmem a).symm
    · rcases a with a | a <;> rcases b with b | b
      · simp [Subsingleton.elim a b]
      · exact absurd hab (G.ne_of_adj (hmem b))
      · exact absurd hab.symm (G.ne_of_adj (hmem a))
      · simp only [g] at hab
        rw [e.injective (Subtype.ext hab)]

/-- The one-round CLIQUE-BCAST algorithm with one-bit messages detecting `K_{1,m}`: every node
broadcasts whether its degree is at least `m`, and accepts iff nobody did. -/
def starAlg (V : Type) [Fintype V] (m : ℕ) : Bcast.Algorithm V (V → Bool) ((V → Bool) × Bool) 1 where
  init _ r := (r, true)
  send _ s := fun _ => decide (m ≤ (Finset.univ.filter fun w => s.1 w = true).card)
  step _ s M := (s.1, decide (∀ w, M w 0 = false))
  out _ s := s.2

theorem starAlg_accepts {V : Type} [Fintype V] (m : ℕ) (G : SimpleGraph V) :
    (starAlg V m).Accepts (adjInput G) 1 ↔ (star m).Free G := by
  classical
  have hdeg : ∀ v, (Finset.univ.filter fun w => adjInput G v w = true).card = G.degree v := by
    intro v
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp [adjInput]
  rw [SimpleGraph.Free, star_isContained_iff]
  simp [Bcast.Algorithm.Accepts, Bcast.Algorithm.run, starAlg, hdeg]
  exact ⟨fun h w => h w w, fun h _ w => h w⟩

/-- **Theorem 22 is false for `ℓ = 1`.** For every constant `c > 0` there are `n`, `b = 1` and a
CLIQUE-BCAST_{n,1} algorithm detecting `K_{1,m}` in `T = 1 < c · √n / b` rounds; so no bound
`T ≥ c · √n / b` holds for `K_{1,m}`-detection (`m ≥ 1`; `K_{1,1}` is a single edge). -/
theorem theorem_22_false_of_l_eq_one (m : ℕ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ (n b T : ℕ) (σ : Type) (A : Bcast.Algorithm (Fin n) (Fin n → Bool) σ b),
      0 < b → (∀ G : SimpleGraph (Fin n), A.Accepts (adjInput G) T ↔ (star m).Free G) →
        c * Real.sqrt n / b ≤ T := by
  rintro ⟨c, hc, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / c ^ 2)
  have := h n 1 1 _ (starAlg (Fin n) m) one_pos (starAlg_accepts m)
  have hsq : 2 / c < Real.sqrt n := by
    rw [Real.lt_sqrt (by positivity)]
    calc ((2 : ℝ) / c) ^ 2 = 4 / c ^ 2 := by field_simp; norm_num
      _ < (n : ℝ) := hn
  have : c * (2 / c) < c * Real.sqrt n := mul_lt_mul_of_pos_left hsq hc
  rw [mul_div_cancel₀ _ hc.ne'] at this
  norm_num at *
  linarith

end Podc.CongestedCliquePower
