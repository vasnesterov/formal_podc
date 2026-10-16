import Papers.PODC2010.EdgeDominatingSets.Basic

/-!
# Theorem 3: a `(4 - 2/d)`-approximation in `d`-regular graphs in one round

The algorithm outputs all edges connected to a port with port number 1 (here: port `0`). One
communication round suffices: each node tells each neighbour whether the connecting port is its
port `0`.
-/

namespace Podc.EdgeDominatingSets

open Cslib.PortNumbering Finset

/-- The local rule of the algorithm of Theorem 3: select port `i` iff `i = 0` or the neighbour's
port at the other end is `0`. -/
def rule3 : ℕ → ℕ → Set ℕ → (ℕ → Option (Set ℕ × ℕ)) → Set ℕ :=
  fun _ d _ m => {i | i < d ∧ (i = 0 ∨ ∃ s, m i = some (s, 0))}

/-- The algorithm of Theorem 3 (running time one round). -/
def alg3 : Algorithm Unit (Set ℕ) :=
  (Algorithm.ofFun fun _ _ => (∅ : Set ℕ)).seq 0 (Algorithm.ofLocal rule3)

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem alg3_eval (G : PNGraph V) (v : V) :
    alg3.eval G 1 (fun _ => ()) v = {i | i < G.deg v ∧ (i = 0 ∨ G.rport v i = 0)} := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, alg3, Algorithm.eval_seq, Algorithm.eval_ofLocal,
    Algorithm.localRun_succ]
  ext i
  simp only [rule3, Algorithm.nbrInfo, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hi, h | ⟨s, hs⟩⟩
    · exact ⟨hi, Or.inl h⟩
    · simp only [hi, ↓reduceIte] at hs
      exact ⟨hi, Or.inr (Prod.ext_iff.1 (Option.some_injective _ hs)).2⟩
  · rintro ⟨hi, h | h⟩
    · exact ⟨hi, Or.inl h⟩
    · exact ⟨hi, Or.inr ⟨_, by simp only [hi, ↓reduceIte, h]; rfl⟩⟩

/-- **Theorem 3.** In every simple `d`-regular port-numbered graph (`d ≥ 1`), the one-round
algorithm `alg3` finds a factor-`(4 - 2/d)` approximation of a minimum edge dominating set. -/
theorem theorem_3 {d : ℕ} (hd : 0 < d) (G : PNGraph V) (hG : G.IsSimple)
    (hreg : ∀ v, G.deg v = d) : Approximates alg3 1 G (4 - 2 / d) := by
  classical
  have hX := alg3_eval G
  unfold Approximates
  generalize alg3.eval G 1 (fun _ => ()) = X at hX ⊢
  -- the selected edges are exactly the port-0 edges
  have hsub : outEdges G X ⊆ univ.image fun v => G.edge v 0 := by
    intro e he
    obtain ⟨v, i, hi, hiX, rfl⟩ := mem_outEdges.1 he
    rw [hX] at hiX
    rcases hiX.2 with rfl | h0
    · exact mem_image.2 ⟨v, mem_univ _, rfl⟩
    · exact mem_image.2 ⟨G.nbr v i, mem_univ _, by rw [← h0, G.edge_nbr hi]⟩
  have h0 : ∀ v, 0 < G.deg v := fun v => hreg v ▸ hd
  refine ⟨?_, ?_, ?_⟩
  · intro v i hi hiX
    rw [hX] at hiX ⊢
    refine ⟨G.rport_lt hi, ?_⟩
    rcases hiX.2 with rfl | h
    · exact Or.inr (G.rport_rport hi)
    · exact Or.inl h
  · refine isEDS_of_cover (outEdges_subset_edgeSet hG X) Set.univ (fun v _ => ?_)
      (fun u _ _ => Or.inl trivial)
    exact ⟨G.edge v 0, edge_mem_outEdges (h0 v) (by rw [hX]; exact ⟨h0 v, Or.inl rfl⟩),
      Sym2.mem_mk_left _ _⟩
  · have hcard : (outEdges G X).card ≤ Fintype.card V :=
      (card_le_card hsub).trans (card_image_le.trans (by simp))
    have hsum := sum_deg_add_le hG (d := d) (fun v => (hreg v).le)
    simp only [hreg, sum_const, card_univ, smul_eq_mul] at hsum
    set γ := edgeDomNum G.toSimpleGraph
    have key : d * (outEdges G X).card + 2 * γ ≤ 4 * d * γ := by nlinarith
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have keyR : (d : ℝ) * (outEdges G X).card + 2 * γ ≤ 4 * d * γ := by exact_mod_cast key
    rw [show (4 - 2 / (d : ℝ)) * γ = (4 * d * γ - 2 * γ) / d by field_simp, le_div_iff₀ hdR]
    linarith

end Podc.EdgeDominatingSets
