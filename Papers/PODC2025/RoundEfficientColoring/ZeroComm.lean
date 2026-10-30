import Papers.PODC2025.RoundEfficientColoring.Model
import Podc.Foundations.Combinatorics.SimpleGraph.EdgeColoring.Vizing

/-!
# Theorem 3: `2Δ`-edge colouring without communication

Chang–Mishra–Nguyen–Salim, PODC 2025, Theorem 3. Each party, on its own, defers a maximal set of
edges joining two vertices of (current) degree `Δ` — these form a matching whose endpoints have
all their `Δ` edges in that party's graph — colours them with one colour of the other party's
palette, and colours the rest with its own palette of `Δ` colours by Fournier's theorem.

The deferral is the sequential procedure of the paper ("each party sequentially identifies edges
connecting two vertices of degree `Δ`"), where *degree* is the current degree in the remaining
graph; with the static reading (all edges between two vertices of degree `Δ` at once) the claim
"colours them using any color from the other party's palette" fails (e.g. a triangle held by Alice
with `Δ = 2`), see `differencies.md`.
-/

namespace Podc.RoundEfficientColoring

open SimpleGraph

variable {V : Type*} [Finite V]

/-- What one party computes locally in Theorem 3: the remaining graph `R ≤ X` with a proper
`Δ`-edge colouring `col`; the deferred edges `X \ R` form a matching and their endpoints have
degree `Δ` in `X`. -/
lemma exists_zeroCommPlan {Δ : ℕ} {X : SimpleGraph V} (hX : ∀ v, (X.neighborSet v).ncard ≤ Δ) :
    ∃ R : SimpleGraph V, ∃ col : Sym2 V → ℕ, R ≤ X ∧ R.IsProperEdgeColoring col Δ ∧
      (∀ v, ((X \ R).neighborSet v).ncard ≤ 1) ∧
      ∀ ⦃u v : V⦄, (X \ R).Adj u v → (X.neighborSet u).ncard = Δ := by
  obtain ⟨R, hRX, hterm, hinv⟩ := exists_deferral X Δ
  obtain ⟨col, hcol⟩ := exists_isProperEdgeColoring_of_ncard_le R Δ
    (fun v => (ncard_neighborSet_le_of_le hRX v).trans (hX v)) hterm
  refine ⟨R, col, hRX, hcol, fun v => ?_, fun u v huv => ?_⟩
  · rw [ncard_neighborSet_sdiff hRX]
    by_cases h : (R.neighborSet v).ncard < (X.neighborSet v).ncard
    · have := hinv v h; have := hX v; omega
    · omega
  · have hpos : 0 < ((X \ R).neighborSet u).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.mpr ⟨v, huv⟩
    rw [ncard_neighborSet_sdiff hRX] at hpos
    have := hinv u (by omega); have := hX u; omega

open Classical in
/-- The output of a party in the zero-communication protocol of Theorem 3: own palette
`[o, o + Δ)`, the deferred matching gets the colour `o'` (a colour of the other party's palette).
-/
noncomputable def zeroCommColor (Δ o o' : ℕ) (X : SimpleGraph V) : Sym2 V → ℕ :=
  if h : ∀ v, (X.neighborSet v).ncard ≤ Δ then
    fun e => if e ∈ (exists_zeroCommPlan h).choose.edgeSet then
      o + (exists_zeroCommPlan h).choose_spec.choose e else o'
  else fun _ => 0

/-- The key properties of a party's output in Theorem 3. -/
lemma zeroCommColor_spec {Δ : ℕ} (o o' : ℕ) {X : SimpleGraph V}
    (hX : ∀ v, (X.neighborSet v).ncard ≤ Δ) :
    ∃ R ≤ X, ∃ col : Sym2 V → ℕ, R.IsProperEdgeColoring col Δ ∧
      (∀ v, ((X \ R).neighborSet v).ncard ≤ 1) ∧
      (∀ ⦃u v : V⦄, (X \ R).Adj u v → (X.neighborSet u).ncard = Δ) ∧
      (∀ ⦃u v : V⦄, R.Adj u v → zeroCommColor Δ o o' X s(u, v) = o + col s(u, v)) ∧
      (∀ ⦃u v : V⦄, (X \ R).Adj u v → zeroCommColor Δ o o' X s(u, v) = o') := by
  obtain ⟨hRX, hcol, h1, h2⟩ := (exists_zeroCommPlan hX).choose_spec.choose_spec
  refine ⟨_, hRX, _, hcol, h1, h2, fun u v huv => ?_, fun u v huv => ?_⟩
  · simp only [zeroCommColor, dite_eq_left hX]
    rw [ite_eq_left ((mem_edgeSet _).mpr huv)]
  · simp only [zeroCommColor, dite_eq_left hX]
    rw [ite_eq_right (fun h => ((sdiff_adj _ _ _ _).mp huv).2 ((mem_edgeSet _).mp h))]

/-- One party's output is a proper colouring of its edges, provided the deferral colour `o'`
is outside the own palette `[o, o + Δ)` and `< k`. -/
lemma zeroCommColor_proper {Δ k o o' : ℕ} {X : SimpleGraph V}
    (hX : ∀ v, (X.neighborSet v).ncard ≤ Δ) (hk : o + Δ ≤ k) (ho' : o' < k)
    (hoo : o' < o ∨ o + Δ ≤ o') : X.IsProperEdgeColoring (zeroCommColor Δ o o' X) k := by
  obtain ⟨R, hRX, col, hcol, h1, h2, hR, hD⟩ := zeroCommColor_spec o o' hX
  have hcases : ∀ ⦃u v⦄, X.Adj u v → R.Adj u v ∨ (X \ R).Adj u v := fun u v h => by
    by_cases hr : R.Adj u v
    · exact Or.inl hr
    · exact Or.inr ((sdiff_adj _ _ _ _).mpr ⟨h, hr⟩)
  refine ⟨fun u v huv => ?_, fun u v w huv huw he => ?_⟩
  · rcases hcases huv with h | h
    · rw [hR h]; have := hcol.1 h; omega
    · rw [hD h]; exact ho'
  · rcases hcases huv with h | h <;> rcases hcases huw with h' | h'
    · rw [hR h, hR h'] at he; exact hcol.2 h h' (by omega)
    · rw [hR h, hD h'] at he; have := hcol.1 h; omega
    · rw [hD h, hR h'] at he; have := hcol.1 h'; omega
    · -- two deferred edges at `u`: the deferred graph is a matching
      by_contra hvw
      have : ({v, w} : Set V) ⊆ (X \ R).neighborSet u := by
        intro x hx; rcases hx with rfl | rfl
        · exact h
        · exact h'
      have := (Set.ncard_le_ncard this (Set.toFinite _)).trans (h1 u)
      rw [Set.ncard_pair hvw] at this
      omega

/-- **Theorem 3** of [CMNS25]: there is a deterministic protocol for `(2Δ)`-edge colouring
without communication. `fA` (Alice's output as a function of her edge set alone) and `fB`
(Bob's) together properly colour every input graph of maximum degree `≤ Δ` with `2Δ` colours. -/
theorem theorem_3 (Δ : ℕ) :
    ∃ fA fB : SimpleGraph V → Sym2 V → ℕ, ∀ A B : SimpleGraph V, ValidInput Δ A B →
      SolvesEdgeColoring (2 * Δ) A B (fA A) (fB B) := by
  refine ⟨zeroCommColor Δ 0 Δ, zeroCommColor Δ Δ 0, fun A B ⟨hAB, hdeg⟩ => ?_⟩
  have hA : ∀ v, (A.neighborSet v).ncard ≤ Δ := fun v => by
    have := hdeg v; rw [ncard_neighborSet_sup hAB] at this; omega
  have hB : ∀ v, (B.neighborSet v).ncard ≤ Δ := fun v => by
    have := hdeg v; rw [ncard_neighborSet_sup hAB] at this; omega
  -- an edge forces `Δ ≥ 1`
  have hΔA : ∀ ⦃u v⦄, A.Adj u v → 0 < Δ := fun u v h =>
    ((Set.ncard_pos (Set.toFinite _)).mpr ⟨v, h⟩).trans_le (hA u)
  have hΔB : ∀ ⦃u v⦄, B.Adj u v → 0 < Δ := fun u v h =>
    ((Set.ncard_pos (Set.toFinite _)).mpr ⟨v, h⟩).trans_le (hB u)
  -- the bound `o' < k` is only needed in the presence of edges; handle `Δ = 0` separately
  rcases Nat.eq_zero_or_pos Δ with hΔ | hΔ
  · subst hΔ
    refine ⟨fun u v h => ?_, fun u v w h => ?_⟩ <;>
    · rcases h with h | h
      · exact absurd (hΔA h) (by omega)
      · exact absurd (hΔB h) (by omega)
  refine solvesEdgeColoring_of hAB
    (zeroCommColor_proper hA (by omega) (by omega) (Or.inr (by omega)))
    (zeroCommColor_proper hB (by omega) (by omega) (Or.inl (by omega))) ?_
  intro v w w' hvw hvw'
  obtain ⟨RA, hRA, colA, hcolA, -, hA2, hAR, -⟩ := zeroCommColor_spec 0 Δ hA
  obtain ⟨RB, hRB, colB, hcolB, -, hB2, hBR, -⟩ := zeroCommColor_spec Δ 0 hB
  -- a vertex of degree `Δ` in one party's graph has no edge in the other's
  have hfullA : ∀ ⦃x y⦄, (A \ RA).Adj x y → ∀ z, ¬ B.Adj x z := fun x y h z hz => by
    have := hdeg x
    rw [ncard_neighborSet_sup hAB, hA2 h] at this
    have h0 : 0 < (B.neighborSet x).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨z, hz⟩
    omega
  have hfullB : ∀ ⦃x y⦄, (B \ RB).Adj x y → ∀ z, ¬ A.Adj x z := fun x y h z hz => by
    have := hdeg x
    rw [ncard_neighborSet_sup hAB, hB2 h] at this
    have h0 : 0 < (A.neighborSet x).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨z, hz⟩
    omega
  have hRA' : RA.Adj v w := by
    by_contra h; exact hfullA ((sdiff_adj _ _ _ _).mpr ⟨hvw, h⟩) w' hvw'
  have hRB' : RB.Adj v w' := by
    by_contra h; exact hfullB ((sdiff_adj _ _ _ _).mpr ⟨hvw', h⟩) w hvw
  rw [hAR hRA', hBR hRB']
  have := hcolA.1 hRA'
  omega

end Podc.RoundEfficientColoring
