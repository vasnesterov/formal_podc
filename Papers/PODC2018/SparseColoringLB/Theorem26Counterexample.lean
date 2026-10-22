import Papers.PODC2018.SparseColoringLB.Theorem26

/-!
# Theorem 2.6 is false as stated for odd `k`

Theorem 2.6 of the paper: "No distributed algorithm can 3-colour the rectangular `k × k` grid in the
plane in less than `k/2` rounds." For odd `k = 2t + 1` this says that `t` rounds do not suffice. But
`t` rounds suffice, even for a proper **2**-colouring: in the `(2t+1) × (2t+1)` grid, the numbers of
nodes at distance `0, 1, …, t` from a node `u` (which `u` knows after `t` rounds) determine the
colour class (`(row + column) mod 2`) of `u`. This file proves it for `k = 3, 5, 7, 9, 11` by a
finite computation (`decide +kernel`); `Theorem26General.lean` proves it for every odd `k`
(`theorem_2_6_false_odd`), using only the number of nodes at distance exactly `t`.

The algorithm is a genuine `t`-round LOCAL algorithm in CSLib's sense (`Cslib.Local.IsLocal`: a node
only uses the edges at distance `< t` and nothing about identifiers), so it is also `BallLocal t`.

The lower bound that the paper's argument actually proves is `2r + 3 ≤ k` (`theorem_2_6`); for
odd `k` it is tight by the present counterexample.
-/

namespace Podc.SparseColoringLB

open SimpleGraph Cslib.Local

/-! ### Distances in the grid -/

/-- Manhattan distance in `Fin N × Fin N`. -/
def l1 {N : ℕ} (p q : Fin N × Fin N) : ℕ :=
  (max (p.1 : ℕ) q.1 - min (p.1 : ℕ) q.1) + (max (p.2 : ℕ) q.2 - min (p.2 : ℕ) q.2)

lemma grid_edist_eq {N : ℕ} (p q : Fin N × Fin N) : (grid N).edist p q = l1 p q := by
  apply le_antisymm
  · -- walk towards `q` coordinate by coordinate
    suffices h : ∀ (n : ℕ) (p : Fin N × Fin N), l1 p q = n → (grid N).edist p q ≤ n from
      h _ p rfl
    intro n
    induction n with
    | zero =>
      intro p hp
      have : p = q := by
        simp only [l1] at hp
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      simp [this]
    | succ n ih =>
      intro p hp
      obtain ⟨p', hadj, hp'⟩ : ∃ p', (grid N).Adj p p' ∧ l1 p' q = n := by
        simp only [l1] at hp
        have h1 := p.1.isLt
        have h2 := q.1.isLt
        have h3 := p.2.isLt
        have h4 := q.2.isLt
        by_cases ha : (p.1 : ℕ) < q.1
        · refine ⟨(⟨p.1 + 1, by omega⟩, p.2), ?_, ?_⟩
          · rw [grid_adj_iff']; left; exact ⟨Or.inl rfl, rfl⟩
          · simp only [l1]; omega
        by_cases hb : (q.1 : ℕ) < p.1
        · refine ⟨(⟨p.1 - 1, by omega⟩, p.2), ?_, ?_⟩
          · rw [grid_adj_iff']; left; exact ⟨Or.inr (by simp; omega), rfl⟩
          · simp only [l1]; omega
        by_cases hc : (p.2 : ℕ) < q.2
        · refine ⟨(p.1, ⟨p.2 + 1, by omega⟩), ?_, ?_⟩
          · rw [grid_adj_iff']; right; exact ⟨Or.inl rfl, rfl⟩
          · simp only [l1]; omega
        · refine ⟨(p.1, ⟨p.2 - 1, by omega⟩), ?_, ?_⟩
          · rw [grid_adj_iff']; right; exact ⟨Or.inr (by simp; omega), rfl⟩
          · simp only [l1]; omega
      calc (grid N).edist p q ≤ (grid N).edist p p' + (grid N).edist p' q :=
          (grid N).edist_triangle
        _ ≤ 1 + n := by rw [edist_eq_one_iff_adj.2 hadj]; gcongr; exact ih p' hp'
        _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring
  · have hlip : ∀ x y : Fin N × Fin N, (grid N).Adj x y → l1 p y ≤ l1 p x + 1 := by
      intro x y h
      rw [grid_adj_iff'] at h
      simp only [l1]
      rcases h with ⟨h, e⟩ | ⟨h, e⟩
      · rw [e]; omega
      · rw [e]; omega
    have := le_add_edist_of_lipschitz hlip p q
    simpa [l1] using this

/-! ### The distance profile -/

/-- Number of nodes at distance exactly `d` from `u`. -/
noncomputable def sphereCard {V : Type*} (G : SimpleGraph V) (u : V) (d : ℕ) : ℕ :=
  Nat.card {v // G.edist u v = d}

/-- The distance profile up to radius `t` is known after `t` rounds. -/
lemma sphereCard_eq_of_gAgree {V : Type*} {G G' : SimpleGraph V} {u : V} {t d : ℕ}
    (h : GAgree G G' u t) (hd : d ≤ t) : sphereCard G u d = sphereCard G' u d := by
  unfold sphereCard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  constructor
  · intro hv
    rw [h.edist_eq (by rw [hv]; exact_mod_cast hd), hv]
  · intro hv
    rw [h.symm.edist_eq (by rw [hv]; exact_mod_cast hd), hv]

/-- Computable distance profile in the grid. -/
def gridSphere {N : ℕ} (p : Fin N × Fin N) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun q => l1 p q = d).card

lemma sphereCard_grid_map {N : ℕ} {V : Type*} (e : (Fin N × Fin N) ≃ V) (p : Fin N × Fin N)
    (d : ℕ) : sphereCard ((grid N).map e.toEmbedding) (e p) d = gridSphere p d := by
  unfold sphereCard gridSphere
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine (Nat.card_congr (Equiv.subtypeEquiv e fun q => ?_)).symm
  show l1 p q = d ↔ ((grid N).map e.toEmbedding).edist (e.toEmbedding p) (e.toEmbedding q) = d
  rw [edist_map_embedding, grid_edist_eq]
  exact_mod_cast Iff.rfl

/-! ### The algorithm -/

/-- Colour class of a grid node. -/
def gridParity {N : ℕ} (p : Fin N × Fin N) : Fin 3 := if ((p.1 : ℕ) + p.2) % 2 = 0 then 0 else 1

lemma gridParity_adj {N : ℕ} {p q : Fin N × Fin N} (h : (grid N).Adj p q) :
    gridParity p ≠ gridParity q := by
  rw [grid_adj_iff'] at h
  unfold gridParity
  rcases h with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;> split_ifs <;> first | decide | omega

/-- The `t`-round algorithm: output the colour class of any grid position with the same distance
profile up to radius `t`. -/
noncomputable def profileAlg (N t : ℕ) {V : Type*} (G : SimpleGraph V) (u : V) : Fin 3 :=
  open Classical in
  if h : ∃ p : Fin N × Fin N, ∀ d ≤ t, gridSphere p d = sphereCard G u d then
    gridParity h.choose else 0

lemma profileAlg_isLocal (N t : ℕ) {V : Type*} :
    IsLocal t (fun G (_ : V → Unit) v => profileAlg N t G v) := by
  intro G x G' x' v hv
  have hs : ∀ d ≤ t, sphereCard G v d = sphereCard G' v d :=
    fun d hd => sphereCard_eq_of_gAgree hv.1 hd
  simp only [profileAlg]
  have : (fun p : Fin N × Fin N => ∀ d ≤ t, gridSphere p d = sphereCard G v d) =
      (fun p => ∀ d ≤ t, gridSphere p d = sphereCard G' v d) := by
    funext p; apply propext
    exact forall₂_congr fun d hd => by rw [hs d hd]
  simp only [this]

/-- If the distance profile up to radius `t` determines the colour class in the `N × N` grid, then
there is a `t`-round algorithm properly 2-colouring the `N × N` grid. -/
theorem grid_colours_of_profile {N t : ℕ}
    (hcheck : ∀ p p' : Fin N × Fin N, (∀ d ≤ t, gridSphere p d = gridSphere p' d) →
      gridParity p = gridParity p')
    {V : Type*} : IsLocal t (fun G (_ : V → Unit) v => profileAlg N t G v) ∧
      ColoursGraph (profileAlg N t (V := V)) (grid N) := by
  refine ⟨profileAlg_isLocal N t, fun e x y hxy => ?_⟩
  have key : ∀ p, profileAlg N t ((grid N).map e.toEmbedding) (e p) = gridParity p := by
    intro p
    have hex : ∃ p' : Fin N × Fin N, ∀ d ≤ t,
        gridSphere p' d = sphereCard ((grid N).map e.toEmbedding) (e p) d :=
      ⟨p, fun d _ => (sphereCard_grid_map e p d).symm⟩
    simp only [profileAlg, hex, dite_true]
    apply hcheck
    intro d hd
    rw [hex.choose_spec d hd, sphereCard_grid_map]
  rw [key, key]
  exact gridParity_adj hxy

/-! ### The counterexamples -/

/-- **Theorem 2.6 is false for `k = 3`**: one round (`1 < 3/2`) suffices to properly colour the
`3 × 3` grid (with 2 colours). -/
theorem theorem_2_6_false_3 {V : Type*} :
    ∃ A : SimpleGraph V → V → Fin 3, IsLocal 1 (fun G (_ : V → Unit) v => A G v) ∧
      ColoursGraph A (grid 3) :=
  ⟨_, grid_colours_of_profile (by decide +kernel)⟩

/-- **Theorem 2.6 is false for `k = 5`**: two rounds (`2 < 5/2`) suffice. -/
theorem theorem_2_6_false_5 {V : Type*} :
    ∃ A : SimpleGraph V → V → Fin 3, IsLocal 2 (fun G (_ : V → Unit) v => A G v) ∧
      ColoursGraph A (grid 5) :=
  ⟨_, grid_colours_of_profile (by decide +kernel)⟩

/-- **Theorem 2.6 is false for `k = 7`**: three rounds (`3 < 7/2`) suffice. -/
theorem theorem_2_6_false_7 {V : Type*} :
    ∃ A : SimpleGraph V → V → Fin 3, IsLocal 3 (fun G (_ : V → Unit) v => A G v) ∧
      ColoursGraph A (grid 7) :=
  ⟨_, grid_colours_of_profile (by decide +kernel)⟩

/-- **Theorem 2.6 is false for `k = 9`**: four rounds (`4 < 9/2`) suffice. -/
theorem theorem_2_6_false_9 {V : Type*} :
    ∃ A : SimpleGraph V → V → Fin 3, IsLocal 4 (fun G (_ : V → Unit) v => A G v) ∧
      ColoursGraph A (grid 9) :=
  ⟨_, grid_colours_of_profile (by decide +kernel)⟩

/-- **Theorem 2.6 is false for `k = 11`**: five rounds (`5 < 11/2`) suffice. -/
theorem theorem_2_6_false_11 {V : Type*} :
    ∃ A : SimpleGraph V → V → Fin 3, IsLocal 5 (fun G (_ : V → Unit) v => A G v) ∧
      ColoursGraph A (grid 11) :=
  ⟨_, grid_colours_of_profile (by decide +kernel)⟩

end Podc.SparseColoringLB
