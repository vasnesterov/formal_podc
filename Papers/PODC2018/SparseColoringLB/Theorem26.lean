import Papers.PODC2018.SparseColoringLB.Klein

/-!
# Theorem 2.6: 3-colouring the `N × N` grid needs about `N/2` rounds

The paper derives Theorem 2.6 from Observation 2.4 with the Klein bottle grid `G_{2k+1,2k+1}`.
We prove the sharp form of this argument: if `2r + 3 ≤ N`, no `r`-round algorithm 3-colours the
`N × N` grid (`theorem_2_6`). The Klein bottle grid `klein m m` (`m` odd, `2r + 3 ≤ m ≤ N`) is not
3-colourable, and every edge of it is seen, within radius `r` from both endpoints, exactly as an edge
in the middle of the grid: shift the edge to column `r` (Klein automorphism `kshift`), delete the
twisted edges (cylinder `C_m □ P_m`), rotate the rows (cylinder automorphism) and delete the
wrap-around rows (grid `P_m □ P_m`), and finally put the `m × m` grid in a corner of the `N × N`
grid (the remaining nodes get the unused identifiers).

The paper claims more: "no distributed algorithm can 3-colour the `k × k` grid in less than `k/2`
rounds", i.e. `2r + 1 ≤ k` would suffice. This is false for every odd `k ≥ 3`: see
`Theorem26Counterexample.lean` and `Theorem26General.lean`.
-/

namespace Podc.SparseColoringLB

open SimpleGraph

/-- The `N × N` grid `P_N □ P_N` (rows, columns). -/
abbrev grid (N : ℕ) : SimpleGraph (Fin N × Fin N) := pathGraph N □ pathGraph N

lemma fin_sub_val {m : ℕ} (a b : Fin m) :
    ((a - b : Fin m) : ℕ) = if (b : ℕ) ≤ a then (a : ℕ) - b else m + (a : ℕ) - b := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.2 h
  · exact Fin.coe_sub_iff_lt.2 (lt_of_not_ge h)

section GridDist

variable {m : ℕ}

lemma grid_adj_iff' {x y : Fin m × Fin m} :
    (grid m).Adj x y ↔ (((x.1 : ℕ) + 1 = y.1 ∨ (y.1 : ℕ) + 1 = x.1) ∧ x.2 = y.2) ∨
      (((x.2 : ℕ) + 1 = y.2 ∨ (y.2 : ℕ) + 1 = x.2) ∧ x.1 = y.1) := by
  rw [boxProd_adj, pathGraph_adj, pathGraph_adj]

lemma grid_row_lip : ∀ x y : Fin m × Fin m, (grid m).Adj x y → (y.1 : ℕ) ≤ x.1 + 1 := by
  intro x y h
  rw [grid_adj_iff'] at h
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · omega
  · rw [h]; omega

lemma grid_row'_lip : ∀ x y : Fin m × Fin m, (grid m).Adj x y →
    m - 1 - (y.1 : ℕ) ≤ m - 1 - x.1 + 1 := by
  intro x y h
  rw [grid_adj_iff'] at h
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · omega
  · rw [h]; omega

lemma grid_col'_lip : ∀ x y : Fin m × Fin m, (grid m).Adj x y →
    m - 1 - (y.2 : ℕ) ≤ m - 1 - x.2 + 1 := by
  intro x y h
  rw [grid_adj_iff'] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · rw [h]; omega
  · omega

lemma grid_edist_row_zero (u a : Fin m × Fin m) (ha : (a.1 : ℕ) = 0) :
    ((u.1 : ℕ) : ℕ∞) ≤ (grid m).edist u a := by
  have := le_add_edist_of_lipschitz grid_row_lip a u
  rw [ha, edist_comm] at this
  simpa using this

lemma grid_edist_row_last (u a : Fin m × Fin m) (ha : (a.1 : ℕ) + 1 = m) :
    ((m - 1 - u.1 : ℕ) : ℕ∞) ≤ (grid m).edist u a := by
  have := le_add_edist_of_lipschitz grid_row'_lip a u
  rw [show m - 1 - (a.1 : ℕ) = 0 by omega, edist_comm] at this
  simpa using this

lemma grid_edist_col_last (u a : Fin m × Fin m) (ha : (a.2 : ℕ) + 1 = m) :
    ((m - 1 - u.2 : ℕ) : ℕ∞) ≤ (grid m).edist u a := by
  have := le_add_edist_of_lipschitz grid_col'_lip a u
  rw [show m - 1 - (a.2 : ℕ) = 0 by omega, edist_comm] at this
  simpa using this

end GridDist

lemma grid_le_cyl (m : ℕ) : grid m ≤ cyl m m := by
  intro a b h
  rcases h with ⟨h, e⟩ | ⟨h, e⟩
  · exact Or.inl ⟨pathGraph_le_cycleGraph h, e⟩
  · exact Or.inr ⟨h, e⟩

/-- Seen from a node `u` with `r ≤ row u ≤ m - 1 - r` (one inequality strict), the cylinder
`C_m □ P_m` and the grid `P_m □ P_m` have the same labelled ball of radius `r`. -/
lemma ballAgree_cyl_grid {m r : ℕ} (u : Fin m × Fin m) (h₁ : r ≤ (u.1 : ℕ))
    (h₂ : r ≤ m - 1 - (u.1 : ℕ)) (h₃ : r < (u.1 : ℕ) ∨ r < m - 1 - (u.1 : ℕ)) :
    BallAgree (cyl m m) (grid m) u r := by
  have wrap : ∀ a b, (cyl m m).Adj a b → ¬ (grid m).Adj a b →
      ((a.1 : ℕ) + 1 = m ∧ (b.1 : ℕ) = 0) ∨ ((b.1 : ℕ) + 1 = m ∧ (a.1 : ℕ) = 0) := by
    intro a b hab hn
    rcases hab with ⟨h, e⟩ | ⟨h, e⟩
    · rw [cycleGraph_adj', fin_sub_val, fin_sub_val] at h
      have hn' : ¬ ((a.1 : ℕ) + 1 = b.1 ∨ (b.1 : ℕ) + 1 = a.1) := fun h' =>
        hn (Or.inl ⟨(pathGraph_adj).2 h', e⟩)
      have := a.1.isLt
      have := b.1.isLt
      split_ifs at h <;> omega
    · exact absurd (Or.inr ⟨h, e⟩) hn
  have end0 := grid_edist_row_zero (m := m) u
  have endl := grid_edist_row_last (m := m) u
  apply ballAgree_of_le (grid_le_cyl m)
  · intro a b hab hn
    rcases wrap a b hab hn with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact le_trans (by exact_mod_cast h₂) (endl a h1)
    · exact le_trans (by exact_mod_cast h₁) (end0 a h2)
  · intro a b hab hn
    rcases wrap a b hab hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases h₃ with h | h
      · exact Or.inr (lt_of_lt_of_le (by exact_mod_cast h) (end0 b h2))
      · exact Or.inl (lt_of_lt_of_le (by exact_mod_cast h) (endl a h1))
    · rcases h₃ with h | h
      · exact Or.inl (lt_of_lt_of_le (by exact_mod_cast h) (end0 a h2))
      · exact Or.inr (lt_of_lt_of_le (by exact_mod_cast h) (endl b h1))

/-! ### The `m × m` grid in a corner of the `N × N` grid -/

/-- The `m × m` grid as the top-left corner of the `N × N` grid. -/
def gridEmb {m N : ℕ} (h : m ≤ N) : Fin m × Fin m ↪ Fin N × Fin N :=
  (Fin.castLEEmb h).prodMap (Fin.castLEEmb h)

@[simp] lemma gridEmb_apply {m N : ℕ} (h : m ≤ N) (w : Fin m × Fin m) :
    gridEmb h w = (Fin.castLE h w.1, Fin.castLE h w.2) := rfl

lemma gridEmb_adj_iff {m N : ℕ} (h : m ≤ N) {a b : Fin m × Fin m} :
    (grid N).Adj (gridEmb h a) (gridEmb h b) ↔ (grid m).Adj a b := by
  simp only [grid_adj_iff', gridEmb_apply, Fin.val_castLE, Fin.ext_iff]

lemma mem_range_gridEmb {m N : ℕ} (h : m ≤ N) (w : Fin N × Fin N) :
    w ∈ Set.range (gridEmb h) ↔ (w.1 : ℕ) < m ∧ (w.2 : ℕ) < m := by
  constructor
  · rintro ⟨a, rfl⟩; simp
  · rintro ⟨h1, h2⟩
    exact ⟨(⟨w.1, h1⟩, ⟨w.2, h2⟩), by simp⟩

/-- Seen from a node `u` of the corner `m × m` grid at distance `≥ r` from its last row and last
column, the `N × N` grid (identifiers `e`) and the corner grid (identifiers `f = e ∘ gridEmb`, the
other identifiers being isolated nodes) have the same labelled ball of radius `r`. -/
lemma ballAgree_grid_embed {m N r : ℕ} (hmN : m ≤ N) {V : Type*} (f : Fin m × Fin m ↪ V)
    (e : (Fin N × Fin N) ≃ V) (he : ∀ w, e (gridEmb hmN w) = f w) (u : Fin m × Fin m)
    (h₁ : r ≤ m - 1 - (u.1 : ℕ)) (h₂ : r ≤ m - 1 - (u.2 : ℕ)) :
    BallAgree ((grid N).map e.toEmbedding) ((grid m).map f) (f u) r := by
  -- an endpoint of a deleted edge is outside the corner, or on its last row / column
  have key : ∀ a' b' : Fin N × Fin N, (grid N).Adj a' b' →
      ¬ ((grid m).map f).Adj (e a') (e b') →
      (r : ℕ∞) ≤ ((grid m).map f).edist (f u) (e a') ∧
        (a' ∉ Set.range (gridEmb hmN) → ((grid m).map f).edist (f u) (e a') = ⊤) ∧
        (a' ∉ Set.range (gridEmb hmN) ∨ b' ∉ Set.range (gridEmb hmN)) := by
    intro a' b' hab hn
    have hout : ∀ a'', a' = gridEmb hmN a'' → b' ∉ Set.range (gridEmb hmN) := by
      rintro a'' rfl ⟨b'', rfl⟩
      rw [gridEmb_adj_iff] at hab
      exact hn (by rw [he, he]; exact (map_adj_apply (f := f)).2 hab)
    have htop : a' ∉ Set.range (gridEmb hmN) →
        ((grid m).map f).edist (f u) (e a') = ⊤ := by
      intro ha
      apply edist_map_of_notMem_range
      rintro ⟨w, hw⟩
      rw [← he] at hw
      exact ha ⟨w, e.injective hw⟩
    refine ⟨?_, htop, ?_⟩
    · by_cases ha : a' ∈ Set.range (gridEmb hmN)
      · obtain ⟨a'', rfl⟩ := ha
        have hb := hout a'' rfl
        rw [he, edist_map_embedding]
        rw [mem_range_gridEmb] at hb
        rw [grid_adj_iff'] at hab
        simp only [gridEmb_apply, Fin.val_castLE, Fin.ext_iff] at hab
        have := a''.1.isLt
        have := a''.2.isLt
        by_cases hrow : (a''.1 : ℕ) + 1 = m
        · exact le_trans (by exact_mod_cast h₁) (grid_edist_row_last u a'' hrow)
        · have hcol : (a''.2 : ℕ) + 1 = m := by omega
          exact le_trans (by exact_mod_cast h₂) (grid_edist_col_last u a'' hcol)
      · rw [htop ha]; exact le_top
    · by_cases ha : a' ∈ Set.range (gridEmb hmN)
      · obtain ⟨a'', rfl⟩ := ha
        exact Or.inr (hout a'' rfl)
      · exact Or.inl ha
  apply ballAgree_of_le
  · intro a b h
    rw [map_adj] at h ⊢
    obtain ⟨a', b', h, rfl, rfl⟩ := h
    exact ⟨gridEmb hmN a', gridEmb hmN b', (gridEmb_adj_iff hmN).2 h, he _, he _⟩
  · intro a b hab hn
    rw [map_adj] at hab
    obtain ⟨a', b', hab, rfl, rfl⟩ := hab
    exact (key a' b' hab hn).1
  · intro a b hab hn
    rw [map_adj] at hab
    obtain ⟨a', b', hab, rfl, rfl⟩ := hab
    rcases (key a' b' hab hn).2.2 with h | h
    · simp only [Equiv.coe_toEmbedding] at hn ⊢
      left; rw [(key a' b' hab hn).2.1 h]; exact WithTop.coe_lt_top _
    · simp only [Equiv.coe_toEmbedding] at hn ⊢
      right
      have hn' : ¬ ((grid m).map f).Adj (e b') (e a') := fun h' => hn h'.symm
      rw [(key b' a' hab.symm hn').2.1 h]; exact WithTop.coe_lt_top _

/-! ### Row rotations of the cylinder -/

/-- Rotate the rows of the cylinder by `s`. -/
def rowRot {m k : ℕ} [NeZero m] (s : Fin m) : Equiv.Perm (Fin m × Fin k) :=
  Equiv.prodCongr (Equiv.addRight s) (Equiv.refl _)

lemma rowRot_adj_iff {m k : ℕ} (s : Fin (m + 2)) (p q : Fin (m + 2) × Fin k) :
    (cyl (m + 2) k).Adj (rowRot s p) (rowRot s q) ↔ (cyl (m + 2) k).Adj p q := by
  simp only [cyl, rowRot, boxProd_adj, cycleGraph_adj, Equiv.prodCongr_apply, Prod.map,
    Equiv.coe_addRight, Equiv.refl_apply, add_sub_add_right_eq_sub, add_left_inj]

/-! ### The lower bound -/

/-- The view of a Klein bottle edge `{p, q}` (with `q` vertical from `p` or `q = kshift p`) is the
view of an edge `{p₂, q₂}` of the grid `P_m □ P_m` near its top-left corner, with identifiers
`f₂`. -/
lemma grid_view {m r : ℕ} (hrm : 2 * r + 3 ≤ m + 2) {V : Type*}
    (e₂ : (Fin (m + 2) × Fin (m + 2)) ↪ V) {p q : Fin (m + 2) × Fin (m + 2)}
    (hpq : (klein (m + 2) (m + 2)).Adj p q) (hcase : p.2 = q.2 ∨ q = kshift p) :
    ∃ (f₂ : (Fin (m + 2) × Fin (m + 2)) ↪ V) (p₂ q₂ : Fin (m + 2) × Fin (m + 2)),
      (grid (m + 2)).Adj p₂ q₂ ∧ f₂ p₂ = e₂ p ∧ f₂ q₂ = e₂ q ∧
      ((p₂.1 : ℕ) ≤ r + 1 ∧ (p₂.2 : ℕ) ≤ r + 1) ∧ ((q₂.1 : ℕ) ≤ r + 1 ∧ (q₂.2 : ℕ) ≤ r + 1) ∧
      BallAgree ((grid (m + 2)).map f₂) ((klein (m + 2) (m + 2)).map e₂) (e₂ p) r ∧
      BallAgree ((grid (m + 2)).map f₂) ((klein (m + 2) (m + 2)).map e₂) (e₂ q) r := by
  obtain ⟨σ, hH, hcp, hcq, hbp, hbq⟩ := cyl_view (m := m) (k := m + 2) (r := r) (by omega) e₂ hpq hcase
  set f₁ := σ.symm.toEmbedding.trans e₂
  -- rotate rows: the upper endpoint goes to row `r`
  obtain ⟨s, hs⟩ : ∃ s : Fin (m + 2), (((rowRot (k := m + 2) s (σ p)).1 : ℕ) = r ∨
      ((rowRot (k := m + 2) s (σ p)).1 : ℕ) = r + 1) ∧
      (((rowRot (k := m + 2) s (σ q)).1 : ℕ) = r ∨
      ((rowRot (k := m + 2) s (σ q)).1 : ℕ) = r + 1) := by
    have hrow : (σ p).1 = (σ q).1 ∨ (σ q).1 - (σ p).1 = 1 ∨ (σ p).1 - (σ q).1 = 1 := by
      rcases hH with ⟨h, -⟩ | ⟨-, h⟩
      · rw [cycleGraph_adj] at h; tauto
      · exact Or.inl h
    have hr : r < m + 2 := by omega
    have h1 : ((⟨r, hr⟩ : Fin (m + 2)) + 1 : Fin (m + 2)) = ⟨r + 1, by omega⟩ := by
      ext; simp [Fin.val_add, Nat.mod_eq_of_lt (show r + 1 < m + 2 by omega)]
    rcases hrow with h | h | h
    · refine ⟨⟨r, hr⟩ - (σ p).1, ?_⟩
      simp [rowRot, ← h]
    · refine ⟨⟨r, hr⟩ - (σ p).1, ?_⟩
      have : (σ q).1 = (σ p).1 + 1 := by rw [← h]; abel
      simp only [rowRot, Equiv.prodCongr_apply, Prod.map, Equiv.coe_addRight, this]
      refine ⟨Or.inl (by simp), Or.inr ?_⟩
      rw [show (σ p).1 + 1 + (⟨r, hr⟩ - (σ p).1) = (⟨r, hr⟩ : Fin (m + 2)) + 1 by abel, h1]
    · refine ⟨⟨r, hr⟩ - (σ q).1, ?_⟩
      have : (σ p).1 = (σ q).1 + 1 := by rw [← h]; abel
      simp only [rowRot, Equiv.prodCongr_apply, Prod.map, Equiv.coe_addRight, this]
      refine ⟨Or.inr ?_, Or.inl (by simp)⟩
      rw [show (σ q).1 + 1 + (⟨r, hr⟩ - (σ q).1) = (⟨r, hr⟩ : Fin (m + 2)) + 1 by abel, h1]
  set ρ : Equiv.Perm (Fin (m + 2) × Fin (m + 2)) := rowRot s
  have hρ : ∀ a b, (cyl (m + 2) (m + 2)).Adj (ρ a) (ρ b) ↔ (cyl (m + 2) (m + 2)).Adj a b :=
    rowRot_adj_iff s
  set f₂ := ρ.symm.toEmbedding.trans f₁
  have hf₂ : ∀ a, f₂ (ρ (σ a)) = e₂ a := fun a => by simp [f₂, f₁]
  have hcyl : (cyl (m + 2) (m + 2)).map f₂ = (cyl (m + 2) (m + 2)).map f₁ :=
    map_trans_eq_of_aut ρ hρ f₁
  set p₂ := ρ (σ p)
  set q₂ := ρ (σ q)
  have hp₂ : ((p₂.1 : ℕ) = r ∨ (p₂.1 : ℕ) = r + 1) ∧ (p₂.2 : ℕ) = r := ⟨hs.1, hcp⟩
  have hq₂ : ((q₂.1 : ℕ) = r ∨ (q₂.1 : ℕ) = r + 1) ∧
      ((q₂.2 : ℕ) = r ∨ (q₂.2 : ℕ) = r + 1) := ⟨hs.2, hcq⟩
  -- the image edge is a grid edge
  have hcadj : (cyl (m + 2) (m + 2)).Adj p₂ q₂ := (hρ _ _).2 hH
  have hgadj : (grid (m + 2)).Adj p₂ q₂ := by
    rcases hcadj with ⟨h, e⟩ | ⟨h, e⟩
    · refine Or.inl ⟨?_, e⟩
      rw [cycleGraph_adj', fin_sub_val, fin_sub_val] at h
      rw [pathGraph_adj]
      have := p₂.1.isLt
      have := q₂.1.isLt
      split_ifs at h <;> omega
    · exact Or.inr ⟨h, e⟩
  have hview : ∀ u, ((u.1 : ℕ) = r ∨ (u.1 : ℕ) = r + 1) →
      BallAgree ((cyl (m + 2) (m + 2)).map f₁) ((klein (m + 2) (m + 2)).map e₂) (f₂ u) r →
      BallAgree ((grid (m + 2)).map f₂) ((klein (m + 2) (m + 2)).map e₂) (f₂ u) r := by
    intro u hu1 b3
    have b2 : BallAgree ((grid (m + 2)).map f₂) ((cyl (m + 2) (m + 2)).map f₂) (f₂ u) r :=
      (BallAgree.map f₂ (ballAgree_cyl_grid (r := r) u (by omega) (by omega) (by omega))).symm
    rw [hcyl] at b2
    exact b2.trans b3
  refine ⟨f₂, p₂, q₂, hgadj, hf₂ p, hf₂ q, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_, ?_⟩
  · rw [← hf₂ p]; exact hview p₂ hp₂.1 (by rw [hf₂]; exact hbp)
  · rw [← hf₂ q]; exact hview q₂ hq₂.1 (by rw [hf₂]; exact hbq)

/-- **Theorem 2.6 (sharp form of the paper's argument).** Let `m` be odd with `2r + 3 ≤ m ≤ N`.
No `r`-round algorithm (identifiers: `V`, `|V| = N²`) 3-colours the `N × N` grid. -/
theorem grid_not_colours {N m r : ℕ} (hm : Odd m) (hrm : 2 * r + 3 ≤ m) (hmN : m ≤ N)
    {V : Type*} [Fintype V] (hV : Fintype.card V = N * N) {A : SimpleGraph V → V → Fin 3}
    (hA : BallLocal r A) : ¬ ColoursGraph A (grid N) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨e₂⟩ : Nonempty ((Fin (m + 2) × Fin (m + 2)) ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_prod, Fintype.card_fin, hV]; exact Nat.mul_le_mul hmN hmN)
  refine not_colours_of_views hA (klein_not_colorable hm (by omega) (by omega)) e₂
    fun x y hxy => ?_
  have key : ∀ p q, (klein (m + 2) (m + 2)).Adj p q → (p.2 = q.2 ∨ q = kshift p) →
      ∃ (e : (Fin N × Fin N) ≃ V) (x' y' : Fin N × Fin N), (grid N).Adj x' y' ∧
        e x' = e₂ p ∧ e y' = e₂ q ∧
        BallAgree ((grid N).map e.toEmbedding) ((klein (m + 2) (m + 2)).map e₂) (e₂ p) r ∧
        BallAgree ((grid N).map e.toEmbedding) ((klein (m + 2) (m + 2)).map e₂) (e₂ q) r := by
    intro p q hpq hcase
    obtain ⟨f₂, p₂, q₂, hgadj, hp, hq, hpp, hqq, hbp, hbq⟩ := grid_view hrm e₂ hpq hcase
    obtain ⟨e, he⟩ := exists_equiv_extend (gridEmb hmN) f₂
      ⟨Fintype.equivOfCardEq (by simp [hV])⟩
    refine ⟨e, gridEmb hmN p₂, gridEmb hmN q₂, (gridEmb_adj_iff hmN).2 hgadj,
      by rw [he, hp], by rw [he, hq], ?_, ?_⟩
    · rw [← hp]
      exact (ballAgree_grid_embed (r := r) hmN f₂ e he p₂ (by omega) (by omega)).trans
        (hp ▸ hbp)
    · rw [← hq]
      exact (ballAgree_grid_embed (r := r) hmN f₂ e he q₂ (by omega) (by omega)).trans
        (hq ▸ hbq)
  rcases klein_adj_cases hxy with h | h | h
  · exact key _ _ hxy (Or.inl h)
  · exact key _ _ hxy (Or.inr h)
  · obtain ⟨e, x', y', hH, h1, h2, h3, h4⟩ := key _ _ hxy.symm (Or.inr h)
    exact ⟨e, y', x', hH.symm, h2, h1, h4, h3⟩

/-- **Theorem 2.6** of the paper, with the bound that its proof gives: if `2r + 3 ≤ N`, no `r`-round
algorithm 3-colours the `N × N` grid. (The paper states `2r + 1 ≤ N`, i.e. "less than `N/2`
rounds", which is false for odd `N`: see `Theorem26Counterexample.lean`.) -/
theorem theorem_2_6 {N r : ℕ} (hr : 2 * r + 3 ≤ N) {V : Type*} [Fintype V]
    (hV : Fintype.card V = N * N) {A : SimpleGraph V → V → Fin 3} (hA : BallLocal r A) :
    ¬ ColoursGraph A (grid N) := by
  rcases Nat.even_or_odd N with h | h
  · exact grid_not_colours (m := N - 1) (by
      obtain ⟨t, ht⟩ := h; exact ⟨t - 1, by omega⟩) (by
      obtain ⟨t, ht⟩ := h; omega) (by omega) hV hA
  · exact grid_not_colours h hr le_rfl hV hA

/-- **Theorem 2.6, second sentence** ("no distributed algorithm can 3-colour every planar
bipartite graph on `n` vertices in `o(√n)` rounds"), with explicit constants: every `r`-round
algorithm on `n ≥ (2r + 3)²` identifiers fails on some copy of the `(2r + 3) × (2r + 3)` grid (planar,
bipartite) plus isolated nodes. -/
theorem theorem_2_6_family {n r : ℕ} (hn : (2 * r + 3) * (2 * r + 3) ≤ n) {V : Type*}
    [Fintype V] (hV : Fintype.card V = n) {A : SimpleGraph V → V → Fin 3} (hA : BallLocal r A) :
    ∃ G : SimpleGraph V, IsCopyOf (grid (2 * r + 3)) G ∧ ∃ u v, G.Adj u v ∧ A G u = A G v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨e₂⟩ : Nonempty ((Fin (2 * r + 1 + 2) × Fin (2 * r + 1 + 2)) ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_prod, Fintype.card_fin, hV]
      exact le_of_eq_of_le (by ring) hn)
  have := coloring_of_views_family hA (𝒢 := {G | IsCopyOf (grid (2 * r + 1 + 2)) G})
    (fun G hG u v huv => hcon G hG u v huv) e₂ (K := klein (2 * r + 1 + 2) (2 * r + 1 + 2))
    fun x y hxy => ?_
  · exact (klein_not_colorable (m := 2 * r + 1 + 2) ⟨r + 1, by ring⟩ (by omega)
      (by omega)).false this.some
  have key : ∀ p q, (klein (2 * r + 1 + 2) (2 * r + 1 + 2)).Adj p q →
      (p.2 = q.2 ∨ q = kshift p) →
      ∃ G ∈ {G | IsCopyOf (grid (2 * r + 1 + 2)) G}, G.Adj (e₂ p) (e₂ q) ∧
        BallAgree G ((klein (2 * r + 1 + 2) (2 * r + 1 + 2)).map e₂) (e₂ p) r ∧
        BallAgree G ((klein (2 * r + 1 + 2) (2 * r + 1 + 2)).map e₂) (e₂ q) r := by
    intro p q hpq hcase
    obtain ⟨f₂, p₂, q₂, hgadj, hp, hq, -, -, hbp, hbq⟩ := grid_view (r := r) (by omega) e₂ hpq hcase
    refine ⟨_, ⟨f₂, rfl⟩, ?_, hbp, hbq⟩
    rw [← hp, ← hq]
    exact (map_adj_apply (f := f₂)).2 hgadj
  rcases klein_adj_cases hxy with h | h | h
  · exact key _ _ hxy (Or.inl h)
  · exact key _ _ hxy (Or.inr h)
  · obtain ⟨G, hG, hadj, h3, h4⟩ := key _ _ hxy.symm (Or.inr h)
    exact ⟨G, hG, hadj.symm, h4, h3⟩

end Podc.SparseColoringLB
