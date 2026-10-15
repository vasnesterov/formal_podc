import Papers.PODC2024.OnlineLocalGrids.Defs

/-!
# Geometry of the simple grid `grid m m`

Positions are `Fin m × Fin m` (row, column). We use integer coordinates `rz p`, `cz p`.

* `grid_adj_iff`: adjacency is Manhattan distance `1`;
* `mem_ball_grid`: balls are Manhattan balls (no border effects for distances in a simple grid);
* `grid_exists_move`: the adversary may move a part of the discovered region along its row by a
  translation or a reflection of the columns, provided the moved part stays (with its radius-`T`
  neighbourhood) inside the grid and far from the rest of the discovered region. This is the
  re-embedding power used in Lemma 3.6 and in the proof of Theorem 1.1.
-/

namespace Papers.PODC2024.OnlineLocalGrids

open SimpleGraph Cslib.OnlineLocal

variable {m : ℕ}

/-- Row coordinate as an integer. -/
def rz (p : Fin m × Fin m) : ℤ := ((p.1 : ℕ) : ℤ)
/-- Column coordinate as an integer. -/
def cz (p : Fin m × Fin m) : ℤ := ((p.2 : ℕ) : ℤ)

lemma rz_nonneg (p : Fin m × Fin m) : 0 ≤ rz p := Int.natCast_nonneg _
lemma rz_lt (p : Fin m × Fin m) : rz p < m := by simp [rz]
lemma cz_nonneg (p : Fin m × Fin m) : 0 ≤ cz p := Int.natCast_nonneg _
lemma cz_lt (p : Fin m × Fin m) : cz p < m := by simp [cz]

/-- Manhattan distance. -/
def md (p q : Fin m × Fin m) : ℕ := (rz p - rz q).natAbs + (cz p - cz q).natAbs

lemma pos_ext {p q : Fin m × Fin m} (h1 : rz p = rz q) (h2 : cz p = cz q) : p = q := by
  simp only [rz, cz] at h1 h2
  apply Prod.ext <;> apply Fin.ext <;> omega

lemma grid_adj_iff {p q : Fin m × Fin m} : (grid m m).Adj p q ↔ md p q = 1 := by
  simp only [grid, boxProd_adj, pathGraph_adj, md, rz, cz, Fin.ext_iff]
  omega

lemma md_comm (p q : Fin m × Fin m) : md p q = md q p := by unfold md; omega

lemma md_triangle (p q r : Fin m × Fin m) : md p r ≤ md p q + md q r := by unfold md; omega

/-- Balls in the simple grid are Manhattan balls. -/
lemma mem_ball_grid {U : Set (Fin m × Fin m)} {k : ℕ} {q : Fin m × Fin m} :
    q ∈ ball (grid m m) U k ↔ ∃ u ∈ U, md u q ≤ k := by
  induction k generalizing q with
  | zero =>
    simp only [Cslib.OnlineLocal.ball_zero, Nat.le_zero]
    constructor
    · intro h; exact ⟨q, h, by simp [md]⟩
    · rintro ⟨u, hu, h⟩
      have : u = q := pos_ext (by unfold md at h; omega) (by unfold md at h; omega)
      exact this ▸ hu
  | succ k ih =>
    constructor
    · rintro (h | ⟨x, hx, hxq⟩)
      · obtain ⟨u, hu, h⟩ := ih.1 h; exact ⟨u, hu, by omega⟩
      · obtain ⟨u, hu, h⟩ := ih.1 hx
        rw [grid_adj_iff] at hxq
        exact ⟨u, hu, by unfold md at h hxq ⊢; omega⟩
    · rintro ⟨u, hu, h⟩
      by_cases hk : md u q ≤ k
      · exact ball_subset_succ (ih.2 ⟨u, hu, hk⟩)
      · -- step from `q` one unit towards `u`
        obtain ⟨q', hq'1, hq'2⟩ : ∃ q' : Fin m × Fin m, md u q' ≤ k ∧ md q' q = 1 := by
          clear ih
          simp only [md, rz, cz] at h hk ⊢
          by_cases hr : (q.1 : ℕ) = u.1
          · by_cases hc : (q.2 : ℕ) < u.2
            · refine ⟨(q.1, ⟨q.2 + 1, by omega⟩), ?_, ?_⟩ <;> simp only <;> omega
            · refine ⟨(q.1, ⟨q.2 - 1, by omega⟩), ?_, ?_⟩ <;> simp only <;> omega
          · by_cases hr' : (q.1 : ℕ) < u.1
            · refine ⟨(⟨q.1 + 1, by omega⟩, q.2), ?_, ?_⟩ <;> simp only <;> omega
            · refine ⟨(⟨q.1 - 1, by omega⟩, q.2), ?_, ?_⟩ <;> simp only <;> omega
        exact mem_ball_succ_of_adj (ih.2 ⟨u, hu, hq'1⟩) (grid_adj_iff.2 hq'2)

/-! ### Column isometries -/

/-- The column map `j ↦ d - j` (if `fl`) or `j ↦ d + j`. -/
def cm (fl : Bool) (d j : ℤ) : ℤ := if fl then d - j else d + j

/-- Its inverse. -/
def cmInv (fl : Bool) (d j : ℤ) : ℤ := if fl then d - j else j - d

@[simp] lemma cm_cmInv (fl : Bool) (d j : ℤ) : cm fl d (cmInv fl d j) = j := by
  cases fl <;> simp [cm, cmInv]

@[simp] lemma cmInv_cm (fl : Bool) (d j : ℤ) : cmInv fl d (cm fl d j) = j := by
  cases fl <;> simp [cm, cmInv]

lemma natAbs_cm_sub (fl : Bool) (d j j' : ℤ) : (cm fl d j - cm fl d j').natAbs = (j - j').natAbs := by
  cases fl <;> simp only [cm, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- An integer, as an element of `Fin m` (meaningful for `0 ≤ z < m`). -/
def toFin [NeZero m] (z : ℤ) : Fin m := ⟨z.toNat % m, Nat.mod_lt _ (NeZero.pos m)⟩

lemma toFin_val [NeZero m] {z : ℤ} (h0 : 0 ≤ z) (h1 : z < m) : (((toFin (m := m) z : Fin m) : ℕ) : ℤ) = z := by
  simp only [toFin]
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- The position in row `r`, column `j` (meaningful in range). -/
def pt [NeZero m] (r j : ℤ) : Fin m × Fin m := (toFin r, toFin j)

lemma rz_pt [NeZero m] {r j : ℤ} (h0 : 0 ≤ r) (h1 : r < m) : rz (pt (m := m) r j) = r := toFin_val h0 h1

lemma cz_pt [NeZero m] {r j : ℤ} (h0 : 0 ≤ j) (h1 : j < m) : cz (pt (m := m) r j) = j := toFin_val h0 h1

lemma eq_pt_iff [NeZero m] {p : Fin m × Fin m} {r j : ℤ} (h0 : 0 ≤ r) (h1 : r < m) (h2 : 0 ≤ j)
    (h3 : j < m) : p = pt r j ↔ rz p = r ∧ cz p = j := by
  constructor
  · rintro rfl; exact ⟨rz_pt h0 h1, cz_pt h2 h3⟩
  · rintro ⟨h, h'⟩; exact pos_ext (by rw [h, rz_pt h0 h1]) (by rw [h', cz_pt h2 h3])

lemma pt_rz_cz [NeZero m] (p : Fin m × Fin m) : pt (rz p) (cz p) = p :=
  ((eq_pt_iff (rz_nonneg p) (rz_lt p) (cz_nonneg p) (cz_lt p)).2 ⟨rfl, rfl⟩).symm

/-- The column isometry acting on positions (the identity outside its range). -/
def colMap [NeZero m] (fl : Bool) (d : ℤ) (p : Fin m × Fin m) : Fin m × Fin m :=
  (p.1, toFin (cm fl d (cz p)))

lemma rz_colMap [NeZero m] (fl : Bool) (d : ℤ) (p : Fin m × Fin m) :
    rz (colMap fl d p) = rz p := rfl

lemma cz_colMap [NeZero m] {fl : Bool} {d : ℤ} {p : Fin m × Fin m} (h0 : 0 ≤ cm fl d (cz p))
    (h1 : cm fl d (cz p) < m) : cz (colMap fl d p) = cm fl d (cz p) := toFin_val h0 h1

/-- **Moving a row piece.** Let the revealed positions be `U₁ ∪ U₂`. Move `U₂` (with its
radius-`T` neighbourhood) by the column isometry `cm fl d`, keeping rows. If `U₂`'s neighbourhood
stays inside the grid before and after the move, and `U₂` is at Manhattan distance `≥ 2T+2` from
`U₁` before and after the move, then the move is invisible to the algorithm. -/
theorem grid_exists_move [NeZero m] {U₁ U₂ : Set (Fin m × Fin m)} {T : ℕ} (fl : Bool) (d : ℤ)
    (hin : ∀ u ∈ U₂, T ≤ rz u ∧ rz u + T < m ∧ T ≤ cz u ∧ cz u + T < m ∧
      T ≤ cm fl d (cz u) ∧ cm fl d (cz u) + T < m)
    (hsep : ∀ u ∈ U₁, ∀ v ∈ U₂, 2 * T + 2 ≤ md u v ∧
      2 * T + 2 ≤ (rz u - rz v).natAbs + (cz u - cm fl d (cz v)).natAbs) :
    ∃ μ : Equiv.Perm (Fin m × Fin m), (∀ p ∈ ball (grid m m) U₁ T, μ p = p) ∧
      (∀ p ∈ U₂, rz (μ p) = rz p ∧ cz (μ p) = cm fl d (cz p)) ∧
      AgreeOn (grid m m) ((grid m m).comap μ) (U₁ ∪ U₂) T := by
  set G := grid m m
  -- points of the neighbourhood of `U₂` are mapped in range
  have hY : ∀ p ∈ ball G U₂ T, ∃ u ∈ U₂, md u p ≤ T ∧ 0 ≤ cm fl d (cz p) ∧ cm fl d (cz p) < m :=
    by
    intro p hp
    obtain ⟨u, hu, h⟩ := mem_ball_grid.1 hp
    obtain ⟨-, -, -, -, h5, h6⟩ := hin u hu
    have := natAbs_cm_sub fl d (cz u) (cz p)
    exact ⟨u, hu, h, by unfold md at h; omega, by unfold md at h; omega⟩
  have hmd : ∀ p ∈ ball G U₂ T, ∀ q ∈ ball G U₂ T,
      md (colMap fl d p) (colMap fl d q) = md p q := by
    intro p hp q hq
    obtain ⟨-, -, -, hp0, hp1⟩ := hY p hp
    obtain ⟨-, -, -, hq0, hq1⟩ := hY q hq
    simp only [md, rz_colMap, cz_colMap hp0 hp1, cz_colMap hq0 hq1, natAbs_cm_sub]
  obtain ⟨μ, hμX, hμY, hag⟩ := exists_move (G := G) (U₁ := U₁) (U₂ := U₂) (T := T) (colMap fl d)
    (fun p hp q hq hpq => by
      have h := hmd p hp q hq
      rw [hpq] at h
      exact pos_ext (by unfold md at h; omega) (by unfold md at h; omega))
    (fun p hp q hq => by rw [grid_adj_iff, grid_adj_iff, hmd p hp q hq])
    (fun k hk p hp q hpq => by
      obtain ⟨u, hu, hup⟩ := mem_ball_grid.1 hp
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin u hu
      obtain ⟨-, -, -, hp0, hp1⟩ := hY p (ball_mono hk.le hp)
      rw [grid_adj_iff] at hpq
      have hcu := natAbs_cm_sub fl d (cz u) (cz p)
      have hcq := natAbs_cm_sub fl d (cz u) (cmInv fl d (cz q))
      rw [cm_cmInv] at hcq
      simp only [md, rz_colMap, cz_colMap hp0 hp1] at hpq hup
      have hc0 : 0 ≤ cmInv fl d (cz q) := by omega
      have hc1 : cmInv fl d (cz q) < m := by omega
      let q' : Fin m × Fin m := (q.1, toFin (cmInv fl d (cz q)))
      have hr' : rz q' = rz q := rfl
      have hc' : cz q' = cmInv fl d (cz q) := toFin_val hc0 hc1
      refine ⟨q', mem_ball_grid.2 ⟨u, hu, ?_⟩, ?_⟩
      · simp only [md, hr', hc']; omega
      · have e0 : 0 ≤ cm fl d (cz q') := by rw [hc', cm_cmInv]; exact cz_nonneg q
        have e1 : cm fl d (cz q') < m := by rw [hc', cm_cmInv]; exact cz_lt q
        exact pos_ext (by rw [rz_colMap, hr']) (by rw [cz_colMap e0 e1, hc', cm_cmInv]))
    (fun p hp q hq => by
      obtain ⟨u, hu, hup⟩ := mem_ball_grid.1 hp
      obtain ⟨v, hv, hvq, -, -⟩ := hY q hq
      obtain ⟨hs1, hs2⟩ := hsep u hu v hv
      have hv' : v ∈ ball G U₂ T := subset_ball hv
      have hs2' : 2 * T + 2 ≤ md u (colMap fl d v) := by
        obtain ⟨-, -, -, h0, h1⟩ := hY v hv'
        simp only [md, rz_colMap, cz_colMap h0 h1]; exact hs2
      have hqv : md (colMap fl d v) (colMap fl d q) = md v q := hmd v hv' q hq
      have t1 := md_triangle u p q
      have t2 := md_triangle u q v
      have t3 := md_triangle u p (colMap fl d q)
      have t4 := md_triangle u (colMap fl d q) (colMap fl d v)
      rw [md_comm q v] at t2
      rw [md_comm (colMap fl d q) (colMap fl d v)] at t4
      clear hs2 hmd hY hsep hin
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · subst h; have : md p p = 0 := by simp [md]
        omega
      · rw [grid_adj_iff] at h; omega
      · subst h; have : md (colMap fl d q) (colMap fl d q) = 0 := by simp [md]
        omega
      · rw [grid_adj_iff] at h; omega)
  refine ⟨μ, hμX, fun p hp => ?_, hag⟩
  have hp' : p ∈ ball G U₂ T := subset_ball hp
  obtain ⟨-, -, -, hp0, hp1⟩ := hY p hp'
  rw [hμY p hp', rz_colMap, cz_colMap hp0 hp1]
  exact ⟨rfl, rfl⟩

end Papers.PODC2024.OnlineLocalGrids
