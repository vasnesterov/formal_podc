import Papers.PODC2019.HardnessOptimization.MDSGraph

/-!
# Local analysis of one bit-gadget 6-cycle (used in the proof of Lemma 2.1)

For a cycle `(ℓ, h)` and a set `D` we record six membership bits `m s κ` (is `gad s ℓ h κ ∈ D`)
and four row bits `r s b` (does `D` contain a row of side `s`, layer `ℓ`, with bit `b` at `h`).
`LocOk m r` says that all six cycle vertices are dominated. All local facts are checked by
`decide` over the `2^10` cases.
-/

namespace HardnessOptimization

/-- Six bits as a function `Bool → Fin 3 → Bool` (`false` = side `A`). -/
def mk6 (a0 a1 a2 b0 b1 b2 : Bool) : Bool → Fin 3 → Bool :=
  fun s κ => if s then ![b0, b1, b2] κ else ![a0, a1, a2] κ

/-- Four bits as a function `Bool → Bool → Bool`. -/
def mk4 (r0 r1 q0 q1 : Bool) : Bool → Bool → Bool :=
  fun s b => if s then (if b then q1 else q0) else (if b then r1 else r0)

lemma eq_mk6 (m : Bool → Fin 3 → Bool) :
    m = mk6 (m false 0) (m false 1) (m false 2) (m true 0) (m true 1) (m true 2) := by
  funext s κ; cases s <;> fin_cases κ <;> rfl

lemma eq_mk4 (r : Bool → Bool → Bool) :
    r = mk4 (r false false) (r false true) (r true false) (r true true) := by
  funext s b; cases s <;> cases b <;> rfl

/-- All six vertices of the cycle are dominated (by cycle vertices or by rows). -/
def LocOk (m : Bool → Fin 3 → Bool) (r : Bool → Bool → Bool) : Prop :=
  ∀ s κ, m s κ = true ∨ (∃ s' κ', CycAdj s κ s' κ' ∧ m s' κ' = true) ∨
    (κ = 0 ∧ r s false = true) ∨ (κ = 1 ∧ r s true = true)

instance (m r) : Decidable (LocOk m r) := by unfold LocOk; infer_instance

/-- Number of cycle vertices in `D`. -/
def cnt6 (m : Bool → Fin 3 → Bool) : ℕ :=
  (m false 0).toNat + (m false 1).toNat + (m false 2).toNat +
    (m true 0).toNat + (m true 1).toNat + (m true 2).toNat

/-- Every cycle contains at least two vertices of a dominating set (the closed neighbourhoods of
`u_A` and `u_B` are disjoint and inside the cycle). -/
lemma loc_two_le : ∀ (m : Bool → Fin 3 → Bool) (r : Bool → Bool → Bool),
    LocOk m r → 2 ≤ cnt6 m := by
  intro m r
  rw [eq_mk6 m, eq_mk4 r]
  generalize m false 0 = a0, m false 1 = a1, m false 2 = a2, m true 0 = b0, m true 1 = b1,
    m true 2 = b2, r false false = r0, r false true = r1, r true false = q0, r true true = q1
  revert a0 a1 a2 b0 b1 b2 r0 r1 q0 q1
  decide

/-- A cycle with exactly two vertices of `D`, both `f_s` and `t_s` among them, needs two rows of
the other side (with both bit values) to dominate `f_{¬s}` and `t_{¬s}`. -/
lemma loc_both : ∀ (m : Bool → Fin 3 → Bool) (r : Bool → Bool → Bool) (s : Bool),
    LocOk m r → cnt6 m ≤ 2 → m s 0 = true → m s 1 = true →
      r (!s) false = true ∧ r (!s) true = true := by
  intro m r s
  rw [eq_mk6 m, eq_mk4 r]
  generalize m false 0 = a0, m false 1 = a1, m false 2 = a2, m true 0 = b0, m true 1 = b1,
    m true 2 = b2, r false false = r0, r false true = r1, r true false = q0, r true true = q1
  revert a0 a1 a2 b0 b1 b2 r0 r1 q0 q1 s
  decide

lemma loc_four : ∀ (m : Bool → Fin 3 → Bool),
    m false 0 = true → m false 1 = true → m true 0 = true → m true 1 = true → 4 ≤ cnt6 m := by
  intro m h1 h2 h3 h4
  simp only [cnt6, h1, h2, h3, h4, Bool.toNat_true]
  omega

/-- Two vertices, one of `f_A, t_A` and one of `f_B, t_B`: they must be antipodal. -/
lemma loc_match_both : ∀ (m : Bool → Fin 3 → Bool) (r : Bool → Bool → Bool),
    LocOk m r → cnt6 m ≤ 2 → (m false 0 = true ∨ m false 1 = true) →
      (m true 0 = true ∨ m true 1 = true) →
        m false 0 = m true 0 ∧ m false 1 = m true 1 := by
  intro m r
  rw [eq_mk6 m, eq_mk4 r]
  generalize m false 0 = a0, m false 1 = a1, m false 2 = a2, m true 0 = b0, m true 1 = b1,
    m true 2 = b2, r false false = r0, r false true = r1, r true false = q0, r true true = q1
  revert a0 a1 a2 b0 b1 b2 r0 r1 q0 q1
  decide

/-- Two vertices, one of `f_s, t_s`, and no row of side `¬s` helps: they must be antipodal. -/
lemma loc_match_one : ∀ (m : Bool → Fin 3 → Bool) (r : Bool → Bool → Bool) (s : Bool),
    LocOk m r → cnt6 m ≤ 2 → (m s 0 = true ∨ m s 1 = true) →
      r (!s) false = false → r (!s) true = false →
        m false 0 = m true 0 ∧ m false 1 = m true 1 := by
  intro m r s
  rw [eq_mk6 m, eq_mk4 r]
  generalize m false 0 = a0, m false 1 = a1, m false 2 = a2, m true 0 = b0, m true 1 = b1,
    m true 2 = b2, r false false = r0, r false true = r1, r true false = q0, r true true = q1
  revert a0 a1 a2 b0 b1 b2 r0 r1 q0 q1 s
  decide

/-- Two vertices and no row helps at all: the pattern is `{f_A, f_B}`, `{t_A, t_B}` or
`{u_A, u_B}`. -/
lemma loc_match_none : ∀ (m : Bool → Fin 3 → Bool) (r : Bool → Bool → Bool),
    LocOk m r → cnt6 m ≤ 2 → (∀ s b, r s b = false) →
      m false 0 = m true 0 ∧ m false 1 = m true 1 ∧ ¬(m false 0 = true ∧ m false 1 = true) := by
  intro m r
  rw [eq_mk6 m, eq_mk4 r]
  generalize m false 0 = a0, m false 1 = a1, m false 2 = a2, m true 0 = b0, m true 1 = b1,
    m true 2 = b2, r false false = r0, r false true = r1, r true false = q0, r true true = q1
  revert a0 a1 a2 b0 b1 b2 r0 r1 q0 q1
  decide

/-- The canonical dominating set meets every cycle in `{f_A, f_B}` or `{t_A, t_B}`, which
dominates the whole cycle. -/
lemma cyc_dom_canon : ∀ (s : Bool) (κ : Fin 3) (b : Bool),
    κ = (if b then 0 else 1) ∨ ∃ s', CycAdj s κ s' (if b then 0 else 1) := by
  decide

end HardnessOptimization
