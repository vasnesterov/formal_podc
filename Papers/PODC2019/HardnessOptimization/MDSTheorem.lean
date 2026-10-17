import Papers.PODC2019.HardnessOptimization.MDS

/-!
# Theorem 2.1: exact MDS needs `Ω(n² / log² n)` CONGEST rounds

The graphs `G_{x,y}` form a family of lower bound graphs (Definition 1.1) for `DISJ_{k²}` with
`V_A` = Alice's rows and bit gadgets, `|E_cut| = 4 log k` (the edges `u_A – f_B`, `f_A – u_B` of the
`2 log k` six-cycles), and `n = 4k + 12 log k` vertices.
-/

namespace HardnessOptimization

open Finset Cslib.Congest Cslib.CommunicationComplexity

variable {L : ℕ}

/-- `G_{x,y}` with the inputs given as strings indexed by pairs `(i, j)`. -/
def mdsG (x y : Idx L × Idx L → Bool) : SimpleGraph (MV L) :=
  mdsGraph (fun i j => x (i, j)) (fun i j => y (i, j))

instance (x y : Idx L × Idx L → Bool) : DecidableRel (mdsG x y).Adj :=
  inferInstanceAs (DecidableRel (mdsGraph _ _).Adj)

/-- The cut edges: `(u_{A_ℓ}^h, f_{B_ℓ}^h)` and `(f_{A_ℓ}^h, u_{B_ℓ}^h)`. -/
def mdsCut (L : ℕ) : Finset (MV L × MV L) :=
  (univ : Finset (Bool × Fin L × Bool)).image fun p =>
    (MV.gad false p.1 p.2.1 (if p.2.2 then 2 else 0), MV.gad true p.1 p.2.1 (if p.2.2 then 0 else 2))

lemma card_mdsCut : (mdsCut L).card = 4 * L := by
  rw [mdsCut, card_image_of_injective]
  · simp [card_univ, Fintype.card_prod]; ring
  · rintro ⟨ℓ, h, b⟩ ⟨ℓ', h', b'⟩ he
    simp only [Prod.mk.injEq, MV.gad.injEq, true_and] at he
    obtain ⟨⟨rfl, rfl, hb⟩, -⟩ := he
    cases b <;> cases b' <;> simp_all

lemma cycAdj_cross {κ κ' : Fin 3} (h : CycAdj false κ true κ') :
    (κ = 2 ∧ κ' = 0) ∨ (κ = 0 ∧ κ' = 2) := by
  revert κ κ' h; decide

section AdjSides

variable {x y : Idx L → Idx L → Bool}

lemma mds_adj_cut {a b : MV L} (ha : a.side = false) (hb : b.side = true)
    (hab : (mdsGraph x y).Adj a b) : (a, b) ∈ mdsCut L := by
  cases a with
  | row s ℓ i =>
    cases b with
    | row s' ℓ' j =>
      rw [adj_row_row] at hab
      simp only [MV.side] at ha hb
      obtain ⟨rfl, -, -⟩ := hab
      simp_all
    | gad s' ℓ' h κ =>
      rw [adj_row_gad] at hab
      simp only [MV.side] at ha hb
      obtain ⟨rfl, -, -⟩ := hab
      simp_all
  | gad s ℓ h κ =>
    cases b with
    | row s' ℓ' j =>
      rw [adj_gad_row] at hab
      simp only [MV.side] at ha hb
      obtain ⟨rfl, -, -⟩ := hab
      simp_all
    | gad s' ℓ' h' κ' =>
      rw [adj_gad_gad] at hab
      obtain ⟨rfl, rfl, hc⟩ := hab
      simp only [MV.side] at ha hb
      subst ha hb
      refine mem_image.2 ?_
      rcases cycAdj_cross hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(_, _, true), mem_univ _, rfl⟩
      · exact ⟨(_, _, false), mem_univ _, rfl⟩

variable (x y) in
lemma mds_adj_A (y' : Idx L → Idx L → Bool) {a b : MV L} (ha : a.side = false)
    (hb : b.side = false) : (mdsGraph x y).Adj a b ↔ (mdsGraph x y').Adj a b := by
  cases a <;> cases b <;> simp_all [MV.side, adj_row_row, adj_row_gad, adj_gad_row,
    adj_gad_gad, redge, xy]

variable (x y) in
lemma mds_adj_B (x' : Idx L → Idx L → Bool) {a b : MV L} (ha : a.side = true)
    (hb : b.side = true) : (mdsGraph x y).Adj a b ↔ (mdsGraph x' y).Adj a b := by
  cases a <;> cases b <;> simp_all [MV.side, adj_row_row, adj_row_gad, adj_gad_row,
    adj_gad_gad, redge, xy]

variable (x y) in
lemma mds_adj_fixed (x' y' : Idx L → Idx L → Bool) {a b : MV L} (ha : a.side = false)
    (hb : b.side = true) : (mdsGraph x y).Adj a b ↔ (mdsGraph x' y').Adj a b := by
  cases a <;> cases b <;> simp_all [MV.side, adj_row_row, adj_row_gad, adj_gad_row,
    adj_gad_gad]

end AdjSides

/-- The MDS lower-bound graphs as a family of lower bound graphs (nodes know their
neighbourhoods). -/
def mdsFamily (L : ℕ) : LBFamily (Idx L × Idx L → Bool) (Idx L × Idx L → Bool) (MV L) (MV L → Bool) :=
  LBFamily.ofAdj mdsG (fun v => !v.side) (mdsCut L)
    (by
      intro p hp
      obtain ⟨q, -, rfl⟩ := mem_image.1 hp
      simp [MV.side])
    (fun x y a b ha hb hab => mds_adj_cut (by simpa using ha) (by simpa using hb) hab)
    (fun x y y' a b ha hb => mds_adj_A _ _ _ (by simpa using ha) (by simpa using hb))
    (fun x x' y a b ha hb => mds_adj_B _ _ _ (by simpa using ha) (by simpa using hb))
    (fun x x' y y' a b ha hb => mds_adj_fixed _ _ _ _ (by simpa using ha) (by simpa using hb))

instance (x y : Idx L × Idx L → Bool) : DecidableRel ((mdsFamily L).G x y).Adj :=
  inferInstanceAs (DecidableRel (mdsG x y).Adj)

lemma mdsFamily_G (x y : Idx L × Idx L → Bool) : (mdsFamily L).G x y = mdsG x y := rfl

lemma mdsFamily_inp (x y : Idx L × Idx L → Bool) :
    (mdsFamily L).inp x y = fun v w => decide ((mdsG x y).Adj v w) := rfl

lemma mdsFamily_Ecut : (mdsFamily L).Ecut = mdsCut L := rfl

/-- The vertex set has `n = 4k + 12 log k` elements, `k = 2^L`. -/
lemma card_MV : Fintype.card (MV L) = 4 * 2 ^ L + 12 * L := by
  let e : MV L ≃ (Bool × Bool × Idx L) ⊕ (Bool × Bool × Fin L × Fin 3) :=
    { toFun := fun v => match v with
        | .row s ℓ i => .inl (s, ℓ, i)
        | .gad s ℓ h κ => .inr (s, ℓ, h, κ)
      invFun := fun p => match p with
        | .inl (s, ℓ, i) => .row s ℓ i
        | .inr (s, ℓ, h, κ) => .gad s ℓ h κ
      left_inv := fun v => by cases v <;> rfl
      right_inv := fun p => by rcases p with ⟨s, ℓ, i⟩ | ⟨s, ℓ, h, κ⟩ <;> rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

/-- **Theorem 2.1** (deterministic, decision version). Let `A` be a deterministic CONGEST algorithm
with `B`-bit messages that, in `T` rounds, decides on every graph `G_{x,y}` of the family whether
there is a dominating set of size at most `M = 4 log k + 2` (all nodes accept iff there is one;
nodes know their neighbourhoods). Then `k² ≤ 8 T B log k + 2`. -/
theorem theorem_2_1 {σ : Type*} {B : ℕ} (A : Algorithm (MV L) (MV L → Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      A.Accepts (mdsG x y) (fun v w => decide ((mdsG x y).Adj v w)) T ↔
        ∃ D : Finset (MV L), IsDominating (mdsG x y) D ∧ D.card ≤ 4 * L + 2) :
    4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := (mdsFamily L).not_disj_lowerBound A T fun x y => by
    change A.Accepts (mdsG x y) (fun v w => decide ((mdsG x y).Adj v w)) T ↔ _
    rw [hA x y, mdsG, lemma_2_1_le]
    simp [Protocol.disj]
  rw [mdsFamily_Ecut, card_mdsCut] at h
  have hc : Fintype.card (Idx L × Idx L) = 4 ^ L := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  calc 4 ^ L ≤ T * (2 * (4 * L * B)) + 2 := h
    _ = T * (8 * L * B) + 2 := by ring

/-- **Theorem 2.1**, in terms of `n = |V|`: `n² ≤ 256 · (8 T B log₂ n + 2)`, i.e.
`T = Ω(n² / (B log n)) = Ω(n² / log² n)` for `B = Θ(log n)`. -/
theorem theorem_2_1_n {σ : Type*} {B : ℕ} (A : Algorithm (MV L) (MV L → Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      A.Accepts (mdsG x y) (fun v w => decide ((mdsG x y).Adj v w)) T ↔
        ∃ D : Finset (MV L), IsDominating (mdsG x y) D ∧ D.card ≤ 4 * L + 2) :
    Fintype.card (MV L) ^ 2 ≤ 256 * (T * (8 * Nat.log 2 (Fintype.card (MV L)) * B) + 2) := by
  have h := theorem_2_1 A T hA
  rw [card_MV]
  have hL : L ≤ 2 ^ L := (Nat.lt_two_pow_self).le
  have hlog : L ≤ Nat.log 2 (4 * 2 ^ L + 12 * L) :=
    Nat.le_log_of_pow_le (by norm_num) (by omega)
  have h1 : (4 * 2 ^ L + 12 * L) ^ 2 ≤ 256 * 4 ^ L := by
    have : 4 * 2 ^ L + 12 * L ≤ 16 * 2 ^ L := by omega
    calc (4 * 2 ^ L + 12 * L) ^ 2 ≤ (16 * 2 ^ L) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 256 * 4 ^ L := by rw [mul_pow, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]; ring
  calc (4 * 2 ^ L + 12 * L) ^ 2 ≤ 256 * 4 ^ L := h1
    _ ≤ 256 * (T * (8 * L * B) + 2) := Nat.mul_le_mul_left _ h
    _ ≤ _ := by gcongr

end HardnessOptimization
