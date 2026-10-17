import Papers.PODC2019.HardnessOptimization.MDSTheorem
import Cslib.Computability.Distributed.Congest.Gather
import Mathlib

/-!
# Connectivity of the MDS lower-bound graphs

The two layers (`A₁, B₁` with their gadgets, and `A₂, B₂` with theirs) are joined only by the input
edges. Hence `G_{0,0}` is **disconnected** (`mdsGraph_zero_not_connected`), while `G_{x,y}` is
connected as soon as `x ≠ 0` or `y ≠ 0` (`mdsGraph_connected`). CONGEST algorithms are usually only
required to work on connected networks; `theorem_2_1_connected` shows that Theorem 2.1 still holds
for such algorithms, because the fooling-set argument never uses the input pair `(0, 0)`.
-/

namespace HardnessOptimization

open Finset Cslib.Congest Cslib.CommunicationComplexity

/-- The layer of a vertex (`false` = rows `A₁, B₁` and their gadgets). -/
def MV.layer {L : ℕ} : MV L → Bool
  | row _ ℓ _ => ℓ
  | gad _ ℓ _ _ => ℓ

variable {L : ℕ} {x y : Idx L → Idx L → Bool}

/-- Without input edges, adjacency preserves the layer. -/
lemma layer_eq_of_adj_zero {u v : MV L}
    (h : (mdsGraph (fun _ _ => false) (fun _ _ => false)).Adj u v) : u.layer = v.layer := by
  cases u <;> cases v <;>
    simp_all [adj_row_row, adj_row_gad, adj_gad_row, adj_gad_gad, redge, xy, MV.layer]

lemma mdsGraph_zero_not_connected [NeZero L] :
    ¬(mdsGraph (L := L) (fun _ _ => false) (fun _ _ => false)).Connected := by
  intro hc
  obtain ⟨p⟩ := hc.preconnected (MV.gad false false (0 : Fin L) 0) (MV.gad false true 0 0)
  have : ∀ {u v : MV L} (q : (mdsGraph (fun _ _ => false) (fun _ _ => false)).Walk u v),
      u.layer = v.layer := by
    intro u v q
    induction q with
    | nil => rfl
    | cons h _ ih => exact (layer_eq_of_adj_zero h).trans ih
  simpa [MV.layer] using this p

section Conn

variable [NeZero L]

omit [NeZero L] in
lemma adj_cyc {s s' ℓ : Bool} {h : Fin L} {κ κ' : Fin 3} (hc : CycAdj s κ s' κ') :
    (mdsGraph x y).Adj (.gad s ℓ h κ) (.gad s' ℓ h κ') :=
  (adj_gad_gad x y).2 ⟨rfl, rfl, hc⟩

omit [NeZero L] in
lemma reach_cycle (ℓ : Bool) (h : Fin L) (s : Bool) (κ : Fin 3) :
    (mdsGraph x y).Reachable (.gad false ℓ h 0) (.gad s ℓ h κ) := by
  have r1 := (adj_cyc (x := x) (y := y) (ℓ := ℓ) (h := h)
    (show CycAdj false 0 false 1 by decide)).reachable
  have r2 := (adj_cyc (x := x) (y := y) (ℓ := ℓ) (h := h)
    (show CycAdj false 1 false 2 by decide)).reachable
  have r3 := (adj_cyc (x := x) (y := y) (ℓ := ℓ) (h := h)
    (show CycAdj false 2 true 0 by decide)).reachable
  have r4 := (adj_cyc (x := x) (y := y) (ℓ := ℓ) (h := h)
    (show CycAdj true 0 true 1 by decide)).reachable
  have r5 := (adj_cyc (x := x) (y := y) (ℓ := ℓ) (h := h)
    (show CycAdj true 1 true 2 by decide)).reachable
  cases s <;> fin_cases κ
  · rfl
  · exact r1
  · exact r1.trans r2
  · exact r1.trans (r2.trans r3)
  · exact r1.trans (r2.trans (r3.trans r4))
  · exact r1.trans (r2.trans (r3.trans (r4.trans r5)))

/-- Each layer is connected. -/
lemma reach_layer (ℓ : Bool) (v : MV L) (hv : v.layer = ℓ) :
    (mdsGraph x y).Reachable (.gad false ℓ 0 0) v := by
  have hbase : ∀ h : Fin L, (mdsGraph x y).Reachable (.gad false ℓ 0 0) (.gad false ℓ h 0) := by
    intro h
    have a1 : (mdsGraph x y).Adj (.gad false ℓ 0 0) (.row false ℓ fun _ => false) :=
      (adj_gad_row x y).2 ⟨rfl, rfl, by simp [bitK]⟩
    have a2 : (mdsGraph x y).Adj (.row false ℓ fun _ => false) (.gad false ℓ h 0) :=
      (adj_row_gad x y).2 ⟨rfl, rfl, by simp [bitK]⟩
    exact a1.reachable.trans a2.reachable
  cases v with
  | row s ℓ' i =>
    simp only [MV.layer] at hv
    subst hv
    have a : (mdsGraph x y).Adj (.gad s ℓ' 0 (bitK (i 0))) (.row s ℓ' i) :=
      (adj_gad_row x y).2 ⟨rfl, rfl, rfl⟩
    exact (reach_cycle ℓ' 0 s _).trans a.reachable
  | gad s ℓ' h κ =>
    simp only [MV.layer] at hv
    subst hv
    exact (hbase h).trans (reach_cycle ℓ' h s κ)

/-- `G_{x,y}` is connected as soon as one input is non-zero. -/
lemma mdsGraph_connected (hxy : (∃ i j, x i j = true) ∨ ∃ i j, y i j = true) :
    (mdsGraph x y).Connected := by
  have hlink : (mdsGraph x y).Reachable (.gad false false (0 : Fin L) 0) (.gad false true 0 0) := by
    rcases hxy with ⟨i, j, hij⟩ | ⟨i, j, hij⟩
    · have a : (mdsGraph x y).Adj (.row false false i) (.row false true j) :=
        (adj_row_row x y).2 ⟨rfl, rfl, by simpa [redge, xy] using hij⟩
      exact (reach_layer false _ rfl).trans (a.reachable.trans (reach_layer true _ rfl).symm)
    · have a : (mdsGraph x y).Adj (.row true false i) (.row true true j) :=
        (adj_row_row x y).2 ⟨rfl, rfl, by simpa [redge, xy] using hij⟩
      exact (reach_layer false _ rfl).trans (a.reachable.trans (reach_layer true _ rfl).symm)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨.gad false false 0 0, fun v => ?_⟩
  cases hv : v.layer
  · exact reach_layer false v hv
  · exact hlink.trans (reach_layer true v hv)

/-- **Theorem 2.1 for algorithms that only work on connected networks.** If a deterministic
CONGEST algorithm with `B`-bit messages decides, in `T` rounds, on every *connected* `G_{x,y}`
whether there is a dominating set of size at most `4 log k + 2`, then `k² ≤ 8 T B log k + 2`. -/
theorem theorem_2_1_connected {σ : Type*} {B : ℕ} (A : Algorithm (MV L) (MV L → Bool) σ B)
    (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool, (mdsG x y).Connected →
      (A.Accepts (mdsG x y) (fun v w => decide ((mdsG x y).Adj v w)) T ↔
        ∃ D : Finset (MV L), IsDominating (mdsG x y) D ∧ D.card ≤ 4 * L + 2)) :
    4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := (mdsFamily L).not_disj_lowerBound_of_ne_zero A T fun x y hxy => by
    change A.Accepts (mdsG x y) (fun v w => decide ((mdsG x y).Adj v w)) T ↔ _
    have hc : (mdsG x y).Connected := mdsGraph_connected (by
      rcases hxy with ⟨⟨i, j⟩, h⟩ | ⟨⟨i, j⟩, h⟩
      · exact Or.inl ⟨i, j, h⟩
      · exact Or.inr ⟨i, j, h⟩)
    rw [hA x y hc, mdsG, lemma_2_1_le]
    simp [Protocol.disj]
  rw [mdsFamily_Ecut, card_mdsCut] at h
  have hc : Fintype.card (Idx L × Idx L) = 4 ^ L := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  calc 4 ^ L ≤ T * (2 * (4 * L * B)) + 2 := h
    _ = T * (8 * L * B) + 2 := by ring

omit [NeZero L] in
/-- **Non-vacuity** of `theorem_2_1_connected`: its hypothesis is satisfiable, e.g. by the
full-information gathering algorithm with `T = n` rounds and `n + n²`-bit messages. -/
theorem theorem_2_1_hyp_satisfiable :
    ∃ (B : ℕ) (A : Algorithm (MV L) (MV L → Bool) (Know (MV L)) B) (T : ℕ),
      ∀ x y : Idx L × Idx L → Bool, (mdsG x y).Connected →
        (A.Accepts (mdsG x y) (fun v w => decide ((mdsG x y).Adj v w)) T ↔
          ∃ D : Finset (MV L), IsDominating (mdsG x y) D ∧ D.card ≤ 4 * L + 2) :=
  ⟨_, gatherAlg fun M => ∃ D : Finset (MV L),
      IsDominating (SimpleGraph.fromRel fun a b => M a b = true) D ∧ D.card ≤ 4 * L + 2,
    Fintype.card (MV L), fun x y hc =>
      gather_accepts_graph (mdsG x y)
        (fun G => ∃ D : Finset (MV L), IsDominating G D ∧ D.card ≤ 4 * L + 2) hc⟩

end Conn

end HardnessOptimization
