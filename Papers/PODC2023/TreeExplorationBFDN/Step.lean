import Papers.PODC2023.TreeExplorationBFDN.Tree

/-!
# Elementary facts about one round of BFDN

For a round with re-anchoring choices `na` and targets `tgt` satisfying `ReanchorOK` and `MoveOK`
we unfold the per-robot behaviour (blocked robot / breadth-first move / depth-next move).
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [DecidableEq V]
variable {act : Finset (Fin k)} {c : Config V k} {na tgt : Fin k → V}

section Reanchor

variable (hR : ∀ i, ReanchorOK T act c na i)
include hR

theorem na_eq_of_not {i : Fin k} (h : ¬ (i ∈ act ∧ c.pos i = T.root)) : na i = c.anchor i := by
  have := hR i; unfold ReanchorOK at this; rwa [ite_eq_right h] at this

theorem na_eq_of_ne_root {i : Fin k} (h : c.pos i ≠ T.root) : na i = c.anchor i :=
  na_eq_of_not hR (fun h' => h h'.2)

theorem na_eq_of_inactive {i : Fin k} (h : i ∉ act) : na i = c.anchor i :=
  na_eq_of_not hR (fun h' => h h'.1)

theorem na_cand {i : Fin k} (hi : i ∈ act) (hp : c.pos i = T.root) (hex : ∃ v, IsCand T c v) :
    IsCand T c (na i) ∧ ∀ v, IsCand T c v → load c na i (na i) ≤ load c na i v := by
  have := hR i; unfold ReanchorOK at this; rw [ite_eq_left ⟨hi, hp⟩] at this; exact this.1 hex

theorem na_root {i : Fin k} (hi : i ∈ act) (hp : c.pos i = T.root) (hex : ¬ ∃ v, IsCand T c v) :
    na i = T.root := by
  have := hR i; unfold ReanchorOK at this; rw [ite_eq_left ⟨hi, hp⟩] at this; exact this.2 hex

end Reanchor

section Move

variable (hM : ∀ i, MoveOK T act c na tgt i)
include hM

theorem tgt_inactive {i : Fin k} (hi : i ∉ act) : tgt i = c.pos i := by
  have := hM i; unfold MoveOK at this; rwa [ite_eq_right hi] at this

theorem tgt_bf {i : Fin k} (hi : i ∈ act) (hb : bf0 T act c na i = true) :
    tgt i = towards T (c.pos i) (na i) := by
  have := hM i; unfold MoveOK at this; rw [ite_eq_left hi, ite_eq_left hb] at this; exact this

theorem tgt_dn {i : Fin k} (hi : i ∈ act) (hb : bf0 T act c na i = false) :
    ((∃ w, FreeDangling T c tgt i w) → FreeDangling T c tgt i (tgt i)) ∧
      ((¬ ∃ w, FreeDangling T c tgt i w) → tgt i = T.parent (c.pos i)) := by
  have := hM i; unfold MoveOK at this; rw [ite_eq_left hi, ite_eq_right (by simp [hb])] at this; exact this

/-- In a depth-next move the robot either takes a free dangling edge or goes up. -/
theorem tgt_dn_cases {i : Fin k} (hi : i ∈ act) (hb : bf0 T act c na i = false) :
    FreeDangling T c tgt i (tgt i) ∨
      ((¬ ∃ w, FreeDangling T c tgt i w) ∧ tgt i = T.parent (c.pos i)) := by
  have h := tgt_dn hM hi hb
  by_cases hex : ∃ w, FreeDangling T c tgt i w
  · exact Or.inl (h.1 hex)
  · exact Or.inr ⟨hex, h.2 hex⟩

end Move

theorem bf0_of_root {i : Fin k} (hi : i ∈ act) (hp : c.pos i = T.root) :
    bf0 T act c na i = decide (na i ≠ T.root) := by
  unfold bf0; rw [ite_eq_left ⟨hi, hp⟩]

theorem bf0_of_not {i : Fin k} (h : ¬ (i ∈ act ∧ c.pos i = T.root)) :
    bf0 T act c na i = c.bf i := by
  unfold bf0; rw [ite_eq_right h]

theorem after_bf_active {i : Fin k} (hi : i ∈ act) :
    (after T act c na tgt).bf i = (bf0 T act c na i && decide (tgt i ≠ na i)) := by
  simp [after, hi]

theorem after_bf_inactive {i : Fin k} (hi : i ∉ act) : (after T act c na tgt).bf i = c.bf i := by
  simp [after, hi]

@[simp] theorem after_pos : (after T act c na tgt).pos = tgt := rfl
@[simp] theorem after_anchor : (after T act c na tgt).anchor = na := rfl
@[simp] theorem after_vis : (after T act c na tgt).vis = c.vis ∪ univ.image tgt := rfl

theorem vis_subset_after : c.vis ⊆ (after T act c na tgt).vis := by
  simp [after]

theorem tgt_mem_after (i : Fin k) : tgt i ∈ (after T act c na tgt).vis := by
  simp [after]

end Podc.TreeExplorationBFDN
