import Papers.PODC2023.TreeExplorationBFDN.Phase

/-!
# How robots move in one round

Every robot stays, moves to the parent, or moves to a child of its position; a robot with a
nonempty stack moves one step down towards its anchor whenever it is allowed to move.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [Fintype V] [DecidableEq V]
variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e)
include he

/-- The three possible moves of a robot. -/
theorem IsExec.pos_succ_cases (t : ℕ) (i : Fin k) :
    (e (t + 1)).pos i = (e t).pos i ∨ (e (t + 1)).pos i = T.parent ((e t).pos i) ∨
      ((e (t + 1)).pos i ≠ T.root ∧ T.parent ((e (t + 1)).pos i) = (e t).pos i) := by
  have hR := he.reanchorOK t
  have hM := he.moveOK t
  have hI := he.inv t
  by_cases hi : i ∈ act t
  · cases hb : bf0 T (act t) (e t) (e (t + 1)).anchor i
    · rcases tgt_dn_cases hM hi hb with h | ⟨_, h⟩
      · exact Or.inr (Or.inr ⟨h.1, h.2.1⟩)
      · exact Or.inr (Or.inl h)
    · obtain ⟨hs, hlt⟩ := bf0_true_spec hI hR hb
      rw [tgt_bf hM hi hb]
      exact Or.inr (Or.inr ⟨towards_ne_root hs hlt, parent_towards hs hlt⟩)
  · exact Or.inl (tgt_inactive hM hi)

theorem IsExec.depth_succ_le (t : ℕ) (i : Fin k) :
    T.depth ((e (t + 1)).pos i) ≤ T.depth ((e t).pos i) + 1 := by
  rcases he.pos_succ_cases t i with h | h | ⟨hne, h⟩
  · rw [h]; omega
  · rw [h]; have := depth_parent_le T ((e t).pos i); omega
  · rw [← h, ← T.depth_parent _ hne]

theorem IsExec.depth_le_succ (t : ℕ) (i : Fin k) :
    T.depth ((e t).pos i) ≤ T.depth ((e (t + 1)).pos i) + 1 := by
  rcases he.pos_succ_cases t i with h | h | ⟨hne, h⟩
  · rw [h]; omega
  · rw [h]
    by_cases hr : (e t).pos i = T.root
    · rw [hr, T.depth_root]; omega
    · rw [← T.depth_parent _ hr]
  · rw [← h]; have := depth_parent_le T ((e (t + 1)).pos i); omega

/-- Depth drops by at most one per round. -/
theorem IsExec.depth_le_add (t m : ℕ) (i : Fin k) :
    T.depth ((e t).pos i) ≤ T.depth ((e (t + m)).pos i) + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := he.depth_le_succ (t + m) i
    rw [show t + (m + 1) = t + m + 1 by omega]; omega

/-- A robot with a nonempty stack that is allowed to move goes one step down towards its anchor
(and keeps its anchor). -/
theorem IsExec.bf_step {t : ℕ} {i : Fin k} (hi : i ∈ act t) (hb : (e t).bf i = true) :
    (e (t + 1)).anchor i = (e t).anchor i ∧
      (e (t + 1)).pos i = towards T ((e t).pos i) ((e t).anchor i) ∧
      T.depth ((e (t + 1)).pos i) = T.depth ((e t).pos i) + 1 := by
  have hI := he.inv t
  obtain ⟨hpr, hs, hlt⟩ := hI.bf_spec i hb
  have hna := na_eq_of_ne_root (he.reanchorOK t) hpr
  have hb0 : bf0 T (act t) (e t) (e (t + 1)).anchor i = true := by
    rw [bf0_of_not (fun h => hpr h.2)]; exact hb
  have htg := tgt_bf (he.moveOK t) hi hb0
  rw [hna] at htg
  exact ⟨hna, htg, by rw [htg]; exact depth_towards hs hlt⟩

/-- A robot not at the root keeps its anchor. -/
theorem IsExec.anchor_succ_of_ne_root {t : ℕ} {i : Fin k} (h : (e t).pos i ≠ T.root) :
    (e (t + 1)).anchor i = (e t).anchor i :=
  na_eq_of_ne_root (he.reanchorOK t) h

/-- The stack flag after a round for a robot not at the root: it can only be cleared. -/
theorem IsExec.bf_succ_of_ne_root {t : ℕ} {i : Fin k} (h : (e t).pos i ≠ T.root)
    (hb : (e (t + 1)).bf i = true) : (e t).bf i = true := by
  have heq := he.eq_after t
  by_cases hi : i ∈ act t
  · have := after_bf_active (T := T) (c := e t) (na := (e (t + 1)).anchor) (tgt := (e (t + 1)).pos) hi
    rw [← heq] at this
    rw [this, bf0_of_not (fun h' => h h'.2)] at hb
    simp only [Bool.and_eq_true] at hb
    exact hb.1
  · have := after_bf_inactive (T := T) (c := e t) (na := (e (t + 1)).anchor) (tgt := (e (t + 1)).pos) hi
    rw [← heq] at this
    rwa [this] at hb

end Podc.TreeExplorationBFDN
