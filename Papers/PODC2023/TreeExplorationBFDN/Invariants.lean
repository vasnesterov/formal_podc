import Papers.PODC2023.TreeExplorationBFDN.Step

/-!
# Invariants of BFDN

The invariant `Inv` collects the structural facts behind the claims of Section 2 of the paper:

* the visited set is closed under taking parents;
* a robot with a nonempty stack (`bf`) is strictly above its anchor, on the path to it, and not
  at the root;
* a robot with an empty stack is inside the subtree `T(v_i)` of its anchor, or above it with the
  anchor already closed (on its way back to the root);
* anchors are never deeper than an open node (anchors are assigned at minimum open depth, and the
  minimum open depth never decreases);
* a robot anchored at an open non-root node is not at the root (it cannot have come back);
* (Claim 5 of the full version) every open non-root node `w` hosts in its subtree a robot whose
  anchor is strictly above `w` (its discoverer).

All facts hold for every set of robots allowed to move (`act`), hence both for Theorem 2.1 and
for the break-down model of Proposition 4.2.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [DecidableEq V]

variable (T) in
/-- The invariant of BFDN executions. -/
structure Inv (c : Config V k) : Prop where
  root_vis : T.root ∈ c.vis
  parent_vis : ∀ v ∈ c.vis, T.parent v ∈ c.vis
  pos_vis : ∀ i, c.pos i ∈ c.vis
  anchor_vis : ∀ i, c.anchor i ∈ c.vis
  bf_spec : ∀ i, c.bf i = true →
    c.pos i ≠ T.root ∧ InSub T (c.pos i) (c.anchor i) ∧ T.depth (c.pos i) < T.depth (c.anchor i)
  dn_spec : ∀ i, c.bf i = false →
    InSub T (c.anchor i) (c.pos i) ∨
      (InSub T (c.pos i) (c.anchor i) ∧ ¬ IsOpen T c (c.anchor i))
  anchor_min : ∀ i x, IsOpen T c x → T.depth (c.anchor i) ≤ T.depth x
  off_root : ∀ i, c.anchor i ≠ T.root → IsOpen T c (c.anchor i) → c.pos i ≠ T.root
  disc : ∀ w, w ≠ T.root → IsOpen T c w →
    ∃ j, InSub T w (c.pos j) ∧ T.depth (c.anchor j) < T.depth w

omit [DecidableEq V] in
theorem inv_init : Inv T (init T k : Config V k) where
  root_vis := by simp [init]
  parent_vis := by
    intro v hv; simp only [init, mem_singleton] at hv ⊢; rw [hv, T.parent_root]
  pos_vis := by simp [init]
  anchor_vis := by simp [init]
  bf_spec := by simp [init]
  dn_spec := fun i _ => Or.inl (InSub.refl _)
  anchor_min := by intro i x _; simp [init, T.depth_root]
  off_root := by intro i h; simp [init] at h
  disc := by
    intro w hw ho
    exact absurd (by simpa [init] using ho.1) hw

section Basic

variable {c : Config V k} (hI : Inv T c)
include hI

omit [DecidableEq V] in
theorem Inv.vis_of_inSub {x y : V} (h : InSub T x y) (hy : y ∈ c.vis) : x ∈ c.vis := by
  obtain ⟨n, rfl⟩ := h
  induction n generalizing y with
  | zero => exact hy
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih (hI.parent_vis _ hy)

end Basic

section Round

variable {act : Finset (Fin k)} {c : Config V k} {na tgt : Fin k → V}
  (hI : Inv T c) (hR : ∀ i, ReanchorOK T act c na i) (hM : ∀ i, MoveOK T act c na tgt i)

theorem isOpen_of_after {x : V} (hx : x ∈ c.vis) (h : IsOpen T (after T act c na tgt) x) :
    IsOpen T c x := by
  obtain ⟨_, w, hw, hp, hv⟩ := h
  exact ⟨hx, w, hw, hp, fun h' => hv (vis_subset_after h')⟩

include hI hR

/-- The (possibly new) anchor is at most as deep as any open node. -/
theorem na_depth_le (i : Fin k) {y : V} (hy : IsOpen T c y) : T.depth (na i) ≤ T.depth y := by
  by_cases h : i ∈ act ∧ c.pos i = T.root
  · by_cases hex : ∃ v, IsCand T c v
    · exact (na_cand hR h.1 h.2 hex).1.2 y hy
    · rw [na_root hR h.1 h.2 hex, T.depth_root]; exact Nat.zero_le _
  · rw [na_eq_of_not hR h]; exact hI.anchor_min i y hy

theorem na_vis (i : Fin k) : na i ∈ c.vis := by
  by_cases h : i ∈ act ∧ c.pos i = T.root
  · by_cases hex : ∃ v, IsCand T c v
    · exact (na_cand hR h.1 h.2 hex).1.1.1
    · rw [na_root hR h.1 h.2 hex]; exact hI.root_vis
  · rw [na_eq_of_not hR h]; exact hI.anchor_vis i

theorem bf0_true_spec {i : Fin k} (hb : bf0 T act c na i = true) :
    InSub T (c.pos i) (na i) ∧ T.depth (c.pos i) < T.depth (na i) := by
  by_cases h : i ∈ act ∧ c.pos i = T.root
  · rw [bf0_of_root h.1 h.2] at hb
    have hne : na i ≠ T.root := by simpa using hb
    rw [h.2]
    exact ⟨InSub.root _, by rw [T.depth_root]; exact RootedTree.depth_pos hne⟩
  · rw [bf0_of_not h] at hb
    rw [na_eq_of_not hR h]
    exact (hI.bf_spec i hb).2

theorem bf0_false_spec {i : Fin k} (hb : bf0 T act c na i = false) :
    InSub T (na i) (c.pos i) ∨ (InSub T (c.pos i) (na i) ∧ ¬ IsOpen T c (na i)) := by
  by_cases h : i ∈ act ∧ c.pos i = T.root
  · rw [bf0_of_root h.1 h.2] at hb
    have : na i = T.root := by simpa using hb
    rw [this]; exact Or.inl (InSub.root _)
  · rw [bf0_of_not h] at hb
    rw [na_eq_of_not hR h]
    exact hI.dn_spec i hb

include hM

theorem tgt_vis_or (i : Fin k) :
    tgt i ∈ c.vis ∨ (i ∈ act ∧ bf0 T act c na i = false ∧ FreeDangling T c tgt i (tgt i)) := by
  by_cases hi : i ∈ act
  · cases hb : bf0 T act c na i
    · rcases tgt_dn_cases hM hi hb with h | ⟨_, h⟩
      · exact Or.inr ⟨hi, rfl, h⟩
      · left; rw [h]; exact hI.parent_vis _ (hI.pos_vis i)
    · left
      rw [tgt_bf hM hi hb]
      exact hI.vis_of_inSub towards_inSub (na_vis hI hR i)
  · left; rw [tgt_inactive hM hi]; exact hI.pos_vis i

/-- Two robots taking dangling edges in the same round take different edges. -/
theorem tgt_inj_of_not_vis {i j : Fin k} (hi : tgt i ∉ c.vis) (hij : tgt i = tgt j) : i = j := by
  have hi' := (tgt_vis_or hI hR hM i).resolve_left hi
  have hj' := (tgt_vis_or hI hR hM j).resolve_left (hij ▸ hi)
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (hj'.2.2.2.2.2 i h)
  · exact h
  · exact absurd hij.symm (hi'.2.2.2.2.2 j h)

omit hI hR hM in
/-- If a robot cannot take a free dangling edge at its position, that position is closed after
the round (all its dangling edges were taken by other robots). -/
theorem not_open_after_of_noFree {i : Fin k} (h : ¬ ∃ w, FreeDangling T c tgt i w) :
    ¬ IsOpen T (after T act c na tgt) (c.pos i) := by
  rintro ⟨_, w, hw, hp, hv⟩
  apply h
  refine ⟨w, hw, hp, fun h' => hv (vis_subset_after h'), fun j _ hj => hv ?_⟩
  rw [← hj]; exact tgt_mem_after j

/-- New open nodes are children of old open nodes. -/
theorem open_after_cases {x : V} (h : IsOpen T (after T act c na tgt) x) :
    IsOpen T c x ∨ (x ∉ c.vis ∧ x ≠ T.root ∧ IsOpen T c (T.parent x)) := by
  by_cases hx : x ∈ c.vis
  · exact Or.inl (isOpen_of_after hx h)
  · right
    refine ⟨hx, ?_⟩
    have hmem := h.1
    simp only [after_vis, mem_union, mem_image, mem_univ, true_and] at hmem
    obtain ⟨j, rfl⟩ := hmem.resolve_left hx
    obtain ⟨_, _, ⟨hne, hp, hnv, _⟩⟩ := (tgt_vis_or hI hR hM j).resolve_left hx
    refine ⟨hne, ?_⟩
    rw [hp]; exact ⟨hI.pos_vis j, tgt j, hne, hp, hnv⟩

theorem exists_open_le {x : V} (h : IsOpen T (after T act c na tgt) x) :
    ∃ y, IsOpen T c y ∧ T.depth y ≤ T.depth x := by
  rcases open_after_cases hI hR hM h with h | ⟨_, hne, h⟩
  · exact ⟨x, h, le_rfl⟩
  · exact ⟨_, h, depth_parent_le T x⟩

theorem inv_after : Inv T (after T act c na tgt) where
  root_vis := vis_subset_after hI.root_vis
  parent_vis := by
    intro v hv
    simp only [after_vis, mem_union, mem_image, mem_univ, true_and] at hv
    rcases hv with hv | ⟨j, rfl⟩
    · exact vis_subset_after (hI.parent_vis _ hv)
    · rcases tgt_vis_or hI hR hM j with h | ⟨_, _, _, hp, _, _⟩
      · exact vis_subset_after (hI.parent_vis _ h)
      · rw [hp]; exact vis_subset_after (hI.pos_vis j)
  pos_vis := tgt_mem_after
  anchor_vis := fun i => vis_subset_after (na_vis hI hR i)
  bf_spec := by
    intro i hb
    simp only [after_pos, after_anchor]
    by_cases hi : i ∈ act
    · rw [after_bf_active hi] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨hb, hne⟩ := hb
      obtain ⟨hsub, hlt⟩ := bf0_true_spec hI hR hb
      rw [tgt_bf hM hi hb] at hne ⊢
      refine ⟨towards_ne_root hsub hlt, towards_inSub, ?_⟩
      have h1 := depth_towards hsub hlt
      rcases Nat.lt_or_ge (T.depth (towards T (c.pos i) (na i))) (T.depth (na i)) with h2 | h2
      · exact h2
      · exact absurd (InSub.eq_of_depth towards_inSub h2) hne
    · rw [after_bf_inactive hi] at hb
      rw [tgt_inactive hM hi, na_eq_of_inactive hR hi]
      exact hI.bf_spec i hb
  dn_spec := by
    intro i hb
    simp only [after_pos, after_anchor]
    by_cases hi : i ∈ act
    · rw [after_bf_active hi] at hb
      cases hb0 : bf0 T act c na i
      · rcases tgt_dn_cases hM hi hb0 with hd | ⟨hno, hup⟩
        · -- depth-next move down a dangling edge
          obtain ⟨hne0, hp, hnv, _⟩ := hd
          rcases bf0_false_spec hI hR hb0 with h | ⟨h, hcl⟩
          · exact Or.inl (InSub.child h hp)
          · exfalso
            have hopen : IsOpen T c (c.pos i) := ⟨hI.pos_vis i, tgt i, hne0, hp, hnv⟩
            have h1 := na_depth_le hI hR i hopen
            have h2 := InSub.depth_le h
            rw [InSub.eq_of_depth h h1] at hopen
            exact hcl hopen
        · -- depth-next move up
          rw [hup]
          rcases bf0_false_spec hI hR hb0 with h | ⟨h, hcl⟩
          · by_cases hpv : c.pos i = na i
            · right
              refine ⟨by rw [hpv]; exact InSub.parent_self _, ?_⟩
              rw [← hpv]; exact not_open_after_of_noFree (act := act) (na := na) hno
            · exact Or.inl (InSub.parent_of_ne h hpv)
          · right
            exact ⟨InSub.trans (InSub.parent_self _) h,
              fun ho => hcl (isOpen_of_after (na_vis hI hR i) ho)⟩
      · rw [hb0] at hb
        simp only [Bool.true_and, decide_eq_false_iff_not, not_not] at hb
        rw [hb]; exact Or.inl (InSub.refl _)
    · rw [after_bf_inactive hi] at hb
      rw [tgt_inactive hM hi, na_eq_of_inactive hR hi]
      rcases hI.dn_spec i hb with h | ⟨h, hcl⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, fun ho => hcl (isOpen_of_after (hI.anchor_vis i) ho)⟩
  anchor_min := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := exists_open_le hI hR hM hx
    exact (na_depth_le hI hR i hy).trans hyx
  off_root := by
    intro i hne ho
    simp only [after_pos, after_anchor] at hne ho ⊢
    have hoc : IsOpen T c (na i) := isOpen_of_after (na_vis hI hR i) ho
    by_cases hi : i ∈ act
    · cases hb0 : bf0 T act c na i
      · rcases tgt_dn_cases hM hi hb0 with hd | ⟨hno, hup⟩
        · exact hd.1
        · rw [hup]
          intro hroot
          rcases bf0_false_spec hI hR hb0 with h | ⟨h, hcl⟩
          · -- the robot is in the subtree of its anchor, at depth `≤ 1`
            have hpi : c.pos i ≠ T.root := by
              intro hp; rw [hp] at h
              exact hne (InSub.eq_of_depth h (by rw [T.depth_root]; omega))
            have hd1 : T.depth (c.pos i) = 1 := by
              have := T.depth_parent _ hpi; rw [hroot, T.depth_root] at this; omega
            have hdna : 1 ≤ T.depth (na i) := RootedTree.depth_pos hne
            have heq : na i = c.pos i := InSub.eq_of_depth h (by omega)
            exact not_open_after_of_noFree (act := act) (na := na) hno (heq ▸ ho)
          · exact hcl hoc
      · rw [tgt_bf hM hi hb0]
        obtain ⟨hsub, hlt⟩ := bf0_true_spec hI hR hb0
        exact towards_ne_root hsub hlt
    · rw [tgt_inactive hM hi]
      rw [na_eq_of_inactive hR hi] at hne hoc
      exact hI.off_root i hne hoc
  disc := by
    intro w hw ho
    simp only [after_pos, after_anchor]
    by_cases hwv : w ∈ c.vis
    · obtain ⟨j, hj, hdj⟩ := hI.disc w hw (isOpen_of_after hwv ho)
      have hpj : c.pos j ≠ T.root := InSub.ne_root_of_depth hj hw
      have hnaj : na j = c.anchor j := na_eq_of_ne_root hR hpj
      refine ⟨j, ?_, by rw [hnaj]; exact hdj⟩
      by_cases hi : j ∈ act
      · cases hb0 : bf0 T act c na j
        · rcases tgt_dn_cases hM hi hb0 with hd | ⟨hno, hup⟩
          · exact InSub.child hj hd.2.1
          · rw [hup]
            by_cases hpw : c.pos j = w
            · exact absurd (hpw ▸ ho) (not_open_after_of_noFree (act := act) (na := na) hno)
            · exact InSub.parent_of_ne hj hpw
        · exfalso
          rw [bf0_of_not (fun h => hpj h.2)] at hb0
          have h1 := (hI.bf_spec j hb0).2.2
          have h2 := InSub.depth_le hj
          omega
      · rw [tgt_inactive hM hi]; exact hj
    · rcases open_after_cases hI hR hM ho with h | ⟨_, _, hpo⟩
      · exact absurd h.1 hwv
      · have hmem := ho.1
        simp only [after_vis, mem_union, mem_image, mem_univ, true_and] at hmem
        obtain ⟨j, hj⟩ := hmem.resolve_left hwv
        refine ⟨j, by rw [hj]; exact InSub.refl _, ?_⟩
        have h1 := na_depth_le hI hR j hpo
        have h2 := T.depth_parent w hw
        omega

end Round

theorem Round.inv {act : Finset (Fin k)} {c c' : Config V k} (hI : Inv T c)
    (h : Round T act c c') : Inv T c' := by
  obtain ⟨na, tgt, hR, hM, rfl⟩ := h
  exact inv_after hI hR hM

theorem IsExec.inv {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e)
    (t : ℕ) : Inv T (e t) := by
  induction t with
  | zero => rw [he.1]; exact inv_init
  | succ t ih => exact (he.2 t).inv ih

end Podc.TreeExplorationBFDN
