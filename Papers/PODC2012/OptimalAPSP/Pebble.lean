import Mathlib

/-!
# The pebble traversal of Algorithm 1 and Lemma 1 of [HW12]

Holzer–Wattenhofer, *Optimal Distributed All Pairs Shortest Paths and Applications*, PODC 2012
([HW12]). Algorithm 1 sends a pebble `P` along a depth-first traversal of a BFS tree `T₁`; when
`P` enters a node `v` for the first time it waits one time slot and then starts `BFS_v`.

This file analyses the pebble *globally* (the distributed implementation in `Algorithm1.lean`
is shown to follow it step by step):

* `RTree V`: a rooted tree given by a parent function and a depth function.
* `PState`, `PState.step`: the global state of the pebble (position, waiting/ready, the set of
  entered nodes, and for every node the set of children not yet visited) and one time slot.
* `PState.done_all_entered`: after `3n - 1` slots the traversal is over and every node has been
  entered (Remark 3: the tree is traversed in `O(n)` time, here with the waiting slots counted).
* `firstVisit`, `firstVisit_le`: the slot in which the pebble enters `v`, at most `3n - 1`.
* `lemma1_sep`: if `u` is entered before `v` then `firstVisit u + 1 + d(u, v) ≤ firstVisit v`
  (the pebble walks along edges of `G` and waits one slot at `u`), and **Lemma 1**
  (`lemma1`): for `u ≠ v` and every node `w`, `firstVisit u + d(u, w) ≠ firstVisit v + d(v, w)`,
  i.e. `w` is never reached by the waves of `BFS_u` and `BFS_v` in the same slot.
-/

-- CSLib candidate: `RTree`, `PState` (generic depth-first token traversal of a rooted tree).

namespace Podc.OptimalAPSP

open Finset

/-- A rooted tree on `V`: parent function with `par root = root` and a depth function decreasing
by one along parent edges. -/
structure RTree (V : Type*) where
  /-- The root. -/
  root : V
  /-- The parent function. -/
  par : V → V
  /-- The depth function. -/
  dep : V → ℕ
  par_root : par root = root
  dep_par : ∀ v, v ≠ root → dep (par v) + 1 = dep v

namespace RTree

variable {V : Type*} (T : RTree V)

/-- `x` is an ancestor of `y` (or `y` itself). -/
def IsAnc (x y : V) : Prop := ∃ k, T.par^[k] y = x

lemma isAnc_refl (x : V) : T.IsAnc x x := ⟨0, rfl⟩

lemma dep_iterate_le (y : V) : ∀ k, T.dep (T.par^[k] y) ≤ T.dep y
  | 0 => le_rfl
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      by_cases h : T.par^[k] y = T.root
      · rw [h, T.par_root]; rw [← h]; exact dep_iterate_le y k
      · have := T.dep_par _ h; have := dep_iterate_le y k; omega

lemma dep_le_of_isAnc {x y : V} (h : T.IsAnc x y) : T.dep x ≤ T.dep y := by
  obtain ⟨k, rfl⟩ := h; exact T.dep_iterate_le y k

lemma iterate_dep_eq_root (y : V) : T.par^[T.dep y] y = T.root := by
  suffices ∀ d y, T.dep y = d → T.par^[d] y = T.root from this _ y rfl
  intro d
  induction d with
  | zero =>
    intro y hy
    by_contra h
    have := T.dep_par y h; omega
  | succ d ih =>
    intro y hy
    by_cases h : y = T.root
    · subst h; exact Function.iterate_fixed T.par_root _
    · rw [Function.iterate_succ_apply]
      exact ih _ (by have := T.dep_par y h; omega)

lemma isAnc_root (y : V) : T.IsAnc T.root y := ⟨_, T.iterate_dep_eq_root y⟩

/-- The children of `x`. -/
def IsKid (x c : V) : Prop := c ≠ T.root ∧ T.par c = x

lemma isAnc_par {y : V} (hy : y ≠ T.root) {x : V} (h : T.IsAnc x (T.par y)) : T.IsAnc x y := by
  obtain ⟨k, hk⟩ := h; exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

lemma isAnc_of_isKid {x c y : V} (hc : T.IsKid x c) (h : T.IsAnc y x) : T.IsAnc y c := by
  apply T.isAnc_par hc.1; rw [hc.2]; exact h

/-- Ancestors of `c` (a child of `x`) are `c` and the ancestors of `x`. -/
lemma isAnc_kid_iff {x c y : V} (hc : T.IsKid x c) : T.IsAnc y c ↔ y = c ∨ T.IsAnc y x := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact Or.inl hk.symm
    | succ k => right; refine ⟨k, ?_⟩; rw [Function.iterate_succ_apply, hc.2] at hk; exact hk
  · rintro (rfl | h)
    · exact T.isAnc_refl _
    · exact T.isAnc_of_isKid hc h

lemma not_isAnc_kid {x c : V} (hc : T.IsKid x c) : ¬ T.IsAnc c x := by
  intro h
  have h1 := T.dep_le_of_isAnc h
  have h2 := T.dep_par c hc.1
  rw [hc.2] at h2; omega

lemma not_isAnc_par {y : V} (hy : y ≠ T.root) : ¬ T.IsAnc y (T.par y) :=
  T.not_isAnc_kid ⟨hy, rfl⟩

/-- A proper descendant `y` of `x` lies below some child of `x`. -/
lemma exists_kid_of_isAnc {x y : V} (h : T.IsAnc x y) (hne : y ≠ x) :
    ∃ c, T.IsKid x c ∧ T.IsAnc c y := by
  classical
  have hex : ∃ k, T.par^[k] y = x := h
  let k := Nat.find hex
  have hk : T.par^[k] y = x := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0] at hk; exact hne hk
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨T.par^[j] y, ⟨?_, ?_⟩, ⟨j, rfl⟩⟩
  · intro hr
    have : T.par^[j] y = x := by
      rw [hj, Function.iterate_succ_apply', hr, T.par_root] at hk; rw [hr, hk]
    have := Nat.find_min hex (show j < k by omega)
    exact this ‹_›
  · rw [← Function.iterate_succ_apply' T.par j y, ← hj, hk]

end RTree

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The next target of a ready pebble at `v` with unvisited children `pend`: the smallest
unvisited child, else the parent (none at the root: the traversal is over). -/
def target (T : RTree V) (pend : Finset V) (v : V) : Option V :=
  if h : pend.Nonempty then some (pend.min' h) else if v = T.root then none else some (T.par v)

/-- Global state of the pebble. `ready = false`: the pebble has just entered `pos` for the first
time and waits one slot. -/
structure PState (V : Type*) where
  /-- Current position. -/
  pos : V
  /-- `false` while waiting at a newly entered node. -/
  ready : Bool
  /-- The nodes entered so far. -/
  ent : Finset V
  /-- Children of each node that the pebble has not yet been sent to. -/
  pend : V → Finset V

namespace PState

variable (T : RTree V)

/-- The children of `x` as a finset. -/
noncomputable def kids (x : V) : Finset V := by
  classical exact univ.filter fun c => T.IsKid x c

lemma mem_kids {x c : V} : c ∈ kids T x ↔ T.IsKid x c := by
  classical simp [kids]

/-- Initial state: the pebble has just entered the root. -/
noncomputable def init : PState V where
  pos := T.root
  ready := false
  ent := {T.root}
  pend := kids T

/-- The ready pebble at `g.pos` is sent to `x`. -/
def move (g : PState V) (x : V) : PState V where
  pos := x
  ready := decide (x ∈ g.ent)
  ent := insert x g.ent
  pend := Function.update g.pend g.pos ((g.pend g.pos).erase x)

@[simp] lemma move_pos (g : PState V) (x : V) : (g.move x).pos = x := rfl
@[simp] lemma move_ready (g : PState V) (x : V) : (g.move x).ready = decide (x ∈ g.ent) := rfl
@[simp] lemma move_ent (g : PState V) (x : V) : (g.move x).ent = insert x g.ent := rfl
@[simp] lemma move_pend (g : PState V) (x : V) :
    (g.move x).pend = Function.update g.pend g.pos ((g.pend g.pos).erase x) := rfl

/-- One time slot. -/
def step (g : PState V) : PState V :=
  if !g.ready then { g with ready := true }
  else match target T (g.pend g.pos) g.pos with
    | none => g
    | some x => g.move x

/-- The traversal is over: the pebble is ready at the root with nothing left to visit. -/
def Done (g : PState V) : Prop := g.ready = true ∧ target T (g.pend g.pos) g.pos = none

lemma step_of_done {g : PState V} (h : Done T g) : step T g = g := by
  simp [step, h.1, h.2]

/-- The invariant of the traversal. -/
structure Inv (g : PState V) : Prop where
  pos_ent : g.pos ∈ g.ent
  pend_kid : ∀ x c, c ∈ g.pend x → T.IsKid x c ∧ c ∉ g.ent
  pend_new : ∀ x, x ∉ g.ent → g.pend x = kids T x
  kid_cov : ∀ x ∈ g.ent, ∀ c, T.IsKid x c → c ∈ g.pend x ∨ c ∈ g.ent
  finished : ∀ x ∈ g.ent, ¬ T.IsAnc x g.pos → ∀ y, T.IsAnc x y → y ∈ g.ent
  anc_ent : ∀ x, T.IsAnc x g.pos → x ∈ g.ent

lemma inv_init : Inv T (init T) where
  pos_ent := by simp [init]
  pend_kid x c h := by
    rw [init, mem_kids] at h
    exact ⟨h, by simp [init, h.1]⟩
  pend_new x _ := rfl
  kid_cov x hx c hc := Or.inl ((mem_kids T).2 hc)
  finished x hx h := by
    simp only [init, mem_singleton] at hx; subst hx; exact absurd (T.isAnc_refl _) h
  anc_ent x h := by
    obtain ⟨k, hk⟩ := h
    have : T.par^[k] T.root = T.root := Function.iterate_fixed T.par_root k
    simp [init, ← hk, this]

/-- Potential: increases by exactly one in every slot before the end. -/
noncomputable def pot (g : PState V) : ℕ := by
  classical
  exact 2 * g.ent.card + (g.ent.filter fun x => ¬ T.IsAnc x g.pos).card + (if g.ready then 1 else 0)

lemma pot_init : pot T (init T) = 2 := by
  classical
  unfold pot init; simp; exact ⟨0, rfl⟩

lemma pot_le (g : PState V) (hg : Inv T g) : pot T g ≤ 3 * Fintype.card V := by
  classical
  unfold pot
  have h1 : g.ent.card ≤ Fintype.card V := card_le_univ _
  have h2 : (g.ent.filter fun x => ¬ T.IsAnc x g.pos).card ≤ Fintype.card V - 1 := by
    have : (g.ent.filter fun x => ¬ T.IsAnc x g.pos) ⊆ univ.erase g.pos := by
      intro x hx
      simp only [mem_filter] at hx
      simp only [mem_erase, mem_univ, and_true]
      rintro rfl; exact hx.2 (T.isAnc_refl _)
    have := card_le_card this
    rw [card_erase_of_mem (mem_univ _), card_univ] at this
    exact this
  have h3 : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨g.pos⟩
  split_ifs <;> omega

/-- The main step lemma: before the end, the invariant is preserved and the potential grows by
one. -/
lemma step_spec (g : PState V) (hg : Inv T g) (hd : ¬ Done T g) :
    Inv T (step T g) ∧ pot T (step T g) = pot T g + 1 := by
  classical
  cases hr : g.ready with
  | false =>
    have hs : step T g = { g with ready := true } := by simp [step, hr]
    rw [hs]
    refine ⟨⟨hg.pos_ent, hg.pend_kid, hg.pend_new, hg.kid_cov, hg.finished, hg.anc_ent⟩, ?_⟩
    simp [pot, hr]
  | true =>
    have hrt : g.ready = true := hr
    unfold Done at hd
    rw [hr] at hd
    simp only [true_and] at hd
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hd
    have hs : step T g = g.move x := by
      unfold step; simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hx]
    rw [hs]
    unfold target at hx
    split_ifs at hx with hne hroot
    · -- descend to the smallest unvisited child `x`
      simp only [Option.some.injEq] at hx
      have hxm : x ∈ g.pend g.pos := hx ▸ min'_mem _ _
      obtain ⟨hkid, hxe⟩ := hg.pend_kid _ _ hxm
      have hxpos : x ≠ g.pos := fun h => hxe (h ▸ hg.pos_ent)
      have hanc : ∀ y, T.IsAnc y x ↔ y = x ∨ T.IsAnc y g.pos := fun y => T.isAnc_kid_iff hkid
      refine ⟨⟨by simp, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try simp only [move_pos, move_ready, move_ent, move_pend]
      · intro y c hc
        by_cases hy : y = g.pos
        · subst hy
          rw [Function.update_self, mem_erase] at hc
          obtain ⟨h1, h2⟩ := hg.pend_kid _ _ hc.2
          exact ⟨h1, by simp [hc.1, h2]⟩
        · rw [Function.update_of_ne hy] at hc
          obtain ⟨h1, h2⟩ := hg.pend_kid _ _ hc
          refine ⟨h1, ?_⟩
          simp only [mem_insert, not_or]
          refine ⟨?_, h2⟩
          rintro rfl; exact hy (h1.2.symm.trans hkid.2)
      · intro y hy
        simp only [mem_insert, not_or] at hy
        have : y ≠ g.pos := fun h => hy.2 (h ▸ hg.pos_ent)
        rw [Function.update_of_ne this]; exact hg.pend_new y hy.2
      · intro y hy c hc
        simp only [mem_insert] at hy ⊢
        rcases hy with rfl | hy
        · left
          rw [Function.update_of_ne hxpos, hg.pend_new _ hxe]; exact (mem_kids T).2 hc
        · rcases hg.kid_cov y hy c hc with h | h
          · by_cases hyp : y = g.pos
            · subst hyp
              by_cases hcx : c = x
              · right; left; exact hcx
              · left; rw [Function.update_self, mem_erase]; exact ⟨hcx, h⟩
            · left; rw [Function.update_of_ne hyp]; exact h
          · right; right; exact h
      · intro y hy hna z hz
        simp only [mem_insert] at hy ⊢
        rw [hanc] at hna
        push_neg at hna
        rcases hy with rfl | hy
        · exact absurd rfl hna.1
        · right; exact hg.finished y hy hna.2 z hz
      · intro y hy
        rw [hanc] at hy
        simp only [mem_insert]
        rcases hy with rfl | hy
        · left; rfl
        · right; exact hg.anc_ent y hy
      · have hp : pot T (g.move x) = 2 * (insert x g.ent).card +
            ((insert x g.ent).filter (fun y => ¬ T.IsAnc y x)).card := by
          unfold pot; simp [hxe]; congr
        have hp' : pot T g = 2 * g.ent.card + (g.ent.filter (fun y => ¬ T.IsAnc y g.pos)).card + 1 := by
          unfold pot; simp [hrt]
        rw [hp, hp', card_insert_of_notMem hxe]
        have : (insert x g.ent).filter (fun y => ¬ T.IsAnc y x) =
            g.ent.filter (fun y => ¬ T.IsAnc y g.pos) := by
          ext y
          simp only [mem_filter, mem_insert, hanc, not_or]
          constructor
          · rintro ⟨rfl | h1, h2, h3⟩
            · exact absurd rfl h2
            · exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩
            exact ⟨Or.inr h1, fun h => hxe (h ▸ h1), h3⟩
        rw [this]; ring
    · -- ascend to the parent
      simp only [Option.some.injEq] at hx
      subst hx
      have hpe : T.par g.pos ∈ g.ent := hg.anc_ent _ ⟨1, rfl⟩
      have hemp : g.pend g.pos = ∅ := not_nonempty_iff_eq_empty.1 hne
      have hpend : Function.update g.pend g.pos ((g.pend g.pos).erase (T.par g.pos)) = g.pend := by
        rw [hemp, Finset.erase_empty, ← hemp, Function.update_eq_self]
      have hins : insert (T.par g.pos) g.ent = g.ent := insert_eq_of_mem hpe
      have hmv : g.move (T.par g.pos) = { g with pos := T.par g.pos, ready := true } := by
        unfold move; rw [hpend, hins]; simp [hpe]
      rw [hmv]
      have hanc : ∀ y, T.IsAnc y g.pos ↔ y = g.pos ∨ T.IsAnc y (T.par g.pos) :=
        fun y => T.isAnc_kid_iff ⟨hroot, rfl⟩
      refine ⟨⟨hpe, hg.pend_kid, hg.pend_new, hg.kid_cov, ?_, ?_⟩, ?_⟩
      · intro y hy hna z hz
        by_cases hyp : y = g.pos
        · subst hyp
          -- the subtree of `pos` is finished
          by_cases hzp : z = g.pos
          · rw [hzp]; exact hg.pos_ent
          · obtain ⟨c, hc, hcz⟩ := T.exists_kid_of_isAnc hz hzp
            have hce : c ∈ g.ent := by
              rcases hg.kid_cov _ hg.pos_ent c hc with h | h
              · rw [hemp] at h; simp at h
              · exact h
            exact hg.finished c hce (T.not_isAnc_kid hc) z hcz
        · exact hg.finished y hy (by rw [hanc]; push_neg; exact ⟨hyp, hna⟩) z hz
      · intro y hy; exact hg.anc_ent y (T.isAnc_par hroot hy)
      · simp only [pot, hrt, hpe, decide_true, ↓reduceIte]
        have : g.ent.filter (fun y => ¬ T.IsAnc y (T.par g.pos)) =
            insert g.pos (g.ent.filter (fun y => ¬ T.IsAnc y g.pos)) := by
          ext y
          simp only [mem_filter, mem_insert, hanc, not_or]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases hyp : y = g.pos
            · left; exact hyp
            · right; exact ⟨h1, hyp, h2⟩
          · rintro (rfl | ⟨h1, _, h3⟩)
            · exact ⟨hg.pos_ent, T.not_isAnc_par hroot⟩
            · exact ⟨h1, h3⟩
        rw [this, card_insert_of_notMem (by simp [T.isAnc_refl])]; ring

/-- At the end of the traversal every node has been entered. -/
lemma done_all_entered (g : PState V) (hg : Inv T g) (hd : Done T g) (v : V) : v ∈ g.ent := by
  obtain ⟨-, ht⟩ := hd
  unfold target at ht
  split_ifs at ht with hne hroot
  have hemp : g.pend g.pos = ∅ := not_nonempty_iff_eq_empty.1 hne
  by_cases hv : v = g.pos
  · rw [hv]; exact hg.pos_ent
  · have : T.IsAnc g.pos v := hroot ▸ T.isAnc_root v
    obtain ⟨c, hc, hcv⟩ := T.exists_kid_of_isAnc this hv
    have hce : c ∈ g.ent := by
      rcases hg.kid_cov _ hg.pos_ent c hc with h | h
      · rw [hemp] at h; simp at h
      · exact h
    refine hg.finished c hce ?_ v hcv
    intro h
    obtain ⟨k, hk⟩ := h
    rw [hroot, Function.iterate_fixed T.par_root] at hk
    exact hc.1 hk.symm

/-- The state after `s` slots. -/
noncomputable def iter (s : ℕ) : PState V := (step T)^[s] (init T)

lemma iter_succ (s : ℕ) : iter T (s + 1) = step T (iter T s) :=
  Function.iterate_succ_apply' _ _ _

lemma iter_inv_pot (s : ℕ) : Inv T (iter T s) ∧ (Done T (iter T s) ∨ pot T (iter T s) = s + 2) := by
  induction s with
  | zero => exact ⟨inv_init T, Or.inr (pot_init T)⟩
  | succ s ih =>
    rw [iter_succ]
    by_cases hd : Done T (iter T s)
    · rw [step_of_done T hd]; exact ⟨ih.1, Or.inl hd⟩
    · obtain ⟨h1, h2⟩ := step_spec T _ ih.1 hd
      refine ⟨h1, Or.inr ?_⟩
      rcases ih.2 with h | h
      · exact absurd h hd
      · omega

lemma iter_inv (s : ℕ) : Inv T (iter T s) := (iter_inv_pot T s).1

/-- **Remark 3**: the traversal ends within `3n - 1` slots (`n - 1` descents, `n - 1` ascents
and `n` waiting slots). -/
lemma iter_done : Done T (iter T (3 * Fintype.card V - 1)) := by
  rcases (iter_inv_pot T (3 * Fintype.card V - 1)).2 with h | h
  · exact h
  · have := pot_le T (iter T (3 * Fintype.card V - 1)) (iter_inv T _)
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨T.root⟩
    omega

lemma ent_mono_succ (s : ℕ) : (iter T s).ent ⊆ (iter T (s + 1)).ent := by
  rw [iter_succ]
  unfold step
  split
  · exact subset_rfl
  · split
    · exact subset_rfl
    · exact subset_insert _ _

lemma ent_mono {s s' : ℕ} (h : s ≤ s') : (iter T s).ent ⊆ (iter T s').ent := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (ent_mono_succ T _)

lemma all_entered (v : V) : v ∈ (iter T (3 * Fintype.card V - 1)).ent :=
  done_all_entered T _ (iter_inv T _) (iter_done T) v

/-- When a node is entered, the pebble is there and waits. -/
lemma step_cases (g : PState V) :
    (g.ready = false ∧ step T g = { g with ready := true }) ∨ step T g = g ∨
      ∃ x, step T g = g.move x := by
  unfold step
  cases h : g.ready
  · left; simp
  · right
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · left; rfl
    · right; exact ⟨_, rfl⟩

lemma enter_spec {s : ℕ} {v : V} (h1 : v ∉ (iter T s).ent) (h2 : v ∈ (iter T (s + 1)).ent) :
    (iter T (s + 1)).pos = v ∧ (iter T (s + 1)).ready = false := by
  rw [iter_succ] at h2 ⊢
  rcases step_cases T (iter T s) with ⟨-, h⟩ | h | ⟨x, h⟩ <;> rw [h] at h2 ⊢
  · exact absurd h2 h1
  · exact absurd h2 h1
  · simp only [move_ent, mem_insert] at h2
    rcases h2 with rfl | h2
    · simp [h1]
    · exact absurd h2 h1

lemma wait_spec {s : ℕ} (h : (iter T s).ready = false) : (iter T (s + 1)).pos = (iter T s).pos := by
  rw [iter_succ]; simp [step, h]

/-- The pebble moves along tree edges. -/
lemma move_spec (s : ℕ) :
    (iter T (s + 1)).pos = (iter T s).pos ∨ T.IsKid (iter T s).pos (iter T (s + 1)).pos ∨
      ((iter T s).pos ≠ T.root ∧ T.par (iter T s).pos = (iter T (s + 1)).pos) := by
  have hinv := iter_inv T s
  rw [iter_succ]
  unfold step
  split
  · left; rfl
  · split
    · left; rfl
    · rename_i x hx
      simp only [move]
      unfold target at hx
      split_ifs at hx with hne hroot
      · simp only [Option.some.injEq] at hx
        right; left
        exact (hinv.pend_kid _ _ (hx ▸ min'_mem _ _)).1
      · simp only [Option.some.injEq] at hx
        right; right; exact ⟨hroot, hx⟩

/-- The slot in which the pebble enters `v` (`0` for the root). -/
noncomputable def firstVisit (v : V) : ℕ := by
  classical exact Nat.find (⟨_, all_entered T v⟩ : ∃ s, v ∈ (iter T s).ent)

lemma firstVisit_spec (v : V) : v ∈ (iter T (firstVisit T v)).ent := by
  classical exact Nat.find_spec (⟨_, all_entered T v⟩ : ∃ s, v ∈ (iter T s).ent)

lemma not_mem_of_lt_firstVisit {v : V} {s : ℕ} (h : s < firstVisit T v) : v ∉ (iter T s).ent := by
  classical exact Nat.find_min (⟨_, all_entered T v⟩ : ∃ s, v ∈ (iter T s).ent) h

lemma mem_iff_firstVisit_le {v : V} {s : ℕ} : v ∈ (iter T s).ent ↔ firstVisit T v ≤ s := by
  constructor
  · intro h; by_contra h'; exact not_mem_of_lt_firstVisit T (not_le.1 h') h
  · intro h; exact ent_mono T h (firstVisit_spec T v)

/-- **Remark 3** (with waiting slots): every node is entered within `3n - 1` slots. -/
lemma firstVisit_le (v : V) : firstVisit T v ≤ 3 * Fintype.card V - 1 :=
  (mem_iff_firstVisit_le T).1 (all_entered T v)

lemma firstVisit_root : firstVisit T T.root = 0 :=
  Nat.eq_zero_of_le_zero ((mem_iff_firstVisit_le T).1 (by simp [iter, init]))

/-- In slot `firstVisit v` the pebble is at `v`, and it is still there one slot later. -/
lemma pos_firstVisit (v : V) :
    (iter T (firstVisit T v)).pos = v ∧ (iter T (firstVisit T v + 1)).pos = v := by
  rcases Nat.eq_zero_or_pos (firstVisit T v) with h | h
  · have hv : v ∈ (iter T 0).ent := h ▸ firstVisit_spec T v
    simp only [iter, Function.iterate_zero, id, init, mem_singleton] at hv
    subst hv
    rw [h]
    have h0 : (iter T 0).pos = T.root := rfl
    exact ⟨h0, (wait_spec T rfl).trans h0⟩
  · obtain ⟨k, hk⟩ : ∃ k, firstVisit T v = k + 1 := ⟨firstVisit T v - 1, by omega⟩
    have h1 : v ∉ (iter T k).ent := not_mem_of_lt_firstVisit T (by omega)
    have h2 : v ∈ (iter T (k + 1)).ent := by
      rw [← hk]; exact firstVisit_spec T v
    obtain ⟨hp, hw⟩ := enter_spec T h1 h2
    rw [hk]
    exact ⟨hp, (wait_spec T hw).trans hp⟩

lemma firstVisit_injective : Function.Injective (firstVisit T) := by
  intro u v h
  rw [← (pos_firstVisit T u).1, ← (pos_firstVisit T v).1, h]

variable {T}

/-- The positions of the pebble form a walk in any graph containing the tree edges. -/
lemma dist_pos_le (G : SimpleGraph V) (hG : ∀ v, v ≠ T.root → G.Adj v (T.par v)) (s : ℕ) :
    ∀ j, G.dist (iter T s).pos (iter T (s + j)).pos ≤ j ∧
      G.Reachable (iter T s).pos (iter T (s + j)).pos
  | 0 => by simp
  | j + 1 => by
      obtain ⟨ih1, ih2⟩ := dist_pos_le G hG s j
      have hstep : (iter T (s + j + 1)).pos = (iter T (s + j)).pos ∨
          G.Adj (iter T (s + j)).pos (iter T (s + j + 1)).pos := by
        rcases move_spec T (s + j) with h | h | h
        · left; exact h
        · right; have := hG _ h.1; rw [h.2] at this; exact this.symm
        · right; rw [← h.2]; exact hG _ h.1
      rw [← add_assoc]
      rcases hstep with h | h
      · rw [h]; exact ⟨by omega, ih2⟩
      · obtain ⟨p, hp⟩ := ih2.exists_walk_length_eq_dist
        refine ⟨?_, ih2.trans h.reachable⟩
        calc G.dist _ _ ≤ (p.concat h).length := SimpleGraph.dist_le _
          _ = G.dist (iter T s).pos (iter T (s + j)).pos + 1 := by simp [hp]
          _ ≤ j + 1 := by omega

/-- The separation property behind Lemma 1: if the pebble enters `u` before `v`, then it waited
one slot at `u` and walked at least `d(u, v)` steps. -/
lemma lemma1_sep (G : SimpleGraph V) (hG : ∀ v, v ≠ T.root → G.Adj v (T.par v)) {u v : V}
    (h : firstVisit T u < firstVisit T v) :
    firstVisit T u + 1 + G.dist u v ≤ firstVisit T v ∧ G.Reachable u v := by
  obtain ⟨-, hu⟩ := pos_firstVisit T u
  obtain ⟨hv, -⟩ := pos_firstVisit T v
  have := dist_pos_le G hG (firstVisit T u + 1) (firstVisit T v - (firstVisit T u + 1))
  rw [show firstVisit T u + 1 + (firstVisit T v - (firstVisit T u + 1)) = firstVisit T v by omega,
    hu, hv] at this
  exact ⟨by omega, this.2⟩

/-- **Lemma 1 of [HW12].** In Algorithm 1, no node `w` is reached by the waves of two different
breadth-first searches in the same time slot: `BFS_u` (started when the pebble enters `u`)
reaches `w` in slot `firstVisit u + d(u, w)`, and these slots are pairwise distinct. -/
theorem lemma1 (G : SimpleGraph V) (hconn : G.Connected)
    (hG : ∀ v, v ≠ T.root → G.Adj v (T.par v)) {u v : V} (huv : u ≠ v) (w : V) :
    firstVisit T u + G.dist u w ≠ firstVisit T v + G.dist v w := by
  have key : ∀ u v, firstVisit T u < firstVisit T v →
      firstVisit T u + G.dist u w < firstVisit T v + G.dist v w := by
    intro u v h
    have h1 := (lemma1_sep G hG h).1
    have h2 := hconn.dist_triangle (u := u) (v := v) (w := w)
    omega
  rcases lt_trichotomy (firstVisit T u) (firstVisit T v) with h | h | h
  · exact (key u v h).ne
  · exact absurd (firstVisit_injective T h) huv
  · exact (key v u h).ne'

end PState

end Podc.OptimalAPSP
