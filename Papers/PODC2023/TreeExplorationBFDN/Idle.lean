import Papers.PODC2023.TreeExplorationBFDN.Motion

/-!
# Idle rounds and the end of the exploration (Claim 1 of the full version, corrected)

A robot allowed to move stays put only at the root, either because no dangling edge is left
(the tree is explored) or because all dangling edges at the root are taken by other robots in this
round (this happens in at most one round). Once the tree is explored, every robot is back at the
root within `2D − 1` rounds (a robot may still have to finish a breadth-first trip). Hence in the
synchronous model at most `2D` rounds before termination contain an idle robot
(`card_idleRounds_le`).

The paper (Claim 1) states `D + 1` instead of `2D`; this is wrong (see `Counterexamples.lean`)
but harmless: `2D` is still absorbed by the bound of Theorem 2.1.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [Fintype V] [DecidableEq V]

/-- If some node is open then some open node has minimum depth (a candidate anchor). -/
theorem exists_cand {c : Config V k} {x : V} (hx : IsOpen T c x) : ∃ v, IsCand T c v := by
  classical
  obtain ⟨v, hv, hmin⟩ := (univ.filter fun y => IsOpen T c y).exists_min_image T.depth
    ⟨x, by simpa using hx⟩
  simp only [mem_filter, mem_univ, true_and] at hv hmin
  exact ⟨v, hv, fun y hy => hmin y hy⟩

/-- With no open node, the whole tree is visited. -/
theorem vis_eq_univ_of_no_open {c : Config V k} (hI : Inv T c) (h : ∀ x, ¬ IsOpen T c x) :
    c.vis = univ := by
  rw [eq_univ_iff_forall]
  intro x
  induction hd : T.depth x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_contra hx
    have hxr : x ≠ T.root := fun h' => hx (h' ▸ hI.root_vis)
    have hp : T.parent x ∈ c.vis := by
      by_contra hp
      exact hp (ih _ (by rw [← hd]; exact RootedTree.depth_parent_lt hxr) _ rfl)
    exact h _ ⟨hp, x, hxr, rfl, hx⟩

theorem not_open_of_vis_eq_univ {c : Config V k} (h : c.vis = univ) (x : V) : ¬ IsOpen T c x := by
  rintro ⟨_, w, _, _, hw⟩; exact hw (h ▸ mem_univ w)

section Exec

variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e)
include he

theorem IsExec.vis_mono {t s : ℕ} (h : t ≤ s) : (e t).vis ⊆ (e s).vis := by
  induction s, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ s _ ih =>
    refine ih.trans ?_
    rw [he.eq_after s]; exact vis_subset_after

/-- A closed visited node stays closed. -/
theorem IsExec.not_open_mono {t s : ℕ} (h : t ≤ s) {x : V} (hx : x ∈ (e t).vis)
    (hc : ¬ IsOpen T (e t) x) : ¬ IsOpen T (e s) x := by
  induction s, h using Nat.le_induction with
  | base => exact hc
  | succ s hs ih =>
    intro ho
    rw [he.eq_after s] at ho
    exact ih (isOpen_of_after (he.vis_mono hs hx) ho)

/-- Terminal configurations are stable. -/
theorem IsExec.terminal_succ {t : ℕ} (h : Terminal T (e t)) : Terminal T (e (t + 1)) := by
  have hI := he.inv t
  have hno : ¬ ∃ v, IsCand T (e t) v := fun ⟨v, hv⟩ => not_open_of_vis_eq_univ h.1 v hv.1
  refine ⟨?_, ?_⟩
  · exact eq_univ_of_forall fun x => he.vis_mono (Nat.le_succ t) (h.1 ▸ mem_univ x)
  · intro i
    by_cases hi : i ∈ act t
    · have hna := na_root (he.reanchorOK t) hi (h.2 i) hno
      have hb : bf0 T (act t) (e t) (e (t + 1)).anchor i = false := by
        rw [bf0_of_root hi (h.2 i), hna]; simp
      rcases tgt_dn_cases (he.moveOK t) hi hb with hd | ⟨_, hup⟩
      · exact absurd (h.1 ▸ mem_univ _) hd.2.2.1
      · rw [hup, h.2 i, T.parent_root]
    · rw [tgt_inactive (he.moveOK t) hi]; exact h.2 i

theorem IsExec.terminal_mono {t s : ℕ} (h : t ≤ s) (ht : Terminal T (e t)) : Terminal T (e s) := by
  induction s, h using Nat.le_induction with
  | base => exact ht
  | succ s _ ih => exact he.terminal_succ ih

/-- A robot allowed to move that stays put is at the root, and either the tree is explored or
the root is closed in this very round. -/
theorem IsExec.idle_cases {t : ℕ} {i : Fin k} (hi : i ∈ act t)
    (hst : (e (t + 1)).pos i = (e t).pos i) :
    (∀ x, ¬ IsOpen T (e t) x) ∨ (IsOpen T (e t) T.root ∧ ¬ IsOpen T (e (t + 1)) T.root) := by
  have hI := he.inv t
  have hR := he.reanchorOK t
  have hM := he.moveOK t
  cases hb : bf0 T (act t) (e t) (e (t + 1)).anchor i
  · rcases tgt_dn_cases hM hi hb with hd | ⟨hno, hup⟩
    · exfalso
      have := hd.2.1; rw [hst] at this
      exact RootedTree.parent_ne_self (hst ▸ hd.1) this
    · have hroot : (e t).pos i = T.root := by
        by_contra hr; exact RootedTree.parent_ne_self hr (hup ▸ hst)
      have hna : (e (t + 1)).anchor i = T.root := by
        rw [bf0_of_root hi hroot] at hb; simpa using hb
      by_cases hex : ∃ v, IsCand T (e t) v
      · right
        have hc := (na_cand hR hi hroot hex).1
        rw [hna] at hc
        refine ⟨hc.1, ?_⟩
        have := not_open_after_of_noFree (act := act t) (na := (e (t + 1)).anchor) hno
        rw [← he.eq_after t, hroot] at this
        exact this
      · left
        intro x hx; exact hex (exists_cand hx)
  · exfalso
    obtain ⟨hs, hlt⟩ := bf0_true_spec hI hR hb
    have h1 := depth_towards hs hlt
    rw [← tgt_bf hM hi hb, hst] at h1
    omega

end Exec

section Sync

variable {e : ℕ → Config V k} (he : IsSyncExec T e)
include he

/-- Remaining time until the robot is back at the root once the tree is explored. -/
def drain (T : G.RootedTree) (c : Config V k) (i : Fin k) : ℕ :=
  if c.bf i = true then 2 * T.depth (c.anchor i) - T.depth (c.pos i) else T.depth (c.pos i)

omit he in
theorem drain_eq_zero {c : Config V k} (hI : Inv T c) {i : Fin k} (h : drain T c i = 0) :
    c.pos i = T.root := by
  unfold drain at h
  split_ifs at h with hb
  · have := (hI.bf_spec i hb).2.2; omega
  · exact RootedTree.depth_eq_zero_iff.1 h

theorem drain_succ {t : ℕ} (hv : (e t).vis = univ) (i : Fin k) :
    drain T (e (t + 1)) i = drain T (e t) i - 1 := by
  have hI := he.inv t
  have hR := he.reanchorOK t
  have hM := he.moveOK t
  have hi : i ∈ (fun _ => (univ : Finset (Fin k))) t := mem_univ i
  have hno : ¬ ∃ v, IsCand T (e t) v := fun ⟨v, hv'⟩ => not_open_of_vis_eq_univ hv v hv'.1
  have hbf : (e (t + 1)).bf i =
      (bf0 T univ (e t) (e (t + 1)).anchor i && decide ((e (t + 1)).pos i ≠ (e (t + 1)).anchor i)) := by
    have := after_bf_active (T := T) (c := e t) (na := (e (t + 1)).anchor)
      (tgt := (e (t + 1)).pos) hi
    rwa [← he.eq_after t] at this
  by_cases hroot : (e t).pos i = T.root
  · have hna := na_root hR hi hroot hno
    have hb : bf0 T univ (e t) (e (t + 1)).anchor i = false := by
      rw [bf0_of_root hi hroot, hna]; simp
    have hbt : (e t).bf i = false := by
      by_contra hc; simp only [Bool.not_eq_false] at hc; exact (hI.bf_spec i hc).1 hroot
    rcases tgt_dn_cases hM hi hb with hd | ⟨_, hup⟩
    · exact absurd (hv ▸ mem_univ _) hd.2.2.1
    · unfold drain
      rw [hbf, hb, hbt, hup, hroot, T.parent_root]; simp [T.depth_root]
  · cases hbt : (e t).bf i
    · -- depth-next, going up
      have hb : bf0 T univ (e t) (e (t + 1)).anchor i = false := by
        rw [bf0_of_not (fun h => hroot h.2), hbt]
      rcases tgt_dn_cases hM hi hb with hd | ⟨_, hup⟩
      · exact absurd (hv ▸ mem_univ _) hd.2.2.1
      · unfold drain
        rw [hbf, hb, hbt, hup]
        have := T.depth_parent _ hroot
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        omega
    · obtain ⟨hna, hpos, hdep⟩ := he.bf_step hi hbt
      have hb : bf0 T univ (e t) (e (t + 1)).anchor i = true := by
        rw [bf0_of_not (fun h => hroot h.2), hbt]
      have hlt := (hI.bf_spec i hbt).2.2
      unfold drain
      rw [hbf, hb, hbt, hna]
      by_cases ha : (e (t + 1)).pos i = (e t).anchor i
      · simp only [ha, ne_eq, not_true_eq_false, decide_false, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte]
        rw [ha] at hdep; omega
      · simp only [ne_eq, ha, not_false_eq_true, decide_true, Bool.and_self, ↓reduceIte]
        omega

theorem drain_add {t : ℕ} (hv : (e t).vis = univ) (m : ℕ) (i : Fin k) :
    drain T (e (t + m)) i = drain T (e t) i - m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hv' : (e (t + m)).vis = univ :=
      eq_univ_of_forall fun x => he.vis_mono (Nat.le_add_right t m) (hv ▸ mem_univ x)
    rw [← add_assoc, drain_succ he hv' i, ih]; omega

omit [Fintype V] in
theorem drain_le {t : ℕ} (i : Fin k) (D : ℕ) (hD : ∀ v, T.depth v ≤ D) :
    drain T (e t) i ≤ 2 * D - 1 := by
  have hI := he.inv t
  unfold drain
  split_ifs with hb
  · obtain ⟨hpr, _, hlt⟩ := hI.bf_spec i hb
    have := RootedTree.depth_pos hpr
    have := hD ((e t).anchor i)
    omega
  · have := hD ((e t).pos i)
    by_cases hr : (e t).pos i = T.root
    · rw [hr, T.depth_root]; omega
    · have := RootedTree.depth_pos hr; omega

/-- Once the tree is explored, all robots are back at the root within `2D − 1` rounds. -/
theorem terminal_of_vis {t : ℕ} (hv : (e t).vis = univ) (D : ℕ) (hD : ∀ v, T.depth v ≤ D) :
    Terminal T (e (t + (2 * D - 1))) := by
  refine ⟨eq_univ_of_forall fun x => he.vis_mono (Nat.le_add_right _ _) (hv ▸ mem_univ x), ?_⟩
  intro i
  apply drain_eq_zero (he.inv _)
  rw [drain_add he hv]
  have := drain_le he (t := t) i D hD
  omega

/-- Rounds before termination in which some robot is idle: at most `2D`. -/
theorem card_idleRounds_le (D : ℕ) (hD : ∀ v, T.depth v ≤ D) (t₁ : ℕ)
    (hnt : ∀ t < t₁, ¬ Terminal T (e t)) :
    ((range t₁).filter fun t => ∃ i, (e (t + 1)).pos i = (e t).pos i).card ≤ 2 * D := by
  classical
  set SA := (range t₁).filter fun t => ∀ x, ¬ IsOpen T (e t) x
  set SB := (range t₁).filter fun t => IsOpen T (e t) T.root ∧ ¬ IsOpen T (e (t + 1)) T.root
  have hsub : ((range t₁).filter fun t => ∃ i, (e (t + 1)).pos i = (e t).pos i) ⊆ SA ∪ SB := by
    intro t ht
    simp only [mem_filter, mem_range] at ht
    obtain ⟨i, hi⟩ := ht.2
    rcases he.idle_cases (mem_univ i) hi with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨mem_range.2 ht.1, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_range.2 ht.1, h⟩)
  have hSB : SB.card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    simp only [SB, mem_filter, mem_range] at ha hb
    by_contra hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact he.not_open_mono h (he.inv _).root_vis ha.2.2 hb.2.1
    · exact he.not_open_mono h (he.inv _).root_vis hb.2.2 ha.2.1
  have hSA : SA.card ≤ 2 * D - 1 := by
    by_cases hne : SA.Nonempty
    · set te := SA.min' hne
      have hte : te ∈ SA := min'_mem SA hne
      have hv : (e te).vis = univ := vis_eq_univ_of_no_open (he.inv te) (mem_filter.1 hte).2
      have : SA ⊆ Ico te (te + (2 * D - 1)) := by
        intro t ht
        rw [mem_Ico]
        refine ⟨min'_le SA t ht, ?_⟩
        by_contra hlt
        push Not at hlt
        have := he.terminal_mono hlt (terminal_of_vis he hv D hD)
        exact hnt t (mem_range.1 (mem_filter.1 ht).1) this
      exact (card_le_card this).trans (by simp)
    · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  have hD0 : D = 0 → t₁ = 0 := by
    intro h0
    by_contra ht
    apply hnt 0 (by omega)
    rw [he.1]
    refine ⟨?_, fun _ => rfl⟩
    rw [eq_univ_iff_forall]; intro x
    have : x = T.root := RootedTree.depth_eq_zero_iff.1 (by have := hD x; omega)
    simp [init, this]
  by_cases h0 : D = 0
  · rw [hD0 h0]; simp
  · calc _ ≤ (SA ∪ SB).card := card_le_card hsub
      _ ≤ SA.card + SB.card := card_union_le _ _
      _ ≤ 2 * D := by omega

end Sync

end Podc.TreeExplorationBFDN
