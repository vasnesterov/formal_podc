import Papers.PODC2023.TreeExplorationBFDN.Motion

/-!
# The `log Δ` part of Lemma 2 (synchronous model)

Full version arXiv:2301.13307, end of the proof of Lemma 2: once every open node of depth `d` has
at least `Δ - 1` robots anchored at it, all these nodes are closed within `d` more rounds, and
until then each robot can be re-anchored at most once more. We prove the corresponding "window"
hypothesis `WindowHyp` of the abstract allocation process for synchronous executions (all robots
move in every round), where `Δ` bounds the degree of every non-root node.

## Proof outline

* (`sync_pend_inj`) For an open non-root node `w`, the robots anchored at `w`, in depth-next mode
  and strictly below `w` lie in pairwise different subtrees `T(c)` of children `c` of `w`
  (a robot enters such a subtree only through a dangling edge, taken by one robot only).
* (`sync_closed`) In the synchronous model a robot anchored at an open node `w` of depth `d`
  at time `s + 1` has an empty stack at time `s + d` (it moves down one level per round). Hence at
  time `s + d` the `≥ Δ - 1 ≥ #children(w)` robots anchored at `w` are spread over distinct
  visited children of `w` or sit at `w` and take distinct dangling edges: `w` is closed at time
  `s + d + 1`. So no assignment at depth `d` happens from round `s + d + 1` on.
* (`sync_desc_not_root`) A robot assigned at depth `d` is not back at the root for `2d - 1`
  rounds, so every robot is assigned at most once in rounds `s + 1, …, s + d`.
* (`sync_key_anchor`, `sync_key_disc`) A robot anchored at time `s + 1` at a node of
  `openAt e d s`, or the discoverer of such a node, that returns to the root by time `s + d`
  witnesses that this node is closed at time `s + 1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [Fintype V] [DecidableEq V]

variable (T) in
/-- The number of children of `w`. -/
def nChildren (w : V) : ℕ := (univ.filter fun x => x ≠ T.root ∧ T.parent x = w).card

variable (T) in
/-- Robot `j` descends along a breadth-first path towards its anchor `a` at time `r` (its stack is
nonempty iff it has not reached `a`). -/
def SyncDesc (e : ℕ → Config V k) (r : ℕ) (j : Fin k) (a : V) : Prop :=
  (e r).anchor j = a ∧ InSub T ((e r).pos j) a ∧ ((e r).bf j = true ↔ (e r).pos j ≠ a)

/-- Robot `j` is anchored at `w`, in depth-next mode, and not at `w` (at time `t`). -/
def SyncPend (e : ℕ → Config V k) (t : ℕ) (w : V) (j : Fin k) : Prop :=
  (e t).anchor j = w ∧ (e t).bf j = false ∧ (e t).pos j ≠ w

omit [Fintype V] [DecidableEq V] in
theorem sync_towards_child {w c : V} (hpar : T.parent c = w) (hc : c ≠ T.root) :
    towards T w c = c := by
  unfold towards
  have := T.depth_parent c hc
  rw [hpar] at this
  rw [show T.depth c - T.depth w - 1 = 0 by omega]; rfl

omit [Fintype V] [DecidableEq V] in
theorem sync_towards_eq {w a c : V} (h : InSub T w a) (hlt : T.depth w < T.depth a)
    (hc : InSub T c a) (hpar : T.parent c = w) (hcr : c ≠ T.root) : towards T w a = c := by
  apply InSub.unique towards_inSub hc
  rw [depth_towards h hlt, ← T.depth_parent c hcr, hpar]

section SyncAux

variable {e : ℕ → Config V k} (he : IsExec T (fun _ => (univ : Finset (Fin k))) e)
include he

theorem sync_eq_after (r : ℕ) :
    e (r + 1) = after T univ (e r) (e (r + 1)).anchor (e (r + 1)).pos := he.eq_after r

theorem sync_bf_succ (r : ℕ) (j : Fin k) :
    (e (r + 1)).bf j = (bf0 T univ (e r) (e (r + 1)).anchor j &&
      decide ((e (r + 1)).pos j ≠ (e (r + 1)).anchor j)) := by
  conv_lhs => rw [sync_eq_after he r]
  exact after_bf_active (mem_univ j)

theorem sync_vis_mono {t t' : ℕ} (h : t ≤ t') : (e t).vis ⊆ (e t').vis := by
  induction t', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ t' _ ih =>
    refine ih.trans ?_
    rw [sync_eq_after he t']
    exact vis_subset_after

theorem sync_open_of_open_le {w : V} {t t' : ℕ} (htt : t ≤ t') (hw : w ∈ (e t).vis)
    (h : IsOpen T (e t') w) : IsOpen T (e t) w := by
  obtain ⟨_, x, hx, hp, hv⟩ := h
  exact ⟨hw, x, hx, hp, fun h' => hv (sync_vis_mono he htt h')⟩

/-- A descending robot that has not reached its anchor moves one level down. -/
theorem sync_desc_step {r : ℕ} {j : Fin k} {a : V} (h : SyncDesc T e r j a)
    (hne : (e r).pos j ≠ a) :
    SyncDesc T e (r + 1) j a ∧ T.depth ((e (r + 1)).pos j) = T.depth ((e r).pos j) + 1 := by
  obtain ⟨ha, _, hb⟩ := h
  have hbt : (e r).bf j = true := hb.2 hne
  obtain ⟨h1, h2, h3⟩ := he.bf_step (mem_univ j) hbt
  have hpr := ((he.inv r).bf_spec j hbt).1
  refine ⟨⟨h1.trans ha, ?_, ?_⟩, h3⟩
  · rw [h2, ha]; exact towards_inSub
  · rw [sync_bf_succ he, bf0_of_not (fun h' => hpr h'.2), hbt, h1, ha]; simp

/-- A robot re-anchored (at the root) to a non-root node starts descending towards it. -/
theorem sync_desc_assign {t : ℕ} {i : Fin k} (hp : (e t).pos i = T.root)
    (ha : (e (t + 1)).anchor i ≠ T.root) :
    SyncDesc T e (t + 1) i ((e (t + 1)).anchor i) ∧ T.depth ((e (t + 1)).pos i) = 1 := by
  have hb0 : bf0 T univ (e t) (e (t + 1)).anchor i = true := by
    rw [bf0_of_root (mem_univ i) hp]; simpa using ha
  have htg := tgt_bf (he.moveOK t) (mem_univ i) hb0
  have hs : InSub T ((e t).pos i) ((e (t + 1)).anchor i) := by rw [hp]; exact InSub.root _
  have hlt : T.depth ((e t).pos i) < T.depth ((e (t + 1)).anchor i) := by
    rw [hp, T.depth_root]; exact RootedTree.depth_pos ha
  refine ⟨⟨rfl, by rw [htg]; exact towards_inSub, ?_⟩, ?_⟩
  · rw [sync_bf_succ he, hb0]; simp
  · rw [htg, depth_towards hs hlt, hp, T.depth_root]

theorem sync_desc_iter {r : ℕ} {j : Fin k} {a : V} (h : SyncDesc T e r j a) :
    ∀ i, T.depth ((e r).pos j) + i ≤ T.depth a →
      SyncDesc T e (r + i) j a ∧ T.depth ((e (r + i)).pos j) = T.depth ((e r).pos j) + i := by
  intro i
  induction i with
  | zero => intro _; exact ⟨h, rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hne : (e (r + i)).pos j ≠ a := by
      intro heq; rw [heq] at h2; omega
    obtain ⟨h3, h4⟩ := sync_desc_step he h1 hne
    exact ⟨h3, by rw [show r + (i + 1) = r + i + 1 by omega, h4, h2]; omega⟩

/-- A descending robot at depth `p ≥ 1` towards an anchor of depth `d` is not at the root during
the next `2d - p` rounds. -/
theorem sync_desc_not_root {r : ℕ} {j : Fin k} {a : V} (h : SyncDesc T e r j a)
    (h1 : 1 ≤ T.depth ((e r).pos j)) {t : ℕ} (hrt : r ≤ t)
    (ht : t + T.depth ((e r).pos j) < r + 2 * T.depth a) : (e t).pos j ≠ T.root := by
  have hda := InSub.depth_le h.2.1
  intro hroot
  by_cases hc : t ≤ r + (T.depth a - T.depth ((e r).pos j))
  · obtain ⟨_, h2⟩ := sync_desc_iter he h (t - r) (by omega)
    rw [show r + (t - r) = t by omega, hroot, T.depth_root] at h2; omega
  · obtain ⟨_, h2⟩ := sync_desc_iter he h (T.depth a - T.depth ((e r).pos j)) (by omega)
    have h3 := he.depth_le_add (r + (T.depth a - T.depth ((e r).pos j)))
      (t - (r + (T.depth a - T.depth ((e r).pos j)))) j
    rw [show r + (T.depth a - T.depth ((e r).pos j)) +
      (t - (r + (T.depth a - T.depth ((e r).pos j)))) = t by omega, hroot, T.depth_root, h2] at h3
    omega

/-- How a robot of `SyncPend e (t + 1) w` (for `w` open at `t + 1`) got there. -/
theorem sync_pend_trans {w : V} (hw : w ≠ T.root) {t : ℕ} (ho : IsOpen T (e (t + 1)) w)
    {j : Fin k} (hj : SyncPend e (t + 1) w j) :
    IsOpen T (e t) w ∧
      ((SyncPend e t w j ∧ towards T w ((e t).pos j) = towards T w ((e (t + 1)).pos j)) ∨
       ((e t).pos j = w ∧ (e (t + 1)).pos j ∉ (e t).vis ∧ T.parent ((e (t + 1)).pos j) = w ∧
          (e (t + 1)).pos j ≠ T.root)) := by
  obtain ⟨ha1, hb1, hp1⟩ := hj
  have hwv : w ∈ (e t).vis := ha1 ▸ na_vis (he.inv t) (he.reanchorOK t) j
  have hot : IsOpen T (e t) w := sync_open_of_open_le he (Nat.le_succ t) hwv ho
  refine ⟨hot, ?_⟩
  have hsub1 : InSub T w ((e (t + 1)).pos j) := by
    rcases (he.inv (t + 1)).dn_spec j hb1 with h | ⟨_, hcl⟩
    · rwa [ha1] at h
    · exact absurd (by rw [ha1]; exact ho) hcl
  have hlt1 : T.depth w < T.depth ((e (t + 1)).pos j) :=
    lt_of_le_of_ne (InSub.depth_le hsub1) (fun h => hp1 (InSub.eq_of_depth hsub1 h.ge).symm)
  have hpr : (e t).pos j ≠ T.root := by
    intro hr
    obtain ⟨⟨_, _, hiff⟩, _⟩ := sync_desc_assign he hr (by rw [ha1]; exact hw)
    rw [hb1, ha1] at hiff
    exact Bool.false_ne_true (hiff.2 hp1)
  have ha0 : (e t).anchor j = w := (he.anchor_succ_of_ne_root hpr).symm.trans ha1
  have hb0 : (e t).bf j = false := by
    cases hb : (e t).bf j
    · rfl
    · exfalso
      obtain ⟨_, h2, _⟩ := he.bf_step (mem_univ j) hb
      have h3 : InSub T ((e (t + 1)).pos j) w := by rw [h2, ha0]; exact towards_inSub
      have := InSub.depth_le h3
      omega
  have hsub0 : InSub T w ((e t).pos j) := by
    rcases (he.inv t).dn_spec j hb0 with h | ⟨_, hcl⟩
    · rwa [ha0] at h
    · exact absurd (by rw [ha0]; exact hot) hcl
  by_cases hpw : (e t).pos j = w
  · right
    have hbf0 : bf0 T univ (e t) (e (t + 1)).anchor j = false := by
      rw [bf0_of_not (fun h => hpr h.2)]; exact hb0
    rcases tgt_dn_cases (he.moveOK t) (mem_univ j) hbf0 with hfd | ⟨_, hup⟩
    · obtain ⟨hne, hpar, hnv, _⟩ := hfd
      exact ⟨hpw, hnv, hpar.trans hpw, hne⟩
    · exfalso
      rw [hup, hpw] at hlt1
      have := depth_parent_le T w
      omega
  · left
    refine ⟨⟨ha0, hb0, hpw⟩, ?_⟩
    have hlt0 : T.depth w < T.depth ((e t).pos j) :=
      lt_of_le_of_ne (InSub.depth_le hsub0) (fun h => hpw (InSub.eq_of_depth hsub0 h.ge).symm)
    have hc : InSub T (towards T w ((e (t + 1)).pos j)) ((e t).pos j) := by
      rcases he.pos_succ_cases t j with h | h | ⟨_, h⟩
      · rw [← h]; exact towards_inSub
      · have h' : InSub T (towards T w ((e (t + 1)).pos j)) (T.parent ((e t).pos j)) := by
          rw [← h]; exact towards_inSub
        exact InSub.of_parent h'
      · have hcne : (e (t + 1)).pos j ≠ towards T w ((e (t + 1)).pos j) := by
          intro h'
          apply hpw
          rw [← h, h']
          exact parent_towards hsub1 hlt1
        rw [← h]
        exact InSub.parent_of_ne towards_inSub hcne
    exact sync_towards_eq hsub0 hlt0 hc (parent_towards hsub1 hlt1) (towards_ne_root hsub1 hlt1)

/-- The robots anchored at an open non-root node `w`, in depth-next mode and strictly below `w`,
are in pairwise different subtrees of children of `w`. -/
theorem sync_pend_inj {w : V} (hw : w ≠ T.root) :
    ∀ t, IsOpen T (e t) w → ∀ j j', SyncPend e t w j → SyncPend e t w j' →
      towards T w ((e t).pos j) = towards T w ((e t).pos j') → j = j' := by
  intro t
  induction t with
  | zero =>
    intro _ j _ hj _ _
    exfalso
    have h := hj.1
    rw [he.1] at h
    exact hw h.symm
  | succ t ih =>
    intro ho j j' hj hj' heq
    obtain ⟨hot, hcj⟩ := sync_pend_trans he hw ho hj
    obtain ⟨_, hcj'⟩ := sync_pend_trans he hw ho hj'
    have hvis : ∀ i, towards T w ((e t).pos i) ∈ (e t).vis := fun i =>
      (he.inv t).vis_of_inSub towards_inSub ((he.inv t).pos_vis i)
    rcases hcj with ⟨hpj, htj⟩ | ⟨_, hnv, hpar, hnr⟩ <;>
      rcases hcj' with ⟨hpj', htj'⟩ | ⟨_, hnv', hpar', hnr'⟩
    · exact ih hot j j' hpj hpj' (htj.trans (heq.trans htj'.symm))
    · exfalso; apply hnv'
      rw [← sync_towards_child hpar' hnr', ← heq, ← htj]; exact hvis j
    · exfalso; apply hnv
      rw [← sync_towards_child hpar hnr, heq, ← htj']; exact hvis j'
    · rw [sync_towards_child hpar hnr, sync_towards_child hpar' hnr'] at heq
      exact tgt_inj_of_not_vis (he.inv t) (he.reanchorOK t) (he.moveOK t) hnv heq

/-- Closure: in the synchronous model, a node `w ∈ openAt e d s` with at least `Δ - 1` robots
anchored at it at time `s + 1` (and at most `Δ - 1` children) is closed at time `s + d + 1`. -/
theorem sync_closed {s d Δ : ℕ} (hd : 1 ≤ d) (hΔ : ∀ w, w ≠ T.root → nChildren T w + 1 ≤ Δ)
    {w : V} (hwO : w ∈ openAt T e d s) (hth : Δ ≤ anchCount e (s + 1) w + 1) :
    ¬ IsOpen T (e (s + d + 1)) w := by
  intro hoE
  obtain ⟨hwd, hos⟩ := mem_openAt.1 hwO
  have hwr : w ≠ T.root := ne_root_of_mem_openAt hd hwO
  have hopen : ∀ t, s ≤ t → t ≤ s + d + 1 → IsOpen T (e t) w := fun t h1 h2 =>
    sync_open_of_open_le he h2 (sync_vis_mono he h1 hos.1) hoE
  set J := univ.filter fun j => (e (s + 1)).anchor j = w with hJ
  have hanc : ∀ j ∈ J, ∀ t, s + 1 ≤ t → t ≤ s + d + 1 → (e t).anchor j = w := by
    intro j hj t ht
    induction t, ht using Nat.le_induction with
    | base => intro _; simpa [J] using hj
    | succ t ht ih =>
      intro ht'
      have h := ih (by omega)
      rw [he.anchor_keep (by rw [h]; exact hwr) (by rw [h]; exact hopen t (by omega) (by omega)), h]
  have hbfd : ∀ j ∈ J, ∀ t, s + 1 ≤ t → t ≤ s + d → (e t).bf j = true →
      t - s ≤ T.depth ((e t).pos j) := by
    intro j hj t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro _ _
      have h := hanc j hj (s + 1) le_rfl (by omega)
      have := (he.inv (s + 1)).off_root j (by rw [h]; exact hwr)
        (by rw [h]; exact hopen _ (by omega) (by omega))
      have := RootedTree.depth_pos this; omega
    | succ t ht ih =>
      intro ht' hb
      have h := hanc j hj t ht (by omega)
      have hpr := (he.inv t).off_root j (by rw [h]; exact hwr)
        (by rw [h]; exact hopen _ (by omega) (by omega))
      have hb' := he.bf_succ_of_ne_root hpr hb
      have h1 := ih (by omega) hb'
      have h2 := (he.bf_step (mem_univ j) hb').2.2
      omega
  have hdn : ∀ j ∈ J, (e (s + d)).bf j = false := by
    intro j hj
    cases hc : (e (s + d)).bf j
    · rfl
    · exfalso
      have h1 := hbfd j hj (s + d) (by omega) le_rfl hc
      have h2 := ((he.inv (s + d)).bf_spec j hc).2.2
      rw [hanc j hj (s + d) (by omega) (by omega), hwd] at h2
      omega
  have hsubw : ∀ j ∈ J, InSub T w ((e (s + d)).pos j) := by
    intro j hj
    have h := hanc j hj (s + d) (by omega) (by omega)
    rcases (he.inv (s + d)).dn_spec j (hdn j hj) with h' | ⟨_, hcl⟩
    · rwa [h] at h'
    · exact absurd (by rw [h]; exact hopen _ (by omega) (by omega)) hcl
  have hatw : ∀ j ∈ J, (e (s + d)).pos j = w →
      (e (s + d + 1)).pos j ∉ (e (s + d)).vis ∧ T.parent ((e (s + d + 1)).pos j) = w ∧
        (e (s + d + 1)).pos j ≠ T.root := by
    intro j hj hp
    have hpr : (e (s + d)).pos j ≠ T.root := by rw [hp]; exact hwr
    have hb0 : bf0 T univ (e (s + d)) (e (s + d + 1)).anchor j = false := by
      rw [bf0_of_not (fun h => hpr h.2)]; exact hdn j hj
    rcases tgt_dn_cases (he.moveOK (s + d)) (mem_univ j) hb0 with hfd | ⟨hno, _⟩
    · obtain ⟨hne, hpar, hnv, _⟩ := hfd
      exact ⟨hnv, hpar.trans hp, hne⟩
    · exfalso
      have := not_open_after_of_noFree (act := univ) (na := (e (s + d + 1)).anchor) hno
      rw [← sync_eq_after he (s + d), hp] at this
      exact this hoE
  let f : Fin k → V := fun j => if (e (s + d)).pos j = w then (e (s + d + 1)).pos j
    else towards T w ((e (s + d)).pos j)
  set Ch := univ.filter fun x => x ≠ T.root ∧ T.parent x = w with hCh
  have hvis : ∀ j, towards T w ((e (s + d)).pos j) ∈ (e (s + d)).vis := fun j =>
    (he.inv _).vis_of_inSub towards_inSub ((he.inv _).pos_vis j)
  have hfmem : ∀ j ∈ J, f j ∈ Ch.filter fun x => x ∈ (e (s + d + 1)).vis := by
    intro j hj
    simp only [f, Ch, mem_filter, mem_univ, true_and]
    split_ifs with hp
    · obtain ⟨_, hpar, hne⟩ := hatw j hj hp
      exact ⟨⟨hne, hpar⟩, (he.inv _).pos_vis j⟩
    · have hs := hsubw j hj
      have hlt : T.depth w < T.depth ((e (s + d)).pos j) :=
        lt_of_le_of_ne (InSub.depth_le hs) (fun h => hp (InSub.eq_of_depth hs h.ge).symm)
      exact ⟨⟨towards_ne_root hs hlt, parent_towards hs hlt⟩,
        sync_vis_mono he (Nat.le_succ _) (hvis j)⟩
  have hfinj : Set.InjOn f J := by
    intro j hj j' hj' hjj
    simp only [mem_coe] at hj hj'
    by_cases hp : (e (s + d)).pos j = w <;> by_cases hp' : (e (s + d)).pos j' = w <;>
      simp only [f, hp, hp', ↓reduceIte] at hjj
    · exact tgt_inj_of_not_vis (he.inv _) (he.reanchorOK _) (he.moveOK _) (hatw j hj hp).1 hjj
    · exfalso; apply (hatw j hj hp).1; rw [hjj]; exact hvis j'
    · exfalso; apply (hatw j' hj' hp').1; rw [← hjj]; exact hvis j
    · exact sync_pend_inj he hwr (s + d) (hopen _ (by omega) (by omega)) j j'
        ⟨hanc j hj _ (by omega) (by omega), hdn j hj, hp⟩
        ⟨hanc j' hj' _ (by omega) (by omega), hdn j' hj', hp'⟩ hjj
  have hcard1 : J.card ≤ (Ch.filter fun x => x ∈ (e (s + d + 1)).vis).card :=
    card_le_card_of_injOn f (fun j hj => hfmem j hj) hfinj
  have hcard2 : Ch.card ≤ J.card := by
    have := hΔ w hwr
    have h2 : anchCount e (s + 1) w = J.card := rfl
    have h3 : nChildren T w = Ch.card := rfl
    omega
  have heq : Ch.filter (fun x => x ∈ (e (s + d + 1)).vis) = Ch :=
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  obtain ⟨_, x, hx, hpx, hxv⟩ := hoE
  have hxC : x ∈ Ch := by simp [Ch, hx, hpx]
  rw [← heq, mem_filter] at hxC
  exact hxv hxC.2

theorem sync_key_low {s d t : ℕ} {j : Fin k} (ht1 : s + 1 ≤ t) (ht2 : t ≤ s + d)
    (hroot : (e t).pos j = T.root) : T.depth ((e (s + 1)).pos j) + 1 ≤ d := by
  have h := he.depth_le_add (s + 1) (t - (s + 1)) j
  rw [show s + 1 + (t - (s + 1)) = t by omega, hroot, T.depth_root] at h
  omega

/-- A robot anchored at time `s + 1` at `w ∈ openAt e d s` and back at the root by time `s + d`
shows that `w` is closed at time `s + 1`; it was already anchored at `w` at time `s`. -/
theorem sync_key_anchor {s d t : ℕ} (hd : 1 ≤ d) {j : Fin k} {w : V} (ht1 : s + 1 ≤ t)
    (ht2 : t ≤ s + d) (hroot : (e t).pos j = T.root) (hwO : w ∈ openAt T e d s)
    (ha : (e (s + 1)).anchor j = w) :
    ¬ IsOpen T (e (s + 1)) w ∧ (e s).anchor j = w := by
  have hlow := sync_key_low he ht1 ht2 hroot
  have hwd := (mem_openAt.1 hwO).1
  have hwr := ne_root_of_mem_openAt hd hwO
  cases hb : (e (s + 1)).bf j
  · rcases (he.inv (s + 1)).dn_spec j hb with h | ⟨_, hcl⟩
    · rw [ha] at h; have := InSub.depth_le h; omega
    · rw [ha] at hcl
      refine ⟨hcl, ?_⟩
      by_cases hp : (e s).pos j = T.root
      · exfalso
        obtain ⟨⟨_, _, hiff⟩, _⟩ := sync_desc_assign he hp (by rw [ha]; exact hwr)
        rw [hb] at hiff
        have : (e (s + 1)).pos j = (e (s + 1)).anchor j := by
          by_contra hc; exact Bool.false_ne_true (hiff.2 hc)
        rw [this, ha] at hlow; omega
      · rw [← ha]; exact (he.anchor_succ_of_ne_root hp).symm
  · exfalso
    obtain ⟨hpr, hs, hlt⟩ := (he.inv (s + 1)).bf_spec j hb
    rw [ha] at hs hlt
    have hD : SyncDesc T e (s + 1) j w :=
      ⟨ha, hs, ⟨fun _ h => by rw [h] at hlt; exact lt_irrefl _ hlt, fun _ => hb⟩⟩
    exact sync_desc_not_root he hD (RootedTree.depth_pos hpr) ht1 (by rw [hwd]; omega) hroot

/-- The discoverer of `w ∈ openAt e d s` (a robot of `T(w)` anchored above `w`), if back at the
root by time `s + d`, shows that `w` is closed at time `s + 1`. -/
theorem sync_key_disc {s d t : ℕ} (hd : 1 ≤ d) {j : Fin k} {w : V} (ht1 : s + 1 ≤ t)
    (ht2 : t ≤ s + d) (hroot : (e t).pos j = T.root) (hwO : w ∈ openAt T e d s)
    (hs : InSub T w ((e s).pos j)) (hda : T.depth ((e s).anchor j) < T.depth w) :
    ¬ IsOpen T (e (s + 1)) w := by
  have hlow := sync_key_low he ht1 ht2 hroot
  have hwd := (mem_openAt.1 hwO).1
  have hwr := ne_root_of_mem_openAt hd hwO
  by_cases hpw : (e s).pos j = w
  · have hpr : (e s).pos j ≠ T.root := by rw [hpw]; exact hwr
    have hbs : (e s).bf j = false := by
      cases hb : (e s).bf j
      · rfl
      · exfalso; have := ((he.inv s).bf_spec j hb).2.2; rw [hpw] at this; omega
    have hb0 : bf0 T univ (e s) (e (s + 1)).anchor j = false := by
      rw [bf0_of_not (fun h => hpr h.2)]; exact hbs
    rcases tgt_dn_cases (he.moveOK s) (mem_univ j) hb0 with hfd | ⟨hno, _⟩
    · exfalso
      obtain ⟨hne, hpar, _, _⟩ := hfd
      have := T.depth_parent _ hne
      rw [hpar, hpw] at this; omega
    · have := not_open_after_of_noFree (act := univ) (na := (e (s + 1)).anchor) hno
      rw [← sync_eq_after he s, hpw] at this
      exact this
  · exfalso
    have hlt : T.depth w < T.depth ((e s).pos j) :=
      lt_of_le_of_ne (InSub.depth_le hs) (fun h => hpw (InSub.eq_of_depth hs h.ge).symm)
    have := he.depth_le_succ s j
    omega

end SyncAux

/-- The window hypothesis holds in the synchronous model when every non-root node has degree
at most `Δ`. -/
theorem sync_window {e : ℕ → Config V k} (he : IsSyncExec T e) {d Δ : ℕ} (hd : 1 ≤ d)
    (hΔ : ∀ w, w ≠ T.root → nChildren T w + 1 ≤ Δ) :
    WindowHyp T (fun _ => univ) e d Δ := by
  have he' : IsExec T (fun _ => (univ : Finset (Fin k))) e := he
  intro s hPs hne hth t₁
  set O := openAt T e d s with hO
  set O' := openAt T e d (s + 1) with hO'
  -- Step 1: the nodes of `O` are closed from time `s + d + 1` on.
  have hcl : ∀ w ∈ O, ∀ t, s + d + 1 ≤ t → ¬ IsOpen T (e t) w := fun w hw t ht ho =>
    sync_closed he' hd hΔ hw (hth w hw) (sync_open_of_open_le he' ht
      (sync_vis_mono he' (by omega) (mem_openAt.1 hw).2.1) ho)
  have hsub : ∀ t, s ≤ t → openAt T e d t ⊆ O := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact subset_rfl
    | succ t ht ih => exact (openAt_succ_subset he' hPs ht).trans ih
  -- Step 2: no assignment at depth `d` from round `s + d + 1` on.
  let F : ℕ → Finset (Fin k) := fun t =>
    univ.filter fun i => (e t).pos i = T.root ∧ T.depth ((e (t + 1)).anchor i) = d
  have hF : ∀ t, assignCount T (fun _ => univ) e d t = (F t).card := by
    intro t; unfold assignCount; congr 1; ext i; simp [F]
  have hF0 : ∀ t, s + d + 1 ≤ t → F t = ∅ := by
    intro t ht
    rw [eq_empty_iff_forall_notMem]
    intro i hi
    simp only [F, mem_filter, mem_univ, true_and] at hi
    have hc := he'.cand_of_assign hd (mem_univ i) hi.1 hi.2
    have hmem : (e (t + 1)).anchor i ∈ openAt T e d t := mem_openAt.2 ⟨hi.2, hc.1⟩
    exact hcl _ (hsub t (by omega) hmem) t ht hc.1
  set W := Ico (s + 1) (min t₁ (s + d + 1)) with hW
  have hsum : ∑ t ∈ Ico (s + 1) t₁, assignCount T (fun _ => univ) e d t =
      ∑ t ∈ W, (F t).card := by
    simp only [hF]
    by_cases h : t₁ ≤ s + d + 1
    · rw [hW, min_eq_left h]
    · have hz : ∑ t ∈ Ico (s + d + 1) t₁, (F t).card = 0 :=
        sum_eq_zero (fun t ht => by rw [hF0 t (mem_Ico.1 ht).1, card_empty])
      rw [hW, min_eq_right (by omega), ← sum_Ico_consecutive _
        (show s + 1 ≤ s + d + 1 by omega) (show s + d + 1 ≤ t₁ by omega), hz, add_zero]
  have hWmem : ∀ t ∈ W, s + 1 ≤ t ∧ t ≤ s + d := by
    intro t ht
    rw [hW, mem_Ico] at ht
    exact ⟨ht.1, by have := (lt_min_iff.1 ht.2).2; omega⟩
  -- Step 3: each robot is assigned at most once in the rounds of `W`.
  have hdisjF : (W : Set ℕ).PairwiseDisjoint F := by
    intro t ht t' ht' hne
    wlog hlt : t < t' generalizing t t'
    · exact (this ht' ht hne.symm (by omega)).symm
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    simp only [F, mem_filter, mem_univ, true_and] at hi hi'
    have hd1 : (e (t + 1)).anchor i ≠ T.root := by
      intro h; rw [h, T.depth_root] at hi; omega
    obtain ⟨hDe, hde⟩ := sync_desc_assign he' hi.1 hd1
    have h1 := hWmem t ht
    have h2 := hWmem t' ht'
    exact sync_desc_not_root (t := t') he' hDe hde.ge (by omega) (by rw [hde, hi.2]; omega) hi'.1
  set P := W.biUnion F with hP
  have hPcard : ∑ t ∈ W, (F t).card = P.card := (card_biUnion hdisjF).symm
  -- Step 4: the robots counted on the left-hand side (anchored at `O` or discoverers).
  have hdisc : ∀ w ∈ O, ∃ j, InSub T w ((e s).pos j) ∧ T.depth ((e s).anchor j) < T.depth w :=
    fun w hw => (he'.inv s).disc w (ne_root_of_mem_openAt hd hw) (mem_openAt.1 hw).2
  have : Nonempty (Fin k) := by
    obtain ⟨w, hw⟩ := hne; exact ⟨(hdisc w hw).choose⟩
  choose! D hD using hdisc
  set S := univ.filter fun j => (e (s + 1)).anchor j ∈ O with hSdef
  have hS : ∑ w ∈ O, anchCount e (s + 1) w = S.card := by
    rw [card_eq_sum_card_fiberwise (f := fun j => (e (s + 1)).anchor j) (t := O)]
    · apply sum_congr rfl
      intro w _
      unfold anchCount
      congr 1; ext j; simp [S]
      intro h; rwa [h]
    · intro j hj; simpa [S] using hj
  have hinj : Set.InjOn D O := by
    intro w hw w' hw' h
    have h1 := (hD w hw).1
    have h2 := (hD w' hw').1
    rw [h] at h1
    exact InSub.unique h1 h2 (by rw [(mem_openAt.1 hw).1, (mem_openAt.1 hw').1])
  have hdisj : Disjoint S (O.image D) := by
    rw [disjoint_right]
    intro j hj hjS
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hj
    have hpr : (e s).pos (D w) ≠ T.root :=
      InSub.ne_root_of_depth (hD w hw).1 (ne_root_of_mem_openAt hd hw)
    have hna := na_eq_of_ne_root (he'.reanchorOK s) hpr
    simp only [S, mem_filter, mem_univ, true_and] at hjS
    rw [hna] at hjS
    have := (hD w hw).2
    rw [(mem_openAt.1 hw).1, ← (mem_openAt.1 hjS).1] at this
    omega
  have hB : ∑ w ∈ O, (anchCount e (s + 1) w + 1) = (S ∪ O.image D).card := by
    rw [sum_add_distrib, hS, sum_const, smul_eq_mul, mul_one, ← card_image_of_injOn hinj,
      ← card_union_of_disjoint hdisj]
  have hkey : P ∩ (S ∪ O.image D) ⊆ (O \ O').biUnion
      (fun w => (univ.filter fun j => (e s).anchor j = w) ∪ {D w}) := by
    intro j hj
    obtain ⟨hjP, hjB⟩ := mem_inter.1 hj
    obtain ⟨t, ht, hjt⟩ := mem_biUnion.1 hjP
    simp only [F, mem_filter, mem_univ, true_and] at hjt
    obtain ⟨ht1, ht2⟩ := hWmem t ht
    rw [mem_biUnion]
    rcases mem_union.1 hjB with hjS | hjD
    · simp only [S, mem_filter, mem_univ, true_and] at hjS
      obtain ⟨hclo, ha⟩ := sync_key_anchor he' hd ht1 ht2 hjt.1 hjS rfl
      exact ⟨_, mem_sdiff.2 ⟨hjS, fun h => hclo (mem_openAt.1 h).2⟩, by simp [ha]⟩
    · obtain ⟨w, hw, rfl⟩ := mem_image.1 hjD
      have hclo := sync_key_disc he' hd ht1 ht2 hjt.1 hw (hD w hw).1 (hD w hw).2
      exact ⟨w, mem_sdiff.2 ⟨hw, fun h => hclo (mem_openAt.1 h).2⟩, by simp⟩
  have hkeycard : (P ∩ (S ∪ O.image D)).card ≤ ∑ w ∈ O \ O', (anchCount e s w + 1) := by
    refine (card_le_card hkey).trans (card_biUnion_le.trans (sum_le_sum fun w _ => ?_))
    exact (card_union_le _ _).trans (by rw [card_singleton]; rfl)
  rw [hsum, hPcard, hB]
  have h1 := card_union_add_card_inter P (S ∪ O.image D)
  have h2 : (P ∪ (S ∪ O.image D)).card ≤ k := (card_le_univ _).trans (by simp)
  omega

end Podc.TreeExplorationBFDN
