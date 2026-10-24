import Papers.PODC2023.TreeExplorationBFDN.Invariants
import Papers.PODC2023.TreeExplorationBFDN.Allocation

/-!
# The depth-`d` phase of BFDN (towards Lemma 2 of the full version)

For a fixed depth `d ≥ 1` we instantiate the abstract allocation process of `Allocation.lean`:

* `openAt e d t`: the open nodes of depth `d` at the start of round `t` (the urns);
* `anchCount e t w`: the number of robots anchored at `w` (the load);
* `assignCount act e d t`: the number of calls of `Reanchor` in round `t` returning a node of
  depth `d` (the assignments).

All hypotheses of `alloc_bound` except the "window" hypothesis are proved here for every
execution, whatever robots are blocked. This gives the `log k` part of Lemma 2
(`assignCount_le_urnSum_k`); the `log Δ` part needs synchrony (`Sync.lean`).

The proofs make precise the reduction to the balls-in-urns game sketched in Section 3.1 of the
full version: the urns are the open nodes of depth `d`, each also holding its discoverer robot
(Claim 5); robots anchored at an open node cannot return to the root before the node closes; the
re-anchoring rule keeps the loads of open nodes balanced.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [Fintype V] [DecidableEq V]

variable (T) in
/-- Number of calls to `Reanchor` in round `t` that return a node of depth `d`. -/
noncomputable def assignCount (act : ℕ → Finset (Fin k)) (e : ℕ → Config V k) (d t : ℕ) : ℕ :=
  open scoped Classical in
  (univ.filter fun i => i ∈ act t ∧ (e t).pos i = T.root ∧ T.depth ((e (t + 1)).anchor i) = d).card

variable (T) in
/-- The open nodes of depth `d` at the start of round `t`. -/
noncomputable def openAt (e : ℕ → Config V k) (d t : ℕ) : Finset V :=
  open scoped Classical in
  univ.filter fun w => T.depth w = d ∧ IsOpen T (e t) w

/-- The number of robots anchored at `w` at the start of round `t`. -/
def anchCount (e : ℕ → Config V k) (t : ℕ) (w : V) : ℕ :=
  (univ.filter fun j => (e t).anchor j = w).card

section Exec

variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e)
include he

omit [Fintype V] in
theorem IsExec.reanchorOK (t : ℕ) (i : Fin k) :
    ReanchorOK T (act t) (e t) (e (t + 1)).anchor i := by
  obtain ⟨na, tgt, hR, _, h⟩ := he.2 t
  rw [h]; exact hR i

omit [Fintype V] in
theorem IsExec.moveOK (t : ℕ) (i : Fin k) :
    MoveOK T (act t) (e t) (e (t + 1)).anchor (e (t + 1)).pos i := by
  obtain ⟨na, tgt, _, hM, h⟩ := he.2 t
  rw [h]; exact hM i

omit [Fintype V] in
theorem IsExec.eq_after (t : ℕ) :
    e (t + 1) = after T (act t) (e t) (e (t + 1)).anchor (e (t + 1)).pos := by
  obtain ⟨na, tgt, _, _, h⟩ := he.2 t
  rw [h]; rfl

omit [Fintype V] in
/-- Minimum open depth never decreases. -/
theorem IsExec.open_depth_mono {d t : ℕ} (h : ∀ x, IsOpen T (e t) x → d ≤ T.depth x) :
    ∀ s, t ≤ s → ∀ x, IsOpen T (e s) x → d ≤ T.depth x := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact h
  | succ s _ ih =>
    intro x hx
    rw [he.eq_after s] at hx
    obtain ⟨y, hy, hyx⟩ := exists_open_le (he.inv s) (he.reanchorOK s) (he.moveOK s) hx
    exact (ih y hy).trans hyx

/-- A call to `Reanchor` at depth `d ≥ 1` returns an open node of minimum depth. -/
theorem IsExec.cand_of_assign {d t : ℕ} (hd : 1 ≤ d) {i : Fin k} (hi : i ∈ act t)
    (hp : (e t).pos i = T.root) (hdi : T.depth ((e (t + 1)).anchor i) = d) :
    IsCand T (e t) ((e (t + 1)).anchor i) := by
  by_cases hex : ∃ v, IsCand T (e t) v
  · exact (na_cand (he.reanchorOK t) hi hp hex).1
  · rw [na_root (he.reanchorOK t) hi hp hex, T.depth_root] at hdi; omega

omit [Fintype V] in
/-- Robots anchored at an open non-root node keep their anchor. -/
theorem IsExec.anchor_keep {t : ℕ} {j : Fin k} (hne : (e t).anchor j ≠ T.root)
    (ho : IsOpen T (e t) ((e t).anchor j)) : (e (t + 1)).anchor j = (e t).anchor j :=
  na_eq_of_ne_root (he.reanchorOK t) ((he.inv t).off_root j hne ho)

end Exec


section Phase

variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e)
  {d : ℕ} (hd : 1 ≤ d) {t₀ : ℕ} (hP : ∀ x, IsOpen T (e t₀) x → d ≤ T.depth x)
  (hmin : ∀ t < t₀, ¬ ∀ x, IsOpen T (e t) x → d ≤ T.depth x)

omit [DecidableEq V] in
theorem mem_openAt {t : ℕ} {w : V} : w ∈ openAt T e d t ↔ T.depth w = d ∧ IsOpen T (e t) w := by
  classical
  unfold openAt; simp

omit [DecidableEq V] in
theorem ne_root_of_mem_openAt (hd : 1 ≤ d) {t : ℕ} {w : V} (hw : w ∈ openAt T e d t) :
    w ≠ T.root := by
  rintro rfl; rw [mem_openAt, T.depth_root] at hw; omega

omit [Fintype V] in
theorem mem_assignCount {t : ℕ} {i : Fin k} :
    i ∈ (open scoped Classical in univ.filter fun i => i ∈ act t ∧ (e t).pos i = T.root ∧
      T.depth ((e (t + 1)).anchor i) = d) ↔
      i ∈ act t ∧ (e t).pos i = T.root ∧ T.depth ((e (t + 1)).anchor i) = d := by
  simp

include he hd

theorem assignCount_eq_zero_of_not {t : ℕ} (h : ¬ ∀ x, IsOpen T (e t) x → d ≤ T.depth x) :
    assignCount T act e d t = 0 := by
  classical
  push Not at h
  obtain ⟨x, hx, hxd⟩ := h
  unfold assignCount
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro i - ⟨hi, hp, hdi⟩
  have := (he.cand_of_assign hd hi hp hdi).2 x hx
  omega

include hP

omit hd in
theorem openAt_succ_subset {t : ℕ} (ht : t₀ ≤ t) : openAt T e d (t + 1) ⊆ openAt T e d t := by
  intro w hw
  rw [mem_openAt] at hw ⊢
  refine ⟨hw.1, ?_⟩
  have h2 := hw.2
  rw [he.eq_after t] at h2
  rcases open_after_cases (he.inv t) (he.reanchorOK t) (he.moveOK t) h2 with h | ⟨_, hne, hpo⟩
  · exact h
  · exfalso
    have := he.open_depth_mono hP t ht _ hpo
    have := T.depth_parent w hne
    omega

omit hd hP in
theorem assignCount_eq_sum {t : ℕ} (_ht : t₀ ≤ t) (hd : 1 ≤ d) :
    assignCount T act e d t = ∑ w ∈ openAt T e d t, (anchCount e (t + 1) w - anchCount e t w) := by
  classical
  have key : ∀ w ∈ openAt T e d t, anchCount e (t + 1) w - anchCount e t w =
      (univ.filter fun i => (i ∈ act t ∧ (e t).pos i = T.root) ∧ (e (t + 1)).anchor i = w).card := by
    intro w hw
    have hwr := ne_root_of_mem_openAt hd hw
    have hwo := (mem_openAt.1 hw).2
    have hsplit : (univ.filter fun j => (e (t + 1)).anchor j = w) =
        (univ.filter fun j => (e t).anchor j = w) ∪
          (univ.filter fun i => (i ∈ act t ∧ (e t).pos i = T.root) ∧ (e (t + 1)).anchor i = w) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · intro h
        by_cases hr : j ∈ act t ∧ (e t).pos j = T.root
        · exact Or.inr ⟨hr, h⟩
        · left; rw [← na_eq_of_not (he.reanchorOK t) hr]; exact h
      · rintro (h | ⟨_, h⟩)
        · rw [← h] at hwr hwo ⊢; exact he.anchor_keep hwr hwo
        · exact h
    have hdisj : Disjoint (univ.filter fun j => (e t).anchor j = w)
        (univ.filter fun i => (i ∈ act t ∧ (e t).pos i = T.root) ∧ (e (t + 1)).anchor i = w) := by
      rw [disjoint_filter]
      rintro j - h ⟨⟨_, hp⟩, _⟩
      rw [← h] at hwr hwo
      exact (he.inv t).off_root j hwr hwo hp
    unfold anchCount
    rw [hsplit, card_union_of_disjoint hdisj]; omega
  rw [sum_congr rfl key]
  rw [← card_biUnion]
  · unfold assignCount
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · rintro ⟨hi, hp, hdi⟩
      have hc := he.cand_of_assign hd hi hp hdi
      exact ⟨_, mem_openAt.2 ⟨hdi, hc.1⟩, ⟨hi, hp⟩, rfl⟩
    · rintro ⟨w, hw, hr, rfl⟩
      exact ⟨hr.1, hr.2, (mem_openAt.1 hw).1⟩
  · intro w _ w' _ hne
    simp only [Function.onFun, disjoint_filter]
    rintro i - ⟨_, h1⟩ ⟨_, h2⟩
    exact hne (h1.symm.trans h2)

end Phase

section Phase2

variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e) {d : ℕ}
include he

theorem anchCount_mono {t : ℕ} (hd : 1 ≤ d) {w : V} (hw : w ∈ openAt T e d t) :
    anchCount e t w ≤ anchCount e (t + 1) w := by
  classical
  have hwr := ne_root_of_mem_openAt hd hw
  have hwo := (mem_openAt.1 hw).2
  unfold anchCount
  apply card_le_card
  intro j
  simp only [mem_filter, mem_univ, true_and]
  intro h
  rw [← h] at hwr hwo ⊢; exact he.anchor_keep hwr hwo

theorem anchCount_eq_zero_init {t₀ : ℕ} (hd : 1 ≤ d)
    (hmin : ∀ t < t₀, ¬ ∀ x, IsOpen T (e t) x → d ≤ T.depth x) {w : V}
    (hw : w ∈ openAt T e d t₀) : anchCount e t₀ w = 0 := by
  classical
  have hwd := (mem_openAt.1 hw).1
  unfold anchCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro j _ hj
  rcases t₀ with _ | s
  · rw [he.1] at hj
    simp only [init] at hj
    rw [← hj, T.depth_root] at hwd; omega
  · have h := hmin s (Nat.lt_succ_self s)
    push Not at h
    obtain ⟨x, hx, hxd⟩ := h
    have := na_depth_le (he.inv s) (he.reanchorOK s) j hx
    rw [hj] at this; omega

/-- Capacity: the robots anchored at open depth-`d` nodes, together with one discoverer per such
node (Claim 5), are pairwise distinct. -/
theorem sum_anchCount_add_one_le (hd : 1 ≤ d) (t : ℕ) :
    ∑ w ∈ openAt T e d t, (anchCount e (t + 1) w + 1) ≤ k := by
  classical
  have hI := he.inv t
  set O := openAt T e d t
  have hdisc : ∀ w ∈ O, ∃ j, InSub T w ((e t).pos j) ∧ T.depth ((e t).anchor j) < T.depth w :=
    fun w hw => hI.disc w (ne_root_of_mem_openAt hd hw) (mem_openAt.1 hw).2
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · have : O = ∅ := by
      rw [eq_empty_iff_forall_notMem]; intro w hw; obtain ⟨j, _⟩ := hdisc w hw; exact hk.elim j
    rw [this]; simp
  choose! D hD using hdisc
  set S := univ.filter fun j => (e (t + 1)).anchor j ∈ O
  have hS : ∑ w ∈ O, anchCount e (t + 1) w = S.card := by
    rw [card_eq_sum_card_fiberwise (f := fun j => (e (t + 1)).anchor j) (t := O)]
    · apply sum_congr rfl
      intro w _
      unfold anchCount
      congr 1; ext j; simp [S]
      intro h; rw [h]; assumption
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
    have hpr : (e t).pos (D w) ≠ T.root :=
      InSub.ne_root_of_depth (hD w hw).1 (ne_root_of_mem_openAt hd hw)
    have hna := na_eq_of_ne_root (he.reanchorOK t) hpr
    simp only [S, mem_filter, mem_univ, true_and] at hjS
    rw [hna] at hjS
    have := (hD w hw).2
    rw [(mem_openAt.1 hw).1, ← (mem_openAt.1 hjS).1] at this
    omega
  rw [sum_add_distrib, hS, sum_const, smul_eq_mul, mul_one, ← card_image_of_injOn hinj,
    ← card_union_of_disjoint hdisj]
  exact (card_le_univ _).trans (by simp)

end Phase2

section Balance

/-- The loads seen during the sequential decisions: robots with index `< m` are counted with their
new anchor, the others with their old anchor. -/
def runLoad (c : Config V k) (na : Fin k → V) (m : ℕ) (v : V) : ℕ :=
  (univ.filter fun j : Fin k => (j.val < m ∧ na j = v) ∨ (m ≤ j.val ∧ c.anchor j = v)).card

omit [Fintype V] in
theorem load_eq_runLoad (c : Config V k) (na : Fin k → V) (i : Fin k) (v : V) :
    load c na i v = runLoad c na i.val v := by
  unfold load runLoad curAnchor
  congr 1; ext j
  simp only [mem_filter, mem_univ, true_and, Fin.lt_def]
  split_ifs with h
  · constructor
    · intro h'; exact Or.inl ⟨h, h'⟩
    · rintro (h' | h')
      · exact h'.2
      · omega
  · constructor
    · intro h'; exact Or.inr ⟨by omega, h'⟩
    · rintro (h' | h')
      · omega
      · exact h'.2

omit [Fintype V] in
theorem runLoad_zero (c : Config V k) (na : Fin k → V) (v : V) :
    runLoad c na 0 v = (univ.filter fun j => c.anchor j = v).card := by
  simp [runLoad]

omit [Fintype V] in
theorem runLoad_k (c : Config V k) (na : Fin k → V) (v : V) :
    runLoad c na k v = (univ.filter fun j => na j = v).card := by
  unfold runLoad; congr 1; ext j; simp [j.isLt]

omit [Fintype V] in
theorem runLoad_succ (c : Config V k) (na : Fin k → V) (i : Fin k) (v : V) :
    runLoad c na (i.val + 1) v + (if c.anchor i = v then 1 else 0) =
      runLoad c na i.val v + (if na i = v then 1 else 0) := by
  unfold runLoad
  rw [card_filter, card_filter, ← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]
  have : ∑ x ∈ univ.erase i, (if (x.val < i.val + 1 ∧ na x = v) ∨ (i.val + 1 ≤ x.val ∧ c.anchor x = v)
      then 1 else 0) = ∑ x ∈ univ.erase i,
        (if (x.val < i.val ∧ na x = v) ∨ (i.val ≤ x.val ∧ c.anchor x = v) then 1 else 0) := by
    apply sum_congr rfl
    intro x hx
    have hne : x.val ≠ i.val := fun h => (mem_erase.1 hx).1 (Fin.ext h)
    congr 1; apply propext
    constructor <;> rintro (h | h)
    · left; exact ⟨by omega, h.2⟩
    · right; exact ⟨by omega, h.2⟩
    · left; exact ⟨by omega, h.2⟩
    · right; exact ⟨by omega, h.2⟩
  rw [this]
  simp only [lt_add_one, true_and, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
    false_and, or_false, false_or, lt_self_iff_false, le_refl]
  omega

variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e) {d : ℕ}
include he

/-- One round of re-anchoring keeps the loads of the open depth-`d` nodes balanced, as long as no
open node is shallower than `d`. -/
theorem balanced_round (hd : 1 ≤ d) {t : ℕ} (hP : ∀ x, IsOpen T (e t) x → d ≤ T.depth x)
    (hstart : ∀ w ∈ openAt T e d t, ∀ w' ∈ openAt T e d t, anchCount e t w ≤ anchCount e t w' + 1) :
    ∀ w ∈ openAt T e d t, ∀ w' ∈ openAt T e d t,
      anchCount e (t + 1) w ≤ anchCount e (t + 1) w' + 1 := by
  set O := openAt T e d t
  set c := e t
  set na := (e (t + 1)).anchor
  have claim : ∀ m ≤ k, ∀ w ∈ O, ∀ w' ∈ O, runLoad c na m w ≤ runLoad c na m w' + 1 := by
    intro m
    induction m with
    | zero => intro _ w hw w' hw'; rw [runLoad_zero, runLoad_zero]; exact hstart w hw w' hw'
    | succ m ih =>
      intro hm w hw w' hw'
      set i : Fin k := ⟨m, by omega⟩
      have hs : ∀ v, runLoad c na (m + 1) v + (if c.anchor i = v then 1 else 0) =
          runLoad c na m v + (if na i = v then 1 else 0) := fun v => runLoad_succ c na i v
      by_cases hr : i ∈ act t ∧ c.pos i = T.root
      · have hanc : ∀ v ∈ O, c.anchor i ≠ v := by
          intro v hv h
          have hvr := ne_root_of_mem_openAt hd hv
          have hvo := (mem_openAt.1 hv).2
          rw [← h] at hvr hvo
          exact (he.inv t).off_root i hvr hvo hr.2
        have hcandw : IsCand T c w := ⟨(mem_openAt.1 hw).2, fun y hy => (mem_openAt.1 hw).1 ▸ hP y hy⟩
        obtain ⟨hg, hgmin⟩ := na_cand (he.reanchorOK t) hr.1 hr.2 ⟨w, hcandw⟩
        have hgO : na i ∈ O := by
          rw [mem_openAt]
          refine ⟨le_antisymm ?_ (hP _ hg.1), hg.1⟩
          have := hg.2 w (mem_openAt.1 hw).2; rw [(mem_openAt.1 hw).1] at this; exact this
        have hmin' : ∀ v ∈ O, runLoad c na m (na i) ≤ runLoad c na m v := by
          intro v hv
          have := hgmin v ⟨(mem_openAt.1 hv).2, fun y hy => (mem_openAt.1 hv).1 ▸ hP y hy⟩
          rwa [load_eq_runLoad, load_eq_runLoad] at this
        have h1 := hs w; have h2 := hs w'
        rw [ite_eq_right (hanc w hw)] at h1; rw [ite_eq_right (hanc w' hw')] at h2
        have ih' := ih (by omega) w hw w' hw'
        have hmw' := hmin' w' hw'
        have ihg := ih (by omega) w hw (na i) hgO
        split_ifs at h1 h2 with hw1 hw2 hw2 <;> (try subst_vars) <;> omega
      · have hna : na i = c.anchor i := na_eq_of_not (he.reanchorOK t) hr
        have h1 := hs w; have h2 := hs w'
        rw [hna] at h1 h2
        have := ih (by omega) w hw w' hw'
        split_ifs at h1 h2 <;> omega
  intro w hw w' hw'
  have := claim k le_rfl w hw w' hw'
  rwa [runLoad_k, runLoad_k] at this

end Balance

section Lemma2

variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e) {d : ℕ}
include he

/-- The window hypothesis of `alloc_bound` for the depth-`d` phase. -/
def WindowHyp (T : G.RootedTree) (act : ℕ → Finset (Fin k)) (e : ℕ → Config V k) (d Δ : ℕ) : Prop :=
  ∀ s, (∀ x, IsOpen T (e s) x → d ≤ T.depth x) → (openAt T e d s).Nonempty →
    (∀ w ∈ openAt T e d s, Δ ≤ anchCount e (s + 1) w + 1) →
    ∀ t₁, ∑ t ∈ Ico (s + 1) t₁, assignCount T act e d t +
      ∑ w ∈ openAt T e d s, (anchCount e (s + 1) w + 1) ≤
        k + ∑ w ∈ openAt T e d s \ openAt T e d (s + 1), (anchCount e s w + 1)

/-- Lemma 2 of the full version, generic form: given the window hypothesis for `Δ`, the number of
calls to `Reanchor` returning a node of depth `d ≥ 1` is at most `S_k(Δ)`. -/
theorem sum_assignCount_le_of_window (hd : 1 ≤ d) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hwin : WindowHyp T act e d Δ) (t₁ : ℕ) :
    ∑ t ∈ range t₁, assignCount T act e d t ≤ urnSum k Δ := by
  classical
  by_cases hex : ∃ t, ∀ x, IsOpen T (e t) x → d ≤ T.depth x
  · set t₀ := Nat.find hex
    have hP : ∀ x, IsOpen T (e t₀) x → d ≤ T.depth x := Nat.find_spec hex
    have hmin : ∀ t < t₀, ¬ ∀ x, IsOpen T (e t) x → d ≤ T.depth x :=
      fun t ht => Nat.find_min hex ht
    have hPs : ∀ s, t₀ ≤ s → ∀ x, IsOpen T (e s) x → d ≤ T.depth x :=
      fun s hs => he.open_depth_mono hP s hs
    have hstart : ∀ t, t₀ ≤ t → ∀ w ∈ openAt T e d t, ∀ w' ∈ openAt T e d t,
        anchCount e t w ≤ anchCount e t w' + 1 := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base =>
        intro w hw w' _
        rw [anchCount_eq_zero_init he hd hmin hw]; exact Nat.zero_le _
      | succ t ht ih =>
        intro w hw w' hw'
        have hsub := openAt_succ_subset he hP ht
        exact balanced_round he hd (hPs t ht) ih w (hsub hw) w' (hsub hw')
    exact alloc_bound k Δ hΔ (openAt T e d) (anchCount e) (assignCount T act e d) t₀
      (fun t ht => assignCount_eq_zero_of_not he hd (hmin t ht))
      (fun t ht => openAt_succ_subset he hP ht)
      (fun w hw => anchCount_eq_zero_init he hd hmin hw)
      (fun t _ w hw => anchCount_mono he hd hw)
      (fun t ht => assignCount_eq_sum he ht hd)
      (fun t ht => balanced_round he hd (hPs t ht) (hstart t ht))
      (fun t _ => sum_anchCount_add_one_le he hd t)
      (fun s hs hne hth t₁ => hwin s (hPs s hs) hne hth t₁) t₁
  · push Not at hex
    have : ∀ t, assignCount T act e d t = 0 := fun t =>
      assignCount_eq_zero_of_not he hd (by push Not; exact hex t)
    simp [this]

/-- Lemma 2 of the full version, `log k` part, for every execution (also with blocked robots):
at most `S_k(k) = ∑_{u=1}^{k} ⌈k/u⌉` calls to `Reanchor` return a node of depth `d ≥ 1`. -/
theorem sum_assignCount_le_k (hd : 1 ≤ d) (t₁ : ℕ) :
    ∑ t ∈ range t₁, assignCount T act e d t ≤ urnSum k (k + 1) := by
  apply sum_assignCount_le_of_window he hd (by omega)
  intro s _ hne hth
  exfalso
  obtain ⟨w, hw⟩ := hne
  have h1 := hth w hw
  have h2 := sum_anchCount_add_one_le he hd s
  have h3 := single_le_sum (f := fun w => anchCount e (s + 1) w + 1) (fun _ _ => Nat.zero_le _) hw
  omega

end Lemma2

end Podc.TreeExplorationBFDN
