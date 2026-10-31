import Papers.PODC2015.LoopFreeUpdates.Basic

/-!
# Peacock (§4): the shortcut selection of odd rounds

In an odd round, Peacock (Algorithm 1, lines 6–9) considers the nodes whose new (dashed) rule points
forward on the current line, in order of non-increasing *distance* (the number of solid edges the
dashed edge skips), and greedily selects a node `u` unless some already selected `v` *blocks* it:
`v < u < out₂ v` or `v < out₂ u < out₂ v` (positions on the current line = the old route).

We abstract the outcome of the greedy procedure as `GoodSelection I C`:
* every selected node has a forward new rule;
* the intervals `[pos₁ c, pos₁ (out₂ c)]` of selected nodes do not overlap (they may touch);
* every forward node that was not selected is blocked by a selected node of at least its distance.

`greedy` is the concrete greedy procedure and `greedy_good` shows that it produces a good selection.
Everything downstream (Lemmas 2, 3 and Theorem 3) is proved for an arbitrary good selection, hence
for any tie-breaking among edges of equal distance.
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

variable {V : Type*} [DecidableEq V]

/-! ### List lemmas -/

theorem nextIn_cons (a : V) (l : List V) (u : V) :
    nextIn (a :: l) u = if a = u then l.head? else nextIn l u := by
  unfold nextIn
  rw [List.idxOf_cons]
  by_cases h : a = u
  · subst h; cases l <;> simp
  · simp [h]

/-- The first element of `l` satisfying `p`. -/
theorem head?_filter_eq_some_iff {l : List V} (hl : l.Nodup) {p : V → Bool} {w : V} :
    (l.filter p).head? = some w ↔
      w ∈ l ∧ p w ∧ ∀ x ∈ l, l.idxOf x < l.idxOf w → p x = false := by
  rw [List.head?_filter, List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hp, i, hi, rfl, hj⟩
    refine ⟨List.getElem_mem _, hp, fun x hx hlt => ?_⟩
    rw [hl.idxOf_getElem] at hlt
    have := hj _ hlt
    rw [List.getElem_idxOf] at this
    simpa using this
  · rintro ⟨hw, hp, hx⟩
    refine ⟨hp, l.idxOf w, List.idxOf_lt_length_of_mem hw, List.getElem_idxOf _, fun j hj => ?_⟩
    have := hx (l[j]'(by have := List.idxOf_lt_length_of_mem hw; omega)) (List.getElem_mem _)
      (by rw [hl.idxOf_getElem]; exact hj)
    simp [this]

/-- Consecutive elements of a filtered list. -/
theorem nextIn_filter {l : List V} (hl : l.Nodup) {p : V → Bool} {u w : V}
    (h : nextIn (l.filter p) u = some w) :
    u ∈ l ∧ w ∈ l ∧ p u ∧ p w ∧ l.idxOf u < l.idxOf w ∧
      ∀ x ∈ l, l.idxOf u < l.idxOf x → l.idxOf x < l.idxOf w → p x = false := by
  induction l with
  | nil => simp [nextIn] at h
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hidx : ∀ x ∈ l, (a :: l).idxOf x = l.idxOf x + 1 := by
      intro x hx
      rw [List.idxOf_cons]
      have : a ≠ x := fun e => hl.1 (e ▸ hx)
      simp [this]
    have hidxa : (a :: l).idxOf a = 0 := by simp
    by_cases hpa : p a = true
    · rw [List.filter_cons_of_pos hpa, nextIn_cons] at h
      split_ifs at h with hau
      · subst hau
        obtain ⟨hw, hpw, hx⟩ := (head?_filter_eq_some_iff hl.2).1 h
        refine ⟨by simp, by simp [hw], hpa, hpw, by rw [hidxa, hidx w hw]; omega, ?_⟩
        intro x hx' h1 h2
        rcases List.mem_cons.1 hx' with rfl | hxl
        · rw [hidxa] at h1; omega
        · rw [hidx x hxl, hidx w hw] at h2
          exact hx x hxl (by omega)
      · obtain ⟨hu, hw, hpu, hpw, hlt, hx⟩ := ih hl.2 h
        refine ⟨by simp [hu], by simp [hw], hpu, hpw, by rw [hidx u hu, hidx w hw]; omega, ?_⟩
        intro x hx' h1 h2
        rcases List.mem_cons.1 hx' with rfl | hxl
        · rw [hidxa] at h1; omega
        · rw [hidx x hxl, hidx u hu] at h1
          rw [hidx x hxl, hidx w hw] at h2
          exact hx x hxl (by omega) (by omega)
    · rw [List.filter_cons_of_neg hpa] at h
      obtain ⟨hu, hw, hpu, hpw, hlt, hx⟩ := ih hl.2 h
      refine ⟨by simp [hu], by simp [hw], hpu, hpw, by rw [hidx u hu, hidx w hw]; omega, ?_⟩
      intro x hx' h1 h2
      rcases List.mem_cons.1 hx' with rfl | hxl
      · simpa using hpa
      · rw [hidx x hxl, hidx u hu] at h1
        rw [hidx x hxl, hidx w hw] at h2
        exact hx x hxl (by omega) (by omega)

namespace Instance

variable (I : Instance V)

/-! ### Forward distances -/

/-- The position on the old route (the current line) of the target of the new rule of `v`
(`0` if `v` has no new rule). -/
def dpos (v : V) : ℕ := ((I.out₂ v).map I.pos₁).getD 0

/-- The *distance* of the dashed edge of `v`: the number of solid edges it skips. -/
def len (v : V) : ℕ := I.dpos v - I.pos₁ v

/-- `v` *blocks* `u` (Algorithm 1, line 8): `v < u < out₂ v` or `v < out₂ u < out₂ v`. -/
def Blocks (v u : V) : Prop :=
  (I.pos₁ v < I.pos₁ u ∧ I.pos₁ u < I.dpos v) ∨ (I.pos₁ v < I.dpos u ∧ I.dpos u < I.dpos v)

instance (v u : V) : Decidable (I.Blocks v u) := by unfold Blocks; infer_instance

theorem dpos_of_out₂ {v w : V} (h : I.out₂ v = some w) : I.dpos v = I.pos₁ w := by
  simp [dpos, h]

theorem out₂_of_fwd {v : V} (h : I.pos₁ v < I.dpos v) :
    ∃ w, I.out₂ v = some w ∧ I.pos₁ w = I.dpos v := by
  unfold dpos at *
  cases hv : I.out₂ v with
  | none => rw [hv] at h; simp at h
  | some w => exact ⟨w, rfl, by simp⟩

theorem mem_old_of_fwd {v : V} (h : I.pos₁ v < I.dpos v) : v ∈ I.old := by
  obtain ⟨w, hw, -⟩ := I.out₂_of_fwd h
  exact (I.out₂_spec hw).1

theorem dpos_lt_of_fwd {v : V} (h : I.pos₁ v < I.dpos v) : I.dpos v < I.old.length := by
  obtain ⟨w, hw, hpw⟩ := I.out₂_of_fwd h
  rw [← hpw]; exact I.pos₁_lt (I.out₂_spec hw).2.1

theorem fwd_iff_dashedFwd (v : V) : I.pos₁ v < I.dpos v ↔ I.DashedFwd v := by
  constructor
  · intro h
    obtain ⟨w, hw, hpw⟩ := I.out₂_of_fwd h
    exact ⟨w, hw, hpw ▸ h⟩
  · rintro ⟨w, hw, hlt⟩
    rw [I.dpos_of_out₂ hw]; exact hlt

/-- Two forward nodes, the shorter of which is not blocked by the longer one, have non-overlapping
intervals. -/
theorem disj_of_not_blocks {u v : V} (hu : I.pos₁ u < I.dpos u) (hv : I.pos₁ v < I.dpos v)
    (hne : u ≠ v) (hlen : I.len u ≤ I.len v) (hb : ¬ I.Blocks v u) :
    I.dpos u ≤ I.pos₁ v ∨ I.dpos v ≤ I.pos₁ u := by
  have hpos : I.pos₁ u ≠ I.pos₁ v := fun e =>
    hne (I.pos₁_inj (I.mem_old_of_fwd hu) (I.mem_old_of_fwd hv) e)
  unfold Blocks at hb
  unfold len at hlen
  omega

/-! ### Good selections -/

/-- The abstract properties of the set `C` of nodes selected in an odd (shortcut) round. -/
structure GoodSelection (C : Finset V) : Prop where
  /-- Selected nodes have forward new rules. -/
  fwd : ∀ c ∈ C, I.pos₁ c < I.dpos c
  /-- The intervals of selected nodes do not overlap. -/
  disj : ∀ a ∈ C, ∀ c ∈ C, a ≠ c → I.dpos a ≤ I.pos₁ c ∨ I.dpos c ≤ I.pos₁ a
  /-- Every forward node that is not selected is blocked by a selected node of at least its
  distance. -/
  blocked : ∀ u, I.pos₁ u < I.dpos u → u ∉ C → ∃ v ∈ C, I.len u ≤ I.len v ∧ I.Blocks v u

/-! ### The greedy selection (Algorithm 1, lines 6–9) -/

/-- Process one candidate: add it unless an already selected node blocks it. -/
def greedyStep (acc : List V) (u : V) : List V :=
  if acc.any (fun v => decide (I.Blocks v u)) then acc else u :: acc

/-- The nodes with a forward new rule. -/
def candidates : List V := I.old.filter (fun v => decide (I.pos₁ v < I.dpos v))

/-- The candidates sorted by non-increasing distance. -/
def sortedCandidates : List V :=
  I.candidates.mergeSort (fun a b => decide (I.len b ≤ I.len a))

/-- The greedy shortcut selection of an odd round. -/
def greedy : Finset V := (I.sortedCandidates.foldl I.greedyStep []).toFinset

theorem greedy_aux (L : List V) : ∀ (acc : List V),
    L.Pairwise (fun a b => I.len b ≤ I.len a) → L.Nodup → (∀ u ∈ L, I.pos₁ u < I.dpos u) →
    (∀ v ∈ acc, I.pos₁ v < I.dpos v) →
    (∀ a ∈ acc, ∀ c ∈ acc, a ≠ c → I.dpos a ≤ I.pos₁ c ∨ I.dpos c ≤ I.pos₁ a) →
    (∀ v ∈ acc, ∀ u ∈ L, I.len u ≤ I.len v) → (∀ v ∈ acc, v ∉ L) →
    (∀ v ∈ acc, v ∈ L.foldl I.greedyStep acc) ∧
    (∀ v ∈ L.foldl I.greedyStep acc, v ∈ acc ∨ v ∈ L) ∧
    (∀ a ∈ L.foldl I.greedyStep acc, ∀ c ∈ L.foldl I.greedyStep acc, a ≠ c →
      I.dpos a ≤ I.pos₁ c ∨ I.dpos c ≤ I.pos₁ a) ∧
    (∀ u ∈ L, u ∉ L.foldl I.greedyStep acc →
      ∃ v ∈ L.foldl I.greedyStep acc, I.len u ≤ I.len v ∧ I.Blocks v u) := by
  induction L with
  | nil =>
    intro acc _ _ _ _ hd _ _
    simp only [List.foldl_nil]
    exact ⟨fun v hv => hv, fun v hv => Or.inl hv, hd, by simp⟩
  | cons u L ih =>
    intro acc hs hnd hc hacc hd hge hnot
    rw [List.pairwise_cons] at hs
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    by_cases hb : ∃ v ∈ acc, I.Blocks v u
    · have hstep : I.greedyStep acc u = acc := by
        unfold greedyStep
        have : acc.any (fun v => decide (I.Blocks v u)) = true := by simpa using hb
        simp [this]
      rw [hstep]
      obtain ⟨h1, h2, h3, h4⟩ := ih acc hs.2 hnd.2 (fun x hx => hc x (by simp [hx])) hacc hd
        (fun v hv x hx => hge v hv x (by simp [hx]))
        (fun v hv hvL => hnot v hv (by simp [hvL]))
      refine ⟨h1, fun v hv => ?_, h3, ?_⟩
      · rcases h2 v hv with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
      · intro x hx hxR
        rcases List.mem_cons.1 hx with rfl | hx
        · obtain ⟨v, hv, hbv⟩ := hb
          exact ⟨v, h1 v hv, hge v hv x (by simp), hbv⟩
        · exact h4 x hx hxR
    · have hstep : I.greedyStep acc u = u :: acc := by
        unfold greedyStep
        have : acc.any (fun v => decide (I.Blocks v u)) = false := by simpa using hb
        simp [this]
      rw [hstep]
      have hu : I.pos₁ u < I.dpos u := hc u (by simp)
      have hunot : u ∉ acc := fun h => hnot u h (by simp)
      obtain ⟨h1, h2, h3, h4⟩ := ih (u :: acc) hs.2 hnd.2 (fun x hx => hc x (by simp [hx]))
        (by
          intro v hv
          rcases List.mem_cons.1 hv with rfl | hv
          · exact hu
          · exact hacc v hv)
        (by
          intro a ha c hc' hac
          rcases List.mem_cons.1 ha with ha1 | ha2
          · subst ha1
            rcases List.mem_cons.1 hc' with hc1 | hc2
            · exact absurd hc1.symm hac
            · exact I.disj_of_not_blocks hu (hacc c hc2) hac (hge c hc2 a (by simp))
                (fun h => hb ⟨c, hc2, h⟩)
          · rcases List.mem_cons.1 hc' with hc1 | hc2
            · subst hc1
              exact (I.disj_of_not_blocks hu (hacc a ha2) (Ne.symm hac) (hge a ha2 c (by simp))
                (fun h => hb ⟨a, ha2, h⟩)).symm
            · exact hd a ha2 c hc2 hac)
        (by
          intro v hv x hx
          rcases List.mem_cons.1 hv with rfl | hv
          · exact hs.1 x hx
          · exact hge v hv x (by simp [hx]))
        (by
          intro v hv hvL
          rcases List.mem_cons.1 hv with rfl | hv
          · exact hnd.1 hvL
          · exact hnot v hv (by simp [hvL]))
      refine ⟨fun v hv => h1 v (by simp [hv]), fun v hv => ?_, h3, ?_⟩
      · rcases h2 v hv with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr (by simp)
          · exact Or.inl h
        · exact Or.inr (by simp [h])
      · intro x hx hxR
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd (h1 x (by simp)) hxR
        · exact h4 x hx hxR

theorem mem_sortedCandidates {v : V} :
    v ∈ I.sortedCandidates ↔ v ∈ I.old ∧ I.pos₁ v < I.dpos v := by
  unfold sortedCandidates
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp [candidates]

/-- The greedy procedure of Algorithm 1 (lines 6–9) produces a good selection. -/
theorem greedy_good : I.GoodSelection I.greedy := by
  have hs : I.sortedCandidates.Pairwise (fun a b => I.len b ≤ I.len a) := by
    have := List.pairwise_mergeSort (le := fun a b => decide (I.len b ≤ I.len a))
      (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) I.candidates
    unfold sortedCandidates
    simpa using this
  have hnd : I.sortedCandidates.Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.2 (I.nodup.filter _)
  obtain ⟨-, h2, h3, h4⟩ := I.greedy_aux I.sortedCandidates [] hs hnd
    (fun u hu => ((I.mem_sortedCandidates).1 hu).2) (by simp) (by simp) (by simp) (by simp)
  refine ⟨fun c hc => ?_, fun a ha c hc hac => ?_, fun u hu huC => ?_⟩
  · rw [greedy, List.mem_toFinset] at hc
    rcases h2 c hc with h | h
    · simp at h
    · exact ((I.mem_sortedCandidates).1 h).2
  · rw [greedy, List.mem_toFinset] at ha hc
    exact h3 a ha c hc hac
  · rw [greedy, List.mem_toFinset] at huC
    obtain ⟨v, hv, hlen, hb⟩ := h4 u ((I.mem_sortedCandidates).2 ⟨I.mem_old_of_fwd hu, hu⟩) huC
    exact ⟨v, by rw [greedy, List.mem_toFinset]; exact hv, hlen, hb⟩

end Instance

end Podc.LoopFreeUpdates
