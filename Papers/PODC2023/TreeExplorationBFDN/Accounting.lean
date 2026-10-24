import Papers.PODC2023.TreeExplorationBFDN.Motion

/-!
# Counting moves (Claims 2 and 3 of the full version)

Every move of a robot is down or up; robots start at the root, so there are at most as many up
moves as down moves. A down move either discovers a new node (a depth-next move through a
dangling edge; distinct robots discover distinct nodes, Claim 2) or is a breadth-first move,
and the breadth-first moves are paid for by the depths of the anchors assigned by `Reanchor`.
Hence (`sum_moved_le`)

  `#moves before t ≤ 2 (#visited nodes − 1) + 2 ∑ (depths of the anchors assigned before t)`,

which is the content of Claims 2–3 used in the proof of Theorem 2.1 (we do not need the exact
per-trip identity of Claim 3).
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [Fintype V] [DecidableEq V]

/-- Remaining breadth-first moves of robot `i` (the size of its stack `S_i`). -/
def bfRem (T : G.RootedTree) (c : Config V k) (i : Fin k) : ℕ :=
  if c.bf i = true then T.depth (c.anchor i) - T.depth (c.pos i) else 0

/-- Robots that move in round `t`. -/
def movedSet (e : ℕ → Config V k) (t : ℕ) : Finset (Fin k) :=
  univ.filter fun i => (e (t + 1)).pos i ≠ (e t).pos i

/-- Sum of the depths of the anchors assigned by `Reanchor` in round `t`. -/
def assignDepth (T : G.RootedTree) (act : ℕ → Finset (Fin k)) (e : ℕ → Config V k) (t : ℕ) : ℕ :=
  ∑ i ∈ univ.filter (fun i => i ∈ act t ∧ (e t).pos i = T.root), T.depth ((e (t + 1)).anchor i)

variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e)
include he

/-- Per robot: a move costs at most two down moves (amortized by the depth). -/
theorem moved_depth_le (t : ℕ) (i : Fin k) :
    (if (e (t + 1)).pos i ≠ (e t).pos i then 1 else 0) + T.depth ((e (t + 1)).pos i) ≤
      T.depth ((e t).pos i) +
        2 * (if T.depth ((e (t + 1)).pos i) = T.depth ((e t).pos i) + 1 then 1 else 0) := by
  rcases he.pos_succ_cases t i with h | h | ⟨hne, h⟩
  · rw [h]; simp
  · rw [h]
    by_cases hr : (e t).pos i = T.root
    · rw [hr, T.parent_root]; simp
    · have := T.depth_parent _ hr
      have hne : T.parent ((e t).pos i) ≠ (e t).pos i := RootedTree.parent_ne_self hr
      split_ifs <;> omega
  · have := T.depth_parent _ hne
    rw [h] at this
    have hne' : (e (t + 1)).pos i ≠ (e t).pos i := by
      intro h'; rw [h'] at this; omega
    split_ifs <;> omega

/-- Per robot: a down move to an already visited node is a breadth-first move, paid by the stack. -/
theorem bfRem_step (t : ℕ) (i : Fin k) :
    bfRem T (e (t + 1)) i +
        (if T.depth ((e (t + 1)).pos i) = T.depth ((e t).pos i) + 1 ∧
            (e (t + 1)).pos i ∈ (e t).vis then 1 else 0) ≤
      bfRem T (e t) i +
        (if i ∈ act t ∧ (e t).pos i = T.root then T.depth ((e (t + 1)).anchor i) else 0) := by
  have hI := he.inv t
  have hR := he.reanchorOK t
  have hM := he.moveOK t
  have heq := he.eq_after t
  by_cases hi : i ∈ act t
  · have hbf : (e (t + 1)).bf i =
        (bf0 T (act t) (e t) (e (t + 1)).anchor i && decide ((e (t + 1)).pos i ≠ (e (t + 1)).anchor i)) := by
      have := after_bf_active (T := T) (c := e t) (na := (e (t + 1)).anchor)
        (tgt := (e (t + 1)).pos) hi
      rwa [← heq] at this
    cases hb : bf0 T (act t) (e t) (e (t + 1)).anchor i
    · -- depth-next: no breadth-first move, empty stack afterwards
      rw [hb] at hbf
      have h0 : bfRem T (e (t + 1)) i = 0 := by simp [bfRem, hbf]
      rw [h0]
      have hc : ¬ (T.depth ((e (t + 1)).pos i) = T.depth ((e t).pos i) + 1 ∧
          (e (t + 1)).pos i ∈ (e t).vis) := by
        rcases tgt_dn_cases hM hi hb with hd | ⟨_, hup⟩
        · exact fun h => hd.2.2.1 h.2
        · intro h; rw [hup] at h; have := depth_parent_le T ((e t).pos i); omega
      rw [ite_eq_right hc]; omega
    · obtain ⟨hs, hlt⟩ := bf0_true_spec hI hR hb
      have htg := tgt_bf hM hi hb
      have hdt := depth_towards hs hlt
      rw [← htg] at hdt
      have hvis : (e (t + 1)).pos i ∈ (e t).vis := by
        rw [htg]; exact hI.vis_of_inSub towards_inSub (na_vis hI hR i)
      rw [ite_eq_left ⟨hdt, hvis⟩]
      have hnew : bfRem T (e (t + 1)) i + 1 = T.depth ((e (t + 1)).anchor i) - T.depth ((e t).pos i) := by
        unfold bfRem
        rw [hbf, hb]
        by_cases hta : (e (t + 1)).pos i = (e (t + 1)).anchor i
        · simp only [hta, ne_eq, not_true_eq_false, decide_false, Bool.true_and, Bool.false_eq_true,
            ↓reduceIte]
          rw [← hta]; omega
        · simp only [ne_eq, hta, not_false_eq_true, decide_true, Bool.true_and, ↓reduceIte]
          omega
      by_cases hr : i ∈ act t ∧ (e t).pos i = T.root
      · rw [ite_eq_left hr]
        have h0 : bfRem T (e t) i = 0 := by
          unfold bfRem
          have : (e t).bf i = false := by
            by_contra hc; simp only [Bool.not_eq_false] at hc
            exact (hI.bf_spec i hc).1 hr.2
          simp [this]
        omega
      · rw [ite_eq_right hr]
        have hb' : (e t).bf i = true := by rw [bf0_of_not hr] at hb; exact hb
        have hna := na_eq_of_not hR hr
        unfold bfRem at ⊢
        rw [ite_eq_left hb', ← hna]
        unfold bfRem at hnew
        omega
  · -- blocked robot: nothing changes
    have hp := tgt_inactive hM hi
    have hna := na_eq_of_inactive hR hi
    have hbf := after_bf_inactive (T := T) (c := e t) (na := (e (t + 1)).anchor)
      (tgt := (e (t + 1)).pos) hi
    rw [← heq] at hbf
    have hc1 : ¬ (i ∈ act t ∧ (e t).pos i = T.root) := fun h => hi h.1
    have hc2 : ¬ (T.depth ((e (t + 1)).pos i) = T.depth ((e t).pos i) + 1 ∧
        (e (t + 1)).pos i ∈ (e t).vis) := by intro h; rw [hp] at h; omega
    rw [ite_eq_right hc1, ite_eq_right hc2]
    unfold bfRem; rw [hbf, hp, hna]

/-- Claim 2: the number of newly visited nodes equals the number of robots moving to an unvisited
node (distinct robots discover distinct nodes). -/
theorem card_vis_succ (t : ℕ) :
    (e (t + 1)).vis.card = (e t).vis.card +
      (univ.filter fun i => (e (t + 1)).pos i ∉ (e t).vis).card := by
  have hI := he.inv t
  have heq := he.eq_after t
  have hvis : (e (t + 1)).vis = (e t).vis ∪
      ((univ.filter fun i => (e (t + 1)).pos i ∉ (e t).vis).image (e (t + 1)).pos) := by
    conv_lhs => rw [heq]
    ext x
    simp only [after_vis, mem_union, mem_image, mem_univ, true_and, mem_filter]
    constructor
    · rintro (h | ⟨i, rfl⟩)
      · exact Or.inl h
      · by_cases h : (e (t + 1)).pos i ∈ (e t).vis
        · exact Or.inl h
        · exact Or.inr ⟨i, h, rfl⟩
    · rintro (h | ⟨i, _, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, rfl⟩
  rw [hvis, card_union_of_disjoint, card_image_of_injOn]
  · intro i hi j _ hij
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi
    exact tgt_inj_of_not_vis hI (he.reanchorOK t) (he.moveOK t) hi hij
  · rw [disjoint_right]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    exact (mem_filter.1 hi).2

/-- Claims 2–3: moves are bounded by twice the discovered nodes plus twice the depths of the
assigned anchors. -/
theorem sum_moved_le (t₁ : ℕ) :
    ∑ t ∈ range t₁, (movedSet e t).card ≤
      2 * ((e t₁).vis.card - 1) + 2 * ∑ t ∈ range t₁, assignDepth T act e t := by
  -- potentials
  set Φ1 : ℕ → ℕ := fun t => ∑ i, T.depth ((e t).pos i)
  set Φ3 : ℕ → ℕ := fun t => ∑ i, bfRem T (e t) i
  set down : ℕ → ℕ := fun t => ∑ i,
    (if T.depth ((e (t + 1)).pos i) = T.depth ((e t).pos i) + 1 then 1 else 0)
  set bfd : ℕ → ℕ := fun t => ∑ i, (if T.depth ((e (t + 1)).pos i) = T.depth ((e t).pos i) + 1 ∧
            (e (t + 1)).pos i ∈ (e t).vis then 1 else 0)
  set dnd : ℕ → ℕ := fun t => (univ.filter fun i => (e (t + 1)).pos i ∉ (e t).vis).card
  have h1 : ∀ t, (movedSet e t).card + Φ1 (t + 1) ≤ Φ1 t + 2 * down t := by
    intro t
    have := sum_le_sum (fun i (_ : i ∈ univ) => moved_depth_le he t i)
    simp only [sum_add_distrib, ← mul_sum] at this
    have hc : (movedSet e t).card = ∑ i, (if (e (t + 1)).pos i ≠ (e t).pos i then 1 else 0) := by
      simp [movedSet, card_filter]
    rw [hc]; exact this
  have h2 : ∀ t, down t ≤ bfd t + dnd t := by
    intro t
    simp only [down, bfd, dnd, card_filter, ← sum_add_distrib]
    apply sum_le_sum; intro i _
    split_ifs <;> simp_all
  have h3 : ∀ t, Φ3 (t + 1) + bfd t ≤ Φ3 t + assignDepth T act e t := by
    intro t
    have := sum_le_sum (fun i (_ : i ∈ univ) => bfRem_step he t i)
    simp only [sum_add_distrib] at this
    simpa [Φ3, bfd, assignDepth, sum_filter] using this
  have h4 : ∀ t, (e (t + 1)).vis.card = (e t).vis.card + dnd t := fun t => card_vis_succ he t
  have hΦ1 : Φ1 0 = 0 := by simp [Φ1, he.1, init, T.depth_root]
  have hΦ3 : Φ3 0 = 0 := by simp [Φ3, he.1, init, bfRem]
  have hvis0 : (e 0).vis.card = 1 := by simp [he.1, init]
  -- sum up
  have s1 : ∀ n, ∑ t ∈ range n, (movedSet e t).card + Φ1 n ≤ 2 * ∑ t ∈ range n, down t := by
    intro n
    induction n with
    | zero => simp [hΦ1]
    | succ n ih => rw [sum_range_succ, sum_range_succ]; have := h1 n; omega
  have s3 : ∀ n, ∑ t ∈ range n, bfd t + Φ3 n ≤ ∑ t ∈ range n, assignDepth T act e t := by
    intro n
    induction n with
    | zero => simp [hΦ3]
    | succ n ih => rw [sum_range_succ, sum_range_succ]; have := h3 n; omega
  have s4 : ∀ n, (e n).vis.card = 1 + ∑ t ∈ range n, dnd t := by
    intro n
    induction n with
    | zero => simp [hvis0]
    | succ n ih => rw [sum_range_succ, h4 n, ih]; ring
  have := s1 t₁; have := s3 t₁; have := s4 t₁
  have s2 : ∑ t ∈ range t₁, down t ≤ ∑ t ∈ range t₁, bfd t + ∑ t ∈ range t₁, dnd t := by
    rw [← sum_add_distrib]; exact sum_le_sum fun t _ => h2 t
  omega

end Podc.TreeExplorationBFDN
