import Papers.PODC2013.RotorRouterRing.Theorem37

/-!
# A label-free version of Lemma 2.4 (pointers point away from the agents)

Lemma 2.4 of the paper describes the agent domains on the ring; its first property fails as
stated (`lemma_2_4_false`, agents may swap along an edge). The following invariant of the
undelayed system holds for every initialization and needs no agent identities:

between two consecutive occupied nodes, the empty nodes read `R…R U…U L…L`, where `R` (`L`) is a
visited node whose pointer points clockwise (counter-clockwise) and `U` is an unvisited node.

Equivalently (`pattern_invariant`), for two adjacent empty nodes `u, u + 1` the patterns
`(L, R)`, `(L, U)` and `(U, R)` never occur. So every visited empty node points away from the
nearest agent on its side, and the unvisited nodes form arcs bordered by pointers leading into
them — the content of the second property of Lemma 2.4 and of the domain picture.
-/

open Finset

namespace Podc.RotorRouterRing

open RotorGraph

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

/-- Pointer of `u` at the start of round `t + 1` points clockwise (to `u + 1`). -/
def PtsR (c₀ : Config (ZMod n)) (t : ℕ) (u : ZMod n) : Prop :=
  ((ring n).run c₀ undelayed t).ptr u % 2 = 0

/-- `u` has been visited by the end of round `t`. -/
def Vis (c₀ : Config (ZMod n)) (t : ℕ) (u : ZMod n) : Prop :=
  0 < (ring n).visits c₀ undelayed t u

lemma pos_succ_undelayed (c₀ : Config (ZMod n)) (t : ℕ) (w : ZMod n) :
    ((ring n).run c₀ undelayed (t + 1)).pos w
      = ∑ v, (ring n).sent v (((ring n).run c₀ undelayed t).ptr v)
          (((ring n).run c₀ undelayed t).pos v) w := by
  simp [run, step, undelayed]

lemma ptr_succ_undelayed (c₀ : Config (ZMod n)) (t : ℕ) (v : ZMod n) :
    ((ring n).run c₀ undelayed (t + 1)).ptr v
      = ((ring n).run c₀ undelayed t).ptr v + ((ring n).run c₀ undelayed t).pos v := by
  simp [run, step, undelayed]

lemma vis_succ (c₀ : Config (ZMod n)) (t : ℕ) (u : ZMod n) :
    Vis c₀ (t + 1) u ↔ Vis c₀ t u ∨ 0 < ((ring n).run c₀ undelayed (t + 1)).pos u := by
  have hv : (ring n).visits c₀ undelayed (t + 1) u = (ring n).visits c₀ undelayed t u +
      ∑ w, (ring n).sent w (((ring n).run c₀ undelayed t).ptr w)
        ((ring n).moved c₀ undelayed t w) u := by
    simp only [visits, Finset.sum_range_succ]; ring
  have hm : ∀ w, (ring n).moved c₀ undelayed t w = ((ring n).run c₀ undelayed t).pos w := by
    intro w; simp [moved, undelayed]
  simp only [hm] at hv
  rw [← pos_succ_undelayed] at hv
  simp only [Vis, hv]; omega

lemma vis_of_pos (c₀ : Config (ZMod n)) (t : ℕ) (u : ZMod n)
    (h : 0 < ((ring n).run c₀ undelayed t).pos u) : Vis c₀ t u := by
  have := pos_add_exits (G := ring n) c₀ undelayed t u
  simp only [Vis]; omega

lemma sent_right_pos (v : ZMod n) (p m : ℕ) (hm : 2 ≤ m ∨ (1 ≤ m ∧ p % 2 = 0)) :
    1 ≤ (ring n).sent v p m (v + 1) := by
  simp only [sent]
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · have : 1 ≤ m := by omega
    calc 1 = Nat.count (fun j => (ring n).target v (p + j) = v + 1) 1 := by
          simp [Nat.count_succ, ring_target, hp]
      _ ≤ _ := Nat.count_monotone _ this
  · have : 2 ≤ m := by omega
    calc 1 ≤ Nat.count (fun j => (ring n).target v (p + j) = v + 1) 2 := by
          simp [Nat.count_succ, ring_target, hp, Nat.add_mod]
      _ ≤ _ := Nat.count_monotone _ this

lemma sent_left_pos (v : ZMod n) (p m : ℕ) (hm : 2 ≤ m ∨ (1 ≤ m ∧ p % 2 = 1)) :
    1 ≤ (ring n).sent v p m (v - 1) := by
  simp only [sent]
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · have : 2 ≤ m := by omega
    calc 1 ≤ Nat.count (fun j => (ring n).target v (p + j) = v - 1) 2 := by
          simp [Nat.count_succ, ring_target, hp, Nat.add_mod]
      _ ≤ _ := Nat.count_monotone _ this
  · have : 1 ≤ m := by omega
    calc 1 = Nat.count (fun j => (ring n).target v (p + j) = v - 1) 1 := by
          simp [Nat.count_succ, ring_target, hp]
      _ ≤ _ := Nat.count_monotone _ this

/-- If nobody arrives at `u + 1`, the agents of `u` (if any) were a single agent sent to `u - 1`. -/
lemma left_mover (c₀ : Config (ZMod n)) (t : ℕ) (u : ZMod n)
    (h : ((ring n).run c₀ undelayed (t + 1)).pos (u + 1) = 0)
    (hu : 0 < ((ring n).run c₀ undelayed t).pos u) :
    ((ring n).run c₀ undelayed t).pos u = 1 ∧ ¬ PtsR c₀ t u := by
  rw [pos_succ_undelayed, Finset.sum_eq_zero_iff] at h
  have h1 := h u (Finset.mem_univ u)
  by_contra hc
  simp only [PtsR, not_and_or, not_not] at hc
  have := sent_right_pos u (((ring n).run c₀ undelayed t).ptr u)
    (((ring n).run c₀ undelayed t).pos u) (by omega)
  omega

/-- If nobody arrives at `u`, the agents of `u + 1` (if any) were a single agent sent to
`u + 2`. -/
lemma right_mover (c₀ : Config (ZMod n)) (t : ℕ) (u : ZMod n)
    (h : ((ring n).run c₀ undelayed (t + 1)).pos u = 0)
    (hu : 0 < ((ring n).run c₀ undelayed t).pos (u + 1)) :
    ((ring n).run c₀ undelayed t).pos (u + 1) = 1 ∧ PtsR c₀ t (u + 1) := by
  rw [pos_succ_undelayed, Finset.sum_eq_zero_iff] at h
  have h1 := h (u + 1) (Finset.mem_univ _)
  by_contra hc
  simp only [PtsR, not_and_or] at hc
  have := sent_left_pos (u + 1) (((ring n).run c₀ undelayed t).ptr (u + 1))
    (((ring n).run c₀ undelayed t).pos (u + 1)) (by omega)
  rw [show u + 1 - 1 = u by ring] at this
  omega

/-- The forbidden patterns `(L, R)`, `(L, U)`, `(U, R)` on two adjacent nodes. -/
def BadPair (c₀ : Config (ZMod n)) (t : ℕ) (u : ZMod n) : Prop :=
  (Vis c₀ t u ∧ ¬ PtsR c₀ t u ∧ Vis c₀ t (u + 1) ∧ PtsR c₀ t (u + 1)) ∨
    (Vis c₀ t u ∧ ¬ PtsR c₀ t u ∧ ¬ Vis c₀ t (u + 1)) ∨
    (¬ Vis c₀ t u ∧ Vis c₀ t (u + 1) ∧ PtsR c₀ t (u + 1))

/-- **Label-free domain invariant** (repaired Lemma 2.4): in the undelayed system, from any
initialization, two adjacent empty nodes never show the patterns `(L, R)`, `(L, U)`, `(U, R)`. -/
theorem pattern_invariant (c₀ : Config (ZMod n)) (t : ℕ) (u : ZMod n)
    (h0 : ((ring n).run c₀ undelayed t).pos u = 0)
    (h1 : ((ring n).run c₀ undelayed t).pos (u + 1) = 0) : ¬ BadPair c₀ t u := by
  induction t generalizing u with
  | zero =>
    have hv : ∀ w, ((ring n).run c₀ undelayed 0).pos w = 0 → ¬ Vis c₀ 0 w := by
      intro w hw; simp only [Vis, visits, Finset.range_zero, Finset.sum_empty, add_zero]
      simpa [run] using hw
    simp only [BadPair]
    have := hv u h0; have := hv (u + 1) h1
    tauto
  | succ t ih =>
    have hr := ptr_succ_undelayed c₀ t
    rcases Nat.eq_zero_or_pos (((ring n).run c₀ undelayed t).pos u) with a0 | a0 <;>
      rcases Nat.eq_zero_or_pos (((ring n).run c₀ undelayed t).pos (u + 1)) with b0 | b0
    · -- nothing moves on `u`, `u + 1`
      have hu : Vis c₀ (t + 1) u ↔ Vis c₀ t u := by rw [vis_succ, h0]; simp
      have hu1 : Vis c₀ (t + 1) (u + 1) ↔ Vis c₀ t (u + 1) := by rw [vis_succ, h1]; simp
      have pu : PtsR c₀ (t + 1) u ↔ PtsR c₀ t u := by simp only [PtsR, hr, a0, add_zero]
      have pu1 : PtsR c₀ (t + 1) (u + 1) ↔ PtsR c₀ t (u + 1) := by
        simp only [PtsR, hr, b0, add_zero]
      have := ih u a0 b0
      simp only [BadPair, hu, hu1, pu, pu1] at this ⊢
      exact this
    · -- only `u + 1` was occupied: it sent its single agent clockwise
      obtain ⟨e, hR⟩ := right_mover c₀ t u h0 b0
      have hv1 : Vis c₀ (t + 1) (u + 1) := (vis_succ c₀ t _).mpr (Or.inl (vis_of_pos c₀ t _ b0))
      have pu1 : ¬ PtsR c₀ (t + 1) (u + 1) := by
        simp only [PtsR, hr, e] at hR ⊢; omega
      simp only [BadPair]; tauto
    · -- only `u` was occupied: it sent its single agent counter-clockwise
      obtain ⟨e, hL⟩ := left_mover c₀ t u h1 a0
      have hv : Vis c₀ (t + 1) u := (vis_succ c₀ t _).mpr (Or.inl (vis_of_pos c₀ t _ a0))
      have pu : PtsR c₀ (t + 1) u := by
        simp only [PtsR, hr, e] at hL ⊢; omega
      simp only [BadPair]; tauto
    · obtain ⟨e, hL⟩ := left_mover c₀ t u h1 a0
      obtain ⟨e', hR⟩ := right_mover c₀ t u h0 b0
      have pu : PtsR c₀ (t + 1) u := by
        simp only [PtsR, hr, e] at hL ⊢; omega
      have pu1 : ¬ PtsR c₀ (t + 1) (u + 1) := by
        simp only [PtsR, hr, e'] at hR ⊢; omega
      simp only [BadPair]; tauto

end Podc.RotorRouterRing
