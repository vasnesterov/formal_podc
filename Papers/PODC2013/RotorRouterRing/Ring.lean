import Papers.PODC2013.RotorRouterRing.Delayed

/-!
# The rotor-router on the ring

The `n`-node ring `ZMod n`: every node has two ports, port `0` leads to `v + 1` and port `1` to
`v - 1` (on the ring there is only one cyclic order of two arcs, so only the initial pointers
matter, as the paper notes in Section 1.3). A pointer `p` points to `v + 1` iff `p` is even.

This file provides
* the ring distance `ringDist v x` and its behaviour on neighbours;
* the **potential identity** (`potential_run`): for any `h : ZMod n → ℤ`,
  `Φ_h(c) = 2 Σ_u pos(u) h(u) + Σ_v h(pointer target of v)` changes in every round by
  `Σ_v (agents released from v) · (h(v+1) + h(v-1) - 2 h(v))`, so
  `Φ_h(run t) = Φ_h(c₀) + Σ_v e_v(t) · Δh(v)`. (This is the standard rotor-router potential of
  Holroyd–Propp type; it is not used in the paper, we use it to prove Theorem 3.7.)
-/

open Finset

namespace Podc.RotorRouterRing

variable {n : ℕ} [NeZero n]

set_option linter.unusedSectionVars false

/-- The `n`-node ring. -/
def ring (n : ℕ) [NeZero n] : RotorGraph (ZMod n) where
  deg _ := 2
  deg_pos _ := two_pos
  port v i := if (i : ℕ) = 0 then v + 1 else v - 1

lemma ring_target (v : ZMod n) (j : ℕ) :
    (ring n).target v j = if j % 2 = 0 then v + 1 else v - 1 := by
  simp [RotorGraph.target, ring]

lemma ring_target_add_two (v : ZMod n) (j : ℕ) :
    (ring n).target v (j + 2) = (ring n).target v j := by
  simp [ring_target, Nat.add_mod_right]

lemma ring_target_succ (v : ZMod n) (j : ℕ) :
    (ring n).target v (j + 1) = if j % 2 = 0 then v - 1 else v + 1 := by
  simp only [ring_target]
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h, Nat.add_mod]

/-! ### The potential identity -/

/-- Second difference (discrete Laplacian) on the ring. -/
def lap (h : ZMod n → ℤ) (v : ZMod n) : ℤ := h (v + 1) + h (v - 1) - 2 * h v

/-- The potential `Φ_h = 2 Σ_u pos(u) h(u) + Σ_v h(target of the pointer of v)`. -/
def potential (h : ZMod n → ℤ) (c : Config (ZMod n)) : ℤ :=
  2 * ∑ u, (c.pos u : ℤ) * h u + ∑ v, h ((ring n).target v (c.ptr v))

lemma sum_sent_mul (h : ZMod n → ℤ) (w : ZMod n) (p m : ℕ) :
    ∑ u, ((ring n).sent w p m u : ℤ) * h u = ∑ j ∈ range m, h ((ring n).target w (p + j)) := by
  induction m with
  | zero => simp [RotorGraph.sent]
  | succ m ih =>
    have : ∀ u, ((ring n).sent w p (m + 1) u : ℤ)
        = (ring n).sent w p m u + if (ring n).target w (p + m) = u then 1 else 0 := by
      intro u; simp only [RotorGraph.sent, Nat.count_succ]; push_cast; split_ifs <;> simp
    simp only [this, add_mul, Finset.sum_add_distrib, ih, Finset.sum_range_succ, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Per node: releasing `m` agents from `w` (pointer at `p`) changes the potential by `m Δh(w)`. -/
lemma node_identity (h : ZMod n → ℤ) (w : ZMod n) (p m : ℕ) :
    2 * ∑ j ∈ range m, h ((ring n).target w (p + j)) - 2 * m * h w
      + h ((ring n).target w (p + m)) - h ((ring n).target w p) = m * lap h w := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : (ring n).target w (p + (m + 1)) = if (p + m) % 2 = 0 then w - 1 else w + 1 := by
      rw [← add_assoc, ring_target_succ]
    have h1 := ring_target w (p + m)
    rw [Finset.sum_range_succ, h2]
    rw [h1] at ih ⊢
    unfold lap at *
    push_cast
    split_ifs at * <;> linarith

lemma pos_eq_sub (c₀ : Config (ZMod n)) (D : ℕ → ZMod n → ℕ) (t : ℕ) (u : ZMod n) :
    ((((ring n).run c₀ D t).pos u : ℕ) : ℤ)
      = ((ring n).visits c₀ D t u : ℤ) - (ring n).exits c₀ D t u := by
  have := RotorGraph.pos_add_exits (G := ring n) c₀ D t u
  omega

/-- **Potential identity**: `Φ_h(run t) = Φ_h(c₀) + Σ_v e_v(t) Δh(v)`, for any delayed
deployment. -/
theorem potential_run (h : ZMod n → ℤ) (c₀ : Config (ZMod n)) (D : ℕ → ZMod n → ℕ) (t : ℕ) :
    potential h ((ring n).run c₀ D t)
      = potential h c₀ + ∑ v, ((ring n).exits c₀ D t v : ℤ) * lap h v := by
  set E := (ring n).exits c₀ D t
  have hvis := RotorGraph.visits_eq_visitsOf (G := ring n) c₀ D t
  have hB : ∑ u, (∑ w, ((ring n).sent w (c₀.ptr w) (E w) u : ℤ)) * h u
      = ∑ w, ∑ j ∈ range (E w), h ((ring n).target w (c₀.ptr w + j)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [sum_sent_mul]
  have key : ∀ w, 2 * ∑ j ∈ range (E w), h ((ring n).target w (c₀.ptr w + j))
      = (E w : ℤ) * lap h w + 2 * (E w) * h w - h ((ring n).target w (c₀.ptr w + E w))
        + h ((ring n).target w (c₀.ptr w)) := fun w => by
    have := node_identity h w (c₀.ptr w) (E w); linarith
  have hsum : 2 * ∑ w, ∑ j ∈ range (E w), h ((ring n).target w (c₀.ptr w + j))
      = ∑ w, (E w : ℤ) * lap h w + 2 * ∑ w, (E w : ℤ) * h w
        - ∑ w, h ((ring n).target w (c₀.ptr w + E w)) + ∑ w, h ((ring n).target w (c₀.ptr w)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    congr 2; congr 1; apply Finset.sum_congr rfl; intro w _; ring
  simp only [potential, pos_eq_sub, RotorGraph.ptr_run, hvis, RotorGraph.visitsOf]
  push_cast
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, hB]
  linarith

/-- The pointer part of the potential never drops below its initial value if every initial
pointer points to the neighbour with the smaller value of `h`. -/
lemma ptr_term_ge (h : ZMod n → ℤ) (c₀ : Config (ZMod n)) (D : ℕ → ZMod n → ℕ)
    (hmin : ∀ v, h ((ring n).target v (c₀.ptr v)) ≤ h ((ring n).target v (c₀.ptr v + 1)))
    (t : ℕ) :
    ∑ v, h ((ring n).target v (c₀.ptr v))
      ≤ ∑ v, h ((ring n).target v (((ring n).run c₀ D t).ptr v)) := by
  gcongr with v
  generalize ((ring n).run c₀ D t).ptr v = q
  have hq : ∀ j, (ring n).target v j = (ring n).target v (c₀.ptr v) ∨
      (ring n).target v j = (ring n).target v (c₀.ptr v + 1) := by
    intro j
    simp only [ring_target]
    rcases Nat.mod_two_eq_zero_or_one j with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (c₀.ptr v) with h2 | h2 <;>
      simp [h1, h2, Nat.add_mod]
  rcases hq q with e | e <;> rw [e]
  exact hmin v

/-- In the undelayed system the exits from `v` in rounds `1..t` are the agents present on `v`
at the starts of these rounds. -/
lemma exits_undelayed (c₀ : Config (ZMod n)) (t : ℕ) (v : ZMod n) :
    (ring n).exits c₀ RotorGraph.undelayed t v
      = ∑ s ∈ range t, ((ring n).run c₀ RotorGraph.undelayed s).pos v := by
  simp [RotorGraph.exits, RotorGraph.moved, RotorGraph.undelayed]

/-! ### Distance on the ring -/

/-- Distance between `v` and `x` on the `n`-node ring. -/
def ringDist (v x : ZMod n) : ℕ := min (x - v).val (n - (x - v).val)

lemma val_add_one' (a : ZMod n) : (a + 1).val = (a.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]

lemma val_sub_one' (a : ZMod n) : (a - 1).val = if a.val = 0 then n - 1 else a.val - 1 := by
  have h := val_add_one' (a - 1)
  rw [sub_add_cancel] at h
  have hb := ZMod.val_lt (a - 1)
  have ha := ZMod.val_lt a
  rcases Nat.lt_or_ge ((a - 1).val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h; split_ifs <;> omega
  · have : (a - 1).val + 1 = n := by omega
    rw [this, Nat.mod_self] at h; split_ifs <;> omega

lemma ringDist_le_half (v x : ZMod n) : 2 * ringDist v x ≤ n := by
  unfold ringDist; omega

/-- Neighbours of a node at distance `d` (not too close to the antipode) are at distances
`d + 1` and `d - 1` (both at distance `1` if `d = 0`). -/
lemma ringDist_neighbors (v x : ZMod n) (hx : 2 * ringDist v x + 2 ≤ n) :
    (ringDist v (x + 1) = ringDist v x + 1 ∧
        ringDist v (x - 1) = if ringDist v x = 0 then 1 else ringDist v x - 1) ∨
      (ringDist v (x - 1) = ringDist v x + 1 ∧
        ringDist v (x + 1) = if ringDist v x = 0 then 1 else ringDist v x - 1) := by
  unfold ringDist at *
  rw [show x + 1 - v = (x - v) + 1 by ring, show x - 1 - v = (x - v) - 1 by ring,
    val_add_one', val_sub_one']
  have ha := ZMod.val_lt (x - v)
  set a := (x - v).val
  rcases Nat.lt_or_ge (a + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]; split_ifs <;> omega
  · have : a + 1 = n := by omega
    rw [this, Nat.mod_self]; split_ifs <;> omega

lemma ringDist_succ_ge (v x : ZMod n) : ringDist v x ≤ ringDist v (x + 1) + 1 := by
  unfold ringDist
  rw [show x + 1 - v = (x - v) + 1 by ring, val_add_one']
  have ha := ZMod.val_lt (x - v)
  rcases Nat.lt_or_ge ((x - v).val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]; omega
  · have : (x - v).val + 1 = n := by omega
    rw [this, Nat.mod_self]; omega

lemma ringDist_pred_ge (v x : ZMod n) : ringDist v x ≤ ringDist v (x - 1) + 1 := by
  unfold ringDist
  rw [show x - 1 - v = (x - v) - 1 by ring, val_sub_one']
  have ha := ZMod.val_lt (x - v)
  split_ifs <;> omega

lemma ringDist_self (v : ZMod n) : ringDist v v = 0 := by simp [ringDist]

lemma ringDist_eq_zero {v x : ZMod n} : ringDist v x = 0 ↔ x = v := by
  unfold ringDist
  have ha := ZMod.val_lt (x - v)
  constructor
  · intro h
    have : (x - v).val = 0 := by omega
    rw [ZMod.val_eq_zero, sub_eq_zero] at this; exact this
  · rintro rfl; simp

lemma ringDist_comm (v x : ZMod n) : ringDist v x = ringDist x v := by
  unfold ringDist
  rw [show v - x = -(x - v) by ring, ZMod.neg_val]
  have ha := ZMod.val_lt (x - v)
  split_ifs with h
  · simp [h]
  · omega

/-- A ball of radius `r` on the ring has at most `2r + 1` nodes. -/
lemma card_ball_le (x : ZMod n) (r : ℕ) :
    (univ.filter (fun v => ringDist v x ≤ r)).card ≤ 2 * r + 1 := by
  have hsub : univ.filter (fun v => ringDist v x ≤ r) ⊆
      (range (2 * r + 1)).image (fun j : ℕ => x + (j : ZMod n) - (r : ZMod n)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [ringDist_comm] at hv
    unfold ringDist at hv
    simp only [Finset.mem_image, Finset.mem_range]
    have ha := ZMod.val_lt (v - x)
    have hv' : (((v - x).val : ℕ) : ZMod n) = v - x := ZMod.natCast_zmod_val _
    rcases le_or_gt (v - x).val r with h | h
    · refine ⟨(v - x).val + r, by omega, ?_⟩
      push_cast; rw [hv']; ring
    · refine ⟨r - (n - (v - x).val), by omega, ?_⟩
      rw [Nat.cast_sub (by omega), Nat.cast_sub ha.le, ZMod.natCast_self, hv']; ring
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

end Podc.RotorRouterRing
