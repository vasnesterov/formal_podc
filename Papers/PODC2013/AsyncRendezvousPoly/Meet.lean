import Papers.PODC2013.AsyncRendezvousPoly.Model

/-!
# Forcing meetings: the two basic arguments

All synchronization arguments of Section 3 reduce to two facts about the continuous model, both
proved with the intermediate value theorem.

* `meet_of_rep` (the core of Lemma 3.1, "catching"): if agent `a` follows a trajectory `T` (forward)
  while agent `b` keeps repeating `T T̄`, they meet. We map the position of `b` to a coordinate on
  `T` with a continuous triangle wave (`foldR`, written with `arccos ∘ cos`), and apply the IVT to
  the difference of the coordinates of `a` and `b`.
* `meet_of_count` ("an integral trajectory forces progress"): if `b` follows `c` consecutive
  integral trajectories while `a` performs at most `c` edge traversals, they meet. Some integral
  trajectory of `b` is followed while `a` stays inside one closed edge `e`; `b` traverses `e` during
  it, and the IVT on `e` gives the meeting (`meet_of_edge`).

**Remark (imprecision in the paper).** The paper's informal version of the second fact (§3, "if one
agent follows an integral trajectory during some time interval, then it must either meet the other
agent or this other agent must perform at least one complete edge traversal during this time
interval") is false as stated for the continuous model: the other agent may cross a node in the
middle of an edge-to-edge move without completing any edge traversal inside the interval (see
`differencies.md`). The counting form that the proofs actually use is correct and is
`meet_of_count` (with `≥` instead of the paper's `>`).
-/

namespace Podc.AsyncRendezvousPoly

open Set Real

variable {V : Type*} [DecidableEq V]

/-! ### The triangle wave -/

/-- The continuous triangle wave of period `2L` and amplitude `L`. -/
noncomputable def foldR (L : ℝ) (y : ℝ) : ℝ := L / π * arccos (cos (π * y / L))

theorem continuous_foldR (L : ℝ) : Continuous (foldR L) := by
  unfold foldR; fun_prop

theorem foldR_nonneg {L : ℝ} (hL : 0 ≤ L) (y : ℝ) : 0 ≤ foldR L y :=
  mul_nonneg (div_nonneg hL pi_pos.le) (arccos_nonneg _)

theorem foldR_le {L : ℝ} (hL : 0 < L) (y : ℝ) : foldR L y ≤ L := by
  unfold foldR
  have := arccos_le_pi (cos (π * y / L))
  calc L / π * arccos (cos (π * y / L)) ≤ L / π * π :=
        mul_le_mul_of_nonneg_left this (div_nonneg hL.le pi_pos.le)
    _ = L := by field_simp

/-- `foldR` interpolates `foldN` linearly. -/
theorem foldR_nat_add {L : ℕ} (hL : 0 < L) (i : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    foldR L (i + c) = foldN L i + c * ((foldN L (i + 1) : ℝ) - foldN L i) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set j := i % (2 * L) with hj
  have hi : (i : ℝ) = j + (i / (2 * L) : ℕ) * (2 * L) := by
    have := Nat.mod_add_div i (2 * L); rw [← hj] at this
    have : (i : ℝ) = (j + 2 * L * (i / (2 * L)) : ℕ) := by rw [this]
    rw [this]; push_cast; ring
  have hcos : cos (π * (i + c) / L) = cos (π * (j + c) / L) := by
    rw [hi, show π * (j + (i / (2 * L) : ℕ) * (2 * L) + c) / L
        = π * (j + c) / L + ((i / (2 * L) : ℕ) : ℝ) * (2 * π) by field_simp; ring]
    exact cos_add_nat_mul_two_pi _ _
  have hjm : j < 2 * L := Nat.mod_lt _ (by omega)
  unfold foldR; rw [hcos]
  rcases foldN_succ hL i with ⟨h, h'⟩ | ⟨h, h'⟩
  · have hf : foldN L i = j := by unfold foldN; rw [← hj]; split_ifs <;> omega
    rw [h', hf, arccos_cos (by positivity)]
    · push_cast; field_simp; ring
    · rw [div_le_iff₀ hLr]
      have : (j : ℝ) + c ≤ L := by
        have : (j : ℝ) + 1 ≤ L := by exact_mod_cast h
        linarith
      nlinarith [pi_pos]
  · have hf : foldN L i = 2 * L - j := by
      unfold foldN; split_ifs with h2
      · omega
      · rfl
    have hf' : (foldN L (i + 1) : ℝ) = foldN L i - 1 := by
      have : foldN L (i + 1) = foldN L i - 1 := by omega
      rw [this, Nat.cast_sub (by omega)]; simp
    have hfr : (foldN L i : ℝ) = 2 * L - j := by rw [hf, Nat.cast_sub (by omega)]; push_cast; ring
    rw [hf', hfr]
    have hc : cos (π * (j + c) / L) = cos (π * (2 * L - j - c) / L) := by
      rw [show π * (2 * L - j - c) / L = 2 * π - π * (j + c) / L by field_simp; ring,
        cos_two_pi_sub]
    have hjr : (L : ℝ) ≤ j := by exact_mod_cast h
    have hjr' : (j : ℝ) + 1 ≤ 2 * L := by exact_mod_cast hjm
    rw [hc, arccos_cos]
    · field_simp; ring
    · apply div_nonneg _ hLr.le; nlinarith [pi_pos]
    · rw [div_le_iff₀ hLr]; nlinarith [pi_pos]

/-- Linear interpolation between two consecutive positions `a`, `b = a ± 1` of a route. -/
theorem posR_interp (f : ℕ → V) {a b : ℕ} (hab : b = a + 1 ∨ b + 1 = a) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    posR f (a + c * ((b : ℝ) - a)) = point (f a) (f b) c := by
  rcases hab with rfl | rfl
  · push_cast; rw [show (a : ℝ) + c * (a + 1 - a) = a + c by ring, posR_nat_add f a hc0 hc1]
  · push_cast
    rw [show (b : ℝ) + 1 + c * (b - (b + 1)) = b + (1 - c) by ring,
      posR_nat_add f b (by linarith) (by linarith), point_symm]
    simp

/-- The position along a repeated `T T̄` is the position along `T` at the folded coordinate. -/
theorem posR_rep {T : Traj V} (hT : 1 ≤ T.len) {c β : ℕ} {r : ℕ → V} (h : RepOcc T c β r)
    (hc : 1 ≤ c) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ (c * (2 * T.len) : ℕ)) :
    posR r (β + y) = posR T.f (foldR T.len y) := by
  obtain ⟨i, hi, c', hc0, hc1, rfl⟩ := exists_nat_add (by nlinarith) hy0 hy1
  rw [show (β : ℝ) + (i + c') = ((β + i : ℕ) : ℝ) + c' by push_cast; ring,
    posR_nat_add r _ hc0 hc1, foldR_nat_add (by omega) i hc0 hc1,
    posR_interp T.f _ hc0 hc1, h i hi.le, show β + i + 1 = β + (i + 1) by ring, h (i + 1) hi]
  rcases foldN_succ (show 0 < T.len by omega) i with ⟨-, h'⟩ | ⟨-, h'⟩
  · exact Or.inl h'
  · exact Or.inr h'

/-- The position along an occurrence of `T`. -/
theorem posR_occ {T : Traj V} (hT : 1 ≤ T.len) {α : ℕ} {r : ℕ → V} (h : Occ T r α) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ T.len) : posR r (α + x) = posR T.f x := by
  obtain ⟨i, hi, c', hc0, hc1, rfl⟩ := exists_nat_add hT hx0 hx1
  rw [show (α : ℝ) + (i + c') = ((α + i : ℕ) : ℝ) + c' by push_cast; ring,
    posR_nat_add r _ hc0 hc1, posR_nat_add T.f _ hc0 hc1, h i hi.le,
    show α + i + 1 = α + (i + 1) by ring, h (i + 1) hi]

/-! ### Intermediate value theorem helpers -/

theorem exists_eq_of_le_of_ge {f g : ℝ → ℝ} {s e : ℝ} (hse : s ≤ e)
    (hf : ContinuousOn f (Icc s e)) (hg : ContinuousOn g (Icc s e)) (h1 : f s ≤ g s)
    (h2 : g e ≤ f e) : ∃ t ∈ Icc s e, f t = g t := by
  have := intermediate_value_Icc hse (hf.sub hg)
  obtain ⟨t, ht, h⟩ := this (show (0 : ℝ) ∈ Icc ((f - g) s) ((f - g) e) from
    ⟨by simp only [Pi.sub_apply]; linarith, by simp only [Pi.sub_apply]; linarith⟩)
  exact ⟨t, ht, by simpa [sub_eq_zero] using h⟩

omit [DecidableEq V] in
/-- Two consecutive repetitions of `T T̄` form one. -/
theorem RepOcc.append {T : Traj V} {c₁ c₂ β : ℕ} {r : ℕ → V} (h₁ : RepOcc T c₁ β r)
    (h₂ : RepOcc T c₂ (β + c₁ * (2 * T.len)) r) : RepOcc T (c₁ + c₂) β r := fun i hi => by
  by_cases h : i ≤ c₁ * (2 * T.len)
  · exact h₁ i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = c₁ * (2 * T.len) + j := ⟨i - c₁ * (2 * T.len), by omega⟩
    rw [← add_assoc, h₂ j (by nlinarith), foldN_add_mul]

/-! ### The two meeting lemmas -/

variable {ra rb : ℕ → V} {Wa Wb : Walk}

/-- If agent `b` traverses (in either direction) the edge `{ra j, ra (j+1)}` while agent `a` is on
this edge, they meet. -/
theorem meet_of_edge {j k : ℕ} (h1 : Wa.τ j ≤ Wb.τ k) (h2 : Wb.τ (k + 1) ≤ Wa.τ (j + 1))
    (he : (rb k = ra j ∧ rb (k + 1) = ra (j + 1)) ∨ (rb k = ra (j + 1) ∧ rb (k + 1) = ra j)) :
    ∃ t, Meet ra rb Wa Wb t ∧ t ≤ Wb.τ (k + 1) := by
  have hse := (Wb.τ_lt (Nat.lt_succ_self k)).le
  have hsub : Icc (Wb.τ k) (Wb.τ (k + 1)) ⊆ Icc (Wa.τ j) (Wa.τ (j + 1)) :=
    Icc_subset_Icc h1 h2
  have hca : ContinuousOn (fun t => Wa.p t - j) (Icc (Wb.τ k) (Wb.τ (k + 1))) :=
    ((Wa.cont j).mono hsub).sub continuousOn_const
  have hcb : ContinuousOn (fun t => Wb.p t - k) (Icc (Wb.τ k) (Wb.τ (k + 1))) :=
    (Wb.cont k).sub continuousOn_const
  have hpa : ∀ t ∈ Icc (Wb.τ k) (Wb.τ (k + 1)), Wa.p t - j ∈ Icc (0 : ℝ) 1 := fun t ht => by
    have := Wa.p_mem j t (hsub ht); constructor <;> linarith [this.1, this.2]
  have hpb : ∀ t ∈ Icc (Wb.τ k) (Wb.τ (k + 1)), Wb.p t - k ∈ Icc (0 : ℝ) 1 := fun t ht => by
    have := Wb.p_mem k t ht; constructor <;> linarith [this.1, this.2]
  have hdom : ∀ t ∈ Icc (Wb.τ k) (Wb.τ (k + 1)), 0 ≤ t ∧ (∃ i, t ≤ Wa.τ i) ∧ ∃ i, t ≤ Wb.τ i :=
    fun t ht => ⟨le_trans (Wb.τ_nonneg k) ht.1, ⟨j + 1, (hsub ht).2⟩, ⟨k + 1, ht.2⟩⟩
  rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · -- same direction
    obtain ⟨t, ht, heq⟩ := exists_eq_of_le_of_ge hse hcb hca
      (by simp only [Wb.p_τ, sub_self]; exact (hpa _ (left_mem_Icc.2 hse)).1)
      (by simp only [Wb.p_τ]; push_cast; simp only [add_sub_cancel_left]
          exact (hpa _ (right_mem_Icc.2 hse)).2)
    refine ⟨t, ⟨(hdom t ht).1, (hdom t ht).2.1, (hdom t ht).2.2, ?_⟩, ht.2⟩
    have ha : Wa.p t = j + (Wa.p t - j) := by ring
    have hb : Wb.p t = k + (Wa.p t - j) := by rw [← heq]; ring
    rw [ha, posR_nat_add ra j (hpa t ht).1 (hpa t ht).2, hb,
      posR_nat_add rb k (hpa t ht).1 (hpa t ht).2, e1, e2]
  · -- opposite directions
    have hcb' : ContinuousOn (fun t => 1 - (Wb.p t - k)) (Icc (Wb.τ k) (Wb.τ (k + 1))) :=
      continuousOn_const.sub hcb
    obtain ⟨t, ht, heq⟩ := exists_eq_of_le_of_ge hse hca hcb'
      (by simp only [Wb.p_τ, sub_self, sub_zero]; exact (hpa _ (left_mem_Icc.2 hse)).2)
      (by simp only [Wb.p_τ]; push_cast; simp only [add_sub_cancel_left, sub_self]
          exact (hpa _ (right_mem_Icc.2 hse)).1)
    refine ⟨t, ⟨(hdom t ht).1, (hdom t ht).2.1, (hdom t ht).2.2, ?_⟩, ht.2⟩
    have ha : Wa.p t = j + (Wa.p t - j) := by ring
    have hb : Wb.p t = k + (1 - (Wa.p t - j)) := by rw [heq]; ring
    have h0 := hpa t ht
    rw [ha, posR_nat_add ra j h0.1 h0.2, hb,
      posR_nat_add rb k (by linarith [h0.2]) (by linarith [h0.1]), e1, e2, point_symm]

-- CSLib candidate
/-- **Catching** (the core of Lemma 3.1). If agent `a` follows the whole trajectory `T` (occurring
at index `α` of its route) during a time interval in which agent `b` keeps repeating `T T̄`
(`c` times from index `β` of its route), the agents meet (before `a` completes `T`). -/
theorem meet_of_rep {T : Traj V} (hT : 1 ≤ T.len) {α β c : ℕ} (ha : Occ T ra α)
    (hb : RepOcc T c β rb) (h1 : Wb.τ β ≤ Wa.τ α)
    (h2 : Wa.τ (α + T.len) ≤ Wb.τ (β + c * (2 * T.len))) :
    ∃ t, Meet ra rb Wa Wb t ∧ t ∈ Icc (Wa.τ α) (Wa.τ (α + T.len)) := by
  have hc : 1 ≤ c := by
    by_contra hc
    have : c = 0 := by omega
    subst this
    have := lt_of_le_of_lt h1 (Wa.τ_lt (show α < α + T.len by omega))
    simp at h2; linarith
  set s := Wa.τ α
  set e := Wa.τ (α + T.len)
  have hse : s ≤ e := Wa.τ_le (by omega)
  have hsub : Icc s e ⊆ Icc (Wb.τ β) (Wb.τ (β + c * (2 * T.len))) := Icc_subset_Icc h1 h2
  have hca : ContinuousOn (fun t => Wa.p t - α) (Icc s e) :=
    (Wa.continuousOn_window _ _).sub continuousOn_const
  have hcb : ContinuousOn (fun t => foldR T.len (Wb.p t - β)) (Icc s e) :=
    (continuous_foldR _).comp_continuousOn
      (((Wb.continuousOn_window _ _).mono hsub).sub continuousOn_const)
  have hLr : (0 : ℝ) < T.len := by exact_mod_cast hT
  obtain ⟨t, ht, heq⟩ := exists_eq_of_le_of_ge hse hca hcb
    (by simp only [s, Wa.p_τ, sub_self]; exact foldR_nonneg hLr.le _)
    (by simp only [e, Wa.p_τ]; push_cast; simp only [add_sub_cancel_left]
        exact foldR_le hLr _)
  have hpa := Wa.p_mem_window (show α ≤ α + T.len by omega) ht
  have hpb := Wb.p_mem_window (show β ≤ β + c * (2 * T.len) by omega) (hsub ht)
  refine ⟨t, ⟨le_trans (Wa.τ_nonneg α) ht.1, ⟨_, ht.2⟩, ⟨_, (hsub ht).2⟩, ?_⟩, ht⟩
  have hx : Wa.p t = α + (Wa.p t - α) := by ring
  have hy : Wb.p t = β + (Wb.p t - β) := by ring
  push_cast at hpa hpb
  rw [hx, posR_occ hT ha (by linarith [hpa.1]) (by linarith [hpa.2]), hy,
    posR_rep hT hb hc (by linarith [hpb.1]) (by push_cast; linarith [hpb.2]), heq]

/-- Pigeonhole for windows: if `b`'s indices `β + q D` (`q ≤ c`) span a time interval inside `a`'s
window `[j0, j0 + c]`, some interval `[τ_b(β + q D), τ_b(β + (q+1) D)]` lies inside a single edge
traversal `[τ_a j, τ_a (j+1)]` of `a`. -/
theorem exists_inside_edge (D : ℕ) : ∀ (c j0 β : ℕ), 1 ≤ c → Wa.τ j0 ≤ Wb.τ β →
    Wb.τ (β + c * D) ≤ Wa.τ (j0 + c) →
    ∃ q < c, ∃ j, Wa.τ j ≤ Wb.τ (β + q * D) ∧ Wb.τ (β + (q + 1) * D) ≤ Wa.τ (j + 1)
  | 0, _, _, h, _, _ => absurd h (by omega)
  | c + 1, j0, β, _, h1, h2 => by
    by_cases h : Wb.τ (β + D) ≤ Wa.τ (j0 + 1)
    · exact ⟨0, by omega, j0, by simpa using h1, by simpa using h⟩
    · rcases Nat.eq_zero_or_pos c with rfl | hc
      · exact absurd (by simpa using h2) h
      · obtain ⟨q, hq, j, h3, h4⟩ := exists_inside_edge D c (j0 + 1) (β + D) hc (not_le.1 h).le
          (by rw [show β + D + c * D = β + (c + 1) * D by ring,
                show j0 + 1 + c = j0 + (c + 1) by ring]; exact h2)
        refine ⟨q + 1, by omega, j, ?_, ?_⟩
        · rwa [show β + (q + 1) * D = β + D + q * D by ring]
        · rwa [show β + (q + 1 + 1) * D = β + D + (q + 1) * D by ring]

-- CSLib candidate
/-- **Counting.** If agent `b` repeats `c ≥ 1` times the trajectory `T T̄` with `T` integral (it
traverses every edge of `G`), while agent `a` (whose route is a route in `G`) performs at most
`c` edge traversals (its progress stays in the window `[j0, j0 + c]`), they meet. -/
theorem meet_of_count {G : SimpleGraph V} (hra : IsRoute G ra) {T : Traj V} (hcov : Covers G T)
    {c β : ℕ} (hb : RepOcc T c β rb) (hc : 1 ≤ c) {j0 : ℕ} (h1 : Wa.τ j0 ≤ Wb.τ β)
    (h2 : Wb.τ (β + c * (2 * T.len)) ≤ Wa.τ (j0 + c)) :
    ∃ t, Meet ra rb Wa Wb t ∧ t ≤ Wb.τ (β + c * (2 * T.len)) := by
  obtain ⟨q, hq, j, h3, h4⟩ := exists_inside_edge (2 * T.len) c j0 β hc h1 h2
  obtain ⟨i, hi, hi'⟩ := hcov _ _ (hra j)
  have hk : rb (β + q * (2 * T.len) + i) = T.f i ∧ rb (β + q * (2 * T.len) + i + 1) = T.f (i + 1) := by
    have hq' : q * (2 * T.len) + (i + 1) ≤ c * (2 * T.len) := by
      have : (q + 1) * (2 * T.len) ≤ c * (2 * T.len) := Nat.mul_le_mul_right _ hq
      nlinarith
    constructor
    · rw [add_assoc, hb _ (by omega), foldN_mul_add hi.le]
    · rw [add_assoc, add_assoc, hb _ hq', foldN_mul_add hi]
  obtain ⟨t, ht, hte⟩ := meet_of_edge (k := β + q * (2 * T.len) + i) (j := j) (ra := ra) (rb := rb)
    (le_trans h3 (Wb.τ_le (by omega)))
    (le_trans (Wb.τ_le (by nlinarith)) h4)
    (by rw [hk.1, hk.2]; rcases hi' with h | h
        · exact Or.inl ⟨h.1, h.2⟩
        · exact Or.inr ⟨h.1, h.2⟩)
  refine ⟨t, ht, le_trans hte (Wb.τ_le ?_)⟩
  have : (q + 1) * (2 * T.len) ≤ c * (2 * T.len) := Nat.mul_le_mul_right _ hq
  nlinarith

end Podc.AsyncRendezvousPoly
