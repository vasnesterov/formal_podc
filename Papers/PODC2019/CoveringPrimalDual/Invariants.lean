import Papers.PODC2019.CoveringPrimalDual.Algorithm

/-!
# Invariants of Algorithm MWHVC (Section 4.1, Claims 4.1, 4.2, 4.4, Corollary C.1)

We prove that the following state invariant `Inv` holds at the end of every iteration:
positivity of deals, Claim 4.1, feasibility of the duals (Claim 4.2), the upper bound
`∑_{E(v)} δ ≤ (1 - (1-κ) 2^{-(ℓ(v)+1)}) w(v)` for active vertices (Eq. (1)/(2) shifted by one
iteration), the lower bound of Eq. (1), Claim 4.4 (levels `< z`) and the `β`-tightness of the
vertices of `C`.
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual

open Finset Cslib.Hypergraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ### The `while` loop of step 3d -/

theorem exists_lvl {ℓ : ℕ} {s w : ℝ} (hw : 0 < w) (hs : s < w) :
    ∃ k : ℕ, s ≤ w * (1 - (1 / 2 : ℝ) ^ (ℓ + k + 1)) := by
  have hpos : 0 < (w - s) / w := div_pos (by linarith) hw
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have h1 : (1 / 2 : ℝ) ^ (ℓ + n + 1) ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [lt_div_iff₀ hw] at hn
  nlinarith

theorem le_lvlUp (ℓ : ℕ) (s w : ℝ) : ℓ ≤ lvlUp ℓ s w := by
  unfold lvlUp; split_ifs <;> omega

/-- The loop terminates in a level `ℓ'` with `s ≤ w (1 - 2^{-(ℓ'+1)})`. -/
theorem lvlUp_upper {ℓ : ℕ} {s w : ℝ} (hw : 0 < w) (hs : s < w) :
    s ≤ w * (1 - (1 / 2 : ℝ) ^ (lvlUp ℓ s w + 1)) := by
  have h := exists_lvl (ℓ := ℓ) hw hs
  unfold lvlUp
  split_ifs with hh
  · exact Nat.find_spec hh
  · exact absurd h hh

/-- If the loop increments the level to `ℓ' > ℓ`, then `s > w (1 - 2^{-ℓ'})`. -/
theorem lvlUp_lower {ℓ : ℕ} {s w : ℝ} (h : ℓ < lvlUp ℓ s w) :
    w * (1 - (1 / 2 : ℝ) ^ (lvlUp ℓ s w)) < s := by
  unfold lvlUp at h ⊢
  split_ifs at h ⊢ with hex
  · have hk : 0 < Nat.find hex := by omega
    have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at hmin
    have : ℓ + (Nat.find hex - 1) + 1 = ℓ + Nat.find hex := by omega
    rw [this] at hmin
    exact hmin
  · omega

/-- If already `s ≤ w (1 - 2^{-(m+1)})` for some `m ≥ ℓ`, the loop stops at a level `≤ m`. -/
theorem lvlUp_le {ℓ m : ℕ} {s w : ℝ} (hm : ℓ ≤ m) (h : s ≤ w * (1 - (1 / 2 : ℝ) ^ (m + 1))) :
    lvlUp ℓ s w ≤ m := by
  have hex : ∃ k : ℕ, s ≤ w * (1 - (1 / 2 : ℝ) ^ (ℓ + k + 1)) :=
    ⟨m - ℓ, by rwa [show ℓ + (m - ℓ) + 1 = m + 1 by omega]⟩
  unfold lvlUp
  split_ifs with hh
  · have := Nat.find_min' hh (m := m - ℓ) (by rwa [show ℓ + (m - ℓ) + 1 = m + 1 by omega])
    omega
  · exact absurd hex hh

/-! ### Basic facts on covers and active vertices -/

namespace Inst

variable (I : Inst V E)

theorem covered_mono {C C' : Finset V} (h : C ⊆ C') {e : E} (he : I.Covered C e) :
    I.Covered C' e := by
  obtain ⟨v, hv, hvC⟩ := he; exact ⟨v, hv, h hvC⟩

theorem uncov_anti {C C' : Finset V} (h : C ⊆ C') (v : V) : I.uncov C' v ⊆ I.uncov C v := by
  intro e he
  simp only [uncov, mem_filter] at he ⊢
  exact ⟨he.1, fun hc => he.2 (I.covered_mono h hc)⟩

theorem active_anti {C C' : Finset V} (h : C ⊆ C') {v : V} (hv : I.Active C' v) :
    I.Active C v :=
  ⟨fun hc => hv.1 (h hc), hv.2.mono (I.uncov_anti h v)⟩

theorem mem_uncov {C : Finset V} {v : V} {e : E} :
    e ∈ I.uncov C v ↔ v ∈ I.inc e ∧ ¬ I.Covered C e := by
  simp [uncov]

theorem active_of_mem {C : Finset V} {e : E} (he : ¬ I.Covered C e) {v : V} (hv : v ∈ I.inc e) :
    I.Active C v :=
  ⟨fun hc => he ⟨v, hv, hc⟩, ⟨e, I.mem_uncov.2 ⟨hv, he⟩⟩⟩

theorem uncov_eq_empty {C : Finset V} {v : V} (h : ¬ I.Active C v) : I.uncov C v = ∅ := by
  by_contra hne
  obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 hne
  exact h (I.active_of_mem (I.mem_uncov.1 he).2 (I.mem_uncov.1 he).1)

theorem deg_pos {v : V} {e : E} (hv : v ∈ I.inc e) : 0 < I.deg v :=
  card_pos.2 ⟨e, mem_edgesAt.2 hv⟩

end Inst

variable (I : Inst V E) (P : Params)

theorem C_subset_joinC (s : State V E) : s.C ⊆ joinC I P s := subset_union_left

theorem C_subset_step (s : State V E) : s.C ⊆ (step I P s).C := C_subset_joinC I P s

/-- A vertex that is active after step 3a was not `β`-tight. -/
theorem not_tight_of_active {s : State V E} {v : V} (h : I.Active (joinC I P s) v) :
    I.load s.δ v < (1 - P.β) * I.w v := by
  by_contra hc
  push Not at hc
  apply h.1
  by_cases hv : v ∈ s.C
  · exact C_subset_joinC I P s hv
  · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hv, hc⟩)

theorem le_lvl1 (s : State V E) (v : V) : s.level v ≤ lvl1 I P s v := by
  unfold lvl1; split_ifs
  · exact le_lvlUp _ _ _
  · exact le_rfl

theorem lvl1_of_not_active {s : State V E} {v : V} (h : ¬ I.Active (joinC I P s) v) :
    lvl1 I P s v = s.level v := by
  simp [lvl1, h]

theorem lvl1_of_active {s : State V E} {v : V} (h : I.Active (joinC I P s) v) :
    lvl1 I P s v = lvlUp (s.level v) (I.load s.δ v) (I.w v) := by
  simp [lvl1, h]

/-- The load after an iteration: `∑_{E(v)} δ' = ∑_{E(v)} δ + κ ∑_{E'(v)} deal`. -/
theorem load_step (s : State V E) (v : V) :
    I.load (step I P s).δ v =
      I.load s.δ v + P.κ * ∑ e ∈ I.uncov (joinC I P s) v, deal2 I P s e := by
  simp only [Inst.load, Cslib.Hypergraph.load, step, Inst.uncov, mul_sum, sum_filter]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

/-! ### The invariant -/

/-- The invariants of Section 4.1, at the end of an iteration. -/
structure Inv (s : State V E) : Prop where
  deal_pos : ∀ e, 0 < s.deal e
  δ_nonneg : ∀ e, 0 ≤ s.δ e
  /-- Claim 4.1. -/
  claim41 : ∀ v, v ∉ s.C →
    ∑ e ∈ I.uncov s.C v, s.deal e ≤ (1 / 2 : ℝ) ^ (s.level v + 1) * I.w v
  /-- Feasibility of the dual (Claim 4.2). -/
  feasible : ∀ v, I.load s.δ v ≤ I.w v
  /-- Upper bound of Eq. (1) (Eq. (2) for `κ = 1/2`), for the next iteration. -/
  activeLoad : ∀ v, I.Active s.C v →
    I.load s.δ v ≤ (1 - (1 - P.κ) * (1 / 2 : ℝ) ^ (s.level v + 1)) * I.w v
  /-- Lower bound of Eq. (1). -/
  lower : ∀ v, I.w v * (1 - (1 / 2 : ℝ) ^ s.level v) ≤ I.load s.δ v
  /-- Claim 4.4. -/
  level_lt : ∀ v, s.level v < P.z
  /-- The vertices of `C` are `β`-tight. -/
  tight : ∀ v ∈ s.C, (1 - P.β) * I.w v ≤ I.load s.δ v

variable {I P}

theorem Params.Valid.β_pos (hP : P.Valid I) : 0 < P.β := by
  have := hP.ε_pos; have : (0 : ℝ) < P.f := by exact_mod_cast hP.f_pos
  unfold Params.β; positivity

theorem Params.Valid.β_lt_one (hP : P.Valid I) : P.β < 1 := by
  have := hP.ε_pos; have : (0 : ℝ) < P.f := by exact_mod_cast hP.f_pos
  unfold Params.β; rw [div_lt_one (by positivity)]; linarith

/-- `2^{-z} ≤ β`. -/
theorem Params.Valid.half_pow_z_le (hP : P.Valid I) : (1 / 2 : ℝ) ^ P.z ≤ P.β := by
  have hβ := hP.β_pos
  have h1 : Real.logb 2 P.β⁻¹ ≤ P.z := Nat.le_ceil _
  have h2 : P.β⁻¹ ≤ 2 ^ P.z := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)] at h1
    simpa [Real.rpow_natCast] using h1
  rw [one_div_pow, div_le_iff₀ (by positivity)]
  rw [inv_le_iff_one_le_mul₀ hβ] at h2
  linarith [mul_comm P.β (2 ^ P.z : ℝ)]

theorem Params.Valid.z_pos (hP : P.Valid I) : 0 < P.z := by
  unfold Params.z
  rw [Nat.ceil_pos]
  apply Real.logb_pos (by norm_num)
  exact (one_lt_inv₀ hP.β_pos).2 hP.β_lt_one

theorem deal0_pos (hP : P.Valid I) (e : E) : 0 < deal0 I P e := by
  unfold deal0
  apply mul_pos hP.c₀_pos
  rw [Finset.lt_inf'_iff]
  intro v hv
  exact div_pos (I.w_pos v) (by exact_mod_cast I.deg_pos hv)

theorem deal0_le (hP : P.Valid I) {e : E} {v : V} (hv : v ∈ I.inc e) :
    deal0 I P e ≤ P.c₀ * (I.w v / I.deg v) :=
  mul_le_mul_of_nonneg_left (inf'_le _ hv) hP.c₀_pos.le

theorem sum_deal0_le (hP : P.Valid I) (v : V) :
    ∑ e ∈ I.E_ v, deal0 I P e ≤ P.c₀ * I.w v := by
  rcases Nat.eq_zero_or_pos (I.deg v) with h0 | hpos
  · rw [card_eq_zero.1 h0, sum_empty]; exact (mul_pos hP.c₀_pos (I.w_pos v)).le
  calc ∑ e ∈ I.E_ v, deal0 I P e ≤ ∑ e ∈ I.E_ v, P.c₀ * (I.w v / I.deg v) :=
        sum_le_sum fun e he => deal0_le hP (mem_edgesAt.1 he)
    _ = P.c₀ * I.w v := by
        rw [sum_const, nsmul_eq_mul]; field_simp

theorem inv_init (hP : P.Valid I) : Inv I P (init I P) := by
  have hc := hP.c₀_le
  have hκ := hP.κ_le
  have hκ0 := hP.κ_pos
  have hload : ∀ v, I.load (init I P).δ v ≤ (1 / 2) * I.w v := fun v =>
    (sum_deal0_le hP v).trans (mul_le_mul_of_nonneg_right hc (I.w_pos v).le)
  refine ⟨deal0_pos hP, fun e => (deal0_pos hP e).le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v _
    have hu : I.uncov ∅ v = I.E_ v := by
      ext e; simp [Inst.uncov, Inst.Covered]
    have := hload v
    simp only [init, zero_add, pow_one, hu] at this ⊢
    exact this
  · intro v; have := hload v; have := I.w_pos v; linarith
  · intro v _
    have h1 := hload v; have := I.w_pos v
    simp only [init, zero_add, pow_one] at h1 ⊢
    nlinarith
  · intro v
    simp only [init, pow_zero, sub_self, mul_zero]
    exact sum_nonneg fun e _ => (deal0_pos hP e).le
  · intro v; exact hP.z_pos
  · intro v hv; simp [init] at hv

/-- Claim 4.1 after an iteration. -/
theorem claim41_step (hP : P.Valid I) {s : State V E} (hs : Inv I P s) {v : V}
    (hv : v ∉ (step I P s).C) :
    ∑ e ∈ I.uncov (joinC I P s) v, deal2 I P s e ≤
      (1 / 2 : ℝ) ^ (lvl1 I P s v + 1) * I.w v := by
  have hα := hP.one_lt_α
  have hd1 : ∀ e, 0 ≤ deal1 I P s e := fun e => by
    unfold deal1; split_ifs
    · exact (hs.deal_pos e).le
    · exact mul_nonneg (hs.deal_pos e).le (by positivity)
  by_cases hact : I.Active (joinC I P s) v
  swap
  · rw [I.uncov_eq_empty hact, sum_empty]; exact mul_nonneg (by positivity) (I.w_pos v).le
  by_cases hr : Raise I P s v
  · calc ∑ e ∈ I.uncov (joinC I P s) v, deal2 I P s e
          ≤ ∑ e ∈ I.uncov (joinC I P s) v, P.α * deal1 I P s e := by
            refine sum_le_sum fun e _ => ?_
            unfold deal2; split_ifs
            · exact le_rfl
            · exact le_mul_of_one_le_left (hd1 e) hα.le
      _ = P.α * ∑ e ∈ I.uncov (joinC I P s) v, deal1 I P s e := by rw [mul_sum]
      _ ≤ P.α * (P.α⁻¹ * (1 / 2 : ℝ) ^ (lvl1 I P s v + 1) * I.w v) :=
            mul_le_mul_of_nonneg_left hr (by linarith)
      _ = (1 / 2 : ℝ) ^ (lvl1 I P s v + 1) * I.w v := by
            field_simp
  · have hle := le_lvl1 I P s v
    have hvC : v ∉ s.C := fun h => hv (C_subset_step I P s h)
    have key : ∀ e ∈ I.uncov (joinC I P s) v,
        deal2 I P s e ≤ (1 / 2 : ℝ) ^ (lvl1 I P s v - s.level v) * s.deal e := by
      intro e he
      obtain ⟨hve, hnc⟩ := I.mem_uncov.1 he
      have hnr : ¬ RaiseEdge I P s e := fun h => hr (h.2 v hve)
      simp only [deal2, hnr, ite_false, deal1, hnc, ite_false]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_right _ (hs.deal_pos e).le
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      exact single_le_sum (f := fun u => lvl1 I P s u - s.level u) (fun _ _ => Nat.zero_le _) hve
    calc ∑ e ∈ I.uncov (joinC I P s) v, deal2 I P s e
          ≤ ∑ e ∈ I.uncov (joinC I P s) v, (1 / 2 : ℝ) ^ (lvl1 I P s v - s.level v) * s.deal e :=
            sum_le_sum key
      _ ≤ ∑ e ∈ I.uncov s.C v, (1 / 2 : ℝ) ^ (lvl1 I P s v - s.level v) * s.deal e :=
            sum_le_sum_of_subset_of_nonneg (I.uncov_anti (C_subset_joinC I P s) v)
              fun e _ _ => mul_nonneg (by positivity) (hs.deal_pos e).le
      _ = (1 / 2 : ℝ) ^ (lvl1 I P s v - s.level v) * ∑ e ∈ I.uncov s.C v, s.deal e := by
            rw [mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ (lvl1 I P s v - s.level v) * ((1 / 2 : ℝ) ^ (s.level v + 1) * I.w v) :=
            mul_le_mul_of_nonneg_left (hs.claim41 v hvC) (by positivity)
      _ = (1 / 2 : ℝ) ^ (lvl1 I P s v + 1) * I.w v := by
            rw [← mul_assoc, ← pow_add]; congr 2; omega

theorem deal2_nonneg {s : State V E} (hP : P.Valid I) (hs : Inv I P s) (e : E) :
    0 ≤ deal2 I P s e := by
  have hα := hP.one_lt_α
  have h1 : 0 < deal1 I P s e := by
    unfold deal1; split_ifs
    · exact hs.deal_pos e
    · exact mul_pos (hs.deal_pos e) (by positivity)
  unfold deal2; split_ifs
  · exact (mul_pos (by linarith) h1).le
  · exact h1.le

theorem load_le_load_step (hP : P.Valid I) {s : State V E} (hs : Inv I P s) (v : V) :
    I.load s.δ v ≤ I.load (step I P s).δ v := by
  rw [load_step]
  have := sum_nonneg fun e (_ : e ∈ I.uncov (joinC I P s) v) => deal2_nonneg hP hs e
  have := hP.κ_pos
  nlinarith

/-- Upper bound of Eq. (1): the loop of step 3d leaves `∑_{E(v)} δ_{i-1} ≤ (1 - 2^{-(ℓ_i+1)}) w`. -/
theorem load_le_lvl1 (hP : P.Valid I) {s : State V E} {v : V} (hact : I.Active (joinC I P s) v) :
    I.load s.δ v ≤ I.w v * (1 - (1 / 2 : ℝ) ^ (lvl1 I P s v + 1)) := by
  rw [lvl1_of_active I P hact]
  apply lvlUp_upper (I.w_pos v)
  have := not_tight_of_active I P hact
  have := hP.β_pos
  have := I.w_pos v
  nlinarith

theorem inv_step (hP : P.Valid I) {s : State V E} (hs : Inv I P s) : Inv I P (step I P s) := by
  have hκ := hP.κ_le
  have hκ0 := hP.κ_pos
  have hmono := load_le_load_step hP hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    have hα := hP.one_lt_α
    have h1 : 0 < deal1 I P s e := by
      unfold deal1; split_ifs
      · exact hs.deal_pos e
      · exact mul_pos (hs.deal_pos e) (by positivity)
    show 0 < deal2 I P s e
    unfold deal2; split_ifs
    · exact mul_pos (by linarith) h1
    · exact h1
  · intro e
    show 0 ≤ (if I.Covered (joinC I P s) e then s.δ e else s.δ e + P.κ * deal2 I P s e)
    split_ifs
    · exact hs.δ_nonneg e
    · exact add_nonneg (hs.δ_nonneg e) (mul_nonneg hκ0.le (deal2_nonneg hP hs e))
  · intro v hv
    exact claim41_step hP hs hv
  · intro v
    rw [load_step]
    by_cases hact : I.Active (joinC I P s) v
    · have h1 := load_le_lvl1 hP hact
      have hv : v ∉ (step I P s).C := hact.1
      have h2 := claim41_step hP hs hv
      have hp : (0 : ℝ) ≤ (1 / 2) ^ (lvl1 I P s v + 1) * I.w v :=
        mul_nonneg (by positivity) (I.w_pos v).le
      nlinarith
    · rw [I.uncov_eq_empty hact, sum_empty, mul_zero, add_zero]; exact hs.feasible v
  · intro v hact
    rw [load_step]
    have h1 := load_le_lvl1 hP hact
    have h2 := claim41_step hP hs hact.1
    show _ ≤ (1 - (1 - P.κ) * (1 / 2 : ℝ) ^ (lvl1 I P s v + 1)) * I.w v
    nlinarith
  · intro v
    show I.w v * (1 - (1 / 2 : ℝ) ^ lvl1 I P s v) ≤ _
    by_cases hlt : s.level v < lvl1 I P s v
    · have hact : I.Active (joinC I P s) v := by
        by_contra h; rw [lvl1_of_not_active I P h] at hlt; omega
      rw [lvl1_of_active I P hact] at hlt ⊢
      exact (lvlUp_lower hlt).le.trans (hmono v)
    · have : lvl1 I P s v = s.level v := le_antisymm (by omega) (le_lvl1 I P s v)
      rw [this]; exact (hs.lower v).trans (hmono v)
  · intro v
    show lvl1 I P s v < P.z
    by_cases hact : I.Active (joinC I P s) v
    · rw [lvl1_of_active I P hact]
      have hz := hP.z_pos
      have hle : lvlUp (s.level v) (I.load s.δ v) (I.w v) ≤ P.z - 1 := by
        apply lvlUp_le (by have := hs.level_lt v; omega)
        rw [show P.z - 1 + 1 = P.z by omega]
        have := not_tight_of_active I P hact
        have := hP.half_pow_z_le
        have := I.w_pos v
        nlinarith
      omega
    · rw [lvl1_of_not_active I P hact]; exact hs.level_lt v
  · intro v hv
    show _ ≤ I.load (step I P s).δ v
    refine le_trans ?_ (hmono v)
    by_cases hvs : v ∈ s.C
    · exact hs.tight v hvs
    · rcases mem_union.1 hv with h | h
      · exact absurd h hvs
      · exact (mem_filter.1 h).2.2

theorem inv_run (hP : P.Valid I) : ∀ i, Inv I P (run I P i)
  | 0 => inv_init hP
  | i + 1 => inv_step hP (inv_run hP i)

end Podc.CoveringPrimalDual
