import Papers.PODC2021.ThinUnison.Observations

/-!
# AlgAU: towards an out-protected graph (Section 2.3.3, Lemmas 2.12–2.14, Corollary 2.15)
-/

namespace ThinUnison

open Cslib.StoneAge

section Pure

variable {k : ℕ}

theorem inw_outw {a : ℤ} (_ha : a ≠ 0) : inw (outw a) = a := by lvl_omega

theorem natAbs_outw {a : ℤ} (_ha : a ≠ 0) : (outw a).natAbs = a.natAbs + 1 := by lvl_omega

theorem outEq_of_outEq_outw {a x : ℤ} (ha : a ≠ 0) (h : OutEq (outw a) x) : OutEq a x := by
  lvl_omega

theorem outEq_trans {a b c : ℤ} (hab : OutEq a b) (hbc : OutEq b c) : OutEq a c := by lvl_omega

theorem eq_outw_of_outward {a x : ℤ} (h : Outward a x) (h' : ¬ FarOut a x) : x = outw a := by
  lvl_omega

theorem not_outward_of_natAbs_eq {a x : ℤ} (hx : IsLevel k x) (ha : a.natAbs = k) :
    ¬ Outward a x := by lvl_omega

theorem not_lAdj_of_farOut {a x : ℤ} (ha : IsLevel k a) (hx : IsLevel k x) (h : FarOut a x) :
    ¬ LAdj k a x := by
  intro h'; rcases h' with rfl | rfl | rfl <;> lvl_omega

/-- Core of step (A) in Lemma 2.12: while `v` is faulty at level `a` and out-protected, a neighbour
cannot move to level `ψ⁺¹(a)`. -/
theorem stay_outw_pure {a b b' : ℤ} {g : Bool} (_ha : IsLevel k a) (hb : IsLevel k b)
    (h2 : 2 ≤ a.natAbs) (hfar : ¬ FarOut a b) (mb : MoveRel k b b' g a true)
    (hb' : b' = outw a) : b = outw a := by
  unfold MoveRel at mb
  simp only [Bool.true_eq_false, false_and, and_false, false_or] at mb
  rcases mb with rfl | ⟨-, h1, rfl⟩
  · exact hb'
  · lvl_omega

theorem not_farOut_of_lAdj {a x : ℤ} (ha : IsLevel k a) (hx : IsLevel k x) (h : LAdj k x a) :
    ¬ FarOut a x := by
  rcases h with rfl | rfl | rfl <;> lvl_omega

theorem outEq_outw_of_farOut {a x : ℤ} (h : FarOut a x) : OutEq (outw a) x := by lvl_omega

theorem natAbs_of_farOut {a x : ℤ} (h : FarOut a x) : a.natAbs + 2 ≤ x.natAbs := by lvl_omega

theorem farOut_inw {a x : ℤ} (h : FarOut a x) : (inw x).natAbs + 1 = x.natAbs := by lvl_omega

theorem outEq_or_of_isLevel {x : ℤ} (hx : IsLevel k x) : OutEq 1 x ∨ OutEq (-1) x := by lvl_omega

theorem outEq_of_natAbs_eq {a x : ℤ} (hx : IsLevel k x) (ha : a.natAbs = k) (h : OutEq a x) :
    x = a := by lvl_omega

theorem natAbs_le_of_isLevel {x : ℤ} (hx : IsLevel k x) : x.natAbs ≤ k := by lvl_omega

theorem outEq_outw_of_outward {a x : ℤ} (h : Outward a x) : OutEq (outw a) x := by lvl_omega

theorem not_farOut_of_natAbs_eq {a x : ℤ} (hx : IsLevel k x) (ha : a.natAbs = k) :
    ¬ FarOut a x := by lvl_omega

end Pure

/-- `∑_{i<n} 2(n - i) = n(n+1)`. -/
theorem sum_range_two_mul_sub (n : ℕ) : ∑ i ∈ Finset.range n, 2 * (n - i) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have : ∑ i ∈ Finset.range n, 2 * (n + 1 - (i + 1)) = ∑ i ∈ Finset.range n, 2 * (n - i) :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_sub_add_right]
    rw [this, ih, Nat.sub_zero]; ring

/-- The number of rounds in Lemma 2.14 for a neighbour `n` levels away:
`∑_{i<n} (2(k - (a + 2 + i)) + 2)` where `a = |ℓ|`. -/
def cost14 (k a n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (2 * (k - (a + 2 + i)) + 2)

theorem cost14_succ (k a n : ℕ) :
    cost14 k a (n + 1) = cost14 k a n + (2 * (k - (a + 2 + n)) + 2) := Finset.sum_range_succ _ _

theorem cost14_mono (k a : ℕ) {m n : ℕ} (h : m ≤ n) : cost14 k a m ≤ cost14 k a n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun _ _ _ => Nat.zero_le _

theorem cost14_eq {k a : ℕ} (h : a + 1 ≤ k) : cost14 k a (k - a - 1) = (k - a) * (k - a - 1) := by
  unfold cost14
  have : ∑ i ∈ Finset.range (k - a - 1), (2 * (k - (a + 2 + i)) + 2) =
      ∑ i ∈ Finset.range (k - a - 1), 2 * (k - a - 1 - i) :=
    Finset.sum_congr rfl fun i hi => by simp at hi; omega
  rw [this, sum_range_two_mul_sub]
  rw [show k - a - 1 + 1 = k - a by omega, Nat.mul_comm]

/-- The total number of rounds of Corollary 2.15: `∑_{j ∈ [i, k)} (k - j)(k - j - 1)`. -/
def outRounds (k i : ℕ) : ℕ := ∑ j ∈ Finset.Ico i k, (k - j) * (k - j - 1)

theorem outRounds_succ {k i : ℕ} (h : i < k) :
    outRounds k i = (k - i) * (k - i - 1) + outRounds k (i + 1) :=
  Finset.sum_eq_sum_Ico_succ_bot h _

namespace AURun

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {A : ℕ → Set V} {C : ℕ → V → Turn k}
variable (hC : AURun G A C)
include hC

/-- A faulty node that keeps its level keeps its turn. -/
theorem faulty_of_lvl_eq {s : ℕ} {u : V} (hf : (C s u).faulty = true)
    (hl : (C (s + 1) u).lvl = (C s u).lvl) : (C (s + 1) u).faulty = true := by
  rcases hC.faulty_cases hf with h | ⟨-, -, h, -⟩
  · rw [h]; exact hf
  · have := (C s u).isLevel; have := (C s u).faulty_two hf
    exfalso; rw [h] at hl; revert hl; lvl_omega

omit hC in
/-- A node that is not protected cannot perform an AA transition. -/
theorem not_aan_of_not_prot {s : ℕ} {u : V} (h : ¬ Prot G C s u) : ¬ AAN G C s u := by
  intro h'; apply h; intro w hw
  rcases (h' w hw).2 with h1 | h1
  · exact Or.inl h1.symm
  · exact Or.inr (Or.inr h1)

/-- A non-protected node only changes its level by an FA transition (inwards). -/
theorem lvl_succ_of_not_prot {s : ℕ} {u : V} (h : ¬ Prot G C s u)
    (hl : (C (s + 1) u).lvl ≠ (C s u).lvl) :
    (C s u).faulty = true ∧ (C (s + 1) u).lvl = inw (C s u).lvl ∧
      (C (s + 1) u).faulty = false := by
  rcases hC.step_cases s u with h1 | ⟨-, -, h1, -⟩ | ⟨-, -, -, h1, -⟩ | ⟨-, h1, -, h2, h3⟩
  · exact absurd (by rw [h1]) hl
  · exact absurd h1 (not_aan_of_not_prot h)
  · exact absurd h1 hl
  · exact ⟨h1, h2, h3⟩

variable [Finite V] (hA : Fair A)
include hA

/-- Lemma 2.12 of [EK21], core form: if the graph is `ℓ`-out-protected at time `t`
(`2 ≤ |ℓ| = k - m`), a node cannot stay in the faulty turn `ℓ̂` during `[t, ϱ^{2m+1}(t)]`. -/
theorem fa_core (m : ℕ) : ∀ (t : ℕ) (v : V) (ℓ : ℤ), ℓ.natAbs + m = k → 2 ≤ ℓ.natAbs →
    LOutProt G C t ℓ →
    ¬ ∀ s, t ≤ s → s ≤ (rho A)^[2 * m + 1] t → (C s v).lvl = ℓ ∧ (C s v).faulty = true := by
  induction m with
  | zero =>
    intro t v ℓ hm h2 _ hstay
    obtain ⟨s, hs1, hs2, hs3⟩ := exists_act hA v t
    have hX : (rho A)^[2 * 0 + 1] t = rho A t := rfl
    obtain ⟨hl, hf⟩ := hstay s hs1 (by rw [hX]; omega)
    have hfan : FAN G C s v := by
      intro u _
      rw [hl]
      exact not_outward_of_natAbs_eq (C s u).isLevel (by omega)
    have h1 := (hC.succ_fa hs3 hf hfan).2
    have h2 := (hstay (s + 1) (by omega) (by rw [hX]; omega)).2
    rw [h1] at h2; exact Bool.false_ne_true h2
  | succ m ih =>
    intro t v ℓ hm h2 hop hstay
    have hℓ0 : ℓ ≠ 0 := by omega
    set ℓ' := outw ℓ with hℓ'
    have hℓ'abs : ℓ'.natAbs = ℓ.natAbs + 1 := natAbs_outw hℓ0
    have hinw : inw ℓ' = ℓ := inw_outw hℓ0
    set τ1 := rho A t with hτ1
    set τ2 := (rho A)^[2 * m + 1] τ1 with hτ2
    set X := (rho A)^[2 * (m + 1) + 1] t with hX
    have hXτ2 : X = rho A τ2 := by
      rw [hX, hτ2, hτ1, show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring,
        Function.iterate_succ_apply', Function.iterate_succ_apply]
    have htτ1 : t ≤ τ1 := le_rho hA t
    have hτ1τ2 : τ1 ≤ τ2 := le_rho_iter hA _ _
    have hτ2X : τ2 ≤ X := hXτ2 ▸ le_rho hA τ2
    -- `v` is out-protected from `t` on
    have hopv : ∀ s, t ≤ s → OutProt G C s v := fun s hs =>
      hC.outProt_le (hop v (Or.inl (hstay t le_rfl (by omega)).1)) hs
    have hLop : ∀ s, t ≤ s → LOutProt G C s ℓ' := fun s hs w hw =>
      hC.lOutProt_le hop hs w (outEq_of_outEq_outw hℓ0 hw)
    -- (A) no neighbour moves to level `ℓ'`
    have hA' : ∀ s, t ≤ s → s < X → ∀ u, G.Adj v u → (C (s + 1) u).lvl = ℓ' →
        (C s u).lvl = ℓ' := by
      intro s hs hsX u hu hl
      obtain ⟨hvl, hvf⟩ := hstay s hs (by omega)
      have mb := hC.moveRel (t := s) hu.symm
      rw [hvl, hvf] at mb
      have hfar := hopv s hs u hu
      rw [hvl] at hfar
      exact stay_outw_pure (k := k) (hvl ▸ (C s v).isLevel) (C s u).isLevel h2 hfar mb hl
    -- (B) nor does an able neighbour at level `ℓ'` come from a faulty turn
    have hB : ∀ s, t ≤ s → s < X → ∀ u, G.Adj v u → (C (s + 1) u).lvl = ℓ' →
        (C (s + 1) u).faulty = false → (C s u).faulty = false := by
      intro s hs hsX u hu hl hf
      have hl' := hA' s hs hsX u hu hl
      by_contra hfs
      simp only [Bool.not_eq_false] at hfs
      have := hC.faulty_of_lvl_eq hfs (by rw [hl, hl'])
      rw [hf] at this; exact Bool.false_ne_true this
    -- (C) an able neighbour at level `ℓ'` becomes faulty when activated
    have hCc : ∀ s, t ≤ s → s < X → ∀ u, G.Adj v u → (C s u).lvl = ℓ' →
        (C s u).faulty = false → u ∈ A s → (C (s + 1) u).faulty = true := by
      intro s hs hsX u hu hl hf hact
      obtain ⟨hvl, hvf⟩ := hstay s hs (by omega)
      refine (hC.succ_af hact hf ⟨?_, Or.inr ⟨v, hu.symm, hvf, ?_⟩⟩).2
      · rw [hl]; omega
      · rw [hvl, hl, hinw]
    -- (D) at time `τ1`, all neighbours at level `ℓ'` are faulty
    have hD : ∀ u, G.Adj v u → (C τ1 u).lvl = ℓ' → (C τ1 u).faulty = true := by
      intro u hu hl
      by_contra hf
      simp only [Bool.not_eq_true] at hf
      have hP := Nat.Icc_induction_down (P := fun s => (C s u).lvl = ℓ' ∧ (C s u).faulty = false)
        (a := t) ⟨hl, hf⟩ (fun s hs hsb hP => ⟨hA' s hs (by omega) u hu hP.1,
          hB s hs (by omega) u hu hP.1 hP.2⟩)
      obtain ⟨s, hs1, hs2, hs3⟩ := exists_act hA u t
      have h1 := hCc s hs1 (by omega) u hu (hP s hs1 (by omega)).1 (hP s hs1 (by omega)).2 hs3
      have h2 := (hP (s + 1) (by omega) (by omega)).2
      rw [h1] at h2; exact Bool.false_ne_true h2.symm
    -- (E) at time `τ2`, no neighbour is at level `ℓ'`
    have hE : ∀ u, G.Adj v u → (C τ2 u).lvl ≠ ℓ' := by
      intro u hu hl
      have hlv := Nat.Icc_induction_down (P := fun s => (C s u).lvl = ℓ') (a := τ1) hl
        (fun s hs hsb hP => hA' s (by omega) (by omega) u hu hP)
      have hfτ1 := hD u hu (hlv τ1 le_rfl hτ1τ2)
      apply ih τ1 u ℓ' (by omega) (by omega) (hLop τ1 htτ1)
      intro s hs1 hs2
      refine ⟨hlv s hs1 hs2, ?_⟩
      by_contra hf
      simp only [Bool.not_eq_true] at hf
      have hP := Nat.Icc_induction_down (P := fun r => (C r u).lvl = ℓ' ∧ (C r u).faulty = false)
        (a := τ1) (b := s) ⟨hlv s hs1 hs2, hf⟩ (fun r hr hrb hP => ⟨hA' r (by omega) (by omega)
          u hu hP.1, hB r (by omega) (by omega) u hu hP.1 hP.2⟩)
      have := (hP τ1 le_rfl hs1).2
      rw [hfτ1] at this; exact Bool.false_ne_true this.symm
    -- (F) from `τ2` on, no neighbour is at level `ℓ'`
    have hF : ∀ u, G.Adj v u → ∀ s, τ2 ≤ s → s ≤ X → (C s u).lvl ≠ ℓ' := fun u hu =>
      Nat.Icc_induction_up (P := fun s => (C s u).lvl ≠ ℓ') (hE u hu)
        (fun s hs hsX hP h' => hP (hA' s (by omega) hsX u hu h'))
    -- finally `v` performs an FA transition in `[τ2, X)`
    obtain ⟨s, hs1, hs2, hs3⟩ := exists_act hA v τ2
    rw [← hXτ2] at hs2
    obtain ⟨hvl, hvf⟩ := hstay s (by omega) (by omega)
    have hfan : FAN G C s v := by
      intro u hu hout
      rw [hvl] at hout
      have hfar := hopv s (by omega) u hu
      rw [hvl] at hfar
      exact hF u hu s hs1 (by omega) (eq_outw_of_outward hout hfar)
    have h1 := (hC.succ_fa hs3 hvf hfan).2
    have h2 := (hstay (s + 1) (by omega) (by omega)).2
    rw [h1] at h2; exact Bool.false_ne_true h2

/-- Lemma 2.12 of [EK21]: if the graph is `ℓ`-out-protected at time `t`, `2 ≤ |ℓ| ≤ k`, and `v` is
in the faulty turn `ℓ̂` at time `t`, then `v` performs an FA transition (to `ψ⁻¹(ℓ)‾`) at some step
`t ≤ s < ϱ^{2(k-|ℓ|)+1}(t)`. -/
theorem lemma_2_12 {t : ℕ} {v : V} {ℓ : ℤ} (h2 : 2 ≤ ℓ.natAbs) (hop : LOutProt G C t ℓ)
    (hl : (C t v).lvl = ℓ) (hf : (C t v).faulty = true) :
    ∃ s, t ≤ s ∧ s < (rho A)^[2 * (k - ℓ.natAbs) + 1] t ∧ (C s v).lvl = ℓ ∧
      (C s v).faulty = true ∧ (C (s + 1) v).lvl = inw ℓ ∧ (C (s + 1) v).faulty = false := by
  classical
  have hk : ℓ.natAbs ≤ k := hl ▸ natAbs_le_of_isLevel (C t v).isLevel
  set X := (rho A)^[2 * (k - ℓ.natAbs) + 1] t
  have hcore := hC.fa_core hA (k - ℓ.natAbs) t v ℓ (by omega) h2 hop
  push Not at hcore
  have hex : ∃ s, t ≤ s ∧ s ≤ X ∧ ¬ ((C s v).lvl = ℓ ∧ (C s v).faulty = true) := by
    obtain ⟨s, h1, h2, h3⟩ := hcore
    exact ⟨s, h1, h2, fun h => h3 h.1 h.2⟩
  obtain ⟨s0, ⟨hs0a, hs0b, hs0c⟩, hmin⟩ : ∃ s0, (t ≤ s0 ∧ s0 ≤ X ∧
      ¬ ((C s0 v).lvl = ℓ ∧ (C s0 v).faulty = true)) ∧ ∀ s < s0, ¬ (t ≤ s ∧ s ≤ X ∧
      ¬ ((C s v).lvl = ℓ ∧ (C s v).faulty = true)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
  have hs0t : s0 ≠ t := by
    intro h; rw [h] at hs0c; exact hs0c ⟨hl, hf⟩
  obtain ⟨s, rfl⟩ : ∃ s, s0 = s + 1 := ⟨s0 - 1, by omega⟩
  have hprev : (C s v).lvl = ℓ ∧ (C s v).faulty = true := by
    by_contra h
    exact hmin s (by omega) ⟨by omega, by omega, h⟩
  refine ⟨s, by omega, by omega, hprev.1, hprev.2, ?_⟩
  rcases hC.faulty_cases hprev.2 with h | ⟨-, -, h1, h2⟩
  · exact absurd (h ▸ hprev) hs0c
  · exact ⟨hprev.1 ▸ h1, h2⟩

/-- Lemma 2.13 of [EK21] (node form): if `u` is not protected at time `t`, `2 ≤ |λ_u|`, and the
graph is `λ_u`-out-protected, then by time `ϱ^{2(k-|λ_u|)+2}(t)` the node `u` changes its level or
becomes protected. (The paper's edge form is `lemma_2_13_edge`.) -/
theorem lemma_2_13 {t : ℕ} {u : V} (h2 : 2 ≤ (C t u).lvl.natAbs)
    (hop : LOutProt G C t (C t u).lvl) (hu : ¬ Prot G C t u) :
    ∃ s, t < s ∧ s ≤ (rho A)^[2 * (k - (C t u).lvl.natAbs) + 2] t ∧
      ((C s u).lvl ≠ (C t u).lvl ∨ Prot G C s u) := by
  set ℓ := (C t u).lvl with hℓ
  by_contra H
  push Not at H
  obtain ⟨s0, hs0a, hs0b, hs0c, hs0d⟩ := exists_first_act hA u t
  have hCs0 : C s0 u = C t u := hC.eq_of_not_mem hs0a hs0d
  -- a time `t1 ≤ ϱ(t)` at which `u` is in turn `ℓ̂`
  obtain ⟨t1, ht1a, ht1b, ht1l, ht1f⟩ : ∃ t1, t ≤ t1 ∧ t1 ≤ rho A t ∧ (C t1 u).lvl = ℓ ∧
      (C t1 u).faulty = true := by
    by_cases hf : (C t u).faulty = true
    · exact ⟨t, le_rfl, le_rho hA t, rfl, hf⟩
    · simp only [Bool.not_eq_true] at hf
      have hnp : ¬ Prot G C s0 u := by
        rcases Nat.eq_or_lt_of_le hs0a with h | h
        · rw [← h]; exact hu
        · exact (H s0 h (hs0b.le.trans (rho_iter_le_iter hA (m := 1) (by omega) t))).2
      have h' := hC.succ_af hs0c (hCs0 ▸ hf) ⟨by rw [hCs0]; omega, Or.inl hnp⟩
      exact ⟨s0 + 1, by omega, hs0b, by rw [h'.1, hCs0], h'.2⟩
  obtain ⟨s, hs1, hs2, -, -, hs5, -⟩ := hC.lemma_2_12 hA h2 (hC.lOutProt_le hop ht1a) ht1l ht1f
  have hle : (rho A)^[2 * (k - ℓ.natAbs) + 1] t1 ≤ (rho A)^[2 * (k - ℓ.natAbs) + 2] t := by
    have : (rho A)^[2 * (k - ℓ.natAbs) + 2] t = (rho A)^[2 * (k - ℓ.natAbs) + 1] (rho A t) :=
      Function.iterate_succ_apply _ _ _
    rw [this]
    exact rho_iter_mono hA _ ht1b
  have := (H (s + 1) (by omega) (by omega)).1
  rw [hs5] at this
  have := (C t u).isLevel
  revert this; rw [← hℓ]; intro this
  have h3 : inw ℓ ≠ ℓ := by lvl_omega
  exact h3 (by assumption)

/-- Lemma 2.13 of [EK21], the paper's edge form (for `2 ≤ |ℓ|`, see `differencies.md`): if the edge
`(u, v)` is not protected at time `t`, `λ_u < λ_v`, and the graph is `ℓ`-out-protected for
`ℓ ∈ {λ_u, λ_v}` with `2 ≤ |ℓ|`, then there is a time `t < t* ≤ ϱ^{2(k-|ℓ|)+2}(t)` with
`λ_u ≤ λ_u*`, `λ_v* ≤ λ_v`, at least one inequality strict. -/
theorem lemma_2_13_edge {t : ℕ} {u v : V} (huv : G.Adj u v)
    (hnp : ¬ LAdj k (C t u).lvl (C t v).lvl) (hlt : (C t u).lvl < (C t v).lvl) {ℓ : ℤ}
    (hℓ : ℓ = (C t u).lvl ∨ ℓ = (C t v).lvl) (h2 : 2 ≤ ℓ.natAbs) (hop : LOutProt G C t ℓ) :
    ∃ t', t < t' ∧ t' ≤ (rho A)^[2 * (k - ℓ.natAbs) + 2] t ∧
      (C t u).lvl ≤ (C t' u).lvl ∧ (C t' v).lvl ≤ (C t v).lvl ∧
      ((C t u).lvl < (C t' u).lvl ∨ (C t' v).lvl < (C t v).lvl) := by
  -- the endpoint `w` at level `ℓ` changes level or becomes protected
  obtain ⟨s, hs1, hs2, hs3⟩ : ∃ s, t < s ∧ s ≤ (rho A)^[2 * (k - ℓ.natAbs) + 2] t ∧
      ((C s u).lvl ≠ (C t u).lvl ∨ (C s v).lvl ≠ (C t v).lvl) := by
    rcases hℓ with rfl | rfl
    · have hu : ¬ Prot G C t u := fun h => hnp (h v huv)
      obtain ⟨s, h1, h2', h3⟩ := hC.lemma_2_13 hA h2 hop hu
      refine ⟨s, h1, h2', ?_⟩
      by_contra hc; push Not at hc
      rcases h3 with h3 | h3
      · exact h3 hc.1
      · exact hnp (by rw [← hc.1, ← hc.2]; exact h3 v huv)
    · have hv : ¬ Prot G C t v := fun h => hnp (by
        have := h u huv.symm; unfold LAdj at this ⊢; tauto)
      obtain ⟨s, h1, h2', h3⟩ := hC.lemma_2_13 hA h2 hop hv
      refine ⟨s, h1, h2', ?_⟩
      by_contra hc; push Not at hc
      rcases h3 with h3 | h3
      · exact h3 hc.2
      · exact hnp (by
          have := h3 u huv.symm; rw [hc.1, hc.2] at this; unfold LAdj at this ⊢; tauto)
  obtain ⟨r, hr1, hr2, hr3, hr4, -⟩ := Nat.exists_first_Ioc
    (Q := fun r => (C r u).lvl ≠ (C t u).lvl ∨ (C r v).lvl ≠ (C t v).lvl) (s := t)
    (by simp) ⟨s, hs1, hs2, hs3⟩
  push Not at hr3
  have h25 := hC.obs25 (t := r) huv (by rw [hr3.1, hr3.2]; exact hnp)
    (by rw [hr3.1, hr3.2]; exact hlt)
  rw [hr3.1, hr3.2] at h25
  refine ⟨r + 1, by omega, hr2, h25.1, h25.2.2, ?_⟩
  rcases hr4 with h | h
  · left; exact lt_of_le_of_ne h25.1 (Ne.symm h)
  · right; exact lt_of_le_of_ne h25.2.2 h

/-- Inner induction of Lemma 2.14: while `v` stays at level `ℓ`, a neighbour `u` that is
`≥ 2` units outwards of `ℓ` moves inwards one level at a time, the move from level `j` taking at
most `2(k - j) + 2` rounds (Lemma 2.13). -/
theorem lemma_2_14_aux {t X : ℕ} {v u : V} {ℓ : ℤ} (hop : LOutProt G C t (outw ℓ))
    (hv : ∀ s, t ≤ s → s ≤ X → (C s v).lvl = ℓ) (hu : G.Adj v u) (n : ℕ) :
    ∀ s, t ≤ s → (C s u).lvl.natAbs ≤ ℓ.natAbs + 1 + n →
      (rho A)^[cost14 k ℓ.natAbs n] s ≤ X →
      ∃ s', s ≤ s' ∧ s' ≤ (rho A)^[cost14 k ℓ.natAbs n] s ∧ ¬ FarOut ℓ (C s' u).lvl := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs habs hX
  have hsX : s ≤ X := (le_rho_iter hA _ s).trans hX
  by_cases hfar : FarOut ℓ (C s u).lvl
  swap
  · exact ⟨s, le_rfl, le_rho_iter hA _ s, hfar⟩
  have hvl := hv s hs hsX
  have hfar2 := natAbs_of_farOut hfar
  obtain ⟨j, hj⟩ : ∃ j, (C s u).lvl.natAbs = ℓ.natAbs + 2 + j := ⟨_, (Nat.add_sub_of_le hfar2).symm⟩
  have hjn : j + 1 ≤ n := by omega
  have hnp : ¬ Prot G C s u := by
    intro hp
    have h' := hp v hu.symm
    rw [hvl] at h'
    exact not_farOut_of_lAdj (hvl ▸ (C s v).isLevel) (C s u).isLevel h' hfar
  have hopu : LOutProt G C s (C s u).lvl := fun w hw =>
    hC.lOutProt_le hop hs w (outEq_trans (outEq_outw_of_farOut hfar) hw)
  set c := 2 * (k - (C s u).lvl.natAbs) + 2 with hc
  have hcost : cost14 k ℓ.natAbs j + c = cost14 k ℓ.natAbs (j + 1) := by
    rw [cost14_succ, hc, hj]
  have hcostn : (rho A)^[cost14 k ℓ.natAbs (j + 1)] s ≤ (rho A)^[cost14 k ℓ.natAbs n] s :=
    rho_iter_le_iter hA (cost14_mono _ _ hjn) s
  have hcj : (rho A)^[c] s ≤ (rho A)^[cost14 k ℓ.natAbs (j + 1)] s :=
    rho_iter_le_iter hA (by rw [← hcost]; omega) s
  have hex := hC.lemma_2_13 hA (by omega) hopu hnp
  obtain ⟨s1, ⟨hs1a, hs1b, hs1c⟩, hmin⟩ : ∃ s1, (s < s1 ∧ s1 ≤ (rho A)^[c] s ∧
      ((C s1 u).lvl ≠ (C s u).lvl ∨ Prot G C s1 u)) ∧ ∀ r < s1, ¬ (s < r ∧ r ≤ (rho A)^[c] s ∧
      ((C r u).lvl ≠ (C s u).lvl ∨ Prot G C r u)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min hex hr⟩
  obtain ⟨r, rfl⟩ : ∃ r, s1 = r + 1 := ⟨s1 - 1, by omega⟩
  have hr : (C r u).lvl = (C s u).lvl ∧ ¬ Prot G C r u := by
    rcases Nat.eq_or_lt_of_le (show s ≤ r by omega) with h | h
    · subst h; exact ⟨rfl, hnp⟩
    · have := hmin r (by omega)
      push Not at this
      exact this h (by omega)
  have hs1X : r + 1 ≤ X := by omega
  rcases hs1c with hch | hprot
  · -- `u` moved one level inwards
    obtain ⟨-, hlv, -⟩ := hC.lvl_succ_of_not_prot hr.2 (by rw [hr.1]; exact hch)
    have habs' : (C (r + 1) u).lvl.natAbs ≤ ℓ.natAbs + 1 + j := by
      rw [hlv, hr.1]; have := farOut_inw hfar; omega
    have hle : (rho A)^[cost14 k ℓ.natAbs j] (r + 1) ≤ (rho A)^[cost14 k ℓ.natAbs (j + 1)] s := by
      rw [← hcost, ← rho_iter_add]
      exact rho_iter_mono hA _ hs1b
    obtain ⟨s', h1, h2, h3⟩ := ih j (by omega) (r + 1) (by omega) habs' (by omega)
    exact ⟨s', by omega, by omega, h3⟩
  · -- `u` became protected
    refine ⟨r + 1, by omega, by omega, ?_⟩
    have h' := hprot v hu.symm
    rw [hv (r + 1) (by omega) hs1X] at h'
    exact not_farOut_of_lAdj (hv (r + 1) (by omega) hs1X ▸ (C (r + 1) v).isLevel)
      (C (r + 1) u).isLevel h'

/-- Lemma 2.14 of [EK21]: if `1 ≤ |ℓ| ≤ k - 1` and the graph is `ψ⁺¹(ℓ)`-out-protected at time
`t`, then it is `ℓ`-out-protected at time `ϱ^{(k-|ℓ|)(k-|ℓ|-1)}(t)`. -/
theorem lemma_2_14 {t : ℕ} {ℓ : ℤ} (hk : ℓ.natAbs + 1 ≤ k) (hop : LOutProt G C t (outw ℓ)) :
    LOutProt G C ((rho A)^[(k - ℓ.natAbs) * (k - ℓ.natAbs - 1)] t) ℓ := by
  set X := (rho A)^[(k - ℓ.natAbs) * (k - ℓ.natAbs - 1)] t with hXdef
  have htX : t ≤ X := le_rho_iter hA _ t
  intro v hv
  rcases hv with hv | hv
  swap
  · exact hC.lOutProt_le hop htX v (outEq_outw_of_outward hv)
  by_cases hch : ∃ r, t ≤ r ∧ r < X ∧ (C (r + 1) v).lvl ≠ (C r v).lvl
  · obtain ⟨r, hr1, hr2, hr3⟩ := hch
    exact hC.outProt_le (hC.obs24 hr3) (by omega)
  push Not at hch
  have hconst : ∀ s, t ≤ s → s ≤ X → (C s v).lvl = ℓ :=
    Nat.Icc_induction_down (P := fun s => (C s v).lvl = ℓ) hv fun s hs hsX h => (hch s hs hsX) ▸ h
  intro u hu
  rw [hv]
  obtain ⟨s', hs'1, hs'2, hs'3⟩ := hC.lemma_2_14_aux hA hop hconst hu (k - ℓ.natAbs - 1) t le_rfl
    (by have := natAbs_le_of_isLevel (C t u).isLevel; omega)
    (by rw [cost14_eq (by omega)])
  rw [cost14_eq (by omega)] at hs'2
  refine Nat.Icc_induction_up (P := fun s => ¬ FarOut ℓ (C s u).lvl) hs'3 (fun s hs hsX h => ?_) X hs'2
    le_rfl
  have hvs := hconst s (by omega) (by omega)
  have hvs' := hconst (s + 1) (by omega) (by omega)
  have := obs23_pure (C s v).isLevel (C s u).isLevel (C s v).faulty_two (C s u).faulty_two
    (hC.moveRel hu) (hC.moveRel hu.symm) (by rw [hvs]; exact h)
  rwa [hvs'] at this

/-- Iterating Lemma 2.14 from the outermost levels: `ℓ`-out-protection holds at time
`ϱ^{outRounds k |ℓ|}(t)`. -/
theorem lOutProt_outRounds (t : ℕ) (n : ℕ) : ∀ ℓ : ℤ, ℓ.natAbs + n = k → 1 ≤ ℓ.natAbs →
    LOutProt G C ((rho A)^[outRounds k ℓ.natAbs] t) ℓ := by
  induction n with
  | zero =>
    intro ℓ hℓ _ v hv
    have := outEq_of_natAbs_eq (C _ v).isLevel (by omega) hv
    intro u _
    rw [this]
    exact not_farOut_of_natAbs_eq (C _ u).isLevel (by omega)
  | succ n ih =>
    intro ℓ hℓ h1
    have hℓ0 : ℓ ≠ 0 := by omega
    have h' := ih (outw ℓ) (by rw [natAbs_outw hℓ0]; omega) (by rw [natAbs_outw hℓ0]; omega)
    rw [natAbs_outw hℓ0] at h'
    have := hC.lemma_2_14 hA (by omega) h'
    rwa [rho_iter_add, ← outRounds_succ (by omega)] at this

/-- Corollary 2.15 of [EK21]: the graph is out-protected at all times
`t ≥ T₀ = R(∑_{j=1}^{k-1} (k-j)(k-j-1))` (`= R(O(k³))`). -/
theorem corollary_2_15 (hk : 1 ≤ k) {t : ℕ} (ht : R A (outRounds k 1) ≤ t) :
    AllOutProt G C t := by
  intro v
  have h1 := hC.lOutProt_outRounds hA 0 (k - 1) 1 (by simp; omega) (by simp)
  have h2 := hC.lOutProt_outRounds hA 0 (k - 1) (-1) (by simp; omega) (by simp)
  simp only [Int.natAbs_one, Int.natAbs_neg] at h1 h2
  rcases outEq_or_of_isLevel (C t v).isLevel with h | h
  · exact hC.lOutProt_le h1 ht v h
  · exact hC.lOutProt_le h2 ht v h

end AURun

end ThinUnison
