import Papers.PODC2021.ThinUnison.OutProtected

/-!
# AlgAU: from an out-protected to a justified graph (Section 2.3.4, Lemmas 2.16–2.18)
-/

namespace ThinUnison

open Cslib.StoneAge

section Pure

variable {k : ℕ}

/-- In an out-protected graph, the endpoints of a non-protected edge have different signs, and a
move of one endpoint (with the other one fixed at `|a| ≥ 2`) keeps the edge non-protected. -/
theorem unprot_stays_pure {a b b' : ℤ} {f g : Bool} (_ha : IsLevel k a) (hb : IsLevel k b)
    (hg : g = true → 2 ≤ b ∨ b ≤ -2) (h2 : 2 ≤ a.natAbs) (h : ¬ LAdj k a b)
    (hab : ¬ FarOut a b) (hba : ¬ FarOut b a) (mb : MoveRel k b b' g a f) : ¬ LAdj k a b' := by
  unfold MoveRel at mb
  rcases mb with rfl | ⟨-, -, hm, rfl⟩ | ⟨rfl, -, rfl⟩
  · exact h
  · exfalso; apply h
    rcases hm with hm | hm
    · exact Or.inl hm
    · exact Or.inr (Or.inl hm)
  · simp only [true_implies] at hg
    unfold LAdj at h ⊢
    have := fwd_spec k a; have := fwd_spec k b; have := fwd_spec k (inw b)
    have := inw_spec b
    unfold IsLevel at hb; unfold FarOut at hab hba
    omega

theorem outward_inw {a : ℤ} (h2 : 2 ≤ a.natAbs) : Outward (inw a) a := by lvl_omega

theorem natAbs_inw {a : ℤ} (h2 : 2 ≤ a.natAbs) : (inw a).natAbs + 1 = a.natAbs := by lvl_omega

end Pure

namespace AURun

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {A : ℕ → Set V} {C : ℕ → V → Turn k}
variable (hC : AURun G A C)
include hC

/-- Lemma 2.16 of [EK21]: in an out-protected graph, a node that is not unjustifiably faulty at
time `t` is not unjustifiably faulty at time `t + 1`. -/
theorem lemma_2_16 {t : ℕ} {v : V} (hop : AllOutProt G C t)
    (hv : (C t v).faulty = true → JustFaulty G C t v) :
    (C (t + 1) v).faulty = true → JustFaulty G C (t + 1) v := by
  intro hf1
  -- the level of `v` is unchanged and `v` has a reason at time `t`
  obtain ⟨hlv, hreason⟩ : (C (t + 1) v).lvl = (C t v).lvl ∧ (¬ Prot G C t v ∨
      ∃ u, G.Adj v u ∧ (C t u).faulty = true ∧ (C t u).lvl = inw (C t v).lvl) := by
    rcases hC.step_cases t v with h | ⟨-, -, -, -, h⟩ | ⟨-, -, h1, h2, -⟩ | ⟨-, -, -, -, h⟩
    · rw [h] at hf1 ⊢; exact ⟨rfl, (hv hf1).2⟩
    · rw [h] at hf1; exact absurd hf1 Bool.false_ne_true
    · exact ⟨h2, h1.2⟩
    · rw [h] at hf1; exact absurd hf1 Bool.false_ne_true
  have h2 : 2 ≤ (C t v).lvl.natAbs := by
    have := (C (t + 1) v).faulty_two hf1; rw [hlv] at this; omega
  refine ⟨hf1, ?_⟩
  rcases hreason with hnp | ⟨u, hu, huf, hul⟩
  · -- (i) a non-protected edge stays non-protected
    left
    intro hp1
    apply hnp
    intro u hu
    by_contra hnadj
    have := unprot_stays_pure (C t v).isLevel (C t u).isLevel (C t u).faulty_two h2 hnadj
      (hop v u hu) (hop u v hu.symm) (hC.moveRel (t := t) hu.symm)
    rw [← hlv] at this
    exact this (hp1 u hu)
  · -- (ii) the faulty neighbour at `ψ⁻¹(λ_v)` cannot move
    right
    refine ⟨u, hu, ?_⟩
    rcases hC.faulty_cases huf with h | ⟨-, hfan, -, -⟩
    · rw [h, hlv]; exact ⟨huf, hul⟩
    · exfalso
      apply hfan v hu.symm
      rw [hul]; exact outward_inw h2

omit hC in
/-- Lemma 2.18 of [EK21]: a justified protected graph is good. -/
theorem lemma_2_18 {t : ℕ} (hj : Justified G C t) (hp : AllProt G C t) : AllGood G C t := by
  have key : ∀ n v, (C t v).lvl.natAbs = n → (C t v).faulty = false := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro v hn
    by_contra hf
    simp only [Bool.not_eq_false] at hf
    rcases (hj v hf).2 with h | ⟨u, -, hu, hul⟩
    · exact h (hp v)
    · have h2 := (C t v).faulty_two hf
      have := natAbs_inw (a := (C t v).lvl) (by omega)
      rw [← hul] at this
      have := ih _ (by omega) u rfl
      rw [hu] at this; exact Bool.false_ne_true this.symm
  exact fun v => ⟨hp v, key _ v rfl, fun u _ => key _ u rfl⟩

variable [Finite V] (hA : Fair A)
include hA

/-- Corollary 2.17 of [EK21]: if the graph is out-protected from time `T₀` on (and `k ≥ 2`), it is
justified from time `T₁ = ϱ^{2k-3}(T₀)` on. -/
theorem corollary_2_17 {T0 : ℕ} (hop : ∀ t, T0 ≤ t → AllOutProt G C t) {t : ℕ}
    (ht : (rho A)^[2 * k - 3] T0 ≤ t) : Justified G C t := by
  intro v
  -- a time `s ≤ T₁` from which `v` is never unjustifiably faulty
  obtain ⟨s, hs1, hs2, hs3⟩ : ∃ s, T0 ≤ s ∧ s ≤ (rho A)^[2 * k - 3] T0 ∧
      ((C s v).faulty = true → JustFaulty G C s v) := by
    by_cases h : (C T0 v).faulty = true → JustFaulty G C T0 v
    · exact ⟨T0, le_rfl, le_rho_iter hA _ _, h⟩
    · push Not at h
      obtain ⟨hf, -⟩ := h
      have h2 := (C T0 v).faulty_two hf
      have hk := natAbs_le_of_isLevel (C T0 v).isLevel
      obtain ⟨s, hs1, hs2, -, -, -, hs6⟩ := hC.lemma_2_12 hA (by omega)
        (fun w _ => hop T0 le_rfl w) rfl hf
      refine ⟨s + 1, by omega, ?_, fun h => absurd (hs6 ▸ h) Bool.false_ne_true⟩
      exact Nat.succ_le_of_lt (lt_of_lt_of_le hs2 (rho_iter_le_iter hA (by omega) _))
  exact fwd_induction (P := fun r => (C r v).faulty = true → JustFaulty G C r v) hs3
    (fun r hr _ h => hC.lemma_2_16 (hop r (by omega)) h) t (by omega) le_rfl

end AURun

end ThinUnison
