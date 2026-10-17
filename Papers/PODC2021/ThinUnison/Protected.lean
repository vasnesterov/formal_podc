import Papers.PODC2021.ThinUnison.Justified
import Cslib.Computability.Distributed.SelfStabilization.Unison
import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner
import Mathlib
import Cslib.Foundations.Data.Nat.Descent

/-!
# AlgAU: from a justified to a good graph (Section 2.3.5, Lemmas 2.19–2.22)

All lemmas here only need the graph to be out-protected (from the starting time on), except
Lemma 2.21 which needs that protected graphs stay protected (true from `T₁` on by Lemmas 2.18 and
2.10).
-/

namespace ThinUnison

open Cslib.StoneAge

section Pure

variable {k : ℕ}

theorem sign_diff_of_unprot {a b : ℤ} (ha : IsLevel k a) (hb : IsLevel k b) (h : ¬ LAdj k a b)
    (hab : ¬ FarOut a b) (hba : ¬ FarOut b a) : (0 < a ↔ b < 0) := by
  unfold LAdj at h; lvl_omega

theorem lAdj_diff_sign {x y : ℤ} (hx : IsLevel k x) (hy : IsLevel k y) (hs : 0 < x ↔ y < 0)
    (h : LAdj k x y) : (x.natAbs = 1 ∧ y.natAbs = 1) ∨ (x.natAbs = k ∧ y.natAbs = k) := by
  rcases h with rfl | rfl | rfl <;> lvl_omega

/-- In an out-protected graph a non-protected edge can only become protected at levels
`{-1, 1}`. -/
theorem newly_prot_pure {a b a' b' : ℤ} {f g : Bool} (ha : IsLevel k a) (hb : IsLevel k b)
    (hf : f = true → 2 ≤ a ∨ a ≤ -2) (hg : g = true → 2 ≤ b ∨ b ≤ -2)
    (ma : MoveRel k a a' f b g) (mb : MoveRel k b b' g a f) (h : ¬ LAdj k a b)
    (hab : ¬ FarOut a b) (hba : ¬ FarOut b a) (h' : LAdj k a' b') : a'.natAbs = 1 := by
  have hs := sign_diff_of_unprot ha hb h hab hba
  have hna : ¬ (a = b ∨ a = fwd k b) := fun h'' => h (by unfold LAdj; tauto)
  have hnb : ¬ (b = a ∨ b = fwd k a) := fun h'' => h (by
    unfold LAdj; rcases h'' with h'' | h'' <;> tauto)
  unfold MoveRel at ma mb
  -- the new levels: `a' ∈ {a, ψ⁻¹ a}`, `b' ∈ {b, ψ⁻¹ b}`
  have ha' : a' = a ∨ (2 ≤ a.natAbs ∧ a' = inw a) := by
    rcases ma with h1 | ⟨-, -, hm, -⟩ | ⟨rfl, -, h1⟩
    · exact Or.inl h1
    · exact absurd hm hnb
    · simp only [true_implies] at hf; exact Or.inr ⟨by omega, h1⟩
  have hb' : b' = b ∨ (2 ≤ b.natAbs ∧ b' = inw b) := by
    rcases mb with h1 | ⟨-, -, hm, -⟩ | ⟨rfl, -, h1⟩
    · exact Or.inl h1
    · exact absurd hm hna
    · simp only [true_implies] at hg; exact Or.inr ⟨by omega, h1⟩
  have hva' : IsLevel k a' := by
    clear * - ha ha'; rcases ha' with rfl | ⟨h1, rfl⟩ <;> lvl_omega
  have hvb' : IsLevel k b' := by
    clear * - hb hb'; rcases hb' with rfl | ⟨h1, rfl⟩ <;> lvl_omega
  have hs' : 0 < a' ↔ b' < 0 := by
    clear * - hs ha' hb' ha hb
    rcases ha' with rfl | ⟨h1, rfl⟩ <;> rcases hb' with rfl | ⟨h2, rfl⟩ <;> lvl_omega
  rcases lAdj_diff_sign hva' hvb' hs' h' with h1 | ⟨h1, h2⟩
  · exact h1.1
  · exfalso
    have hk1 : a.natAbs = k := by
      rcases ha' with rfl | ⟨h3, rfl⟩
      · exact h1
      · clear * - h1 h3 ha; have := natAbs_le_of_isLevel ha; lvl_omega
    have hk2 : b.natAbs = k := by
      rcases hb' with rfl | ⟨h3, rfl⟩
      · exact h2
      · clear * - h2 h3 hb; have := natAbs_le_of_isLevel hb; lvl_omega
    clear * - hk1 hk2 h hs ha hb
    apply h; unfold LAdj; have := fwd_spec k a; have := fwd_spec k b; unfold IsLevel at ha hb
    omega

/-- Level changes in the region `{-1} ∪ [1, k-1]`. -/
theorem region_step {x x' : ℤ} {f : Bool} (hx : IsLevel k x) (hf : f = true → 2 ≤ x ∨ x ≤ -2)
    (hstep : x' = x ∨ x' = fwd k x ∨ (f = true ∧ x' = inw x))
    (hreg : x = -1 ∨ (1 ≤ x ∧ x + 1 ≤ k)) :
    (x = -1 ∧ (x' = -1 ∨ x' = 1)) ∨ (1 ≤ x ∧ 1 ≤ x' ∧ x - 1 ≤ x' ∧ x' ≤ x + 1) := by
  rcases hstep with rfl | rfl | ⟨rfl, rfl⟩
  · lvl_omega
  · lvl_omega
  · simp only [true_implies] at hf; lvl_omega

/-- Adjacent levels in the positive range `[2, k-2]` differ by at most one. -/
theorem lAdj_pos_mid {a b : ℤ} (hb : IsLevel k b) (h2 : 2 ≤ a) (hak : a + 2 ≤ k)
    (h : LAdj k a b) : a - 1 ≤ b ∧ b ≤ a + 1 := by
  rcases h with rfl | rfl | rfl <;> lvl_omega

theorem lAdj_of_aan {a b : ℤ} (h : b = a ∨ b = fwd k a) : LAdj k a b := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)

theorem lAdj_of_natAbs_one {a b : ℤ} (hk : 2 ≤ k) (ha : a.natAbs = 1) (hb : b.natAbs = 1) :
    LAdj k a b := by
  unfold LAdj; have := fwd_spec k a; have := fwd_spec k b; omega

end Pure

namespace AURun

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {A : ℕ → Set V} {C : ℕ → V → Turn k}
variable (hC : AURun G A C)
include hC

/-- The level of a node changes only by `φ` (AA) or `ψ⁻¹` (FA, from a faulty turn). -/
theorem lvl_succ_cases (s : ℕ) (v : V) :
    (C (s + 1) v).lvl = (C s v).lvl ∨ (C (s + 1) v).lvl = fwd k (C s v).lvl ∨
      ((C s v).faulty = true ∧ (C (s + 1) v).lvl = inw (C s v).lvl) := by
  rcases hC.step_cases s v with h | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, h1, -, h, -⟩
  · left; rw [h]
  · right; left; exact h
  · left; exact h
  · right; right; exact ⟨h1, h⟩

/-- In an out-protected graph, a node that becomes protected is at level `±1`. -/
theorem natAbs_eq_one_of_newly_prot {t : ℕ} {v : V} (hop : AllOutProt G C t)
    (h0 : ¬ Prot G C t v) (h1 : Prot G C (t + 1) v) : (C (t + 1) v).lvl.natAbs = 1 := by
  simp only [Prot, not_forall] at h0
  obtain ⟨u, hu, hnadj⟩ := h0
  exact newly_prot_pure (C t v).isLevel (C t u).isLevel (C t v).faulty_two (C t u).faulty_two
    (hC.moveRel hu) (hC.moveRel hu.symm) hnadj (hop v u hu) (hop u v hu.symm) (h1 u hu)

/-- A non-protected node at level `±1` does not move. -/
theorem lvl_succ_of_not_prot_one {s : ℕ} {v : V} (h : ¬ Prot G C s v)
    (h1 : (C s v).lvl.natAbs = 1) : (C (s + 1) v).lvl = (C s v).lvl := by
  by_contra hne
  obtain ⟨hf, -⟩ := hC.lvl_succ_of_not_prot h hne
  have := (C s v).faulty_two hf; omega

variable [Finite V] (hA : Fair A)
include hA

/-- Lemma 2.13 in the out-protected regime: a non-protected node with `|λ| ≥ 2` changes its level
or becomes protected within `2k - 2` rounds. -/
theorem lemma_2_13' {t : ℕ} {u : V} (hop : AllOutProt G C t) (h2 : 2 ≤ (C t u).lvl.natAbs)
    (hu : ¬ Prot G C t u) :
    ∃ s, t < s ∧ s ≤ (rho A)^[2 * k - 2] t ∧ ((C s u).lvl ≠ (C t u).lvl ∨ Prot G C s u) := by
  obtain ⟨s, h1, h2', h3⟩ := hC.lemma_2_13 hA h2 (fun w _ => hop w) hu
  have hk := natAbs_le_of_isLevel (C t u).isLevel
  exact ⟨s, h1, h2'.trans (rho_iter_le_iter hA (by omega) t), h3⟩

/-- First phase of Lemma 2.19: a non-protected node moves inwards until it is protected or at
level `±1`, within `(|λ| - 1)(2k - 2)` rounds. -/
theorem lemma_2_19_phaseA {t : ℕ} (hop : AllOutProt G C t) (v : V) (n : ℕ) :
    ∀ s, t ≤ s → ¬ Prot G C s v → (C s v).lvl.natAbs ≤ n + 1 →
      ∃ s', s ≤ s' ∧ s' ≤ (rho A)^[n * (2 * k - 2)] s ∧
        (Prot G C s' v ∨ (C s' v).lvl.natAbs = 1) := by
  induction n with
  | zero =>
    intro s _ _ habs
    exact ⟨s, le_rfl, le_rho_iter hA _ s, Or.inr (by have := (C s v).isLevel; lvl_omega)⟩
  | succ n ih =>
    intro s hs hnp habs
    by_cases h1 : (C s v).lvl.natAbs = 1
    · exact ⟨s, le_rfl, le_rho_iter hA _ s, Or.inr h1⟩
    have h2 : 2 ≤ (C s v).lvl.natAbs := by have := (C s v).isLevel; lvl_omega
    have hops := hC.allOutProt_le hop hs
    obtain ⟨r, hr1, hr2, hr3, hr4, hr5⟩ := Nat.exists_first_Ioc
      (Q := fun r => (C r v).lvl ≠ (C s v).lvl ∨ Prot G C r v) (by simp [hnp])
      (hC.lemma_2_13' hA hops h2 hnp)
    have hle : (rho A)^[2 * k - 2] s ≤ (rho A)^[(n + 1) * (2 * k - 2)] s :=
      rho_iter_le_iter hA (by nlinarith) s
    simp only [not_or, not_not] at hr3
    rcases hr4 with hch | hprot
    · obtain ⟨-, hlv, -⟩ := hC.lvl_succ_of_not_prot hr3.2 (by rw [hr3.1]; exact hch)
      have habs' : (C (r + 1) v).lvl.natAbs ≤ n + 1 := by
        rw [hlv, hr3.1]; have := natAbs_inw h2; omega
      by_cases hnp' : Prot G C (r + 1) v
      · exact ⟨r + 1, by omega, hr2.trans hle, Or.inl hnp'⟩
      obtain ⟨s', h1', h2'', h3'⟩ := ih (r + 1) (by omega) hnp' habs'
      refine ⟨s', by omega, h2''.trans ?_, h3'⟩
      calc (rho A)^[n * (2 * k - 2)] (r + 1)
          ≤ (rho A)^[n * (2 * k - 2)] ((rho A)^[2 * k - 2] s) := rho_iter_mono hA _ hr2
        _ = (rho A)^[(n + 1) * (2 * k - 2)] s := by rw [rho_iter_add]; congr 1; ring
    · exact ⟨r + 1, by omega, hr2.trans hle, Or.inl hprot⟩

/-- Second phase of Lemma 2.19: a non-protected node at level `±1` becomes protected within
`(k - 1)(2k - 2)` rounds. -/
theorem lemma_2_19_phaseB (hk : 2 ≤ k) {t : ℕ} (hop : AllOutProt G C t) {v : V}
    (hnp : ¬ Prot G C t v) (h1 : (C t v).lvl.natAbs = 1) :
    ∃ s, t < s ∧ s ≤ (rho A)^[(k - 1) * (2 * k - 2)] t ∧ Prot G C s v := by
  set X := (rho A)^[(k - 1) * (2 * k - 2)] t
  by_contra H
  push Not at H
  have hnp' : ∀ s, t ≤ s → s ≤ X → ¬ Prot G C s v := by
    intro s hs hsX
    rcases Nat.eq_or_lt_of_le hs with h | h
    · subst h; exact hnp
    · exact H s h hsX
  have hconst : ∀ s, t ≤ s → s ≤ X → (C s v).lvl = (C t v).lvl :=
    Nat.Icc_induction_up (P := fun s => (C s v).lvl = (C t v).lvl) rfl fun s hs hsX h => by
      rw [hC.lvl_succ_of_not_prot_one (hnp' s hs hsX.le) (h ▸ h1), h]
  apply hnp' X (le_rho_iter hA _ t) le_rfl
  intro u hu
  -- some time in `[t, X]` at which the edge `(v, u)` is protected
  obtain ⟨s', hs'1, hs'2, hs'3⟩ : ∃ s', t ≤ s' ∧ s' ≤ X ∧ LAdj k (C s' v).lvl (C s' u).lvl := by
    by_cases hadj : LAdj k (C t v).lvl (C t u).lvl
    · exact ⟨t, le_rfl, le_rho_iter hA _ t, hadj⟩
    have hnpu : ¬ Prot G C t u := fun hp => hadj (by
      have := hp v hu.symm; unfold LAdj at this ⊢; tauto)
    obtain ⟨s', h1', h2', h3'⟩ := hC.lemma_2_19_phaseA hA hop u (k - 1) t le_rfl hnpu
      (by have := natAbs_le_of_isLevel (C t u).isLevel; omega)
    refine ⟨s', h1', h2', ?_⟩
    rcases h3' with hp | habs
    · have := hp v hu.symm; unfold LAdj at this ⊢; tauto
    · rw [hconst s' h1' h2'] at *
      exact lAdj_of_natAbs_one hk h1 habs
  refine Nat.Icc_induction_up (P := fun s => LAdj k (C s v).lvl (C s u).lvl) hs'3
    (fun s hs hsX h => ?_) X hs'2 le_rfl
  have hvs := hconst s (by omega) hsX.le
  exact hC.obs21 hu h (by rw [hvs]; omega) (by rw [hvs]; omega)

/-- Lemma 2.19 of [EK21] (in the out-protected regime): a non-protected node becomes protected
within `2(k-1)(2k-2)` rounds; at the first such time its level is `±1`. -/
theorem lemma_2_19 (hk : 2 ≤ k) {t : ℕ} (hop : AllOutProt G C t) {v : V}
    (hnp : ¬ Prot G C t v) :
    ∃ s, t < s ∧ s ≤ (rho A)^[2 * ((k - 1) * (2 * k - 2))] t ∧ Prot G C s v ∧
      (C s v).lvl.natAbs = 1 := by
  set c := (k - 1) * (2 * k - 2)
  have hex : ∃ s, t < s ∧ s ≤ (rho A)^[2 * c] t ∧ Prot G C s v := by
    obtain ⟨s1, h1, h2, h3⟩ := hC.lemma_2_19_phaseA hA hop v (k - 1) t le_rfl hnp
      (by have := natAbs_le_of_isLevel (C t v).isLevel; omega)
    have h2c : (rho A)^[c] t ≤ (rho A)^[2 * c] t := rho_iter_le_iter hA (by omega) t
    by_cases hp : Prot G C s1 v
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h; exact absurd hp hnp
      · exact ⟨s1, h, h2.trans h2c, hp⟩
    · rcases h3 with h3 | h3
      · exact absurd h3 hp
      obtain ⟨s, h4, h5, h6⟩ := hC.lemma_2_19_phaseB hA hk (hC.allOutProt_le hop h1) hp h3
      refine ⟨s, by omega, h5.trans ?_, h6⟩
      calc (rho A)^[c] s1 ≤ (rho A)^[c] ((rho A)^[c] t) := rho_iter_mono hA _ h2
        _ = (rho A)^[2 * c] t := by rw [rho_iter_add, two_mul]
  obtain ⟨r, hr1, hr2, hr3, hr4, -⟩ := Nat.exists_first_Ioc (Q := fun s => Prot G C s v) hnp hex
  exact ⟨r + 1, by omega, hr2, hr4,
    hC.natAbs_eq_one_of_newly_prot (hC.allOutProt_le hop hr1) hr3 hr4⟩

omit [Finite V] hA in
/-- An increase `x ↦ x + 1` of a positive level `x < k` is an AA transition: the node was able,
protected, and all its neighbours were able at level `x` or `x + 1`. -/
theorem aan_of_incr {s : ℕ} {v : V} (h1 : 1 ≤ (C s v).lvl) (_hk : (C s v).lvl < k)
    (hinc : (C (s + 1) v).lvl = (C s v).lvl + 1) :
    (C s v).faulty = false ∧ AAN G C s v ∧ Prot G C s v := by
  have hlv := (C s v).isLevel
  rcases hC.step_cases s v with h | ⟨-, h1', h2', -, -⟩ | ⟨-, -, -, h3, -⟩ | ⟨-, -, -, h3, -⟩
  · rw [h] at hinc; omega
  · exact ⟨h1', h2', fun u hu => lAdj_of_aan (h2' u hu).2⟩
  · rw [h3] at hinc; omega
  · rw [h3] at hinc; revert hinc; clear * - h1 hlv; lvl_omega

omit [Finite V] hA in
/-- One step of a node in the region `{-1} ∪ [1, k-1]`. -/
theorem region_step' {s : ℕ} {v : V} (hreg : (C s v).lvl = -1 ∨ (1 ≤ (C s v).lvl ∧
    (C s v).lvl + 1 ≤ k)) :
    ((C s v).lvl = -1 ∧ ((C (s + 1) v).lvl = -1 ∨ (C (s + 1) v).lvl = 1)) ∨
      (1 ≤ (C s v).lvl ∧ 1 ≤ (C (s + 1) v).lvl ∧ (C s v).lvl - 1 ≤ (C (s + 1) v).lvl ∧
        (C (s + 1) v).lvl ≤ (C s v).lvl + 1) :=
  region_step (C s v).isLevel (C s v).faulty_two (hC.lvl_succ_cases s v) hreg

omit [Finite V] hA in
/-- The claim in the proof of Lemma 2.20 of [EK21]: if `v` moves from level `ℓ` to `ℓ + 1` in step
`t`, from `ℓ + 2d` to `ℓ + 2d + 1` in step `t''`, and stays strictly between `ℓ` and `ℓ + 2d + 1` in
between (`1 ≤ ℓ`, `ℓ + 3d < k`), then all nodes at distance `≤ d` from `v` are protected at time
`t'' + 1`. -/
theorem lemma_2_20_claim (d : ℕ) : ∀ (v : V) (t t'' : ℕ) (ℓ : ℤ), 1 ≤ ℓ → ℓ + 3 * d < k →
    t ≤ t'' → (C t v).lvl = ℓ → (C (t + 1) v).lvl = ℓ + 1 → (C t'' v).lvl = ℓ + 2 * d →
    (C (t'' + 1) v).lvl = ℓ + 2 * d + 1 →
    (∀ s, t < s → s ≤ t'' → ℓ < (C s v).lvl ∧ (C s v).lvl < ℓ + 2 * d + 1) →
    ∀ u (p : G.Walk v u), p.length ≤ d → Prot G C (t'' + 1) u := by
  classical
  induction d with
  | zero =>
    intro v t t'' ℓ hℓ hk htt' h1 h2 h3 h4 _ u p hp
    have hp0 : p.length = 0 := by omega
    obtain ⟨-, -, hprot⟩ := hC.aan_of_incr (s := t'') (v := v) (by omega) (by omega) (by omega)
    have := hC.obs22 hprot (by omega) (by omega)
    obtain rfl : v = u := SimpleGraph.Walk.eq_of_length_eq_zero hp0
    exact this
  | succ d ih =>
    intro v t t'' ℓ hℓ hk htt' h1 h2 h3 h4 hmid u p hp
    -- `v` is protected throughout `[t, t'' + 1]`
    have hvlvl : ∀ s, t ≤ s → s ≤ t'' → ℓ ≤ (C s v).lvl ∧ (C s v).lvl ≤ ℓ + 2 * (d + 1) := by
      intro s hs hs'
      rcases Nat.eq_or_lt_of_le hs with h | h
      · subst h; omega
      · have := hmid s h hs'; omega
    obtain ⟨-, haan, hprot⟩ := hC.aan_of_incr (s := t) (v := v) (by omega) (by omega) (by omega)
    have hvprot : ∀ s, t ≤ s → s ≤ t'' + 1 → Prot G C s v :=
      Nat.Icc_induction_up (P := fun s => Prot G C s v) hprot fun s hs hs' h => by
        have := hvlvl s hs (by omega); exact hC.obs22 h (by omega) (by omega)
    cases p with
    | nil => exact hvprot (t'' + 1) (by omega) le_rfl
    | @cons _ w _ hvw q' =>
    simp only [SimpleGraph.Walk.length_cons] at hp
    -- the levels of the neighbour `w` during `[t, t'']`
    obtain ⟨-, haan'', -⟩ := hC.aan_of_incr (s := t'') (v := v) (by omega) (by omega) (by omega)
    have hwt : (C t w).lvl = ℓ ∨ (C t w).lvl = ℓ + 1 := by
      have := (haan w hvw).2
      have hf := fwd_spec k (C t v).lvl; omega
    have hwt'' : (C t'' w).lvl = ℓ + 2 * (d + 1) ∨ (C t'' w).lvl = ℓ + 2 * (d + 1) + 1 := by
      have := (haan'' w hvw).2
      have hf := fwd_spec k (C t'' v).lvl; push_cast at h3 ⊢; omega
    have hwrange : ∀ s, t ≤ s → s ≤ t'' → ℓ ≤ (C s w).lvl ∧ (C s w).lvl ≤ ℓ + 2 * (d + 1) + 1 := by
      intro s hs hs'
      rcases Nat.eq_or_lt_of_le hs with h | h
      · subst h; omega
      · have hm := hmid s h hs'
        have := lAdj_pos_mid (C s w).isLevel (by omega) (by omega) (hvprot s hs (by omega) w hvw)
        omega
    have hwstep : ∀ s, t ≤ s → s < t'' → (C s w).lvl - 1 ≤ (C (s + 1) w).lvl ∧
        (C (s + 1) w).lvl ≤ (C s w).lvl + 1 := by
      intro s hs hs'
      have hr := hwrange s hs hs'.le
      rcases hC.region_step' (s := s) (v := w) (Or.inr ⟨by omega, by omega⟩) with h | h
      · omega
      · exact ⟨h.2.2.1, h.2.2.2⟩
    -- `t'_w`: the first time `w` reaches level `ℓ + 2d + 2`
    obtain ⟨r, hr1, hr2, hr3, hr4, hr5⟩ := Nat.exists_first_Ioc
      (Q := fun s => ℓ + 2 * (d + 1) ≤ (C s w).lvl) (s := t) (B := t'')
      (by omega) ⟨t'', by
        rcases Nat.eq_or_lt_of_le htt' with h | h
        · subst h; omega
        · exact h, le_rfl, by omega⟩
    simp only [not_le] at hr3 hr5
    have hwr := hwstep r hr1 (by omega)
    have hwr1 : (C r w).lvl = ℓ + 1 + 2 * d ∧ (C (r + 1) w).lvl = ℓ + 1 + 2 * d + 1 := by omega
    -- `t_w`: the last time `≤ r` at which `w` is at level `≤ ℓ + 1`
    obtain ⟨q, hqge, hqle, hqP, hqgt⟩ :=
      Nat.exists_last_of_le (p := fun s => (C s w).lvl ≤ ℓ + 1) hr1 (by omega)
    simp only [not_le] at hqgt
    have hq1 : ℓ + 1 < (C (q + 1) w).lvl := by
      rcases Nat.eq_or_lt_of_le hqle with h | h
      · rw [h]; omega
      · exact hqgt (q + 1) (by omega) (by omega)
    have hwq := hwstep q hqge (by omega)
    have hwq1 : (C q w).lvl = ℓ + 1 ∧ (C (q + 1) w).lvl = ℓ + 1 + 1 := by
      have := hwrange q hqge (by omega); omega
    -- induction hypothesis for `w`
    have hIH := ih w q r (ℓ + 1) (by omega) (by omega) hqle hwq1.1 hwq1.2 hwr1.1 hwr1.2
      (fun x hx hxr => ⟨hqgt x hx hxr, by have := hr5 x (by omega) hxr; omega⟩)
    -- all nodes of `p` are protected at time `r + 1`
    have hall : ∀ x ∈ (SimpleGraph.Walk.cons hvw q').support, Prot G C (r + 1) x := by
      intro x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hvprot (r + 1) (by omega) (by omega)
      · exact hIH x (q'.takeUntil x hx) ((q'.length_takeUntil_le_length hx).trans (by omega))
    have := hC.obs29 (SimpleGraph.Walk.cons hvw q') hall (show r + 1 ≤ t'' + 1 by omega)
      (fun s hs hs' => by
        have := hmid s (by omega) (by omega)
        simp only [SimpleGraph.Walk.length_cons]; omega)
    exact this u (SimpleGraph.Walk.end_mem_support _)

omit [Finite V] hA in
/-- Lemma 2.20 of [EK21]: if a node `v` is at level `±1` at time `t` and at a level of magnitude
`≥ 2D + 2` at some time `s ≥ t` (with `3D + 2 ≤ k` and diameter `≤ D`), then the graph is protected
at some time in `(t, s]` (namely when `v` first reaches level `2D + 2`). -/
theorem lemma_2_20 {D : ℕ} (hk : 3 * D + 2 ≤ k) (hD : G.ediam ≤ D) {v : V} {t s : ℕ}
    (ht : (C t v).lvl.natAbs = 1) (hts : t ≤ s) (hs : 2 * D + 2 ≤ (C s v).lvl.natAbs) :
    ∃ r, t < r ∧ r ≤ s ∧ AllProt G C r := by
  classical
  obtain ⟨r0, hr1, hr2, hr3, hr4, hr5⟩ := Nat.exists_first_Ioc
    (Q := fun x => 2 * D + 2 ≤ (C x v).lvl.natAbs) (s := t) (B := s) (by omega)
    ⟨s, by rcases Nat.eq_or_lt_of_le hts with h | h
           · subst h; omega
           · exact h, le_rfl, hs⟩
  simp only [not_le] at hr3 hr5
  -- region invariant on `[t, r0]`
  have hreg : ∀ x, t ≤ x → x ≤ r0 → (C x v).lvl = -1 ∨ (1 ≤ (C x v).lvl ∧
      (C x v).lvl ≤ 2 * D + 1) := by
    refine Nat.Icc_induction_up (P := fun x => (C x v).lvl = -1 ∨ (1 ≤ (C x v).lvl ∧
      (C x v).lvl ≤ 2 * D + 1)) (by omega) (fun x hx hxr h => ?_)
    have h5 := hr5 (x + 1) (by omega) (by omega)
    rcases hC.region_step' (s := x) (v := v) (by omega) with h' | h' <;> omega
  have hr0 := hreg r0 hr1 le_rfl
  have hstep := hC.region_step' (s := r0) (v := v) (by omega)
  have hr0' : (C r0 v).lvl = 2 * D + 1 ∧ (C (r0 + 1) v).lvl = 2 * D + 2 := by omega
  -- the last time `≤ r0` at level `≤ 1`
  obtain ⟨q, hqge, hqle, hqP, hqgt⟩ :=
    Nat.exists_last_of_le (p := fun x => (C x v).lvl ≤ 1) hr1 (by omega)
  simp only [not_le] at hqgt
  have hq1 : 1 < (C (q + 1) v).lvl := by
    rcases Nat.eq_or_lt_of_le hqle with h | h
    · rw [h]; omega
    · exact hqgt (q + 1) (by omega) (by omega)
  have hqreg := hreg q hqge hqle
  have hqstep := hC.region_step' (s := q) (v := v) (by omega)
  have hq' : (C q v).lvl = 1 ∧ (C (q + 1) v).lvl = 1 + 1 := by omega
  refine ⟨r0 + 1, by omega, hr2, fun u => ?_⟩
  obtain ⟨p, hp⟩ := SimpleGraph.ediam_le_coe_iff.1 hD v u
  have := hC.lemma_2_20_claim D v q r0 1 le_rfl (by omega) hqle hq'.1 hq'.2 (by omega) (by omega)
    (fun x hx hxr => ⟨hqgt x hx hxr, by have := hreg x (by omega) hxr; omega⟩) u p hp
  intro w hw
  exact this w hw

variable (G C) in
/-- A node `v` is grounded at time `t` (w.r.t. the diameter bound `D`) if it lies on a walk of
length `≤ D` all of whose nodes are protected and one of whose endpoints is at level `±1`. -/
def Grounded (D t : ℕ) (v : V) : Prop :=
  ∃ (u w : V) (p : G.Walk u w), p.length ≤ D ∧ v ∈ p.support ∧
    (∀ x ∈ p.support, Prot G C t x) ∧ (C t u).lvl.natAbs = 1

omit [Finite V] hA in
/-- Lemma 2.21 of [EK21]: a grounded node stays protected, provided that protected graphs stay
protected (which holds from time `T₁` on by Lemmas 2.18 and 2.10). -/
theorem lemma_2_21 {D : ℕ} (hk : 3 * D + 2 ≤ k) (hD : G.ediam ≤ D) {t : ℕ}
    (hpersist : ∀ s, t ≤ s → AllProt G C s → AllProt G C (s + 1)) {v : V}
    (hg : Grounded G C D t v) : ∀ t', t ≤ t' → Prot G C t' v := by
  obtain ⟨u, w, p, hpl, hvp, hprot, hu⟩ := hg
  intro t' htt'
  by_contra hnp
  by_cases hsmall : ∀ s, t ≤ s → s < t' → (C s u).lvl.natAbs + p.length < k
  · exact hnp (hC.obs29 p hprot htt' hsmall v hvp)
  push Not at hsmall
  obtain ⟨s, hs1, hs2, hs3⟩ := hsmall
  obtain ⟨r, hr1, hr2, hr3⟩ := hC.lemma_2_20 hk hD hu hs1 (by omega)
  have : ∀ x, r ≤ x → x ≤ t' → AllProt G C x :=
    Nat.Icc_induction_up (P := fun x => AllProt G C x) hr3 fun x hx _ h => hpersist x (by omega) h
  exact hnp (this t' (by omega) le_rfl v)

/-- The inductive argument of Lemma 2.22 of [EK21]: if `v` is joined by a walk of length `j ≤ D`
to a non-protected node, all other nodes of the walk being protected, then `v` becomes grounded
within `(j + 1) · 2(k-1)(2k-2)` rounds. -/
theorem lemma_2_22_aux (hk2 : 2 ≤ k) {D T : ℕ} (hop : AllOutProt G C T) (j : ℕ) :
    ∀ t, T ≤ t → ∀ (v x : V) (p : G.Walk v x), p.length = j → j ≤ D →
      (∀ i < j, Prot G C t (p.getVert i)) → ¬ Prot G C t x →
      ∃ s, t ≤ s ∧ s ≤ (rho A)^[(j + 1) * (2 * ((k - 1) * (2 * k - 2)))] t ∧
        Grounded G C D s v := by
  classical
  set c := 2 * ((k - 1) * (2 * k - 2)) with hc
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro t hTt v x p hpl hjD hprot hnp
  have hopt := hC.allOutProt_le hop hTt
  obtain ⟨s1, hs1a, hs1b, hs1c, -⟩ := hC.lemma_2_19 hA hk2 hopt hnp
  rw [← hc] at hs1b
  obtain ⟨r, hr1, hr2, hr3, hr4, -⟩ := Nat.exists_first_Ioc
    (Q := fun r => (∃ i < j, ¬ Prot G C r (p.getVert i)) ∨ Prot G C r x)
    (by push Not; exact ⟨hprot, hnp⟩) ⟨s1, hs1a, hs1b, Or.inr hs1c⟩
  push Not at hr3
  have hcle : (rho A)^[c] t ≤ (rho A)^[(j + 1) * c] t :=
    rho_iter_le_iter hA (by nlinarith) t
  by_cases ha : ∃ i < j, ¬ Prot G C (r + 1) (p.getVert i)
  · -- a node of the walk became non-protected: recurse on the shorter prefix
    let i0 := Nat.find ha
    obtain ⟨hi0j, hi0⟩ := Nat.find_spec ha
    have hmin : ∀ i < i0, Prot G C (r + 1) (p.getVert i) := by
      intro i hi
      have := Nat.find_min ha hi
      push Not at this
      exact this (by omega)
    have hlen : (p.take i0).length = i0 := by
      rw [SimpleGraph.Walk.take_length]; omega
    obtain ⟨s, hs1, hs2, hs3⟩ := ih i0 hi0j (r + 1) (by omega) v (p.getVert i0) (p.take i0) hlen
      (by omega) (fun i hi => by
        rw [SimpleGraph.Walk.take_getVert, min_eq_right hi.le]; exact hmin i hi)
      hi0
    refine ⟨s, by omega, hs2.trans ?_, hs3⟩
    calc (rho A)^[(i0 + 1) * c] (r + 1) ≤ (rho A)^[j * c] ((rho A)^[c] t) :=
          (rho_iter_le_iter hA (Nat.mul_le_mul_right _ (by omega)) _).trans
            (rho_iter_mono hA _ hr2)
      _ = (rho A)^[(j + 1) * c] t := by rw [rho_iter_add]; congr 1; ring
  · -- the endpoint became protected: the walk is grounded
    push Not at ha
    have hx : Prot G C (r + 1) x := by
      rcases hr4 with ⟨i, hi, h⟩ | h
      · exact absurd (ha i hi) h
      · exact h
    have hx1 := hC.natAbs_eq_one_of_newly_prot (hC.allOutProt_le hopt hr1) hr3.2 hx
    refine ⟨r + 1, by omega, by omega, x, v, p.reverse, by simp; omega, by simp, ?_, hx1⟩
    intro y hy
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
      SimpleGraph.Walk.mem_support_iff_exists_getVert] at hy
    obtain ⟨n, rfl, hn⟩ := hy
    rcases Nat.lt_or_ge n j with h | h
    · exact ha n h
    · have : n = p.length := by omega
      rw [this, SimpleGraph.Walk.getVert_length]; exact hx

/-- Lemma 2.22 of [EK21]: if from time `T` on the graph is out-protected and protected graphs stay
protected (true from `T₁` on), then the graph is protected at time
`T₂ = ϱ^{(D+1) · 2(k-1)(2k-2)}(T)` (`= ϱ^{O(k³)}(T)`). -/
theorem lemma_2_22 {D : ℕ} (hk : 3 * D + 2 ≤ k) (hD : G.ediam ≤ D) {T : ℕ}
    (hop : AllOutProt G C T) (hpersist : ∀ s, T ≤ s → AllProt G C s → AllProt G C (s + 1)) :
    AllProt G C ((rho A)^[(D + 1) * (2 * ((k - 1) * (2 * k - 2)))] T) := by
  classical
  set X := (rho A)^[(D + 1) * (2 * ((k - 1) * (2 * k - 2)))] T
  by_cases hall : AllProt G C T
  · exact Nat.Icc_induction_up (P := fun x => AllProt G C x) hall (fun x hx _ h => hpersist x hx h) X
      (le_rho_iter hA _ T) le_rfl
  simp only [AllProt, not_forall] at hall
  obtain ⟨y, hy⟩ := hall
  intro v
  obtain ⟨p, hp⟩ := SimpleGraph.ediam_le_coe_iff.1 hD v y
  have hex : ∃ i, i ≤ p.length ∧ ¬ Prot G C T (p.getVert i) :=
    ⟨p.length, le_rfl, by rw [SimpleGraph.Walk.getVert_length]; exact hy⟩
  let i0 := Nat.find hex
  obtain ⟨hi0l, hi0⟩ := Nat.find_spec hex
  have hmin : ∀ i < i0, Prot G C T (p.getVert i) := by
    intro i hi
    have := Nat.find_min hex hi
    push Not at this
    exact this (by omega)
  have hlen : (p.take i0).length = i0 := by rw [SimpleGraph.Walk.take_length]; omega
  obtain ⟨s, hs1, hs2, hs3⟩ := hC.lemma_2_22_aux hA (D := D) (by omega) hop i0 T le_rfl v
    (p.getVert i0)
    (p.take i0) hlen (by omega)
    (fun i hi => by rw [SimpleGraph.Walk.take_getVert, min_eq_right hi.le]; exact hmin i hi) hi0
  refine hC.lemma_2_21 hk hD (fun x hx h => hpersist x (by omega) h) hs3 X (hs2.trans ?_)
  exact rho_iter_le_iter hA (Nat.mul_le_mul_right _ (by omega)) T

end AURun

end ThinUnison
