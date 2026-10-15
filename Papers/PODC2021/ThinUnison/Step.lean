import Papers.PODC2021.ThinUnison.Defs

/-!
# AlgAU: one-step transition lemmas

For an execution `C` of AlgAU (`hC : IsRun G (algAU k) A C`) we describe the possible transitions of
a node in terms of the turns of its neighbours (`step_cases`), and the enabling lemmas
(`succ_aa`, `succ_af`, `succ_fa`). `MoveRel` records, for a node `v` and a neighbour `u`, what the
transition of `v` implies about `u` — enough for the pairwise invariants of Section 2.3.1.
-/

namespace ThinUnison

open Cslib.StoneAge

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {A : ℕ → Set V} {C : ℕ → V → Turn k}

section Conds

variable (G C)

/-- AA condition, in terms of the neighbours. -/
def AAN (t : ℕ) (v : V) : Prop :=
  ∀ u, G.Adj v u → (C t u).faulty = false ∧ ((C t u).lvl = (C t v).lvl ∨
    (C t u).lvl = fwd k (C t v).lvl)

/-- FA condition, in terms of the neighbours. -/
def FAN (t : ℕ) (v : V) : Prop := ∀ u, G.Adj v u → ¬ Outward (C t v).lvl (C t u).lvl

/-- AF condition, in terms of the neighbours. -/
def AFN (t : ℕ) (v : V) : Prop :=
  (2 ≤ (C t v).lvl ∨ (C t v).lvl ≤ -2) ∧ (¬ Prot G C t v ∨
    ∃ u, G.Adj v u ∧ (C t u).faulty = true ∧ (C t u).lvl = inw (C t v).lvl)

end Conds

theorem aaCond_signal_iff {t : ℕ} {v : V} :
    AACond (C t v) (signal G (C t) v) ↔ (C t v).faulty = false ∧ AAN G C t v := by
  rw [AACond, forall_mem_signal]; simp [AAN]

theorem faCond_signal_iff {t : ℕ} {v : V} :
    FACond (C t v) (signal G (C t) v) ↔ FAN G C t v := by
  rw [FACond, forall_mem_signal]; simp [FAN, Outward]

theorem afCond_signal_iff {t : ℕ} {v : V} (hf : (C t v).faulty = false) :
    AFCond (C t v) (signal G (C t) v) ↔ AFN G C t v := by
  unfold AFCond AFN Prot
  apply and_congr_right; intro _
  apply or_congr
  · constructor
    · rintro ⟨q, ⟨u, hu | hu, rfl⟩, h⟩
      · subst hu; exact absurd (Or.inl rfl) h
      · exact fun h' => h (h' u hu)
    · intro h; push Not at h; obtain ⟨u, hu, h⟩ := h; exact ⟨_, mem_signal_of_adj G _ hu, h⟩
  · constructor
    · rintro ⟨q, ⟨u, hu | hu, rfl⟩, h⟩
      · subst hu; simp [hf] at h
      · exact ⟨u, hu, h⟩
    · rintro ⟨u, hu, h⟩; exact ⟨_, mem_signal_of_adj G _ hu, h⟩

/-- Possible moves of a node `v` (level `ℓ ↦ ℓ'`, faulty flag `f`) relative to a neighbour (level
`m`, faulty flag `g`): stay at the same level; an AA move (requires the neighbour able and at
level `ℓ` or `φ(ℓ)`); or an FA move (requires the neighbour not outwards of `ℓ`). -/
def MoveRel (k : ℕ) (ℓ ℓ' : ℤ) (f : Bool) (m : ℤ) (g : Bool) : Prop :=
  ℓ' = ℓ ∨ (f = false ∧ g = false ∧ (m = ℓ ∨ m = fwd k ℓ) ∧ ℓ' = fwd k ℓ) ∨
    (f = true ∧ ¬ Outward ℓ m ∧ ℓ' = inw ℓ)

variable (G A C) in
/-- `C` is an execution of AlgAU (with parameter `k`) on `G` under schedule `A`. -/
structure AURun : Prop where
  isRun : IsRun G (algAU k) A C

theorem aURun_run (C0 : V → Turn k) : AURun G A (run G (algAU k) C0 A) := ⟨isRun_run _ _ _ _⟩

namespace AURun

variable (hC : AURun G A C)
include hC

theorem succ_of_mem {t : ℕ} {v : V} (hv : v ∈ A t) :
    C (t + 1) v = δ k (C t v) (signal G (C t) v) := hC.isRun.succ_of_mem hv

theorem succ_of_not_mem {t : ℕ} {v : V} (hv : v ∉ A t) : C (t + 1) v = C t v :=
  hC.isRun.succ_of_not_mem hv

theorem mem_of_ne {t : ℕ} {v : V} (h : C (t + 1) v ≠ C t v) : v ∈ A t := hC.isRun.mem_of_ne h

theorem eq_of_not_mem {t t' : ℕ} {v : V} (htt' : t ≤ t')
    (h : ∀ s, t ≤ s → s < t' → v ∉ A s) : C t' v = C t v := hC.isRun.eq_of_not_mem htt' h

open Classical in
theorem succ_eq (t : ℕ) (v : V) :
    C (t + 1) v = if v ∈ A t then δ k (C t v) (signal G (C t) v) else C t v := by
  split_ifs with h
  · exact hC.succ_of_mem h
  · exact hC.succ_of_not_mem h

open Classical in
/-- The transitions of a node. -/
theorem step_cases (t : ℕ) (v : V) :
    C (t + 1) v = C t v ∨
    (v ∈ A t ∧ (C t v).faulty = false ∧ AAN G C t v ∧ (C (t + 1) v).lvl = fwd k (C t v).lvl ∧
      (C (t + 1) v).faulty = false) ∨
    (v ∈ A t ∧ (C t v).faulty = false ∧ AFN G C t v ∧ (C (t + 1) v).lvl = (C t v).lvl ∧
      (C (t + 1) v).faulty = true) ∨
    (v ∈ A t ∧ (C t v).faulty = true ∧ FAN G C t v ∧ (C (t + 1) v).lvl = inw (C t v).lvl ∧
      (C (t + 1) v).faulty = false) := by
  rw [hC.succ_eq t v]
  by_cases hv : v ∈ A t
  · simp only [hv, ite_true, true_and]
    unfold δ
    by_cases hf : (C t v).faulty = true
    · simp only [hf, dite_true]
      by_cases h : FACond (C t v) (signal G (C t) v)
      · simp only [h, ite_true]
        right; right; right
        exact ⟨by simp, faCond_signal_iff.1 h, rfl, rfl⟩
      · simp [h]
    · have hf' : (C t v).faulty = false := by simpa using hf
      simp only [hf]
      by_cases h : AACond (C t v) (signal G (C t) v)
      · simp only [h, ite_true]
        right; left
        exact ⟨by simp, (aaCond_signal_iff.1 h).2, rfl, rfl⟩
      · simp only [h, ite_false]
        by_cases h' : AFCond (C t v) (signal G (C t) v)
        · simp only [h', dite_true]
          right; right; left
          exact ⟨by simp, (afCond_signal_iff hf').1 h', rfl, rfl⟩
        · simp [h']
  · simp [hv]

theorem succ_fa {t : ℕ} {v : V} (hv : v ∈ A t) (hf : (C t v).faulty = true)
    (h : FAN G C t v) :
    (C (t + 1) v).lvl = inw (C t v).lvl ∧ (C (t + 1) v).faulty = false := by
  rw [hC.succ_of_mem hv]
  unfold δ
  simp only [hf, dite_true, faCond_signal_iff.2 h, ite_true]
  exact ⟨rfl, rfl⟩

theorem succ_aa {t : ℕ} {v : V} (hv : v ∈ A t) (hf : (C t v).faulty = false)
    (h : AAN G C t v) :
    (C (t + 1) v).lvl = fwd k (C t v).lvl ∧ (C (t + 1) v).faulty = false := by
  rw [hC.succ_of_mem hv]
  unfold δ
  simp only [hf, Bool.false_eq_true, dite_false, aaCond_signal_iff.2 ⟨hf, h⟩, ite_true]
  exact ⟨rfl, rfl⟩

omit hC in
theorem not_aan_of_afn {t : ℕ} {v : V} (h : AFN G C t v) : ¬ AAN G C t v := by
  intro h'
  rcases h.2 with h2 | ⟨u, hu, h2, -⟩
  · apply h2; intro u hu
    rcases (h' u hu).2 with h3 | h3
    · exact Or.inl h3.symm
    · exact Or.inr (Or.inr h3)
  · simp [(h' u hu).1] at h2

theorem succ_af {t : ℕ} {v : V} (hv : v ∈ A t) (hf : (C t v).faulty = false)
    (h : AFN G C t v) :
    (C (t + 1) v).lvl = (C t v).lvl ∧ (C (t + 1) v).faulty = true := by
  rw [hC.succ_of_mem hv]
  have h1 : ¬ AACond (C t v) (signal G (C t) v) := fun h' =>
    not_aan_of_afn h (aaCond_signal_iff.1 h').2
  unfold δ
  simp only [hf, Bool.false_eq_true, dite_false, h1, ite_false, (afCond_signal_iff hf).2 h,
    dite_true]
  exact ⟨rfl, rfl⟩

/-- A faulty node only leaves its turn by an FA transition. -/
theorem faulty_cases {t : ℕ} {v : V} (hf : (C t v).faulty = true) :
    C (t + 1) v = C t v ∨ (v ∈ A t ∧ FAN G C t v ∧ (C (t + 1) v).lvl = inw (C t v).lvl ∧
      (C (t + 1) v).faulty = false) := by
  rcases hC.step_cases t v with h | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h1, -, h2, h3, h4⟩
  · exact Or.inl h
  · simp [hf] at h
  · simp [hf] at h
  · exact Or.inr ⟨h1, h2, h3, h4⟩

/-- The move of `v` relative to a neighbour `u`. -/
theorem moveRel {t : ℕ} {v u : V} (h : G.Adj v u) :
    MoveRel k (C t v).lvl (C (t + 1) v).lvl (C t v).faulty (C t u).lvl (C t u).faulty := by
  rcases hC.step_cases t v with h1 | ⟨-, h1, h2, h3, -⟩ | ⟨-, -, -, h3, -⟩ | ⟨-, h1, h2, h3, -⟩
  · left; rw [h1]
  · right; left; exact ⟨h1, (h2 u h).1, (h2 u h).2, h3⟩
  · left; exact h3
  · right; right; exact ⟨h1, h2 u h, h3⟩


end AURun

end ThinUnison
