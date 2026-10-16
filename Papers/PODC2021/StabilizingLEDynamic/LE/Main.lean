import Papers.PODC2021.StabilizingLEDynamic.LE.Stable

/-!
# Algorithm `LE`: Theorem 6, Corollary 6, Theorem 7
-/

namespace StabilizingLEDynamic.LE

open Classical Cslib.HeardOf

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ}

/-- A sequence of naturals that is monotone from index `1` on and bounded is eventually
constant. -/
theorem eventually_const_of_bdd (f : ℕ → ℕ) (hmono : ∀ t u, 1 ≤ t → t ≤ u → f t ≤ f u)
    (B : ℕ) (hB : ∀ t ≥ 1, f t ≤ B) : ∃ T ≥ 1, ∀ t ≥ T, f t = f T := by
  set S := f '' {t | 1 ≤ t}
  have hne : S.Nonempty := ⟨f 1, 1, show 1 ≤ 1 from le_rfl, rfl⟩
  have hbdd : BddAbove S := ⟨B, by rintro _ ⟨t, ht, rfl⟩; exact hB t ht⟩
  obtain ⟨T, hT, hTeq⟩ := Nat.sSup_mem hne hbdd
  refine ⟨T, hT, fun t ht => le_antisymm ?_ (hmono T t hT ht)⟩
  rw [hTeq]
  have h1 : 1 ≤ t := le_trans hT ht
  exact le_csSup hbdd ⟨t, h1, rfl⟩

theorem tsource_of_J1sB {V : Finset ι} {G : DG ι} (hG : G ∈ J1sB Δ V) :
    ∃ r, TSource G V (Δ := Δ) r := by
  obtain ⟨-, r, hr, h⟩ := hG
  exact ⟨r, hr, h⟩

/-- **Theorem 6.** In every execution of `LE` in a dynamic graph of `J^B_{1,*}(Δ)`, there is a
time `T ≥ 1` (the paper's Remark 5) and a process `ℓ` such that from time `T + 4Δ` on, every
process elects `ℓ`. As in the paper, `ℓ` is the smallest identifier among the processes whose
suspicion value is eventually constant and minimum: from time `T` on, the suspicion value of `ℓ`
is constant, and every process has a larger suspicion value, or an equal one and a larger
identifier. -/
theorem theorem_6 (hΔ : 1 ≤ Δ) {V : Finset ι} {G : DG ι} (hG : G ∈ J1sB Δ V)
    (γ : ι → St ι Δ) : ∃ T ≥ 1, ∃ ℓ ∈ V,
      (∀ t ≥ T, ∀ p ∈ V, susp G γ t ℓ = susp G γ T ℓ ∧ susp G γ t ℓ ≤ susp G γ t p ∧
        (susp G γ t p = susp G γ t ℓ → ℓ ≤ p)) ∧
      ∀ t ≥ T + 4 * Δ, ∀ q ∈ V, (algLE Δ).lid q (X G γ t q) = ℓ := by
  have hdg : IsDG V G := hG.1
  obtain ⟨r, hr⟩ := tsource_of_J1sB hG
  -- `♢Const`
  set C := V.filter fun p => ∃ T, ConstFrom G γ p T
  have hrC : r ∈ C := Finset.mem_filter.mpr ⟨hr.1, 2 * Δ, by omega,
    fun t ht => lemma_10 hΔ hdg hr ht⟩
  have hCne : C.Nonempty := ⟨r, hrC⟩
  set Tc : ι → ℕ := fun p => if h : ∃ T, ConstFrom G γ p T then h.choose else 0
  have hTc : ∀ p ∈ C, ConstFrom G γ p (Tc p) := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    simp only [Tc, dif_pos h]; exact h.choose_spec
  set fin : ι → ℕ := fun p => susp G γ (Tc p) p
  set m := C.inf' hCne fin
  -- processes outside `♢Const` eventually exceed `m`
  have hunb : ∀ p ∈ V, p ∉ C → ∃ t ≥ 1, m < susp G γ t p := by
    intro p hp hpC
    by_contra hcon
    push Not at hcon
    obtain ⟨T, hT, hconst⟩ := eventually_const_of_bdd (fun t => susp G γ t p)
      (fun t u ht htu => susp_mono hΔ ht htu p) m hcon
    exact hpC (Finset.mem_filter.mpr ⟨hp, T, hT, hconst⟩)
  set g : ι → ℕ := fun p => if p ∈ C then Tc p else
    if h : ∃ t ≥ 1, m < susp G γ t p then h.choose else 0
  set T := V.sup g + 1
  have hgT : ∀ p ∈ V, g p < T := fun p hp => Nat.lt_succ_of_le (Finset.le_sup (f := g) hp)
  have hC : ∀ p ∈ C, ∀ t ≥ T, susp G γ t p = fin p := by
    intro p hp t ht
    have hpV := (Finset.mem_filter.mp hp).1
    have := hgT p hpV
    simp only [g, if_pos hp] at this
    exact (hTc p hp).2 t (by omega)
  have hnC : ∀ p ∈ V, p ∉ C → m < susp G γ T p := by
    intro p hp hpC
    have h := hunb p hp hpC
    have := hgT p hp
    simp only [g, if_neg hpC, dif_pos h] at this
    exact lt_of_lt_of_le h.choose_spec.2 (susp_mono hΔ h.choose_spec.1 (by omega) p)
  obtain ⟨ℓ0, hℓ0C, hℓ0m⟩ := Finset.exists_mem_eq_inf' hCne fin
  have hFne : (C.filter fun p => fin p = m).Nonempty :=
    ⟨ℓ0, Finset.mem_filter.mpr ⟨hℓ0C, hℓ0m.symm⟩⟩
  set ℓ := (C.filter fun p => fin p = m).min' hFne
  have hℓF := Finset.min'_mem _ hFne
  rw [Finset.mem_filter] at hℓF
  refine ⟨T, by omega, ℓ, (Finset.mem_filter.mp hℓF.1).1, fun t ht p hp => ?_,
    fun t ht q hq => ?_⟩
  · have hℓt : susp G γ t ℓ = m := (hC ℓ hℓF.1 t ht).trans hℓF.2
    have hℓT : susp G γ T ℓ = m := (hC ℓ hℓF.1 T le_rfl).trans hℓF.2
    refine ⟨hℓt.trans hℓT.symm, ?_⟩
    rw [hℓt]
    by_cases hpC : p ∈ C
    · rw [hC p hpC t ht]
      exact ⟨Finset.inf'_le _ hpC,
        fun hpm => Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hpC, hpm⟩)⟩
    · have h1 := hnC p hp hpC
      have h2 := susp_mono hΔ (G := G) (γ := γ) (show 1 ≤ T by omega) ht p
      exact ⟨by omega, fun h => by omega⟩
  exact theorem_6_core hΔ hdg hr (by omega) (Finset.filter_subset _ _) fin hC
    (fun p hp => Finset.inf'_le _ hp) hnC hℓF.1 hℓF.2
    (fun p hp hpm => Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hp, hpm⟩)) ht hq

/-- **Corollary 6** (Theorem 4.1 of the PODC version, first part). Algorithm `LE` is a
deterministic pseudo-stabilizing leader election algorithm for `J^B_{1,*}(Δ)`, for every number
of processes. -/
theorem corollary_6 (hΔ : 1 ≤ Δ) (n : ℕ) : PseudoStab (algLE (ι := ι) Δ) (J1sB Δ) n := by
  intro V _ G hG γ
  obtain ⟨T, -, ℓ, hℓ, -, h⟩ := theorem_6 hΔ hG γ
  exact ⟨T + 4 * Δ, ℓ, hℓ, fun t q hq => h _ (by omega) q hq⟩

/-- **Theorem 7** (sharp form). In `J^B_{*,*}(Δ)`, `SP_LE` holds for Algorithm `LE` from the
configuration `γ_{6Δ+1}` (0-indexed time `6Δ`) on, for systems of `n ≥ 1` processes. -/
theorem theorem_7_sharp (hΔ : 1 ≤ Δ) {n : ℕ} (hn : 1 ≤ n) :
    PseudoStabWithin (algLE (ι := ι) Δ) (JssB Δ) n (6 * Δ) := by
  intro V hV G hG γ
  obtain ⟨r, hr⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  have hdg : IsDG V G := hG.1
  have hall : ∀ p ∈ V, TSource G V (Δ := Δ) p := fun p hp => ⟨hp, fun q hq => hG.2 p hp q hq⟩
  set fin : ι → ℕ := fun p => susp G γ (2 * Δ) p
  have hVne : V.Nonempty := ⟨r, hr⟩
  set m := V.inf' hVne fin
  obtain ⟨ℓ0, hℓ0V, hℓ0m⟩ := Finset.exists_mem_eq_inf' hVne fin
  have hFne : (V.filter fun p => fin p = m).Nonempty :=
    ⟨ℓ0, Finset.mem_filter.mpr ⟨hℓ0V, hℓ0m.symm⟩⟩
  set ℓ := (V.filter fun p => fin p = m).min' hFne
  have hℓF := Finset.min'_mem _ hFne
  rw [Finset.mem_filter] at hℓF
  refine ⟨ℓ, hℓF.1, fun t q hq => ?_⟩
  exact theorem_6_core hΔ hdg (hall r hr) (T := 2 * Δ) (by omega) le_rfl fin
    (fun p hp t ht => lemma_10 hΔ hdg (hall p hp) ht) (fun p hp => Finset.inf'_le _ hp)
    (fun p hp hpC => absurd hp hpC) hℓF.1 hℓF.2
    (fun p hp hpm => Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hp, hpm⟩)) (by omega) hq

/-- **Theorem 7** (Theorem 4.1 of the PODC version, second part). The pseudo-stabilization time
of Algorithm `LE` in `J^B_{*,*}(Δ)` is at most `6Δ + 2` rounds: `SP_LE` holds from the paper's
configuration `γ_{6Δ+2}` (0-indexed time `6Δ + 1`) on. -/
theorem theorem_7 (hΔ : 1 ≤ Δ) {n : ℕ} (hn : 1 ≤ n) :
    PseudoStabWithin (algLE (ι := ι) Δ) (JssB Δ) n (6 * Δ + 1) := by
  intro V hV G hG γ
  have := (theorem_7_sharp hΔ hn V hV G hG γ).shift 1
  simpa only [Nat.add_assoc, Nat.add_comm 1] using this

end StabilizingLEDynamic.LE
