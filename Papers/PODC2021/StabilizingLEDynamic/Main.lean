import Papers.PODC2021.StabilizingLEDynamic.Classes
import Papers.PODC2021.StabilizingLEDynamic.Impossibility
import Papers.PODC2021.StabilizingLEDynamic.Counterexample
import Papers.PODC2021.StabilizingLEDynamic.LE.Main

/-!
# Main results: Corollaries 1–3 and the summary of Figure 1

Altisen, Devismes, Durand, Johnen, Petit, *On Implementing Stabilizing Leader Election with Weak
Assumptions on Network Dynamics*, PODC 2021 (journal version: HAL hal-03346225).
-/

namespace StabilizingLEDynamic

variable {ι σ : Type*}

theorem PseudoStab.mono_card {A : Algorithm ι σ} {C C' : DGClass ι} {n : ℕ}
    (h : PseudoStab A C n) (hC : ∀ V : Finset ι, V.card = n → C' V ⊆ C V) :
    PseudoStab A C' n :=
  fun V hV G hG => h V hV G (hC V hV hG)

theorem SelfStab.mono_card {A : Algorithm ι σ} {C C' : DGClass ι} {n : ℕ}
    (h : SelfStab A C n) (hC : ∀ V : Finset ι, V.card = n → C' V ⊆ C V) :
    SelfStab A C' n := by
  intro V hV
  obtain ⟨L, h1, h2⟩ := h V hV
  exact ⟨L, fun G hG => h1 G (hC V hV hG), fun G hG => h2 G (hC V hV hG)⟩

/-- Class inclusions (Figure 2) for systems of `n ≥ 1` processes. -/
theorem J_mono_card {n : ℕ} (hn : 1 ≤ n) {k k' : Kind} {τ τ' : Timeliness} {Δ : ℕ}
    (hk : k ≤ k') (hτ : τ ≤ τ') : ∀ V : Finset ι, V.card = n → J k τ Δ V ⊆ J k' τ' Δ V :=
  fun V hV => J_mono (Finset.card_pos.mp (by omega)) hk hτ

theorem selfStab_pseudoStab_J {A : Algorithm ι σ} {k : Kind} {τ : Timeliness} {Δ n : ℕ}
    (h : SelfStab A (J k τ Δ) n) : PseudoStab A (J k τ Δ) n :=
  h.pseudoStab fun _ _ hG i => J_shift hG i

/-- `J^B ⊆ J^Q ⊆ J` (same kind) and `J_{*,*} ⊆ J_{1,*}, J_{*,1}`, as needed below. -/
theorem J_sub (Δ : ℕ) {n : ℕ} (hn : 1 ≤ n) {k k' : Kind} {τ τ' : Timeliness}
    (hk : k ≤ k') (hτ : τ ≤ τ') (V : Finset ι) (hV : V.card = n) : J k τ Δ V ⊆ J k' τ' Δ V :=
  J_mono_card hn hk hτ V hV

/-- **Corollary 1** (Corollary 3.4 of the PODC version). No deterministic self-stabilizing leader
election algorithm for `J^Q_{1,*}(Δ)` nor for `J_{1,*}` (`n ≥ 2` processes). -/
theorem corollary_1 [Infinite ι] [Nonempty σ] (A : Algorithm ι σ) {Δ n : ℕ} (hΔ : 1 ≤ Δ)
    (h2 : 2 ≤ n) : ¬ SelfStab A (J1sQ Δ) n ∧ ¬ SelfStab A J1s n := by
  constructor
  · intro h
    exact theorem_2 A hΔ h2 (h.mono_card (J_sub (k := .src) (k' := .src) (τ := .bounded)
      (τ' := .quasi) Δ (by omega) le_rfl (by decide)))
  · intro h
    exact theorem_2 A hΔ h2 (h.mono_card (J_sub (k := .src) (k' := .src) (τ := .bounded)
      (τ' := .recur) Δ (by omega) le_rfl (by decide)))

/-- **Corollary 2** (Corollary 3.6 of the PODC version). No deterministic pseudo-stabilizing
leader election algorithm for `J_{1,*}` (`n ≥ 2` processes). -/
theorem corollary_2 [Infinite ι] [Nonempty σ] (A : Algorithm ι σ) {n : ℕ} (h2 : 2 ≤ n) :
    ¬ PseudoStab A J1s n := fun h =>
  theorem_3 A (Δ := 1) le_rfl h2 (h.mono_card (J_sub (k := .src) (k' := .src) (τ := .quasi)
      (τ' := .recur) 1 (by omega) le_rfl (by decide)))

/-- **Corollary 3** (Corollary 3.9 of the PODC version). For `n ≥ 3` processes: no deterministic
pseudo-stabilizing leader election algorithm for `J^Q_{*,1}(Δ)` nor `J_{*,1}`, and no
self-stabilizing one for `J^B_{*,1}(Δ)`, `J^Q_{*,1}(Δ)`, `J_{*,1}`. -/
theorem corollary_3 [Infinite ι] [Nonempty σ] (A : Algorithm ι σ) {Δ n : ℕ} (hΔ : 1 ≤ Δ)
    (h3 : 3 ≤ n) :
    ¬ PseudoStab A (Js1Q Δ) n ∧ ¬ PseudoStab A Js1 n ∧
      ¬ SelfStab A (Js1B Δ) n ∧ ¬ SelfStab A (Js1Q Δ) n ∧ ¬ SelfStab A Js1 n := by
  have hB : ¬ PseudoStab A (Js1B Δ) n := theorem_4 A hΔ h3
  have hQ : ¬ PseudoStab A (Js1Q Δ) n := fun h =>
    hB (h.mono_card (J_sub (k := .snk) (k' := .snk) (τ := .bounded) (τ' := .quasi) Δ
      (by omega) le_rfl (by decide)))
  have hR : ¬ PseudoStab A Js1 n := fun h =>
    hB (h.mono_card (J_sub (k := .snk) (k' := .snk) (τ := .bounded) (τ' := .recur) Δ
      (by omega) le_rfl (by decide)))
  exact ⟨hQ, hR, fun h => hB (selfStab_pseudoStab_J h), fun h => hQ (selfStab_pseudoStab_J h),
    fun h => hR (selfStab_pseudoStab_J h)⟩

/-- **Figure 1** (summary of the results of this paper), for `n ≥ 3` processes, `Δ ≥ 1`, an
infinite identifier domain and any nonempty state type:

* self-stabilizing leader election is impossible in the six classes with a source or a sink
  (`k ≠ all`);
* pseudo-stabilizing leader election is impossible in these classes except `J^B_{1,*}(Δ)`;
* Algorithm `LE` is pseudo-stabilizing in `J^B_{1,*}(Δ)` (hence in `J^B_{*,*}(Δ)`), with
  pseudo-stabilization time at most `6Δ + 2` rounds in `J^B_{*,*}(Δ)`, while no bound exists in
  `J^B_{1,*}(Δ)` (Theorem 5).

(The possibility of self-stabilization in the three classes `J_{*,*}` is from the authors' earlier
paper and is not formalized.) -/
theorem figure_1 [Infinite ι] [LinearOrder ι] [Nonempty σ] {Δ n : ℕ} (hΔ : 1 ≤ Δ) (h3 : 3 ≤ n) :
    (∀ (A : Algorithm ι σ) (k : Kind) (τ : Timeliness), k ≠ .all → ¬ SelfStab A (J k τ Δ) n) ∧
    (∀ (A : Algorithm ι σ) (k : Kind) (τ : Timeliness), k ≠ .all → (k, τ) ≠ (.src, .bounded) →
      ¬ PseudoStab A (J k τ Δ) n) ∧
    PseudoStab (LE.algLE (ι := ι) Δ) (J1sB Δ) n ∧
    PseudoStabWithin (LE.algLE (ι := ι) Δ) (JssB Δ) n (6 * Δ + 1) ∧
    (∀ (A : Algorithm ι σ) (T : ℕ), ¬ PseudoStabWithin A (J1sB Δ) n T) := by
  refine ⟨?_, ?_, LE.corollary_6 hΔ n, LE.theorem_7 hΔ (by omega),
    fun A T => theorem_5 A hΔ (by omega) T⟩
  · intro A k τ hk h
    cases k with
    | all => exact hk rfl
    | src =>
      exact theorem_2 A hΔ (by omega) (h.mono_card (J_sub (k := .src) (k' := .src)
        (τ := .bounded) (τ' := τ) Δ (by omega) le_rfl (by cases τ <;> decide)))
    | snk =>
      exact theorem_4 A hΔ h3 (selfStab_pseudoStab_J (h.mono_card (J_sub (k := .snk)
        (k' := .snk) (τ := .bounded) (τ' := τ) Δ (by omega) le_rfl (by cases τ <;> decide))))
  · intro A k τ hk hkτ h
    cases k with
    | all => exact hk rfl
    | src =>
      cases τ with
      | bounded => exact hkτ rfl
      | quasi => exact theorem_3 A hΔ (by omega) h
      | recur =>
        exact theorem_3 A hΔ (by omega) (h.mono_card (J_sub (k := .src) (k' := .src)
          (τ := .quasi) (τ' := .recur) Δ (by omega) le_rfl (by decide)))
    | snk =>
      exact theorem_4 A hΔ h3 (h.mono_card (J_sub (k := .snk) (k' := .snk) (τ := .bounded)
        (τ' := τ) Δ (by omega) le_rfl (by cases τ <;> decide)))

/-- **Theorem 4 needs `n ≥ 3`.** For systems of exactly two processes, `J^B_{*,1}(Δ)` coincides
with `J^B_{1,*}(Δ)` (`J_src_eq_snk_of_card_two`), so Algorithm `LE` *is* pseudo-stabilizing there.
(The paper's statement quantifies over all system sizes, so it is not contradicted; but the
impossibility for classes with a sink is a phenomenon of `n ≥ 3`.) -/
theorem theorem_4_card_two [LinearOrder ι] {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    PseudoStab (LE.algLE (ι := ι) Δ) (Js1B Δ) 2 :=
  (LE.corollary_6 hΔ 2).mono_card fun _ hV =>
    (J_src_eq_snk_of_card_two hV .bounded Δ).symm.le

end StabilizingLEDynamic
