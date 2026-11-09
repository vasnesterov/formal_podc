import Papers.PODC2024.FairOrderingSocialChoice.Batches

/-!
# Lemma 3.8: the Themis example

Lemma 3.8 of [Ramseyer–Goel]: in Themis, even if all replicas report `τ` before `τ'`, there are no
faulty replicas and no cycles of `γ`-ordering dependencies for any `γ > 1/2`, the output may put
`τ'` before `τ`.

We do not model the Themis protocol. We formalize the example of the paper's proof and Themis's
dependency rule as the proof paraphrases it: with `w(τ, τ')` the number of votes for `τ ≺ τ'`,
a dependency `(τ, τ')` is included if (1) `w(τ, τ') ≥ w(τ', τ)` and
(2) `w(τ, τ') ≥ n(1 - γ) + f + 1`, ties in (1) being broken arbitrarily (`ThemisDeps`).
Inside a strongly connected component Themis walks along a Hamiltonian cycle.

The example: `n = 2g` replicas, `f = 0`; `g` replicas receive `τ₁ ≺ τ₂ ≺ τ₃`, the other `g`
receive `τ₃ ≺ τ₁ ≺ τ₂` (transactions `0, 1, 2 : Fin 3`). Then `w(τ₁, τ₂) = 2g` and all other pairs
are tied at `g`, so the cycle `τ₁ → τ₂ → τ₃ → τ₁` is a valid choice of dependencies **provided
`g ≥ n(1 - γ) + 1`, i.e. `γ ≥ 1/2 + 1/n`** (`cycleDeps_iff`). The paper's justification of (2)
via "`(1 - γ) + (f + 1)/n ≤ (1 - γ) + 2f/n`" fails for `f = 0` (`paper_step_false`); e.g. for
`n = 4`, `γ = 3/5` the cycle is not a valid dependency set. This is harmless: the lemma only
needs some `n`, and for every `γ > 1/2` a large enough `n` works (`lemma_3_8_exists`).
-/

namespace Podc.FairOrderingSocialChoice

open Cslib.SocialChoice Finset Relation

variable {ι X : Type*} [Fintype ι]

/-- Themis's dependency rule (as paraphrased in the proof of Lemma 3.8), with `f` faulty replicas
tolerated: every chosen dependency `(x, y)` has (1) a weak majority and (2) at least
`n(1 - γ) + f + 1` votes; no pair is chosen in both directions; and every pair meeting (1) and (2)
is chosen in at least one direction (ties are broken arbitrarily). -/
structure ThemisDeps (σ : Profile ι X) (γ f : ℝ) (D : X → X → Prop) : Prop where
  sound : ∀ x y, D x y → x ≠ y ∧ count σ y x ≤ count σ x y ∧
    Fintype.card ι * (1 - γ) + f + 1 ≤ count σ x y
  antisymm : ∀ x y, D x y → ¬ D y x
  complete : ∀ x y, x ≠ y → count σ y x ≤ count σ x y →
    Fintype.card ι * (1 - γ) + f + 1 ≤ count σ x y → D x y ∨ D y x

namespace Themis

/-- Ranks of `τ₁ τ₂ τ₃` in group one (`τ₁ ≺ τ₂ ≺ τ₃`) and group two (`τ₃ ≺ τ₁ ≺ τ₂`). -/
def rk : Fin g ⊕ Fin g → Fin 3 → ℕ
  | .inl _ => ![0, 1, 2]
  | .inr _ => ![1, 2, 0]

/-- The profile of the example: `n = 2g` replicas in two groups of `g`. -/
noncomputable def T (g : ℕ) : Profile (Fin g ⊕ Fin g) (Fin 3) := fun i => Pref.ofRank (rk i)

/-- The dependency cycle `τ₁ → τ₂ → τ₃ → τ₁`. -/
def D (x y : Fin 3) : Prop := (x, y) ∈ ({(0, 1), (1, 2), (2, 0)} : Finset (Fin 3 × Fin 3))

instance : DecidableRel D := fun _ _ => by unfold D; infer_instance

/-- A possible output of Themis: `τ₂ ≺ τ₃ ≺ τ₁`. -/
noncomputable def out : Pref (Fin 3) := Pref.ofRank ![2, 0, 1]

theorem card_eq (g : ℕ) : Fintype.card (Fin g ⊕ Fin g) = 2 * g := by simp; ring

/-- The vote counts: `w(τ₁, τ₂) = 2g`, `w(τ₂, τ₁) = 0`, and all other pairs `g : g`. -/
theorem count_T {g : ℕ} (x y : Fin 3) :
    count (T g) x y = g * ((if (![0, 1, 2] : Fin 3 → ℕ) x < (![0, 1, 2] : Fin 3 → ℕ) y then 1 else 0)
      + (if (![1, 2, 0] : Fin 3 → ℕ) x < (![1, 2, 0] : Fin 3 → ℕ) y then 1 else 0)) := by
  by_cases hxy : x = y
  · subst hxy; unfold count; simp [(T g _).irrefl]
  have hr : ∀ x y : Fin 3, x ≠ y →
      (![0, 1, 2] : Fin 3 → ℕ) x ≠ ![0, 1, 2] y ∧ (![1, 2, 0] : Fin 3 → ℕ) x ≠ ![1, 2, 0] y := by
    decide
  change count (fun i => Pref.ofRank (rk i)) x y = _
  rw [count_ofRank rk fun i => by
      cases i
      · exact (hr x y hxy).1
      · exact (hr x y hxy).2, card_filter, Fintype.sum_sum_type]
  simp only [rk]
  by_cases h1 : (![0, 1, 2] : Fin 3 → ℕ) x < ![0, 1, 2] y <;>
    by_cases h2 : (![1, 2, 0] : Fin 3 → ℕ) x < ![1, 2, 0] y <;> simp [h1, h2, mul_two]

theorem count_01 {g : ℕ} : count (T g) 0 1 = 2 * g := by rw [count_T]; simp; ring
theorem count_10 {g : ℕ} : count (T g) 1 0 = 0 := by rw [count_T]; simp
theorem count_tie {g : ℕ} {x y : Fin 3} (h : x ≠ y) (h' : ¬ (x = 0 ∧ y = 1)) (h'' : ¬ (x = 1 ∧ y = 0)) :
    count (T g) x y = g := by
  have key : ((if (![0, 1, 2] : Fin 3 → ℕ) x < (![0, 1, 2] : Fin 3 → ℕ) y then 1 else 0)
      + (if (![1, 2, 0] : Fin 3 → ℕ) x < (![1, 2, 0] : Fin 3 → ℕ) y then 1 else 0)) = 1 := by
    revert x y; decide
  rw [count_T, key, mul_one]

/-- In the example, for `1/2 < γ ≤ 1`, the only pair received in order by `γ n` replicas is
`(τ₁, τ₂)`. -/
theorem atLeast_iff {g : ℕ} (hg : 1 ≤ g) {γ : ℝ} (h1 : 1 / 2 < γ) (h2 : γ ≤ 1) (x y : Fin 3) :
    AtLeast (T g) γ x y ↔ x = 0 ∧ y = 1 := by
  unfold AtLeast
  rw [card_eq]
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  constructor
  · intro h
    by_contra hc
    by_cases hxy : x = y
    · subst hxy
      have : count (T g) x x = 0 := by unfold count; simp [(T g _).irrefl]
      rw [this] at h; push_cast at h; nlinarith
    by_cases h10 : x = 1 ∧ y = 0
    · obtain ⟨rfl, rfl⟩ := h10; rw [count_10] at h; push_cast at h; nlinarith
    rw [count_tie hxy hc h10] at h; push_cast at h; nlinarith
  · rintro ⟨rfl, rfl⟩; rw [count_01]; push_cast; nlinarith

theorem cycleDeps_iff {g : ℕ} (hg : 1 ≤ g) (γ : ℝ) :
    ThemisDeps (T g) γ 0 D ↔ 1 / 2 + 1 / (2 * g) ≤ γ := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have key : 1 / 2 + 1 / (2 * g) ≤ γ ↔ (2 * g : ℝ) * (1 - γ) + 0 + 1 ≤ g := by
    rw [div_add_div _ _ (by norm_num) (by positivity), div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [key]
  constructor
  · intro h
    have := (h.sound 1 2 (by decide)).2.2
    rwa [count_tie (by decide) (by decide) (by decide), card_eq, Nat.cast_mul,
      Nat.cast_ofNat] at this
  · intro h
    have h01 : (2 * g : ℝ) * (1 - γ) + 0 + 1 ≤ (2 * g : ℕ) := by push_cast; linarith
    refine ⟨fun x y hxy => ?_, fun x y hxy => by revert x y; decide, fun x y hxy _ _ => ?_⟩
    · rw [card_eq, Nat.cast_mul, Nat.cast_ofNat]
      have hD : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 0) := by revert x y; decide
      rcases hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [count_01, count_10]; exact ⟨by decide, by omega, h01⟩
      · rw [count_tie (by decide) (by decide) (by decide),
          count_tie (by decide) (by decide) (by decide)]
        exact ⟨by decide, le_rfl, h⟩
      · rw [count_tie (by decide) (by decide) (by decide),
          count_tie (by decide) (by decide) (by decide)]
        exact ⟨by decide, le_rfl, h⟩
    · have hc : ∀ x y : Fin 3, x ≠ y → D x y ∨ D y x := by decide
      exact hc x y hxy

end Themis

open Themis in
/-- **Lemma 3.8** of [Ramseyer–Goel] (the example of its proof). With `n = 2g` honest replicas
(`f = 0`), half receiving `τ₁ ≺ τ₂ ≺ τ₃` and half `τ₃ ≺ τ₁ ≺ τ₂`, and any
`γ ≥ 1/2 + 1/n`:
* every replica reports `τ₁` before `τ₂`;
* the `γ`-ordering-dependency graph (Definition 3.1) has no cycle;
* the cycle `τ₁ → τ₂ → τ₃ → τ₁` is a valid choice of Themis dependencies, and it is strongly
  connected;
* the output `τ₂ ≺ τ₃ ≺ τ₁` walks along this Hamiltonian cycle, and puts `τ₂` before `τ₁`. -/
theorem lemma_3_8 {g : ℕ} (hg : 1 ≤ g) {γ : ℝ} (hγ : 1 / 2 + 1 / (2 * g) ≤ γ) :
    (∀ i, (T g i).P 0 1) ∧
    (∀ x, ¬ TransGen (AtLeast (T g) γ) x x) ∧
    ThemisDeps (T g) γ 0 D ∧ (∀ x y, TransGen D x y) ∧
    (out.P 1 2 ∧ D 1 2) ∧ (out.P 2 0 ∧ D 2 0) ∧ out.P 1 0 := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hγ1 : 1 / 2 < γ := lt_of_lt_of_le (by simp; positivity) hγ
  refine ⟨fun i => Pref.ofRank_P_of_lt (by cases i <;> simp [rk]), ?_, (cycleDeps_iff hg γ).2 hγ,
    ?_, ⟨Pref.ofRank_P_of_lt (by decide), by decide⟩,
    ⟨Pref.ofRank_P_of_lt (by decide), by decide⟩, Pref.ofRank_P_of_lt (by decide)⟩
  · -- every `γ`-edge is `(τ₁, τ₂)` (for `γ > 1` there are none), so there is no cycle
    have hE : ∀ x y, AtLeast (T g) γ x y → x = 0 ∧ y = 1 := by
      intro x y h
      rcases le_or_gt γ 1 with h2 | h2
      · exact (atLeast_iff hg hγ1 h2 x y).1 h
      · exfalso
        have := count_le (T g) x y
        unfold AtLeast at h; rw [card_eq] at h this
        have : (count (T g) x y : ℝ) ≤ 2 * g := by exact_mod_cast this
        push_cast at h; nlinarith
    have hpath : ∀ x y, TransGen (AtLeast (T g) γ) x y → x = 0 ∧ y = 1 := by
      intro x y h
      induction h with
      | single h => exact hE _ _ h
      | tail _ h ih => exact absurd ((hE _ _ h).1.symm.trans ih.2) (by decide)
    intro x h
    obtain ⟨h1, h2⟩ := hpath x x h
    exact absurd (h1.symm.trans h2) (by decide)
  · have h01 : TransGen D 0 1 := .single (by decide)
    have h12 : TransGen D 1 2 := .single (by decide)
    have h20 : TransGen D 2 0 := .single (by decide)
    intro x y
    fin_cases x <;> fin_cases y
    all_goals first
      | exact h01 | exact h12 | exact h20 | exact h01.trans h12 | exact h12.trans h20
      | exact h20.trans h01 | exact h01.trans (h12.trans h20) | exact h12.trans (h20.trans h01)
      | exact h20.trans (h01.trans h12)

/-- For every `γ > 1/2`, the example of Lemma 3.8 works with `g` large enough. -/
theorem lemma_3_8_exists {γ : ℝ} (hγ : 1 / 2 < γ) :
    ∃ g : ℕ, 1 ≤ g ∧ (∀ x, ¬ TransGen (AtLeast (Themis.T g) γ) x x) ∧
      ThemisDeps (Themis.T g) γ 0 Themis.D ∧ Themis.out.P 1 0 ∧ ∀ i, (Themis.T g i).P 0 1 := by
  obtain ⟨g, hg⟩ := exists_nat_gt (1 / (2 * γ - 1))
  have hpos : 0 < 2 * γ - 1 := by linarith
  have hg0 : (0 : ℝ) < g := lt_trans (by positivity) hg
  have hg1 : 1 ≤ g := by exact_mod_cast hg0
  have : 1 / 2 + 1 / (2 * (g : ℝ)) ≤ γ := by
    rw [div_lt_iff₀ hpos] at hg
    rw [div_add_div _ _ (by norm_num) (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨h1, h2, h3, -, -, -, h4⟩ := lemma_3_8 hg1 this
  exact ⟨g, hg1, h2, h3, h4, h1⟩

/-- The step "`(1 - γ) + (f + 1)/n ≤ (1 - γ) + 2f/n`" in the proof of Lemma 3.8 fails for `f = 0`. -/
theorem paper_step_false {n : ℕ} (hn : 0 < n) (γ : ℝ) :
    ¬ ((1 - γ) + ((0 : ℝ) + 1) / n ≤ (1 - γ) + 2 * 0 / n) := by
  simp; positivity

/-- Consequently the cycle needs `γ ≥ 1/2 + 1/n`: for `n = 4` (`g = 2`) and `γ = 3/5 > 1/2` it is not
a valid set of Themis dependencies (`τ₂ ≺ τ₃` has `2 < n(1 - γ) + 1 = 2.6` votes). -/
theorem cycleDeps_fails_small_n : ¬ ThemisDeps (Themis.T 2) (3 / 5) 0 Themis.D := by
  rw [Themis.cycleDeps_iff (by norm_num)]; norm_num

end Podc.FairOrderingSocialChoice
