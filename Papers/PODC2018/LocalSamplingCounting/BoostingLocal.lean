import Papers.PODC2018.LocalSamplingCounting.Boosting
import Papers.PODC2018.LocalSamplingCounting.SSM

/-!
# The boosting lemma (Lemma 4.1) as a statement about local algorithms

`boostAlg G F A t ℓ` is Algorithm `A^×_ε` of Lemma 4.1: node `v` (if free) enumerates the shell
`Γ = B_{t+ℓ}(v) \ (B_t(v) ∪ Λ)` in a fixed order, pins each `vᵢ ∈ Γ` to the value maximizing the
answer of the `t`-local TV-approximate algorithm `A` on the current pinning, and returns the
marginal at `v` computed from the factors inside `B_{t+ℓ}(v)` (Proposition 2.1).

* `boostAlg_isLocal`: if `A` is `t`-local, `boostAlg` is `(2t + ℓ)`-local;
* `lemma_4_1`: if `A` has TV error `ε / (5qn)` (`q = |Σ|`, `n = |V|`, `0 < ε < 1`) and returns
  probability vectors, then `boostAlg` has multiplicative error `ε` on every feasible instance.
-/

set_option linter.unusedSectionVars false

namespace Podc.LocalSamplingCounting

open Finset

open scoped Classical

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Nonempty S]
variable {ι : Type*} [Fintype ι]

/-- The shell `Γ`, enumerated in a fixed order (the paper: increasing IDs). -/
noncomputable def shellList (G : SimpleGraph V) (τ : Pin V S) (v : V) (t ℓ : ℕ) : List V :=
  (univ.filter (· ∈ shell G τ v t ℓ)).toList

/-- **Algorithm `A^×_ε` of Lemma 4.1.** -/
noncomputable def boostAlg (G : SimpleGraph V) (F : ι → Factor V S) (A : Pin V S → V → S → ℝ)
    (t ℓ : ℕ) : Pin V S → V → S → ℝ := fun τ v =>
  if τ v = none then
    marg (gibbsWOn F (ball G v (t + ℓ)))
      (restrictPin (pinSeq A (shellList G τ v t ℓ) τ) (ball G v (t + ℓ))) v
  else fun c => if τ v = some c then 1 else 0

lemma shell_congr {G : SimpleGraph V} {τ τ' : Pin V S} {v : V} {t ℓ : ℕ}
    (h : ∀ u, G.edist v u ≤ ((t + ℓ : ℕ) : ℕ∞) → τ u = τ' u) :
    shell G τ v t ℓ = shell G τ' v t ℓ := by
  ext u
  simp only [shell, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (h u h2) ▸ h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (h u h2).symm ▸ h3⟩

lemma pinSeq_congr {G : SimpleGraph V} {A : Pin V S → V → S → ℝ} {t : ℕ}
    (hA : IsLocalAlg G t A) {v : V} {R : ℕ} :
    ∀ (l : List V), (∀ x ∈ l, G.edist v x + t ≤ R) → ∀ ρ ρ' : Pin V S,
      (∀ u, G.edist v u ≤ R → ρ u = ρ' u) →
      ∀ u, G.edist v u ≤ R → pinSeq A l ρ u = pinSeq A l ρ' u
  | [], _, _, _, h => h
  | x :: l, hl, ρ, ρ', h => by
    have hx : A ρ x = A ρ' x := hA x ρ ρ' fun u hu =>
      h u (le_trans (SimpleGraph.edist_triangle (v := x)) (le_trans (add_le_add le_rfl hu)
        (hl x (by simp))))
    simp only [pinSeq, hx]
    refine pinSeq_congr hA l (fun y hy => hl y (by simp [hy])) _ _ fun u hu => ?_
    by_cases hux : u = x
    · subst hux; simp
    · simp only [Function.update_of_ne hux]; exact h u hu

/-- Algorithm `A^×_ε` is `(2t + ℓ)`-local if `A` is `t`-local. -/
theorem boostAlg_isLocal (G : SimpleGraph V) (F : ι → Factor V S) {A : Pin V S → V → S → ℝ}
    {t : ℕ} (hA : IsLocalAlg G t A) (ℓ : ℕ) : IsLocalAlg G (2 * t + ℓ) (boostAlg G F A t ℓ) := by
  intro v τ τ' h
  have hle : ∀ u, G.edist v u ≤ ((t + ℓ : ℕ) : ℕ∞) → G.edist v u ≤ ((2 * t + ℓ : ℕ) : ℕ∞) :=
    fun u hu => le_trans hu (by exact_mod_cast (by omega : t + ℓ ≤ 2 * t + ℓ))
  have hv : τ v = τ' v := h v (by simp)
  have hsh : shellList G τ v t ℓ = shellList G τ' v t ℓ := by
    unfold shellList; rw [shell_congr fun u hu => h u (hle u hu)]
  unfold boostAlg
  rw [hv, hsh]
  split_ifs
  · congr 1
    refine restrictPin_congr fun u (hu : G.edist v u ≤ ((t + ℓ : ℕ) : ℕ∞)) => ?_
    refine pinSeq_congr hA _ (fun x hx => ?_) τ τ' h u (hle u hu)
    have hx' : x ∈ shell G τ' v t ℓ := by
      simpa [shellList] using hx
    calc G.edist v x + t ≤ ((t + ℓ : ℕ) : ℕ∞) + t := add_le_add hx'.2.1 le_rfl
      _ = ((2 * t + ℓ : ℕ) : ℕ∞) := by push_cast; ring
  · rfl

lemma pinSeq_ne_none (A : Pin V S → V → S → ℝ) {u : V} :
    ∀ (l : List V) (ρ : Pin V S), ρ u ≠ none → pinSeq A l ρ u ≠ none
  | [], _, h => h
  | x :: l, ρ, h => pinSeq_ne_none A l _ (by
      by_cases hux : u = x
      · subst hux; simp
      · rwa [Function.update_of_ne hux])

lemma pinSeq_ne_none_of_mem (A : Pin V S → V → S → ℝ) {u : V} :
    ∀ (l : List V) (ρ : Pin V S), u ∈ l → pinSeq A l ρ u ≠ none
  | [], _, h => by simp at h
  | x :: l, ρ, h => by
    by_cases hux : u = x
    · subst hux; exact pinSeq_ne_none A l _ (by simp)
    · exact pinSeq_ne_none_of_mem A l _ (by simpa [hux] using h)

lemma marg_of_pinned {w : (V → S) → ℝ} {τ : Pin V S} (hτ : Feasible w τ) {v : V} {c₀ : S}
    (hv : τ v = some c₀) (c : S) : marg w τ v c = if c₀ = c then 1 else 0 := by
  unfold marg margNum
  split_ifs with hc
  · subst hc
    rw [show (∑ σ, if Cons σ τ ∧ σ v = c₀ then w σ else 0) = Z w τ from
      sum_congr rfl fun σ _ => by
        by_cases h : Cons σ τ
        · simp [h, h v c₀ hv]
        · simp [h]]
    exact div_self hτ.ne'
  · rw [sum_eq_zero fun σ _ => by
      rw [if_neg]; rintro ⟨h1, h2⟩; exact hc ((h1 v c₀ hv).symm.trans h2), zero_div]

/-- **Lemma 4.1 (boosting lemma).** Let the Gibbs distribution have constraints of diameter
`≤ ℓ`, and let `A` be a `t`-local algorithm returning probability vectors with total variation
error `ε / (5qn)` on feasible instances (`q = |Σ|`, `n = |V|`, `0 < ε < 1`). Then Algorithm
`A^×_ε = boostAlg` is `(2t + ℓ)`-local and returns, on every feasible instance, marginals with
multiplicative error at most `ε`. -/
theorem lemma_4_1 {G : SimpleGraph V} {F : ι → Factor V S} {ℓ : ℕ} (hℓ : GibbsLocal G F ℓ)
    {A : Pin V S → V → S → ℝ} {t : ℕ} (hA : IsLocalAlg G t A) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1)
    (hacc : ∀ ρ u, Feasible (gibbsW F) ρ → ∑ c, A ρ u c = 1 ∧
      tv (A ρ u) (marg (gibbsW F) ρ u) ≤ ε / (5 * Fintype.card S * Fintype.card V)) :
    IsLocalAlg G (2 * t + ℓ) (boostAlg G F A t ℓ) ∧
    ∀ τ v, Feasible (gibbsW F) τ →
      MultClose (boostAlg G F A t ℓ τ v) (marg (gibbsW F) τ v) ε := by
  refine ⟨boostAlg_isLocal G F hA ℓ, fun τ v hτ => ?_⟩
  have hw : ∀ σ, 0 ≤ gibbsW F σ := gibbsW_nonneg F
  unfold boostAlg
  split_ifs with hv
  · set Γ := shellList G τ v t ℓ
    have hmemΓ : ∀ u, u ∈ Γ ↔ u ∈ shell G τ v t ℓ := fun u => by simp [Γ, shellList]
    have hΓ : ∀ u ∈ Γ, u ≠ v ∧ τ u = none := fun u hu => by
      have h := (hmemΓ u).1 hu
      refine ⟨fun huv => ?_, h.2.2⟩
      subst huv; simp [shell] at h
    have hlen : Γ.length ≤ Fintype.card V := by
      simp only [Γ, shellList, length_toList]; exact card_le_univ _
    have hblind : ∀ (ρ : Pin V S) (u : V) (c : S), u ∈ Γ →
        A (Function.update ρ v (some c)) u = A ρ u := fun ρ u c hu =>
      hA u _ _ fun u' hu' => by
        have hne : u' ≠ v := by
          rintro rfl
          have h1 := ((hmemΓ u).1 hu).1
          rw [SimpleGraph.edist_comm] at hu'
          exact absurd hu' (not_le.2 h1)
        simp [Function.update_of_ne hne]
    obtain ⟨hfeas, hmc⟩ := lemma_4_1_core hw hε0 hε1 (Fintype.card_pos_iff.2 ⟨v⟩) hacc hτ hv Γ
      (nodup_toList _) hΓ hlen hblind
    -- the locally computed marginal is the exact `μ^{τ_m}_v`
    have heq : marg (gibbsW F) (pinSeq A Γ τ) v =
        marg (gibbsWOn F (ball G v (t + ℓ))) (restrictPin (pinSeq A Γ τ) (ball G v (t + ℓ))) v :=
      marg_eq_local (I := ball G v t) (B := ball G v (t + ℓ))
        (fun u (hu : G.edist v u ≤ t) => show G.edist v u ≤ ((t + ℓ : ℕ) : ℕ∞) from
          le_trans hu (by exact_mod_cast (by omega : t ≤ t + ℓ)))
        (by simp [ball])
        (fun i ⟨u, hu, (huI : G.edist v u ≤ t)⟩ u' hu' =>
          show G.edist v u' ≤ ((t + ℓ : ℕ) : ℕ∞) by
            calc G.edist v u' ≤ G.edist v u + G.edist u u' := SimpleGraph.edist_triangle
              _ ≤ (t : ℕ∞) + (ℓ : ℕ∞) := add_le_add huI (hℓ i u hu u' (by simpa using hu'))
              _ = ((t + ℓ : ℕ) : ℕ∞) := by push_cast; ring)
        (fun u (huB : G.edist v u ≤ ((t + ℓ : ℕ) : ℕ∞)) (huI : ¬ G.edist v u ≤ t) => by
          by_cases hτu : τ u = none
          · exact pinSeq_ne_none_of_mem A Γ τ ((hmemΓ u).2 ⟨not_le.1 huI, huB, hτu⟩)
          · exact pinSeq_ne_none A Γ τ hτu)
        hfeas
    rw [← heq]; exact hmc
  · obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.1 hv
    intro c
    rw [marg_of_pinned hτ hc₀, hc₀]
    by_cases hc : c₀ = c
    · subst hc; simp [Real.exp_neg, Real.add_one_le_exp, Real.one_le_exp hε0.le]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 hε0.le) |> fun h => by
        rw [Real.exp_neg] at h; exact h
    · have : ¬ some c₀ = some c := fun h => hc (Option.some_inj.1 h)
      simp [hc, this]

end Podc.LocalSamplingCounting
