import Papers.PODC2026.OrderStatisticsPP.Fixation

/-!
# Order-Based dynamics (Definition 4.2, Theorem 7) — intended reading

Definition 4.2 of the paper only constrains configurations with pairwise distinct opinions, but
the proof of Theorem 7 uses the rank structure also on configurations with ties (which appear
after the first opinion change), as the paper's gloss ("a function of the ranks only") intends;
under the literal reading Theorem 7 fails (clarification in `Counterexample.lean`). Here we use the
intended definition: the rank-event probabilities govern *all* configurations, phrased via
thresholds (implied by the rank-event condition with ties broken arbitrarily): for every lower set `D` of opinions holding `m = cnt D c` agents,
* `P[an agent outside D adopts an opinion in D] = f (m + 1)` (`= ∑_{i>m, j≤m} q_j(i)`),
* `P[an agent in D adopts an opinion outside D] = h m` (`= ∑_{i≤m, j>m} q_j(i)`),
one agent changes per step and only adopts an opinion currently present.

`orderBased_fixation` (**Theorem 7**, intended reading of Definition 4.2): if `f (k+1) > 0` and `h k > 0` for
`k ∈ [1, n-1]`, fixation on the `k`-th smallest opinion has probability
`π_k = π_1 ∏_{i=1}^{k-1} h_i / f_{i+1}`, `π_1 = (∑_k ∏_{i=1}^{k-1} h_i / f_{i+1})⁻¹`.
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

variable {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α] {Ω : Type*} [Fintype Ω]

/-- Order-based single-agent dynamics (intended reading of Definition 4.2): random choice `ω ~ μ`, agent
`a ω c` adopts the opinion `y ω c` held by some agent; threshold up/down probabilities are given
by `f (m+1)` and `h m`. -/
structure OrderBased (μ : Ω → ℝ) (a : Ω → Config n α → Fin n) (y : Ω → Config n α → α)
    (f h : ℕ → ℝ) : Prop where
  nonneg : ∀ ω, 0 ≤ μ ω
  sum_one : ∑ ω, μ ω = 1
  adopt : ∀ ω c, ∃ v, y ω c = c v
  up : ∀ D : Set α, IsLowerSet D → ∀ c, upMass μ a y D c = f (cnt D c + 1)
  down : ∀ D : Set α, IsLowerSet D → ∀ c, downMass μ a y D c = h (cnt D c)

/-- The fixation law of Theorem 7 (unnormalised weights). -/
noncomputable def obWeight (f h : ℕ → ℝ) (k : ℕ) : ℝ := ∏ i ∈ Ico 1 k, (h i / f (i + 1))

/-- The fixation law of Theorem 7: `π_k = π_1 ∏_{i=1}^{k-1} h_i / f_{i+1}`. -/
noncomputable def obLaw (n : ℕ) (f h : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ j ∈ Ioc 0 n, obWeight f h j)⁻¹ * obWeight f h k

lemma obWeight_pos {f h : ℕ → ℝ} (hf : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < f (k + 1))
    (hh : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < h k) {k : ℕ} (hk : k ≤ n) : 0 < obWeight f h k := by
  unfold obWeight
  refine Finset.prod_pos fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  exact div_pos (hh i hi.1 (by omega)) (hf i hi.1 (by omega))

lemma cumul_obLaw (hn : 0 < n) {f h : ℕ → ℝ} (hf : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < f (k + 1))
    (hh : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < h k) : cumul (obLaw n f h) n = 1 := by
  unfold cumul obLaw
  rw [← Finset.mul_sum]
  refine inv_mul_cancel₀ (ne_of_gt (Finset.sum_pos (fun k hk => ?_) ⟨1, by simp; omega⟩))
  exact obWeight_pos hf hh (Finset.mem_Ioc.mp hk).2

lemma obLaw_balance {f h : ℕ → ℝ} (hf : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < f (k + 1)) {m : ℕ}
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) : obLaw n f h (m + 1) * f (m + 1) = obLaw n f h m * h m := by
  unfold obLaw obWeight
  rw [Finset.prod_Ico_succ_top hm]
  have := (hf m hm hmn).ne'
  field_simp

variable {μ : Ω → ℝ} {a : Ω → Config n α → Fin n} {y : Ω → Config n α → α} {f h : ℕ → ℝ}

lemma upMass_eq_zero_of_cnt_zero (hO : OrderBased μ a y f h) {D : Set α} {c : Config n α}
    (hc : cnt D c = 0) : upMass μ a y D c = 0 := by
  unfold upMass
  refine Finset.sum_eq_zero fun ω _ => ?_
  obtain ⟨v, hv⟩ := hO.adopt ω c
  rw [hv, ind_not_mem ((cnt_eq_zero_iff D c).mp hc v)]; ring

lemma downMass_eq_zero_of_cnt_zero {D : Set α} {c : Config n α} (hc : cnt D c = 0) :
    downMass μ a y D c = 0 := by
  unfold downMass
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [ind_not_mem ((cnt_eq_zero_iff D c).mp hc _)]; ring

lemma upMass_eq_zero_of_cnt_n {D : Set α} {c : Config n α} (hc : cnt D c = n) :
    upMass μ a y D c = 0 := by
  unfold upMass
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [ind_mem ((cnt_eq_n_iff D c).mp hc _)]; ring

lemma downMass_eq_zero_of_cnt_n (hO : OrderBased μ a y f h) {D : Set α} {c : Config n α}
    (hc : cnt D c = n) : downMass μ a y D c = 0 := by
  unfold downMass
  refine Finset.sum_eq_zero fun ω _ => ?_
  obtain ⟨v, hv⟩ := hO.adopt ω c
  rw [hv, ind_mem ((cnt_eq_n_iff D c).mp hc v)]; ring

/-- **Theorem 7** (intended reading, general initial configurations, ties summed). -/
theorem orderBased_fixation (hn : 0 < n) (hO : OrderBased μ a y f h)
    (hf : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < f (k + 1)) (hh : ∀ k, 1 ≤ k → k + 1 ≤ n → 0 < h k)
    (c : Config n α) (x : α) :
    Tendsto (fun t => (randomMap μ (fun ω c => Function.update c (a ω c) (y ω c)) ^ t) c
      (const x)) atTop
      (𝓝 (∑ k ∈ Ioc (cnt (Set.Iio x) c) (cnt (Set.Iic x) c), obLaw n f h k)) := by
  set T := randomMap μ (fun ω c => Function.update c (a ω c) (y ω c))
  have hT : T ∈ rowStochastic ℝ (Config n α) := randomMap_mem_rowStochastic hO.nonneg hO.sum_one _
  refine fixation_of_harmonic hT hn _ (cumul_obLaw hn hf hh) ?_ ?_ ?_ c x
  · -- consensus is absorbing
    intro z s hs
    refine randomMap_eq_zero_of_fixed (fun ω => ?_) hs
    obtain ⟨v, hv⟩ := hO.adopt ω (const z)
    funext u
    rw [hv]
    by_cases hu : u = a ω (const z)
    · subst hu; simp [const]
    · rw [Function.update_of_ne hu]
  · -- consensus is reachable: some agent below the maximum adopts the maximum
    refine reach_const_of_step hn T (fun c M hle hex hlt => ?_)
    have hpos : 0 < cnt (Set.Iio M) c := (cnt_pos_iff _ c).mpr hlt
    have hlt' : cnt (Set.Iio M) c < n := by
      obtain ⟨t, ht⟩ := hex
      have := cnt_le (Set.Iio M) c
      by_contra hge
      have : cnt (Set.Iio M) c = n := by omega
      exact (lt_irrefl M) (ht ▸ (cnt_eq_n_iff _ c).mp this t)
    have hd := hO.down (Set.Iio M) (isLowerSet_Iio M) c
    have hdpos : 0 < downMass μ a y (Set.Iio M) c := by
      rw [hd]; exact hh _ hpos (by omega)
    unfold downMass at hdpos
    obtain ⟨ω, -, hω⟩ := exists_pos_of_sum_pos' hdpos
    have hμ : 0 < μ ω := by
      by_contra hle
      have : μ ω = 0 := le_antisymm (not_lt.mp hle) (hO.nonneg ω)
      rw [this, zero_mul] at hω; exact lt_irrefl _ hω
    have h1 : c (a ω c) < M := by
      by_contra hge
      rw [ind_not_mem (show c (a ω c) ∉ Set.Iio M by simpa using hge)] at hω; simp at hω
    have h2 : y ω c = M := by
      obtain ⟨v, hv⟩ := hO.adopt ω c
      by_contra hne
      have : y ω c < M := lt_of_le_of_ne (hv ▸ hle v) hne
      rw [ind_mem (show y ω c ∈ Set.Iio M from this)] at hω; simp at hω
    refine ⟨a ω c, h1, ?_⟩
    have := randomMap_pos hO.nonneg (fun ω c => Function.update c (a ω c) (y ω c)) hμ c
    simpa [h2] using this
  · -- harmonicity from the balance condition
    intro D hD
    refine harmonic_of_balance μ hO.sum_one a y _ D fun c => ?_
    set m := cnt D c with hm
    have hmn : m ≤ n := cnt_le D c
    by_cases h0 : m = 0
    · rw [upMass_eq_zero_of_cnt_zero hO h0, downMass_eq_zero_of_cnt_zero h0]; ring
    by_cases hn' : m = n
    · rw [upMass_eq_zero_of_cnt_n hn', downMass_eq_zero_of_cnt_n hO hn']; ring
    rw [hO.up D hD c, hO.down D hD c, ← hm]
    exact obLaw_balance hf (by omega) (by omega)

end OrderStatisticsPP
