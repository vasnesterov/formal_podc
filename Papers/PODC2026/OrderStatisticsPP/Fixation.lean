import Papers.PODC2026.OrderStatisticsPP.Basic

/-!
# The generic fixation theorem (threshold method)

* `fixation_of_harmonic`: if consensus configurations are absorbing and reachable, and for every
  lower set `D` the function `c ↦ cumul π (cnt D c)` is harmonic, then the probability of fixation
  on `x` is `∑ π k` over the ranks `k` of `x` (`#{u | c u < x} < k ≤ #{u | c u ≤ x}`).
* `harmonic_of_balance`: for single-agent update dynamics (`randomMap` of
  `ω ↦ update c (a ω c) (y ω c)`), harmonicity follows from the balance condition
  `π (m+1) · P[cnt D increases] = π m · P[cnt D decreases]`, `m = cnt D c`.
* `reach_const_of_step`: consensus is reachable if a non-maximal agent can always adopt the
  maximum with positive probability.
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

variable {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α]

lemma const_injective (hn : 0 < n) : Function.Injective (const : α → Config n α) := by
  intro a b h
  exact congrFun h ⟨0, hn⟩

/-- **Generic fixation theorem.** -/
theorem fixation_of_harmonic {T : Matrix (Config n α) (Config n α) ℝ}
    (hT : T ∈ rowStochastic ℝ (Config n α)) (hn : 0 < n) (π : ℕ → ℝ) (hπ : cumul π n = 1)
    (habs : ∀ (z : α) (s : Config n α), s ≠ const z → T (const z) s = 0)
    (hreach : ∀ c : Config n α, ∃ z, Relation.ReflTransGen (fun a b => 0 < T a b) c (const z))
    (hharm : ∀ D : Set α, IsLowerSet D →
      T *ᵥ (fun c => cumul π (cnt D c)) = fun c => cumul π (cnt D c))
    (c : Config n α) (x : α) :
    Tendsto (fun t => (T ^ t) c (const x)) atTop
      (𝓝 (∑ k ∈ Ioc (cnt (Set.Iio x) c) (cnt (Set.Iic x) c), π k)) := by
  set A : Finset (Config n α) := univ.image const with hA
  have hclosed : ∀ a ∈ A, ∀ s ∉ A, T a s = 0 := by
    intro a ha s hs
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp ha
    exact habs z s fun h => hs (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ z))
  have hreach' : ∀ s, ∃ a ∈ A, Relation.ReflTransGen (fun x y => 0 < T x y) s a := by
    intro s
    obtain ⟨z, hz⟩ := hreach s
    exact ⟨const z, Finset.mem_image_of_mem _ (Finset.mem_univ z), hz⟩
  -- the limit for each lower set
  have hD : ∀ D : Set α, IsLowerSet D →
      Tendsto (fun t => ∑ z, ind D z * (T ^ t) c (const z)) atTop
        (𝓝 (cumul π (cnt D c))) := by
    intro D hDl
    have := tendsto_sum_mul_of_harmonic hT hclosed hreach' (hharm D hDl) c
    refine this.congr fun t => ?_
    rw [hA, Finset.sum_image (fun a _ b _ h => const_injective hn h)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [cnt_const]
    by_cases hz : z ∈ D <;> simp [hz, hπ, cumul_zero, ind_mem, ind_not_mem]
  have hlim := (hD (Set.Iic x) (isLowerSet_Iic x)).sub (hD (Set.Iio x) (isLowerSet_Iio x))
  rw [cumul_sub π (cnt_mono Set.Iio_subset_Iic_self c)] at hlim
  refine hlim.congr fun t => ?_
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single x]
  · simp [ind_mem, ind_not_mem]
  · intro z _ hz
    rcases lt_or_gt_of_ne hz with h | h
    · simp [ind_mem, h, h.le]
    · rw [ind_not_mem (by simpa using h), ind_not_mem (by simpa using h.le)]; ring
  · simp

/-- For injective `c`, exactly one agent holds `c u`. -/
lemma cnt_Iic_injective {c : Config n α} (hc : Function.Injective c) (u : Fin n) :
    cnt (Set.Iic (c u)) c = cnt (Set.Iio (c u)) c + 1 := by
  rw [cnt_eq_card, cnt_eq_card]
  calc _ = (insert u (univ.filter fun v => c v ∈ Set.Iio (c u))).card := by
        congr 1
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iic, Set.mem_Iio,
          Finset.mem_insert]
        constructor
        · intro hv
          rcases hv.lt_or_eq with h | h
          · exact Or.inr h
          · exact Or.inl (hc h)
        · rintro (rfl | h)
          · exact le_rfl
          · exact h.le
    _ = _ := by rw [Finset.card_insert_of_notMem (by simp)]

/-- For injective configurations: fixation on the `k`-th smallest value has probability `π k`. -/
theorem fixation_of_harmonic_injective {T : Matrix (Config n α) (Config n α) ℝ}
    (hT : T ∈ rowStochastic ℝ (Config n α)) (hn : 0 < n) (π : ℕ → ℝ) (hπ : cumul π n = 1)
    (habs : ∀ (z : α) (s : Config n α), s ≠ const z → T (const z) s = 0)
    (hreach : ∀ c : Config n α, ∃ z, Relation.ReflTransGen (fun a b => 0 < T a b) c (const z))
    (hharm : ∀ D : Set α, IsLowerSet D →
      T *ᵥ (fun c => cumul π (cnt D c)) = fun c => cumul π (cnt D c))
    (c : Config n α) (hc : Function.Injective c) (u : Fin n) :
    Tendsto (fun t => (T ^ t) c (const (c u))) atTop (𝓝 (π (rank c (c u)))) := by
  have h := fixation_of_harmonic hT hn π hπ habs hreach hharm c (c u)
  have hr := cnt_Iic_injective hc u
  rw [hr, Nat.Ioc_succ_singleton, Finset.sum_singleton] at h
  unfold rank
  rwa [hr]

/-! ### Harmonicity from balance -/

section Balance

variable {Ω : Type*} [Fintype Ω]

/-- Up-probability: an agent outside `D` adopts an opinion in `D`. -/
noncomputable def upMass (μ : Ω → ℝ) (a : Ω → Config n α → Fin n) (y : Ω → Config n α → α)
    (D : Set α) (c : Config n α) : ℝ :=
  ∑ ω, μ ω * ((1 - ind D (c (a ω c))) * ind D (y ω c))

/-- Down-probability: an agent in `D` adopts an opinion outside `D`. -/
noncomputable def downMass (μ : Ω → ℝ) (a : Ω → Config n α → Fin n) (y : Ω → Config n α → α)
    (D : Set α) (c : Config n α) : ℝ :=
  ∑ ω, μ ω * (ind D (c (a ω c)) * (1 - ind D (y ω c)))

lemma cumul_cnt_update (π : ℕ → ℝ) (D : Set α) (c : Config n α) (u : Fin n) (y : α) :
    cumul π (cnt D (Function.update c u y)) = cumul π (cnt D c)
      + (1 - ind D (c u)) * ind D y * π (cnt D c + 1)
      - ind D (c u) * (1 - ind D y) * π (cnt D c) := by
  have h := cnt_update_int D c u y
  by_cases hu : c u ∈ D <;> by_cases hy : y ∈ D <;>
    simp only [hu, hy, ite_true, ite_false, ind_mem, ind_not_mem, not_false_eq_true] at h ⊢
  · have : cnt D (Function.update c u y) = cnt D c := by omega
    rw [this]; ring
  · have hpos : 1 ≤ cnt D c := by omega
    have : cnt D (Function.update c u y) + 1 = cnt D c := by omega
    rw [← this, cumul_succ]; ring
  · have : cnt D (Function.update c u y) = cnt D c + 1 := by omega
    rw [this, cumul_succ]; ring
  · have : cnt D (Function.update c u y) = cnt D c := by omega
    rw [this]; ring

/-- One-step expectation of `cumul π (cnt D ·)` for single-agent update dynamics. -/
lemma randomMap_mulVec_cumul (μ : Ω → ℝ) (h1 : ∑ ω, μ ω = 1) (a : Ω → Config n α → Fin n)
    (y : Ω → Config n α → α) (π : ℕ → ℝ) (D : Set α) (c : Config n α) :
    (randomMap μ (fun ω c => Function.update c (a ω c) (y ω c)) *ᵥ
        (fun c => cumul π (cnt D c))) c =
      cumul π (cnt D c) + π (cnt D c + 1) * upMass μ a y D c
        - π (cnt D c) * downMass μ a y D c := by
  rw [randomMap_mulVec]
  simp_rw [cumul_cnt_update]
  unfold upMass downMass
  have e : ∀ ω, μ ω * (cumul π (cnt D c) + (1 - ind D (c (a ω c))) * ind D (y ω c) *
      π (cnt D c + 1) - ind D (c (a ω c)) * (1 - ind D (y ω c)) * π (cnt D c)) =
      μ ω * cumul π (cnt D c) + π (cnt D c + 1) * (μ ω * ((1 - ind D (c (a ω c))) *
        ind D (y ω c))) - π (cnt D c) * (μ ω * (ind D (c (a ω c)) * (1 - ind D (y ω c)))) := by
    intro ω; ring
  simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    h1, one_mul]

/-- **Harmonicity from balance** for single-agent update dynamics. -/
theorem harmonic_of_balance (μ : Ω → ℝ) (h1 : ∑ ω, μ ω = 1) (a : Ω → Config n α → Fin n)
    (y : Ω → Config n α → α) (π : ℕ → ℝ) (D : Set α)
    (hbal : ∀ c, π (cnt D c + 1) * upMass μ a y D c = π (cnt D c) * downMass μ a y D c) :
    randomMap μ (fun ω c => Function.update c (a ω c) (y ω c)) *ᵥ
        (fun c => cumul π (cnt D c)) = fun c => cumul π (cnt D c) := by
  funext c
  rw [randomMap_mulVec_cumul μ h1, hbal c]
  ring

end Balance

/-! ### Reaching consensus -/

/-- If a non-maximal agent can always adopt the (current) maximum opinion with positive
probability, then consensus is reachable from every configuration. -/
theorem reach_const_of_step (hn : 0 < n) (T : Matrix (Config n α) (Config n α) ℝ)
    (hstep : ∀ (c : Config n α) (M : α), (∀ w, c w ≤ M) → (∃ w, c w = M) → (∃ u, c u < M) →
      ∃ u, c u < M ∧ 0 < T c (Function.update c u M))
    (c : Config n α) : ∃ z, Relation.ReflTransGen (fun a b => 0 < T a b) c (const z) := by
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_max_image Finset.univ c ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set M := c w₀
  refine ⟨M, ?_⟩
  -- induction on the number of non-maximal agents, keeping the maximum `M`
  suffices H : ∀ k, ∀ c : Config n α, cnt (Set.Iio M) c = k → (∀ w, c w ≤ M) → (∃ w, c w = M) →
      Relation.ReflTransGen (fun a b => 0 < T a b) c (const M) from
    H _ c rfl (fun w => hw₀ w (Finset.mem_univ w)) ⟨w₀, rfl⟩
  intro k
  induction k with
  | zero =>
    intro c hk hle _
    have : c = const M := by
      funext w
      have : c w ∉ Set.Iio M := (cnt_eq_zero_iff _ c).mp hk w
      exact le_antisymm (hle w) (not_lt.mp this)
    rw [this]
  | succ k ih =>
    intro c hk hle hex
    have hu : ∃ u, c u < M := by
      by_contra hne
      push Not at hne
      have : cnt (Set.Iio M) c = 0 :=
        (cnt_eq_zero_iff _ c).mpr fun v hv => not_lt.mpr (hne v) hv
      omega
    obtain ⟨u, hu, hpos⟩ := hstep c M hle hex hu
    refine Relation.ReflTransGen.head hpos (ih _ ?_ ?_ ?_)
    · have := cnt_update_int (Set.Iio M) c u M
      simp only [Set.mem_Iio, hu, ite_true, lt_irrefl, ite_false] at this
      omega
    · intro w
      rcases eq_or_ne w u with rfl | h
      · simp
      · rw [Function.update_of_ne h]; exact hle w
    · exact ⟨u, by simp⟩

end OrderStatisticsPP
