import Papers.PODC2026.OrderStatisticsPP.CopyOrMax
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Counterexamples

1. **Definition 4.2 is under-specified (clarification for Theorem 7).** Definition 4.2
   ("Order-Based dynamics") literally only constrains configurations whose opinions are pairwise
   distinct (the paper's gloss shows that the rank structure is intended on all configurations;
   see `OrderBased.lean`). The dynamics `tieMax`
   below (3 agents, opinions `0 < 1 < 2`, `p = 1/2`) *is* Copy-or-Max on every configuration with
   distinct opinions (`tieMax_eq_copyOrMax`), hence satisfies Definition 4.2 with Copy-or-Max's
   `q_j(i)` (Lemma 4.1) and the positivity hypotheses of Theorem 7; on configurations with a tie
   it runs the pure Max dynamics. It converges to consensus a.s., but fixes on the largest opinion
   with probability `7/9`, not `π_3 = 4/7` (`tieMax_fixation`, `tieMax_not_geometric`), so the
   literal reading of Definition 4.2 is too weak for Theorem 7.

2. **D vs D⁻¹ slip in Proposition 6, Item iv)** (minor; Lemma 4.7 itself is valid, its item iv)
   being an existential hypothesis satisfied by `D = diag(1/√π_k)`): with the proof's choice
   `D = diag(√π_k)` the matrix `D⁻¹ Pᵀ D` is *not* symmetric (`D Pᵀ D⁻¹` is), already for `n = 2`,
   `p = 1/2` (`prop6_itemIv_sqrt_slip`).
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP.Counterexample

open Finset Matrix Filter Topology Cslib.Probability.Markov OrderStatisticsPP

/-! ### 1. The literal reading of Definition 4.2 -/

/-- Copy-or-Max (`p = 1/2`) on configurations with distinct opinions, Max on configurations with a
tie. -/
noncomputable def tieMax : Matrix (Config 3 (Fin 3)) (Config 3 (Fin 3)) ℝ :=
  randomMap (comμ (fun _ _ => (1 : ℝ)) (1 / 2)) fun ω c =>
    Function.update c ω.1 (if Function.Injective c then comNew c ω else max (c ω.1) (c ω.2.1))

/-- On configurations with pairwise distinct opinions, `tieMax` *is* Copy-or-Max: in particular
it is Order-Based in the sense of Definition 4.2, with the `q_j(i)` of Lemma 4.1. -/
theorem tieMax_eq_copyOrMax (c : Config 3 (Fin 3)) (hc : Function.Injective c)
    (c' : Config 3 (Fin 3)) : tieMax c c' = copyOrMax 3 (Fin 3) (1 / 2) c c' := by
  unfold tieMax copyOrMax copyOrMaxW randomMap
  simp only [ite_eq_left hc]

/-- The fixation probability of opinion `2`. -/
noncomputable def hfix (c : Config 3 (Fin 3)) : ℝ :=
  if Function.Injective c then 7 / 9 else if ∃ u, c u = 2 then 1 else 0

/-- Contribution of a random choice at an injective configuration, in terms of opinions. -/
noncomputable def G (a b : Fin 3) (copy : Bool) : ℝ :=
  if (if copy then b else max a b) = a then 7 / 9 else if a = 2 then 0 else 1

lemma update_not_injective {c : Config 3 (Fin 3)} {u v : Fin 3} (huv : u ≠ v) :
    ¬ Function.Injective (Function.update c u (c v)) := by
  intro h
  exact huv (h (by simp [Function.update_of_ne huv.symm]))

lemma hfix_step_inj (c : Config 3 (Fin 3)) (hc : Function.Injective c)
    (ω : Fin 3 × Fin 3 × Bool) :
    hfix (Function.update c ω.1 (comNew c ω)) = G (c ω.1) (c ω.2.1) ω.2.2 := by
  obtain ⟨u, v, b⟩ := ω
  have hbij : Function.Bijective c := Finite.injective_iff_bijective.mp hc
  -- the adopted opinion is `c x` for `x ∈ {u, v}`
  obtain ⟨x, hx, hxuv⟩ : ∃ x, comNew c (u, v, b) = c x ∧ (x = u ∨ x = v) := by
    unfold comNew
    cases b
    · rcases max_choice (c u) (c v) with h | h
      · exact ⟨u, by simpa using h, Or.inl rfl⟩
      · exact ⟨v, by simpa using h, Or.inr rfl⟩
    · exact ⟨v, rfl, Or.inr rfl⟩
  have hG : G (c u) (c v) b =
      if c x = c u then 7 / 9 else if c u = 2 then 0 else 1 := by
    unfold G; rw [← hx]; rfl
  rw [hG, hx]
  by_cases hxu : c x = c u
  · rw [ite_eq_left hxu, hxu, Function.update_eq_self]
    simp [hfix, hc]
  · rw [ite_eq_right hxu]
    have hxu' : u ≠ x := fun h => hxu (h ▸ rfl)
    unfold hfix
    rw [ite_eq_right (update_not_injective hxu')]
    by_cases h2 : c u = 2
    · rw [ite_eq_left h2, ite_eq_right]
      rintro ⟨w, hw⟩
      rcases eq_or_ne w u with rfl | hwu
      · rw [Function.update_self] at hw; exact hxu (hw.trans h2.symm)
      · rw [Function.update_of_ne hwu] at hw; exact hwu (hc (hw.trans h2.symm))
    · rw [ite_eq_right h2, ite_eq_left]
      obtain ⟨w, hw⟩ := hbij.2 2
      refine ⟨w, ?_⟩
      have hwu : w ≠ u := fun h => h2 (h ▸ hw)
      rw [Function.update_of_ne hwu, hw]

lemma hfix_step_tie (c : Config 3 (Fin 3)) (hc : ¬ Function.Injective c) (u v : Fin 3) :
    hfix (Function.update c u (max (c u) (c v))) = hfix c := by
  unfold hfix
  have hni : ¬ Function.Injective (Function.update c u (max (c u) (c v))) := by
    rcases max_choice (c u) (c v) with h | h
    · rw [h, Function.update_eq_self]; exact hc
    · rw [h]
      by_cases huv : u = v
      · subst huv; rw [Function.update_eq_self]; exact hc
      · exact update_not_injective huv
  rw [ite_eq_right hni, ite_eq_right hc]
  congr 1
  apply propext
  constructor
  · rintro ⟨w, hw⟩
    rcases eq_or_ne w u with rfl | hwu
    · rw [Function.update_self] at hw
      rcases max_choice (c w) (c v) with h | h
      · exact ⟨w, h ▸ hw⟩
      · exact ⟨v, h ▸ hw⟩
    · exact ⟨w, by rwa [Function.update_of_ne hwu] at hw⟩
  · rintro ⟨w, hw⟩
    rcases eq_or_ne w u with rfl | hwu
    · refine ⟨w, ?_⟩
      rw [Function.update_self, hw]
      exact le_antisymm (Fin.le_last _) (le_max_left _ _)
    · exact ⟨w, by rwa [Function.update_of_ne hwu]⟩

lemma comμ_one_half (ω : Fin 3 × Fin 3 × Bool) :
    comμ (fun _ _ => (1 : ℝ)) (1 / 2) ω = 1 / 18 := by
  unfold comμ
  simp only [Fin.sum_univ_three]
  split_ifs <;> norm_num

lemma sum_G : ∑ a : Fin 3, ∑ b : Fin 3, ∑ copy : Bool, G a b copy = 14 := by
  simp only [Fin.sum_univ_three, Fintype.sum_bool, G]
  norm_num [max_def]

lemma tieMax_harmonic : tieMax *ᵥ hfix = hfix := by
  funext c
  unfold tieMax
  rw [randomMap_mulVec]
  simp only [comμ_one_half]
  by_cases hc : Function.Injective c
  · simp only [ite_eq_left hc, hfix_step_inj c hc]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    set e := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hc)
    have hsum : ∑ u, ∑ v, ∑ b, (1 / 18 : ℝ) * G (c u) (c v) b =
        ∑ a : Fin 3, ∑ b : Fin 3, ∑ copy : Bool, (1 / 18 : ℝ) * G a b copy := by
      calc ∑ u, ∑ v, ∑ b, (1 / 18 : ℝ) * G (c u) (c v) b
          = ∑ u, ∑ b' : Fin 3, ∑ copy : Bool, (1 / 18 : ℝ) * G (c u) b' copy :=
            Finset.sum_congr rfl fun u _ =>
              Equiv.sum_comp e (fun b' => ∑ copy : Bool, (1 / 18 : ℝ) * G (c u) b' copy)
        _ = _ := Equiv.sum_comp e (fun a => ∑ b' : Fin 3, ∑ copy : Bool, (1 / 18 : ℝ) * G a b' copy)
    rw [hsum]
    simp only [← Finset.mul_sum, sum_G]
    simp [hfix, hc]; norm_num
  · simp only [ite_eq_right hc, hfix_step_tie c hc]
    simp only [← Finset.sum_mul, Finset.sum_const, Finset.card_univ]
    norm_num

lemma tieMax_mem : tieMax ∈ rowStochastic ℝ (Config 3 (Fin 3)) :=
  randomMap_mem_rowStochastic
    (comμ_nonneg (fun _ _ => zero_le_one) (clique_W_pos (by norm_num)) (by norm_num) (by norm_num))
    (comμ_sum (clique_W_pos (by norm_num))) _

lemma const_not_injective (z : Fin 3) : ¬ Function.Injective (const z : Config 3 (Fin 3)) :=
  fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide)

/-- The configuration `(0, 1, 2)`. -/
def c₀ : Config 3 (Fin 3) := id

/-- **Clarification for Theorem 7 (literal reading of Definition 4.2).** From `(0, 1, 2)`, `tieMax` fixes on
the largest opinion with probability `7/9`. -/
theorem tieMax_fixation :
    Tendsto (fun t => (tieMax ^ t) c₀ (const 2)) atTop (𝓝 (7 / 9)) := by
  set A : Finset (Config 3 (Fin 3)) := univ.image const
  have hclosed : ∀ a ∈ A, ∀ s ∉ A, tieMax a s = 0 := by
    intro a ha s hs
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp ha
    refine randomMap_eq_zero_of_fixed (fun ω => ?_) (fun h => hs (h ▸ Finset.mem_image_of_mem _
      (Finset.mem_univ z)))
    rw [ite_eq_right (const_not_injective z)]
    funext v; simp [const, Function.update_apply]
  have hreach : ∀ s, ∃ a ∈ A, Relation.ReflTransGen (fun x y => 0 < tieMax x y) s a := by
    intro s
    obtain ⟨z, hz⟩ := reach_const_of_step (by norm_num) tieMax (fun c M hle hex hlt => by
      obtain ⟨t, ht⟩ := hex
      obtain ⟨u, hu⟩ := hlt
      refine ⟨u, hu, ?_⟩
      have := randomMap_pos (μ := comμ (fun _ _ => (1 : ℝ)) (1 / 2))
        (fun ω => by rw [comμ_one_half]; norm_num)
        (fun ω (c : Config 3 (Fin 3)) => Function.update c ω.1
          (if Function.Injective c then comNew c ω else max (c ω.1) (c ω.2.1)))
        (ω := (u, t, false)) (by rw [comμ_one_half]; norm_num) c
      have hm : max (c u) (c t) = M := by rw [ht]; exact max_eq_right (hle u)
      unfold tieMax
      split_ifs at this <;> simpa [comNew, hm] using this) s
    exact ⟨const z, Finset.mem_image_of_mem _ (Finset.mem_univ z), hz⟩
  have h := tendsto_sum_mul_of_harmonic tieMax_mem hclosed hreach tieMax_harmonic c₀
  have hc₀ : hfix c₀ = 7 / 9 := by simp [hfix, c₀, Function.injective_id]
  rw [hc₀] at h
  refine h.congr fun t => ?_
  rw [Finset.sum_image (fun a _ b _ hab => const_injective (by norm_num) hab)]
  rw [Finset.sum_eq_single 2]
  · simp [hfix, const_not_injective, const]
  · intro z _ hz
    simp [hfix, const_not_injective, const, hz]
  · simp

lemma rank_c₀ : rank c₀ (c₀ 2) = 3 := by
  rw [rank, cnt_eq_card]
  decide

/-- The geometric law of Theorem 7 / Proposition 5 predicts `π_3 = 4/7 ≠ 7/9`. -/
theorem tieMax_not_geometric :
    ¬ Tendsto (fun t => (tieMax ^ t) c₀ (const (c₀ 2))) atTop
      (𝓝 (geomLaw 3 (1 / 2) (rank c₀ (c₀ 2)))) := by
  intro h
  have := tendsto_nhds_unique h tieMax_fixation
  rw [rank_c₀] at this
  norm_num [geomLaw] at this

/-! ### 2. Item iv) in the proof of Proposition 6 -/

/-- `Pᵀ` of Lemma 4.3 for `n = 2`, `p = 1/2`: `h₁ = 1/4`, `f₂ = 1/8`. -/
noncomputable def K2 : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, 1 / 4; 1 / 8, 7 / 8]

/-- Its stationary distribution `π = (1/3, 2/3)` (geometric law, `n = 2`, `p = 1/2`). -/
noncomputable def π2 : Fin 2 → ℝ := ![1 / 3, 2 / 3]

lemma π2_stationary : π2 ᵥ* K2 = π2 := by
  funext j; fin_cases j <;> simp [π2, K2, vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- **Proposition 6, Item iv) (D vs D⁻¹ slip):** with the proof's `D = diag(√π)`, `D⁻¹ Pᵀ D` is
not symmetric, whereas `D Pᵀ D⁻¹` is (i.e. Lemma 4.7 iv) holds with `diag(1/√π)`). -/
theorem prop6_itemIv_sqrt_slip :
    let D := Matrix.diagonal fun i => Real.sqrt (π2 i)
    let Dinv := Matrix.diagonal fun i => (Real.sqrt (π2 i))⁻¹
    Dinv * K2 * D ≠ (Dinv * K2 * D)ᵀ ∧ D * K2 * Dinv = (D * K2 * Dinv)ᵀ := by
  intro D Dinv
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs3 : 0 < Real.sqrt 3 := by positivity
  constructor
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [D, Dinv, K2, π2, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    field_simp at this
    nlinarith [hsq, h3]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Dinv, K2, π2, Matrix.diagonal_mul, Matrix.mul_diagonal] <;>
      field_simp <;> nlinarith [hsq, h3]

end OrderStatisticsPP.Counterexample
