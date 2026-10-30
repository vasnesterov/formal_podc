import Papers.PODC2011.UniformLocalAlgorithms.Theorem3
import Papers.PODC2011.UniformLocalAlgorithms.Theorem4
import Papers.PODC2011.UniformLocalAlgorithms.Pruning
import Cslib.Foundations.Data.Nat.LogStar

/-!
# Corollaries 1, 2 and 4: uniform MIS and maximal matching algorithms

The cited non-uniform algorithms (Barenboim–Elkin [4], Kuhn [22], Panconesi–Srinivasan [34],
Hańćkowiak–Karoński–Panconesi [19], Barenboim–Elkin [6]) are not formalized; their existence, with
the stated running times, is a hypothesis of each corollary. All instances are finite graphs with
identifiers in `V` (`allFinite`), `n = numNodes`, `Δ = maxDeg`.

* `theorem_1_additive`: Theorem 1 for additive running-time bounds (`s_f = 1`, Observation 4.1):
  the uniform running time is `O(f*)`.
* `corollary_2_delta`: uniform MIS in `O(Δ + log* n)` from a non-uniform one using `ñ, Δ̃`.
* `corollary_2_n`: uniform MIS in `O(g(n))` from a non-uniform one using `ñ` with time `g(ñ)`
  (e.g. `g(ñ) = 2^{O(√log ñ)}` for [34]).
* `corollary_1_vi`: uniform maximal matching in `O(g(n))` (e.g. `O(log⁴ n)` for [19]) — for the
  partner-identity encoding of matchings (the paper's encoding admits no pruning algorithm,
  `observation_3_3_false`).
* `corollary_4`: Theorem 3 with `Γ = {a, n}`, `Λ = {n}` for any parameter `a ≤ n` (e.g. the
  arboricity), assuming the cited algorithm runs in time `f(ñ)` for all good guesses.
* `corollary_1_i`: combining three uniform MIS algorithms with Theorem 4.
-/

open Filter

namespace Podc.UniformLocalAlgorithms

variable {V α β : Type*}

/-- Theorem 1 for an additive running-time bound `f(g) = Σ_k f_k(g_k)` with `f_k ≥ 0` ascending:
by Observation 4.1, `s_f = 1`, so the uniform algorithm runs in time `O(f*)`. -/
theorem theorem_1_additive [Inhabited β] {ℓ : ℕ} (Pb : Problem V α β) (F : Family V α)
    (Γ : Fin ℓ → Param V α) (A : (Fin ℓ → ℕ) → Alg V α β) (fk : Fin ℓ → ℕ → ℝ)
    (h0 : ∀ k y, 0 ≤ fk k y) (hinf : ∀ k, Tendsto (fk k) atTop atTop)
    (hA : DependsWithTime Pb F Γ A (fun g => ∑ k, fk k (g k)))
    (P : Pruning Pb F) (hP : ∀ k, P.Monotone (Γ k)) :
    ∃ U : Alg V α β, ∃ C : ℝ, ∀ G x, F.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C * (∑ k, fk k (Γ k G x) + 1) ∧ U.SolvesWithin Pb G x T := by
  obtain ⟨U, C, hU⟩ := theorem_1 Pb F Γ A _ (fun g => Finset.sum_nonneg fun k _ => h0 k (g k)) hA
    _ (observation_4_1_additive fk h0 hinf) P hP
  exact ⟨U, C, fun G x hx => by simpa [correct] using hU G x hx⟩

lemma tendsto_logStar : Tendsto (fun y : ℕ => (Nat.logStar y : ℝ)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.2 fun m => ⟨Nat.tower m, ?_⟩)
  intro n hn
  exact (Nat.le_logStar_iff (by have := Nat.tower_pos m; omega)).2 hn

lemma tendsto_const_mul {g : ℕ → ℝ} {C : ℝ} (hC : 0 < C) (hg : Tendsto g atTop atTop) :
    Tendsto (fun y => C * g y) atTop atTop :=
  hg.const_mul_atTop hC

/-- **Corollary 2** (first item; Corollary 1(i), `h(Δ, n)`). If there is a non-uniform
deterministic MIS algorithm that uses guesses `ñ ≥ n`, `Δ̃ ≥ Δ` and runs in time
`C (Δ̃ + log* ñ)` (Barenboim–Elkin [4], Kuhn [22]), then there is a uniform deterministic MIS
algorithm running in time `O(Δ + log* n)`. -/
theorem corollary_2_delta (A : (Fin 2 → ℕ) → Alg V α Bool) (C : ℝ) (hC : 0 < C)
    (hA : DependsWithTime mis allFinite ![numNodes, maxDeg] A
      (fun g => C * Nat.logStar (g 0) + C * g 1)) :
    ∃ U : Alg V α Bool, ∃ C' : ℝ, ∀ G x, allFinite.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C' * (maxDeg G x + Nat.logStar (numNodes G x) + 1) ∧
      U.SolvesWithin mis G x T := by
  let fk : Fin 2 → ℕ → ℝ := ![fun y => C * Nat.logStar y, fun y => C * y]
  have hfk0 : ∀ k y, 0 ≤ fk k y := by
    intro k y; fin_cases k <;> simp [fk] <;> positivity
  have hinf : ∀ k, Tendsto (fk k) atTop atTop := by
    intro k; fin_cases k
    · exact tendsto_const_mul hC tendsto_logStar
    · exact tendsto_const_mul hC tendsto_natCast_atTop_atTop
  have hP := observation_3_2 (V := V) (α := α) 1 le_rfl
  obtain ⟨U, C₁, hU⟩ := theorem_1_additive mis allFinite ![numNodes, maxDeg] A fk hfk0 hinf
    (by simpa [fk, Fin.sum_univ_two] using hA) misPruning
    (fun k => by fin_cases k; exacts [hP.2.1, hP.2.2.1])
  refine ⟨U, max C₁ 0 * max C 1, fun G x hx => ?_⟩
  obtain ⟨T, hT, hsol⟩ := hU G x hx
  refine ⟨T, hT.trans ?_, hsol⟩
  simp only [fk, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : (0 : ℝ) ≤ Nat.logStar (numNodes G x) := by positivity
  have h2 : (0 : ℝ) ≤ maxDeg G x := by positivity
  have hb : C * Nat.logStar (numNodes G x) + C * maxDeg G x + 1 ≤
      max C 1 * (maxDeg G x + Nat.logStar (numNodes G x) + 1) := by
    have := le_max_left C 1; have := le_max_right C 1
    nlinarith
  calc C₁ * (C * Nat.logStar (numNodes G x) + C * maxDeg G x + 1)
      ≤ max C₁ 0 * (C * Nat.logStar (numNodes G x) + C * maxDeg G x + 1) := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _); positivity
    _ ≤ max C₁ 0 * (max C 1 * (maxDeg G x + Nat.logStar (numNodes G x) + 1)) :=
        mul_le_mul_of_nonneg_left hb (le_max_right _ _)
    _ = _ := by ring

/-- A transformer for algorithms whose only parameter is `n` and whose running time `g(ñ)` is
ascending: the uniform algorithm runs in `O(g(n))`. -/
theorem uniform_of_numNodes [Inhabited β] (Pb : Problem V α β) (P : Pruning Pb allFinite)
    (hP : P.Monotone numNodes) (A : (Fin 1 → ℕ) → Alg V α β) (g : ℕ → ℝ) (hg0 : ∀ y, 0 ≤ g y)
    (hg : Tendsto g atTop atTop) (hA : DependsWithTime Pb allFinite ![numNodes] A (fun h => g (h 0))) :
    ∃ U : Alg V α β, ∃ C : ℝ, ∀ G x, allFinite.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C * (g (numNodes G x) + 1) ∧ U.SolvesWithin Pb G x T := by
  obtain ⟨U, C, hU⟩ := theorem_1_additive Pb allFinite ![numNodes] A (fun _ => g)
    (fun _ => hg0) (fun _ => hg) (by simpa using hA) P (fun k => by fin_cases k; exact hP)
  exact ⟨U, C, fun G x hx => by simpa using hU G x hx⟩

/-- **Corollary 2** (second item; Corollary 1(i), `g(n)`). If there is a non-uniform deterministic
MIS algorithm that uses a guess `ñ ≥ n` and runs in time `g(ñ)` for an ascending `g` (for
Panconesi–Srinivasan [34], `g(ñ) = 2^{O(√log ñ)}`), then there is a uniform deterministic MIS
algorithm running in time `O(g(n))`. -/
theorem corollary_2_n (A : (Fin 1 → ℕ) → Alg V α Bool) (g : ℕ → ℝ) (hg0 : ∀ y, 0 ≤ g y)
    (hg : Tendsto g atTop atTop) (hA : DependsWithTime mis allFinite ![numNodes] A (fun h => g (h 0))) :
    ∃ U : Alg V α Bool, ∃ C : ℝ, ∀ G x, allFinite.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C * (g (numNodes G x) + 1) ∧ U.SolvesWithin mis G x T :=
  uniform_of_numNodes mis misPruning (observation_3_2 (V := V) (α := α) 1 le_rfl).2.1 A g hg0 hg hA

/-- **Corollary 1(vi)**, for matchings encoded by partner identities (`mmId`). If there is a
non-uniform deterministic maximal matching algorithm using a guess `ñ ≥ n` with running time `g(ñ)`
for an ascending `g` (Hańćkowiak et al. [19]: `g(ñ) = O(log⁴ ñ)`), then there is a uniform one
running in time `O(g(n))`. -/
theorem corollary_1_vi (A : (Fin 1 → ℕ) → Alg V α (Option V)) (g : ℕ → ℝ) (hg0 : ∀ y, 0 ≤ g y)
    (hg : Tendsto g atTop atTop)
    (hA : DependsWithTime mmId allFinite ![numNodes] A (fun h => g (h 0))) :
    ∃ U : Alg V α (Option V), ∃ C : ℝ, ∀ G x, allFinite.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C * (g (numNodes G x) + 1) ∧ U.SolvesWithin mmId G x T :=
  uniform_of_numNodes mmId mmPruning (observation_3_3_repaired (V := V) (α := α)).2.1 A g hg0 hg hA

/-- **Corollary 4** (the application of Theorem 3 with `Γ = {a, n}` and `Λ = {n}`). Let `a` be a
parameter with `a ≤ n` (such as the arboricity). If a non-uniform deterministic MIS algorithm uses
guesses `ã ≥ a`, `ñ ≥ n` and, for all good guesses, runs in time `f(ñ)` for a non-decreasing
ascending `f` (the paper's reading of Barenboim–Elkin [6, Thm 6.3]), then there is a uniform
deterministic MIS algorithm running in time `O(f(n))`. -/
theorem corollary_4 (a : Param V α) (ha : ∀ G x, allFinite.mem G x → a G x ≤ numNodes G x)
    (A : (Fin 2 → ℕ) → Alg V α Bool) (f : ℕ → ℝ) (hf : Monotone f) (hf0 : ∀ y, 0 ≤ f y)
    (hinf : Tendsto f atTop atTop)
    (hA : ∀ G x, allFinite.mem G x → ∀ γ : Fin 2 → ℕ, a G x ≤ γ 0 → numNodes G x ≤ γ 1 →
      ∀ T : ℕ, f (γ 1) ≤ T → (A γ).SolvesWithin mis G x T) :
    ∃ U : Alg V α Bool, ∃ C : ℝ, ∀ G x, allFinite.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C * (f (numNodes G x) + 1) ∧ U.SolvesWithin mis G x T := by
  have hseq := observation_4_1_additive (ℓ := 1) (fun _ => f) (fun _ => hf0) (fun _ => hinf)
  obtain ⟨U, C, hU⟩ := theorem_3 mis allFinite ![a, numNodes] ![numNodes] (fun _ => some 1)
    (fun i j hij G x _ => by fin_cases i; simp at hij; subst hij; rfl)
    (fun j hj => by
      fin_cases j
      · exact ⟨0, fun y => y, fun _ _ h => by simp only; exact_mod_cast h, tendsto_natCast_atTop_atTop,
          fun G x hx => by simpa using ha G x hx⟩
      · exact absurd rfl (hj 0))
    A (fun h => f (h 0)) (fun _ _ h => hf (h 0)) (fun _ => hf0 _)
    (fun G x hx γ hγ T hT => hA G x hx γ (by simpa using hγ 0) (by simpa using hγ 1) T
      (by simpa [mixVec] using hT))
    (fun _ => 1) (by simpa using hseq) misPruning
    (fun i => by fin_cases i; exact (observation_3_2 (V := V) (α := α) 1 le_rfl).2.1)
  exact ⟨U, C, fun G x hx => by simpa [correct] using hU G x hx⟩

/-- **Corollary 1(i)** (combination step, Theorem 4): uniform MIS algorithms with running times
`O(g(n))`, `O(Δ + log* n)` and `O(f(a, n))` (for non-decreasing `g`, `f` and a non-decreasing
parameter `a`) combine into one uniform MIS algorithm running in time
`O(min {g(n), Δ + log* n, f(a, n)})`. -/
theorem corollary_1_i (a : Param V α) (ha : NonDecreasing allFinite a)
    (U₁ U₂ U₃ : Alg V α Bool) (g : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hg : Monotone g)
    (hf : ∀ a₁ a₂ n₁ n₂, a₁ ≤ a₂ → n₁ ≤ n₂ → f a₁ n₁ ≤ f a₂ n₂) (hg0 : ∀ y, 0 ≤ g y)
    (hf0 : ∀ y z, 0 ≤ f y z)
    (h₁ : ∀ G x, allFinite.mem G x → ∀ T : ℕ, g (numNodes G x) ≤ T → U₁.SolvesWithin mis G x T)
    (h₂ : ∀ G x, allFinite.mem G x → ∀ T : ℕ,
      (maxDeg G x + Nat.logStar (numNodes G x) : ℝ) ≤ T → U₂.SolvesWithin mis G x T)
    (h₃ : ∀ G x, allFinite.mem G x → ∀ T : ℕ, f (a G x) (numNodes G x) ≤ T →
      U₃.SolvesWithin mis G x T) :
    ∃ U : Alg V α Bool, ∃ C : ℝ, ∀ G x, allFinite.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C * (g (numNodes G x) + 1) ∧
      (T : ℝ) ≤ C * (maxDeg G x + Nat.logStar (numNodes G x) + 1) ∧
      (T : ℝ) ≤ C * (f (a G x) (numNodes G x) + 1) ∧ U.SolvesWithin mis G x T := by
  have hP := observation_3_2 (V := V) (α := α) 1 le_rfl
  let fs : Fin 3 → (Fin 3 → ℕ) → ℝ :=
    ![fun v => g (v 0), fun v => v 1 + Nat.logStar (v 0), fun v => f (v 2) (v 0)]
  obtain ⟨U, C, hU⟩ := theorem_4 mis allFinite 3 (by norm_num) (fun _ => 3)
    (fun _ => ![numNodes, maxDeg, a]) fs
    (fun j => by
      fin_cases j
      · exact fun v w h => hg (h 0)
      · intro v w h
        have := Nat.logStar_mono (h 0)
        simp only [fs, Fin.reduceFinMk, Matrix.cons_val]
        have h1 : (v 1 : ℝ) ≤ w 1 := by exact_mod_cast h 1
        have h2 : (Nat.logStar (v 0) : ℝ) ≤ Nat.logStar (w 0) := by exact_mod_cast this
        linarith
      · exact fun v w h => hf _ _ _ _ (h 2) (h 0))
    (fun j v => by fin_cases j <;> simp [fs] <;> first | exact hg0 _ | exact hf0 _ _ | positivity)
    ![U₁, U₂, U₃]
    (fun j G x hx T hT => by
      fin_cases j
      · exact h₁ G x hx T (by simpa [fs, correct] using hT)
      · exact h₂ G x hx T (by simpa [fs, correct, add_comm] using hT)
      · exact h₃ G x hx T (by simpa [fs, correct] using hT))
    misPruning
    (fun j i => by fin_cases i; exacts [hP.2.1, hP.2.2.1, hP.2.2.2 a ha])
  refine ⟨U, C, fun G x hx => ?_⟩
  obtain ⟨T, hT, hsol⟩ := hU G x hx
  refine ⟨T, ?_, ?_, ?_, hsol⟩
  · simpa [fs, correct] using hT 0
  · simpa [fs, correct, add_comm] using hT 1
  · simpa [fs, correct] using hT 2

end Podc.UniformLocalAlgorithms
