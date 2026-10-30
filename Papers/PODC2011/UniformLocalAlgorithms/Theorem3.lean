import Papers.PODC2011.UniformLocalAlgorithms.Theorem1
import Papers.PODC2011.UniformLocalAlgorithms.Observation41

/-!
# Theorem 3: correctness parameters `Γ` and running-time parameters `Λ` (Section 4.5,
deterministic case)

The non-uniform algorithm `A_Γ` needs guesses for the parameters `Γ = (p_1, …, p_r)`, while its
running time is a function `f` of the parameters `Λ = (q_1, …, q_ℓ)`. Some parameters may be shared:
`σ i = some j` means `q_i = p_j`. With good guesses `γ` for `Γ`, the running time is at most
`f(w)` where `w_i` is the guess `γ j` if `q_i = p_j` is shared, and the correct value `q_i(G, x)`
otherwise (`mixVec`). `Γ` is *weakly dominated* by `Λ`: each non-shared `p_j` satisfies
`g_j(p_j) ≤ q_{i_j}` for some `i_j` and some ascending `g_j`.

* `theorem_3`: Theorem 3 (deterministic case). Our proof is a direct reduction to Theorem 1: guesses
  for `Γ` are computed from guesses for `Λ` by `γ_j = max {y : g_j(y) ≤ q̃_{i_j}}` (the paper's
  `g_j⁻¹(x) = min g_j⁻¹({x})` is undefined when `x` is not a value of `g_j`). Only
  `Λ`-monotonicity of the pruning algorithm is needed (the paper assumes `Λ ∪ Γ`).
-/

open Filter

namespace Podc.UniformLocalAlgorithms

variable {V α β : Type*} {r ℓ : ℕ}

/-- The argument of the running-time bound: the guess for a shared parameter, the correct value of
a parameter that is not a correctness parameter. -/
def mixVec (Λ : Fin ℓ → Param V α) (σ : Fin ℓ → Option (Fin r)) (γ : Fin r → ℕ)
    (G : SimpleGraph V) (x : V → Option α) : Fin ℓ → ℕ :=
  fun i => match σ i with
    | some j => γ j
    | none => Λ i G x

/-- `Γ` is weakly dominated by `Λ` (Section 2): every correctness parameter `p_j` that is not
shared is bounded, after applying an ascending function `g_j`, by some running-time parameter. -/
def WeaklyDominated (F : Family V α) (Γ : Fin r → Param V α) (Λ : Fin ℓ → Param V α)
    (σ : Fin ℓ → Option (Fin r)) : Prop :=
  ∀ j, (∀ i, σ i ≠ some j) → ∃ (i : Fin ℓ) (g : ℕ → ℝ), Monotone g ∧ Tendsto g atTop atTop ∧
    ∀ G x, F.mem G x → g (Γ j G x) ≤ Λ i G x

/-- **Theorem 3** of [Korman–Sereni–Viennot] (deterministic case). Let `Γ` be weakly dominated by
`Λ`, and let `A_Γ` be a deterministic algorithm depending on `Γ` whose running time with good
guesses is bounded, with respect to `Γ` and `Λ`, by a non-decreasing `f : ℕ^ℓ → ℝ_{≥0}` with a
sequence-number function `s_f`. If there is a `Λ`-monotone pruning algorithm for `Π` and `F`, then
there is a uniform deterministic algorithm for `Π` and `F` with running time `O(f* · s_f(f*))`,
`f* = f(Λ*(G, x))` (precisely: at most `C · (f* · s_f(⌊f*⌋) + 1)`). -/
theorem theorem_3 [Inhabited β] (Pb : Problem V α β) (F : Family V α) (Γ : Fin r → Param V α)
    (Λ : Fin ℓ → Param V α) (σ : Fin ℓ → Option (Fin r))
    (hσ : ∀ i j, σ i = some j → ∀ G x, F.mem G x → Γ j G x = Λ i G x)
    (hdom : WeaklyDominated F Γ Λ σ)
    (A : (Fin r → ℕ) → Alg V α β) (f : (Fin ℓ → ℕ) → ℝ) (hf : Monotone f) (hf0 : ∀ g, 0 ≤ f g)
    (hA : ∀ G x, F.mem G x → ∀ γ : Fin r → ℕ, (∀ j, Γ j G x ≤ γ j) →
      ∀ T : ℕ, f (mixVec Λ σ γ G x) ≤ T → (A γ).SolvesWithin Pb G x T)
    (sf : ℕ → ℕ) (hsf : IsSeqNumber f sf) (P : Pruning Pb F) (hP : ∀ i, P.Monotone (Λ i)) :
    ∃ U : Alg V α β, ∃ C : ℝ, ∀ G x, F.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C * (f (correct Λ G x) * sf ⌊f (correct Λ G x)⌋₊ + 1) ∧
      U.SolvesWithin Pb G x T := by
  classical
  -- for every non-shared correctness parameter, a running-time parameter dominating it
  choose idx g _ hg hgdom using hdom
  -- guesses for `Γ` computed from guesses `h` for `Λ`
  let γ : (Fin ℓ → ℕ) → Fin r → ℕ := fun h j =>
    if hj : ∃ i, σ i = some j then sInf {n | ∃ i, σ i = some j ∧ h i = n}
    else maxLe (g j (not_exists.mp hj)) (h (idx j (not_exists.mp hj)))
  apply theorem_1 Pb F Λ (fun h => A (γ h)) f hf0 _ sf hsf P hP
  intro G x hx h hh T hT
  have hgood : ∀ j, Γ j G x ≤ γ h j := by
    intro j
    by_cases hj : ∃ i, σ i = some j
    · simp only [γ, hj, ↓reduceDIte]
      obtain ⟨i, hi, hin⟩ := Nat.sInf_mem (s := {n | ∃ i, σ i = some j ∧ h i = n})
        (by obtain ⟨i, hi⟩ := hj; exact ⟨h i, i, hi, rfl⟩)
      rw [← hin, hσ i j hi G x hx]
      exact hh i
    · simp only [γ, hj, ↓reduceDIte]
      exact le_maxLe (hg j _) ((hgdom j _ G x hx).trans (by exact_mod_cast hh _))
  have hmix : mixVec Λ σ (γ h) G x ≤ h := by
    intro i
    simp only [mixVec]
    split
    · rename_i j hj
      have hex : ∃ i, σ i = some j := ⟨i, hj⟩
      simp only [γ, hex, ↓reduceDIte]
      exact Nat.sInf_le ⟨i, hj, rfl⟩
    · exact hh i
  exact hA G x hx (γ h) hgood T ((hf hmix).trans hT)

end Podc.UniformLocalAlgorithms
