import Cslib.Probability.Markov.Absorption

-- CSLib candidate: Cslib/Probability/Markov/Stationary.lean

/-!
# Stationary distributions of finite Markov chains

A finite Markov chain is a row-stochastic matrix `T : Matrix S S ℝ` (as in
`Cslib.Probability.Markov.Absorption`). A distribution (row vector) `π : S → ℝ` is *stationary* if
`π ᵥ* T = π`.

## Main statements

* `IsStationary`, `IsDistribution`, `DetailedBalance`, `IsIrreducibleChain`;
* `isStationary_of_detailedBalance`: detailed balance `π s T s s' = π s' T s' s` implies
  stationarity (for row-stochastic `T`);
* `eq_zero_of_isStationary`: for an irreducible chain, a nonnegative stationary vector vanishing
  at one state vanishes everywhere;
* `IsStationary.pos`: stationary distributions of irreducible chains are strictly positive;
* `IsStationary.unique`: an irreducible finite chain has at most one stationary distribution;
* `isIrreducibleChain_of_symm`: if the positive-probability relation is symmetric, it suffices that every
  state reaches one fixed state.
-/

open Matrix Finset

namespace Cslib.Probability.Markov

variable {S : Type*} [Fintype S] {T : Matrix S S ℝ}

/-- `π` is a probability distribution on `S`. -/
def IsDistribution (π : S → ℝ) : Prop := (∀ s, 0 ≤ π s) ∧ ∑ s, π s = 1

/-- `π` is stationary for `T`: `π T = π` (row vector times matrix). -/
def IsStationary (T : Matrix S S ℝ) (π : S → ℝ) : Prop := π ᵥ* T = π

/-- The detailed balance equations `π(s) T(s,s') = π(s') T(s',s)`. -/
def DetailedBalance (T : Matrix S S ℝ) (π : S → ℝ) : Prop :=
  ∀ s s', π s * T s s' = π s' * T s' s

/-- `T` is irreducible: every state reaches every state by positive-probability steps. -/
def IsIrreducibleChain (T : Matrix S S ℝ) : Prop :=
  ∀ s s', Relation.ReflTransGen (fun a b => 0 < T a b) s s'

/-- Detailed balance implies stationarity. -/
theorem isStationary_of_detailedBalance [DecidableEq S] (hT : T ∈ rowStochastic ℝ S) {π : S → ℝ}
    (h : DetailedBalance T π) : IsStationary T π := by
  funext s'
  simp only [vecMul, dotProduct]
  calc ∑ s, π s * T s s' = ∑ s, π s' * T s' s := Finset.sum_congr rfl fun s _ => h s s'
    _ = π s' * ∑ s, T s' s := by rw [Finset.mul_sum]
    _ = π s' := by rw [sum_row_of_mem_rowStochastic hT, mul_one]

/-- For an irreducible chain with nonnegative entries, a nonnegative stationary vector that
vanishes at one state vanishes everywhere. -/
theorem eq_zero_of_isStationary (hT : ∀ s s', 0 ≤ T s s') (hirr : IsIrreducibleChain T) {ρ : S → ℝ}
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρ : IsStationary T ρ) {s₀ : S} (hs₀ : ρ s₀ = 0) (s : S) :
    ρ s = 0 := by
  -- the zero set is closed under predecessors
  have key : ∀ a b, 0 < T a b → ρ b = 0 → ρ a = 0 := by
    intro a b hab hb
    have hsum : ∑ c, ρ c * T c b = 0 := by
      have := congrFun hρ b
      simp only [vecMul, dotProduct] at this
      rw [this, hb]
    have hle : ρ a * T a b ≤ ∑ c, ρ c * T c b :=
      Finset.single_le_sum (f := fun c => ρ c * T c b)
        (fun c _ => mul_nonneg (hρ0 c) (hT c b)) (Finset.mem_univ a)
    rw [hsum] at hle
    have : ρ a * T a b = 0 := le_antisymm hle (mul_nonneg (hρ0 a) (hT a b))
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hab.ne'
  have path := hirr s s₀
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact hs₀
  | head hab _ ih => exact key _ _ hab ih

/-- Stationary distributions of irreducible chains are strictly positive. -/
theorem IsStationary.pos (hT : ∀ s s', 0 ≤ T s s') (hirr : IsIrreducibleChain T) {π : S → ℝ}
    (hd : IsDistribution π) (hπ : IsStationary T π) (s : S) : 0 < π s := by
  rcases (hd.1 s).lt_or_eq with h | h
  · exact h
  · have hz := eq_zero_of_isStationary hT hirr hd.1 hπ h.symm
    have := hd.2
    simp [hz] at this

/-- **Uniqueness of the stationary distribution** of an irreducible finite chain. -/
theorem IsStationary.unique (hT : ∀ s s', 0 ≤ T s s') (hirr : IsIrreducibleChain T) {μ ν : S → ℝ}
    (hμd : IsDistribution μ) (hμ : IsStationary T μ) (hνd : IsDistribution ν)
    (hν : IsStationary T ν) : μ = ν := by
  have hne : (Finset.univ : Finset S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hνd.2
    rw [h, Finset.sum_empty] at this
    exact zero_ne_one this
  have hνpos := hν.pos hT hirr hνd
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_min_image Finset.univ (fun s => μ s / ν s) hne
  set c := μ s₀ / ν s₀
  have hρ0 : ∀ s, 0 ≤ μ s - c * ν s := by
    intro s
    have h1 := hs₀ s (Finset.mem_univ s)
    rw [le_div_iff₀ (hνpos s)] at h1
    linarith
  have hρ : IsStationary T (μ - c • ν) := by
    unfold IsStationary at *
    rw [sub_vecMul, smul_vecMul, hμ, hν]
  have hz : ∀ s, μ s - c * ν s = 0 := by
    intro s
    have := eq_zero_of_isStationary hT hirr (ρ := μ - c • ν) (by simpa using hρ0) hρ
      (s₀ := s₀) (by simp [c, (hνpos s₀).ne']) s
    simpa using this
  have hc : c = 1 := by
    have h1 : ∑ s, μ s = c * ∑ s, ν s := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by linarith [hz s]
    rw [hμd.2, hνd.2] at h1
    linarith
  funext s
  have := hz s
  rw [hc] at this
  linarith

omit [Fintype S] in
/-- If positive-probability steps are symmetric and every state reaches a fixed state `s₀`,
then the chain is irreducible. -/
theorem isIrreducibleChain_of_symm (hsymm : ∀ a b, 0 < T a b → 0 < T b a) (s₀ : S)
    (hreach : ∀ s, Relation.ReflTransGen (fun a b => 0 < T a b) s s₀) : IsIrreducibleChain T := by
  intro s s'
  refine (hreach s).trans ?_
  have h := hreach s'
  clear hreach
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

omit [Fintype S] in
/-- With a strictly positive vector satisfying detailed balance, positive-probability steps are
symmetric. -/
theorem DetailedBalance.pos_symm {π : S → ℝ} (h : DetailedBalance T π) (hπ : ∀ s, 0 < π s)
    {a b : S} (hab : 0 < T a b) : 0 < T b a := by
  have h1 : 0 < π a * T a b := mul_pos (hπ a) hab
  rw [h a b] at h1
  exact pos_of_mul_pos_right h1 (hπ b).le

end Cslib.Probability.Markov
