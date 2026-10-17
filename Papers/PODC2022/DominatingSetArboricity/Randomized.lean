import Papers.PODC2022.DominatingSetArboricity.Deterministic
import Podc.Probability.Finite.Bernoulli
import Podc.Data.Nat.TimeRec

/-!
# The randomized extension (Lemmas 4.6–4.8, Theorems 1.2 and 1.3)

Given the output of Lemma 4.1 (a set `S`, a feasible packing `x` with `x_v ≥ λ τ_v` for every `v`
not dominated by `S`), the algorithm of Lemma 4.6 runs `t = ⌈log_γ λ⁻¹⌉` phases of
`r = ⌈log_γ (Δ+1)⌉ + 1` iterations each. In iteration `i` of a phase, every node of
`Γ = {u ∉ S ∪ S' : X_u ≥ w_u/γ}` (where `X_u` sums the packing values of the still *undominated*
vertices of `N⁺_u`) joins `S'` with probability `p_i = min(γ^i/(Δ+1), 1)`. Between phases the
packing values are multiplied by `γ`.

## Probability model

Synchronous rounds with private randomness: in step `k` every node flips an independent coin with
success probability `p_k`; the next state is a deterministic function of the current state and of
the vector of coins `c : V → Bool`. The probability of a coin vector is the product weight
`coinProb p c = ∏_u (if c u then p else 1 - p)`, and the expectation of a function of the final
state is the finite backward recursion `expect` (the expectation under the product of the
step-wise product measures). A node sampled with probability `p_k ≥ 1` is sampled regardless of its
coin.

## Proof of the expectation bound

The paper bounds the expected cost of a phase by a worst-case sequence of "degrees" `d_i`, which
ignores that the process is adaptive. We use instead the potential (`Phi`)
`Φ_i(s) = γ ∑_{v undominated} x_v (p_i d_v(s) + γ)`, `d_v = |N⁺_v ∩ Γ|`, and show that
`(sampled weight) + Φ_{i+1}` does not increase `Φ_i` in expectation (`coinExpect_bound_mid`), using
`w_Γ ≤ γ ∑ x_v d_v` (`wt_Gam_le`), `p_{i+1} ≤ γ p_i` and `(1 + p d)(1-p)^d ≤ (1-p²)^d ≤ 1`
(`key_ineq`). At the start of a phase `Φ_0 ≤ γ(γ+1) w(D)` by weak duality, because the packing
restricted to undominated vertices is feasible (`RInv`, preserved since `p = 1` in the last
iteration of every phase). The bound `expect_core` follows from a generic supermartingale
argument (`expect_le_of_super`).
-/

namespace DominatingSetArboricity

open Finset SimpleGraph Cslib.Probability

variable {V : Type*} [Fintype V] [DecidableEq V]

-- CSLib candidate (with `runCoins`, `expect_le_of_super`)
/-- Expected value of `f` of the state after `n` more random steps, starting from state `s` at
step index `k`; `p k` is the coin probability in step `k` and `step k s c` the next state. -/
noncomputable def expect {σ : Type*} (p : ℕ → ℝ) (step : ℕ → σ → (V → Bool) → σ)
    (f : σ → ℝ) : ℕ → ℕ → σ → ℝ
  | _, 0, s => f s
  | k, n + 1, s => ∑ c : V → Bool, coinProb (p k) c * expect p step f (k + 1) n (step k s c)

/-- The state after `n` steps from step index `k` for a fixed sequence of coin vectors: step
`k + j` applies `step (k + j)` with the coins `cs (k + j)`. -/
def runCoins {σ : Type*} (step : ℕ → σ → (V → Bool) → σ) (cs : ℕ → V → Bool) (k n : ℕ)
    (s : σ) : σ :=
  Nat.timeRec (fun j s => step (k + j) s (cs (k + j))) s n

/-! ### Expectation along the process -/

theorem expect_zero {σ : Type*} (p : ℕ → ℝ) (step : ℕ → σ → (V → Bool) → σ) (f : σ → ℝ)
    (k : ℕ) (s : σ) : expect p step f k 0 s = f s := rfl

theorem expect_succ {σ : Type*} (p : ℕ → ℝ) (step : ℕ → σ → (V → Bool) → σ) (f : σ → ℝ)
    (k n : ℕ) (s : σ) :
    expect p step f k (n + 1) s =
      coinExpect (p k) (fun c => expect p step f (k + 1) n (step k s c)) :=
  rfl

/-- **Supermartingale bound.** If `Ψ` is a potential that, under an invariant `I` preserved by
every step, does not increase in expectation, and dominates `f` at the final step `N`, then the
expectation of `f` after the remaining steps is bounded by the current potential. -/
theorem expect_le_of_super {σ : Type*} {p : ℕ → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    {step : ℕ → σ → (V → Bool) → σ} {f : σ → ℝ} {N : ℕ} {I : ℕ → σ → Prop} {Ψ : ℕ → σ → ℝ}
    (hI : ∀ k s c, k < N → I k s → I (k + 1) (step k s c))
    (hΨ : ∀ k s, k < N → I k s → coinExpect (p k) (fun c => Ψ (k + 1) (step k s c)) ≤ Ψ k s)
    (hf : ∀ s, I N s → f s ≤ Ψ N s) :
    ∀ n k s, k + n = N → I k s → expect p step f k n s ≤ Ψ k s := by
  intro n
  induction n with
  | zero => intro k s hk hs; subst hk; exact hf s hs
  | succ n ih =>
    intro k s hk hs
    rw [expect_succ]
    refine le_trans (coinExpect_mono (hp0 k) (hp1 k) fun c => ?_) (hΨ k s (by omega) hs)
    exact ih (k + 1) _ (by omega) (hI k s c (by omega) hs)

omit [Fintype V] [DecidableEq V] in
theorem runCoins_zero {σ : Type*} (step : ℕ → σ → (V → Bool) → σ) (cs : ℕ → V → Bool)
    (k : ℕ) (s : σ) : runCoins step cs k 0 s = s := rfl

omit [Fintype V] [DecidableEq V] in
theorem runCoins_succ' {σ : Type*} (step : ℕ → σ → (V → Bool) → σ) (cs : ℕ → V → Bool)
    (n k : ℕ) (s : σ) :
    runCoins step cs k (n + 1) s = step (k + n) (runCoins step cs k n s) (cs (k + n)) := rfl

omit [Fintype V] [DecidableEq V] in
/-- The first step, then the remaining `n` steps from step index `k + 1`. -/
theorem runCoins_succ {σ : Type*} (step : ℕ → σ → (V → Bool) → σ) (cs : ℕ → V → Bool)
    (n k : ℕ) (s : σ) :
    runCoins step cs k (n + 1) s = runCoins step cs (k + 1) n (step k s (cs k)) := by
  simp only [runCoins, Nat.timeRec_succ', Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- State of the algorithm of Lemma 4.6. -/
structure RState (V : Type*) where
  /-- the current dominating part `S ∪ S'` -/
  T : Finset V
  /-- the sampled nodes `S'` -/
  S' : Finset V
  /-- the current (scaled) packing values -/
  x : V → ℝ

/-- Undominated vertices. -/
def undom (s : RState V) : Finset V := univ.filter fun v => v ∉ dom G s.T

/-- `X_u`: sum of packing values of the undominated vertices of `N⁺_u`. -/
def Xund (s : RState V) (u : V) : ℝ := ∑ v ∈ (cnbr G u).filter (· ∈ undom G s), s.x v

/-- `Γ = {u ∉ S ∪ S' : X_u ≥ w_u / γ}`. -/
noncomputable def Gam (w : V → ℝ) (γ : ℝ) (s : RState V) : Finset V :=
  univ.filter fun u => u ∉ s.T ∧ w u / γ ≤ Xund G s u

/-- Iterations per phase: `r = ⌈log_γ (Δ+1)⌉ + 1`. -/
noncomputable def itersPerPhase (γ : ℝ) : ℕ := ⌈Real.logb γ (G.maxDegree + 1)⌉₊ + 1

/-- Number of phases: `t = ⌈log_γ λ⁻¹⌉`. -/
noncomputable def numPhases (γ lam : ℝ) : ℕ := ⌈Real.logb γ lam⁻¹⌉₊

/-- Sampling probability in global step `k` (iteration `k % r` of its phase). -/
noncomputable def sampProb (γ : ℝ) (k : ℕ) : ℝ :=
  min (γ ^ (k % itersPerPhase G γ) / (G.maxDegree + 1)) 1

/-- The nodes sampled in step `k` with coins `c`. -/
noncomputable def sampled (w : V → ℝ) (γ : ℝ) (k : ℕ) (s : RState V) (c : V → Bool) : Finset V :=
  (Gam G w γ s).filter fun u => c u = true ∨ 1 ≤ sampProb G γ k

/-- One step of Lemma 4.6's algorithm; at the end of a phase all packing values are multiplied
by `γ`. -/
noncomputable def rstep (w : V → ℝ) (γ : ℝ) (k : ℕ) (s : RState V) (c : V → Bool) : RState V :=
  ⟨s.T ∪ sampled G w γ k s c, s.S' ∪ sampled G w γ k s c,
    if k % itersPerPhase G γ = itersPerPhase G γ - 1 then fun v => γ * s.x v else s.x⟩

/-- Initial state: `T = S`, `S' = ∅`, packing `x`. -/
def rinit (S : Finset V) (x : V → ℝ) : RState V := ⟨S, ∅, x⟩

/-- Total number of steps of Lemma 4.6's algorithm. -/
noncomputable def numSteps (γ lam : ℝ) : ℕ := numPhases γ lam * itersPerPhase G γ

variable {G}

/-! ### Arithmetic of step indices and sampling probabilities -/

theorem succ_div_mod_of_eq {r k : ℕ} (hr : 0 < r) (hk : k % r = r - 1) :
    (k + 1) / r = k / r + 1 ∧ (k + 1) % r = 0 := by
  rw [Nat.div_mod_unique hr]
  have := Nat.mod_add_div k r
  refine ⟨?_, hr⟩
  rw [Nat.mul_succ]; omega

theorem succ_div_mod_of_ne {r k : ℕ} (hr : 0 < r) (hk : k % r ≠ r - 1) :
    (k + 1) / r = k / r ∧ (k + 1) % r = k % r + 1 := by
  rw [Nat.div_mod_unique hr]
  have := Nat.mod_add_div k r
  have := Nat.mod_lt k hr
  omega

omit [DecidableEq V] in
theorem itersPerPhase_pos (γ : ℝ) : 0 < itersPerPhase G γ := by
  unfold itersPerPhase; omega

omit [DecidableEq V] in
theorem sampProb_nonneg {γ : ℝ} (hγ : 0 < γ) (k : ℕ) : 0 ≤ sampProb G γ k := by
  unfold sampProb; positivity

omit [DecidableEq V] in
theorem sampProb_le_one (γ : ℝ) (k : ℕ) : sampProb G γ k ≤ 1 := min_le_right _ _

omit [DecidableEq V] in
theorem maxDeg_le_pow {γ : ℝ} (hγ : 1 < γ) :
    (G.maxDegree + 1 : ℝ) ≤ γ ^ (itersPerPhase G γ - 1) := by
  have h : itersPerPhase G γ - 1 = ⌈Real.logb γ (G.maxDegree + 1)⌉₊ := by
    unfold itersPerPhase; omega
  rw [h, ← Real.rpow_natCast]
  calc (G.maxDegree + 1 : ℝ) = γ ^ Real.logb γ (G.maxDegree + 1) :=
        (Real.rpow_logb (by linarith) hγ.ne' (by positivity)).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hγ.le (Nat.le_ceil _)

/-- In the last iteration of a phase every node of `Γ` is sampled. -/
theorem sampProb_last {γ : ℝ} (hγ : 1 < γ) {k : ℕ} (hk : k % itersPerPhase G γ =
    itersPerPhase G γ - 1) : sampProb G γ k = 1 := by
  unfold sampProb
  rw [hk, min_eq_right]
  rw [le_div_iff₀ maxDeg_pos, one_mul]
  exact maxDeg_le_pow hγ

omit [DecidableEq V] in
theorem sampProb_succ_le {γ : ℝ} (hγ : 1 ≤ γ) {k : ℕ}
    (hk : k % itersPerPhase G γ ≠ itersPerPhase G γ - 1) :
    sampProb G γ (k + 1) ≤ γ * sampProb G γ k := by
  unfold sampProb
  rw [(succ_div_mod_of_ne (itersPerPhase_pos γ) hk).2, mul_min_of_nonneg _ _ (by linarith)]
  refine le_min (min_le_left _ _ |>.trans (le_of_eq ?_)) (min_le_right _ _ |>.trans (by rw [mul_one]; exact hγ))
  ring

omit [DecidableEq V] in
theorem sampProb_first {γ : ℝ} {k : ℕ} (hk : k % itersPerPhase G γ = 0) :
    sampProb G γ k * (G.maxDegree + 1) ≤ 1 := by
  unfold sampProb
  rw [hk, pow_zero]
  calc min (1 / (G.maxDegree + 1 : ℝ)) 1 * (G.maxDegree + 1) ≤
      1 / (G.maxDegree + 1 : ℝ) * (G.maxDegree + 1) := by
        gcongr; exact min_le_left _ _
    _ = 1 := by field_simp

/-! ### Structure of a step -/

section Step

variable {w : V → ℝ} {γ : ℝ}

theorem sampled_subset (k : ℕ) (s : RState V) (c : V → Bool) :
    sampled G w γ k s c ⊆ Gam G w γ s := filter_subset _ _

theorem sampled_of_one {k : ℕ} (hk : 1 ≤ sampProb G γ k) (s : RState V) (c : V → Bool) :
    sampled G w γ k s c = Gam G w γ s := by
  unfold sampled; exact filter_true_of_mem fun u _ => Or.inr hk

/-- Almost surely, the sampled nodes are the nodes of `Γ` whose coin is `true`. -/
theorem sampled_ae {k : ℕ} {s : RState V} {c : V → Bool}
    (hc : coinProb (sampProb G γ k) c ≠ 0) :
    sampled G w γ k s c = (Gam G w γ s).filter fun u => c u = true := by
  unfold sampled
  by_cases h1 : 1 ≤ sampProb G γ k
  · have h : sampProb G γ k = 1 := le_antisymm (sampProb_le_one γ k) h1
    rw [h] at hc
    refine filter_congr fun u _ => ?_
    simp [coinProb_one_ne_zero hc u]
  · simp [h1]

theorem undom_anti {s s' : RState V} (h : s.T ⊆ s'.T) : undom G s' ⊆ undom G s := by
  intro v hv
  simp only [undom, mem_filter, mem_univ, true_and] at hv ⊢
  exact fun h' => hv (dom_mono h h')

theorem Xund_anti {s s' : RState V} (h : s.T ⊆ s'.T) (hx : s'.x = s.x)
    (hnn : ∀ v, 0 ≤ s.x v) (u : V) : Xund G s' u ≤ Xund G s u := by
  unfold Xund
  rw [hx]
  exact sum_le_sum_of_subset_of_nonneg (fun v hv => by
    simp only [mem_filter] at hv ⊢; exact ⟨hv.1, undom_anti h hv.2⟩)
    fun v _ _ => hnn v

theorem Gam_anti {s s' : RState V} (h : s.T ⊆ s'.T) (hx : s'.x = s.x)
    (hnn : ∀ v, 0 ≤ s.x v) : Gam G w γ s' ⊆ Gam G w γ s := by
  intro u hu
  simp only [Gam, mem_filter, mem_univ, true_and] at hu ⊢
  exact ⟨fun h' => hu.1 (h h'), hu.2.trans (Xund_anti h hx hnn u)⟩

theorem rstep_T (k : ℕ) (s : RState V) (c : V → Bool) :
    (rstep G w γ k s c).T = s.T ∪ sampled G w γ k s c := rfl

theorem rstep_S' (k : ℕ) (s : RState V) (c : V → Bool) :
    (rstep G w γ k s c).S' = s.S' ∪ sampled G w γ k s c := rfl

theorem rstep_x_of_eq {k : ℕ} (hk : k % itersPerPhase G γ = itersPerPhase G γ - 1)
    (s : RState V) (c : V → Bool) : (rstep G w γ k s c).x = fun v => γ * s.x v := by
  simp [rstep, hk]

theorem rstep_x_of_ne {k : ℕ} (hk : k % itersPerPhase G γ ≠ itersPerPhase G γ - 1)
    (s : RState V) (c : V → Bool) : (rstep G w γ k s c).x = s.x := by
  simp [rstep, hk]

theorem T_subset_rstep (k : ℕ) (s : RState V) (c : V → Bool) :
    s.T ⊆ (rstep G w γ k s c).T := subset_union_left

theorem x_nonneg_rstep (hγ : 0 ≤ γ) {k : ℕ} {s : RState V} (hnn : ∀ v, 0 ≤ s.x v)
    (c : V → Bool) (v : V) : 0 ≤ (rstep G w γ k s c).x v := by
  by_cases hk : k % itersPerPhase G γ = itersPerPhase G γ - 1
  · rw [rstep_x_of_eq hk]; exact mul_nonneg hγ (hnn v)
  · rw [rstep_x_of_ne hk]; exact hnn v

theorem mem_undom {s : RState V} {v : V} : v ∈ undom G s ↔ v ∉ dom G s.T := by
  simp [undom]

end Step

/-! ### The potential of Lemmas 4.7–4.8 -/

variable (G) in
/-- `d_v = |N⁺_v ∩ Γ|`. -/
noncomputable def dGam (w : V → ℝ) (γ : ℝ) (s : RState V) (v : V) : ℕ :=
  ((cnbr G v).filter (· ∈ Gam G w γ s)).card

variable (G) in
/-- The potential `Φ_k(s) = γ ∑_{v undominated} x_v (p_k d_v + γ)`, an upper bound on the expected
weight sampled in the remaining iterations of the current phase. -/
noncomputable def Phi (w : V → ℝ) (γ : ℝ) (k : ℕ) (s : RState V) : ℝ :=
  γ * ∑ v ∈ undom G s, s.x v * (sampProb G γ k * dGam G w γ s v + γ)

variable (G) in
/-- Invariant of the process: packing values are nonnegative, and at the start of every phase the
packing restricted to the undominated vertices is feasible. -/
def RInv (w : V → ℝ) (γ : ℝ) (k : ℕ) (s : RState V) : Prop :=
  (∀ v, 0 ≤ s.x v) ∧ (k % itersPerPhase G γ = 0 → ∀ u, Xund G s u ≤ w u)

section Potential

variable {w : V → ℝ} {γ : ℝ}

/-- Every node of `Γ` is paid by the packing values around it:
`w_Γ ≤ γ ∑_{v undominated} x_v d_v`. -/
theorem wt_Gam_le (hγ : 0 < γ) (s : RState V) :
    wt w (Gam G w γ s) ≤ γ * ∑ v ∈ undom G s, s.x v * dGam G w γ s v := by
  calc wt w (Gam G w γ s) = ∑ u ∈ Gam G w γ s, w u := rfl
    _ ≤ ∑ u ∈ Gam G w γ s, γ * Xund G s u := by
        refine sum_le_sum fun u hu => ?_
        have := (mem_filter.1 hu).2.2
        rw [div_le_iff₀ hγ] at this
        linarith
    _ = γ * ∑ u ∈ Gam G w γ s, ∑ v ∈ (cnbr G u).filter (· ∈ undom G s), s.x v := by
        rw [mul_sum]; rfl
    _ = γ * ∑ v ∈ undom G s, ∑ u ∈ (cnbr G v).filter (· ∈ Gam G w γ s), s.x v := by
        congr 1
        refine sum_comm' fun u v => ?_
        simp only [mem_filter]
        rw [mem_cnbr_comm]
        tauto
    _ = γ * ∑ v ∈ undom G s, s.x v * dGam G w γ s v := by
        congr 1
        refine sum_congr rfl fun v _ => ?_
        rw [sum_const, nsmul_eq_mul, mul_comm]; rfl

/-- Weak duality for the packing restricted to the undominated vertices. -/
theorem sum_undom_le {s : RState V} (hnn : ∀ v, 0 ≤ s.x v) (hfeas : ∀ u, Xund G s u ≤ w u)
    {D : Finset V} (hD : IsDominating G D) : ∑ v ∈ undom G s, s.x v ≤ wt w D := by
  have hp : IsPacking G w fun v => if v ∈ undom G s then s.x v else 0 := by
    refine ⟨fun v => by dsimp only; split_ifs <;> simp [hnn v], fun u => ?_⟩
    rw [sum_ite_mem]
    convert hfeas u using 1
    unfold Xund
    rw [filter_mem_eq_inter]
  have := sum_le_wt_of_isPacking G hp hD
  rwa [sum_ite_mem, univ_inter] at this

theorem dGam_le (s : RState V) (v : V) : dGam G w γ s v ≤ G.maxDegree + 1 :=
  (card_filter_le _ _).trans (card_cnbr_le v)

/-- At the start of a phase the potential is at most `γ(γ+1) w(D)`. -/
theorem Phi_start (hγ : 1 < γ) {k : ℕ} (hk : k % itersPerPhase G γ = 0) {s : RState V}
    (hnn : ∀ v, 0 ≤ s.x v) (hfeas : ∀ u, Xund G s u ≤ w u) {D : Finset V}
    (hD : IsDominating G D) : Phi G w γ k s ≤ γ * (γ + 1) * wt w D := by
  have hP := sampProb_first (G := G) hk
  have hP0 := sampProb_nonneg (G := G) (by linarith : (0 : ℝ) < γ) k
  calc Phi G w γ k s ≤ γ * ∑ v ∈ undom G s, s.x v * (1 + γ) := by
        unfold Phi
        gcongr with v
        · exact hnn v
        · refine le_trans ?_ hP
          gcongr
          exact_mod_cast dGam_le s v
    _ = γ * (γ + 1) * ∑ v ∈ undom G s, s.x v := by rw [← sum_mul]; ring
    _ ≤ γ * (γ + 1) * wt w D := by
        gcongr
        exact sum_undom_le hnn hfeas hD

theorem coinExpect_sampled {k : ℕ} {s : RState V} {u : V} (hu : u ∈ Gam G w γ s) :
    coinExpect (sampProb G γ k) (fun c => if u ∈ sampled G w γ k s c then 1 else 0) =
      sampProb G γ k := by
  refine (coinExpect_congr (h := fun c => if c u = true then 1 else 0) fun c hc => ?_).trans
    (coinExpect_coin _ u)
  rw [sampled_ae hc]
  simp [hu]

theorem coinExpect_undom {k : ℕ} {s : RState V} {v : V} (hv : v ∈ undom G s) :
    coinExpect (sampProb G γ k) (fun c => if v ∈ undom G (rstep G w γ k s c) then 1 else 0) =
      (1 - sampProb G γ k) ^ dGam G w γ s v := by
  rw [dGam, ← coinExpect_forall_eq_false]
  refine coinExpect_congr fun c hc => ?_
  have : v ∈ undom G (rstep G w γ k s c) ↔
      ∀ u ∈ (cnbr G v).filter (· ∈ Gam G w γ s), c u = false := by
    rw [mem_undom, rstep_T, sampled_ae hc, mem_dom]
    rw [mem_undom, mem_dom] at hv
    simp only [mem_union, mem_filter, not_exists, not_and]
    push Not at hv
    constructor
    · rintro h u ⟨hu, huG⟩
      by_contra hcu
      exact h u (Or.inr ⟨huG, by simpa using hcu⟩) hu
    · rintro h u (hu | ⟨huG, hcu⟩) hcv
      · exact hv u hu hcv
      · rw [h u ⟨hcv, huG⟩] at hcu; exact Bool.false_ne_true hcu
  by_cases h : v ∈ undom G (rstep G w γ k s c)
  · rw [ite_eq_left h, ite_eq_left (this.1 h)]
  · rw [ite_eq_right h, ite_eq_right (mt this.2 h)]

/-- `(p' d + γ)(1-p)^d ≤ γ` when `p' ≤ γ p`: the key estimate `e^{-β}(1+β) ≤ 1`, in the form
`(1 + pd)(1-p)^d ≤ (1+p)^d (1-p)^d = (1-p²)^d ≤ 1`. -/
theorem key_ineq {P P' γ : ℝ} (d : ℕ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hP' : P' ≤ γ * P)
    (hγ : 1 ≤ γ) : (P' * d + γ) * (1 - P) ^ d ≤ γ := by
  have hq : 0 ≤ (1 - P) ^ d := pow_nonneg (by linarith) d
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : 1 + d * P ≤ (1 + P) ^ d := one_add_mul_le_pow (by linarith) d
  have h2 : (1 + P) ^ d * (1 - P) ^ d = (1 - P ^ 2) ^ d := by rw [← mul_pow]; ring_nf
  have h3 : (1 - P ^ 2) ^ d ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)
  calc (P' * d + γ) * (1 - P) ^ d ≤ γ * (1 + d * P) * (1 - P) ^ d := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_right hP' hd]
    _ ≤ γ * (1 + P) ^ d * (1 - P) ^ d := by gcongr
    _ = γ * (1 - P ^ 2) ^ d := by rw [mul_assoc, h2]
    _ ≤ γ := by nlinarith

/-- The invariant is preserved by every step, for every coin vector. -/
theorem RInv_step (hw : ∀ v, 0 ≤ w v) (hγ : 1 < γ) {k : ℕ} {s : RState V}
    (h : RInv G w γ k s) (c : V → Bool) : RInv G w γ (k + 1) (rstep G w γ k s c) := by
  refine ⟨x_nonneg_rstep (by linarith) h.1 c, fun hk1 => ?_⟩
  have hr := itersPerPhase_pos (G := G) γ
  by_cases hk : k % itersPerPhase G γ = itersPerPhase G γ - 1
  · have hsamp : sampled G w γ k s c = Gam G w γ s :=
      sampled_of_one (sampProb_last hγ hk).ge s c
    intro u
    by_cases hu : u ∈ s.T ∪ Gam G w γ s
    · refine le_of_eq_of_le (sum_eq_zero fun v hv => ?_) (hw u)
      exfalso
      rw [mem_filter, mem_undom, rstep_T, hsamp] at hv
      exact hv.2 (mem_dom.2 ⟨u, hu, mem_cnbr_comm.1 hv.1⟩)
    · rw [mem_union, not_or] at hu
      have hlt : Xund G s u < w u / γ := by
        by_contra hc
        exact hu.2 (mem_filter.2 ⟨mem_univ _, hu.1, not_lt.1 hc⟩)
      have hγ0 : 0 < γ := by linarith
      calc Xund G (rstep G w γ k s c) u
          = ∑ v ∈ (cnbr G u).filter (· ∈ undom G (rstep G w γ k s c)), γ * s.x v := by
            unfold Xund; rw [rstep_x_of_eq hk]
        _ ≤ ∑ v ∈ (cnbr G u).filter (· ∈ undom G s), γ * s.x v := by
            refine sum_le_sum_of_subset_of_nonneg (fun v hv => ?_)
              fun v _ _ => mul_nonneg hγ0.le (h.1 v)
            simp only [mem_filter] at hv ⊢
            exact ⟨hv.1, undom_anti (T_subset_rstep k s c) hv.2⟩
        _ = γ * Xund G s u := by rw [Xund, mul_sum]
        _ ≤ w u := by
            have := (lt_div_iff₀ hγ0).1 hlt
            linarith
  · rw [(succ_div_mod_of_ne hr hk).2] at hk1
    omega

end Potential

/-! ### One step inside a phase -/

section MidPhase

variable {w : V → ℝ} {γ : ℝ} {f : RState V → ℝ}

/-- Pointwise bound for a step that is not the last of its phase. -/
theorem step_bound_mid (hγ : 1 < γ)
    (hf : ∀ k s c, f (rstep G w γ k s c) ≤ f s + wt w (sampled G w γ k s c)) {k : ℕ}
    (hk : k % itersPerPhase G γ ≠ itersPerPhase G γ - 1) {s : RState V}
    (hnn : ∀ v, 0 ≤ s.x v) (c : V → Bool) :
    f (rstep G w γ k s c) + Phi G w γ (k + 1) (rstep G w γ k s c) ≤
      f s + ∑ u ∈ Gam G w γ s, w u * (if u ∈ sampled G w γ k s c then 1 else 0) +
      γ * ∑ v ∈ undom G s, s.x v * (sampProb G γ (k + 1) * dGam G w γ s v + γ) *
        (if v ∈ undom G (rstep G w γ k s c) then 1 else 0) := by
  set s' := rstep G w γ k s c
  have hx : s'.x = s.x := rstep_x_of_ne hk s c
  have hT : s.T ⊆ s'.T := T_subset_rstep k s c
  have hγ0 : 0 < γ := by linarith
  have h1 : wt w (sampled G w γ k s c) =
      ∑ u ∈ Gam G w γ s, w u * (if u ∈ sampled G w γ k s c then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, inter_eq_right.2 (sampled_subset k s c)]; rfl
  have h2 : Phi G w γ (k + 1) s' ≤ γ * ∑ v ∈ undom G s, s.x v *
      (sampProb G γ (k + 1) * dGam G w γ s v + γ) * (if v ∈ undom G s' then 1 else 0) := by
    unfold Phi
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, inter_eq_right.2 (undom_anti hT), hx]
    gcongr with v
    · exact hnn v
    · exact sampProb_nonneg hγ0 _
    · exact card_le_card fun u hu => by
        simp only [mem_filter] at hu ⊢
        exact ⟨hu.1, Gam_anti hT hx hnn hu.2⟩
  linarith [hf k s c]

/-- Expected bound for a step that is not the last of its phase:
`E[sampled weight + Φ_{k+1}] ≤ Φ_k`. -/
theorem coinExpect_bound_mid (hγ : 1 < γ) {k : ℕ}
    (hk : k % itersPerPhase G γ ≠ itersPerPhase G γ - 1) {s : RState V}
    (hnn : ∀ v, 0 ≤ s.x v) :
    coinExpect (sampProb G γ k) (fun c =>
      ∑ u ∈ Gam G w γ s, w u * (if u ∈ sampled G w γ k s c then 1 else 0) +
      γ * ∑ v ∈ undom G s, s.x v * (sampProb G γ (k + 1) * dGam G w γ s v + γ) *
        (if v ∈ undom G (rstep G w γ k s c) then 1 else 0)) ≤ Phi G w γ k s := by
  have hγ0 : 0 < γ := by linarith
  set P := sampProb G γ k
  set P' := sampProb G γ (k + 1)
  have hP0 : 0 ≤ P := sampProb_nonneg hγ0 k
  rw [coinExpect_add, coinExpect_sum, coinExpect_mul_left, coinExpect_sum]
  have e1 : ∑ u ∈ Gam G w γ s,
      coinExpect P (fun c => w u * (if u ∈ sampled G w γ k s c then 1 else 0)) =
        wt w (Gam G w γ s) * P := by
    rw [wt, sum_mul]
    refine sum_congr rfl fun u hu => ?_
    rw [coinExpect_mul_left, coinExpect_sampled hu]
  have e2 : ∑ v ∈ undom G s, coinExpect P (fun c => s.x v * (P' * dGam G w γ s v + γ) *
      (if v ∈ undom G (rstep G w γ k s c) then 1 else 0)) ≤ ∑ v ∈ undom G s, s.x v * γ := by
    refine sum_le_sum fun v hv => ?_
    rw [coinExpect_mul_left, coinExpect_undom hv, mul_assoc]
    exact mul_le_mul_of_nonneg_left (key_ineq _ hP0 (sampProb_le_one γ k)
      (sampProb_succ_le hγ.le hk) hγ.le) (hnn v)
  rw [e1]
  have e3 := wt_Gam_le (G := G) (w := w) hγ0 s
  have e4 : Phi G w γ k s = γ * (∑ v ∈ undom G s, s.x v * dGam G w γ s v) * P +
      γ * ∑ v ∈ undom G s, s.x v * γ := by
    unfold Phi
    rw [mul_assoc, sum_mul, ← mul_add, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun v _ => by ring
  rw [e4]
  have := mul_le_mul_of_nonneg_right e3 hP0
  have := mul_le_mul_of_nonneg_left e2 hγ0.le
  linarith

end MidPhase

/-! ### The expected weight (Lemmas 4.7–4.8) -/

/-- Steps not at the end of a phase stay inside the run. -/
theorem succ_lt_of_ne {r t k : ℕ} (hr : 0 < r) (hk : k < t * r) (hne : k % r ≠ r - 1) :
    k + 1 < t * r := by
  have h1 := Nat.mod_add_div k r
  have h2 := Nat.mod_lt k hr
  have h3 : k / r < t := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  have h4 : r * (k / r + 1) ≤ r * t := Nat.mul_le_mul_left r h3
  rw [Nat.mul_succ, mul_comm r t] at h4
  omega

/-- **Expected weight** of the sampled nodes over `t` phases (Lemmas 4.7–4.8, via the potential
`Φ`): for any `f` that grows by at most the weight of the newly sampled nodes in each step,
`E[f(s_N)] ≤ f(s_0) + γ(γ+1) t · w(D)`, provided the initial packing restricted to undominated
vertices is feasible. -/
theorem expect_core {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {γ : ℝ} (hγ : 1 < γ) {f : RState V → ℝ}
    (hf : ∀ k s c, f (rstep G w γ k s c) ≤ f s + wt w (sampled G w γ k s c))
    {s₀ : RState V} (hnn : ∀ v, 0 ≤ s₀.x v) (hfeas : ∀ u, Xund G s₀ u ≤ w u)
    {D : Finset V} (hD : IsDominating G D) (t : ℕ) :
    expect (sampProb G γ) (rstep G w γ) f 0 (t * itersPerPhase G γ) s₀ ≤
      f s₀ + γ * (γ + 1) * t * wt w D := by
  set r := itersPerPhase G γ with hr_def
  have hr : 0 < r := itersPerPhase_pos γ
  set N := t * r
  set W := wt w D
  have hW : 0 ≤ W := sum_nonneg fun v _ => hw v
  have hγ0 : 0 < γ := by linarith
  set Ψ : ℕ → RState V → ℝ := fun k s => f s +
    if k < N then Phi G w γ k s + γ * (γ + 1) * ((t - 1 - k / r : ℕ) : ℝ) * W else 0 with hΨ
  have key := expect_le_of_super (sampProb_nonneg (G := G) hγ0) (sampProb_le_one (G := G) γ)
    (step := rstep G w γ) (f := f) (N := N) (I := RInv G w γ) (Ψ := Ψ)
    (fun k s c _ hs => RInv_step hw hγ hs c) ?_ ?_ N 0 s₀ (zero_add N) ⟨hnn, fun _ => hfeas⟩
  · refine key.trans ?_
    simp only [hΨ]
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp [N]
    · have h0 : 0 < N := Nat.mul_pos ht hr
      rw [ite_eq_left h0, Nat.zero_div, Nat.sub_zero, Nat.cast_sub ht, Nat.cast_one]
      have := Phi_start hγ (Nat.zero_mod r) hnn hfeas hD
      nlinarith
  · intro k s hk hs
    have hkt : k / r < t := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hk)
    simp only [hΨ, ite_eq_left hk]
    set R := γ * (γ + 1) * ((t - 1 - k / r : ℕ) : ℝ) * W
    have hR : 0 ≤ R := by positivity
    by_cases hlast : k % r = r - 1
    · -- last iteration of a phase: everything in `Γ` is sampled
      have hP : sampProb G γ k = 1 := sampProb_last hγ hlast
      have hsamp : ∀ c, sampled G w γ k s c = Gam G w γ s := fun c => sampled_of_one hP.ge s c
      have hdm := succ_div_mod_of_eq hr hlast
      refine (coinExpect_mono (sampProb_nonneg hγ0 k) (sampProb_le_one γ k)
        (h := fun _ => f s + (Phi G w γ k s + R)) fun c => ?_).trans (coinExpect_const _ _).le
      have hfs : f (rstep G w γ k s c) ≤ f s + Phi G w γ k s := by
        refine (hf k s c).trans ?_
        rw [hsamp]
        refine add_le_add le_rfl ((wt_Gam_le (G := G) hγ0 s).trans ?_)
        unfold Phi
        rw [hP]
        gcongr with v
        · exact hs.1 v
        · linarith
      split_ifs with h1
      · have hs' := RInv_step hw hγ hs c
        have hP' := Phi_start hγ hdm.2 hs'.1 (hs'.2 hdm.2) hD
        have h2 : (k + 1) / r < t := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h1)
        have e : t - 1 - k / r = (t - 1 - (k + 1) / r) + 1 := by omega
        simp only [R]
        rw [e]; push_cast
        nlinarith
      · linarith
    · -- inside a phase
      have hdm := succ_div_mod_of_ne hr hlast
      have h1 : k + 1 < N := succ_lt_of_ne hr hk hlast
      simp only [ite_eq_left h1, hdm.1]
      have hb := coinExpect_bound_mid (G := G) (w := w) hγ hlast hs.1
      calc coinExpect (sampProb G γ k) (fun c => f (rstep G w γ k s c) +
            (Phi G w γ (k + 1) (rstep G w γ k s c) + R))
          ≤ coinExpect (sampProb G γ k) (fun c => (f s + R) +
            (∑ u ∈ Gam G w γ s, w u * (if u ∈ sampled G w γ k s c then 1 else 0) +
            γ * ∑ v ∈ undom G s, s.x v * (sampProb G γ (k + 1) * dGam G w γ s v + γ) *
              (if v ∈ undom G (rstep G w γ k s c) then 1 else 0))) :=
            coinExpect_mono (sampProb_nonneg hγ0 k) (sampProb_le_one γ k) fun c => by
              linarith [step_bound_mid hγ hf hlast hs.1 c]
        _ = (f s + R) + coinExpect (sampProb G γ k) (fun c =>
            ∑ u ∈ Gam G w γ s, w u * (if u ∈ sampled G w γ k s c then 1 else 0) +
            γ * ∑ v ∈ undom G s, s.x v * (sampProb G γ (k + 1) * dGam G w γ s v + γ) *
              (if v ∈ undom G (rstep G w γ k s c) then 1 else 0)) := by
            rw [coinExpect_add, coinExpect_const]
        _ ≤ f s + (Phi G w γ k s + R) := by linarith
  · intro s _
    simp [hΨ, N]





/-! ### Runs for a fixed coin sequence -/

section Runs

variable {w : V → ℝ} {γ : ℝ}

theorem run_succ (cs : ℕ → V → Bool) (n : ℕ) (s : RState V) :
    runCoins (rstep G w γ) cs 0 (n + 1) s =
      rstep G w γ n (runCoins (rstep G w γ) cs 0 n s) (cs n) := by
  rw [runCoins_succ', zero_add]

/-- Along every run, the packing after `n` steps is `γ^{⌊n/r⌋} x`, and `T = S ∪ S'`. -/
theorem run_props (cs : ℕ → V → Bool) (S : Finset V) (x : V → ℝ) (n : ℕ) :
    (runCoins (rstep G w γ) cs 0 n (rinit S x)).x =
        (fun v => γ ^ (n / itersPerPhase G γ) * x v) ∧
      (runCoins (rstep G w γ) cs 0 n (rinit S x)).T =
        S ∪ (runCoins (rstep G w γ) cs 0 n (rinit S x)).S' := by
  induction n with
  | zero => exact ⟨by funext v; simp [runCoins, rinit], by simp [runCoins, rinit]⟩
  | succ n ih =>
    rw [run_succ]
    refine ⟨?_, by rw [rstep_T, rstep_S', ih.2, union_assoc]⟩
    have hr := itersPerPhase_pos (G := G) γ
    by_cases hk : n % itersPerPhase G γ = itersPerPhase G γ - 1
    · rw [rstep_x_of_eq hk, ih.1, (succ_div_mod_of_eq hr hk).1]
      funext v; ring
    · rw [rstep_x_of_ne hk, ih.1, (succ_div_mod_of_ne hr hk).1]

/-- `γ^{⌈log_γ λ⁻¹⌉} λ ≥ 1`. -/
theorem one_le_pow_numPhases_mul (hγ : 1 < γ) {lam : ℝ} (hlam : 0 < lam) :
    1 ≤ γ ^ numPhases γ lam * lam := by
  have h : lam⁻¹ ≤ γ ^ numPhases γ lam := by
    rw [numPhases, ← Real.rpow_natCast]
    calc lam⁻¹ = γ ^ Real.logb γ lam⁻¹ :=
          (Real.rpow_logb (by linarith) hγ.ne' (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hγ.le (Nat.le_ceil _)
  rw [inv_le_iff_one_le_mul₀ hlam] at h
  linarith

theorem numPhases_pos (hγ : 1 < γ) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) :
    0 < numPhases γ lam :=
  Nat.ceil_pos.2 (Real.logb_pos hγ (one_lt_inv₀ hlam |>.2 hlam1))

end Runs


/-- **Lemma 4.6** (correctness): for every outcome of the coins, `S ∪ S'` is a dominating set
after `t · r` steps, provided `0 < λ < 1`, `γ > 1`, `w ≥ 0`, `x` is a feasible packing and
`x_v ≥ λ τ_v` for every `v ∉ N⁺_S`. -/
theorem lemma_4_6_dominating {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {γ lam : ℝ} (hγ : 1 < γ)
    (hlam : 0 < lam) (hlam1 : lam < 1) {S : Finset V} {x : V → ℝ} (hx : IsPacking G w x)
    (hb : ∀ v ∉ dom G S, lam * tau G w v ≤ x v) (cs : ℕ → V → Bool) :
    IsDominating G (runCoins (rstep G w γ) cs 0 (numSteps G γ lam) (rinit S x)).T := by
  set r := itersPerPhase G γ
  set t := numPhases γ lam
  have hr : 0 < r := itersPerPhase_pos γ
  have ht : 0 < t := numPhases_pos hγ hlam hlam1
  have hγ0 : 0 < γ := by linarith
  -- the last step has index `N - 1 = (t-1) r + (r-1)`
  have hN : numSteps G γ lam = (t * r - 1) + 1 := by
    have := Nat.mul_pos ht hr; show t * r = _; omega
  have hdm : (t * r - 1) / r = t - 1 ∧ (t * r - 1) % r = r - 1 := by
    rw [Nat.div_mod_unique hr, Nat.mul_sub_one, mul_comm r t]
    have := Nat.mul_le_mul_right r (Nat.one_le_iff_ne_zero.2 ht.ne')
    constructor <;> omega
  rw [hN, run_succ]
  set s := runCoins (rstep G w γ) cs 0 (t * r - 1) (rinit S x)
  obtain ⟨hsx, hsT⟩ := run_props (G := G) (w := w) (γ := γ) cs S x (t * r - 1)
  have hP : sampProb G γ (t * r - 1) = 1 := sampProb_last hγ hdm.2
  rw [rstep_T, sampled_of_one hP.ge]
  intro v
  by_contra hv
  push Not at hv
  have hvs : v ∉ dom G s.T := fun h => by
    obtain ⟨u, hu, h'⟩ := mem_dom.1 h; exact hv u (mem_union_left _ hu) h'
  have hvS : v ∉ dom G S := fun h => hvs (dom_mono (hsT ▸ subset_union_left) h)
  set u := tauNode G w v
  have huT : u ∉ s.T := fun h => hvs (mem_dom.2 ⟨u, h, tauNode_mem w v⟩)
  have hτ : 0 ≤ tau G w v := by rw [← w_tauNode (G := G) w v]; exact hw _
  have hxv : s.x v = γ ^ (t - 1) * x v := by rw [hsx, hdm.1]
  have hnn : ∀ v, 0 ≤ s.x v := fun v => by rw [hsx]; exact mul_nonneg (by positivity) (hx.1 v)
  have hX : s.x v ≤ Xund G s u :=
    single_le_sum (f := s.x) (fun v _ => hnn v)
      (mem_filter.2 ⟨mem_cnbr_comm.1 (tauNode_mem w v), mem_undom.2 hvs⟩)
  have hpow := one_le_pow_numPhases_mul hγ hlam
  have hpow' : γ ^ t = γ ^ (t - 1) * γ := by rw [← pow_succ]; congr 1; omega
  have hwu : w u / γ ≤ s.x v := by
    rw [show w u = tau G w v from w_tauNode w v, hxv, div_le_iff₀ hγ0]
    have h1 := hb v hvS
    have h2 : 0 ≤ γ ^ (t - 1) := by positivity
    calc tau G w v ≤ tau G w v * (γ ^ t * lam) := le_mul_of_one_le_right hτ hpow
      _ = γ ^ (t - 1) * (lam * tau G w v) * γ := by rw [hpow']; ring
      _ ≤ γ ^ (t - 1) * x v * γ := by gcongr
  have huG : u ∈ Gam G w γ s := mem_filter.2 ⟨mem_univ _, huT, hwu.trans hX⟩
  exact hv u (mem_union_right _ huG) (tauNode_mem w v)

/-- **Lemmas 4.6–4.8** (expected weight): `E[w_{S'}] ≤ γ(γ+1) ⌈log_γ λ⁻¹⌉ · w(D)` for every
dominating set `D`. -/
theorem lemma_4_6_expect {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {γ lam : ℝ} (hγ : 1 < γ)
    (hlam : 0 < lam) {S : Finset V} {x : V → ℝ} (hx : IsPacking G w x)
    {D : Finset V} (hD : IsDominating G D) :
    expect (sampProb G γ) (rstep G w γ) (fun s => wt w s.S') 0 (numSteps G γ lam) (rinit S x) ≤
      γ * (γ + 1) * numPhases γ lam * wt w D := by
  have _ := hlam -- `λ > 0` is not needed for the bound
  have h := expect_core (G := G) hw hγ (f := fun s => wt w s.S')
    (fun k s c => by rw [rstep_S']; exact wt_union_le hw _ _) (s₀ := rinit S x) hx.1
    (fun u => (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun v _ _ => hx.1 v).trans
      (hx.2 u)) hD (numPhases γ lam)
  simpa [rinit, wt, numSteps] using h

/-- **Theorem 1.3**: on any graph with `Δ ≥ 1`, running Lemma 4.6's algorithm from `S = ∅`,
`x_v = τ_v/(Δ+1)`, `λ = 1/(Δ+1)` gives (for every outcome of the coins) a dominating set of
expected weight `≤ γ(γ+1)⌈log_γ(Δ+1)⌉ · w(D)` for every dominating set `D`, in
`⌈log_γ(Δ+1)⌉ (⌈log_γ(Δ+1)⌉ + 1)` steps. -/
theorem theorem_1_3 {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {γ : ℝ} (hγ : 1 < γ) (hΔ : 1 ≤ G.maxDegree)
    {D : Finset V} (hD : IsDominating G D) :
    (∀ cs, IsDominating G (runCoins (rstep G w γ) cs 0 (numSteps G γ (1 / (G.maxDegree + 1)))
        (rinit ∅ (init G w).x)).S') ∧
    expect (sampProb G γ) (rstep G w γ) (fun s => wt w s.S') 0
        (numSteps G γ (1 / (G.maxDegree + 1))) (rinit ∅ (init G w).x) ≤
      γ * (γ + 1) * ⌈Real.logb γ (G.maxDegree + 1)⌉₊ * wt w D := by
  have hΔ' : (1 : ℝ) ≤ G.maxDegree := by exact_mod_cast hΔ
  set lam : ℝ := 1 / (G.maxDegree + 1) with hlam_def
  have hlam : 0 < lam := by positivity
  have hlam1 : lam < 1 := by rw [hlam_def, div_lt_one (by positivity)]; linarith
  have hx : IsPacking G w (init G w).x := ⟨(inv_init hw 0).nonneg, (inv_init hw 0).feas⟩
  have hb : ∀ v ∉ dom G ∅, lam * tau G w v ≤ (init G w).x v := fun v _ =>
    le_of_eq (by simp only [init, hlam_def]; ring)
  refine ⟨fun cs => ?_, ?_⟩
  · have := lemma_4_6_dominating hw hγ hlam hlam1 hx hb cs
    rwa [(run_props cs ∅ _ _).2, empty_union] at this
  · have h := lemma_4_6_expect (S := ∅) hw hγ hlam hx hD
    have e : numPhases γ lam = ⌈Real.logb γ (G.maxDegree + 1)⌉₊ := by
      rw [numPhases, hlam_def, one_div, inv_inv]
    rwa [e] at h

/-- The arithmetic of Theorem 1.3 with `γ = Δ^{1/k}`: if `(Δ+1)^k ≤ Δ^{k+1}` then
`⌈log_γ(Δ+1)⌉ ≤ k + 1`, so the approximation factor is `≤ Δ^{1/k}(Δ^{1/k}+1)(k+1)` and the number
of steps is `≤ (k+1)(k+2) = O(k²)`. -/
theorem theorem_1_3_param {Δ k : ℕ} (hΔ : 2 ≤ Δ) (hk : 1 ≤ k)
    (hgap : ((Δ : ℝ) + 1) ^ k ≤ (Δ : ℝ) ^ (k + 1)) :
    ⌈Real.logb ((Δ : ℝ) ^ (1 / (k : ℝ))) (Δ + 1)⌉₊ ≤ k + 1 := by
  rw [Nat.ceil_le]
  push_cast
  have hΔ0 : (0 : ℝ) < Δ := by positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlogΔ : 0 < Real.log Δ := Real.log_pos (by exact_mod_cast hΔ)
  have h1 : (k : ℝ) * Real.log (Δ + 1) ≤ (k + 1) * Real.log Δ := by
    have := Real.log_le_log (by positivity) hgap
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    exact this
  rw [Real.logb, Real.log_rpow hΔ0, div_le_iff₀ (by positivity)]
  calc Real.log (Δ + 1) = (k * Real.log (Δ + 1)) / k := by field_simp
    _ ≤ ((k + 1) * Real.log Δ) / k := by gcongr
    _ = (k + 1) * (1 / k * Real.log Δ) := by ring

/-- **Theorem 1.2** (explicit form). Let `G` have an orientation with out-degree `≤ α`, `α ≥ 1`,
`t ≥ 1`, `γ > 1`, `w ≥ 0`. Run Lemma 4.1 with `ε = 1/(4t)`, `λ = ε/(α+1)`, then Lemma 4.6 from its
output. For every outcome of the coins the result is a dominating set, and its expected weight is
at most `(α (1 + 1/t) + γ(γ+1)⌈log_γ (4t(α+1))⌉) · w(D)` for every dominating set `D`. -/
theorem theorem_1_2 {α : ℕ} (o : G.OutOrientation α) (hα : 1 ≤ α) {t : ℕ} (ht : 1 ≤ t)
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {γ : ℝ} (hγ : 1 < γ) {D : Finset V} (hD : IsDominating G D) :
    let ε : ℝ := 1 / (4 * t)
    let lam : ℝ := ε / (α + 1)
    let p := partialDS G ε lam w
    (∀ cs, IsDominating G (runCoins (rstep G w γ) cs 0 (numSteps G γ lam) (rinit p.S p.x)).T) ∧
    expect (sampProb G γ) (rstep G w γ) (fun s => wt w s.T) 0 (numSteps G γ lam)
        (rinit p.S p.x) ≤
      (α * (1 + 1 / t) + γ * (γ + 1) * ⌈Real.logb γ (4 * t * (α + 1))⌉₊) * wt w D := by
  intro ε lam p
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hα' : (1 : ℝ) ≤ α := by exact_mod_cast hα
  have hε : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by
    simp only [ε]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h4ε : 4 * ε = 1 / t := by simp only [ε]; field_simp
  have hlam0 : 0 < lam := by positivity
  have hlamε : lam * (α + 1) = ε := by simp only [lam]; field_simp
  have hlam' : lam < 1 / ((α + 1) * (1 + ε)) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hlam1 : lam < 1 := by nlinarith
  obtain ⟨hpack, ha, hb⟩ := lemma_4_1 o hw hε hlam0.le hlam'
  refine ⟨fun cs => lemma_4_6_dominating hw hγ hlam0 hlam1 hpack hb cs, ?_⟩
  set W := wt w D
  have hW : 0 ≤ W := sum_nonneg fun v _ => hw v
  -- the deterministic part
  have hsum : ∑ v ∈ dom G p.S, p.x v ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => hpack.1 v).trans
      (sum_le_wt_of_isPacking G hpack hD)
  have hsum0 : 0 ≤ ∑ v ∈ dom G p.S, p.x v := sum_nonneg fun v _ => hpack.1 v
  set c := 1 / (1 + ε) - lam * (α + 1) with hc_def
  have hc : 1 ≤ (1 + 1 / t) * c := by
    rw [hc_def, hlamε, ← h4ε]
    have e : (1 + 4 * ε) * (1 / (1 + ε) - ε) - 1 = ε * (2 - 5 * ε - 4 * ε ^ 2) / (1 + ε) := by
      field_simp; ring
    have : 0 ≤ ε * (2 - 5 * ε - 4 * ε ^ 2) / (1 + ε) := by
      apply div_nonneg _ (by linarith)
      apply mul_nonneg hε.le
      nlinarith
    linarith
  have hcpos : 0 < c := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + 1 / t) (neg_nonneg.2 h)]
  have hcinv : c⁻¹ ≤ 1 + 1 / t := (inv_le_iff_one_le_mul₀ hcpos).2 hc
  have hS : wt w p.S ≤ α * (1 + 1 / t) * W := by
    refine ha.trans ?_
    calc α * c⁻¹ * ∑ v ∈ dom G p.S, p.x v ≤ α * (1 + 1 / t) * ∑ v ∈ dom G p.S, p.x v := by
          gcongr
      _ ≤ α * (1 + 1 / t) * W := by gcongr
  -- the randomized part
  have h := expect_core (G := G) hw hγ (f := fun s => wt w s.T)
    (fun k s c => by rw [rstep_T]; exact wt_union_le hw _ _) (s₀ := rinit p.S p.x) hpack.1
    (fun u => (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun v _ _ => hpack.1 v).trans
      (hpack.2 u)) hD (numPhases γ lam)
  have e : numPhases γ lam = ⌈Real.logb γ (4 * t * (α + 1))⌉₊ := by
    rw [numPhases]
    congr 3
    simp only [lam, ε]
    field_simp
  rw [e] at h
  change _ ≤ wt w p.S + _ at h
  unfold numSteps
  rw [e]
  nlinarith

end DominatingSetArboricity
