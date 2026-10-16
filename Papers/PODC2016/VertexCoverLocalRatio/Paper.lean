import Papers.PODC2016.VertexCoverLocalRatio.Rounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The paper's parameters: Lemmas 3.2 and 3.3 for Algorithm 1

Algorithm 1 is the iteration of `Algorithm.lean` with `vault(v) = ε'·w_0(v)` (`a = ε'`), threshold
`θ = ε'`, and the greedy response rule of line 20 in an arbitrary order `ord` (slack `σ = 0`),
where `ε' = ε/(2+ε)`.

* `alg1_correct` (Lemma 3.2): once everybody has returned, the `InCover` vertices form a vertex
  cover of weight `≤ (2+ε)·w(C)` for every vertex cover `C`; everybody does return.
* `lemma_3_3_small`, `lemma_3_3_large` (Lemma 3.3): a vertex of degree `d` takes part in at most
  `(34+2E)/ε` iterations if `d ≤ 16`, and at most `(2+3E)·log d/(ε·log log d)` iterations if
  `d > 16`, whenever `0 < ε ≤ E` (natural logarithms).
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem epsP_pos {ε : ℝ} (hε : 0 < ε) : 0 < epsP ε := div_pos hε (by linarith)

theorem epsP_lt_one {ε : ℝ} (hε : 0 < ε) : epsP ε < 1 := by
  unfold epsP; rw [div_lt_one (by linarith)]; linarith

/-- `(1 - ε')/ε' = 2/ε`. -/
theorem one_sub_epsP_div {ε : ℝ} (hε : 0 < ε) (K : ℝ) : K * (1 - epsP ε) / epsP ε = 2 * K / ε := by
  unfold epsP
  field_simp
  ring

/-- The paper's parameters satisfy the hypotheses. -/
theorem hyp_alg1 {ε : ℝ} (hε : 0 < ε) {ord : V → Finset V → List V} (hord : IsOrdering ord)
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) : Hyp (epsP ε) (epsP ε) 0 (greedyRule ord) w where
  ha := epsP_pos hε
  hσ := le_rfl
  haσ := by simp
  hθ := epsP_lt_one hε
  hR := greedy_spec hord
  hw0 := hw

/-- The global state of Algorithm 1 at the beginning of iteration `i`. -/
noncomputable abbrev alg1 (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (ord : V → Finset V → List V) (w : V → ℝ) (i : ℕ) : GState V :=
  run G (epsP ε) (epsP ε) (greedyRule ord) w i

/-- **Lemma 3.2** for Algorithm 1: every vertex returns; after that, the set of vertices that
returned `InCover` is a vertex cover whose weight is at most `(2+ε)` times the weight of any vertex
cover (in particular of a minimum-weight one). Holds for every processing order. -/
theorem alg1_correct {ε : ℝ} (hε : 0 < ε) {ord : V → Finset V → List V} (hord : IsOrdering ord)
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    (∃ T, ∀ v, (alg1 G ε ord w T).st v ≠ .active) ∧
    ∀ T, (∀ v, (alg1 G ε ord w T).st v ≠ .active) →
      let C := univ.filter fun v => (alg1 G ε ord w T).st v = .inCover
      G.IsVertexCover ↑C ∧ ∀ C' : Finset V, G.IsVertexCover ↑C' → wt w C ≤ (2 + ε) * wt w C' :=
  ⟨exists_all_returned (hyp_alg1 hε hord hw), fun _ hT =>
    let h := lemma_3_2 hε rfl (hyp_alg1 hε hord hw) hT
    ⟨h.1, h.2.2⟩⟩

/-- The bound of the proof of Lemma 3.3 with the paper's parameters: if `v` is still running at
the beginning of iteration `n`, then `n ≤ 2K/ε + log d(v)/log K` for all `K > 1`. -/
theorem alg1_active_bound {ε : ℝ} (hε : 0 < ε) {ord : V → Finset V → List V}
    (hord : IsOrdering ord) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {v : V} {n : ℕ}
    (hv : (alg1 G ε ord w n).st v = .active) {K : ℝ} (hK : 1 < K) :
    (n : ℝ) ≤ 2 * K / ε + Real.log (G.degree v) / Real.log K := by
  have := active_bound (hyp_alg1 hε hord hw) hv hK
  rwa [one_sub_epsP_div hε] at this

/-! ### From the exact bound to the asymptotic one

`small_of_bound` / `large_of_bound`: if `n ≤ c·K/ε + log d/log K` for every `K > 1`, then
`n + 1 ≤ (17c + 2E)/ε` when `d ≤ 16` and `n + 1 ≤ (c + 3E)·log d/(ε·log log d)` when `d > 16`
(for `0 < ε ≤ E`). Algorithm 1 has `c = 2`; the CONGEST variant of Section 4 has `c = 4`. -/

theorem small_of_bound {E ε c : ℝ} (hε : 0 < ε) (hεE : ε ≤ E) (hc : 0 ≤ c) {d n : ℕ}
    (hd : d ≤ 16) (hb : ∀ K : ℝ, 1 < K → (n : ℝ) ≤ c * K / ε + Real.log d / Real.log K) :
    (n : ℝ) + 1 ≤ (17 * c + 2 * E) / ε := by
  have hE2 : 2 ≤ 2 * E / ε := by
    rw [mul_div_assoc]; have : 1 ≤ E / ε := by rw [le_div_iff₀ hε]; linarith
    linarith
  rw [add_div]
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · have := hb 2 one_lt_two
    rw [h0, Nat.cast_zero, Real.log_zero, zero_div, add_zero] at this
    have h4 : c * 2 / ε ≤ 17 * c / ε := div_le_div_of_nonneg_right (by linarith) hε.le
    linarith
  · have hd1 : (1 : ℝ) < d + 1 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast h0
      linarith
    have := hb _ hd1
    have hlog : Real.log d / Real.log (d + 1) ≤ 1 := by
      rw [div_le_one (Real.log_pos hd1)]
      exact Real.log_le_log (by exact_mod_cast h0) (by linarith)
    have hK : c * ((d : ℝ) + 1) / ε ≤ 17 * c / ε := by
      apply div_le_div_of_nonneg_right _ hε.le
      have : (d : ℝ) ≤ 16 := by exact_mod_cast hd
      nlinarith
    linarith

/-- `log y ≤ y/2` for `y > 0`. -/
theorem log_le_half {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / 2 := by
  have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < y / 2)
  rw [Real.log_div hy.ne' two_ne_zero] at h1
  have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
  linarith

theorem large_of_bound {E ε c : ℝ} (hε : 0 < ε) (hεE : ε ≤ E) {d n : ℕ}
    (hd : 16 < d) (hb : ∀ K : ℝ, 1 < K → (n : ℝ) ≤ c * K / ε + Real.log d / Real.log K) :
    (n : ℝ) + 1 ≤ (c + 3 * E) * (Real.log d / (ε * Real.log (Real.log d))) := by
  set L := Real.log d
  set LL := Real.log L
  have hd' : (16 : ℝ) < d := by exact_mod_cast hd
  have hL1 : 1 < L := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hLL : 0 < LL := Real.log_pos hL1
  have hLLL : LL < L := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < L); linarith
  set K := L / LL
  have hK1 : 1 < K := by rw [lt_div_iff₀ hLL]; linarith
  have hlogK : LL / 2 ≤ Real.log K := by
    rw [Real.log_div (by linarith) hLL.ne']
    have := log_le_half hLL
    linarith
  have h1 := hb K hK1
  have h2 : L / Real.log K ≤ 2 * K := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ K := by linarith
    calc L = 2 * K * (LL / 2) := by simp only [K]; field_simp
      _ ≤ 2 * K * Real.log K := by gcongr
  have hEK : K ≤ E * K / ε := by
    rw [show E * K / ε = K * (E / ε) by ring]
    have : 1 ≤ E / ε := by rw [le_div_iff₀ hε]; linarith
    nlinarith
  have hgoal : (c + 3 * E) * (L / (ε * LL)) = c * K / ε + 3 * (E * K / ε) := by
    simp only [K]; field_simp
  rw [hgoal]
  linarith

/-- **Lemma 3.3**, case `d(v) ≤ 16`: `v` takes part in at most `(34 + 2E)/ε = O(1/ε)` iterations
(if `v` is running at the beginning of iteration `n`, then `n + 1 ≤ (34+2E)/ε`). -/
theorem lemma_3_3_small {E ε : ℝ} (hε : 0 < ε) (hεE : ε ≤ E) {ord : V → Finset V → List V}
    (hord : IsOrdering ord) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {v : V} (hd : G.degree v ≤ 16)
    {n : ℕ} (hv : (alg1 G ε ord w n).st v = .active) :
    (n : ℝ) + 1 ≤ (34 + 2 * E) / ε := by
  have := small_of_bound hε hεE zero_le_two hd fun _ hK => alg1_active_bound hε hord hw hv hK
  norm_num at this ⊢; exact this

/-- **Lemma 3.3**, case `d(v) > 16`: with `K_v = log d/log log d`, `v` takes part in at most
`(2 + 3E)·log d/(ε·log log d) = O(log d/(ε log log d))` iterations. -/
theorem lemma_3_3_large {E ε : ℝ} (hε : 0 < ε) (hεE : ε ≤ E) {ord : V → Finset V → List V}
    (hord : IsOrdering ord) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {v : V} (hd : 16 < G.degree v)
    {n : ℕ} (hv : (alg1 G ε ord w n).st v = .active) :
    (n : ℝ) + 1 ≤
      (2 + 3 * E) * (Real.log (G.degree v) / (ε * Real.log (Real.log (G.degree v)))) :=
  large_of_bound hε hεE hd fun _ hK => alg1_active_bound hε hord hw hv hK

end VertexCoverLocalRatio
