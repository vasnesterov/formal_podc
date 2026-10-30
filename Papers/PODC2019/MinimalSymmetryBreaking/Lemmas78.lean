import Papers.PODC2019.MinimalSymmetryBreaking.Chain

/-!
# Lemmas 7, 8, 14, 15 as stated in the paper

The paper states the speedup lemmas with explicit failure bounds, e.g. Lemma 7: from a `t`-round
weak `c`-colouring algorithm with local failure probability `p` one gets a `(t−1)`-round edge
algorithm for weak edge `2^(2c)`-colouring with local failure probability
`p' ≤ 5 p^(1/5) c^(4/5)`. Its proof chooses the threshold `f = p'/(5c)`, which depends on the
failure probability `p'` of the algorithm built with that very threshold (a circular choice). We
instead choose `f = q/(5c)` for the target bound `q = 5 p^(1/5) c^(4/5)` and argue by
contradiction; this needs `p > 0`, which holds for every algorithm on the infinite tree
(`NodeAlg.failProb_pos`, a consequence of Claim 11).

General `Δ = 2k` (Lemmas 14 and 15); `Δ = 4` (`k = 2`) gives Lemmas 7 and 8.
-/

namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

variable {k : ℕ} {Ω : Type} [Fintype Ω] [Inhabited Ω] {μ : FinDist Ω}

lemma lb_pos : ∀ t c, 1 ≤ c → 0 < lb k t c
  | 0, c, hc => by
    simp only [lb]; have : (0 : ℝ) < c := by exact_mod_cast hc
    positivity
  | t + 1, c, hc => by
    simp only [lb, phi1, phi2]
    have := lb_pos t (nodePal k c) (one_le_two_pow _)
    have : (0 : ℝ) < c := by exact_mod_cast hc
    have : (0 : ℝ) < 2 ^ (2 * c) := by positivity
    have hk : (0 : ℝ) ≤ k := by positivity
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · have : (0 : ℝ) < k := by exact_mod_cast h
      positivity

/-- On the infinite tree every node algorithm fails locally with positive probability. -/
theorem NodeAlg.failProb_pos (hk : 0 < k) {t : ℕ} {α : Type} [Fintype α] (A : NodeAlg k Ω t α) :
    0 < A.failProb μ := by
  have hne : Nonempty α := ⟨A.out (fun _ => default)⟩
  exact lt_of_lt_of_le (lb_pos t (Fintype.card α) Fintype.card_pos)
    (nodeLB_lb (μ := μ) hk t _ Fintype.card_pos α le_rfl A)

/-- On the infinite tree every edge algorithm fails locally with positive probability. -/
theorem EdgeAlg.failProb_pos (hk : 0 < k) {t : ℕ} {β : Type} [Fintype β] (B : EdgeAlg k Ω t β) :
    0 < B.failProb μ := by
  have hne : Nonempty β := ⟨B.out ⟨0, hk⟩ (fun _ => default)⟩
  have hc : 1 ≤ Fintype.card β := Fintype.card_pos
  have h := edgeLB_of_nodeLB (μ := μ) hk hc (lb_nonneg _ _)
    (nodeLB_lb (μ := μ) hk t (2 ^ (2 * k * Fintype.card β)) (one_le_two_pow _)) β le_rfl B
  refine lt_of_lt_of_le ?_ h
  unfold phi2
  have := lb_pos (k := k) t (2 ^ (2 * k * Fintype.card β)) (one_le_two_pow _)
  have : (0 : ℝ) < k := by exact_mod_cast hk
  have : (0 : ℝ) < Fintype.card β := by exact_mod_cast hc
  positivity

/-- **Lemma 14** (Lemma 7 for `Δ = 4`, first speedup lemma). Let `A` be a `t`-round weak
`c`-colouring algorithm with local failure probability `p`. Then there is a `(t−1)`-round edge
algorithm for weak edge `2^(2c)`-colouring (colours: pairs of subsets of the `c` colours) with
local failure probability `p' ≤ (Δ+1) p^(1/(Δ+1)) c^(Δ/(Δ+1))`. -/
theorem lemma_14 (hk : 0 < k) {t : ℕ} {α : Type} [Fintype α] (A : NodeAlg k Ω (t + 1) α) :
    ∃ B : EdgeAlg k Ω t (Finset α × Finset α),
      B.failProb μ ≤ (2 * k + 1) * (A.failProb μ) ^ ((1 : ℝ) / (2 * k + 1)) *
        (Fintype.card α : ℝ) ^ ((2 * k : ℝ) / (2 * k + 1)) := by
  set p := A.failProb μ
  set c : ℝ := (Fintype.card α : ℝ)
  have hne : Nonempty α := ⟨A.out (fun _ => default)⟩
  have hc : 0 < c := by simp only [c]; exact_mod_cast Fintype.card_pos
  have hp : 0 < p := A.failProb_pos hk
  set n : ℝ := 2 * k + 1
  have hn : 0 < n := by positivity
  set q := n * p ^ (1 / n) * c ^ (2 * k / n)
  have hq : 0 < q := by positivity
  set f := q / (n * c)
  have hf : 0 < f := by positivity
  refine ⟨speedEdge μ A f, ?_⟩
  by_contra hcon
  push_neg at hcon
  have key := speedup1_ineq (μ := μ) A hf.le
  -- `(q / n)^(2k+1) = p c^(2k)`
  have hpow : (q / n) ^ (2 * k + 1) = p * c ^ (2 * k) := by
    have e : q / n = p ^ (1 / n) * c ^ (2 * k / n) := by
      simp only [q]; field_simp
    rw [e, mul_pow, ← Real.rpow_natCast (p ^ (1 / n)), ← Real.rpow_natCast (c ^ (2 * k / n)),
      ← Real.rpow_mul hp.le, ← Real.rpow_mul hc.le]
    have h1 : 1 / n * ((2 * k + 1 : ℕ) : ℝ) = 1 := by
      simp only [n]; push_cast; field_simp
    have h2 : 2 * k / n * ((2 * k + 1 : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by
      simp only [n]; push_cast; field_simp
    rw [h1, h2, Real.rpow_one, Real.rpow_natCast]
  have hlt : p < f ^ (2 * k) * ((speedEdge μ A f).failProb μ - 2 * k * c * f) := by
    have h1 : f ^ (2 * k) * (q - 2 * k * c * f) = p := by
      have e1 : q - 2 * k * c * f = q / n := by simp only [f, n]; field_simp; ring
      have e2 : f = q / n / c := by simp only [f]; rw [div_div]
      rw [e1, e2, div_pow, show (q / n) ^ (2 * k) / c ^ (2 * k) * (q / n) =
        (q / n) ^ (2 * k + 1) / c ^ (2 * k) by ring, hpow]
      field_simp
    rw [← h1]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    linarith
  linarith

/-- **Lemma 15** (Lemma 8 for `Δ = 4`, second speedup lemma). Let `B` be a `t`-round weak edge
`c`-colouring algorithm with local failure probability `p`. Then there is a `t`-round algorithm
for weak `2^(Δc)`-colouring (colours: one subset of the `c` edge colours per incident edge) with
local failure probability `p' ≤ Δ p^(1/Δ) c^(1−1/Δ)`. -/
theorem lemma_15 (hk : 0 < k) {t : ℕ} {β : Type} [Fintype β] (B : EdgeAlg k Ω t β) :
    ∃ A : NodeAlg k Ω t (Fin k × Bool → Finset β),
      A.failProb μ ≤ (2 * k) * (B.failProb μ) ^ ((1 : ℝ) / (2 * k)) *
        (Fintype.card β : ℝ) ^ (1 - (1 : ℝ) / (2 * k)) := by
  set p := B.failProb μ
  set c : ℝ := (Fintype.card β : ℝ)
  have hne : Nonempty β := ⟨B.out ⟨0, hk⟩ (fun _ => default)⟩
  have hc : 0 < c := by simp only [c]; exact_mod_cast Fintype.card_pos
  have hp : 0 < p := B.failProb_pos hk
  set n : ℝ := 2 * k
  have hn : 0 < n := by positivity
  set q := n * p ^ (1 / n) * c ^ (1 - 1 / n)
  have hq : 0 < q := by positivity
  set f := q / (n * c)
  have hf : 0 < f := by positivity
  refine ⟨speedNode μ B f, ?_⟩
  by_contra hcon
  push_neg at hcon
  have key := speedup2_ineq (μ := μ) hk B hf.le
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
  have hm' : 2 * k - 1 = m := by omega
  rw [hm'] at key
  have hnm : n = m + 1 := by simp only [n]; exact_mod_cast hm
  have hpow : (q / n) ^ (m + 1) = p * c ^ m := by
    have e : q / n = p ^ (1 / n) * c ^ (1 - 1 / n) := by
      simp only [q]; field_simp
    rw [e, mul_pow, ← Real.rpow_natCast (p ^ (1 / n)), ← Real.rpow_natCast (c ^ (1 - 1 / n)),
      ← Real.rpow_mul hp.le, ← Real.rpow_mul hc.le]
    have h1 : 1 / n * ((m + 1 : ℕ) : ℝ) = 1 := by
      rw [hnm]; push_cast; field_simp
    have h2 : (1 - 1 / n) * ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) := by
      rw [hnm]; push_cast; field_simp; ring
    rw [h1, h2, Real.rpow_one, Real.rpow_natCast]
  have hlt : p < f ^ m * ((speedNode μ B f).failProb μ - (2 * k - 1) * c * f) := by
    have h1 : f ^ m * (q - (2 * k - 1) * c * f) = p := by
      have e1 : q - (2 * k - 1) * c * f = q / n := by
        simp only [f]; rw [show (2 * k - 1 : ℝ) = n - 1 by simp [n]]; field_simp; ring
      have e2 : f = q / n / c := by simp only [f]; rw [div_div]
      rw [e1, e2, div_pow, show (q / n) ^ m / c ^ m * (q / n) = (q / n) ^ (m + 1) / c ^ m by ring,
        hpow]
      field_simp
    rw [← h1]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    linarith
  linarith

end

end Podc.MinimalSymmetryBreaking
