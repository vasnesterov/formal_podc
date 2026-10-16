import Papers.PODC2016.VertexCoverLocalRatio.Distributed

/-!
# Theorem 3.1

Algorithm 1, run in the synchronous LOCAL model (`Distributed.lean`) with `θ = a = ε' = ε/(2+ε)`
and the greedy response rule in an arbitrary order `ord`, is a deterministic distributed
`(2+ε)`-approximation for minimum-weight vertex cover in which a vertex `v` of degree `d(v)`
completes in `O(1/ε)` rounds if `d(v) ≤ 16` and in `O(log d(v)/(ε log log d(v)))` rounds otherwise,
for `0 < ε ≤ E` (explicit constants `3(34+2E)` and `3(2+3E)`).
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph Cslib.LocallyIterative

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The configuration after `t` rounds of Algorithm 1 (LOCAL implementation) with parameter `ε`,
processing order `ord` and weights `w`. -/
noncomputable abbrev alg1Dist (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (ord : V → Finset V → List V) (w : V → ℝ) (t : ℕ) : V → NState V :=
  cfg G (epsP ε) (epsP ε) (greedyRule ord) w t

/-- The vertices that have returned `InCover` after `t` rounds. -/
noncomputable def coverAt (c : V → NState V) : Finset V := univ.filter fun v => (c v).st = .inCover

theorem nat_lt_three_mul (t : ℕ) : (t : ℝ) < 3 * (((t / 3 : ℕ) : ℝ) + 1) := by
  have : t < 3 * (t / 3 + 1) := by omega
  exact_mod_cast this

/-- **Theorem 3.1** (Bar-Yehuda, Censor-Hillel, Schwartzman). For `0 < ε ≤ E`, nonnegative
weights and any processing order:
1. (correctness, Lemma 3.2) all vertices return, and as soon as they have, the `InCover` vertices
   form a vertex cover of weight at most `(2+ε)` times the weight of any vertex cover;
2. (Lemma 3.3) a vertex `v` with `d(v) ≤ 16` has returned after `3(34+2E)/ε` rounds;
3. (Lemma 3.3) a vertex `v` with `d(v) > 16` has returned after
   `3(2+3E)·log d(v)/(ε log log d(v))` rounds;
4. a vertex that has returned never changes its state (its output is final). -/
theorem theorem_3_1 {E ε : ℝ} (hε : 0 < ε) (hεE : ε ≤ E) {ord : V → Finset V → List V}
    (hord : IsOrdering ord) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    ((∃ T, ∀ v, (alg1Dist G ε ord w T v).st ≠ .active) ∧
      ∀ t, (∀ v, (alg1Dist G ε ord w t v).st ≠ .active) →
        G.IsVertexCover ↑(coverAt (alg1Dist G ε ord w t)) ∧
        ∀ C : Finset V, G.IsVertexCover ↑C →
          wt w (coverAt (alg1Dist G ε ord w t)) ≤ (2 + ε) * wt w C) ∧
    (∀ v t, G.degree v ≤ 16 → (alg1Dist G ε ord w t v).st = .active →
      (t : ℝ) < 3 * ((34 + 2 * E) / ε)) ∧
    (∀ v t, 16 < G.degree v → (alg1Dist G ε ord w t v).st = .active →
      (t : ℝ) < 3 * ((2 + 3 * E) *
        (Real.log (G.degree v) / (ε * Real.log (Real.log (G.degree v)))))) ∧
    (∀ v t k, (alg1Dist G ε ord w t v).st ≠ .active →
      alg1Dist G ε ord w (t + k) v = alg1Dist G ε ord w t v) := by
  have h := hyp_alg1 hε hord hw
  refine ⟨⟨?_, fun t ht => ?_⟩, fun v t hd hv => ?_, fun v t hd hv => ?_,
    fun v t k hv => dist_frozen hv k⟩
  · obtain ⟨T, hT⟩ := exists_all_returned h (G := G)
    refine ⟨3 * T, fun v => ?_⟩
    rw [cfg_st, show 3 * T / 3 = T by omega]
    exact hT v
  · have hT : ∀ v, (alg1 G ε ord w (t / 3)).st v ≠ .active := fun v => by
      rw [← cfg_st]; exact ht v
    have hC : coverAt (alg1Dist G ε ord w t) = output G (epsP ε) (epsP ε) (greedyRule ord) w (t / 3) := by
      ext v; simp only [coverAt, output, mem_filter, mem_univ, true_and]; rw [cfg_st]
    rw [hC]
    obtain ⟨h1, -, h3⟩ := lemma_3_2 hε rfl h hT
    exact ⟨h1, h3⟩
  · rw [cfg_st] at hv
    have := lemma_3_3_small hε hεE hord hw hd hv
    have := nat_lt_three_mul t
    linarith
  · rw [cfg_st] at hv
    have := lemma_3_3_large hε hεE hord hw hd hv
    have := nat_lt_three_mul t
    linarith

/-- Non-vacuity: `Finset.toList` is a valid processing order, so `theorem_3_1` applies to every
finite graph, every `ε > 0` and all nonnegative weights. -/
example {ε : ℝ} (hε : 0 < ε) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    ∃ T, ∀ v, (alg1Dist G ε (fun _ S => S.toList) w T v).st ≠ .active :=
  (theorem_3_1 hε le_rfl isOrdering_toList hw).1.1

end VertexCoverLocalRatio
