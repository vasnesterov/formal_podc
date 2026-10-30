import Papers.PODC2016.BoundedGenusMDS.Lemma12

/-!
# Theorem 13: bounded genus

Mathlib has no surfaces or graph genus, so the genus facts of Section 2 enter as hypotheses:

* `EulerEdgeBound G g`: every depth-1 minor `H` of `G` has `|E(H)| ≤ 3|V(H)| + 6g`
  (Lemma 1: depth-1 minors of a graph of genus `≤ g` have genus `≤ g`; Lemma 4: Euler's bound
  `|E| ≤ 3|V| + 6g − 6`, resp. `3|V| + 3g̃ − 3`);
* `ExcludesKt3 G (4g + 3)` (Lemma 2: `K_{4g+3,3}` has orientable genus `g + 1`).

From these we get `Depth1DensityLE G c` with `c = 3 + ⌊√(3g)⌋ + 1` (`depth1DensityLE_of_euler`),
and Lemma 12 gives an approximation factor `≤ 1100 (g + 1)²` (`theorem_13`, `factor_le`).

The paper claims an `O(g)` approximation. Its proof treats `c` as a constant (“`c ≤ 3.01` in
sufficiently large graphs”, Section 4), but Lemmas 5 and 10 apply the density bound to small
depth-1 minors as well, and small graphs of genus `g` can have density `Θ(√g)` (e.g. `K_k` has
genus `⌈(k-3)(k-4)/12⌉`). Within the hypothesis class above, `c` must grow with `g`
(`density_unbounded`); so with `t = 4g + 3` Lemma 12 only yields `O(g²)`.
-/

open Finset

namespace Podc.BoundedGenusMDS

open SimpleGraph (Depth1Model IsDepth1Minor Depth1DensityLE ExcludesKt3 depth1_of_cover_two)

open Classical

variable {V : Type}

/-- Every depth-1 minor `H` of `G` satisfies Euler's edge bound for genus `g`:
`|E(H)| ≤ 3|V(H)| + 6g` (Lemmas 1 and 4 of the paper). -/
def EulerEdgeBound (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (W : Type) [Finite W] (H : SimpleGraph W), IsDepth1Minor H G →
    H.edgeSet.ncard ≤ 3 * Nat.card W + 6 * g

/-- The density parameter used for genus `g`: `c(g) = 3 + ⌊√(3g)⌋ + 1`. -/
def cGenus (g : ℕ) : ℕ := 3 + (Nat.sqrt (3 * g) + 1)

/-- The approximation factor of Lemma 12 for `c = c(g)`, `t = 4g + 3`. -/
def factor (g : ℕ) : ℕ := 6 * cGenus g ^ 2 * (4 * g + 3) + (2 * (4 * g + 3) + 5) * cGenus g + 4

lemma ncard_edgeSet_le_choose {W : Type} [Finite W] (H : SimpleGraph W) :
    H.edgeSet.ncard ≤ (Nat.card W).choose 2 := by
  have := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card]
  have h := H.card_edgeFinset_le_card_choose_two
  rwa [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h

/-- Euler's bound for all depth-1 minors gives `Depth1DensityLE G (c g)`. -/
theorem depth1DensityLE_of_euler {G : SimpleGraph V} {g : ℕ} (hE : EulerEdgeBound G g) :
    Depth1DensityLE G (cGenus g) := by
  intro W _ H hH
  have h1 := hE W H hH
  have h2 := ncard_edgeSet_le_choose H
  set n := Nat.card W
  set s := Nat.sqrt (3 * g) + 1
  have hs : 3 * g < s ^ 2 := Nat.lt_succ_sqrt' _
  have hc : cGenus g = 3 + s := rfl
  rw [hc]
  by_cases hn : n ≤ 2 * s + 7
  · -- small minors: `|E| ≤ n(n-1)/2 ≤ (3 + s) n`
    have : n.choose 2 ≤ (3 + s) * n := by
      rw [Nat.choose_two_right]
      apply Nat.div_le_of_le_mul
      rcases n with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]; nlinarith
    omega
  · -- large minors: `6g ≤ 2s² ≤ s n`
    push Not at hn
    nlinarith

/-- **Theorem 13** (with the genus facts as hypotheses). If every depth-1 minor of `G` satisfies
Euler's bound for genus `g` and `G` excludes `K_{4g+3,3}` as a depth-1 minor, then the modified
algorithm with parameter `c(g) = 3 + ⌊√(3g)⌋ + 1` computes a `factor g`-approximation, and
`factor g ≤ 1100 (g + 1)²` (`factor_le`). -/
theorem theorem_13 [Fintype V] {G : SimpleGraph V} {g : ℕ} (hE : EulerEdgeBound G g)
    (hK : ExcludesKt3 G (4 * g + 3)) {dom : V → V}
    (hdom : IsDominator G (phase1 G (cGenus g)) dom) :
    IsApprox G (factor g) (output G (cGenus g) dom) :=
  lemma_12 (depth1DensityLE_of_euler hE) hK hdom

/-- The approximation factor of Theorem 13 is `O(g²)`. -/
theorem factor_le (g : ℕ) : factor g ≤ 1100 * (g + 1) ^ 2 := by
  have h1 := Nat.sqrt_le' (3 * g)
  set r := Nat.sqrt (3 * g)
  have hc : cGenus g = 4 + r := by simp only [cGenus]; ring
  have hc2 : cGenus g ^ 2 ≤ 6 * g + 32 := by rw [hc]; nlinarith [sq_nonneg ((r : ℤ) - 4)]
  have hc1 : cGenus g ≤ cGenus g ^ 2 := Nat.le_self_pow two_ne_zero _
  simp only [factor]
  nlinarith

/-- Small depth-1 minors can be dense: for every `c` there is a graph satisfying Euler's bound for
some genus `g` and excluding `K_{4g+3,3}` as a depth-1 minor (namely a complete graph) whose
depth-1 minors are not all of density `≤ c`. Hence the density parameter `c` in Lemma 12 cannot be
taken independent of `g`. -/
theorem density_unbounded (c : ℕ) :
    ∃ (k g : ℕ), EulerEdgeBound (⊤ : SimpleGraph (Fin k)) g ∧
      ExcludesKt3 (⊤ : SimpleGraph (Fin k)) (4 * g + 3) ∧
      ¬ Depth1DensityLE (⊤ : SimpleGraph (Fin k)) c := by
  -- depth-1 minors of `K_k` have at most `k` vertices
  have hcard : ∀ (k : ℕ) (W : Type) [Finite W] (H : SimpleGraph W),
      IsDepth1Minor H (⊤ : SimpleGraph (Fin k)) → Nat.card W ≤ k := by
    intro k W _ H ⟨μ⟩
    have hinj : Function.Injective μ.center := by
      intro w w' h
      by_contra hne
      exact Set.disjoint_left.1 (μ.disjoint w w' hne) (μ.center_mem w) (h ▸ μ.center_mem w')
    have := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card]
    simpa using Fintype.card_le_of_injective _ hinj
  refine ⟨2 * c + 2, (2 * c + 2) ^ 2, ?_, ?_, ?_⟩
  · intro W _ H hH
    have h1 := ncard_edgeSet_le_choose H
    have h2 := hcard _ W H hH
    have h3 : (Nat.card W).choose 2 ≤ Nat.card W * Nat.card W := by
      rw [Nat.choose_two_right]; exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    nlinarith
  · intro hH
    have h := hcard _ _ _ hH
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at h
    nlinarith
  · intro hD
    have h := hD (Fin (2 * c + 2)) ⊤ ⟨{
      branch := fun w => ({w} : Set (Fin (2 * c + 2)))
      center := id
      center_mem := fun _ => rfl
      adj_center := fun _ _ hx hne => absurd hx hne
      disjoint := fun _ _ h => Set.disjoint_singleton.2 h
      edge := fun w w' h => ⟨w, rfl, w', rfl, h⟩ }⟩
    have hE := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin (2 * c + 2))
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Fintype.card_fin] at hE
    rw [hE, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.choose_two_right] at h
    have : (2 * c + 2) * (2 * c + 2 - 1) = (2 * c + 2) * (2 * c + 1) := rfl
    rw [this] at h
    have h2 : (2 * c + 2) * (2 * c + 1) / 2 = (c + 1) * (2 * c + 1) := by
      rw [show (2 * c + 2) * (2 * c + 1) = 2 * ((c + 1) * (2 * c + 1)) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [h2] at h
    nlinarith

end Podc.BoundedGenusMDS
