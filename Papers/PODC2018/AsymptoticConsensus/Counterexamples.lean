import Papers.PODC2018.AsymptoticConsensus.Theorem4
import Papers.PODC2018.AsymptoticConsensus.Algorithms

/-!
# Counterexamples for statements of FNS'18 taken literally

All in the network model `N₃ = {H₀, H₁, H₂}` with two agents.

* `sourceIncompatible_N3`, `alphaDiam_N3` (`D = 2` for the per-agent reading of Definition 15, as
  the paper remarks after Definition 22), `alphaDiamLit_N3` (`D = 1` for the literal reading
  `In_S(G) = ⋃_{j ∈ S} In_j(G)`: `H₀` has both agents as roots and `In_{1,2}(G) = {1,2}` for all `G`).
* `lemma20_literal_false`: with the literal reading, Lemma 20 fails (Algorithm 1, `H₁ α_{H₀} H₂`,
  disjoint valencies `[0, 1/3]` and `[2/3, 1]`).
* `theorem5_literal_false`: with the literal reading, Theorem 5 would give rate `≥ 1/2` for
  Algorithm 1 in `N₃`, whose rate is `1/3`.
* `fd_not_vanishing`: the paper's claim "`δ_N(C_t) → 0` in any execution" is false (for the
  first-deviation algorithm `fd`).
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Cslib.HeardOf.Chain Filter Topology Set Classical
open Cslib.DynNet (IsRoot)
open scoped ENNReal

/-- The model `N₃ = {H₀, H₁, H₂}`. -/
def N3s : Set (Graph (Fin 2)) := {H0, H1, H2}

theorem not_root_H1 : (1 : Fin 2) ∉ Roots H1 := fun h => by
  have := (Relation.reflTransGen_iff_eq (fun y hy => by simp [H1] at hy)).1 (h 0)
  exact absurd this (by decide)

theorem not_root_H2 : (0 : Fin 2) ∉ Roots H2 := fun h => by
  have := (Relation.reflTransGen_iff_eq (fun y hy => by simp [H2] at hy)).1 (h 1)
  exact absurd this (by decide)

theorem roots_H0 (i : Fin 2) : i ∈ Roots H0 := fun j => by
  by_cases h : i = j
  · subst h; exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h

theorem sourceIncompatible_N3 : SourceIncompatible N3s := by
  intro r
  fin_cases r
  · exact ⟨H2, by simp [N3s], not_root_H2⟩
  · exact ⟨H1, by simp [N3s], not_root_H1⟩

theorem roots_H1 {i : Fin 2} (h : i ∈ Roots H1) : i = 0 := by
  fin_cases i
  · rfl
  · exact absurd h not_root_H1

theorem roots_H2 {i : Fin 2} (h : i ∈ Roots H2) : i = 1 := by
  fin_cases i
  · exact absurd h not_root_H2
  · rfl

section chains

variable {α : Type*} {rel : Graph α → Graph α → Graph α → Prop} {N : Set (Graph α)} {D : ℕ}

theorem alphaChain0 {G : Graph α} :
    ∃ q ≤ D, ∃ c : ℕ → Graph α, c 0 = G ∧ c q = G ∧
      ∀ r < q, c r ∈ N ∧ c (r + 1) ∈ N ∧ ∃ K ∈ N, rel K (c r) (c (r + 1)) :=
  ⟨0, Nat.zero_le _, fun _ => G, rfl, rfl, fun r hr => absurd hr (by omega)⟩

theorem alphaChain1 (hD : 1 ≤ D) {G H K : Graph α} (hG : G ∈ N) (hH : H ∈ N) (hK : K ∈ N)
    (h : rel K G H) : ∃ q ≤ D, ∃ c : ℕ → Graph α, c 0 = G ∧ c q = H ∧
      ∀ r < q, c r ∈ N ∧ c (r + 1) ∈ N ∧ ∃ K ∈ N, rel K (c r) (c (r + 1)) := by
  refine ⟨1, hD, fun r => if r = 0 then G else H, by simp, by simp, fun r hr => ?_⟩
  obtain rfl : r = 0 := by omega
  simpa using ⟨hG, hH, K, hK, h⟩

theorem alphaChain2 (hD : 2 ≤ D) {G H I K K' : Graph α} (hG : G ∈ N) (hH : H ∈ N) (hI : I ∈ N)
    (hK : K ∈ N) (hK' : K' ∈ N) (h : rel K G H) (h' : rel K' H I) :
    ∃ q ≤ D, ∃ c : ℕ → Graph α, c 0 = G ∧ c q = I ∧
      ∀ r < q, c r ∈ N ∧ c (r + 1) ∈ N ∧ ∃ K ∈ N, rel K (c r) (c (r + 1)) := by
  refine ⟨2, hD, fun r => if r = 0 then G else if r = 1 then H else I, by simp, by simp,
    fun r hr => ?_⟩
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · simpa using ⟨hG, hH, K, hK, h⟩
  · simpa using ⟨hH, hI, K', hK', h'⟩

end chains

/-- The α-diameter of `N₃` (per-agent reading) is at most `2`. -/
theorem alphaDiam_N3 : AlphaDiamLE AlphaRel N3s 2 := by
  have m0 : H0 ∈ N3s := by simp [N3s]
  have m1 : H1 ∈ N3s := by simp [N3s]
  have m2 : H2 ∈ N3s := by simp [N3s]
  have r01 : AlphaRel H2 H0 H1 := fun i hi => by rw [roots_H2 hi]; exact sameIn_H0_H1
  have r02 : AlphaRel H1 H0 H2 := fun i hi => by rw [roots_H1 hi]; exact sameIn_H0_H2
  have r10 : AlphaRel H2 H1 H0 := fun i hi => (r01 i hi).symm
  have r20 : AlphaRel H1 H2 H0 := fun i hi => (r02 i hi).symm
  intro G hG H hH
  simp only [N3s, mem_insert_iff, mem_singleton_iff] at hG hH
  rcases hG with rfl | rfl | rfl <;> rcases hH with rfl | rfl | rfl
  · exact alphaChain0
  · exact alphaChain1 (by norm_num) m0 m1 m2 r01
  · exact alphaChain1 (by norm_num) m0 m2 m1 r02
  · exact alphaChain1 (by norm_num) m1 m0 m2 r10
  · exact alphaChain0
  · exact alphaChain2 le_rfl m1 m0 m2 m2 m1 r10 r02
  · exact alphaChain1 (by norm_num) m2 m0 m1 r20
  · exact alphaChain2 le_rfl m2 m0 m1 m1 m2 r20 r01
  · exact alphaChain0

/-- With the literal reading of Definition 15, any two graphs are `α_{H₀}`-related. -/
theorem alphaRelLit_H0 (G H : Graph (Fin 2)) : AlphaRelLit H0 G H := fun j =>
  ⟨fun _ => ⟨j, roots_H0 j, hears_self _ _⟩, fun _ => ⟨j, roots_H0 j, hears_self _ _⟩⟩

/-- With the literal reading of Definition 15, the α-diameter of `N₃` is `1` (contradicting the
paper's remark that it is `2`). -/
theorem alphaDiamLit_N3 : AlphaDiamLE AlphaRelLit N3s 1 := fun G hG H hH =>
  alphaChain1 le_rfl hG hH (by simp [N3s]) (alphaRelLit_H0 G H)

/-! ### Lemma 20 and Theorem 5 under the literal reading -/

/-- Lemma 20 with the literal reading of Definition 15. -/
def Lemma20LitStatement : Prop :=
  ∀ (σ : Type) (A : Alg (Fin 2) σ ℝ) (N : Set (Graph (Fin 2))) (G H K : Graph (Fin 2))
    (C : Fin 2 → σ), A.Solves N → G ∈ N → H ∈ N → K ∈ N → AlphaRelLit K G H → A.Reach N C →
    (A.val (Pat N) (next A.step G C) ∩ A.val (Pat N) (next A.step H C)).Nonempty

/-- **Lemma 20 is false under the literal reading of Definition 15**: for Algorithm 1 from initial
values `(0, 1)`, `H₁ α_{H₀} H₂` but the valencies of `H₁.C₀ ⊆ [0, 1/3]` and `H₂.C₀ ⊆ [2/3, 1]` are
disjoint. -/
theorem lemma20_literal_false : ¬ Lemma20LitStatement := by
  intro h
  have hN : N3s ⊆ rooted2 := N3_subset_rooted2
  have hA : (alg1 (V := ℝ)).Solves N3s := alg1_solves.mono hN
  obtain ⟨z, hz1, hz2⟩ := h ℝ alg1 N3s H1 H2 H0 ![0, 1] hA (by simp [N3s]) (by simp [N3s])
    (by simp [N3s]) (alphaRelLit_H0 H1 H2) (Alg.Reach.initC ⟨H0, by simp [N3s]⟩ _)
  have s1 := averaging_alg1.val_subset _ (Alg.val_mono (pat_mono hN) _ hz1)
  have s2 := averaging_alg1.val_subset _ (Alg.val_mono (pat_mono hN) _ hz2)
  rw [range_fin_two, convexHull_pair, segment_eq_Icc'] at s1 s2
  have e10 := next_alg1_zero (V := ℝ) H1 ![0, 1]
  have e11 := next_alg1_one (V := ℝ) H1 ![0, 1]
  have e20 := next_alg1_zero (V := ℝ) H2 ![0, 1]
  have e21 := next_alg1_one (V := ℝ) H2 ![0, 1]
  simp only [H1, H2] at e10 e11 e20 e21
  simp only [alg1, memoryless] at s1 s2
  norm_num at e10 e11 e20 e21
  rw [e10, e11] at s1; rw [e20, e21] at s2
  simp only [mem_Icc] at s1 s2
  norm_num at s1 s2
  linarith [s1.2, s2.1]

/-- Theorem 5 with the literal reading of Definition 15 (and the paper's hypothesis that exact
consensus is not solvable). -/
def Theorem5LitStatement : Prop :=
  ∀ (σ : Type) (A : Alg (Fin 2) σ ℝ) (N : Set (Graph (Fin 2))) (D : ℕ), A.Solves N →
    ¬ ExactSolvable (Fin 2) ℝ N → AlphaDiamLE AlphaRelLit N D → ((D : ℝ≥0∞) + 1)⁻¹ ≤ A.rate N

/-- **Theorem 5 is false under the literal reading of Definition 15**: it would give contraction
rate `≥ 1/2` for Algorithm 1 in `N₃`, whose rate is `1/3`. -/
theorem theorem5_literal_false : ¬ Theorem5LitStatement := by
  intro h
  obtain ⟨hA, hrate⟩ := alg1_rate_eq_N3 (V := ℝ)
  have := h ℝ alg1 N3s 1 hA (not_exactSolvable_N3 subset_rfl) alphaDiamLit_N3
  rw [show (N3s : Set (Graph (Fin 2))) = {H0, H1, H2} from rfl, hrate] at this
  norm_num at this

/-- **The claim "`δ_N(C_t) → 0` along every execution" is false**: the first-deviation algorithm
does not have vanishing valency diameters in `N₃` (otherwise, by the repaired Theorem 4, some
valency would be a nontrivial connected set, contradicting `valencyProp_fd`). -/
theorem fd_not_vanishing : ¬ VanishingValency (fd (V := ℝ)) N3s := by
  intro hvan
  obtain ⟨x, hnt, hpc⟩ := theorem4_mpr_repaired le_rfl fd_solves hvan subset_rfl
    ⟨H0, by simp [N3s]⟩ sourceIncompatible_N3 alphaDiam_N3
  rcases valencyProp_fd N3s subset_rfl ⟨H0, by simp [N3s]⟩ x with ⟨z, hz⟩ | hnpc
  · have hnt' : (fd.val (Pat N3s) (fd.initC x)).Nontrivial := hnt
    rw [hz] at hnt'; exact hnt'.not_subsingleton subsingleton_singleton
  · exact hnpc hpc

/-! ### Theorem 2 of Section 2.2 (continuity for convex combination algorithms) -/

/-- **Theorem 2 of Section 2.2 of FNS'18** (for the averaging algorithms of `Algorithms.lean`,
in the valency form): the valency diameters of an averaging algorithm vanish along every
execution, i.e. its consensus function is continuous. In particular Algorithm 1 and the midpoint
algorithm satisfy the hypothesis of the repaired Theorem 4. -/
theorem Averaging.vanishing {α V : Type} [Finite α] [Nonempty α] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : StepFn α V} {N : Set (Graph α)} {r : ℝ≥0∞} (h : Averaging f N r) :
    VanishingValency (memoryless f) N := by
  intro N' hN' x p hp
  have hfin : Metric.ediam (range x) ≠ ∞ := (finite_range x).isBounded.ediam_ne_top
  have hlim : Tendsto (fun t => Metric.ediam (range x) * r ^ t) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h.lt_one)
      (Or.inr hfin)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    fun t => ?_
  calc (memoryless f).δ N' (conf (memoryless f).step ((memoryless f).initC x) p t)
      ≤ (memoryless f).δ N (conf (memoryless f).step ((memoryless f).initC x) p t) :=
        Alg.δ_mono hN' _
    _ ≤ Metric.ediam (range (conf f x p t)) := h.δ_le _
    _ ≤ Metric.ediam (range x) * r ^ t := h.ediam_conf_le (pat_mono hN' hp) x t

end AsymptoticConsensus
