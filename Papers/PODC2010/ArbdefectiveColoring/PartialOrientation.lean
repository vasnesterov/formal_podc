import Papers.PODC2010.ArbdefectiveColoring.HPartition
import Papers.PODC2010.ArbdefectiveColoring.AlongOrientation

/-!
# Procedure Partial-Orientation (Algorithm 1, Theorem 3.5) and Procedure Arbdefective-Coloring
(Corollary 3.6)

The defective colourings of the H-sets (Lemma 2.1, Kuhn SPAA'09) are a black box: a
`DefectiveAlg V Δ d K R` is an `R`-round algorithm that computes, on every graph of maximum degree
`≤ Δ`, a `d`-defective colouring with colours `< K`.

* `partialOrientation A L D G`: compute the H-partition (`L` rounds, degree parameter `A`), colour
  the subgraphs `G(H_i)` in parallel with the black box `D`, and orient every edge towards the
  endpoint with the larger pair `(H-index, colour)` (edges inside an H-set between equal colours
  stay unoriented).
* `partialOrientation_spec` (**Theorem 3.5**): if `G` has an orientation of out-degree `≤ a` and
  `n (2a)^L < (A+1)^L`, the result is an acyclic partial orientation with out-degree `≤ A`, deficit
  `≤ d` and length `≤ L·K - 1`; it takes `L + R + 1` rounds (`partialOrientation_isLocal`).
* `completeOrientation_spec` (**Lemma 3.3**): with a legal colouring (`d = 0`) the orientation is
  complete.
* `arbdefectiveColoring_spec` (**Corollary 3.6**, general form): Procedure Arbdefective-Coloring
  (Partial-Orientation followed by Simple-Arbdefective) computes a `(d + ⌊A/k⌋)`-arbdefective
  `k`-colouring in `L + R + 1 + (L·K - 1)` rounds.
* `legalColoring_spec` (**Lemma 2.2(1)**, via Lemma 3.3 and greedy colouring along the complete
  orientation): a legal colouring with colours `≤ A`, in `L + R + 1 + (L·K - 1)` rounds.
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- A black-box `R`-round algorithm computing a `d`-defective colouring with colours `< K` on every
graph of maximum degree `≤ Δ` (Lemma 2.1 provides one with `d = ⌊Δ/p⌋`, `K = O(p²)` and
`R = O(log* n)`). -/
structure DefectiveAlg (V : Type*) [Fintype V] (Δ d K R : ℕ) where
  /-- The colouring computed on a graph. -/
  col : SimpleGraph V → V → ℕ
  /-- It takes `R` rounds. -/
  isLocal : IsLocalG R col
  /-- It is `d`-defective on graphs of maximum degree `≤ Δ`. -/
  defective : ∀ G, MaxDegLE G Δ → IsDefective G (col G) d
  /-- It uses colours `< K` on graphs of maximum degree `≤ Δ`. -/
  lt : ∀ G, MaxDegLE G Δ → ∀ v, col G v < K

/-- Strict lexicographic order on pairs (H-index, colour). -/
def LexLt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- The orientation defined by vertex labels `y`: the parents of `v` are its neighbours with a
lexicographically larger label. -/
noncomputable def orientOf (G : SimpleGraph V) (y : V → ℕ × ℕ) (v : V) : Finset V :=
  {u | ∃ p, nbrView G y v u = some p ∧ LexLt (y v) p}

lemma mem_orientOf {G : SimpleGraph V} {y : V → ℕ × ℕ} {v u : V} :
    u ∈ orientOf G y v ↔ G.Adj v u ∧ LexLt (y v) (y u) := by
  unfold orientOf
  rw [Finset.mem_filter]
  simp only [nbrView, mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hlt⟩
    split_ifs at hp with h
    · exact ⟨h, (Option.some.inj hp) ▸ hlt⟩
  · rintro ⟨h, hlt⟩
    exact ⟨y u, by simp [h], hlt⟩

/-- Labels `(H-index, colour of G(H_i))` computed in Partial-Orientation (lines 1–4). -/
noncomputable def hLabel (A L : ℕ) (D : SimpleGraph V → V → ℕ) (G : SimpleGraph V) (v : V) :
    ℕ × ℕ :=
  (hIdx G A L v, D (classGraph G (hIdx G A L)) v)

/-- **Procedure Partial-Orientation** (Algorithm 1). -/
noncomputable def partialOrientation (A L : ℕ) (D : SimpleGraph V → V → ℕ) (G : SimpleGraph V) :
    V → Finset V :=
  orientOf G (hLabel A L D G)

/-- Partial-Orientation takes `L + R + 1` rounds. -/
theorem partialOrientation_isLocal {R : ℕ} (A L : ℕ) {D : SimpleGraph V → V → ℕ}
    (hD : IsLocalG R D) : IsLocalG (1 + (R + L)) (partialOrientation A L D) := by
  -- lines 2–4: colour the H-sets in parallel
  have h2 : IsLocal (V := V) R (fun G (y : V → ℕ) v => (y v, D (classGraph G (id ∘ y)) v)) :=
    IsLocal.prod ((isLocal_self fun _ (a : ℕ) => a).mono (Nat.zero_le _)) (hD.classGraph id)
  have h12 : IsLocalG (R + L) (hLabel A L D) := by
    have := h2.comp (hIdx_isLocal (V := V) A L)
    simpa [IsLocalG, hLabel] using this
  -- lines 5–13: one round to orient the edges
  have h3 : IsLocal (V := V) 1 (fun G (y : V → ℕ × ℕ) v => orientOf G y v) :=
    isLocal_one_nbr (fun _ yv view => ({u | ∃ p, view u = some p ∧ LexLt yv p} : Finset V))
  have := h3.comp h12
  simpa [IsLocalG, partialOrientation] using this

lemma maxDegLE_classGraph_hIdx {G : SimpleGraph V} {a A L : ℕ} (hG : G.HasOutDegLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) :
    MaxDegLE (classGraph G (hIdx G A L)) A := by
  intro v
  refine (card_le_card fun u hu => ?_).trans ((hPartition hG hL).2 v)
  simp only [classGraph_adj, mem_filter, mem_univ, true_and] at hu ⊢
  exact ⟨hu.1, hu.2.le⟩

lemma height_le {L K x z : ℕ} (hx : x < L) (hz : z < K) :
    (L - 1 - x) * K + (K - 1 - z) ≤ L * K - 1 := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have : (L + 1 - 1 - x) * (K + 1) ≤ L * (K + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : (L + 1) * (K + 1) = L * (K + 1) + K + 1 := by ring
  omega

lemma height_lt {a b c d K : ℕ} (hab : a < b) (hc : c < K) : a * K + (K - 1 - c) < b * K + d := by
  have : (a + 1) * K ≤ b * K := Nat.mul_le_mul_right _ hab
  have h2 : (a + 1) * K = a * K + K := by ring
  omega

/-- **Theorem 3.5** (Partial-Orientation). Let `G` have an orientation of out-degree `≤ a`
(e.g. arboricity `≤ a`), let `n (2a)^L < (A+1)^L` (so the H-partition finishes in `L` rounds), and
let `D` be an `R`-round `d`-defective colouring algorithm with colours `< K` for graphs of maximum
degree `≤ A`. Then Procedure Partial-Orientation produces an acyclic partial orientation of
out-degree `≤ A`, deficit `≤ d` and length `≤ L·K - 1`. It runs in `L + R + 1` rounds
(`partialOrientation_isLocal`). -/
theorem partialOrientation_spec {G : SimpleGraph V} {a A L d K R : ℕ} (hG : G.HasOutDegLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) (D : DefectiveAlg V A d K R) :
    IsPartialOrientation G (partialOrientation A L D.col G) ∧
      OutDegLE (partialOrientation A L D.col G) A ∧
      DeficitLE G (partialOrientation A L D.col G) d ∧
      LengthLE (partialOrientation A L D.col G) (L * K - 1) := by
  have hHP := hPartition (A := A) hG hL
  have hdeg := maxDegLE_classGraph_hIdx (A := A) hG hL
  have hφ : ∀ v, D.col (classGraph G (hIdx G A L)) v < K := D.lt _ hdeg
  refine ⟨⟨fun v u hu => (mem_orientOf.1 hu).1, fun v u hu hv => ?_⟩, fun v => ?_, fun v => ?_, ?_⟩
  · have h1 := (mem_orientOf.1 hu).2
    have h2 := (mem_orientOf.1 hv).2
    simp only [LexLt] at h1 h2
    omega
  · -- out-degree: parents have H-index at least the own one
    refine (card_le_card fun u hu => ?_).trans (hHP.2 v)
    have := mem_orientOf.1 hu
    simp only [LexLt, hLabel] at this
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨this.1, by omega⟩
  · -- deficit: unoriented edges join vertices with equal labels, i.e. monochromatic edges of the
    -- defective colouring of `G(H_i)`
    refine (card_le_card fun u hu => ?_).trans (D.defective _ hdeg v)
    simp only [mem_filter, mem_univ, true_and, partialOrientation, mem_orientOf, LexLt] at hu ⊢
    obtain ⟨huv, h1, h2⟩ := hu
    simp only [huv, true_and, not_or, not_and, not_lt, huv.symm, hLabel] at h1 h2
    refine ⟨⟨huv, by omega⟩, ?_⟩
    have := h2.2 (by omega)
    have := h1.2 (by omega)
    omega
  · -- length: a height function bounded by `L·K - 1`
    refine lengthLE_of_height
      (h := fun v => (L - 1 - hIdx G A L v) * K + (K - 1 - D.col (classGraph G (hIdx G A L)) v))
      (fun v => height_le (hHP.1 v) (hφ v)) fun v u hu => ?_
    have h1 := (mem_orientOf.1 hu).2
    simp only [LexLt, hLabel] at h1
    have hu1 := hHP.1 u
    have hu2 := hφ u
    rcases h1 with h1 | ⟨h1, h2⟩
    · exact height_lt (by omega) hu2
    · rw [h1]
      omega

/-- An orientation of deficit `0` is complete. -/
lemma IsComplete.of_deficitLE_zero {G : SimpleGraph V} {par : V → Finset V}
    (h : DeficitLE G par 0) : IsComplete G par := by
  intro u v huv
  by_contra hc
  push Not at hc
  have := h u
  simp only [deficit, Nat.le_zero, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies,
    not_and, not_not] at this
  exact hc.2 (this huv hc.1)

/-- **Lemma 3.3** (Procedure Complete-Orientation): with a legal colouring of the H-sets (`d = 0`)
the orientation of Theorem 3.5 is complete and acyclic, with out-degree `≤ A` and length
`≤ L·K - 1`, computed in `L + R + 1` rounds. -/
theorem completeOrientation_spec {G : SimpleGraph V} {a A L K R : ℕ} (hG : G.HasOutDegLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) (D : DefectiveAlg V A 0 K R) :
    IsPartialOrientation G (partialOrientation A L D.col G) ∧
      IsComplete G (partialOrientation A L D.col G) ∧
      OutDegLE (partialOrientation A L D.col G) A ∧
      LengthLE (partialOrientation A L D.col G) (L * K - 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := partialOrientation_spec hG hL D
  exact ⟨h1, IsComplete.of_deficitLE_zero h3, h2, h4⟩

/-! ### Procedure Arbdefective-Coloring -/

/-- **Procedure Arbdefective-Coloring** with `k` colours: Partial-Orientation followed by
Simple-Arbdefective (run for `L·K - 1` rounds, the length bound of Theorem 3.5). -/
noncomputable def arbCol (k A L K : ℕ) (D : SimpleGraph V → V → ℕ) (G : SimpleGraph V) : V → ℕ :=
  simpleArb k (L * K - 1) G (partialOrientation A L D G)

/-- Arbdefective-Coloring takes `L + R + 1 + (L·K - 1)` rounds. -/
theorem arbCol_isLocal {R : ℕ} (k A L K : ℕ) {D : SimpleGraph V → V → ℕ} (hD : IsLocalG R D) :
    IsLocalG (L * K - 1 + (1 + (R + L))) (arbCol k A L K D) := by
  have := (simpleArb_isLocal (V := V) k (L * K - 1)).comp (partialOrientation_isLocal A L hD)
  simpa [IsLocalG, arbCol] using this

/-- **Corollary 3.6** (general form). Under the assumptions of Theorem 3.5 and for `k > 0`,
Procedure Arbdefective-Coloring computes a `(d + ⌊A/k⌋)`-arbdefective `k`-colouring. -/
theorem arbdefectiveColoring_spec {G : SimpleGraph V} {a A L d K R k : ℕ} (hG : G.HasOutDegLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) (D : DefectiveAlg V A d K R) (hk : 0 < k) :
    IsArbdefective G (arbCol k A L K D.col G) (d + A / k) ∧ ∀ v, arbCol k A L K D.col G v < k := by
  obtain ⟨h1, h2, h3, h4⟩ := partialOrientation_spec hG hL D
  exact simpleArbdefective h1 h4 h2 h3 hk

/-! ### Legal colouring of graphs of bounded arboricity (Lemma 2.2(1)) -/

/-- Legal colouring: Complete-Orientation followed by greedy colouring along the orientation. -/
noncomputable def legalCol (A L K : ℕ) (D : SimpleGraph V → V → ℕ) (G : SimpleGraph V) : V → ℕ :=
  greedyOrient (L * K - 1) G (partialOrientation A L D G)

/-- The legal colouring takes `L + R + 1 + (L·K - 1)` rounds. -/
theorem legalCol_isLocal {R : ℕ} (A L K : ℕ) {D : SimpleGraph V → V → ℕ} (hD : IsLocalG R D) :
    IsLocalG (L * K - 1 + (1 + (R + L))) (legalCol A L K D) := by
  have := (greedyOrient_isLocal (V := V) (L * K - 1)).comp (partialOrientation_isLocal A L hD)
  simpa [IsLocalG, legalCol] using this

/-- **Lemma 2.2(1)** (of [BE08], derived from Lemma 3.3): if `G` has an orientation of out-degree
`≤ a` and `n (2a)^L < (A+1)^L`, the procedure computes a legal colouring with the `A + 1` colours
`0, …, A`, in `L + R + 1 + (L·K - 1)` rounds, given an `R`-round legal `K`-colouring algorithm `D`
for graphs of maximum degree `≤ A`. (With `A = ⌊(2+ε)a⌋`, `L = O(log n)` and the `(Δ+1)`-colouring
of [BE09] (`K = A + 1`, `R = O(A + log* n)`) this is `O(a log n)` rounds.) -/
theorem legalColoring_spec {G : SimpleGraph V} {a A L K R : ℕ} (hG : G.HasOutDegLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) (D : DefectiveAlg V A 0 K R) :
    IsLegal G (legalCol A L K D.col G) ∧ ∀ v, legalCol A L K D.col G v ≤ A := by
  obtain ⟨h1, h2, h3, h4⟩ := completeOrientation_spec hG hL D
  exact greedyAlongOrientation h1 h2 h4 h3

end Podc.ArbdefectiveColoring
