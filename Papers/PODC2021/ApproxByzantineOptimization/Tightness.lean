/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2021.ApproxByzantineOptimization.Basic

/-!
# Theorem 1, class reading: `(2f, ε')`-redundancy does not allow `(f, ε)`-resilience for `ε < ε'`

The meaningful content of Theorem 1 ("`(f, ε)`-resilience is feasible only if `(2f, ε)`-redundancy
holds", "characterizing the correlation between relaxation in redundancy and approximation in
resilience"): no deterministic algorithm is `(f, ε)`-resilient on the whole class of profiles that
satisfy Assumption 1 and `(2f, ε')`-redundancy when `ε < ε'` (`theorem_1_class`). Together with
Theorem 2 the optimal resilience on that class lies in `[ε', 2ε']`.

The paper's proof does not establish this: its second profile (the faulty agents' fabricated
functions made honest) is not shown to be `(2f, ε')`-redundant. We use a different, single
profile (`gridProfile`) supported on the three points `-v, 0, v` with `‖v‖ = ε'` (value `1`
elsewhere):

* agents `i < f` (group 2) pull towards `v`, agents `f ≤ i < 2f` (group 3) towards `-v`, the others
  (group 1) prefer `0`;
* `v` can be a minimum point of a set only if it contains group-2 agents and no group-3 agent, and
  symmetrically for `-v`; hence for `Ŝ ⊆ S` the two `arg min`s lie together in `{0, v}` or in
  `{0, -v}`, and the Hausdorff distance is at most `ε'`;
* the `n - f` agents outside group 3 have `arg min = {v}`, those outside group 2 have `{-v}`, at
  distance `2ε' > 2ε`.

The cost functions are discontinuous; the paper's Section 3 allows arbitrary cost functions
subject to Assumption 1.
-/

open Finset Metric
open scoped ENNReal NNReal

namespace Podc.ApproxByzantineOptimization

namespace Grid

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ}

/-- Cost function supported on the grid `{0, v, -v}`: value `0` at `0`, `a` at `v`, `b` at `-v`,
and `1` elsewhere. -/
noncomputable def gridQ (v : E) (a b : Fin n → ℝ) : Profile n E := fun i x =>
  if x = 0 then 0 else if x = v then a i else if x = -v then b i else 1

variable {v : E} {a b : Fin n → ℝ}

lemma sum_gridQ (hv0 : v ≠ 0) (hvn : -v ≠ v) (T : Finset (Fin n)) (y : E) :
    ∑ i ∈ T, gridQ v a b i y =
      if y = 0 then 0 else if y = v then ∑ i ∈ T, a i
      else if y = -v then ∑ i ∈ T, b i else (T.card : ℝ) := by
  have hn0 : -v ≠ 0 := neg_ne_zero.2 hv0
  by_cases h0 : y = 0
  · simp [gridQ, h0]
  by_cases h1 : y = v
  · simp [gridQ, h1, hv0]
  by_cases h2 : y = -v
  · simp [gridQ, h2, hn0, hvn]
  simp [gridQ, h0, h1, h2]

variable (hv0 : v ≠ 0) (hvn : -v ≠ v)
include hv0 hvn

lemma mem_grid {T : Finset (Fin n)} (hT : T.Nonempty) {x : E} (hx : x ∈ argminSet (gridQ v a b) T) :
    x = 0 ∨ x = v ∨ x = -v := by
  by_contra h
  push Not at h
  have := hx 0
  rw [sum_gridQ hv0 hvn, sum_gridQ hv0 hvn] at this
  simp only [h.1, h.2.1, h.2.2, ↓reduceIte] at this
  have : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.2 hT
  linarith

lemma sum_a_nonpos {T : Finset (Fin n)} (hx : v ∈ argminSet (gridQ v a b) T) :
    ∑ i ∈ T, a i ≤ 0 := by
  have := hx 0
  rw [sum_gridQ hv0 hvn, sum_gridQ hv0 hvn] at this
  simpa [hv0] using this

lemma sum_b_nonpos {T : Finset (Fin n)} (hx : -v ∈ argminSet (gridQ v a b) T) :
    ∑ i ∈ T, b i ≤ 0 := by
  have := hx 0
  rw [sum_gridQ hv0 hvn, sum_gridQ hv0 hvn] at this
  simpa [hv0, hvn] using this

lemma argminSet_nonempty {T : Finset (Fin n)} (hT : T.Nonempty) :
    (argminSet (gridQ v a b) T).Nonempty := by
  have hc : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.2 hT
  set A := ∑ i ∈ T, a i
  set B := ∑ i ∈ T, b i
  by_cases hA : A ≤ 0 ∧ A ≤ B
  · refine ⟨v, fun y => ?_⟩
    rw [sum_gridQ hv0 hvn, sum_gridQ hv0 hvn]
    simp only [hv0, ↓reduceIte]
    split_ifs <;> linarith
  by_cases hB : B ≤ 0 ∧ B ≤ A
  · refine ⟨-v, fun y => ?_⟩
    rw [sum_gridQ hv0 hvn, sum_gridQ hv0 hvn]
    simp only [neg_ne_zero.2 hv0, hvn, ↓reduceIte]
    split_ifs <;> linarith
  · refine ⟨0, fun y => ?_⟩
    rw [sum_gridQ hv0 hvn, sum_gridQ hv0 hvn]
    simp only [↓reduceIte]
    have h1 : 0 ≤ A := by
      by_contra h; push Not at h
      by_cases hAB : A ≤ B
      · exact hA ⟨h.le, hAB⟩
      · exact hB ⟨by linarith, by linarith⟩
    have h2 : 0 ≤ B := by
      by_contra h; push Not at h
      by_cases hAB : B ≤ A
      · exact hB ⟨h.le, hAB⟩
      · exact hA ⟨by linarith, by linarith⟩
    split_ifs <;> linarith

lemma argminSet_eq_v {T : Finset (Fin n)} (hT : T.Nonempty) (hA : ∑ i ∈ T, a i < 0)
    (hAB : ∑ i ∈ T, a i < ∑ i ∈ T, b i) : argminSet (gridQ v a b) T = {v} := by
  have hc : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.2 hT
  apply argminSet_eq_singleton
  intro y hy
  rw [sum_gridQ hv0 hvn, sum_gridQ hv0 hvn]
  simp only [hv0, hy, ↓reduceIte]
  split_ifs <;> linarith

lemma argminSet_eq_neg_v {T : Finset (Fin n)} (hT : T.Nonempty) (hB : ∑ i ∈ T, b i < 0)
    (hAB : ∑ i ∈ T, b i < ∑ i ∈ T, a i) : argminSet (gridQ v a b) T = {-v} := by
  have hc : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.2 hT
  apply argminSet_eq_singleton
  intro y hy
  rw [sum_gridQ hv0 hvn, sum_gridQ hv0 hvn]
  simp only [neg_ne_zero.2 hv0, hvn, hy, ↓reduceIte]
  split_ifs <;> linarith

lemma argminSet_subset {T : Finset (Fin n)} (hT : T.Nonempty) :
    argminSet (gridQ v a b) T ⊆ {0, v, -v} := fun x hx => by
  rcases mem_grid hv0 hvn hT hx with h | h | h <;> simp [h]

end Grid

open Grid

variable {n : ℕ}

/-- Values at `v`: group 2 (`i < f`) `-n`, group 3 (`f ≤ i < 2f`) `n² + 1`, group 1 `1`. -/
noncomputable def aVal (n f : ℕ) (i : Fin n) : ℝ :=
  if (i : ℕ) < f then -(n : ℝ) else if (i : ℕ) < 2 * f then (n : ℝ) ^ 2 + 1 else 1

/-- Values at `-v`: group 2 `n² + 1`, group 3 `-n`, group 1 `1`. -/
noncomputable def bVal (n f : ℕ) (i : Fin n) : ℝ :=
  if (i : ℕ) < f then (n : ℝ) ^ 2 + 1 else if (i : ℕ) < 2 * f then -(n : ℝ) else 1

/-- The profile of `theorem_1_corrected`. -/
noncomputable def gridProfile {E : Type*} [NormedAddCommGroup E] (f : ℕ) (v : E) : Profile n E :=
  gridQ v (aVal n f) (bVal n f)

/-- A sum of values `≥ -n` containing one value `n² + 1` is positive. -/
lemma sum_pos_of_big {T : Finset (Fin n)} {c : Fin n → ℝ} (hc : ∀ i, -(n : ℝ) ≤ c i) {j : Fin n}
    (hj : j ∈ T) (hcj : c j = (n : ℝ) ^ 2 + 1) : 0 < ∑ i ∈ T, c i := by
  rw [← Finset.add_sum_erase T c hj, hcj]
  have h1 : (T.erase j).card ≤ n := by simpa using Finset.card_le_univ (T.erase j)
  have h2 : ∑ i ∈ T.erase j, (-(n : ℝ)) ≤ ∑ i ∈ T.erase j, c i := Finset.sum_le_sum fun i _ => hc i
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  have h3 : ((T.erase j).card : ℝ) ≤ n := by exact_mod_cast h1
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- A sum of values `≤ 1` over at most `n` agents containing one value `-n` is negative. -/
lemma sum_neg_of_small {T : Finset (Fin n)} {c : Fin n → ℝ} (hc : ∀ i ∈ T, c i ≤ 1) {j : Fin n}
    (hj : j ∈ T) (hcj : c j = -(n : ℝ)) : ∑ i ∈ T, c i < 0 := by
  rw [← Finset.add_sum_erase T c hj, hcj]
  have h1 : (T.erase j).card + 1 ≤ n := by
    rw [Finset.card_erase_add_one hj]; simpa using Finset.card_le_univ T
  have h2 : ∑ i ∈ T.erase j, c i ≤ ∑ i ∈ T.erase j, (1 : ℝ) :=
    Finset.sum_le_sum fun i hi => hc i (Finset.mem_of_mem_erase hi)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  have h3 : ((T.erase j).card : ℝ) + 1 ≤ n := by exact_mod_cast h1
  linarith

variable {f : ℕ}

lemma aVal_ge (i : Fin n) : -(n : ℝ) ≤ aVal n f i := by
  unfold aVal; split_ifs <;> nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

lemma bVal_ge (i : Fin n) : -(n : ℝ) ≤ bVal n f i := by
  unfold bVal; split_ifs <;> nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- If `T` contains a group-3 agent, `∑_T a > 0`. -/
lemma sum_aVal_pos_of_g3 {T : Finset (Fin n)} {j : Fin n} (hj : j ∈ T) (h1 : f ≤ (j : ℕ))
    (h2 : (j : ℕ) < 2 * f) : 0 < ∑ i ∈ T, aVal n f i :=
  sum_pos_of_big aVal_ge hj (by simp [aVal, h2, not_lt.2 h1])

/-- If `T` contains a group-2 agent, `∑_T b > 0`. -/
lemma sum_bVal_pos_of_g2 {T : Finset (Fin n)} {j : Fin n} (hj : j ∈ T) (h1 : (j : ℕ) < f) :
    0 < ∑ i ∈ T, bVal n f i :=
  sum_pos_of_big bVal_ge hj (by simp [bVal, h1])

/-- If `T ≠ ∅` has no group-2 agent, `∑_T a > 0`. -/
lemma sum_aVal_pos_of_no_g2 {T : Finset (Fin n)} (hT : T.Nonempty) (h : ∀ i ∈ T, ¬ (i : ℕ) < f) :
    0 < ∑ i ∈ T, aVal n f i :=
  Finset.sum_pos (fun i hi => by
    unfold aVal; simp only [h i hi, ↓reduceIte]; split_ifs <;> positivity) hT

/-- If `T ≠ ∅` has no group-3 agent, `∑_T b > 0`. -/
lemma sum_bVal_pos_of_no_g3 {T : Finset (Fin n)} (hT : T.Nonempty)
    (h : ∀ i ∈ T, ¬ (f ≤ (i : ℕ) ∧ (i : ℕ) < 2 * f)) : 0 < ∑ i ∈ T, bVal n f i :=
  Finset.sum_pos (fun i hi => by
    unfold bVal
    split_ifs with h1 h2
    · positivity
    · exact absurd ⟨not_lt.1 h1, h2⟩ (h i hi)
    · norm_num) hT

variable {E : Type*} [NormedAddCommGroup E] {v : E}

/-- `v` is a minimum point only of sets with a group-2 agent and no group-3 agent. -/
lemma of_v_mem (hv0 : v ≠ 0) (hvn : -v ≠ v) {T : Finset (Fin n)} (hT : T.Nonempty)
    (hx : v ∈ argminSet (gridProfile f v) T) :
    (∀ i ∈ T, ¬ (f ≤ (i : ℕ) ∧ (i : ℕ) < 2 * f)) ∧ ∃ i ∈ T, (i : ℕ) < f := by
  have hA := sum_a_nonpos hv0 hvn hx
  refine ⟨fun i hi hg => ?_, ?_⟩
  · exact absurd hA (not_le.2 (sum_aVal_pos_of_g3 hi hg.1 hg.2))
  · by_contra h
    push Not at h
    exact absurd hA (not_le.2 (sum_aVal_pos_of_no_g2 hT fun i hi => not_lt.2 (h i hi)))

/-- `-v` is a minimum point only of sets with a group-3 agent and no group-2 agent. -/
lemma of_neg_v_mem (hv0 : v ≠ 0) (hvn : -v ≠ v) {T : Finset (Fin n)} (hT : T.Nonempty)
    (hx : -v ∈ argminSet (gridProfile f v) T) :
    (∀ i ∈ T, ¬ (i : ℕ) < f) ∧ ∃ i ∈ T, f ≤ (i : ℕ) ∧ (i : ℕ) < 2 * f := by
  have hB := sum_b_nonpos hv0 hvn hx
  refine ⟨fun i hi hg => ?_, ?_⟩
  · exact absurd hB (not_le.2 (sum_bVal_pos_of_g2 hi hg))
  · by_contra h
    push Not at h
    exact absurd hB (not_le.2 (sum_bVal_pos_of_no_g3 hT fun i hi hg =>
      absurd (h i hi hg.1) (by omega)))

/-- The `n - f` agents outside group 3. -/
def S₀ (n f : ℕ) : Finset (Fin n) := univ.filter fun i => ¬ (f ≤ (i : ℕ) ∧ (i : ℕ) < 2 * f)

/-- The `n - f` agents outside group 2. -/
def T₀ (n f : ℕ) : Finset (Fin n) := univ.filter fun i => ¬ (i : ℕ) < f

lemma card_T₀ (hfn : f ≤ n) : (T₀ n f).card + f = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n => (i : ℕ) < f)
  rw [Finset.card_univ, Fintype.card_fin, Fin.card_filter_val_lt] at h
  unfold T₀
  rw [min_eq_right hfn] at h
  omega

lemma card_S₀ (hfn : 2 * f ≤ n) : (S₀ n f).card + f = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n => f ≤ (i : ℕ) ∧ (i : ℕ) < 2 * f)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h3 : (univ.filter fun i : Fin n => f ≤ (i : ℕ) ∧ (i : ℕ) < 2 * f) =
      (univ.filter fun i : Fin n => (i : ℕ) < 2 * f) \ (univ.filter fun i : Fin n => (i : ℕ) < f) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]; omega
  have h4 : (univ.filter fun i : Fin n => (i : ℕ) < f) ⊆
      (univ.filter fun i : Fin n => (i : ℕ) < 2 * f) := by
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [h3, Finset.card_sdiff_of_subset h4, Fin.card_filter_val_lt, Fin.card_filter_val_lt,
    min_eq_right hfn, min_eq_right (by omega)] at h
  unfold S₀
  omega

variable [NormedSpace ℝ E]

/-- **Theorem 1, corrected (class reading).** Let `1 ≤ f`, `2f < n` and `0 ≤ ε < ε'`. For every
deterministic algorithm there is a profile satisfying Assumption 1 and `(2f, ε')`-redundancy on
which the algorithm is not `(f, ε)`-resilient. (Any real normed space `E ≠ 0`, e.g. `ℝ^d`,
`d ≥ 1`.) -/
theorem theorem_1_corrected [Nontrivial E] (hf1 : 1 ≤ f) (hfn : 2 * f < n) {ε ε' : ℝ≥0}
    (hε : ε < ε') (alg : Algorithm n E) :
    ∃ Q : Profile n E, Assumption1 Q ∧ IsRedundant f ε' Q ∧ ¬ IsResilient f ε alg Q := by
  obtain ⟨v, hv⟩ := exists_norm_eq E ε'.coe_nonneg
  have hε'pos : (0 : ℝ) < ε' := ε.coe_nonneg.trans_lt (by exact_mod_cast hε)
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv; linarith
  have hvn : -v ≠ v := by
    intro h
    have : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel v
    exact hv0 ((smul_eq_zero.1 this).resolve_left two_ne_zero)
  have hedist : edist (0 : E) v = ε' := by
    rw [edist_dist, dist_zero_left, hv, ENNReal.ofReal_coe_nnreal]
  have hedist' : edist (0 : E) (-v) = ε' := by
    rw [edist_dist, dist_zero_left, norm_neg, hv, ENNReal.ofReal_coe_nnreal]
  refine ⟨gridProfile f v, fun T hT => ⟨argminSet_nonempty hv0 hvn hT,
    ((Set.toFinite _).subset (argminSet_subset hv0 hvn hT)).isClosed⟩, ?_, ?_⟩
  · -- redundancy: the two `arg min`s lie together in `{0, v}` or in `{0, -v}`
    intro S S' hsub hS hS'
    have hS'ne : S'.Nonempty := Finset.card_pos.1 (by omega)
    have hSne : S.Nonempty := hS'ne.mono hsub
    set X := argminSet (gridProfile f v) S
    set X' := argminSet (gridProfile f v) S'
    have key : ¬ ((v ∈ X ∨ v ∈ X') ∧ (-v ∈ X ∨ -v ∈ X')) := by
      rintro ⟨h1 | h1, h2 | h2⟩
      · obtain ⟨-, i, hi, hlt⟩ := of_v_mem hv0 hvn hSne h1
        exact (of_neg_v_mem hv0 hvn hSne h2).1 i hi hlt
      · obtain ⟨-, i, hi, hg⟩ := of_neg_v_mem hv0 hvn hS'ne h2
        exact (of_v_mem hv0 hvn hSne h1).1 i (hsub hi) hg
      · obtain ⟨-, i, hi, hlt⟩ := of_v_mem hv0 hvn hS'ne h1
        exact (of_neg_v_mem hv0 hvn hSne h2).1 i (hsub hi) hlt
      · obtain ⟨-, i, hi, hlt⟩ := of_v_mem hv0 hvn hS'ne h1
        exact (of_neg_v_mem hv0 hvn hS'ne h2).1 i hi hlt
    have hsub3 : X ∪ X' ⊆ {0, v, -v} :=
      Set.union_subset (argminSet_subset hv0 hvn hSne) (argminSet_subset hv0 hvn hS'ne)
    refine (hausdorffEDist_le_ediam (argminSet_nonempty hv0 hvn hSne)
      (argminSet_nonempty hv0 hvn hS'ne)).trans ?_
    by_cases hvU : v ∈ X ∨ v ∈ X'
    · have hn : ¬ (-v ∈ X ∨ -v ∈ X') := fun h => key ⟨hvU, h⟩
      have : X ∪ X' ⊆ {0, v} := fun x hx => by
        rcases hsub3 hx with h | h | h
        · simp [h]
        · simp [h]
        · rw [Set.mem_singleton_iff] at h; subst h
          exact absurd hx (by simpa [Set.mem_union] using hn)
      exact (ediam_mono this).trans (by rw [ediam_pair, hedist])
    · have : X ∪ X' ⊆ {0, -v} := fun x hx => by
        rcases hsub3 hx with h | h | h
        · simp [h]
        · subst h
          exact absurd hx (by simpa [Set.mem_union] using hvU)
        · simp [h]
      exact (ediam_mono this).trans (by rw [ediam_pair, hedist'])
  · -- non-resilience: `arg min (S₀) = {v}`, `arg min (T₀) = {-v}`
    have hn : 0 < n := by omega
    let j₀ : Fin n := ⟨0, hn⟩
    let j₁ : Fin n := ⟨f, by omega⟩
    have hj₀ : j₀ ∈ S₀ n f := by simp [S₀, j₀]
    have hj₁ : j₁ ∈ T₀ n f := by simp [T₀, j₁]
    have hX : argminSet (gridProfile f v) (S₀ n f) = {v} := by
      have hA : ∑ i ∈ S₀ n f, aVal n f i < 0 :=
        sum_neg_of_small (fun i hi => by
          simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          unfold aVal; split_ifs with h1 h2
          · nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
          · exact absurd ⟨not_lt.1 h1, h2⟩ hi
          · exact le_rfl) hj₀ (by simp [aVal, j₀]; omega)
      have hB := sum_bVal_pos_of_g2 (f := f) hj₀ (show (j₀ : ℕ) < f by simp [j₀]; omega)
      exact argminSet_eq_v hv0 hvn ⟨j₀, hj₀⟩ hA (by linarith)
    have hY : argminSet (gridProfile f v) (T₀ n f) = {-v} := by
      have hB : ∑ i ∈ T₀ n f, bVal n f i < 0 :=
        sum_neg_of_small (fun i hi => by
          simp only [T₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          unfold bVal; split_ifs with h1
          · nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
          · exact le_rfl) hj₁ (by simp [bVal, j₁]; omega)
      have hA := sum_aVal_pos_of_no_g2 (f := f) (T := T₀ n f) ⟨j₁, hj₁⟩
        (fun i hi => by simpa [T₀] using hi)
      exact argminSet_eq_neg_v hv0 hvn ⟨j₁, hj₁⟩ hB (by linarith)
    refine not_isResilient_of_far (card_S₀ hfn.le) (card_T₀ (by omega)) hX hY ?_ alg
    rw [edist_dist, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ, norm_smul, hv, Real.norm_two]
    rw [show (2 : ℝ≥0∞) * ε = ENNReal.ofReal (2 * ε) by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      (by have : (ε : ℝ) < ε' := by exact_mod_cast hε
          linarith)

/-- **Theorem 1, class form.** If a deterministic algorithm is `(f, ε)`-resilient on every profile
satisfying Assumption 1 and `(2f, ε')`-redundancy (`1 ≤ f`, `2f < n`), then `ε' ≤ ε`: resilience
`ε` requires the profiles to be `(2f, ε)`-redundant in this quantitative sense. -/
theorem theorem_1_class [Nontrivial E] (hf1 : 1 ≤ f) (hfn : 2 * f < n) {ε ε' : ℝ≥0}
    (alg : Algorithm n E)
    (h : ∀ Q : Profile n E, Assumption1 Q → IsRedundant f ε' Q → IsResilient f ε alg Q) :
    ε' ≤ ε := by
  by_contra hlt
  push Not at hlt
  obtain ⟨Q, hA, hR, hn⟩ := theorem_1_corrected hf1 hfn hlt alg
  exact hn (h Q hA hR)

end Podc.ApproxByzantineOptimization
