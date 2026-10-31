import Papers.PODC2010.TruncatedGaleShapley.Stable

/-!
# Theorem 3, deterministic ingredients (§6.3)

* `Minf I`: the stable matching `M_∞` reached by the algorithm (§5.1).
* (3) `size_run_le_Minf`, `size_Minf_le`: `|M_j| ≤ |M_∞| ≤ (1 + ε/2) |M_j|` for
  `j ≥ 1 + (2Δ - 2)/ε`, `j ≥ 2`.
* (4), (5) `card_reds_le`, `card_blues_le`: in a graph without isolated nodes, a stable matching
  `M` satisfies `|R| ≤ Δ |M|` and `|B| ≤ Δ |M|`.
* (9) `estimate_error`: the accuracy of the estimate `m̂ = n (X/N) (Y/N)` when `X/N` and `Y/N` are
  within relative error `γ` of their means.
-/

namespace Podc.TruncatedGaleShapley

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Bicoloured

variable {I : Bicoloured V}

/-- The size of a matching given by a state (number of matched blue nodes). -/
noncomputable abbrev size (I : Bicoloured V) (s : State V) : ℝ := I.blueW s (fun _ => 1)

lemma sum_nodeW_one (s : State V) (S : Finset V) :
    ∑ v ∈ S, nodeW s (fun _ => 1) v = (#(S.filter fun v => s.p v ≠ none) : ℝ) := by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun v _ => ?_
  rcases h : s.p v with _ | u <;> simp [nodeW, h]

/-- `|M| =` the number of matched blue nodes. -/
lemma card_matchingEdges {s : State V} (hs : I.IsMatching s.p) :
    ((matchingEdges s.p).card : ℝ) = I.size s := by
  rw [size, ← sum_matchingEdges_eq_blueW hs]; simp

/-- `|M| =` the number of matched red nodes. -/
lemma size_eq_card_matched_reds {s : State V} (hs : I.IsMatching s.p) :
    I.size s = (#(I.reds.filter fun v => s.p v ≠ none) : ℝ) := by
  rw [size, ← sum_matchingEdges_eq_blueW hs, matchingEdges_sum hs _ true, ← sum_nodeW_one]; rfl

lemma size_eq_card_matched_blues (s : State V) :
    I.size s = (#(I.blues.filter fun v => s.p v ≠ none) : ℝ) := by
  rw [size, blueW, sum_nodeW_one]

/-! ### `M_∞` -/

/-- The round after which the algorithm is stable and constant. -/
noncomputable def zStab (I : Bicoloured V) : ℕ := Classical.choose (exists_stable I)

/-- The stable matching `M_∞` found by the (untruncated) algorithm. -/
noncomputable def Minf (I : Bicoloured V) : State V := I.run (zStab I)

lemma one_le_zStab : 1 ≤ zStab I := (Classical.choose_spec (exists_stable I)).1

lemma isStable_Minf : I.IsStable (Minf I).p := (Classical.choose_spec (exists_stable I)).2.1

lemma isMatching_Minf : I.IsMatching (Minf I).p := isMatching_run _

lemma run_eq_Minf {i : ℕ} (hi : zStab I ≤ i) : I.run i = Minf I :=
  (Classical.choose_spec (exists_stable I)).2.2 i hi

/-- `|M_j| ≤ |M_∞|`. -/
lemma size_run_le_Minf {j : ℕ} (hj : 1 ≤ j) : I.size (I.run j) ≤ I.size (Minf I) := by
  rw [← run_eq_Minf (le_max_left (zStab I) j)]
  exact size_mono hj (le_max_right _ _)

/-- `|M_∞| ≤ |M_j| + f_j(R)`. -/
lemma size_Minf_le_add {j : ℕ} (hj : 1 ≤ j) :
    I.size (Minf I) ≤ I.size (I.run j) + I.potR (I.run j) (fun _ => 1) := by
  rw [← run_eq_Minf (le_max_left (zStab I) j)]
  exact size_le_add_potR hj (le_max_right _ _)

/-- (3): for `j ≥ 2` and `j ≥ 1 + (2Δ - 2)/ε`, `|M_∞| ≤ (1 + ε/2) |M_j|`. -/
theorem size_Minf_le {Δ : ℕ} (hΔ : ∀ v, (I.N v).card ≤ Δ) {ε : ℝ} (hε : 0 < ε) {j : ℕ}
    (hj2 : 2 ≤ j) (hj : 1 + ((Δ - 1 : ℕ) : ℝ) / (ε / 2) ≤ j) :
    I.size (Minf I) ≤ (1 + ε / 2) * I.size (I.run j) := by
  have h6 := lemma_6 I.respectsPrefs_one hΔ (by positivity : 0 < ε / 2) hj2 hj
  have := size_Minf_le_add (I := I) (by omega : 1 ≤ j)
  simp only [size] at *
  linarith

/-! ### (4), (5) -/

/-- (4): if no node is isolated and all degrees are at most `Δ`, a stable matching `p` has
`|R| ≤ Δ · #(matched blue nodes)`. -/
theorem card_reds_le {p : V → Option V} (hp : I.IsMatching p) (hst : I.IsStable p)
    (hiso : ∀ v, (I.N v).Nonempty) {Δ : ℕ} (hΔ : ∀ v, (I.N v).card ≤ Δ) :
    I.reds.card ≤ Δ * (I.blues.filter fun v => p v ≠ none).card := by
  have hsub : I.reds ⊆ (I.blues.filter fun v => p v ≠ none).biUnion I.N := by
    intro r hr
    have hr := I.mem_reds.1 hr
    simp only [mem_biUnion, mem_filter, mem_blues]
    rcases hpr : p r with _ | b
    · obtain ⟨b, hb⟩ := hiso r
      refine ⟨b, ⟨blue_of_mem_red hb hr, fun hpb => hst r b ⟨hb, by rw [hpr]; trivial, ?_⟩⟩,
        I.symm hb⟩
      rw [hpb]; trivial
    · have hb := hp.mem_N r b hpr
      exact ⟨b, ⟨blue_of_mem_red hb hr, by rw [hp.symm r b hpr]; simp⟩, I.symm hb⟩
  calc I.reds.card ≤ _ := card_le_card hsub
    _ ≤ ∑ b ∈ I.blues.filter (fun v => p v ≠ none), (I.N b).card := card_biUnion_le
    _ ≤ ∑ b ∈ I.blues.filter (fun v => p v ≠ none), Δ := sum_le_sum fun b _ => hΔ b
    _ = Δ * _ := by rw [sum_const, smul_eq_mul, mul_comm]

/-- (5): symmetrically, `|B| ≤ Δ · #(matched red nodes)`. -/
theorem card_blues_le {p : V → Option V} (hp : I.IsMatching p) (hst : I.IsStable p)
    (hiso : ∀ v, (I.N v).Nonempty) {Δ : ℕ} (hΔ : ∀ v, (I.N v).card ≤ Δ) :
    I.blues.card ≤ Δ * (I.reds.filter fun v => p v ≠ none).card := by
  have hsub : I.blues ⊆ (I.reds.filter fun v => p v ≠ none).biUnion I.N := by
    intro b hb
    have hb := I.mem_blues.1 hb
    simp only [mem_biUnion, mem_filter, mem_reds]
    rcases hpb : p b with _ | r
    · obtain ⟨r, hr⟩ := hiso b
      refine ⟨r, ⟨red_of_mem_blue hr hb, fun hpr => hst b r ⟨hr, by rw [hpb]; trivial, ?_⟩⟩,
        I.symm hr⟩
      rw [hpr]; trivial
    · have hr := hp.mem_N b r hpb
      exact ⟨r, ⟨red_of_mem_blue hr hb, by rw [hp.symm b r hpb]; simp⟩, I.symm hr⟩
  calc I.blues.card ≤ _ := card_le_card hsub
    _ ≤ ∑ r ∈ I.reds.filter (fun v => p v ≠ none), (I.N r).card := card_biUnion_le
    _ ≤ ∑ r ∈ I.reds.filter (fun v => p v ≠ none), Δ := sum_le_sum fun r _ => hΔ r
    _ = Δ * _ := by rw [sum_const, smul_eq_mul, mul_comm]

lemma card_reds_add_blues : I.reds.card + I.blues.card = Fintype.card V := by
  rw [← card_union_of_disjoint, ← card_univ]
  · congr 1; ext v; cases h : I.red v <;> simp [h]
  · rw [disjoint_left]; intro v h1 h2; simp_all

end Bicoloured

/-! ### (9): accuracy of the estimate -/

/-- (9) and the final estimate of §6.3, as an inequality between reals: `n` nodes, `R` red nodes,
`Mj = |M_j|`, `Minf = |M_∞|`, sample frequencies `x = X/N` and `y = Y/N` within relative error `γ`
of `R/n` and `Mj/R`. If `n ≤ 2Δ |M_∞|`, `4Δγ = ε/2` and `|M_j| ≤ |M_∞| ≤ |M_j| + (ε/2)|M_∞|`, then
`|n x y - |M_∞|| ≤ ε |M_∞|`. -/
theorem estimate_error {n R Mj Minf x y γ ε Δ : ℝ} (hR : 0 < R) (hRn : R ≤ n) (hMj0 : 0 ≤ Mj)
    (hMjR : Mj ≤ R) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hγ0 : 0 ≤ γ)
    (hx : |x - R / n| < γ * (R / n)) (hy : |y - Mj / R| < γ * (Mj / R))
    (hnM : n ≤ 2 * Δ * Minf) (hγ : 4 * Δ * γ = ε / 2) (hM1 : Mj ≤ Minf)
    (hM2 : Minf ≤ Mj + ε / 2 * Minf) : |n * x * y - Minf| ≤ ε * Minf := by
  have hn : 0 < n := hR.trans_le hRn
  set q := Mj / R
  set p := R / n
  have hq1 : q ≤ 1 := (div_le_one hR).2 hMjR
  have hq0 : 0 ≤ q := div_nonneg hMj0 hR.le
  have hp0 : 0 ≤ p := div_nonneg hR.le hn.le
  have hnqp : n * q * p = Mj := by
    simp only [q, p]; field_simp
  have hsplit : n * x * y - Mj = n * x * (y - q) + n * q * (x - p) := by
    rw [← hnqp]; ring
  have h1 : |n * x * (y - q)| ≤ n * γ := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ n * x)]
    calc n * x * |y - q| ≤ n * 1 * (γ * q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx1 hn.le) hy.le (abs_nonneg _) (by positivity)
      _ ≤ n * γ := by
        have := mul_le_mul_of_nonneg_left hq1 (mul_nonneg hn.le hγ0)
        linarith
  have h2 : |n * q * (x - p)| ≤ γ * Mj := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ n * q)]
    calc n * q * |x - p| ≤ n * q * (γ * p) := mul_le_mul_of_nonneg_left hx.le (by positivity)
      _ = γ * Mj := by rw [← hnqp]; ring
  have h3 : |n * x * y - Mj| ≤ 2 * γ * n := by
    rw [hsplit]
    calc _ ≤ |n * x * (y - q)| + |n * q * (x - p)| := abs_add_le _ _
      _ ≤ n * γ + γ * Mj := add_le_add h1 h2
      _ ≤ 2 * γ * n := by nlinarith
  have h4 : 2 * γ * n ≤ ε / 2 * Minf := by
    rw [← hγ]; nlinarith
  have h5 : |Mj - Minf| ≤ ε / 2 * Minf := by
    rw [abs_le]; constructor <;> linarith
  calc |n * x * y - Minf| = |(n * x * y - Mj) + (Mj - Minf)| := by ring_nf
    _ ≤ |n * x * y - Mj| + |Mj - Minf| := abs_add_le _ _
    _ ≤ ε * Minf := by linarith

end Podc.TruncatedGaleShapley
