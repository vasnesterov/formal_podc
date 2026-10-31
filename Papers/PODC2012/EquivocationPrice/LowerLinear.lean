import Papers.PODC2012.EquivocationPrice.Projection
import Papers.PODC2012.EquivocationPrice.Bisection

/-!
# Theorem 3: the linear lower bound `Tₙ(h) ≥ (3/4) n (1 - o(1))`

Jaffe, Moscibroda, Sen, *On the Price of Equivocation in Byzantine Agreement*, PODC 2012,
Section 3.1.

For `n = 3k` and `h ≤ k`, fix a `k`-set `C`. Every bisection `(S, U \ S)` of `U = V \ C`
together with `C` is a valid colouring (all parts have `k ≥ h` vertices and the sizes sum to
`n ≥ (n + 3h)/2`), so `h`-disjointness gives a rainbow hyperedge, whose projection by `C` crosses
the bisection. By Lemma 4 the projection has at least `|U|/2 = k` edges. Summing over all
`C(n, k)` sets `C` and using that every hyperedge is counted at most `3 · C(n-3, k-1)` times
(`sum_card_proj_le`) gives `k · C(n, k) ≤ 3 · C(n-3, k-1) · |E|`, i.e.
`|E| ≥ (n-1)(n-2)/(4n/3 - 2)` (`theorem_3`, `theorem_3_nat`, `theorem_3'`).

The paper silently assumes `3 ∣ n`. For arbitrary `n ≥ 3` we take `|C| = ⌊n/3⌋` and bisect the
remaining `n - ⌊n/3⌋` vertices into parts of sizes `⌊·/2⌋, ⌈·/2⌉ ≥ h`, which gives
`3(n-1)(n-2) ≤ 2(2n-1)|E|` (`theorem_3_general`) and hence the explicit form
`|E| ≥ 3n/4 - 2` of the paper's `Tₙ(h) ≥ (3/4) n (1 - o(1))` for all `n` and all `h ≤ n/3`
(`theorem_3_asymptotic`).
-/

namespace Podc.EquivocationPrice

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] {E : Finset (Finset V)} {h k : ℕ}

/-- Step 1 of the proof of Theorem 3 of [JMS12]: for `n = 3k`, `h ≤ k` and `|C| = k`, the
projection of an `h`-disjoint hypergraph by `C` has at least `k = n/3` edges. -/
theorem le_card_proj (hE : Uniform3 E) (hD : HDisjoint E h) (hn : Fintype.card V = 3 * k)
    (hh : h ≤ k) {C : Finset V} (hC : C.card = k) : k ≤ (proj E C).card := by
  have hU : (univ \ C).card = 2 * k := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn, hC]; omega
  suffices (univ \ C).card ≤ 2 * (proj E C).card by omega
  refine lemma_4 (univ \ C) (proj E C) (proj_subset_compl hE) fun S hSU hS => ?_
  rw [hU, show 2 * k / 2 = k by omega] at hS
  have hSc : ((univ \ C) \ S).card = k := by rw [card_sdiff_of_subset hSU, hU, hS]; omega
  have hval : ValidColoring h S ((univ \ C) \ S) C := by
    refine ⟨disjoint_sdiff, ?_, ?_, by omega, by omega, by omega, by omega⟩
    · exact Finset.disjoint_of_subset_left hSU sdiff_disjoint
    · exact Finset.disjoint_of_subset_left sdiff_subset sdiff_disjoint
  obtain ⟨x, hx, y, hy, z, hz, he⟩ := hD _ _ _ hval
  have hxC : x ∉ C := by have := hSU hx; simp_all
  have hy' := mem_sdiff.mp hy
  have hyC : y ∉ C := by have := hy'.1; simp_all
  have hxy : x ≠ y := fun hxy => hy'.2 (hxy ▸ hx)
  refine ⟨{x, y}, pair_mem_proj hxC hyC hz hxy he, ⟨x, by simp [hx]⟩, ⟨y, by simp [hy'.2]⟩⟩

/-- **Theorem 3** of [JMS12], exact form for `n = 3k`: an `h`-disjoint 3-uniform hypergraph
with `h ≤ n/3` satisfies `k · C(n, k) ≤ 3 · C(n-3, k-1) · |E|` (the paper's inequality (1)
combined with the overcounting bound). -/
theorem theorem_3 (hE : Uniform3 E) (hD : HDisjoint E h) (hn : Fintype.card V = 3 * k)
    (hh : h ≤ k) :
    k * (3 * k).choose k ≤ 3 * (3 * k - 3).choose (k - 1) * E.card := by
  calc k * (3 * k).choose k
      = ∑ _C ∈ (univ : Finset V).powersetCard k, k := by
        rw [sum_const, card_powersetCard, card_univ, hn, smul_eq_mul, mul_comm]
    _ ≤ ∑ C ∈ (univ : Finset V).powersetCard k, (proj E C).card :=
        sum_le_sum fun C hC => le_card_proj hE hD hn hh (mem_powersetCard.mp hC).2
    _ ≤ 3 * (Fintype.card V - 3).choose (k - 1) * E.card := sum_card_proj_le hE k
    _ = _ := by rw [hn]

/-- `C(3k, k) / C(3k-3, k-1) = 3(3k-1)(3k-2) / (2k(2k-1))`, cleared of denominators. -/
theorem choose_three_mul_identity (k : ℕ) (hk : 1 ≤ k) :
    2 * (2 * k - 1) * (k * (3 * k).choose k) =
      3 * ((3 * k - 1) * (3 * k - 2)) * (3 * k - 3).choose (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e1 : 2 * (2 * (j + 1) - 1) = 2 * (2 * j + 1) := by omega
  have e2 : 3 * (j + 1) - 1 = 3 * j + 2 := by omega
  have e3 : 3 * (j + 1) - 2 = 3 * j + 1 := by omega
  have e4 : 3 * (j + 1) - 3 = 3 * j := by omega
  have e5 : 3 * (j + 1) = 3 * j + 2 + 1 := by omega
  rw [e1, e2, e3, e4, Nat.add_sub_cancel, e5]
  have h1 := Nat.add_one_mul_choose_eq (3 * j + 2) j
  have h2 := Nat.choose_mul_succ_eq (3 * j + 1) j
  have h3 := Nat.choose_mul_succ_eq (3 * j) j
  rw [show 3 * j + 1 + 1 - j = 2 * j + 2 by omega, show 3 * j + 1 + 1 = 3 * j + 2 by omega] at h2
  rw [show 3 * j + 1 - j = 2 * j + 1 by omega] at h3
  zify at h1 h2 h3 ⊢
  linear_combination (-(2 : ℤ) * (2 * j + 1)) * h1 - 3 * (2 * j + 1) * h2 -
    3 * (3 * j + 2) * h3

/-- **Theorem 3** of [JMS12], integer form for `n = 3k`: `(n-1)(n-2) ≤ 2(2k-1)|E|`. -/
theorem theorem_3_nat (hE : Uniform3 E) (hD : HDisjoint E h) (hn : Fintype.card V = 3 * k)
    (hh : h ≤ k) (hk : 1 ≤ k) :
    (3 * k - 1) * (3 * k - 2) ≤ 2 * (2 * k - 1) * E.card := by
  have h3 := Nat.mul_le_mul_left (2 * (2 * k - 1)) (theorem_3 hE hD hn hh)
  rw [choose_three_mul_identity k hk] at h3
  have hpos : 0 < 3 * (3 * k - 3).choose (k - 1) := by
    have := Nat.choose_pos (show k - 1 ≤ 3 * k - 3 by omega); omega
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc 3 * (3 * k - 3).choose (k - 1) * ((3 * k - 1) * (3 * k - 2))
      = 3 * ((3 * k - 1) * (3 * k - 2)) * (3 * k - 3).choose (k - 1) := by ring
    _ ≤ 2 * (2 * k - 1) * (3 * (3 * k - 3).choose (k - 1) * E.card) := h3
    _ = _ := by ring

/-- **Theorem 3** of [JMS12], the paper's displayed bound: for `n = 3k ≥ 3` and `h ≤ n/3`,
an `h`-disjoint 3-uniform hypergraph has at least `(n-1)(n-2)/(4n/3 - 2) = (3/4) n (1 - o(1))`
hyperedges. -/
theorem theorem_3' (hE : Uniform3 E) (hD : HDisjoint E h) (hn : Fintype.card V = 3 * k)
    (hh : h ≤ k) (hk : 1 ≤ k) :
    ((Fintype.card V : ℝ) - 1) * (Fintype.card V - 2) / (4 * Fintype.card V / 3 - 2) ≤ E.card := by
  have H := theorem_3_nat hE hD hn hh hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 3 * (j + 1) - 1 = 3 * j + 2 by omega, show 3 * (j + 1) - 2 = 3 * j + 1 by omega,
    show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at H
  have H' : ((3 * j + 2 : ℕ) : ℝ) * ((3 * j + 1 : ℕ) : ℝ) ≤ 2 * ((2 * j + 1 : ℕ) : ℝ) * E.card := by
    exact_mod_cast H
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  rw [hn, div_le_iff₀ (by push_cast; linarith)]
  push_cast at H' ⊢
  linarith

/-! ### All `n`, not only multiples of 3 -/

/-- Step 1 of the proof of Theorem 3 of [JMS12] for arbitrary `n` and `|C| = k`: if `h ≤ k`,
`2h ≤ n - k` and `3h ≤ n`, then every bisection of `V \ C` (parts of sizes `⌊(n-k)/2⌋` and
`⌈(n-k)/2⌉`) together with `C` is a valid colouring, so by Lemma 4 the projection by `C` has at
least `(n - k)/2` edges. -/
theorem le_two_mul_card_proj (hE : Uniform3 E) (hD : HDisjoint E h) {C : Finset V}
    (hhk : h ≤ C.card) (hh2 : 2 * h ≤ Fintype.card V - C.card) (hh3 : 3 * h ≤ Fintype.card V) :
    Fintype.card V - C.card ≤ 2 * (proj E C).card := by
  have hU : (univ \ C).card = Fintype.card V - C.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
  rw [← hU]
  refine lemma_4 (univ \ C) (proj E C) (proj_subset_compl hE) fun S hSU hS => ?_
  have hSc : ((univ \ C) \ S).card = (univ \ C).card - S.card := card_sdiff_of_subset hSU
  have hCle : C.card ≤ Fintype.card V := card_le_univ C
  have hval : ValidColoring h S ((univ \ C) \ S) C := by
    refine ⟨disjoint_sdiff, ?_, ?_, by omega, by omega, by omega, by omega⟩
    · exact Finset.disjoint_of_subset_left hSU sdiff_disjoint
    · exact Finset.disjoint_of_subset_left sdiff_subset sdiff_disjoint
  obtain ⟨x, hx, y, hy, z, hz, he⟩ := hD _ _ _ hval
  have hxC : x ∉ C := by have := hSU hx; simp_all
  have hy' := mem_sdiff.mp hy
  have hyC : y ∉ C := by have := hy'.1; simp_all
  have hxy : x ≠ y := fun hxy => hy'.2 (hxy ▸ hx)
  refine ⟨{x, y}, pair_mem_proj hxC hyC hz hxy he, ⟨x, by simp [hx]⟩, ⟨y, by simp [hy'.2]⟩⟩

/-- `C(n, k) · k (n-k)(n-k-1) = n(n-1)(n-2) · C(n-3, k-1)` for `1 ≤ k ≤ n - 2`. -/
theorem choose_mul_identity (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    n.choose k * (k * (n - k) * (n - k - 1)) = n * (n - 1) * (n - 2) * (n - 3).choose (k - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = q + r + 3 := ⟨n - q - 3, by omega⟩
  rw [show q + r + 3 - (q + 1) = r + 2 by omega, show r + 2 - 1 = r + 1 by omega,
    show q + r + 3 - 1 = q + r + 2 by omega, show q + r + 3 - 2 = q + r + 1 by omega,
    show q + r + 3 - 3 = q + r by omega, show q + 1 - 1 = q by omega]
  have h1 : (q + r + 3) * (q + r + 2).choose q = (q + r + 3).choose (q + 1) * (q + 1) :=
    Nat.add_one_mul_choose_eq (q + r + 2) q
  have h2 : (q + r + 1).choose q * (q + r + 2) = (q + r + 2).choose q * (r + 2) := by
    have := Nat.choose_mul_succ_eq (q + r + 1) q
    rwa [show q + r + 1 + 1 - q = r + 2 by omega] at this
  have h3 : (q + r).choose q * (q + r + 1) = (q + r + 1).choose q * (r + 1) := by
    have := Nat.choose_mul_succ_eq (q + r) q
    rwa [show q + r + 1 - q = r + 1 by omega] at this
  zify at h1 h2 h3 ⊢
  linear_combination (-((r : ℤ) + 2) * (r + 1)) * h1 - ((q : ℤ) + r + 3) * (r + 1) * h2 -
    ((q : ℤ) + r + 3) * (q + r + 2) * h3

/-- **Theorem 3** of [JMS12] for every `n ≥ 3` (not only multiples of 3): with
`|C| = ⌊n/3⌋`, an `h`-disjoint 3-uniform hypergraph with `h ≤ n/3` satisfies
`3(n-1)(n-2) ≤ 2(2n-1)|E|`, i.e. `|E| ≥ 3(n-1)(n-2)/(2(2n-1))`. -/
theorem theorem_3_general (hE : Uniform3 E) (hD : HDisjoint E h)
    (hh : 3 * h ≤ Fintype.card V) (hn : 3 ≤ Fintype.card V) :
    3 * ((Fintype.card V - 1) * (Fintype.card V - 2)) ≤
      2 * (2 * Fintype.card V - 1) * E.card := by
  set n := Fintype.card V with hn_def
  set k := n / 3 with hk_def
  have hk1 : 1 ≤ k := by omega
  -- summing Step 1 over all `k`-sets `C`
  have hsum : (n - k) * n.choose k ≤ 6 * (n - 3).choose (k - 1) * E.card := by
    calc (n - k) * n.choose k
        = ∑ _C ∈ (univ : Finset V).powersetCard k, (n - k) := by
          rw [sum_const, card_powersetCard, card_univ, smul_eq_mul, mul_comm]
      _ ≤ ∑ C ∈ (univ : Finset V).powersetCard k, 2 * (proj E C).card := by
          refine sum_le_sum fun C hC => ?_
          have hCk := (mem_powersetCard.mp hC).2
          have := le_two_mul_card_proj hE hD (C := C) (by omega) (by omega) hh
          rwa [hCk] at this
      _ = 2 * ∑ C ∈ (univ : Finset V).powersetCard k, (proj E C).card := by rw [mul_sum]
      _ ≤ 2 * (3 * (n - 3).choose (k - 1) * E.card) :=
          Nat.mul_le_mul_left 2 (sum_card_proj_le hE k)
      _ = 6 * (n - 3).choose (k - 1) * E.card := by ring
  have hid := choose_mul_identity n k hk1 (by omega)
  have hpos : 0 < (n - 3).choose (k - 1) := Nat.choose_pos (by omega)
  -- `n(n-1)(n-2) ≤ 6 k (n-k-1) |E|`
  have h2 : n * (n - 1) * (n - 2) ≤ 6 * (k * (n - k - 1)) * E.card := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    have := Nat.mul_le_mul_left (k * (n - k - 1)) hsum
    calc (n - 3).choose (k - 1) * (n * (n - 1) * (n - 2))
        = n.choose k * (k * (n - k) * (n - k - 1)) := by rw [hid]; ring
      _ = k * (n - k - 1) * ((n - k) * n.choose k) := by ring
      _ ≤ k * (n - k - 1) * (6 * (n - 3).choose (k - 1) * E.card) := this
      _ = _ := by ring
  -- `9 k (n-k-1) ≤ n (2n-1)`
  have h3 : 9 * (k * (n - k - 1)) ≤ n * (2 * n - 1) := by
    have e1 : 3 * k ≤ n := by omega
    have e2 : 3 * (n - k - 1) ≤ 2 * n - 1 := by omega
    calc 9 * (k * (n - k - 1)) = (3 * k) * (3 * (n - k - 1)) := by ring
      _ ≤ n * (2 * n - 1) := Nat.mul_le_mul e1 e2
  have h4 : 3 * n * (3 * ((n - 1) * (n - 2))) ≤ 3 * n * (2 * (2 * n - 1) * E.card) := by
    calc 3 * n * (3 * ((n - 1) * (n - 2))) = 9 * (n * (n - 1) * (n - 2)) := by ring
      _ ≤ 9 * (6 * (k * (n - k - 1)) * E.card) := Nat.mul_le_mul_left 9 h2
      _ = 6 * (9 * (k * (n - k - 1))) * E.card := by ring
      _ ≤ 6 * (n * (2 * n - 1)) * E.card := by gcongr
      _ = 3 * n * (2 * (2 * n - 1) * E.card) := by ring
  exact Nat.le_of_mul_le_mul_left h4 (by omega)

/-- **Theorem 3** of [JMS12] (`Tₙ(h) ≥ (3/4) n (1 - o(1))` for `h ≤ n/3`), with an explicit
error term: every `h`-disjoint 3-uniform hypergraph on `n` vertices with `h ≤ n/3` has at least
`3n/4 - 2` hyperedges, for every `n`. -/
theorem theorem_3_asymptotic (hE : Uniform3 E) (hD : HDisjoint E h)
    (hh : 3 * h ≤ Fintype.card V) :
    3 * Fintype.card V ≤ 4 * E.card + 8 := by
  by_cases hn : 3 ≤ Fintype.card V
  · have H := theorem_3_general hE hD hh hn
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨Fintype.card V - 3, by omega⟩
    rw [hm, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show 2 * (m + 3) - 1 = 2 * m + 5 by omega] at H
    rw [hm]
    nlinarith
  · omega

end Podc.EquivocationPrice
