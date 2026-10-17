import Cslib.Foundations.Combinatorics.SimpleGraph.BlockingSet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/BlockingSet.lean (append to the existing file)

/-!
# Size of graphs with small blocking sets, in `n^{1 + 1/k}` form

`IsBlockingSet.ncard_edgeSet_mul_le` (blocking set + Moore bound) gives, for every `s, d` with
`2 D s ≤ n` and `s ≤ d ^ k`, the natural-number bound `|E| (s - 1) ≤ 2 d n (n - 1)`. Choosing
`s = ⌊n / 2D⌋` and `d = ⌈s^{1/k}⌉` turns it into the bound used by Bodwin–Patel (PODC'19,
Corollary 2) and Dinitz–Robelle (PODC'20, Theorem 8).

## Main statements

* `Nat.cast_le_rpow_of_forall_mul_sub_one_le`: the arithmetic step,
  `m ≤ 8 (2D)^{1 - 1/k} n^{1 + 1/k}`.
* `SimpleGraph.IsBlockingSet.ncard_edgeSet_le_rpow`: a graph with a `2k`-blocking set of size
  `≤ D |E|` has `|E| ≤ 8 (2D)^{1 - 1/k} n^{1 + 1/k}` edges.
* `Real.two_mul_rpow_le_of_le_mul`: `(2D)^{1 - 1/k} ≤ 2 c f^{1 - 1/k}` for `D ≤ c f`, `c ≥ 1`;
  `SimpleGraph.IsBlockingSet.ncard_edgeSet_le_mul_rpow`: hence `|E| ≤ 16 c f^{1 - 1/k} n^{1 + 1/k}`.
-/

open Finset

/-- Real form of the blocking-set size bound: from `2 m ≤ n (n - 1)` and the bounds
`m (s - 1) ≤ 2 d n (n - 1)` for all `s, d` with `2 D s ≤ n` and `s ≤ d ^ k`, derive
`m ≤ 8 (2D)^{1 - 1/k} n^{1 + 1/k}`. -/
theorem Nat.cast_le_rpow_of_forall_mul_sub_one_le {k D n m : ℕ} (hk : 1 ≤ k) (hD : 1 ≤ D)
    (hm : 2 * m ≤ n * (n - 1))
    (h : ∀ s d : ℕ, 2 * D * s ≤ n → s ≤ d ^ k → m * (s - 1) ≤ 2 * d * (n * (n - 1))) :
    (m : ℝ) ≤ 8 * (2 * D : ℝ) ^ (1 - 1 / (k : ℝ)) * (n : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  set e : ℝ := 1 / (k : ℝ) with he
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by rw [he, div_le_one (by linarith)]; exact hkR
  have hDR : (1:ℝ) ≤ D := by exact_mod_cast hD
  have h2D : (0:ℝ) < 2 * D := by linarith
  have hX : (2 * D : ℝ) ^ (1 - e) * (2 * D : ℝ) ^ e = 2 * D := by
    rw [← Real.rpow_add h2D]; simp
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : m = 0 := by simpa using hm
    subst this; simp only [Nat.cast_zero]; positivity
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hY : (n:ℝ) ^ (1 + e) = n * (n:ℝ) ^ e := by
    rw [Real.rpow_add hnR, Real.rpow_one]
  have hmR : 2 * (m:ℝ) ≤ n * n := by
    have : 2 * m ≤ n * n := hm.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast this
  have hA : 0 ≤ (2 * D : ℝ) ^ (1 - e) := by positivity
  have hB : 0 ≤ (n : ℝ) ^ (1 + e) := by positivity
  by_cases hsmall : n < 8 * D
  · have h1 : (n:ℝ) ^ (1 - e) ≤ (4 * (2 * D) : ℝ) ^ (1 - e) := by
      apply Real.rpow_le_rpow hnR.le _ (by linarith)
      have : (n:ℝ) < 8 * D := by exact_mod_cast hsmall
      linarith
    rw [Real.mul_rpow (by norm_num) h2D.le] at h1
    have h4 : (4:ℝ) ^ (1 - e) ≤ 4 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by linarith)
    have hnn : (n:ℝ) * n = (n:ℝ) ^ (1 + e) * (n:ℝ) ^ (1 - e) := by
      rw [← Real.rpow_add hnR, show (1 + e) + (1 - e) = ((2:ℕ):ℝ) by push_cast; ring,
        Real.rpow_natCast]; ring
    have h5 : (n:ℝ) ^ (1 + e) * (n:ℝ) ^ (1 - e) ≤
        (n:ℝ) ^ (1 + e) * (4 * (2 * D : ℝ) ^ (1 - e)) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h4 hA)) hB
    nlinarith [mul_nonneg hA hB]
  · push Not at hsmall
    set s := n / (2 * D) with hs
    have hsD : s * (2 * D) ≤ n := Nat.div_mul_le_self _ _
    have hs4 : 4 ≤ s := by rw [hs, Nat.le_div_iff_mul_le (by omega)]; omega
    have hlt : n < s * (2 * D) + 2 * D := Nat.lt_div_mul_add (by omega)
    set d := ⌈(s:ℝ) ^ e⌉₊ with hd
    have hsR : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
    have hsd : s ≤ d ^ k := by
      have : (s:ℝ) ≤ (d:ℝ) ^ k := by
        calc (s:ℝ) = ((s:ℝ) ^ e) ^ k := by
              rw [he, one_div, Real.rpow_inv_natCast_pow (by positivity) (by omega)]
          _ ≤ (d:ℝ) ^ k := pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) k
      exact_mod_cast this
    have hmain := h s d (by rw [mul_comm]; exact hsD) hsd
    have hmainR : (m:ℝ) * ((s:ℝ) - 1) ≤ 2 * d * (n * n) := by
      have h' : m * (s - 1) ≤ 2 * d * (n * n) :=
        hmain.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
      have : ((m * (s - 1) : ℕ) : ℝ) ≤ ((2 * d * (n * n) : ℕ) : ℝ) := by exact_mod_cast h'
      push_cast [Nat.cast_sub (by omega : 1 ≤ s)] at this
      exact this
    have hse1 : 1 ≤ (s:ℝ) ^ e := Real.one_le_rpow hsR he0
    have hdR : (d:ℝ) ≤ 2 * (s:ℝ) ^ e := by
      have := Nat.ceil_lt_add_one (show 0 ≤ (s:ℝ) ^ e by positivity)
      linarith
    have hltR : (n:ℝ) < s * (2 * D) + 2 * D := by exact_mod_cast hlt
    have hsmallR : (8 * D : ℝ) ≤ n := by exact_mod_cast hsmall
    have hs1 : (n:ℝ) ≤ 4 * D * ((s:ℝ) - 1) := by nlinarith
    -- m n ≤ 16 D s^e n^2
    have hm1 : (m:ℝ) * n ≤ 16 * D * (s:ℝ) ^ e * n * n := by
      have hm0 : (0:ℝ) ≤ m := by positivity
      calc (m:ℝ) * n ≤ m * (4 * D * ((s:ℝ) - 1)) := mul_le_mul_of_nonneg_left hs1 hm0
        _ = 4 * D * (m * ((s:ℝ) - 1)) := by ring
        _ ≤ 4 * D * (2 * d * (n * n)) := mul_le_mul_of_nonneg_left hmainR (by positivity)
        _ ≤ 4 * D * (2 * (2 * (s:ℝ) ^ e) * (n * n)) := by gcongr
        _ = 16 * D * (s:ℝ) ^ e * n * n := by ring
    have hm2 : (m:ℝ) ≤ 16 * D * (s:ℝ) ^ e * n := by
      have : (m:ℝ) * n ≤ (16 * D * (s:ℝ) ^ e * n) * n := by linarith
      exact le_of_mul_le_mul_right this hnR
    have hsle : (s:ℝ) ≤ n / (2 * D) := by
      rw [le_div_iff₀ h2D]; exact_mod_cast hsD
    have hse : (s:ℝ) ^ e ≤ (n:ℝ) ^ e / (2 * D : ℝ) ^ e := by
      rw [← Real.div_rpow hnR.le h2D.le]
      exact Real.rpow_le_rpow (by positivity) hsle he0
    have hDe : 0 < (2 * D : ℝ) ^ e := by positivity
    have hm3 : (m:ℝ) * (2 * D : ℝ) ^ e ≤
        (8 * (2 * D : ℝ) ^ (1 - e) * (n:ℝ) ^ (1 + e)) * (2 * D : ℝ) ^ e := by
      have h6 : (m:ℝ) ≤ 16 * D * n * ((n:ℝ) ^ e / (2 * D : ℝ) ^ e) := by
        calc (m:ℝ) ≤ 16 * D * (s:ℝ) ^ e * n := hm2
          _ = 16 * D * n * (s:ℝ) ^ e := by ring
          _ ≤ 16 * D * n * ((n:ℝ) ^ e / (2 * D : ℝ) ^ e) := by gcongr
      have h7 : (m:ℝ) * (2 * D : ℝ) ^ e ≤ 16 * D * n * (n:ℝ) ^ e := by
        have := mul_le_mul_of_nonneg_right h6 hDe.le
        rwa [mul_assoc, div_mul_cancel₀ _ hDe.ne'] at this
      calc (m:ℝ) * (2 * D : ℝ) ^ e ≤ 16 * D * n * (n:ℝ) ^ e := h7
        _ = 8 * ((2 * D : ℝ) ^ (1 - e) * (2 * D : ℝ) ^ e) * (n * (n:ℝ) ^ e) := by
          rw [hX]; ring
        _ = (8 * (2 * D : ℝ) ^ (1 - e) * (n:ℝ) ^ (1 + e)) * (2 * D : ℝ) ^ e := by
          rw [hY]; ring
    exact le_of_mul_le_mul_right hm3 hDe

/-- The constant of the blocking-set size bound: if `0 ≤ D ≤ c f` with `c ≥ 1` and `f ≥ 0`, then
`(2D)^{1 - 1/k} ≤ 2 c f^{1 - 1/k}`. -/
theorem Real.two_mul_rpow_le_of_le_mul {k : ℕ} {D c f : ℝ} (hk : 1 ≤ k) (hD0 : 0 ≤ D)
    (hf : 0 ≤ f) (hc : 1 ≤ c) (hD : D ≤ c * f) :
    (2 * D) ^ (1 - 1 / (k : ℝ)) ≤ 2 * c * f ^ (1 - 1 / (k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hkR
  have ha1 : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  calc (2 * D) ^ (1 - 1 / (k : ℝ)) ≤ ((2 * c) * f) ^ (1 - 1 / (k : ℝ)) :=
        Real.rpow_le_rpow (by positivity) (by linarith) ha0
    _ = (2 * c) ^ (1 - 1 / (k : ℝ)) * f ^ (1 - 1 / (k : ℝ)) :=
        Real.mul_rpow (by positivity) hf
    _ ≤ 2 * c * f ^ (1 - 1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by linarith) ha1)
          (by positivity)

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- **Size of a graph with a small blocking set** (Moore-bound form; Bodwin–Patel, PODC'19,
Corollary 2; Dinitz–Robelle, PODC'20, Theorem 8): if `H` has a `2k`-blocking set of size
`≤ D |E(H)|` with `D ≥ 1`, then `|E(H)| ≤ 8 (2D)^{1 - 1/k} n^{1 + 1/k}`. -/
theorem IsBlockingSet.ncard_edgeSet_le_rpow {H : SimpleGraph V} {k D : ℕ}
    {B : Finset (V × Sym2 V)} (hk : 1 ≤ k) (hD : 1 ≤ D) (hB : H.IsBlockingSet (2 * k) B)
    (hBc : #B ≤ D * H.edgeSet.ncard) :
    (H.edgeSet.ncard : ℝ) ≤
      8 * (2 * D : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  classical
  refine Nat.cast_le_rpow_of_forall_mul_sub_one_le hk hD ?_
    fun s d hs hsd => hB.ncard_edgeSet_mul_le hk hBc hD hs hsd
  have h1 := H.card_edgeFinset_le_card_choose_two
  rw [Nat.choose_two_right] at h1
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have := Nat.mul_div_le (Fintype.card V * (Fintype.card V - 1)) 2
  omega

/-- **Size of a graph with a small blocking set**, with the constant simplified: if `H` has a
`2k`-blocking set of size `≤ D |E(H)|` with `1 ≤ D ≤ c f` and `c ≥ 1`, then
`|E(H)| ≤ 16 c f^{1 - 1/k} n^{1 + 1/k}`. -/
theorem IsBlockingSet.ncard_edgeSet_le_mul_rpow {H : SimpleGraph V} {k D : ℕ} {c f : ℝ}
    {B : Finset (V × Sym2 V)} (hk : 1 ≤ k) (hD : 1 ≤ D) (hB : H.IsBlockingSet (2 * k) B)
    (hBc : #B ≤ D * H.edgeSet.ncard) (hf : 0 ≤ f) (hc : 1 ≤ c) (hDc : (D : ℝ) ≤ c * f) :
    (H.edgeSet.ncard : ℝ) ≤
      16 * c * f ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  refine (hB.ncard_edgeSet_le_rpow hk hD hBc).trans ?_
  have h := Real.two_mul_rpow_le_of_le_mul hk (Nat.cast_nonneg D) hf hc hDc
  have hn : 0 ≤ (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by positivity
  calc 8 * (2 * D : ℝ) ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ))
      ≤ 8 * (2 * c * f ^ (1 - 1 / (k : ℝ))) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
        gcongr
    _ = 16 * c * f ^ (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by ring

end SimpleGraph
