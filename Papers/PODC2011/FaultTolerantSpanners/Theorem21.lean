import Papers.PODC2011.FaultTolerantSpanners.Conversion
import Cslib.Foundations.Combinatorics.SimpleGraph.Minor

/-!
# Theorem 2.1 of Dinitz–Krauthgamer (PODC'11) with explicit constants

The paper: *if there is an algorithm that on every graph builds a `k`-spanner of size `f(n)`, then
there is an algorithm that on any graph builds with high probability an `r`-fault tolerant
`k`-spanner of size `O(r³ log n · f(2n/r))`.*

We instantiate `conversion_explicit` with the paper's parameters: `p = 1 - 1/r` (`m = r`; `m = 2`
when `r = 1`, as in the paper) and `α = ⌈8 r² (r + 2 + C) ln(n+1)⌉` iterations, and obtain
(`theorem_2_1`), for `1 ≤ r ≤ n`, every `C ∈ ℕ`, monotone `f` with `f 2 ≥ 1`:

`Pr[H is an r-FT k-spanner with |E(H)| ≤ (8C + 26) r³ ln(n+1) f(⌊2n/r⌋)]
   ≥ 1 - (n+1)^{-C} - α e^{-n^{1/3}/6}`.

The last term is the paper's Chernoff/union bound over the iterations for the size; it is only
needed when `r³ < n²` (otherwise the size bound holds deterministically, the paper's
"w.l.o.g. `r ≤ n^{2/3}`"), and it is `n^{-ω(1)}`.

Constants: the per-iteration success probability is `q = (1/m)²(1 - 1/m)^r ≥ 1/(8r²)`
(`q_ge`; the paper claims `≥ 1/(4r²)` for `r ≥ 2`, which is also true, and `1/8` for `r = 1`).
-/

open Finset SimpleGraph Cslib.Probability
open scoped ENNReal NNReal

namespace DinitzKrauthgamer

instance neZero_max_two (r : ℕ) : NeZero (max r 2) := ⟨by omega⟩

/-- `(1 - 1/r)^r ≥ e^{-2}` for `r ≥ 2`. -/
lemma one_sub_inv_pow_ge {r : ℕ} (hr : 2 ≤ r) :
    Real.exp (-2) ≤ (1 - 1 / (r : ℝ)) ^ r := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  -- `1 - 1/r ≥ exp(-1/(r-1))`
  have h1 : Real.exp (-(1 / ((r : ℝ) - 1))) ≤ 1 - 1 / (r : ℝ) := by
    have := Real.add_one_le_exp (1 / ((r : ℝ) - 1))
    rw [Real.exp_neg]
    have hpos : (0 : ℝ) < 1 / ((r : ℝ) - 1) + 1 := by positivity
    have heq : 1 - 1 / (r : ℝ) = (1 / ((r : ℝ) - 1) + 1)⁻¹ := by
      field_simp
      ring
    rw [heq]
    exact inv_anti₀ hpos this
  calc Real.exp (-2) ≤ Real.exp (-(1 / ((r : ℝ) - 1))) ^ r := by
        rw [← Real.exp_nat_mul, Real.exp_le_exp]
        rw [show (r : ℝ) * -(1 / ((r : ℝ) - 1)) = -(r / (r - 1)) by ring, neg_le_neg_iff,
          div_le_iff₀ hr1]
        linarith
    _ ≤ (1 - 1 / (r : ℝ)) ^ r := pow_le_pow_left₀ (Real.exp_pos _).le h1 r

/-- Per-iteration success probability: `(1/m)² (1 - 1/m)^r ≥ 1/(8 r²)` for `m = max r 2`. -/
lemma q_ge {r : ℕ} (hr : 1 ≤ r) :
    1 / (8 * (r : ℝ) ^ 2) ≤
      (1 / ((max r 2 : ℕ) : ℝ)) ^ 2 * (1 - 1 / ((max r 2 : ℕ) : ℝ)) ^ r := by
  rcases Nat.lt_or_ge r 2 with h | h
  · have : r = 1 := by omega
    subst this
    norm_num
  · rw [max_eq_left h]
    have he : Real.exp (-2) ≥ 1 / 8 := by
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h8 : Real.exp 2 ≤ 8 := by rw [h2]; nlinarith [Real.exp_pos 1]
      rw [Real.exp_neg, ge_iff_le, inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) h8
    have := one_sub_inv_pow_ge h
    have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
    calc 1 / (8 * (r : ℝ) ^ 2) = (1 / (r : ℝ)) ^ 2 * (1 / 8) := by field_simp
      _ ≤ (1 / (r : ℝ)) ^ 2 * (1 - 1 / (r : ℝ)) ^ r := by gcongr; linarith

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {w : Sym2 V → ℝ≥0} {k : ℕ} {f : ℕ → ℝ}

/-- The number of iterations used in Theorem 2.1. -/
noncomputable def numIter (n r C : ℕ) : ℕ :=
  ⌈8 * (r : ℝ) ^ 2 * ((r : ℝ) + 2 + C) * Real.log ((n : ℝ) + 1)⌉₊

/-- `0 ≤ (1/m)²(1 - 1/m)^r ≤ 1` for `m ≥ 1`. -/
lemma q_le_one {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    (1 / (m : ℝ)) ^ 2 * (1 - 1 / (m : ℝ)) ^ r ≤ 1 := by
  have h0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have h1 : 1 / (m : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hm
  calc (1 / (m : ℝ)) ^ 2 * (1 - 1 / (m : ℝ)) ^ r ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ h0 h1) (pow_le_one₀ (by linarith) (by linarith))
          (pow_nonneg (by linarith) _) zero_le_one
    _ = 1 := one_mul 1

/-- The correctness failure probability is at most `(n+1)^{-C}` with `α = numIter n r C`. -/
lemma failure_le {n r C : ℕ} (hr : 1 ≤ r) :
    ((n : ℝ) + 1) ^ r * (n : ℝ) ^ 2 *
        (1 - (1 / ((max r 2 : ℕ) : ℝ)) ^ 2 * (1 - 1 / ((max r 2 : ℕ) : ℝ)) ^ r) ^ numIter n r C
      ≤ 1 / ((n : ℝ) + 1) ^ C := by
  set q := (1 / ((max r 2 : ℕ) : ℝ)) ^ 2 * (1 - 1 / ((max r 2 : ℕ) : ℝ)) ^ r
  set α := numIter n r C
  set L := Real.log ((n : ℝ) + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hq := q_ge hr
  have hq1 : q ≤ 1 := q_le_one (by omega) r
  have hr2 : (0 : ℝ) < 8 * (r : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    positivity
  have hqpos : 0 ≤ q := le_trans (by positivity) hq
  have hα : 8 * (r : ℝ) ^ 2 * ((r : ℝ) + 2 + C) * L ≤ α := Nat.le_ceil _
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- `(1 - q)^α ≤ exp(-(r + 2 + C) L)`
  have h1 : (1 - q) ^ α ≤ Real.exp (-(((r : ℝ) + 2 + C) * L)) := by
    calc (1 - q) ^ α ≤ Real.exp (-q) ^ α := by
          gcongr
          linarith [Real.add_one_le_exp (-q)]
      _ = Real.exp (-(q * α)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(((r : ℝ) + 2 + C) * L)) := by
          rw [Real.exp_le_exp, neg_le_neg_iff]
          calc ((r : ℝ) + 2 + C) * L = 1 / (8 * (r : ℝ) ^ 2) *
                (8 * (r : ℝ) ^ 2 * ((r : ℝ) + 2 + C) * L) := by field_simp
            _ ≤ q * α := mul_le_mul hq hα (by positivity) hqpos
  -- `(n+1)^r n² ≤ exp((r+2) L)`
  have h2 : ((n : ℝ) + 1) ^ r * (n : ℝ) ^ 2 ≤ Real.exp (((r : ℝ) + 2) * L) := by
    rw [show ((r : ℝ) + 2) * L = (r + 2 : ℕ) * L by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log hn1, pow_add]
    gcongr
    linarith
  have h3 : 1 / ((n : ℝ) + 1) ^ C = Real.exp (-(C * L)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn1, one_div]
  calc ((n : ℝ) + 1) ^ r * (n : ℝ) ^ 2 * (1 - q) ^ α
      ≤ Real.exp (((r : ℝ) + 2) * L) * Real.exp (-(((r : ℝ) + 2 + C) * L)) :=
        mul_le_mul h2 h1 (pow_nonneg (by linarith) _) (Real.exp_pos _).le
    _ = 1 / ((n : ℝ) + 1) ^ C := by rw [h3, ← Real.exp_add]; ring_nf

/-- `numIter n r C ≤ (8C + 26) r³ ln(n+1)`, i.e. `α = O(r³ log n)`. -/
lemma numIter_le {n r C : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) :
    (numIter n r C : ℝ) ≤ (8 * C + 26) * (r : ℝ) ^ 3 * Real.log ((n : ℝ) + 1) := by
  set L := Real.log ((n : ℝ) + 1)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL : 1 / 2 ≤ L := by
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hL0 : 0 ≤ L := by linarith
  have h1 := Nat.ceil_lt_add_one (show 0 ≤ 8 * (r : ℝ) ^ 2 * ((r : ℝ) + 2 + C) * L by positivity)
  have hr3 : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ hr'
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have key : 8 * (r : ℝ) ^ 2 * ((r : ℝ) + 2 + C) ≤ (8 * C + 24) * (r : ℝ) ^ 3 := by
    have : (r : ℝ) + 2 + C ≤ (3 + C) * r := by nlinarith
    calc 8 * (r : ℝ) ^ 2 * ((r : ℝ) + 2 + C) ≤ 8 * (r : ℝ) ^ 2 * ((3 + C) * r) := by gcongr
      _ = (8 * C + 24) * (r : ℝ) ^ 3 := by ring
  unfold numIter
  calc (⌈8 * (r : ℝ) ^ 2 * ((r : ℝ) + 2 + C) * L⌉₊ : ℝ)
      ≤ 8 * (r : ℝ) ^ 2 * ((r : ℝ) + 2 + C) * L + 1 := h1.le
    _ ≤ (8 * C + 24) * (r : ℝ) ^ 3 * L + 2 * (r : ℝ) ^ 3 * L := by
        gcongr
        nlinarith
    _ = (8 * C + 26) * (r : ℝ) ^ 3 * L := by ring

/-- **Theorem 2.1 of Dinitz–Krauthgamer (PODC'11).** Let `A` build, on every induced subgraph
`G[S]` of the weighted graph `(G, w)`, a `k`-spanner with at most `f(|S|)` edges (`f` monotone,
`f 2 ≥ 1`). Run the conversion with `α = numIter n r C = ⌈8 r² (r+2+C) ln(n+1)⌉` iterations and
failure probability `1 - 1/r` per vertex (`1/2` if `r = 1`). Then, for `1 ≤ r ≤ n`, with probability
at least `1 - (n+1)^{-C} - α e^{-n^{1/3}/6}` the output `H` is an `r`-fault-tolerant `k`-spanner with
`|E(H)| ≤ (8C + 26) r³ ln(n+1) · f(⌊2n/r⌋)`. -/
theorem theorem_2_1 (A : SpannerAlg G w k f) (hk : 1 ≤ k) (hf : Monotone f) (hf2 : 1 ≤ f 2)
    {r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ Fintype.card V) (C : ℕ) :
    1 - 1 / ((Fintype.card V : ℝ) + 1) ^ C -
        numIter (Fintype.card V) r C * Real.exp (-((Fintype.card V : ℝ) ^ ((1 : ℝ) / 3) / 6)) ≤
      uprob (fun ω : Fin (numIter (Fintype.card V) r C) → V → Fin (max r 2) =>
        IsWeightedVFTSpanner G (ftUnion A ω) w r k ∧
        ((ftUnion A ω).edgeSet.ncard : ℝ) ≤ (8 * C + 26) * (r : ℝ) ^ 3 *
          Real.log ((Fintype.card V : ℝ) + 1) * f ⌊2 * (Fintype.card V : ℝ) / r⌋₊) := by
  set n := Fintype.card V with hn_def
  set α := numIter n r C
  set m := max r 2
  set L := Real.log ((n : ℝ) + 1)
  set K := (8 * C + 26) * (r : ℝ) ^ 3 * L * f ⌊2 * (n : ℝ) / r⌋₊
  have hn : 1 ≤ n := hr.trans hrn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hL : 1 / 2 ≤ L := by
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hfr : 1 ≤ f ⌊2 * (n : ℝ) / r⌋₊ := by
    refine hf2.trans (hf (Nat.le_floor ?_))
    rw [le_div_iff₀ (by linarith)]; push_cast; linarith
  have hmr : r ≤ m := le_max_left _ _
  have hm2r : (m : ℝ) ≤ 2 * r := by
    have : m ≤ 2 * r := max_le (by omega) (by omega)
    exact_mod_cast this
  have hfm : f ⌊2 * (n : ℝ) / m⌋₊ ≤ f ⌊2 * (n : ℝ) / r⌋₊ := by
    refine hf (Nat.floor_le_floor ?_)
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by exact_mod_cast hmr)
  have hαK : (α : ℝ) * f ⌊2 * (n : ℝ) / m⌋₊ ≤ K := by
    have := numIter_le (C := C) hr hn
    calc (α : ℝ) * f ⌊2 * (n : ℝ) / m⌋₊ ≤ (α : ℝ) * f ⌊2 * (n : ℝ) / r⌋₊ := by gcongr
      _ ≤ ((8 * C + 26) * (r : ℝ) ^ 3 * L) * f ⌊2 * (n : ℝ) / r⌋₊ :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = K := rfl
  have hfail := failure_le (n := n) (C := C) hr
  have hexp0 : 0 ≤ (α : ℝ) * Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 3) / 6)) := by positivity
  by_cases hbig : n ^ 2 ≤ r ^ 3
  · -- the size bound holds deterministically
    have hK : ((n : ℝ) ^ 2) ≤ K := by
      have h1 : ((n : ℝ) ^ 2) ≤ (r : ℝ) ^ 3 := by exact_mod_cast hbig
      have h2 : (1 : ℝ) ≤ (8 * C + 26) * L := by
        have : (0 : ℝ) ≤ C := Nat.cast_nonneg C
        nlinarith
      calc ((n : ℝ) ^ 2) ≤ (r : ℝ) ^ 3 * 1 * 1 := by linarith
        _ ≤ (r : ℝ) ^ 3 * ((8 * C + 26) * L) * f ⌊2 * (n : ℝ) / r⌋₊ := by
            gcongr
        _ = K := by ring
    have hmono := uprob_mono (Ω := Fin α → V → Fin m)
      (E := fun ω => IsWeightedVFTSpanner G (ftUnion A ω) w r k)
      (E' := fun ω => IsWeightedVFTSpanner G (ftUnion A ω) w r k ∧
        ((ftUnion A ω).edgeSet.ncard : ℝ) ≤ K)
      fun ω h => ⟨h, le_trans (by
        have := (ftUnion A ω).ncard_edgeSet_le_card_mul_card
        rw [Nat.card_eq_fintype_card] at this
        rw [sq]; exact_mod_cast this) hK⟩
    have hnot := uprob_not (Ω := Fin α → V → Fin m)
      (fun ω => IsWeightedVFTSpanner G (ftUnion A ω) w r k)
    have hbad := uprob_not_isVFT_le A hk r m α
    linarith
  · -- `r < n^{2/3}`: the Chernoff term is at most `e^{-n^{1/3}/6}`
    push Not at hbig
    have hexp : Real.exp (-((n : ℝ) / (3 * m))) ≤ Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 3) / 6)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      set t := (n : ℝ) ^ ((1 : ℝ) / 3)
      have ht0 : 0 ≤ t := by positivity
      have ht3 : t ^ 3 = n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have hrt : (r : ℝ) < t ^ 2 := by
        have : (r : ℝ) ^ 3 < (t ^ 2) ^ 3 := by
          rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ht3]; exact_mod_cast hbig
        exact lt_of_pow_lt_pow_left₀ 3 (by positivity) this
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : t * (3 * m) ≤ t * (6 * r) := mul_le_mul_of_nonneg_left (by linarith) ht0
      nlinarith
    have hconv := conversion_explicit A hk hf r m α
    have hmono := uprob_mono (Ω := Fin α → V → Fin m)
      (E := fun ω => IsWeightedVFTSpanner G (ftUnion A ω) w r k ∧
        ((ftUnion A ω).edgeSet.ncard : ℝ) ≤ α * f ⌊2 * (n : ℝ) / m⌋₊)
      (E' := fun ω => IsWeightedVFTSpanner G (ftUnion A ω) w r k ∧
        ((ftUnion A ω).edgeSet.ncard : ℝ) ≤ K)
      fun ω h => ⟨h.1, h.2.trans hαK⟩
    have hαe : (α : ℝ) * Real.exp (-((n : ℝ) / (3 * m))) ≤
        α * Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 3) / 6)) := by gcongr
    linarith

end DinitzKrauthgamer
