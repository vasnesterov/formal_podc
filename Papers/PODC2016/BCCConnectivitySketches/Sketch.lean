import Mathlib

-- CSLib candidate: deterministic sparse linear sketches over `𝔽_p`

/-!
# Deterministic sparse linear sketches (Lemma 1)

Lemma 1 of Montealegre–Todinca (PODC 2016 BA): for `n, d > 0` there is a prime `p = 2^{O(d log n)}`
and a linear map `f : ℤⁿ → 𝔽_p` that is injective on `d`-sparse Boolean vectors.

Construction (as in the paper): `p = sketchPrime n d` is the least prime `> (1+n)^{2d}·n`
(by Bertrand's postulate `p ≤ 2(1+n)^{2d}·n`); `x = sketchPoint n d ∈ 𝔽_p` is a common non-root of
all polynomials `P(S) - P(S')`, `P(S) = ∑_{i ∈ S} X^i`, for distinct `S, S' ⊆ [n]` of size `≤ d`
(there are fewer than `(1+n)^{2d}` such pairs, each difference is a nonzero polynomial of degree
`< n`, so fewer than `p` roots in total). Then `f(v) = ∑ v_i x^i`.

Indices are `Fin n` (`0, …, n-1`; the paper's `x^{i-1}` for `i = 1, …, n`). We work with the
supports `S : Finset (Fin n)` of Boolean vectors: `sk x S = ∑_{i ∈ S} x^i = f (𝟙_S)`.
-/

namespace Podc.BCCConnectivitySketches

open Finset Polynomial

/-- `(1+n)^{2d} · n`, the lower bound for the prime of Lemma 1. -/
def sketchBound (n d : ℕ) : ℕ := (1 + n) ^ (2 * d) * n

/-- The prime of Lemma 1: the least prime `> (1+n)^{2d} · n`. -/
noncomputable def sketchPrime (n d : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (sketchBound n d + 1))

lemma sketchPrime_spec (n d : ℕ) :
    sketchBound n d + 1 ≤ sketchPrime n d ∧ (sketchPrime n d).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (sketchBound n d + 1))

lemma sketchPrime_prime (n d : ℕ) : (sketchPrime n d).Prime := (sketchPrime_spec n d).2

lemma lt_sketchPrime (n d : ℕ) : sketchBound n d < sketchPrime n d := (sketchPrime_spec n d).1

instance (n d : ℕ) : Fact (sketchPrime n d).Prime := ⟨sketchPrime_prime n d⟩

/-- Bertrand's postulate: `p ≤ 2 (1+n)^{2d} n`, so `p = 2^{O(d log n)}`. -/
lemma sketchPrime_le {n : ℕ} (hn : 0 < n) (d : ℕ) : sketchPrime n d ≤ 2 * sketchBound n d := by
  have h0 : sketchBound n d ≠ 0 := by unfold sketchBound; positivity
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ h0
  exact (Nat.find_min' _ ⟨hlt, hq⟩).trans hle

/-- The sketch of a set of indices: `∑_{i ∈ S} x^i`. -/
def sk {n p : ℕ} (x : ZMod p) (S : Finset (Fin n)) : ZMod p := ∑ i ∈ S, x ^ (i : ℕ)

lemma sk_erase {n p : ℕ} (x : ZMod p) (S : Finset (Fin n)) {k : Fin n} (hk : k ∈ S) :
    sk x (S.erase k) = sk x S - x ^ (k : ℕ) := by
  unfold sk
  rw [← Finset.add_sum_erase S _ hk]
  ring

/-- The polynomial `P(S) = ∑_{i ∈ S} X^i`. -/
noncomputable def poly {n p : ℕ} (S : Finset (Fin n)) : (ZMod p)[X] := ∑ i ∈ S, X ^ (i : ℕ)

lemma eval_poly {n p : ℕ} (x : ZMod p) (S : Finset (Fin n)) : (poly S).eval x = sk x S := by
  simp [poly, sk, eval_finsetSum]

lemma coeff_poly {n p : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (poly (p := p) S).coeff i = if i ∈ S then 1 else 0 := by
  simp only [poly, finsetSum_coeff, coeff_X_pow, Fin.val_inj]
  exact Finset.sum_ite_eq S i (fun _ => (1 : ZMod p))

lemma natDegree_poly_le {n p : ℕ} (S : Finset (Fin n)) : (poly (p := p) S).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_X_pow_le _).trans i.2.le

lemma poly_sub_ne_zero {n p : ℕ} [Fact p.Prime] {S S' : Finset (Fin n)} (h : S ≠ S') :
    poly (p := p) S - poly S' ≠ 0 := by
  intro h0
  apply h
  ext i
  have := congrArg (fun q : (ZMod p)[X] => q.coeff i) h0
  simp only [coeff_sub, coeff_poly, coeff_zero] at this
  by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;> simp_all

/-- Sets of size at most `d`. -/
def small (n d : ℕ) : Finset (Finset (Fin n)) := univ.filter fun S => S.card ≤ d

lemma mem_small {n d : ℕ} {S : Finset (Fin n)} : S ∈ small n d ↔ S.card ≤ d := by simp [small]

/-- There are at most `(1+n)^d` sets of size `≤ d` (they inject into `Fin d → Option (Fin n)`). -/
lemma card_small_le (n d : ℕ) : (small n d).card ≤ (1 + n) ^ d := by
  classical
  let g : Finset (Fin n) → Fin d → Option (Fin n) := fun T i =>
    if h : i.1 < T.card then some (T.equivFin.symm ⟨i.1, h⟩) else none
  have hmem : ∀ T : Finset (Fin n), T.card ≤ d → ∀ v, v ∈ T ↔ ∃ i, g T i = some v := by
    intro T hT v
    constructor
    · intro hv
      refine ⟨⟨(T.equivFin ⟨v, hv⟩).1, by omega⟩, ?_⟩
      simp [g]
    · rintro ⟨i, hi⟩
      simp only [g] at hi
      split_ifs at hi with h
      · simp only [Option.some.injEq] at hi
        rw [← hi]; exact (T.equivFin.symm _).2
  have hinj : Set.InjOn g (small n d) := by
    intro T hT T' hT' he
    rw [mem_coe, mem_small] at hT hT'
    ext v
    rw [hmem T hT, hmem T' hT', he]
  calc _ ≤ (univ : Finset (Fin d → Option (Fin n))).card :=
        card_le_card_of_injOn g (fun _ _ => mem_coe.2 (mem_univ _)) hinj
    _ = (1 + n) ^ d := by simp [add_comm]

/-- The bad points: roots of some `P(S) - P(S')`, `S ≠ S'` small. -/
noncomputable def badPoints (n d p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  ((small n d ×ˢ small n d).filter fun q => q.1 ≠ q.2).biUnion
    fun q => (poly (p := p) q.1 - poly q.2).roots.toFinset

lemma card_badPoints_le (n d p : ℕ) [Fact p.Prime] : (badPoints n d p).card ≤ sketchBound n d := by
  unfold badPoints sketchBound
  refine card_biUnion_le.trans ?_
  calc ∑ q ∈ (small n d ×ˢ small n d).filter (fun q => q.1 ≠ q.2),
        (poly (p := p) q.1 - poly q.2).roots.toFinset.card
      ≤ ∑ _q ∈ (small n d ×ˢ small n d).filter (fun q => q.1 ≠ q.2), n := by
        refine sum_le_sum fun q _ => ?_
        refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
        exact (natDegree_sub_le _ _).trans (max_le (natDegree_poly_le _) (natDegree_poly_le _))
    _ ≤ (small n d ×ˢ small n d).card * n := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ ≤ (1 + n) ^ (2 * d) * n := by
        rw [card_product, two_mul, pow_add]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (card_small_le n d) (card_small_le n d))

lemma exists_good_point (n d : ℕ) : ∃ x : ZMod (sketchPrime n d), x ∉ badPoints n d (sketchPrime n d) := by
  by_contra h
  push Not at h
  have h1 : (univ : Finset (ZMod (sketchPrime n d))).card ≤ (badPoints n d _).card :=
    card_le_card fun x _ => h x
  rw [card_univ, ZMod.card] at h1
  exact absurd ((card_badPoints_le n d _).trans_lt (lt_sketchPrime n d)) (not_lt.2 h1)

/-- The evaluation point `x(n, d)` of Lemma 1 (a fixed common non-root; the paper takes the least
one, any fixed choice works). -/
noncomputable def sketchPoint (n d : ℕ) : ZMod (sketchPrime n d) := (exists_good_point n d).choose

/-- **Injectivity of the sketch** on sets of size `≤ d`. -/
theorem sk_injOn (n d : ℕ) {S S' : Finset (Fin n)} (hS : S.card ≤ d) (hS' : S'.card ≤ d)
    (h : sk (sketchPoint n d) S = sk (sketchPoint n d) S') : S = S' := by
  by_contra hne
  have hx : sketchPoint n d ∉ badPoints n d (sketchPrime n d) := (exists_good_point n d).choose_spec
  apply hx
  simp only [badPoints, mem_biUnion, mem_filter, mem_product, Multiset.mem_toFinset]
  refine ⟨(S, S'), ⟨⟨mem_small.2 hS, mem_small.2 hS'⟩, hne⟩, ?_⟩
  rw [mem_roots (poly_sub_ne_zero hne), IsRoot, eval_sub, eval_poly, eval_poly]
  exact sub_eq_zero.2 h

/-- The linear sketch `f(v) = ∑ v_i x^i` over `𝔽_p`. -/
noncomputable def sketchMap (n d : ℕ) : (Fin n → ℤ) →ₗ[ℤ] ZMod (sketchPrime n d) where
  toFun v := ∑ i, (v i : ZMod (sketchPrime n d)) * sketchPoint n d ^ (i : ℕ)
  map_add' v w := by simp [add_mul, sum_add_distrib]
  map_smul' c v := by simp [mul_sum, mul_assoc]

/-- `d`-sparse Boolean vectors. -/
def SparseBool (n d : ℕ) : Set (Fin n → ℤ) :=
  {b | (∀ i, b i = 0 ∨ b i = 1) ∧ (univ.filter fun i => b i ≠ 0).card ≤ d}

lemma sketchMap_bool (n d : ℕ) {b : Fin n → ℤ} (hb : ∀ i, b i = 0 ∨ b i = 1) :
    sketchMap n d b = sk (sketchPoint n d) (univ.filter fun i => b i ≠ 0) := by
  simp only [sketchMap, LinearMap.coe_mk, AddHom.coe_mk, sk, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  rcases hb i with h | h <;> simp [h]

/-- **Lemma 1** of [Montealegre–Todinca]: for `n > 0` there is a prime `p ≤ 2(1+n)^{2d} n`
(so `p = 2^{O(d log n)}`) and a `ℤ`-linear map `f : ℤⁿ → 𝔽_p` injective on `d`-sparse Boolean
vectors. -/
theorem lemma_1 (n d : ℕ) (hn : 0 < n) :
    ∃ p, p.Prime ∧ p ≤ 2 * ((1 + n) ^ (2 * d) * n) ∧
      ∃ f : (Fin n → ℤ) →ₗ[ℤ] ZMod p, Set.InjOn f (SparseBool n d) := by
  refine ⟨sketchPrime n d, sketchPrime_prime n d, sketchPrime_le hn d, sketchMap n d, ?_⟩
  rintro b ⟨hb, hbd⟩ b' ⟨hb', hbd'⟩ h
  rw [sketchMap_bool n d hb, sketchMap_bool n d hb'] at h
  have hS := sk_injOn n d hbd hbd' h
  funext i
  have := congrArg (i ∈ ·) hS
  simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
  rcases hb i with h1 | h1 <;> rcases hb' i with h2 | h2 <;> simp_all

end Podc.BCCConnectivitySketches
