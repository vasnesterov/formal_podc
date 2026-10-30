/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

-- CSLib candidate: Cslib/Computability/CommunicationComplexity/GapDisjointness.lean

public import Cslib.Computability.CommunicationComplexity.Protocol
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Preorder.Finite

/-!
# Deterministic communication complexity of gap disjointness

*Gap disjointness* is the promise problem in which Alice and Bob hold subsets `x, y` of an
`N`-element set `ι` and must answer one value `b` if `x ∩ y = ∅` and the other value `!b` if
`x` and `y` are *far from disjoint*, here `N ≤ 12 · |x ∩ y|`; on the remaining inputs any answer is
allowed. Deterministically this is as hard as disjointness up to a constant factor:
every deterministic protocol exchanges at least `N / 3` bits (`gapDisj_lowerBound`).

This is Lemma 2.5 of Censor-Hillel–Dory, *Distributed Spanner Approximation* (PODC 2018), where
it is stated with `Ω(N)` (see also Rao–Yehudayoff, *Communication Complexity and Applications*).

## Proof

Gilbert–Varshamov plus a fooling set. With `r = ⌊(N - 1) / 6⌋`, a maximal code `C` of minimum
Hamming distance `> r` covers the cube by Hamming balls of radius `r`, and a ball of radius `r`
has at most `6 ^ N / 5 ^ (N - r)` points, so `2 ^ N · 5 ^ (N - r) ≤ |C| · 6 ^ N`. The pairs
`(x, xᶜ)`, `x ∈ C`, are disjoint, while for `x ≠ x'` in `C` one of the crossed pairs `(x, x'ᶜ)`,
`(x', xᶜ)` has intersection at least `d(x, x') / 2 > r / 2`, i.e. is far from disjoint. So they
form a fooling set and `|C| ≤ 2 ^ c`, which yields `N ≤ 3 c`.

## Main definitions and results

* `interCard x y`: the size of the intersection of two subsets given as indicator vectors.
* `gapDisj_lowerBound`: Lemma 2.5 (deterministic gap disjointness needs `≥ N / 3` bits).
* `gapDisj_lowerBound_of_eval`: the same for a protocol that answers `!disj x y` (or `disj x y`)
  on all inputs satisfying the promise.
-/

@[expose] public section

namespace Cslib.CommunicationComplexity.Protocol

open Finset

variable {ι : Type*} [Fintype ι]

/-- Size of the intersection of two subsets of `ι` given as indicator vectors. -/
def interCard (x y : ι → Bool) : ℕ :=
  (univ.filter fun i => x i = true ∧ y i = true).card

/-- The intersections of `x` with the complement of `x'` and of `x'` with the complement of `x`
together form the symmetric difference of `x` and `x'`. -/
theorem interCard_not_add_interCard_not (x x' : ι → Bool) :
    interCard x (fun i => !x' i) + interCard x' (fun i => !x i) = hammingDist x x' := by
  classical
  unfold interCard hammingDist
  rw [card_filter, card_filter, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  cases h : x i <;> cases h' : x' i <;> simp [h, h']

/-- A Hamming ball of radius `r ≤ N` in `{0,1}^N` has at most `6 ^ N / 5 ^ (N - r)` points. -/
theorem card_hammingBall_mul_le [DecidableEq ι] (c : ι → Bool) (r : ℕ) :
    (univ.filter fun x : ι → Bool => hammingDist x c ≤ r).card * 5 ^ (Fintype.card ι - r) ≤
      6 ^ Fintype.card ι := by
  classical
  set N := Fintype.card ι
  let T : Finset (Finset ι) := (univ : Finset ι).powerset.filter fun t => t.card ≤ r
  have hball : (univ.filter fun x : ι → Bool => hammingDist x c ≤ r).card ≤ T.card := by
    refine card_le_card_of_injOn (fun x => univ.filter fun i => x i ≠ c i) ?_ ?_
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simp only [T, coe_filter, mem_powerset, subset_univ, true_and, Set.mem_ofPred_eq]
      exact hx
    · intro x _ x' _ h
      funext i
      have := congrArg (i ∈ ·) h
      simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
      cases hx : x i <;> cases hx' : x' i <;> cases hc : c i <;> simp_all
  calc (univ.filter fun x : ι → Bool => hammingDist x c ≤ r).card * 5 ^ (N - r)
      ≤ T.card * 5 ^ (N - r) := Nat.mul_le_mul_right _ hball
    _ = ∑ _t ∈ T, 5 ^ (N - r) := by simp
    _ ≤ ∑ t ∈ T, 5 ^ (N - t.card) := by
        refine sum_le_sum fun t ht => Nat.pow_le_pow_right (by norm_num) ?_
        have := (mem_filter.1 ht).2
        omega
    _ ≤ ∑ t ∈ (univ : Finset ι).powerset, 5 ^ (N - t.card) :=
        sum_le_sum_of_subset (filter_subset _ _)
    _ = ∑ t ∈ (univ : Finset ι).powerset, 1 ^ t.card * 5 ^ ((univ : Finset ι).card - t.card) := by
        simp [N]
    _ = 6 ^ N := by rw [sum_pow_mul_eq_add_pow]; norm_num [N]

/-- **Gilbert–Varshamov covering**: there is a code `C ⊆ {0,1}^ι` with pairwise Hamming distances
`> r` such that every word is within distance `r` of `C`. -/
theorem exists_code_covering [DecidableEq ι] (r : ℕ) :
    ∃ C : Finset (ι → Bool), (∀ x ∈ C, ∀ x' ∈ C, x ≠ x' → r < hammingDist x x') ∧
      ∀ x, ∃ c ∈ C, hammingDist x c ≤ r := by
  classical
  let codes : Finset (Finset (ι → Bool)) :=
    univ.filter fun C => ∀ x ∈ C, ∀ x' ∈ C, x ≠ x' → r < hammingDist x x'
  obtain ⟨C, hC, hmax⟩ := exists_maximal (s := codes) ⟨∅, by simp [codes]⟩
  have hC' := (mem_filter.1 hC).2
  refine ⟨C, hC', fun x => ?_⟩
  by_contra hx
  push Not at hx
  have hxC : x ∉ C := fun h => by simpa using hx x h
  have hins : insert x C ∈ codes := by
    refine mem_filter.2 ⟨mem_univ _, fun a ha a' ha' hne => ?_⟩
    rcases mem_insert.1 ha with h1 | h1 <;> rcases mem_insert.1 ha' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · subst h1; exact hx a' h2
    · subst h2; rw [hammingDist_comm]; exact hx a h1
    · exact hC' a h1 a' h2 hne
  exact hxC (hmax hins (subset_insert _ _) (mem_insert_self _ _))

/-- Arithmetic core of `gapDisj_lowerBound`. -/
private lemma arith {N r K c : ℕ} (hr : 6 * r < N) (hK : K ≤ 2 ^ c)
    (h : 2 ^ N * 5 ^ (N - r) ≤ K * 6 ^ N) : N ≤ 3 * c := by
  by_contra hlt
  push Not at hlt
  have h1 : 2 ^ N * 5 ^ (N - r) ≤ 2 ^ c * 6 ^ N :=
    h.trans (Nat.mul_le_mul_right _ hK)
  have h2 := Nat.pow_le_pow_left h1 6
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul] at h2
  have h3 : 5 ^ (5 * N + 1) ≤ 5 ^ ((N - r) * 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (c * 6) * 4 ≤ 2 ^ (2 * N) := by
    rw [show 4 = 2 ^ 2 by rfl, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ (N * 6) * 5 ^ (5 * N + 1) * 4 ≤ 2 ^ (2 * N) * 6 ^ (N * 6) := by
    calc 2 ^ (N * 6) * 5 ^ (5 * N + 1) * 4 ≤ 2 ^ (N * 6) * 5 ^ ((N - r) * 6) * 4 := by
          gcongr
      _ ≤ 2 ^ (c * 6) * 6 ^ (N * 6) * 4 := by gcongr
      _ = 2 ^ (c * 6) * 4 * 6 ^ (N * 6) := by ring
      _ ≤ 2 ^ (2 * N) * 6 ^ (N * 6) := by gcongr
  have e1 : 2 ^ (N * 6) * 5 ^ (5 * N + 1) * 4 = 200000 ^ N * 20 := by
    have ha : 2 ^ (N * 6) = 64 ^ N := by rw [mul_comm, pow_mul]; norm_num
    have hb : 5 ^ (5 * N + 1) = 3125 ^ N * 5 := by rw [pow_succ, pow_mul]; norm_num
    rw [ha, hb, show (200000 : ℕ) = 64 * 3125 by norm_num, mul_pow]
    ring
  have e2 : 2 ^ (2 * N) * 6 ^ (N * 6) = 186624 ^ N := by
    rw [mul_comm N 6, pow_mul, pow_mul, ← mul_pow]; norm_num
  rw [e1, e2] at h5
  have : 186624 ^ N ≤ 200000 ^ N := Nat.pow_le_pow_left (by norm_num) N
  have : 0 < 200000 ^ N := by positivity
  omega

/-- **Lemma 2.5 of [Censor-Hillel–Dory, PODC 2018]** (gap disjointness, deterministic): a protocol
that answers `b` on disjoint inputs and `!b` on inputs that are far from disjoint
(`|ι| ≤ 12 · |x ∩ y|`) exchanges at least `|ι| / 3` bits. -/
theorem gapDisj_lowerBound {P : Protocol (ι → Bool) (ι → Bool) Bool} {c : ℕ} (b : Bool)
    (hdisj : ∀ x y, disj x y = true → P.eval x y = b)
    (hfar : ∀ x y, Fintype.card ι ≤ 12 * interCard x y → P.eval x y = !b)
    (hc : P.CostLE c) : Fintype.card ι ≤ 3 * c := by
  classical
  set N := Fintype.card ι with hN
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · omega
  set r := (N - 1) / 6
  have hr : 6 * r < N := by omega
  obtain ⟨C, hCdist, hCcov⟩ := exists_code_covering (ι := ι) r
  -- Covering: `2 ^ N · 5 ^ (N - r) ≤ |C| · 6 ^ N`.
  have hcover : 2 ^ N * 5 ^ (N - r) ≤ C.card * 6 ^ N := by
    have hsub : (univ : Finset (ι → Bool)) ⊆
        C.biUnion fun c => univ.filter fun x : ι → Bool => hammingDist x c ≤ r := by
      intro x _
      obtain ⟨c, hc, hxc⟩ := hCcov x
      exact mem_biUnion.2 ⟨c, hc, mem_filter.2 ⟨mem_univ _, hxc⟩⟩
    have h2N : (univ : Finset (ι → Bool)).card = 2 ^ N := by simp [hN]
    calc 2 ^ N * 5 ^ (N - r)
        ≤ (∑ c ∈ C, (univ.filter fun x : ι → Bool => hammingDist x c ≤ r).card) *
            5 ^ (N - r) := by
          rw [← h2N]
          exact Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
      _ = ∑ c ∈ C, (univ.filter fun x : ι → Bool => hammingDist x c ≤ r).card *
            5 ^ (N - r) := sum_mul _ _ _
      _ ≤ ∑ _c ∈ C, 6 ^ N := sum_le_sum fun c _ => card_hammingBall_mul_le c r
      _ = C.card * 6 ^ N := by simp
  -- Fooling set `{(x, xᶜ) | x ∈ C}`.
  let S : Finset ((ι → Bool) × (ι → Bool)) := C.image fun x => (x, fun i => !x i)
  have hinj : Function.Injective fun x : ι → Bool => (x, fun i => !x i) :=
    fun a b h => (Prod.ext_iff.1 h).1
  have hScard : S.card = C.card := card_image_of_injective _ hinj
  have hfool : IsFooling P.eval b S := by
    refine ⟨fun s hs => ?_, fun s hs t ht hst => ?_⟩
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hs
      exact hdisj _ _ (by simp [disj])
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hs
      obtain ⟨x', hx', rfl⟩ := mem_image.1 ht
      have hne : x ≠ x' := fun h => hst (by rw [h])
      have hd := hCdist x hx x' hx' hne
      have hsum := interCard_not_add_interCard_not x x'
      by_cases h : interCard x' (fun i => !x i) ≤ interCard x (fun i => !x' i)
      · left
        rw [hfar x _ (by dsimp only; omega)]
        cases b <;> simp
      · right
        rw [hfar x' _ (by dsimp only; omega)]
        cases b <;> simp
  have hK : C.card ≤ 2 ^ c := hScard ▸ card_le_of_fooling P c b S hc hfool
  exact arith hr hK hcover

/-- Gap disjointness in the "do the sets intersect?" form: a deterministic protocol that outputs
`!disj x y` (`true` iff `x ∩ y ≠ ∅`) whenever `x ∩ y = ∅` or `|ι| ≤ 12 · |x ∩ y|` exchanges at least
`|ι| / 3` bits. -/
theorem gapDisj_lowerBound_of_eval {P : Protocol (ι → Bool) (ι → Bool) Bool} {c : ℕ}
    (hP : ∀ x y, disj x y = true ∨ Fintype.card ι ≤ 12 * interCard x y →
      P.eval x y = !disj x y)
    (hc : P.CostLE c) : Fintype.card ι ≤ 3 * c := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · omega
  refine gapDisj_lowerBound (P := P) false (fun x y h => by rw [hP x y (Or.inl h), h]; rfl)
    (fun x y h => ?_) hc
  rw [hP x y (Or.inr h)]
  have : 0 < interCard x y := by omega
  obtain ⟨i, hi⟩ := card_pos.1 this
  simp only [mem_filter, mem_univ, true_and] at hi
  simp only [disj, Bool.not_false]
  simpa using ⟨i, hi⟩

end Cslib.CommunicationComplexity.Protocol
