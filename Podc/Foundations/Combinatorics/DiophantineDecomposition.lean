/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Foundations/Combinatorics/DiophantineDecomposition.lean
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Small decompositions of solutions of homogeneous linear Diophantine inequalities

Let `A` be an `e × n` integer matrix with entries bounded by `M ≥ 1` in absolute value. Every
natural solution `x ∈ ℕⁿ` of `A x ≥ 0` is a sum of solutions `y` of `A y ≥ 0` of `ℓ₁`-norm at most
`(2M) ^ (2 ^ e - 1)`. This is a weak (doubly exponential) form of Pottier's bound on the size of
Hilbert bases (L. Pottier, *Minimal solutions of linear Diophantine systems: bounds and
algorithms*, RTA 1991), which is all that is needed for qualitative "small basis" arguments.

The proof is by induction on the number of rows, using a combinatorial partition lemma: a
multiset of integers in `[-L, L]` (`L ≥ 1`) with sum `0` splits into zero-sum parts of size at
most `2L` (`Cslib.DiophantineDecomposition.exists_partition_sum_eq_zero`). The proof of this lemma
orders the elements greedily so that all partial sums lie in `(-L, L]` and applies the pigeonhole
principle to `2L + 1` partial sums.

## Main results

* `Cslib.DiophantineDecomposition.exists_partition_sum_eq_zero`: the zero-sum partition lemma.
* `Cslib.DiophantineDecomposition.exists_partition_sum_nonneg`: its nonnegative-sum variant.
* `Cslib.exists_small_decomposition`: the decomposition theorem.
-/

namespace Cslib

namespace DiophantineDecomposition

open Multiset

variable {α : Type*}

/-- Greedy ordering: from a zero-sum multiset with weights in `[-L, L]` one can extract any
number `n ≤ card s` of elements, as a list, so that all partial sums lie in `(-L, L]`. -/
theorem exists_greedy_list (f : α → ℤ) (L : ℕ) (hL : 1 ≤ L) (s : Multiset α)
    (hf : ∀ a ∈ s, |f a| ≤ L) (hs : (s.map f).sum = 0) :
    ∀ n ≤ card s, ∃ l : List α, (l : Multiset α) ≤ s ∧ l.length = n ∧
      ∀ k ≤ n, -(L : ℤ) < ((l.take k).map f).sum ∧ ((l.take k).map f).sum ≤ L := by
  classical
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨[], by simp, rfl, fun k _ => ?_⟩
    simp only [List.take_nil, List.map_nil, List.sum_nil]
    constructor <;> omega
  | succ n ih =>
    intro hn
    obtain ⟨l, hls, hlen, hpart⟩ := ih (by omega)
    set r := s - (l : Multiset α) with hr
    have hrs : r + l = s := tsub_add_cancel_of_le hls
    have hrcard : card r = card s - n := by
      rw [hr, Multiset.card_sub hls, Multiset.coe_card, hlen]
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, Multiset.card_zero] at hrcard
      omega
    set c := (l.map f).sum with hc
    have hcL : -(L : ℤ) < c ∧ c ≤ L := by
      have := hpart n le_rfl
      rwa [← hlen, List.take_length] at this
    have hrsum : (r.map f).sum = -c := by
      have : (r.map f).sum + c = 0 := by
        rw [hc, ← Multiset.sum_coe, ← Multiset.map_coe, ← Multiset.sum_add, ← Multiset.map_add,
          hrs, hs]
      omega
    have hmemr : ∀ a ∈ r, a ∈ s := fun a ha => Multiset.mem_of_le (Multiset.sub_le_self _ _) ha
    -- choose the next element
    obtain ⟨a, har, ha⟩ : ∃ a ∈ r, -(L : ℤ) < c + f a ∧ c + f a ≤ L := by
      have hfa := fun a (ha : a ∈ r) => abs_le.1 (hf a (hmemr a ha))
      by_cases hc0 : c ≤ 0
      · obtain ⟨a, har, ha⟩ : ∃ a ∈ r, 0 ≤ f a := by
          by_contra hne
          push Not at hne
          have := Multiset.sum_lt_sum_of_nonempty (s := r) (f := f) (g := fun _ => (0 : ℤ))
            (by simpa using hr0) hne
          simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_zero] at this
          omega
        exact ⟨a, har, by have := hfa a har; constructor <;> omega⟩
      · obtain ⟨a, har, ha⟩ : ∃ a ∈ r, f a < 0 := by
          by_contra hne
          push Not at hne
          have := Multiset.sum_nonneg (s := r.map f) (by simpa using hne)
          omega
        exact ⟨a, har, by have := hfa a har; constructor <;> omega⟩
    refine ⟨l ++ [a], ?_, by simp [hlen], fun k hk => ?_⟩
    · rw [← Multiset.coe_add, Multiset.coe_singleton, ← hrs, add_comm r]
      exact add_le_add_right (Multiset.singleton_le.2 har) _
    · rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
      · rw [List.take_append_of_le_length (by omega)]
        exact hpart k (by omega)
      · rw [List.take_of_length_le (by simp; omega)]
        simpa [← hc] using ha

/-- A zero-sum multiset with weights in `[-L, L]` (`L ≥ 1`) and at least `2L` elements has a
nonempty zero-sum sub-multiset with at most `2L` elements. -/
theorem exists_small_zero_sum_le (f : α → ℤ) (L : ℕ) (hL : 1 ≤ L) (s : Multiset α)
    (hf : ∀ a ∈ s, |f a| ≤ L) (hs : (s.map f).sum = 0) (hcard : 2 * L ≤ card s) :
    ∃ t ≤ s, t ≠ 0 ∧ card t ≤ 2 * L ∧ (t.map f).sum = 0 := by
  obtain ⟨l, hls, hlen, hpart⟩ := exists_greedy_list f L hL s hf hs (2 * L) hcard
  let g : ℕ → ℤ := fun k => ((l.take k).map f).sum
  obtain ⟨x, hx, y, hy, hxy, hgxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (2 * L + 1)) (t := Finset.Ioc (-(L : ℤ)) L) (f := g)
    (by rw [Int.card_Ioc, Finset.card_range]; omega)
    (fun k hk => by
      rw [Finset.mem_coe, Finset.mem_Ioc]
      exact hpart k (by rw [Finset.mem_coe, Finset.mem_range] at hk; omega))
  rw [Finset.mem_range] at hx hy
  -- reduce to `i < j`
  obtain ⟨i, j, hij, hj, hg⟩ : ∃ i j, i < j ∧ j ≤ 2 * L ∧ g i = g j := by
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, h, by omega, hgxy⟩
    · exact ⟨y, x, h, by omega, hgxy.symm⟩
  refine ⟨((l.take j).drop i : List α), ?_, ?_, ?_, ?_⟩
  · exact le_trans (Multiset.coe_le.2 ((List.drop_sublist _ _).trans
      (List.take_sublist _ _)).subperm) hls
  · simp only [ne_eq, Multiset.coe_eq_zero, List.drop_eq_nil_iff, List.length_take]
    omega
  · simp only [Multiset.coe_card, List.length_drop, List.length_take]
    omega
  · have hsplit := congrArg (fun l' : List α => (l'.map f).sum)
      (List.take_append_drop i (l.take j))
    simp only [List.take_take, List.map_append, List.sum_append] at hsplit
    rw [min_eq_left hij.le] at hsplit
    have : g i = ((l.take i).map f).sum := rfl
    have : g j = ((l.take j).map f).sum := rfl
    rw [Multiset.map_coe, Multiset.sum_coe]
    omega

/-- **Zero-sum partition lemma.** A multiset whose weights lie in `[-L, L]` (`L ≥ 1`) and sum to
`0` is the union of zero-sum parts with at most `2L` elements each. -/
theorem exists_partition_sum_eq_zero (f : α → ℤ) (L : ℕ) (hL : 1 ≤ L) (s : Multiset α)
    (hf : ∀ a ∈ s, |f a| ≤ L) (hs : (s.map f).sum = 0) :
    ∃ P : Multiset (Multiset α), P.join = s ∧ ∀ p ∈ P, card p ≤ 2 * L ∧ (p.map f).sum = 0 := by
  classical
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    by_cases hcard : 2 * L ≤ card s
    · obtain ⟨t, hts, ht0, htcard, htsum⟩ := exists_small_zero_sum_le f L hL s hf hs hcard
      have hlt : s - t < s := by
        refine lt_of_le_of_ne (Multiset.sub_le_self _ _) fun h => ht0 ?_
        have := congrArg Multiset.card h
        rw [Multiset.card_sub hts] at this
        have := Multiset.card_le_card hts
        exact Multiset.card_eq_zero.1 (by omega)
      have hst : s - t + t = s := tsub_add_cancel_of_le hts
      obtain ⟨P, hP, hPp⟩ := ih (s - t) hlt
        (fun a ha => hf a (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha))
        (by
          have : ((s - t).map f).sum + (t.map f).sum = (s.map f).sum := by
            rw [← Multiset.sum_add, ← Multiset.map_add, hst]
          omega)
      refine ⟨t ::ₘ P, ?_, ?_⟩
      · rw [Multiset.join_cons, hP, add_comm, hst]
      · intro p hp
        rcases Multiset.mem_cons.1 hp with rfl | hp
        · exact ⟨htcard, htsum⟩
        · exact hPp p hp
    · refine ⟨{s}, Multiset.singleton_join s, fun p hp => ?_⟩
      rw [Multiset.mem_singleton] at hp
      subst hp
      exact ⟨by omega, hs⟩

/-- Weight on `Option α` used to reduce the nonnegative case to the zero-sum case: the dummy
element `none` has weight `-1`. -/
private def optWeight (f : α → ℤ) : Option α → ℤ := fun o => o.elim (-1) f

private theorem filterMap_id_aux (f : α → ℤ) (p : Multiset (Option α)) :
    card (p.filterMap id) ≤ card p ∧
      (p.map (optWeight f)).sum ≤ ((p.filterMap id).map f).sum := by
  induction p using Multiset.induction_on with
  | empty => simp
  | cons o p ih =>
    cases o with
    | none =>
      rw [Multiset.filterMap_cons_none _ _ rfl]
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, optWeight,
        Option.elim_none]
      omega
    | some a =>
      rw [Multiset.filterMap_cons_some id (some a) p rfl]
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, optWeight,
        Option.elim_some] at ih ⊢
      omega

/-- **Nonnegative-sum partition lemma.** A multiset whose weights lie in `[-L, L]` (`L ≥ 1`) and
have nonnegative sum is the union of parts with nonnegative sum and at most `2L` elements each. -/
theorem exists_partition_sum_nonneg (f : α → ℤ) (L : ℕ) (hL : 1 ≤ L) (s : Multiset α)
    (hf : ∀ a ∈ s, |f a| ≤ L) (hs : 0 ≤ (s.map f).sum) :
    ∃ P : Multiset (Multiset α), P.join = s ∧ ∀ p ∈ P, card p ≤ 2 * L ∧ 0 ≤ (p.map f).sum := by
  set n := (s.map f).sum.toNat with hn
  have hn' : (n : ℤ) = (s.map f).sum := Int.toNat_of_nonneg hs
  let s' : Multiset (Option α) := s.map some + Multiset.replicate n none
  obtain ⟨P', hP', hP'p⟩ := exists_partition_sum_eq_zero (optWeight f) L hL s'
    (by
      intro o ho
      rcases Multiset.mem_add.1 ho with ho | ho
      · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 ho
        exact hf a ha
      · rw [Multiset.eq_of_mem_replicate ho]
        simp only [optWeight, Option.elim_none, abs_neg, abs_one]
        exact_mod_cast hL)
    (by
      simp only [s', Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def,
        optWeight, Option.elim_some, Multiset.map_replicate, Option.elim_none,
        Multiset.sum_replicate, nsmul_eq_mul, mul_neg, mul_one]
      linarith)
  refine ⟨P'.map (Multiset.filterMap id), ?_, ?_⟩
  · rw [← Multiset.filterMap_join, hP']
    simp only [s', Multiset.filterMap_add, Multiset.filterMap_map, Function.id_comp,
      Multiset.filterMap_some]
    have : (Multiset.replicate n (none : Option α)).filterMap id = 0 := by
      induction n with
      | zero => simp
      | succ k ih =>
        rw [Multiset.replicate_succ, Multiset.filterMap_cons_none _ _ rfl]
        exact ih
    rw [this, add_zero]
  · intro p hp
    obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.1 hp
    obtain ⟨h1, h2⟩ := filterMap_id_aux f p'
    obtain ⟨h3, h4⟩ := hP'p p' hp'
    exact ⟨h1.trans h3, h4 ▸ h2⟩

/-- The value of a linear form `y ↦ ∑ j, c j * y j` on a sum of vectors. -/
theorem sum_map_linear {V : Type*} [Fintype V] (c : V → ℤ) (s : Multiset (V → ℕ)) :
    (s.map fun y => ∑ j, c j * (y j : ℤ)).sum = ∑ j, c j * (s.sum j : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, Pi.add_apply, Nat.cast_add, mul_add,
      Finset.sum_add_distrib]

/-- The `ℓ₁`-norm of a sum of vectors in `ℕ^V` is the sum of their norms. -/
theorem sum_map_norm {V : Type*} [Fintype V] (s : Multiset (V → ℕ)) :
    (s.map fun y => ∑ j, y j).sum = ∑ j, s.sum j := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, Pi.add_apply, Finset.sum_add_distrib]

/-- The decomposition theorem for the rows in a finite set `R`, by induction on `R`. -/
theorem exists_small_decomposition_finset {ι V : Type*} [DecidableEq ι] [Fintype V] (M : ℕ)
    (hM : 1 ≤ M) (A : ι → V → ℤ) (hA : ∀ i j, |A i j| ≤ M) (x : V → ℕ) (R : Finset ι)
    (hx : ∀ i ∈ R, 0 ≤ ∑ j, A i j * (x j : ℤ)) :
    ∃ s : Multiset (V → ℕ), s.sum = x ∧ ∀ y ∈ s, (∀ i ∈ R, 0 ≤ ∑ j, A i j * (y j : ℤ)) ∧
      ∑ j, y j ≤ (2 * M) ^ (2 ^ R.card - 1) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨∑ j, Multiset.replicate (x j) (Pi.single j 1), ?_, fun y hy => ⟨by simp, ?_⟩⟩
    · rw [Multiset.sum_sum]
      simp only [Multiset.sum_replicate]
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    · obtain ⟨j, -, hy⟩ := Multiset.mem_sum.1 hy
      rw [Multiset.eq_of_mem_replicate hy]
      simp
  | insert i R hi ih =>
    obtain ⟨s, hsx, hsy⟩ := ih (fun i' hi' => hx i' (Finset.mem_insert_of_mem hi'))
    set K := (2 * M) ^ (2 ^ R.card - 1) with hK
    have hK1 : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
    let f : (V → ℕ) → ℤ := fun y => ∑ j, A i j * (y j : ℤ)
    have hf : ∀ y ∈ s, |f y| ≤ ((M * K : ℕ) : ℤ) := by
      intro y hy
      calc |f y| ≤ ∑ j, |A i j * (y j : ℤ)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |A i j| * (y j : ℤ) := by simp [abs_mul]
        _ ≤ ∑ j, (M : ℤ) * (y j : ℤ) := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hA i j) (by positivity)
        _ = (M : ℤ) * ((∑ j, y j : ℕ) : ℤ) := by rw [← Finset.mul_sum]; push_cast; rfl
        _ ≤ ((M * K : ℕ) : ℤ) := by
          rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hsy y hy).2) (by positivity)
    have hfs : 0 ≤ (s.map f).sum := by
      rw [sum_map_linear, hsx]
      exact hx i (Finset.mem_insert_self _ _)
    obtain ⟨P, hPs, hPp⟩ := exists_partition_sum_nonneg f (M * K) (Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (by omega) (by omega))) s hf hfs
    refine ⟨P.map Multiset.sum, ?_, ?_⟩
    · rw [← Multiset.sum_join, hPs, hsx]
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hy
      have hps : ∀ z ∈ p, z ∈ s := fun z hz => hPs ▸ Multiset.mem_join.2 ⟨p, hp, hz⟩
      obtain ⟨hpcard, hpsum⟩ := hPp p hp
      refine ⟨fun i' hi' => ?_, ?_⟩
      · rw [← sum_map_linear]
        rcases Finset.mem_insert.1 hi' with rfl | hi'
        · exact hpsum
        · exact Multiset.sum_nonneg fun z hz => by
            obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hz
            exact (hsy w (hps w hw)).1 i' hi'
      · rw [← sum_map_norm, Finset.card_insert_of_notMem hi]
        calc (p.map fun y => ∑ j, y j).sum ≤ card (p.map fun y => ∑ j, y j) • K :=
              Multiset.sum_le_card_nsmul _ _ fun n hn => by
                obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hn
                exact (hsy w (hps w hw)).2
          _ ≤ (2 * (M * K)) * K := by
            rw [Multiset.card_map, smul_eq_mul]
            exact Nat.mul_le_mul_right _ hpcard
          _ = (2 * M) ^ (2 ^ (R.card + 1) - 1) := by
            have h1 : 1 ≤ 2 ^ R.card := Nat.one_le_two_pow
            have h2 : 2 ^ (R.card + 1) - 1 = (2 ^ R.card - 1) + (2 ^ R.card - 1) + 1 := by
              rw [pow_succ]; omega
            rw [h2, pow_succ, pow_add, ← hK]
            ring

end DiophantineDecomposition

open DiophantineDecomposition in
/-- **Small decomposition theorem** (weak form of Pottier's bound). Let `A` be an integer matrix
with rows indexed by `ι` and entries bounded by `M ≥ 1` in absolute value. Every `x ∈ ℕ^V` with
`A x ≥ 0` is a sum of vectors `y ∈ ℕ^V` with `A y ≥ 0` and `‖y‖₁ ≤ (2M) ^ (2 ^ |ι| - 1)`. -/
theorem exists_small_decomposition {ι V : Type*} [Fintype ι] [Fintype V] (M : ℕ) (hM : 1 ≤ M)
    (A : ι → V → ℤ) (hA : ∀ i j, |A i j| ≤ M) (x : V → ℕ)
    (hx : ∀ i, 0 ≤ ∑ j, A i j * (x j : ℤ)) :
    ∃ s : Multiset (V → ℕ), s.sum = x ∧ ∀ y ∈ s, (∀ i, 0 ≤ ∑ j, A i j * (y j : ℤ)) ∧
      ∑ j, y j ≤ (2 * M) ^ (2 ^ Fintype.card ι - 1) := by
  classical
  obtain ⟨s, hs, hsy⟩ := exists_small_decomposition_finset M hM A hA x Finset.univ
    (fun i _ => hx i)
  refine ⟨s, hs, fun y hy => ⟨fun i => (hsy y hy).1 i (Finset.mem_univ i), ?_⟩⟩
  rw [← Finset.card_univ]
  exact (hsy y hy).2

end Cslib
