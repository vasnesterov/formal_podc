import Mathlib
import Papers.PODC2017.LCLGrids.Orientation

/-!
# A `{0,3,4}`-orientation of every `n × n` torus (counterexample to Theorem 22, third bullet)

Theorem 22 of Brandt et al., *LCL Problems on Grids* (PODC 2017) classifies the
`X`-orientation problems on the 2-dimensional torus (every vertex must have in-degree in
`X ⊆ {0,…,4}`). Its third bullet claims: if `2 ∉ X`, `{1,3,4} ⊄ X` and `{0,1,3} ⊄ X`, then no
solution exists for infinitely many `n`. For `X = {0,3,4}` all three conditions hold, but we
construct a `{0,3,4}`-orientation of the `n × n` torus for **every** `n ≥ 3`.

## Construction

Coordinate `0` is east, coordinate `1` is north. Vertices are grouped into diagonal classes
`cls v = v 1 - v 0 ∈ ZMod n` (the construction is invariant under `v ↦ v + (1,1)`). With the
sequence `t034 : ZMod n → ℕ` (`0, 2, 0, 2, …`, ending with `1` at `n - 1` when `n` is odd):

* the east edge `u — u + e₀` is directed `u → u + e₀` iff `t (cls u - 1) ≤ 1`;
* the north edge `u — u + e₁` is directed `u → u + e₁` iff `1 ≤ t (cls u)`.

The in-degree of a vertex of class `k` is `2 - t k + t (k - 1)`, and consecutive pairs
`(t (k - 1), t k)` are always `(0,2)`, `(2,0)`, `(1,0)` or `(2,1)`, giving in-degree `0, 4, 3, 3`.

The general part (`orientationOfFwd`, `inDeg_orientationOfFwd`) builds an orientation of the
`d`-dimensional torus from any choice of direction `fwd i u` for each edge `u — u + e_i`.
-/

namespace Podc.LCLGrids

open Finset SimpleGraph

section General

variable {d n : ℕ}

lemma nbr_nbr_swap (v : Fin d → ZMod n) (s : Fin d ⊕ Fin d) : nbr (nbr v s) s.swap = v := by
  rcases s with i | i <;> simp [nbr]

lemma torusGraph_adj_nbr [NeZero n] (hn : 3 ≤ n) (v : Fin d → ZMod n) (s : Fin d ⊕ Fin d) :
    (torusGraph d n).Adj v (nbr v s) := by
  rw [← mem_neighborFinset, neighborFinset_torusGraph hn]
  exact mem_image_of_mem _ (mem_univ _)

/-- Direction data for the edge from `u` to `nbr u s`: for `s = inl i` it is the forward edge
`u → u + e_i` (oriented away from `u` iff `fwd i u`); for `s = inr i` it is the edge
`u - e_i → u`, oriented away from `u` iff it is not forward. -/
def fwdDir (fwd : Fin d → (Fin d → ZMod n) → Prop) :
    Fin d ⊕ Fin d → (Fin d → ZMod n) → Prop
  | .inl i, u => fwd i u
  | .inr i, u => ¬ fwd i (u - Pi.single i 1)

lemma fwdDir_swap (fwd : Fin d → (Fin d → ZMod n) → Prop) (u : Fin d → ZMod n)
    (s : Fin d ⊕ Fin d) : fwdDir fwd s.swap (nbr u s) ↔ ¬ fwdDir fwd s u := by
  rcases s with i | i <;> simp [fwdDir, nbr]

/-- The orientation of the torus `(ℤ/n)^d` (`n ≥ 3`) in which the edge `u — u + e_i` is directed
`u → u + e_i` iff `fwd i u`, and `u + e_i → u` otherwise. -/
def orientationOfFwd [NeZero n] (hn : 3 ≤ n) (fwd : Fin d → (Fin d → ZMod n) → Prop) :
    (torusGraph d n).Orientation where
  out u w := ∃ s, w = nbr u s ∧ fwdDir fwd s u
  adj_of_out := by
    rintro u _ ⟨s, rfl, -⟩
    exact torusGraph_adj_nbr hn u s
  out_or_out := by
    intro u w h
    have hw : w ∈ (torusGraph d n).neighborFinset u := (mem_neighborFinset _ _ _).2 h
    rw [neighborFinset_torusGraph hn, mem_image] at hw
    obtain ⟨s, -, rfl⟩ := hw
    by_cases hs : fwdDir fwd s u
    · exact Or.inl ⟨s, rfl, hs⟩
    · exact Or.inr ⟨s.swap, (nbr_nbr_swap u s).symm, (fwdDir_swap fwd u s).2 hs⟩
  not_out_of_out := by
    rintro u _ ⟨s, rfl, hs⟩ ⟨s', hs', hd⟩
    have : s' = s.swap :=
      nbr_injective hn (nbr u s) (hs'.symm.trans (nbr_nbr_swap u s).symm)
    subst this
    exact (fwdDir_swap fwd u s).1 hd hs

open scoped Classical in
/-- In-degree in `orientationOfFwd`: vertex `v` receives the edge `v — v + e_i` iff it is not
forward, and the edge `v - e_i — v` iff it is forward. -/
lemma inDeg_orientationOfFwd [NeZero n] (hn : 3 ≤ n) (fwd : Fin d → (Fin d → ZMod n) → Prop)
    (v : Fin d → ZMod n) :
    inDeg (orientationOfFwd hn fwd) v =
      ∑ i, ((if fwd i v then 0 else 1) + (if fwd i (v - Pi.single i 1) then 1 else 0)) := by
  have hset : {u | (orientationOfFwd hn fwd).out u v} =
      nbr v '' {s | fwdDir fwd s.swap (nbr v s)} := by
    ext u
    simp only [orientationOfFwd, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨s, rfl, hs⟩
      refine ⟨s.swap, ?_, nbr_nbr_swap u s⟩
      rwa [Sum.swap_swap, nbr_nbr_swap]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.swap, (nbr_nbr_swap v s).symm, hs⟩
  rw [inDeg, hset, Set.ncard_image_of_injective _ (nbr_injective hn v),
    Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, card_filter, Fintype.sum_sum_type,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [fwdDir, nbr, Sum.swap_inl, Sum.swap_inr, add_sub_cancel_right]
  congr 1; split_ifs <;> rfl

end General

section Construction

variable {n : ℕ}

/-- The diagonal class `v 1 - v 0` of a vertex of the 2-dimensional torus. -/
def cls (v : Fin 2 → ZMod n) : ZMod n := v 1 - v 0

/-- The sequence `0, 2, 0, 2, …` along the diagonal classes, with a `1` at the last class when
`n` is odd. -/
def t034 (k : ZMod n) : ℕ := if Odd n ∧ k.val + 1 = n then 1 else if Even k.val then 0 else 2

/-- Consecutive values `(t (k - 1), t k)` are `(0,2)`, `(2,0)`, `(1,0)` or `(2,1)`. -/
lemma t034_pair [NeZero n] (hn : 3 ≤ n) (k : ZMod n) :
    (t034 (k - 1) = 0 ∧ t034 k = 2) ∨ (t034 (k - 1) = 2 ∧ t034 k = 0) ∨
      (t034 (k - 1) = 1 ∧ t034 k = 0) ∨ (t034 (k - 1) = 2 ∧ t034 k = 1) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hlt := k.val_lt
  have hval : (k.val = 0 ∧ (k - 1).val = n - 1) ∨ (k.val ≠ 0 ∧ (k - 1).val = k.val - 1) := by
    by_cases h : k.val = 0
    · refine Or.inl ⟨h, ?_⟩
      rw [ZMod.val_eq_zero] at h
      subst h
      rw [zero_sub, ZMod.neg_val, ite_eq_right_iff.2 (fun h => absurd h one_ne_zero),
        ZMod.val_one]
    · exact Or.inr ⟨h, by rw [ZMod.val_sub (by rw [ZMod.val_one]; omega), ZMod.val_one]⟩
  rcases hval with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp only [t034, h1] <;> split_ifs <;>
    simp only [Nat.even_iff, Nat.odd_iff] at * <;> norm_num <;> omega

/-- The direction data of the `{0,3,4}`-orientation (coordinate `0` = east, `1` = north). -/
def fwd034 : Fin 2 → (Fin 2 → ZMod n) → Prop
  | 0, u => t034 (cls u - 1) ≤ 1
  | 1, u => 1 ≤ t034 (cls u)

lemma cls_sub_e0 (v : Fin 2 → ZMod n) : cls (v - Pi.single 0 1) = cls v + 1 := by
  simp [cls]; ring

lemma cls_sub_e1 (v : Fin 2 → ZMod n) : cls (v - Pi.single 1 1) = cls v - 1 := by
  simp [cls]; ring

end Construction

variable {n : ℕ}

/-- For every `n ≥ 3` the `n × n` torus has an orientation in which every in-degree is `0`, `3`
or `4` (an `X`-orientation for `X = {0,3,4}`). -/
theorem exists_orientation034 (hn : 3 ≤ n) :
    ∃ o : (torusGraph 2 n).Orientation, ∀ v, inDeg o v = 0 ∨ inDeg o v = 3 ∨ inDeg o v = 4 := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨orientationOfFwd hn fwd034, fun v => ?_⟩
  rw [inDeg_orientationOfFwd, Fin.sum_univ_two]
  simp only [fwd034, cls_sub_e0, cls_sub_e1, add_sub_cancel_right]
  rcases t034_pair hn (cls v) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp [h1, h2]

/-- **Theorem 22 (third bullet) of [Brandt et al., *LCL Problems on Grids*, PODC 2017] is false.**

The bullet claims that if `2 ∉ X`, `{1,3,4} ⊄ X` and `{0,1,3} ⊄ X`, then the `X`-orientation
problem has no solution on the `n × n` torus for infinitely many `n`. The set `X = {0,3,4}`
satisfies all three conditions (`2 ∉ X`, and `1 ∉ X`, so neither `{1,3,4}` nor `{0,1,3}` is a
subset of it), yet by `exists_orientation034` a `{0,3,4}`-orientation exists for every `n ≥ 3`:
the set of `n` without a solution is contained in `{0, 1, 2}`, hence finite. -/
theorem theorem22_third_bullet_false :
    ¬ {n : ℕ | ¬ ∃ o : (torusGraph 2 n).Orientation,
        ∀ v, inDeg o v = 0 ∨ inDeg o v = 3 ∨ inDeg o v = 4}.Infinite := by
  rw [Set.not_infinite]
  refine (Set.finite_Iio 3).subset fun n hn => ?_
  by_contra h
  exact hn (exists_orientation034 (by simpa using h))

end Podc.LCLGrids
