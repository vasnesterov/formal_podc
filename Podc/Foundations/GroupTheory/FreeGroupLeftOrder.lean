/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Foundations/GroupTheory/FreeGroupLeftOrder.lean
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Order.RelClasses
import Mathlib.Order.Basic
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Ring

/-!
# Free groups are left-orderable

We construct an explicit strict total order on `FreeGroup α` (for a linearly ordered alphabet `α`)
that is invariant under left multiplication. This is Lemma 4 of Göös–Hirvonen–Suomela,
*Linear-in-Δ lower bounds in the LOCAL model* (PODC 2014), proved in their Appendix A.2 via the
Cayley tree of the free group.

## Construction

Letters are elements of `α × Bool` (`(a, true)` is `of a`, `(a, false)` is `(of a)⁻¹`), ordered
lexicographically. For a word `w = l₁ ⋯ lₙ` we define the *score*

  `score w = ∑ᵢ sgn lᵢ + ∑_{i<n} turn lᵢ lᵢ₊₁`,

where `sgn (a, b) = ±1` according to `b`, and `turn l l' = +1` if `inv l < l'` and `-1` otherwise.
Geometrically, the reduced word of `x⁻¹ * y` is the path from `x` to `y` in the Cayley tree; the
`sgn` terms record the direction in which edges are traversed and the `turn` terms record the
relative order of the incoming and outgoing directions at interior vertices. We set

  `Lt x y :↔ 0 < score (x⁻¹ * y).toWord`,

which is manifestly left-invariant. The score of a nonempty word is odd, and inverting a reduced
word negates its score; this gives irreflexivity and trichotomy. Transitivity amounts to the
positive cone being closed under multiplication, which follows from analysing the cancellation
in `toWord x ++ toWord y`.

## Main definitions and results

* `Cslib.FreeGroupOrder.Lt`: the strict order.
* `Cslib.FreeGroupOrder.instIsStrictTotalOrder`: it is a strict total order.
* `Cslib.FreeGroupOrder.lt_mul_left_iff`: it is left-invariant.
* `Cslib.FreeGroupOrder.linearOrder`: the induced linear order (not a global instance), with
  `Cslib.FreeGroupOrder.linearOrder_lt_iff` and `Cslib.FreeGroupOrder.linearOrder_le_mul_left_iff`.
-/

namespace Cslib.FreeGroupOrder

open FreeGroup

variable {α : Type*}

/-! ### Letters and scores of words -/

/-- The inverse of a letter. -/
def inv (l : α × Bool) : α × Bool := (l.1, !l.2)

/-- Inverting a letter is an involution. -/
@[simp] theorem inv_inv (l : α × Bool) : inv (inv l) = l := by simp [inv]

/-- `invRev` in terms of the letter inverse `inv`. -/
theorem invRev_eq (w : List (α × Bool)) : invRev w = (w.map inv).reverse := rfl

/-- The sign of a letter: `+1` for a generator, `-1` for an inverse generator. -/
def sgn (l : α × Bool) : ℤ := if l.2 then 1 else -1

/-- The inverse letter has the opposite sign. -/
theorem sgn_inv (l : α × Bool) : sgn (inv l) = -sgn l := by
  cases l with | mk a b => cases b <;> simp [sgn, inv]

/-- Signs are `±1`. -/
theorem sgn_eq (l : α × Bool) : sgn l = 1 ∨ sgn l = -1 := by
  unfold sgn; split_ifs <;> simp

variable [LinearOrder α]

/-- The turn term at an interior vertex entered by letter `l` and left by letter `l'`. -/
def turn (l l' : α × Bool) : ℤ := if toLex (inv l) < toLex l' then 1 else -1

/-- The turn term between a letter and the first letter of a word (`0` if the word is empty). -/
def jHead (l : α × Bool) : List (α × Bool) → ℤ
  | [] => 0
  | l' :: _ => turn l l'

/-- The score of a word: signs of the letters plus turns between consecutive letters. -/
def score : List (α × Bool) → ℤ
  | [] => 0
  | l :: w => sgn l + jHead l w + score w

/-- The turn term at the junction of two words (`0` if one of them is empty). -/
def jPair (u v : List (α × Bool)) : ℤ :=
  match u.getLast?, v.head? with
  | some a, some b => turn a b
  | _, _ => 0

/-- The empty word has score `0`. -/
@[simp] theorem score_nil : score ([] : List (α × Bool)) = 0 := rfl

/-- No junction term when the left word is empty. -/
@[simp] theorem jPair_nil_left (v : List (α × Bool)) : jPair [] v = 0 := rfl

/-- No junction term when the right word is empty. -/
@[simp] theorem jPair_nil_right (u : List (α × Bool)) : jPair u [] = 0 := by
  unfold jPair; cases u.getLast? <;> rfl

/-- Turn terms are `±1`. -/
theorem turn_eq (l l' : α × Bool) : turn l l' = 1 ∨ turn l l' = -1 := by
  unfold turn; split_ifs <;> simp

/-- The score of a concatenation. -/
theorem score_append (u v : List (α × Bool)) :
    score (u ++ v) = score u + score v + jPair u v := by
  induction u with
  | nil => simp
  | cons l u ih =>
    cases u with
    | nil =>
      cases v with
      | nil => simp [score, jHead]
      | cons r v => simp [score, jHead, jPair]; ring
    | cons m u =>
      have hj : jPair (l :: m :: u) v = jPair (m :: u) v := by
        simp [jPair, List.getLast?_cons_cons]
      show sgn l + jHead l (m :: (u ++ v)) + score (m :: u ++ v)
        = sgn l + jHead l (m :: u) + score (m :: u) + score v + jPair (l :: m :: u) v
      rw [hj, ih]
      simp only [jHead]; ring

/-- The score of a nonempty word is odd. -/
theorem score_cons_odd (l : α × Bool) (w : List (α × Bool)) :
    ∃ k, score (l :: w) = 2 * k + 1 := by
  induction w generalizing l with
  | nil =>
    rcases sgn_eq l with h | h
    · exact ⟨0, by simp [score, jHead, h]⟩
    · exact ⟨-1, by simp [score, jHead, h]⟩
  | cons m w ih =>
    obtain ⟨k, hk⟩ := ih m
    rw [score, jHead, hk]
    rcases sgn_eq l with h | h <;> rcases turn_eq l m with h' | h' <;> rw [h, h']
    · exact ⟨k + 1, by ring⟩
    · exact ⟨k, by ring⟩
    · exact ⟨k, by ring⟩
    · exact ⟨k - 1, by ring⟩

/-- A nonempty word has nonzero score. -/
theorem score_ne_zero {w : List (α × Bool)} (hw : w ≠ []) : score w ≠ 0 := by
  obtain ⟨l, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  obtain ⟨k, hk⟩ := score_cons_odd l w
  omega

/-- Inverting a reduced word negates its score. -/
theorem score_invRev {w : List (α × Bool)} (hw : IsReduced w) : score (invRev w) = -score w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [invRev_cons, score_append]
    cases w with
    | nil => simp [invRev_eq, score, jHead, sgn_inv]
    | cons m w =>
      rw [isReduced_cons_cons] at hw
      rw [ih hw.2]
      have hj : jPair (invRev (m :: w)) (invRev [l]) = turn (inv m) (inv l) := by
        simp [jPair, invRev_eq]
      have hne : toLex m ≠ toLex (inv l) := by
        intro h
        have h' : m = inv l := by simpa using h
        subst h'
        simp [inv] at hw
      rw [hj]
      simp only [score, jHead, invRev_eq, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, sgn_inv, turn, inv_inv]
      rcases lt_or_gt_of_ne hne with h | h
      · simp [h, not_lt.2 h.le]; ring
      · simp [h, not_lt.2 h.le]; ring

/-! ### Cancellation in products of reduced words -/

/-- Two reduced words `u`, `v` decompose as `u = a ++ c`, `v = invRev c ++ b` with `a ++ b`
reduced. -/
theorem exists_cancel (u : List (α × Bool)) :
    ∀ v : List (α × Bool), IsReduced u → IsReduced v →
      ∃ a c b, u = a ++ c ∧ v = invRev c ++ b ∧ IsReduced (a ++ b) := by
  induction u using List.reverseRecOn with
  | nil => intro v _ hv; exact ⟨[], [], v, by simp, by simp [invRev], by simpa using hv⟩
  | append_singleton u l ih =>
    intro v hu hv
    cases v with
    | nil => exact ⟨u ++ [l], [], [], by simp, by simp [invRev], by simpa using hu⟩
    | cons m v =>
      by_cases hm : m = inv l
      · obtain ⟨a, c, b, rfl, rfl, hab⟩ :=
          ih v (hu.infix ⟨[], [l], by simp⟩) (hv.infix ⟨[m], [], by simp⟩)
        refine ⟨a, c ++ [l], b, by simp, ?_, hab⟩
        simp [invRev_eq, hm]
      · refine ⟨u ++ [l], [], m :: v, by simp, by simp [invRev], ?_⟩
        rw [FreeGroup.IsReduced, List.isChain_append]
        refine ⟨hu, hv, ?_⟩
        simp only [List.getLast?_append, List.getLast?_singleton, Option.mem_def,
          Option.some_or, Option.some.injEq, List.head?_cons, forall_eq']
        intro h1
        by_contra h2
        apply hm
        obtain ⟨m1, m2⟩ := m
        obtain ⟨l1, l2⟩ := l
        simp only at h1 h2
        subst h1
        cases m2 <;> cases l2 <;> simp_all [inv]

/-- The reduced word of a product, in terms of the cancellation decomposition. -/
theorem toWord_mul_eq (x y : FreeGroup α) :
    ∃ a c b, x.toWord = a ++ c ∧ y.toWord = invRev c ++ b ∧ (x * y).toWord = a ++ b := by
  obtain ⟨a, c, b, hx, hy, hab⟩ :=
    exists_cancel x.toWord y.toWord isReduced_toWord isReduced_toWord
  refine ⟨a, c, b, hx, hy, ?_⟩
  rw [toWord_mul, ← hab.reduce_eq]
  apply reduce.sound
  rw [hx, hy, ← mul_mk, ← mul_mk, ← mul_mk, ← mul_mk, ← inv_mk]
  rw [mul_assoc, mul_inv_cancel_left]

/-- The key inequality on the three turn terms involved in a product. -/
theorem jPair_key (a c b : List (α × Bool)) :
    -1 ≤ jPair a b - jPair a c - jPair (invRev c) b := by
  rcases List.eq_nil_or_concat a with rfl | ⟨a, p, rfl⟩
  · cases c with
    | nil => simp [invRev]
    | cons q c =>
      cases b with
      | nil => simp
      | cons r b =>
        have hl : (invRev (q :: c)).getLast? = some (inv q) := by simp [invRev_eq]
        simp only [jPair, hl, List.getLast?_nil, List.head?_cons]
        rcases turn_eq (inv q) r with h | h <;> simp [h]
  · have hp : (a.concat p).getLast? = some p := by simp
    cases c with
    | nil =>
      cases b with
      | nil => simp
      | cons r b =>
        simp only [jPair, hp, List.head?_cons, List.head?_nil,
          invRev_eq, List.map_nil, List.reverse_nil, List.getLast?_nil]
        rcases turn_eq p r with h | h <;> simp [h]
    | cons q c =>
      have hl : (invRev (q :: c)).getLast? = some (inv q) := by simp [invRev_eq]
      cases b with
      | nil =>
        simp only [jPair, hp, List.head?_cons, List.head?_nil]
        rcases turn_eq p q with h | h <;> simp [h]
      | cons r b =>
        simp only [jPair, hl, hp, List.head?_cons, turn, inv_inv]
        split_ifs <;> try omega
        rename_i h1 h2 h3
        exact absurd (h2.trans h3) h1

/-- The positive cone `{g | 0 < score g.toWord}` is closed under multiplication. -/
theorem score_mul_pos {x y : FreeGroup α} (hx : 0 < score x.toWord) (hy : 0 < score y.toWord) :
    0 < score (x * y).toWord := by
  obtain ⟨a, c, b, hxw, hyw, hxy⟩ := toWord_mul_eq x y
  have hc : IsReduced c := (isReduced_toWord (x := x)).infix ⟨a, [], by simp [hxw]⟩
  have h1 := score_append a c
  have h2 := score_append (invRev c) b
  have h3 := score_append a b
  rw [score_invRev hc] at h2
  rw [← hxw] at h1
  rw [← hyw] at h2
  rw [← hxy] at h3
  have := jPair_key a c b
  omega

/-! ### The order -/

/-- The left-invariant strict order on `FreeGroup α`: `x < y` iff the reduced word of `x⁻¹ * y`
has positive score. -/
def Lt (x y : FreeGroup α) : Prop := 0 < score (x⁻¹ * y).toWord

/-- The score of the inverse is the negated score. -/
theorem score_toWord_inv (x : FreeGroup α) : score x⁻¹.toWord = -score x.toWord := by
  rw [toWord_inv, score_invRev isReduced_toWord]

/-- `Lt` is a strict total order. -/
instance instIsStrictTotalOrder : IsStrictTotalOrder (FreeGroup α) Lt where
  irrefl x := by simp [Lt]
  trans x y z hxy hyz := by
    have := score_mul_pos hxy hyz
    rwa [← mul_assoc, mul_inv_cancel_right] at this
  trichotomous x y hxy hyx := by
    by_contra hne
    have hw : (x⁻¹ * y).toWord ≠ [] := by
      rw [Ne, toWord_eq_nil_iff, inv_mul_eq_one]; exact hne
    have h0 := score_ne_zero hw
    have hinv := score_toWord_inv (x⁻¹ * y)
    rw [mul_inv_rev, _root_.inv_inv] at hinv
    simp only [Lt] at hxy hyx
    omega

/-- `Lt` is invariant under left multiplication. -/
theorem lt_mul_left_iff (g x y : FreeGroup α) : Lt (g * x) (g * y) ↔ Lt x y := by
  simp [Lt, mul_assoc]

/-- The linear order on `FreeGroup α` induced by `Lt` (not a global instance). -/
@[instance_reducible]
noncomputable def linearOrder : LinearOrder (FreeGroup α) :=
  haveI := Classical.decRel (Lt (α := α))
  linearOrderOfSTO Lt

/-- The strict order of `linearOrder` is `Lt`. -/
theorem linearOrder_lt_iff (x y : FreeGroup α) : linearOrder.lt x y ↔ Lt x y := Iff.rfl

/-- The non-strict order of `linearOrder`. -/
theorem linearOrder_le_iff (x y : FreeGroup α) : linearOrder.le x y ↔ x = y ∨ Lt x y := Iff.rfl

/-- The linear order `linearOrder` is invariant under left multiplication. -/
theorem linearOrder_le_mul_left_iff (g x y : FreeGroup α) :
    linearOrder.le (g * x) (g * y) ↔ linearOrder.le x y := by
  rw [linearOrder_le_iff, linearOrder_le_iff, lt_mul_left_iff, mul_right_inj]

end Cslib.FreeGroupOrder
