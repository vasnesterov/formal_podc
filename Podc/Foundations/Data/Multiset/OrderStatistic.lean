/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Foundations/Data/Multiset/OrderStatistic.lean
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.Filter
import Mathlib.Order.Basic

/-!
# Order statistics of a multiset

`Multiset.orderStat s i` is the `i`-th smallest element of a multiset `s` over a linear order
(0-indexed: `orderStat s 0` is the minimum, `orderStat s (card s - 1)` the maximum), i.e. the `i`-th
entry of `s` sorted in ascending order. Out of range it is `default`.

Order statistics are the basic tool for trimming algorithms (approximate agreement: "sort the
received values, discard the `t` lowest and the `t` highest"). Everything is reduced to counting:

## Main statements

* `Multiset.orderStat_le_iff`: `orderStat s i ≤ y ↔ i < #{z ∈ s | z ≤ y}`;
  `Multiset.orderStat_lt_iff`: `orderStat s i < y ↔ i < #{z ∈ s | z < y}`;
  `Multiset.le_orderStat_iff`: `y ≤ orderStat s i ↔ #{z ∈ s | z < y} ≤ i`.
* `Multiset.orderStat_mono`, `Multiset.orderStat_mem`.
* Removing elements: if `t ≤ s` then `orderStat s i ≤ orderStat t i ≤ orderStat s (i + (#s - #t))`
  (`Multiset.orderStat_le_orderStat_of_le`, `Multiset.orderStat_le_orderStat_add_of_le`); in
  particular inserting one element `a` shifts every order statistic by at most one position
  (`Multiset.orderStat_cons_le`, `Multiset.orderStat_le_orderStat_cons_succ`).
-/

namespace Multiset

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-- The `i`-th smallest element of `s` (0-indexed), `default` if `i ≥ card s`. -/
def orderStat (s : Multiset α) (i : ℕ) : α := (s.sort (· ≤ ·)).getD i default

variable {s t : Multiset α} {i j : ℕ} {y : α}

theorem orderStat_eq (hi : i < card s) :
    orderStat s i = (s.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi) := by
  have hl : i < (s.sort (· ≤ ·)).length := by simpa [length_sort] using hi
  simp [orderStat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

theorem orderStat_mem (hi : i < card s) : orderStat s i ∈ s := by
  rw [orderStat_eq hi, ← mem_sort (r := (· ≤ ·))]
  exact List.getElem_mem _

theorem orderStat_mono (hij : i ≤ j) (hj : j < card s) : orderStat s i ≤ orderStat s j := by
  rw [orderStat_eq (hij.trans_lt hj), orderStat_eq hj]
  rcases hij.lt_or_eq with h | rfl
  · exact List.pairwise_iff_getElem.mp (pairwise_sort s (· ≤ ·)) i j _ _ h
  · exact le_rfl

omit [Inhabited α] in
/-- Counting in a sorted list: for a downward closed predicate `p`, the `i`-th entry satisfies `p`
iff more than `i` entries satisfy `p`. -/
theorem _root_.List.Pairwise.getElem_iff_lt_countP {l : List α} (hl : l.Pairwise (· ≤ ·))
    {p : α → Bool} (hp : ∀ a b, a ≤ b → p b → p a) (hi : i < l.length) :
    p l[i] ↔ i < l.countP p := by
  have hmono : ∀ a b (ha : a < l.length) (hb : b < l.length), a ≤ b → l[a] ≤ l[b] := by
    intro a b ha hb hab
    rcases hab.lt_or_eq with h | rfl
    · exact List.pairwise_iff_getElem.mp hl a b ha hb h
    · exact le_rfl
  constructor
  · intro h
    rw [← List.take_append_drop (i + 1) l, List.countP_append]
    have : (l.take (i + 1)).countP p = i + 1 := by
      rw [List.countP_eq_length.mpr, List.length_take]
      · omega
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      rw [List.getElem_take]
      simp only [List.length_take] at hk
      exact hp _ _ (hmono k i _ hi (by omega)) h
    omega
  · intro h
    by_contra hn
    rw [← List.take_append_drop i l, List.countP_append] at h
    have h1 : (l.take i).countP p ≤ i := List.countP_le_length.trans (by simp)
    have h2 : (l.drop i).countP p = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      rw [List.getElem_drop]
      simp only [List.length_drop] at hk
      intro hpa
      exact hn (hp _ _ (hmono i (i + k) hi (by omega) (by omega)) hpa)
    omega

omit [Inhabited α] in
theorem card_filter_eq_countP (p : α → Prop) [DecidablePred p] :
    card (s.filter p) = (s.sort (· ≤ ·)).countP (fun x => decide (p x)) := by
  conv_lhs => rw [← sort_eq s (· ≤ ·)]
  rw [filter_coe, coe_card, List.countP_eq_length_filter]

/-- `orderStat s i ≤ y` iff more than `i` elements of `s` are `≤ y`. -/
theorem orderStat_le_iff (hi : i < card s) : orderStat s i ≤ y ↔ i < card (s.filter (· ≤ y)) := by
  rw [card_filter_eq_countP, orderStat_eq hi]
  have := (pairwise_sort s (· ≤ ·)).getElem_iff_lt_countP (p := fun x => decide (x ≤ y))
    (fun a b hab hb => by simpa using hab.trans (by simpa using hb)) (i := i)
    (by simpa [length_sort] using hi)
  simpa using this

/-- `orderStat s i < y` iff more than `i` elements of `s` are `< y`. -/
theorem orderStat_lt_iff (hi : i < card s) : orderStat s i < y ↔ i < card (s.filter (· < y)) := by
  rw [card_filter_eq_countP, orderStat_eq hi]
  have := (pairwise_sort s (· ≤ ·)).getElem_iff_lt_countP (p := fun x => decide (x < y))
    (fun a b hab hb => by simpa using hab.trans_lt (by simpa using hb)) (i := i)
    (by simpa [length_sort] using hi)
  simpa using this

/-- `y ≤ orderStat s i` iff at most `i` elements of `s` are `< y`. -/
theorem le_orderStat_iff (hi : i < card s) : y ≤ orderStat s i ↔ card (s.filter (· < y)) ≤ i := by
  rw [← not_lt, orderStat_lt_iff hi, not_lt]

/-- At most `i` elements lie strictly below the `i`-th smallest one. -/
theorem card_filter_lt_orderStat_le (hi : i < card s) :
    card (s.filter (· < orderStat s i)) ≤ i :=
  (le_orderStat_iff hi).1 le_rfl

/-- At least `i + 1` elements are at most the `i`-th smallest one. -/
theorem lt_card_filter_le_orderStat (hi : i < card s) :
    i < card (s.filter (· ≤ orderStat s i)) :=
  (orderStat_le_iff hi).1 le_rfl

/-- Removing elements can only increase an order statistic: `t ≤ s → orderStat s i ≤ orderStat t i`. -/
theorem orderStat_le_orderStat_of_le (hts : t ≤ s) (hi : i < card t) :
    orderStat s i ≤ orderStat t i := by
  refine (orderStat_le_iff (hi.trans_le (card_le_card hts))).2 ?_
  exact (lt_card_filter_le_orderStat hi).trans_le (card_le_card (filter_le_filter _ hts))

/-- Removing `#s - #t` elements shifts an order statistic by at most `#s - #t` positions:
`t ≤ s → orderStat t i ≤ orderStat s (i + (#s - #t))`. -/
theorem orderStat_le_orderStat_add_of_le (hts : t ≤ s) (hi : i < card t) :
    orderStat t i ≤ orderStat s (i + (card s - card t)) := by
  have hc := card_le_card hts
  refine (le_orderStat_iff (by omega)).2 ?_
  obtain ⟨u, rfl⟩ := le_iff_exists_add.mp hts
  rw [filter_add, card_add, card_add]
  have h1 := card_filter_lt_orderStat_le hi
  have h2 : card (u.filter (· < orderStat t i)) ≤ card u := card_le_card (filter_le _ _)
  omega

/-- Inserting an element can only decrease an order statistic. -/
theorem orderStat_cons_le (a : α) (hi : i < card s) : orderStat (a ::ₘ s) i ≤ orderStat s i :=
  orderStat_le_orderStat_of_le (le_cons_self s a) hi

/-- Inserting an element shifts an order statistic by at most one position. -/
theorem orderStat_le_orderStat_cons_succ (a : α) (hi : i < card s) :
    orderStat s i ≤ orderStat (a ::ₘ s) (i + 1) := by
  have := orderStat_le_orderStat_add_of_le (le_cons_self s a) hi
  simpa using this

end Multiset
