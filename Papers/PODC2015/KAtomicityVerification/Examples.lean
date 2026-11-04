import Papers.PODC2015.KAtomicityVerification.Characterization

/-!
# The example history of Figure 3.1

The history of Fig. 3.1 of [Golab–Li–López-Ortiz–Nishimura] with times read off the figure
(events numbered `1, …, 18` from left to right):

| op   | `s` | `f` |   | op   | `s` | `f` |
|------|-----|-----|---|------|-----|-----|
| w(1) | 4   | 6   |   | r(1) | 8   | 11  |
| w(2) | 2   | 3   |   | r(2) | 12  | 16  |
| w(3) | 5   | 9   |   | r(3) | 13  | 17  |
| w(4) | 7   | 14  |   | r(4) | 15  | 18  |
| w(5) | 1   | 10  |   |      |     |     |

We check that these times produce exactly the graphs `G_R` and `G_W` drawn in Fig. 3.1, and prove
the paper's claims about this example (Section 3, after Lemma 3.8, and Table 5.1 in Section 5.2):

* `fig31_kAtomic_three`, `fig31_not_kAtomic_two`, `fig31_not_kAtomic_one`: `H` is 3-atomic but
  neither 2- nor 1-atomic;
* `fig31_valueOrders_three`: the 3-atomic value orders (in the sense of Lemma 3.8) are exactly
  `⟨5,2,1,3,4⟩` and `⟨5,2,3,1,4⟩`;
* `fig31'_topoOrders`, `fig31'_table51`: Table 5.1 for the history without `w(5)`.

All finite checks are by `decide` after reducing the conditions to quantifiers over `Fin` and
over permutations (`List.permutations'`) of a fixed list of values.
-/

namespace Podc.KAtomicityVerification

namespace History

variable {V R : Type*} (H : History V R)

instance decRelHbEx : DecidableRel H.hb := fun a b => Nat.decLt (H.f a) (H.s b)

instance decRelEWEx : DecidableRel H.EW := fun a b => inferInstanceAs (Decidable (H.hb (.inl a) (.inl b)))

instance decRelERex [DecidableEq V] [Fintype R] : DecidableRel H.ER :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ ∃ r : R, H.val r = b ∧ H.hb (.inl a) (.inr r)))

lemma isKAtomicValueOrder_iff (k : ℕ) (T : List V) :
    H.IsKAtomicValueOrder k T ↔ T.Nodup ∧ (∀ v, v ∈ T) ∧
      (∀ i j : Fin T.length, H.EW T[i] T[j] → i < j) ∧
      (∀ i j : Fin T.length, H.ER T[i] T[j] → (i : ℕ) < j + k) :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, fun i j => h3 i j i.2 j.2, fun i j => h4 i j i.2 j.2⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, fun i j hi hj => h3 ⟨i, hi⟩ ⟨j, hj⟩,
      fun i j hi hj => h4 ⟨i, hi⟩ ⟨j, hj⟩⟩⟩

lemma isTopoOrder_iff (T : List V) :
    H.IsTopoOrder T ↔ T.Nodup ∧ (∀ v, v ∈ T) ∧ (∀ i j : Fin T.length, H.EW T[i] T[j] → i < j) :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun i j => h3 i j i.2 j.2⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun i j hi hj => h3 ⟨i, hi⟩ ⟨j, hj⟩⟩⟩

instance decIsKAtomicValueOrder [DecidableEq V] [Fintype V] [Fintype R] (k : ℕ) (T : List V) :
    Decidable (H.IsKAtomicValueOrder k T) :=
  decidable_of_iff' _ (H.isKAtomicValueOrder_iff k T)

instance decIsTopoOrder [DecidableEq V] [Fintype V] (T : List V) :
    Decidable (H.IsTopoOrder T) :=
  decidable_of_iff' _ (H.isTopoOrder_iff T)

/-- A list listing every value exactly once is a permutation of any fixed such list `L`, so it
occurs in `L.permutations'`; this reduces statements about all value orders to finite checks. -/
lemma mem_permutations'_of_complete {L T : List V} (hL : L.Nodup) (hLc : ∀ v, v ∈ L)
    (hT : T.Nodup) (hTc : ∀ v, v ∈ T) : T ∈ L.permutations' :=
  List.mem_permutations'.2 ((List.perm_ext_iff_of_nodup hT hL).2 fun v => by simp [hLc, hTc])

end History

/-! ### The history -/

/-- The values `1, …, 5` written in Fig. 3.1. -/
inductive Val | v1 | v2 | v3 | v4 | v5
  deriving DecidableEq, Repr

/-- The values `1, …, 4` (Fig. 3.1 with `w(5)` removed). -/
inductive Val4 | v1 | v2 | v3 | v4
  deriving DecidableEq, Repr

/-- The reads `r(1), …, r(4)` of Fig. 3.1. -/
inductive Rd | r1 | r2 | r3 | r4
  deriving DecidableEq, Repr

instance : Fintype Val :=
  ⟨⟨[Val.v1, .v2, .v3, .v4, .v5], by decide⟩, fun x => by cases x <;> decide⟩

instance : Fintype Val4 := ⟨⟨[Val4.v1, .v2, .v3, .v4], by decide⟩, fun x => by cases x <;> decide⟩

instance : Fintype Rd := ⟨⟨[Rd.r1, .r2, .r3, .r4], by decide⟩, fun x => by cases x <;> decide⟩

open Val Rd

/-- Start times of the operations of Fig. 3.1. -/
def fig31S : Val ⊕ Rd → ℕ
  | .inl v1 => 4 | .inl v2 => 2 | .inl v3 => 5 | .inl v4 => 7 | .inl v5 => 1
  | .inr r1 => 8 | .inr r2 => 12 | .inr r3 => 13 | .inr r4 => 15

/-- Finish times of the operations of Fig. 3.1. -/
def fig31F : Val ⊕ Rd → ℕ
  | .inl v1 => 6 | .inl v2 => 3 | .inl v3 => 9 | .inl v4 => 14 | .inl v5 => 10
  | .inr r1 => 11 | .inr r2 => 16 | .inr r3 => 17 | .inr r4 => 18

/-- The value returned by each read: `r(i)` reads `i`. -/
def fig31Val : Rd → Val
  | r1 => v1 | r2 => v2 | r3 => v3 | r4 => v4

/-- The example history `H` of Fig. 3.1. -/
def fig31 : History Val Rd where
  val := fig31Val
  s := fig31S
  f := fig31F
  s_lt_f := by decide

/-- The history of Fig. 3.1 with `w(5)` removed (same times for the other operations). -/
def fig31' : History Val4 Rd where
  val
    | r1 => .v1 | r2 => .v2 | r3 => .v3 | r4 => .v4
  s
    | .inl .v1 => 4 | .inl .v2 => 2 | .inl .v3 => 5 | .inl .v4 => 7
    | .inr r1 => 8 | .inr r2 => 12 | .inr r3 => 13 | .inr r4 => 15
  f
    | .inl .v1 => 6 | .inl .v2 => 3 | .inl .v3 => 9 | .inl .v4 => 14
    | .inr r1 => 11 | .inr r2 => 16 | .inr r3 => 17 | .inr r4 => 18
  s_lt_f := by decide

/-! ### Sanity checks: the graphs of Fig. 3.1 and the assumptions -/

/-- The read value graph `G_R` of Fig. 3.1: edges `1 ↔ 2`, `1 → 3`, `1 → 4`, `2 → 3`, `3 → 2`,
`2 → 4`, `3 → 4`, `5 → 2`, `5 → 3`, `5 → 4`. -/
theorem fig31_ER (a b : Val) :
    fig31.ER a b ↔ (a, b) ∈ [(v1, v2), (v2, v1), (v1, v3), (v1, v4), (v2, v3), (v3, v2),
      (v2, v4), (v3, v4), (v5, v2), (v5, v3), (v5, v4)] := by
  revert a b; decide

/-- The write graph `G_W` of Fig. 3.1: edges `2 → 1`, `2 → 3`, `2 → 4`, `1 → 4`. -/
theorem fig31_EW (a b : Val) :
    fig31.EW a b ↔ (a, b) ∈ [(v2, v1), (v2, v3), (v2, v4), (v1, v4)] := by
  revert a b; decide

theorem fig31_distinctTimes : fig31.DistinctTimes := by
  unfold History.DistinctTimes; decide

theorem fig31_assumption34 : fig31.Assumption34 := by
  unfold History.Assumption34; decide

/-- The full history violates Assumption 4.1: `w(5)` has no dictated read. -/
theorem fig31_not_assumption41 : ¬ fig31.Assumption41 := by
  unfold History.Assumption41 History.hb; decide

theorem fig31'_distinctTimes : fig31'.DistinctTimes := by
  unfold History.DistinctTimes; decide

theorem fig31'_assumption34 : fig31'.Assumption34 := by
  unfold History.Assumption34; decide

/-- Without `w(5)`, Assumption 4.1 holds. -/
theorem fig31'_assumption41 : fig31'.Assumption41 := by
  unfold History.Assumption41 History.hb; decide

/-! ### The claims of Section 3 -/

/-- Every value order of `H` lies among the permutations of `⟨1,2,3,4,5⟩`. -/
lemma fig31_mem_perms {k : ℕ} {T : List Val} (hT : fig31.IsKAtomicValueOrder k T) :
    T ∈ [v1, v2, v3, v4, v5].permutations' :=
  History.mem_permutations'_of_complete (by decide) (by decide) hT.nodup hT.complete

/-- The 3-atomic value orders of `H` (in the sense of Lemma 3.8) are exactly
`T₁ = ⟨5,2,1,3,4⟩` and `T₂ = ⟨5,2,3,1,4⟩` (Section 3, after Fig. 3.1). -/
theorem fig31_valueOrders_three (T : List Val) :
    fig31.IsKAtomicValueOrder 3 T ↔ T = [v5, v2, v1, v3, v4] ∨ T = [v5, v2, v3, v1, v4] := by
  constructor
  · intro hT
    have hmem := fig31_mem_perms hT
    revert hT
    revert T
    decide +kernel
  · rintro (rfl | rfl) <;> decide

/-- No value order of `H` is 2-atomic. -/
lemma fig31_no_valueOrder_two (T : List Val) : ¬ fig31.IsKAtomicValueOrder 2 T := by
  intro hT
  have hmem := fig31_mem_perms hT
  revert hT
  revert T
  decide +kernel

/-- `H` is 3-atomic (Section 3, after Fig. 3.1). -/
theorem fig31_kAtomic_three : fig31.KAtomic 3 :=
  (History.kAtomic_iff_exists_valueOrder fig31_assumption34 (by norm_num)).2
    ⟨_, ((fig31_valueOrders_three _).2 (Or.inl rfl))⟩

/-- `H` is not 2-atomic: `w(1)` and `w(3)` both separate `w(2)` from `r(2)`. -/
theorem fig31_not_kAtomic_two : ¬ fig31.KAtomic 2 := by
  rw [History.kAtomic_iff_exists_valueOrder fig31_assumption34 (by norm_num)]
  exact fun ⟨T, hT⟩ => fig31_no_valueOrder_two T hT

/-- `H` is not 1-atomic. -/
theorem fig31_not_kAtomic_one : ¬ fig31.KAtomic 1 := by
  rw [History.kAtomic_iff_exists_valueOrder fig31_assumption34 (by norm_num)]
  rintro ⟨T, hT⟩
  have hmem := fig31_mem_perms hT
  revert hT
  revert T
  decide +kernel

/-! ### Table 5.1: the history without `w(5)` -/

lemma fig31'_mem_perms {T : List Val4} (hT : T.Nodup) (hTc : ∀ v, v ∈ T) :
    T ∈ [Val4.v1, .v2, .v3, .v4].permutations' :=
  History.mem_permutations'_of_complete (by decide) (by decide) hT hTc

/-- Table 5.1: the topological orderings of `G_W` for the history without `w(5)` are exactly
`⟨2,1,3,4⟩`, `⟨2,1,4,3⟩` and `⟨2,3,1,4⟩`. -/
theorem fig31'_topoOrders (T : List Val4) :
    fig31'.IsTopoOrder T ↔
      T = [.v2, .v1, .v3, .v4] ∨ T = [.v2, .v1, .v4, .v3] ∨ T = [.v2, .v3, .v1, .v4] := by
  constructor
  · intro hT
    have hmem := fig31'_mem_perms hT.nodup hT.complete
    revert hT
    revert T
    decide +kernel
  · rintro (rfl | rfl | rfl) <;> decide

/-- Table 5.1, columns "is 2-atomic" and "is 3-atomic": none of the three topological orderings
is a 2-atomic value order; `⟨2,1,3,4⟩` and `⟨2,3,1,4⟩` are 3-atomic value orders, `⟨2,1,4,3⟩`
is not. The reasons given in the table are the `G_R` edges `(3, 2)` (`w(3) <_H r(2)`) and
`(1, 2)` (`w(1) <_H r(2)`). -/
theorem fig31'_table51 :
    (∀ T, ¬ fig31'.IsKAtomicValueOrder 2 T) ∧
    fig31'.IsKAtomicValueOrder 3 [.v2, .v1, .v3, .v4] ∧
    ¬ fig31'.IsKAtomicValueOrder 3 [.v2, .v1, .v4, .v3] ∧
    fig31'.IsKAtomicValueOrder 3 [.v2, .v3, .v1, .v4] ∧
    fig31'.hb (.inl .v3) (.inr r2) ∧ fig31'.hb (.inl .v1) (.inr r2) := by
  refine ⟨fun T hT => ?_, by decide, by decide, by decide, by decide, by decide⟩
  have hmem := fig31'_mem_perms hT.nodup hT.complete
  revert hT
  revert T
  decide +kernel

/-- Without `w(5)` the history is still 3-atomic but not 2-atomic (Sections 4.2 and 5.2). -/
theorem fig31'_kAtomic_three_not_two : fig31'.KAtomic 3 ∧ ¬ fig31'.KAtomic 2 := by
  rw [History.kAtomic_iff_exists_valueOrder fig31'_assumption34 (by norm_num),
    History.kAtomic_iff_exists_valueOrder fig31'_assumption34 (by norm_num)]
  exact ⟨⟨_, fig31'_table51.2.1⟩, fun ⟨T, hT⟩ => fig31'_table51.1 T hT⟩

end Podc.KAtomicityVerification
