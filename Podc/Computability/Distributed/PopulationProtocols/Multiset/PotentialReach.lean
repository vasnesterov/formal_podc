/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/PopulationProtocols/Multiset/PotentialReach.lean
import Podc.Computability.Distributed.PopulationProtocols.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Flow equations, traps, siphons and potential reachability

Over-approximations of reachability in multiset population protocols (equivalently, in Petri nets
with transitions of size two), as in Blondin, Esparza, Jaax, Meyer, *Towards efficient
verification of population protocols*, PODC 2017, §4.2.

## Main definitions

* `FiresSeq w C C'`: the sequence of transitions `w` fires from `C` and leads to `C'`.
* `FlowEq C C' x`: the *flow equations* `C'(q) = C(q) + ∑ₜ x(t) · (post(t)(q) − pre(t)(q))`.
* `Transition.Into R` (`t ∈ •R`), `Transition.OutOf R` (`t ∈ R•`), `mass C R` (`C(R)`).
* `IsUTrap U R` (`R• ∩ U ⊆ •R`) and `IsUSiphon U R` (`•R ∩ U ⊆ R•`).
* `PotReachVia T C C' x` (`C ⇢ˣ C'`): flow equations, trap and siphon constraints for
  `U = ⟦x⟧ ⊆ T`; `PotReach T C C'`.

## Main statements

* `MReach.exists_firesSeq`: reachability is witnessed by a firing sequence.
* `FiresSeq.flowEq`: firing sequences satisfy the flow equations with their Parikh vector.
* `FiresSeq.trap`, `FiresSeq.siphon`: Observation 11 (trap and siphon constraints).
* `MReach.potReach`: reachability implies potential reachability.
-/

namespace Cslib.PopulationProtocol

open Finset

variable {Q : Type*} [DecidableEq Q]

namespace Transition

/-- The effect `post(t)(q) − pre(t)(q)` of `t` on state `q`. -/
def delta (t : Transition Q) (q : Q) : ℤ := (t.post.count q : ℤ) - t.pre.count q

/-- `t ∈ •R`: the transition moves an agent into `R`. -/
def Into (t : Transition Q) (R : Finset Q) : Prop := ∃ q ∈ t.post, q ∈ R

/-- `t ∈ R•`: the transition takes an agent from `R`. -/
def OutOf (t : Transition Q) (R : Finset Q) : Prop := ∃ q ∈ t.pre, q ∈ R

theorem Fires.count_eq {t : Transition Q} {C C' : Multiset Q} (h : t.Fires C C') (q : Q) :
    (C'.count q : ℤ) = C.count q + t.delta q := by
  have hle := Multiset.count_le_of_le q h.1
  rw [h.2, Multiset.count_add, Multiset.count_sub, delta]
  push_cast [hle]
  ring

end Transition

/-- The number `C(R)` of agents of `C` in states of `R`. -/
def mass (C : Multiset Q) (R : Finset Q) : ℕ := Multiset.card (C.filter (· ∈ R))

theorem mass_add (C D : Multiset Q) (R : Finset Q) : mass (C + D) R = mass C R + mass D R := by
  simp [mass, Multiset.filter_add]

theorem mass_pos_iff {C : Multiset Q} {R : Finset Q} : 0 < mass C R ↔ ∃ q ∈ C, q ∈ R := by
  simp [mass, Multiset.card_pos, Multiset.eq_zero_iff_forall_notMem]

theorem mass_mono {C D : Multiset Q} (h : C ≤ D) (R : Finset Q) : mass C R ≤ mass D R :=
  Multiset.card_le_card (Multiset.filter_le_filter _ h)

namespace Transition

variable {t : Transition Q} {C C' : Multiset Q} {R : Finset Q}

theorem Fires.mass_eq (h : t.Fires C C') :
    mass C' R + mass t.pre R = mass C R + mass t.post R := by
  have hC : C = C - t.pre + t.pre := (tsub_add_cancel_of_le h.1).symm
  conv_rhs => rw [hC]
  rw [h.2, mass_add, mass_add]
  omega

theorem into_iff : t.Into R ↔ 0 < mass t.post R := by rw [mass_pos_iff]; rfl

theorem outOf_iff : t.OutOf R ↔ 0 < mass t.pre R := by rw [mass_pos_iff]; rfl

/-- After a transition moving an agent into `R`, `R` is populated. -/
theorem Fires.mass_pos_of_into (h : t.Fires C C') (hi : t.Into R) : 0 < mass C' R := by
  have := h.mass_eq (R := R)
  have := into_iff.1 hi
  have : mass t.pre R ≤ mass C R := mass_mono h.1 R
  omega

/-- Before a transition taking an agent from `R`, `R` is populated. -/
theorem Fires.mass_pos_of_outOf (h : t.Fires C C') (ho : t.OutOf R) : 0 < mass C R :=
  lt_of_lt_of_le (outOf_iff.1 ho) (mass_mono h.1 R)

end Transition

/-- The firing sequence `w` leads from `C` to `C'`. -/
def FiresSeq : List (Transition Q) → Multiset Q → Multiset Q → Prop
  | [], C, C' => C' = C
  | t :: w, C, C' => ∃ C₁, t.Fires C C₁ ∧ FiresSeq w C₁ C'

@[simp] theorem firesSeq_nil {C C' : Multiset Q} : FiresSeq [] C C' ↔ C' = C := Iff.rfl

@[simp] theorem firesSeq_cons {t : Transition Q} {w : List (Transition Q)} {C C' : Multiset Q} :
    FiresSeq (t :: w) C C' ↔ ∃ C₁, t.Fires C C₁ ∧ FiresSeq w C₁ C' := Iff.rfl

theorem FiresSeq.append {w v : List (Transition Q)} {C D E : Multiset Q} (h₁ : FiresSeq w C D)
    (h₂ : FiresSeq v D E) : FiresSeq (w ++ v) C E := by
  induction w generalizing C with
  | nil => simp only [firesSeq_nil] at h₁; subst h₁; exact h₂
  | cons t w ih =>
    obtain ⟨C₁, h, hw⟩ := h₁
    exact ⟨C₁, h, ih hw⟩

theorem FiresSeq.mreach {T : Set (Transition Q)} {w : List (Transition Q)} {C C' : Multiset Q}
    (h : FiresSeq w C C') (hw : ∀ t ∈ w, t ∈ T) : MReach T C C' := by
  induction w generalizing C with
  | nil => simp only [firesSeq_nil] at h; subst h; exact .refl
  | cons t w ih =>
    obtain ⟨C₁, h, hrest⟩ := h
    exact Relation.ReflTransGen.head ⟨t, hw t (by simp), h⟩
      (ih hrest fun s hs => hw s (by simp [hs]))

/-- Reachability is witnessed by a firing sequence. -/
theorem MReach.exists_firesSeq {T : Set (Transition Q)} {C C' : Multiset Q}
    (h : MReach T C C') : ∃ w, (∀ t ∈ w, t ∈ T) ∧ FiresSeq w C C' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by simp, rfl⟩
  | head hs _ ih =>
    obtain ⟨t, ht, hf⟩ := hs
    obtain ⟨w, hw, hfw⟩ := ih
    refine ⟨t :: w, fun s hs => ?_, _, hf, hfw⟩
    rcases List.mem_cons.1 hs with rfl | hs
    exacts [ht, hw s hs]

variable [Fintype Q]

/-- The flow equations for `(C, C', x)`. -/
def FlowEq (C C' : Multiset Q) (x : Transition Q → ℕ) : Prop :=
  ∀ q, (C'.count q : ℤ) = C.count q + ∑ t, (x t : ℤ) * t.delta q

/-- **Flow equations.** A firing sequence satisfies the flow equations with its Parikh vector. -/
theorem FiresSeq.flowEq {w : List (Transition Q)} {C C' : Multiset Q} (h : FiresSeq w C C') :
    FlowEq C C' (fun t => w.count t) := by
  induction w generalizing C with
  | nil => simp only [firesSeq_nil] at h; subst h; intro q; simp
  | cons t w ih =>
    obtain ⟨C₁, h₁, hw⟩ := h
    intro q
    rw [ih hw q, h₁.count_eq q]
    simp only [List.count_cons, beq_iff_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq,
      mem_univ, ite_true]
    ring

/-- `R` is a `U`-trap: `R• ∩ U ⊆ •R`. -/
def IsUTrap (U : Set (Transition Q)) (R : Finset Q) : Prop := ∀ t ∈ U, t.OutOf R → t.Into R

/-- `R` is a `U`-siphon: `•R ∩ U ⊆ R•`. -/
def IsUSiphon (U : Set (Transition Q)) (R : Finset Q) : Prop := ∀ t ∈ U, t.Into R → t.OutOf R

omit [Fintype Q] in
/-- A populated trap stays populated. -/
theorem FiresSeq.mass_pos_of_trap {U : Set (Transition Q)} {R : Finset Q}
    {w : List (Transition Q)} {C C' : Multiset Q} (h : FiresSeq w C C') (hwU : ∀ t ∈ w, t ∈ U)
    (hR : IsUTrap U R) (hC : 0 < mass C R) : 0 < mass C' R := by
  induction w generalizing C with
  | nil => simp only [firesSeq_nil] at h; subst h; exact hC
  | cons t w ih =>
    obtain ⟨C₁, h₁, hw⟩ := h
    refine ih hw (fun s hs => hwU s (by simp [hs])) ?_
    by_cases ho : t.OutOf R
    · exact h₁.mass_pos_of_into (hR t (hwU t (by simp)) ho)
    · have := h₁.mass_eq (R := R)
      have : mass t.pre R = 0 := by
        by_contra hne; exact ho (Transition.outOf_iff.2 (Nat.pos_of_ne_zero hne))
      omega

omit [Fintype Q] in
/-- **Observation 11 (traps).** If some transition of a `U`-firing sequence moves an agent into
a `U`-trap `R`, then `R` is populated at the end. -/
theorem FiresSeq.trap {U : Set (Transition Q)} {R : Finset Q}
    {w : List (Transition Q)} {C C' : Multiset Q} (h : FiresSeq w C C') (hwU : ∀ t ∈ w, t ∈ U)
    (hR : IsUTrap U R) {t : Transition Q} (ht : t ∈ w) (hi : t.Into R) : 0 < mass C' R := by
  induction w generalizing C with
  | nil => simp at ht
  | cons s w ih =>
    obtain ⟨C₁, h₁, hw⟩ := h
    have hwU' : ∀ t ∈ w, t ∈ U := fun s hs => hwU s (by simp [hs])
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hw.mass_pos_of_trap hwU' hR (h₁.mass_pos_of_into hi)
    · exact ih hw hwU' ht

omit [Fintype Q] in
/-- A siphon populated at the end was populated at the start. -/
theorem FiresSeq.mass_pos_of_siphon {U : Set (Transition Q)} {R : Finset Q}
    {w : List (Transition Q)} {C C' : Multiset Q} (h : FiresSeq w C C') (hwU : ∀ t ∈ w, t ∈ U)
    (hR : IsUSiphon U R) (hC' : 0 < mass C' R) : 0 < mass C R := by
  induction w generalizing C with
  | nil => simp only [firesSeq_nil] at h; subst h; exact hC'
  | cons t w ih =>
    obtain ⟨C₁, h₁, hw⟩ := h
    have h1 := ih hw (fun s hs => hwU s (by simp [hs]))
    by_cases hi : t.Into R
    · exact h₁.mass_pos_of_outOf (hR t (hwU t (by simp)) hi)
    · have := h₁.mass_eq (R := R)
      have : mass t.post R = 0 := by
        by_contra hne; exact hi (Transition.into_iff.2 (Nat.pos_of_ne_zero hne))
      omega

omit [Fintype Q] in
/-- **Observation 11 (siphons).** If some transition of a `U`-firing sequence takes an agent from
a `U`-siphon `R`, then `R` is populated at the start. -/
theorem FiresSeq.siphon {U : Set (Transition Q)} {R : Finset Q}
    {w : List (Transition Q)} {C C' : Multiset Q} (h : FiresSeq w C C') (hwU : ∀ t ∈ w, t ∈ U)
    (hR : IsUSiphon U R) {t : Transition Q} (ht : t ∈ w) (ho : t.OutOf R) : 0 < mass C R := by
  induction w generalizing C with
  | nil => simp at ht
  | cons s w ih =>
    obtain ⟨C₁, h₁, hw⟩ := h
    have hwU' : ∀ t ∈ w, t ∈ U := fun s hs => hwU s (by simp [hs])
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h₁.mass_pos_of_outOf ho
    · have := h₁.mass_eq (R := R)
      have h1 := ih hw hwU' ht
      by_cases hi : s.Into R
      · exact h₁.mass_pos_of_outOf (hR s (hwU s (by simp)) hi)
      · have : mass s.post R = 0 := by
          by_contra hne; exact hi (Transition.into_iff.2 (Nat.pos_of_ne_zero hne))
        omega

/-- **Potential reachability** `C ⇢ˣ C'` (Definition 12): `x` is supported on `T`, the flow
equations hold, and the trap and siphon constraints hold for `U = ⟦x⟧`. -/
def PotReachVia (T : Set (Transition Q)) (C C' : Multiset Q) (x : Transition Q → ℕ) : Prop :=
  (∀ t, x t ≠ 0 → t ∈ T) ∧ FlowEq C C' x ∧
  (∀ R, IsUTrap {t | x t ≠ 0} R → mass C' R = 0 → ∀ t, x t ≠ 0 → ¬ t.Into R) ∧
  (∀ R, IsUSiphon {t | x t ≠ 0} R → mass C R = 0 → ∀ t, x t ≠ 0 → ¬ t.OutOf R)

/-- `C ⇢ C'`: `C'` is potentially reachable from `C`. -/
def PotReach (T : Set (Transition Q)) (C C' : Multiset Q) : Prop := ∃ x, PotReachVia T C C' x

/-- **Reachability implies potential reachability** (consequence of Observation 11). -/
theorem MReach.potReach {T : Set (Transition Q)} {C C' : Multiset Q} (h : MReach T C C') :
    PotReach T C C' := by
  obtain ⟨w, hwT, hw⟩ := h.exists_firesSeq
  have hwU : ∀ t ∈ w, t ∈ {t | w.count t ≠ 0} := fun t ht => (List.count_pos_iff.2 ht).ne'
  refine ⟨fun t => w.count t, fun t ht => hwT t (List.count_pos_iff.1 (Nat.pos_of_ne_zero ht)),
    hw.flowEq, ?_, ?_⟩
  · intro R hR hC' t ht hi
    have := hw.trap hwU hR (List.count_pos_iff.1 (Nat.pos_of_ne_zero ht)) hi
    omega
  · intro R hR hC t ht ho
    have := hw.siphon hwU hR (List.count_pos_iff.1 (Nat.pos_of_ne_zero ht)) ho
    omega

/-- The flow equations preserve the number of agents. -/
theorem FlowEq.card_eq {C C' : Multiset Q} {x : Transition Q → ℕ} (h : FlowEq C C' x) :
    Multiset.card C' = Multiset.card C := by
  have hsum : ∀ D : Multiset Q, (Multiset.card D : ℤ) = ∑ q, (D.count q : ℤ) := fun D => by
    rw [← Multiset.toFinset_sum_count_eq D, Nat.cast_sum]
    exact sum_subset (subset_univ _) fun q _ hq => by
      simp [Multiset.count_eq_zero.2 (by simpa using hq)]
  have hdelta : ∀ t : Transition Q, ∑ q, t.delta q = 0 := fun t => by
    simp only [Transition.delta]
    rw [sum_sub_distrib, ← hsum, ← hsum]
    simp
  have := hsum C'
  rw [sum_congr rfl (fun q _ => h q), sum_add_distrib, ← hsum C, sum_comm] at this
  simp only [← mul_sum, hdelta, mul_zero, sum_const_zero, add_zero] at this
  exact_mod_cast this

/-- **Conserved weights.** If every transition in the support of `x` preserves the weight `w`
(`∑_q (post(t)(q) − pre(t)(q)) · w(q) = 0`), then the flow equations preserve the total weight
`∑_q C(q) · w(q)`. -/
theorem FlowEq.weight_eq {C C' : Multiset Q} {x : Transition Q → ℕ} (h : FlowEq C C' x)
    (w : Q → ℤ) (hw : ∀ t, x t ≠ 0 → ∑ q, t.delta q * w q = 0) :
    ∑ q, (C'.count q : ℤ) * w q = ∑ q, (C.count q : ℤ) * w q := by
  have h' : ∀ q, (C'.count q : ℤ) = C.count q + ∑ t, (x t : ℤ) * t.delta q := h
  simp only [h', add_mul, sum_add_distrib, sum_mul]
  rw [sum_comm (f := fun q t => (x t : ℤ) * t.delta q * w q)]
  have : ∀ t : Transition Q, ∑ q, (x t : ℤ) * t.delta q * w q = 0 := fun t => by
    by_cases ht : x t = 0
    · simp [ht]
    · simp only [mul_assoc, ← mul_sum, hw t ht, mul_zero]
  simp [this]

/-- The total weight of a multiset as a sum over states. -/
theorem sum_map_eq_sum_count (C : Multiset Q) (w : Q → ℤ) :
    (C.map w).sum = ∑ q, (C.count q : ℤ) * w q := by
  rw [Finset.sum_multiset_map_count]
  refine sum_subset (subset_univ _) (fun q _ hq => by
    simp [Multiset.count_eq_zero.2 (by simpa using hq)]) |>.trans ?_
  simp

/-- `∑_q (post(t)(q) − pre(t)(q)) · w(q) = w(post(t)) − w(pre(t))`. -/
theorem Transition.sum_delta_mul (t : Transition Q) (w : Q → ℤ) :
    ∑ q, t.delta q * w q = (t.post.map w).sum - (t.pre.map w).sum := by
  simp only [Transition.delta, sub_mul, sum_sub_distrib, sum_map_eq_sum_count]

end Cslib.PopulationProtocol
