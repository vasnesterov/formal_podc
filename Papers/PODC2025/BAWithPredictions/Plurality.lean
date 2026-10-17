import Podc.Foundations.Count

/-!
# Vote counting and plurality

The counting function and the plurality vote of this formalization are the shared library ones
(`Podc.Foundations.Count`), under the names used in the paper's algorithms:

* `cnt X f w = X.countEq f w`: the number of elements of `X` on which `f` takes the value `w`;
* `plur X f d = X.plurality f d`: a value of `f` that occurs most often on `X` (`d` if `X` is
  empty), ties broken arbitrarily. The only property used is
  `Finset.plurality_eq_of_card_lt_two_mul_countEq`: a value that occurs on a strict majority of
  `X` is the plurality.
-/

namespace BAWithPredictions

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- The number of `j ∈ X` with `f j = w`. -/
abbrev cnt (X : Finset ι) (f : ι → α) (w : α) : ℕ := X.countEq f w

/-- A most frequent value of `f` on `X` (`d` if `X = ∅`). -/
noncomputable abbrev plur (X : Finset ι) (f : ι → α) (d : α) : α := X.plurality f d

omit [DecidableEq ι] in
/-- `Finset.countEq_add_countEq_le` in terms of `cnt` (so that `omega` sees the same atoms). -/
theorem cnt_add_cnt_le {X : Finset ι} {f : ι → α} {w w' : α} (h : w ≠ w') :
    cnt X f w + cnt X f w' ≤ X.card :=
  Finset.countEq_add_countEq_le h

end BAWithPredictions
