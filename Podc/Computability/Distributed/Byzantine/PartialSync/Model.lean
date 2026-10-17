import Cslib.Computability.Distributed.Byzantine.PartialSync.Model

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/PartialSync/Model.lean (append to
-- the existing file; `List.flatMap_range_eq_of_forall_ne` to `Cslib/Foundations/Data/List`)

/-!
# Inboxes on links with a constant delay

Addition to `Cslib/Computability/Distributed/Byzantine/PartialSync/Model.lean`.

* `List.flatMap_range_eq_of_forall_ne`: a `flatMap` over `range n` of a function that is `[]`
  except at `k < n` is its value at `k`.
* `Run.inbox_of_dl_eq_add`: on a link on which every batch is delivered `e` time units after it is
  sent, the inbox at time `τ` is the batch sent at `τ - e` (nothing before time `e`). The
  zero-delay case is CSLib's `Run.inbox_of_dl_eq`.
-/

/-- A `flatMap` over `range n` of a function that is `[]` except at `k < n` is its value at `k`. -/
theorem List.flatMap_range_eq_of_forall_ne {α : Type*} {f : ℕ → List α} {k : ℕ} :
    ∀ {n : ℕ}, k < n → (∀ t, t ≠ k → f t = []) → (List.range n).flatMap f = f k := by
  intro n hk h
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge k n with h' | h'
    · rw [ih h', h n (by omega), List.append_nil]
    · obtain rfl : k = n := by omega
      rw [List.flatMap_eq_nil_iff.mpr (fun t ht => h t (by simp at ht; omega)), List.nil_append]

namespace Cslib.Byzantine.PartialSync

namespace Run

variable {P M S VI VO : Type*} [DecidableEq P] (A : Algorithm P M S VI VO)

/-- On a link `q → p` on which every batch is delivered `e` time units after it is sent, the inbox
of `p` at time `τ` is the batch sent by `q` at time `τ - e` (nothing before time `e`). -/
theorem inbox_of_dl_eq_add {R : Run P M VI} {q p : P} {e : ℕ} (h : ∀ σ, R.dl q σ p = σ + e)
    (τ : ℕ) : R.inbox A p τ q = if e ≤ τ then R.out A q (τ - e) p else [] := by
  rw [inbox_eq_flatMap]
  split_ifs with he
  · rw [List.flatMap_range_eq_of_forall_ne (k := τ - e) (by omega)]
    · simp only [dlv, h]; rw [ite_eq_left (by omega)]
    · intro t ht
      simp only [dlv, h]; rw [ite_eq_right (by omega)]
  · refine List.flatMap_eq_nil_iff.mpr fun t _ => ?_
    simp only [dlv, h]
    rw [ite_eq_right (by omega)]

end Run

end Cslib.Byzantine.PartialSync
