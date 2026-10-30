import Papers.PODC2026.ConflictFreedom.Alg1WCF

/-!
# Example: the shared counter of Figure 1

The counter with operations `read`, `inc`, `dec` (Section 3.2, Figure 1): updates commute with
each other, reads conflict with updates. The universal construction instantiated with the counter
is linearizable and weakly conflict-free (non-vacuity of the hypotheses of Theorems 4.3–4.4).
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz

/-- Counter operations. -/
inductive CtrOp where
  | read
  | inc
  | dec
  deriving DecidableEq, Inhabited

/-- The shared counter (`inc`/`dec` return `0`). -/
abbrev counter : ObjSpec where
  State := ℤ
  Op := CtrOp
  Resp := ℤ
  init := 0
  δ q o := match o with
    | .read => (q, q)
    | .inc => (q + 1, 0)
    | .dec => (q - 1, 0)

instance : Inhabited counter.Op := inferInstanceAs (Inhabited CtrOp)
instance : Inhabited counter.Resp := inferInstanceAs (Inhabited ℤ)

/-- Increments and decrements commute. -/
example : ¬ counter.Conflicting .inc .dec := by
  rintro ⟨q, hq⟩
  apply hq
  refine ⟨?_, rfl, rfl⟩
  change (q : ℤ) + 1 - 1 = q - 1 + 1
  ring

/-- A read conflicts with an increment. -/
example : counter.Conflicting .read .inc := by
  refine ⟨(0 : ℤ), fun h => ?_⟩
  have := h.2.1
  change (0 : ℤ) = 0 + 1 - 1 + 1 at this
  omega

/-- Theorem 4.3 for the counter and two processes. -/
example : (Alg1.impl (A := counter) (n := 2)).Linearizable := Alg1.linearizable

/-- Theorem 4.4 for the counter and three processes. -/
example : WeakConflictFree (Alg1.impl (A := counter) (n := 3)) := Alg1.weakConflictFree

end Podc.ConflictFreedom
