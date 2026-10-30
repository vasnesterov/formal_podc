import Podc.Foundations.Data.Mazurkiewicz.Equiv
import Papers.PODC2026.ConflictFreedom.Progress

/-!
# Well-defined return values on traces (Lemmas 4.1 and 4.2)

Kuznetsov, Sutra and Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*, PODC 2026,
Section 4.1 and Appendix A.2.

For a sequential object `A`, schedules are lists of operations; `s ∼ t`
(`TraceEquiv A.Conflicting s t`) means that `t` has the same operations as `s` (as a multiset) and
every pair of occurrences of conflicting operations appears in the same order. `respOcc A.δ q s o i`
is the response of the `i`-th (0-based) occurrence of `o` when `s` is executed from `q`
(`ret*(o^(i+1), s)` for `q = q₀`).
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

variable (A : ObjSpec)

/-- Lemma 4.1 of [KST26]: equivalent schedules give the same response to every occurrence of an
operation (and lead to the same state). -/
theorem lemma_4_1 {s t : List A.Op} (h : TraceEquiv A.Conflicting s t) (o : A.Op) (i : ℕ) :
    respOcc A.δ A.init s o i = respOcc A.δ A.init t o i ∧
      runState A.δ A.init s = runState A.δ A.init t :=
  ⟨respOcc_eq_of_traceEquiv_conflict h A.init o i,
    runState_eq_of_traceEquiv_conflict h A.init⟩

/-- Lemma 4.2 of [KST26]: if (the trace of) `s` is a prefix of (the trace of) `t`, i.e.
`t ∼ s · z`, then every occurrence in `s` has the same response in `s` and in `t`. -/
theorem lemma_4_2 {s t z : List A.Op} (h : TraceEquiv A.Conflicting t (s ++ z)) {o : A.Op}
    {i : ℕ} (hi : i < s.count o) :
    respOcc A.δ A.init s o i = respOcc A.δ A.init t o i :=
  respOcc_eq_of_le_conflict h A.init hi

end Podc.ConflictFreedom
