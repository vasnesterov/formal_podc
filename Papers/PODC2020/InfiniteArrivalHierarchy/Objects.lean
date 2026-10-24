import Podc.Computability.Distributed.SharedMemory.Arrival.Basic
import Cslib.Computability.Distributed.SharedMemory.Objects.Window

/-!
# Shared objects of Perrin–Mostéfaoui–Bonin (PODC 2020), Section 2.3

* `consObj V`: the atomic consensus object `cons⟨V⟩` (the first proposed value is decided and
  returned to every invocation); `cons⟨B⟩` is `consObj Bool`;
* `consnObj V n junk`: the `n`-process consensus object `consₙ⟨V⟩`: the first `n` invocations
  return the first proposed value; the responses of later invocations are "unspecified" — they
  are given by an arbitrary function `junk` (of the number of earlier invocations and of the
  proposed value), and results about algorithms using `consnObj` hold for every `junk`;
* window registers are CSLib's `windowObj V k` (`k`-WReg; a register is a `1`-WReg).
-/

namespace Podc.InfiniteArrivalHierarchy

open Cslib.SharedMemory

/-- The atomic (multi-valued) consensus object `cons⟨V⟩`: the state is the decided value
(`none` before the first proposal); `propose v` returns the decided value. -/
abbrev consObj (V : Type) : ObjSpec where
  State := Option V
  Op := V
  Resp := V
  init := none
  δ s v := ((some (s.getD v)), s.getD v)

/-- The `n`-process consensus object `consₙ⟨V⟩`. The state is the number of invocations so far
and the decided value. The first `n` invocations return the first proposed value; the `k`-th
invocation with `k ≥ n` (0-based) proposing `v` returns `junk k v` (arbitrary). -/
abbrev consnObj (V : Type) (n : ℕ) (junk : ℕ → V → V) : ObjSpec where
  State := ℕ × Option V
  Op := V
  Resp := V
  init := (0, none)
  δ s v := ((s.1 + 1, some (s.2.getD v)), if s.1 < n then s.2.getD v else junk s.1 v)

@[simp] lemma consObj_δ {V : Type} (s : Option V) (v : V) :
    (consObj V).δ s v = (some (s.getD v), s.getD v) := rfl

@[simp] lemma consnObj_δ {V : Type} {n : ℕ} {junk : ℕ → V → V} (s : ℕ × Option V) (v : V) :
    (consnObj V n junk).δ s v =
      ((s.1 + 1, some (s.2.getD v)), if s.1 < n then s.2.getD v else junk s.1 v) := rfl

end Podc.InfiniteArrivalHierarchy
