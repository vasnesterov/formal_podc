import Papers.PODC2025.ByzantineSWMRRegisters.Impossibility
import Papers.PODC2025.ByzantineSWMRRegisters.Objects

/-!
# Main impossibility results of Hu–Toueg (PODC 2025)

Implementations from SWMR registers: base objects `register (Val i) (v₀ i)`, `i : ι`, where only
`owner i` may write register `i` (`swmrAccess owner`); processes `P` (finite, `n = card P`);
at most `f` Byzantine processes. Correctness is `Impl.ByzCorrect` (Byzantine linearizability of
every finite execution + termination in fair executions, Definition 9).

* `theorem29`: no correct implementation of the one-shot test-or-set object if `3 ≤ n ≤ 3f`.
* `theorem31_verifiable`, `theorem31_authenticated`, `theorem31_sticky`: no correct
  implementation of a verifiable / authenticated / sticky register if `3 ≤ n ≤ 3f` (for the
  authenticated register: if some value differs from the initial one; for the sticky register:
  if the value domain is nonempty).

The proofs instantiate `SigTest.no_byzCorrect`; Theorem 31 is proved directly (the paper derives
it from Theorem 29 and Observation 30, which tacitly needs a composition property of Byzantine
linearizable implementations).
-/

namespace Podc.ByzantineSWMRRegisters

open Cslib.SharedMemory Cslib.SharedMemory.Byzantine

variable {P : Type} [Fintype P] [DecidableEq P] {ι : Type} [DecidableEq ι] {Val : ι → Type}
  {v₀ : (i : ι) → Val i} {L : Type}

/-- **Theorem 29** of [Hu–Toueg, PODC 2025]: in a system with `3 ≤ n ≤ 3f` processes, `f` of
which may be Byzantine, there is no correct implementation of the (one-shot) test-or-set object
from SWMR registers. -/
theorem theorem29 (owner : ι → P) (s : P)
    (I : Impl testOrSet (fun i => register (Val i) (v₀ i)) P L) (hall : I.allowed = tosAllowed s)
    (hI : I.RespectsAccess (swmrAccess owner)) {f : ℕ} (hn3 : 3 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 3 * f) : ¬ I.ByzCorrect (swmrAccess owner) f oneShot :=
  (tosSig s).no_byzCorrect (swmr_singleWriter owner) I hall hI hn3 hn (tosSig_admits s)

/-- **Theorem 31** of [Hu–Toueg, PODC 2025], verifiable registers: for `3 ≤ n ≤ 3f` there is no
correct implementation of an SWMR verifiable register (Definition 10) from SWMR registers. -/
theorem theorem31_verifiable {V : Type} (v₀' : V) (owner : ι → P) (w : P)
    (I : Impl (verReg V v₀') (fun i => register (Val i) (v₀ i)) P L)
    (hall : I.allowed = verAllowed w) (hI : I.RespectsAccess (swmrAccess owner)) {f : ℕ}
    (hn3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * f) :
    ¬ I.ByzCorrect (swmrAccess owner) f (fun _ _ => True) :=
  (verSig v₀' w v₀').no_byzCorrect (swmr_singleWriter owner) I hall hI hn3 hn
    (sigTest_admits_true _)

/-- **Theorem 31** of [Hu–Toueg, PODC 2025], authenticated registers: for `3 ≤ n ≤ 3f` there is no
correct implementation of an SWMR authenticated register (Definition 15) from SWMR registers,
provided some value differs from the initial value `v₀'` (for a one-element domain the
authenticated register is trivial, see `Degenerate.lean`). -/
theorem theorem31_authenticated {V : Type} (v₀' : V) {v : V} (hv : v ≠ v₀') (owner : ι → P)
    (w : P) (I : Impl (authReg V v₀') (fun i => register (Val i) (v₀ i)) P L)
    (hall : I.allowed = authAllowed w) (hI : I.RespectsAccess (swmrAccess owner)) {f : ℕ}
    (hn3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * f) :
    ¬ I.ByzCorrect (swmrAccess owner) f (fun _ _ => True) :=
  (authSig w hv).no_byzCorrect (swmr_singleWriter owner) I hall hI hn3 hn (sigTest_admits_true _)

/-- **Theorem 31** of [Hu–Toueg, PODC 2025], sticky registers: for `3 ≤ n ≤ 3f` there is no
correct implementation of an SWMR sticky register (Definition 21) from SWMR registers. -/
theorem theorem31_sticky {V : Type} [Nonempty V] (owner : ι → P) (w : P)
    (I : Impl (stickyReg V) (fun i => register (Val i) (v₀ i)) P L)
    (hall : I.allowed = stickyAllowed w) (hI : I.RespectsAccess (swmrAccess owner)) {f : ℕ}
    (hn3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * f) :
    ¬ I.ByzCorrect (swmrAccess owner) f (fun _ _ => True) :=
  (stickySig w (Classical.arbitrary V)).no_byzCorrect (swmr_singleWriter owner) I hall hI hn3 hn
    (sigTest_admits_true _)

end Podc.ByzantineSWMRRegisters
