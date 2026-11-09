import Papers.PODC2016.OhRAMAtomicMemory.Safety
import Papers.PODC2016.OhRAMAtomicMemory.Liveness
import Papers.PODC2016.OhRAMAtomicMemory.ComplexityFix
import Papers.PODC2016.OhRAMAtomicMemory.Sanity

/-!
# Oh-RAM! (Hadjistasi–Nicolaou–Schwarzmann, PODC 2016): main results

Theorems 5, 12, 16 and 22: OhSam, OhMam, OhSam', OhMam' implement atomic registers
(atomicity: `theorem_5`, …; termination with at most `f < |S|/2` server crashes: `theorem_5_live`, …).
The read message complexity of Table 1 fails for the printed code (`ohSam_read_msgs_gt`, …) and holds
after nesting line 53 in the `if` of line 51 (`readMsgBound_fix_paper`).
-/

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [DecidableEq V]

/-- **Theorem 5** (OhSam implements an atomic SWMR register): atomicity and termination when
fewer than half of the servers crash. -/
theorem theorem_5_full (v₀ : V) {f : ℕ} (hf : 2 * f < Fintype.card S) :
    (ohSam R S V v₀).Linearizable ∧ Live (ohSam R S V v₀) f :=
  ⟨theorem_5 v₀, theorem_5_live _ _ _ v₀ hf⟩

/-- **Theorem 12** (OhMam implements an atomic MWMR register). -/
theorem theorem_12_full [LinearOrder W] (v₀ : V) {f : ℕ} (hf : 2 * f < Fintype.card S) :
    (ohMam W R S V v₀).Linearizable ∧ Live (ohMam W R S V v₀) f :=
  ⟨theorem_12 v₀, theorem_12_live _ _ _ _ v₀ hf⟩

/-- **Theorem 16** (OhSam' implements an atomic SWMR register). -/
theorem theorem_16_full (v₀ : V) {f : ℕ} (hf : 2 * f < Fintype.card S) :
    (ohSam' R S V v₀).Linearizable ∧ Live (ohSam' R S V v₀) f :=
  ⟨theorem_16 v₀, theorem_16_live _ _ _ v₀ hf⟩

/-- **Theorem 22** (OhMam' implements an atomic MWMR register). -/
theorem theorem_22_full [LinearOrder W] (v₀ : V) {f : ℕ} (hf : 2 * f < Fintype.card S) :
    (ohMam' W R S V v₀).Linearizable ∧ Live (ohMam' W R S V v₀) f :=
  ⟨theorem_22 v₀, theorem_22_live _ _ _ _ v₀ hf⟩

end Podc.OhRAM
