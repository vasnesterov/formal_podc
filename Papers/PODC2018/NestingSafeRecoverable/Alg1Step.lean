import Papers.PODC2018.NestingSafeRecoverable.Alg1
import Papers.PODC2018.NestingSafeRecoverable.Alg1Gen

/-!
# One-step lemmas for Algorithm 1

The effect of each kind of step of Algorithm 1 on the value of `R` (`Rv`), the registers `S_p`
(`Sv`), the local states and the history.
-/

set_option linter.unusedSectionVars false

namespace Podc.NestingSafeRecoverable.Alg1

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] {v₀ : V}

/-- The value of the register `R`. -/
def Rv (C : (alg1 P V v₀).Cfg) : V := C.mem none

/-- The value of `S_p`. -/
def Sv (C : (alg1 P V v₀).Cfg) (p : P) : Bool × Option V := C.mem (some p)

section Steps

variable {C : (alg1 P V v₀).Cfg} {p : P} {o : RWOp V} {pc pc' : PC1} {v : Loc1 V}

lemma ev_R_read (h : C.st p = some (o, pc, v)) {k : V → Loc1 V}
    (ha : act1 P V v₀ p o pc v = .access none (RWOp.read : RWOp V) pc' k) :
    C.ev (.step p) = { C with st := Function.update C.st p (some (o, pc', k (Rv C))) } := by
  rw [Alg.ev_step_access C h ha]
  congr 1
  exact @Function.update_eq_self _ _ (fun a b => Classical.propDecidable (a = b)) _ _

lemma ev_R_write (h : C.st p = some (o, pc, v)) {k : V → Loc1 V} {w : V}
    (ha : act1 P V v₀ p o pc v = .access none (RWOp.write w) pc' k) :
    Rv (C.ev (.step p)) = w ∧ (∀ q, Sv (C.ev (.step p)) q = Sv C q) ∧
    (C.ev (.step p)).st = Function.update C.st p (some (o, pc', k w)) ∧
    (C.ev (.step p)).hist = C.hist := by
  rw [Alg.ev_step_access C h ha]
  refine ⟨?_, fun q => ?_, rfl, rfl⟩
  · simp [Rv]
  · simp [Sv]

lemma ev_S_read (h : C.st p = some (o, pc, v)) {k : Bool × Option V → Loc1 V}
    (ha : act1 P V v₀ p o pc v = .access (some p) (RWOp.read : RWOp (Bool × Option V)) pc' k) :
    C.ev (.step p) = { C with st := Function.update C.st p (some (o, pc', k (Sv C p))) } := by
  rw [Alg.ev_step_access C h ha]
  congr 1
  exact @Function.update_eq_self _ _ (fun a b => Classical.propDecidable (a = b)) _ _

lemma ev_S_write (h : C.st p = some (o, pc, v)) {k : Bool × Option V → Loc1 V}
    {s : Bool × Option V}
    (ha : act1 P V v₀ p o pc v = .access (some p) (RWOp.write s) pc' k) :
    Rv (C.ev (.step p)) = Rv C ∧ Sv (C.ev (.step p)) p = s ∧
    (∀ q, q ≠ p → Sv (C.ev (.step p)) q = Sv C q) ∧
    (C.ev (.step p)).st = Function.update C.st p (some (o, pc', k s)) ∧
    (C.ev (.step p)).hist = C.hist := by
  rw [Alg.ev_step_access C h ha]
  refine ⟨?_, ?_, fun q hq => ?_, rfl, rfl⟩
  · simp [Rv]
  · simp [Sv]
  · simp [Sv, hq]

end Steps

end Podc.NestingSafeRecoverable.Alg1
