import Papers.PODC2021.ScannableBinaryObjects.Impl1
import Podc.SharedMemory.LinResp
import Podc.SharedMemory.Run

/-!
# Implementation 1 is linearizable (Theorem 2 of Ovens, PODC 2021, safety part)

The generic tools `IsLinearization.insert`, `split_insert`, `split_cons_insert` (retroactive
linearization points) live in `Podc/SharedMemory/LinResp.lean`.

-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open List

section ScanLin

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

/-- The abstract state after a sequential history of the scannable object. -/
abbrev linSt (L : List (OpId P × ScanOp O)) : Fin k → Bool := linState (A := scannable O) L

@[simp] lemma scannable_δ_scan (v : Fin k → Bool) :
    (scannable O).δ v .scan = (v, .view v) := rfl

/-- Scans do not change the state. -/
lemma runOps_append_scans (q : Fin k → Bool) (S₁ S₂ : List (OpId P × ScanOp O))
    (h : ∀ y ∈ S₂, y.2.isScan = true) :
    (scannable O).runOps q ((S₁ ++ S₂).map Prod.snd) = (scannable O).runOps q (S₁.map Prod.snd) := by
  induction S₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton S₂ y ih =>
    obtain ⟨x, o⟩ := y
    have hy := h (x, o) (by simp)
    cases o with
    | scan =>
      rw [← append_assoc, map_append, ObjSpec.runOps_append, ih (fun y hy => h y (by simp [hy]))]
      rfl
    | update i o => simp [ScanOp.isScan] at hy

lemma linState_append_scans (S₁ S₂ : List (OpId P × ScanOp O))
    (h : ∀ y ∈ S₂, y.2.isScan = true) :
    linSt (S₁ ++ S₂) = linSt S₁ :=
  runOps_append_scans _ S₁ S₂ h

lemma linState_insert_scan (S₁ S₂ : List (OpId P × ScanOp O)) (x : OpId P) :
    linSt (S₁ ++ (x, .scan) :: S₂) = linSt (S₁ ++ S₂) := by
  simp only [linState, map_append, map_cons]
  rw [ObjSpec.runOps_append, ObjSpec.runOps_append]
  rfl

lemma linState_push_update (L : List (OpId P × ScanOp O)) (x : OpId P) (i : Fin k)
    (o : (O i).Op) :
    linSt (L ++ [(x, .update i o)]) = Function.update (linSt L) i ((O i).δ (linSt L i) o).1 := by
  simp only [linState, map_append, map_cons, map_nil]
  rw [ObjSpec.runOps_append]
  rfl

end ScanLin

namespace Impl1

open List

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P] {Sc Up : Finset P}

/-- Update in local state `l` has written `R p` and will not write it again before accessing
`B i` (the *dangerous* updates for a validating scanner `p`). -/
def dang (p : P) : Loc O Sc → Bool
  | .upd _ _ rest => rest.all (fun j => !decide (j.val = p))
  | _ => false

/-- Number of updaters whose pending update is dangerous for `p`. -/
def numDanger (Up : Finset P) (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) (p : P) : ℕ :=
  (Up.filter (fun q => dang p (C.loc q) = true)).card

/-- `L = L₁ ++ L₂` and no operation of `L₂` precedes `x`: `x` may be linearized between
`L₁` and `L₂`. -/
def Cut (α : List (Label P (scannable O))) (L : List (OpId P × ScanOp O)) (x : OpId P)
    (L₁ L₂ : List (OpId P × ScanOp O)) : Prop :=
  L = L₁ ++ L₂ ∧ ∀ y ∈ L₂, ¬ Precedes α y.1 x

/-- Invariant of a validating scanner `p` (state `scan2 c m b`) while `R p = 0`:
`S₁ | S₂` is the cut at the beginning of the current collect; if no update was linearized
since (`S₂` consists of scans), the reads of the current collect so far agree with the state
at the cut; `d` counts dirty collects (during which an update accessed some `B i`), each of
which consumed a dangerous update; either a clean collect has already been found (a cut whose
state is `b`), or all `c` completed collects were dirty. -/
def ScanInv (Up : Finset P) (α : List (Label P (scannable O)))
    (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) (L : List (OpId P × ScanOp O)) (p : P)
    (c m : ℕ) (b : Fin k → Bool) : Prop :=
  ∃ S₁ S₂ d, Cut α L (curOp α p) S₁ S₂ ∧
    ((∀ y ∈ S₂, y.2.isScan = true) → ∀ i : Fin k, i.val < m → linSt S₁ i = b i) ∧
    numDanger Up C p + d ≤ Up.card ∧
    ((∃ W₁ W₂, Cut α L (curOp α p) W₁ W₂ ∧ linSt W₁ = b) ∨
      (c ≤ d ∧ ((∃ y ∈ S₂, y.2.isScan = false) → c + 1 ≤ d)))

/-- Per-process invariant, by local state. -/
def PInvL (Sc Up : Finset P) (α : List (Label P (scannable O)))
    (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) (L : List (OpId P × ScanOp O)) (p : P) :
    Loc O Sc → Prop
  | .idle => C.pend p = none
  | .upd i o _ => C.pend p = some (.update i o) ∧ p ∈ Up ∧ curOp α p ∉ L.map Prod.fst ∧
      opOf α (curOp α p) = some (.update i o)
  | .scan1 _ _ => C.pend p = some .scan ∧ p ∈ Sc ∧ curOp α p ∉ L.map Prod.fst ∧
      opOf α (curOp α p) = some .scan
  | .scan2 c m b => (C.pend p = some .scan ∧ p ∈ Sc ∧ curOp α p ∉ L.map Prod.fst ∧
      opOf α (curOp α p) = some .scan) ∧
      ∀ hp : p ∈ Sc, C.mem (.inr ⟨p, hp⟩) = false → ScanInv Up α C L p c m b
  | .done r => C.pend p ≠ none ∧ ∃ L₁ L₂ o, L = L₁ ++ (curOp α p, o) :: L₂ ∧
      ((scannable O).δ (linSt L₁) o).2 = r

/-- The linearizability invariant. -/
structure Inv (Sc Up : Finset P) (α : List (Label P (scannable O)))
    (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) (L : List (OpId P × ScanOp O)) :
    Prop where
  lin : IsLinearization α L
  mem : ∀ i, C.mem (.inl i) = linSt L i
  proc : ∀ p, PInvL Sc Up α C L p (C.loc p)

end Impl1

end Cslib.SharedMemory.Scannable
