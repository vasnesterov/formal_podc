import Papers.PODC2014.WritableObjects.Proj
import Papers.PODC2014.WritableObjects.Defs

/-!
# Removing internal steps from a history

CSLib executions contain internal steps (`Label.tau`); the histories of base objects in our
transcripts do not. Removing the internal steps changes none of the history notions
(`opOf`, `respOf`, `Invoked`, `Completed`, `Precedes`), hence preserves linearizations, isolation
of writes and sequential writability (`SeqWritable.dropTau`).

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/History.lean
-/

namespace Podc.WritableObjects

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-- Keep invocations and responses, drop internal steps. -/
def keepIR : Label P A → Option (Label P A)
  | .tau _ => none
  | ℓ => some ℓ

/-- The history without internal steps. -/
def dropTau (β : List (Label P A)) : List (Label P A) := β.filterMap keepIR

lemma opsOf_filterMap_keepIR (β : List (Label P A)) (p : P) :
    opsOf (β.filterMap keepIR) p = opsOf β p := by
  induction β with
  | nil => rfl
  | cons ℓ β ih => cases ℓ <;> simp [keepIR, ih, List.filterMap_cons]

lemma respsOf_filterMap_keepIR (β : List (Label P A)) (p : P) :
    respsOf (β.filterMap keepIR) p = respsOf β p := by
  induction β with
  | nil => rfl
  | cons ℓ β ih => cases ℓ <;> simp [keepIR, ih, List.filterMap_cons]

lemma precedes_iff_take (β : List (Label P A)) (x y : OpId P) :
    Precedes β x y ↔ ∃ t ≤ β.length, Completed (β.take t) x ∧ ¬ Invoked (β.take t) y := by
  have := precedes_iff (fun ℓ : Label P A => some ℓ) β x y
  simpa using this

lemma precedes_dropTau (β : List (Label P A)) (x y : OpId P) :
    Precedes (dropTau β) x y ↔ Precedes β x y := by
  rw [dropTau, precedes_iff, precedes_iff_take]
  simp only [Completed, Invoked, opsOf_filterMap_keepIR, respsOf_filterMap_keepIR]

lemma opOf_dropTau (β : List (Label P A)) (x : OpId P) : opOf (dropTau β) x = opOf β x := by
  simp [opOf, dropTau, opsOf_filterMap_keepIR]

lemma respOf_dropTau (β : List (Label P A)) (x : OpId P) :
    respOf (dropTau β) x = respOf β x := by
  simp [respOf, dropTau, respsOf_filterMap_keepIR]

lemma invoked_dropTau (β : List (Label P A)) (x : OpId P) :
    Invoked (dropTau β) x ↔ Invoked β x := by
  simp [Invoked, dropTau, opsOf_filterMap_keepIR]

lemma completed_dropTau (β : List (Label P A)) (x : OpId P) :
    Completed (dropTau β) x ↔ Completed β x := by
  simp [Completed, dropTau, respsOf_filterMap_keepIR]

lemma seqOK_dropTau (β : List (Label P A)) (q : A.State) (L : List (OpId P × A.Op)) :
    SeqOK (dropTau β) q L ↔ SeqOK β q L := by
  induction L generalizing q with
  | nil => simp [SeqOK]
  | cons y L ih =>
    obtain ⟨x, o⟩ := y
    simp only [SeqOK, respOf_dropTau, ih]

lemma isLinearization_dropTau (β : List (Label P A)) (L : List (OpId P × A.Op)) :
    IsLinearization (dropTau β) L ↔ IsLinearization β L := by
  constructor
  · intro h
    exact ⟨h.nodup, fun y hy => (opOf_dropTau β y.1) ▸ h.op_eq y hy,
      fun a ha => h.complete a ((completed_dropTau β a).2 ha),
      fun a b hab hb => h.realtime a b ((precedes_dropTau β a b).2 hab) hb,
      (seqOK_dropTau β _ L).1 h.seq⟩
  · intro h
    exact ⟨h.nodup, fun y hy => (opOf_dropTau β y.1).symm ▸ h.op_eq y hy,
      fun a ha => h.complete a ((completed_dropTau β a).1 ha),
      fun a b hab hb => h.realtime a b ((precedes_dropTau β a b).1 hab) hb,
      (seqOK_dropTau β _ L).2 h.seq⟩

/-- Sequential writability does not depend on internal steps. -/
lemma SeqWritable.dropTau {T : ObjSpec} {W : Writable T} {β : List (Label P T)}
    (h : SeqWritable W β) : SeqWritable W (dropTau β) := by
  intro hiso
  have hiso' : WritesIsolated W β := by
    intro x y hxy hx hy
    rw [← opOf_dropTau] at hx
    rw [← invoked_dropTau] at hy
    simpa only [precedes_dropTau] using hiso x y hxy hx hy
  obtain ⟨L, hL⟩ := h hiso'
  exact ⟨L, (isLinearization_dropTau β L).2 hL⟩

end Podc.WritableObjects
