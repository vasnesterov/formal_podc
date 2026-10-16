import Papers.PODC2021.ScannableBinaryObjects.Impl1

/-!
# Implementation 1 is linearizable (Theorem 2 of Ovens, PODC 2021, safety part)

Generic tools (CSLib candidates):

* `IsLinearization.insert`: a pending operation that does not change the state at the chosen
  position can be inserted into the middle of a linearization, provided no operation after
  the insertion point precedes it in real time (retroactive linearization points of read-only
  operations);
* list lemmas describing how a split `L = L₁ ++ L₂` survives such an insertion.

-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

open List

section Generic

variable {P : Type} {A : ObjSpec} [DecidableEq P]

-- CSLib candidate
/-- Retroactive linearization point: insert a pending operation `x` (which does not change the
state reached after `L₁`) between `L₁` and `L₂`, if nothing in `L₂` precedes `x`. -/
lemma IsLinearization.insert {α : List (Label P A)} {L₁ L₂ : List (OpId P × A.Op)}
    (hL : IsLinearization α (L₁ ++ L₂)) {x : OpId P} {o : A.Op} (hx : opOf α x = some o)
    (hxL : x ∉ (L₁ ++ L₂).map Prod.fst) (hxc : ¬ Completed α x)
    (hro : (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).1 = A.runOps A.init (L₁.map Prod.snd))
    (h2 : ∀ y ∈ L₂, ¬ Precedes α y.1 x) : IsLinearization α (L₁ ++ (x, o) :: L₂) where
  nodup := by
    have := hL.nodup
    simp only [map_append, map_cons] at this hxL ⊢
    rw [nodup_middle, nodup_cons]
    exact ⟨hxL, this⟩
  op_eq y hy := by
    simp only [mem_append, mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hL.op_eq y (mem_append_left _ hy)
    · exact hx
    · exact hL.op_eq y (mem_append_right _ hy)
  complete a ha := by
    have := hL.complete a ha
    simp only [map_append, map_cons, mem_append, mem_cons] at this ⊢
    tauto
  realtime a b hab hb := by
    have hsub : (L₁ ++ L₂).map Prod.fst <+ (L₁ ++ (x, o) :: L₂).map Prod.fst := by
      simp only [map_append, map_cons]
      exact Sublist.append_left (sublist_cons_self _ _) _
    by_cases hbx : b = x
    · subst hbx
      have ha := hL.complete a hab.completed
      have ha1 : a ∈ L₁.map Prod.fst := by
        simp only [map_append, mem_append] at ha
        rcases ha with ha | ha
        · exact ha
        · obtain ⟨y, hy, rfl⟩ := mem_map.1 ha
          exact absurd hab (h2 y hy)
      rw [sublist_pair_iff]
      exact ⟨L₁.map Prod.fst, (L₂.map Prod.fst).cons b, by simp, ha1, by simp⟩
    · have hb' : b ∈ (L₁ ++ L₂).map Prod.fst := by
        simp only [map_append, map_cons, mem_append, mem_cons] at hb ⊢
        rcases hb with hb | hb | hb
        · exact Or.inl hb
        · exact absurd hb hbx
        · exact Or.inr hb
      exact (hL.realtime a b hab hb').trans hsub
  seq := by
    have hs := hL.seq
    rw [seqOK_append] at hs ⊢
    refine ⟨hs.1, ?_, ?_⟩
    · intro r hr
      exact absurd (completed_iff_respOf.2 (by rw [hr]; rfl)) hxc
    · rw [hro]; exact hs.2

-- CSLib candidate
/-- A split `L = S₁ ++ S₂` survives the insertion of `z` at another split `L = W₁ ++ W₂`:
`z` lands either in the left part or in the right part. -/
lemma split_insert {X : Type} {S₁ S₂ W₁ W₂ : List X} (h : S₁ ++ S₂ = W₁ ++ W₂) (z : X) :
    ∃ S₁' S₂', W₁ ++ z :: W₂ = S₁' ++ S₂' ∧ (∀ y ∈ S₂', y ∈ S₂ ∨ y = z) ∧
      (∀ y ∈ S₂, y ∈ S₂') ∧ (S₁' = S₁ ∨ ∃ A B, S₁ = A ++ B ∧ S₁' = A ++ z :: B) := by
  rcases append_eq_append_iff.1 h with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · -- `W₁ = S₁ ++ a'`, `S₂ = a' ++ W₂`
    refine ⟨S₁, a' ++ z :: W₂, by simp, ?_, ?_, Or.inl rfl⟩
    · intro y hy; simp only [mem_append, mem_cons] at hy ⊢; tauto
    · intro y hy; simp only [mem_append, mem_cons] at hy ⊢; tauto
  · -- `S₁ = W₁ ++ c'`, `W₂ = c' ++ S₂`
    refine ⟨W₁ ++ z :: c', S₂, by simp, fun y hy => Or.inl hy, fun y hy => hy,
      Or.inr ⟨W₁, c', rfl, rfl⟩⟩

-- CSLib candidate
/-- A split around an element, `L = L₁ ++ y :: L₂`, survives the insertion of `z` at another
split `L = W₁ ++ W₂`. -/
lemma split_cons_insert {X : Type} {L₁ L₂ W₁ W₂ : List X} {y : X}
    (h : L₁ ++ y :: L₂ = W₁ ++ W₂) (z : X) :
    ∃ L₁' L₂', W₁ ++ z :: W₂ = L₁' ++ y :: L₂' ∧
      (L₁' = L₁ ∨ ∃ A B, L₁ = A ++ B ∧ L₁' = A ++ z :: B) := by
  rcases append_eq_append_iff.1 h with ⟨a', rfl, h2⟩ | ⟨c', rfl, rfl⟩
  · rcases a' with _ | ⟨y', a'⟩
    · simp only [nil_append] at h2; subst h2
      exact ⟨L₁ ++ [z], L₂, by simp, Or.inr ⟨L₁, [], by simp, rfl⟩⟩
    · simp only [cons_append, cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨L₁, a' ++ z :: W₂, by simp, Or.inl rfl⟩
  · exact ⟨W₁ ++ z :: c', L₂, by simp, Or.inr ⟨W₁, c', rfl, rfl⟩⟩

end Generic

end Cslib.SharedMemory

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

/-- The current operation instance of `p` (the next one if `p` is idle). -/
def cur (α : List (Label P (scannable O))) (p : P) : OpId P := (p, (respsOf α p).length)

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
  ∃ S₁ S₂ d, Cut α L (cur α p) S₁ S₂ ∧
    ((∀ y ∈ S₂, y.2.isScan = true) → ∀ i : Fin k, i.val < m → linSt S₁ i = b i) ∧
    numDanger Up C p + d ≤ Up.card ∧
    ((∃ W₁ W₂, Cut α L (cur α p) W₁ W₂ ∧ linSt W₁ = b) ∨
      (c ≤ d ∧ ((∃ y ∈ S₂, y.2.isScan = false) → c + 1 ≤ d)))

/-- Per-process invariant, by local state. -/
def PInvL (Sc Up : Finset P) (α : List (Label P (scannable O)))
    (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) (L : List (OpId P × ScanOp O)) (p : P) :
    Loc O Sc → Prop
  | .idle => C.pend p = none
  | .upd i o _ => C.pend p = some (.update i o) ∧ p ∈ Up ∧ cur α p ∉ L.map Prod.fst ∧
      opOf α (cur α p) = some (.update i o)
  | .scan1 _ _ => C.pend p = some .scan ∧ p ∈ Sc ∧ cur α p ∉ L.map Prod.fst ∧
      opOf α (cur α p) = some .scan
  | .scan2 c m b => (C.pend p = some .scan ∧ p ∈ Sc ∧ cur α p ∉ L.map Prod.fst ∧
      opOf α (cur α p) = some .scan) ∧
      ∀ hp : p ∈ Sc, C.mem (.inr ⟨p, hp⟩) = false → ScanInv Up α C L p c m b
  | .done r => C.pend p ≠ none ∧ ∃ L₁ L₂ o, L = L₁ ++ (cur α p, o) :: L₂ ∧
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
