import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Window registers, stacks, queues and classes of base objects

Sequential specifications (`ObjSpec`) of

* `windowObj V w` — the `w`-window register of Mostéfaoui, Perrin and Raynal: it stores the
  sequence of the last `w` values written (fewer if fewer were written); `read` returns the
  sequence. A `1`-window register is a standard register; the consensus number of a `w`-window
  register is `w`.
* `stackObj V` — an atomic stack (`push v` / `pop`, `pop` on the empty stack returns `none`).
* `queueObj V` — an atomic FIFO queue (`enq v` / `deq`, `deq` on the empty queue returns `none`).

and semantic *classes* of base objects, used to state impossibility results for all objects of a
class at once:

* `ObjSpec.CommuteAt`, `ObjSpec.OverwritesAt`, `ObjSpec.Interfering` — Herlihy's *interfering*
  primitives: at every state, any two operations commute or one overwrites the other
  (read, write, test&set, swap, fetch&add, …);
* `ObjSpec.WindowLike S w` — every operation is read-only or has a state-independent response
  ("write"), and any `w` consecutive non-read-only operations determine the state;
  `windowObj V w'` is `WindowLike` for every `w ≥ w'`;
* `StackRep S V`, `ObjSpec.StackLike` — the object is (isomorphic to) a stack.
-/

namespace Cslib.SharedMemory

-- CSLib candidate (whole file)

/-! ## Window registers -/

/-- Operations of a window register. -/
inductive WinOp (V : Type) where
  /-- Append a value. -/
  | write (v : V)
  /-- Read the window. -/
  | read
  deriving DecidableEq

/-- The `w`-window register over `V`, initially empty (`⊥`): the state is the list of the last
(at most) `w` values written, oldest first. -/
abbrev windowObj (V : Type) (w : ℕ) : ObjSpec where
  State := List V
  Op := WinOp V
  Resp := List V
  init := []
  δ s
    | .write v => ((s ++ [v]).drop (s.length + 1 - w), [])
    | .read => (s, s)

/-! ## Stacks and queues -/

/-- Operations of a stack. -/
inductive StackOp (V : Type) where
  | push (v : V)
  | pop
  deriving DecidableEq

/-- An atomic stack over `V` (top = head of the list). `push` returns `none`. -/
abbrev stackObj (V : Type) : ObjSpec where
  State := List V
  Op := StackOp V
  Resp := Option V
  init := []
  δ s
    | .push v => (v :: s, none)
    | .pop => (s.tail, s.head?)

/-- Operations of a queue. -/
inductive FifoOp (V : Type) where
  | enq (v : V)
  | deq
  deriving DecidableEq

/-- An atomic FIFO queue over `V` (oldest = head of the list). `enq` returns `none`. -/
abbrev queueObj (V : Type) : ObjSpec where
  State := List V
  Op := FifoOp V
  Resp := Option V
  init := []
  δ s
    | .enq v => (s ++ [v], none)
    | .deq => (s.tail, s.head?)

/-! ## Interfering objects -/

namespace ObjSpec

variable (S : ObjSpec)

/-- `o₁` and `o₂` commute at `s` (Herlihy): both orders lead to the same state. -/
def CommuteAt (s : S.State) (o₁ o₂ : S.Op) : Prop :=
  (S.δ (S.δ s o₁).1 o₂).1 = (S.δ (S.δ s o₂).1 o₁).1

/-- `o₁` overwrites `o₂` at `s` (Herlihy): applying `o₂` and then `o₁` leads to the same state as
applying `o₁` alone. -/
def OverwritesAt (s : S.State) (o₁ o₂ : S.Op) : Prop :=
  (S.δ (S.δ s o₂).1 o₁).1 = (S.δ s o₁).1

/-- Herlihy's *interfering* objects: at every state, any two operations commute or one of them
overwrites the other. -/
def Interfering : Prop :=
  ∀ s o₁ o₂, S.CommuteAt s o₁ o₂ ∨ S.OverwritesAt s o₁ o₂ ∨ S.OverwritesAt s o₂ o₁

/-- *Window-like* objects with window `w`: every operation is read-only or a "write" whose
response does not depend on the state, and any sequence of at least `w` non-read-only operations
leads to a state that does not depend on the starting state. -/
def WindowLike (w : ℕ) : Prop :=
  (∀ o, S.ReadOnly o ∨ ∀ s s', (S.δ s o).2 = (S.δ s' o).2) ∧
  ∀ os : List S.Op, os ≠ [] → w ≤ os.length → (∀ o ∈ os, ¬ S.ReadOnly o) →
    ∀ s s', S.runOps s os = S.runOps s' os

lemma WindowLike.mono {S : ObjSpec} {w w' : ℕ} (h : S.WindowLike w) (hw : w ≤ w') :
    S.WindowLike w' :=
  ⟨h.1, fun os hne hos hro s s' => h.2 os hne (hw.trans hos) hro s s'⟩

end ObjSpec

/-- A representation of the object `S` as a stack over `V`: states are (injectively) lists,
every operation is a `push v` or a `pop`, with the stack's effect and responses. -/
structure StackRep (S : ObjSpec) (V : Type) where
  /-- The stack contents (top first). -/
  toList : S.State → List V
  inj : Function.Injective toList
  /-- `some v`: the operation pushes `v`; `none`: it pops. -/
  push : S.Op → Option V
  push_state : ∀ s o v, push o = some v → toList (S.δ s o).1 = v :: toList s
  push_resp : ∀ s s' o v, push o = some v → (S.δ s o).2 = (S.δ s' o).2
  pop_state : ∀ s o, push o = none → toList (S.δ s o).1 = (toList s).tail
  pop_resp : ∀ s s' o, push o = none → (toList s).head? = (toList s').head? →
    (S.δ s o).2 = (S.δ s' o).2

/-- The object is (isomorphic to) a stack. -/
def ObjSpec.StackLike (S : ObjSpec) : Prop := ∃ V : Type, Nonempty (StackRep S V)

/-! ## The standard objects belong to the classes -/

/-- The stack is stack-like. -/
def stackObj.rep (V : Type) : StackRep (stackObj V) V where
  toList s := s
  inj := fun _ _ h => h
  push
    | .push v => some v
    | .pop => none
  push_state s o v h := by cases o <;> simp_all
  push_resp s s' o v h := by cases o <;> simp_all
  pop_state s o h := by cases o <;> simp_all
  pop_resp s s' o h h' := by cases o <;> simp_all

lemma stackObj_stackLike (V : Type) : (stackObj V).StackLike := ⟨V, ⟨stackObj.rep V⟩⟩

/-- The window after a write, in terms of the full history `t` (the state is its last `w`
values). -/
lemma windowObj_write_last {V : Type} {w : ℕ} (t : List V) (v : V) :
    ((windowObj V w).δ (t.drop (t.length - w)) (.write v)).1 =
      (t ++ [v]).drop ((t ++ [v]).length - w) := by
  simp only [List.drop_append, List.drop_drop, List.length_drop, List.length_append,
    List.length_singleton]
  congr 2 <;> omega

lemma windowObj_runOps_writes_last {V : Type} {w : ℕ} (t : List V) (vs : List V) :
    (windowObj V w).runOps (t.drop (t.length - w)) (vs.map WinOp.write) =
      (t ++ vs).drop ((t ++ vs).length - w) := by
  induction vs generalizing t with
  | nil => simp [ObjSpec.runOps]
  | cons v vs ih =>
    rw [List.map_cons, ObjSpec.runOps_cons, windowObj_write_last, ih]
    simp

/-- After at least one write, the window is the last `w` values of the full history. -/
lemma windowObj_runOps_writes {V : Type} {w : ℕ} (s : List V) (v : V) (vs : List V) :
    (windowObj V w).runOps s ((v :: vs).map WinOp.write) =
      (s ++ v :: vs).drop ((s ++ v :: vs).length - w) := by
  rw [List.map_cons, ObjSpec.runOps_cons]
  have : ((windowObj V w).δ s (.write v)).1 = (s ++ [v]).drop ((s ++ [v]).length - w) := by
    simp only [List.length_append, List.length_singleton]
  rw [this, windowObj_runOps_writes_last]
  simp

lemma drop_append_last {V : Type} {w : ℕ} (s l : List V) (hw : w ≤ l.length) :
    (s ++ l).drop ((s ++ l).length - w) = l.drop (l.length - w) := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega)]
  simp only [List.length_append, List.nil_append]
  congr 1; omega

/-- A `w'`-window register is window-like with window `w` for every `w ≥ w'`. -/
lemma windowObj_windowLike (V : Type) {w' w : ℕ} (hw : w' ≤ w) :
    (windowObj V w').WindowLike w := by
  refine ⟨fun o => ?_, fun os hne hos hro s s' => ?_⟩
  · cases o with
    | write v => exact Or.inr fun s s' => rfl
    | read => exact Or.inl fun s => rfl
  · have hw : ∀ o ∈ os, ∃ v, o = WinOp.write v := by
      intro o ho
      cases o with
      | write v => exact ⟨v, rfl⟩
      | read => exact absurd (fun s => rfl) (hro _ ho)
    obtain ⟨vs, rfl⟩ : ∃ vs : List V, os = vs.map WinOp.write := by
      clear hos hro hne
      induction os with
      | nil => exact ⟨[], rfl⟩
      | cons o os ih =>
        obtain ⟨v, rfl⟩ := hw o (by simp)
        obtain ⟨vs, rfl⟩ := ih (fun o ho => hw o (by simp [ho]))
        exact ⟨v :: vs, rfl⟩
    obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hne
      | cons v vs' => exact ⟨v, vs', rfl⟩
    simp only [List.length_map] at hos
    rw [windowObj_runOps_writes, windowObj_runOps_writes, drop_append_last _ _ (by omega),
      drop_append_last _ _ (by omega)]

/-- Read/write registers are interfering (a read commutes with everything, a write overwrites
everything). -/
lemma register_interfering (V : Type) (v₀ : V) : (register V v₀).Interfering := by
  intro s o₁ o₂
  cases o₁ <;> cases o₂ <;> simp [ObjSpec.CommuteAt, ObjSpec.OverwritesAt]

/-- Window registers with window `1` are standard registers: interfering. -/
lemma windowObj_one_interfering (V : Type) : (windowObj V 1).Interfering := by
  intro s o₁ o₂
  cases o₁ <;> cases o₂ <;> simp [ObjSpec.CommuteAt, ObjSpec.OverwritesAt]

end Cslib.SharedMemory
