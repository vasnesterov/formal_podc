import Podc.Computability.Distributed.SharedMemory.NRL.Erase
import Podc.Computability.Distributed.SharedMemory.NRL.Model

/-!
# Generic helpers for the correctness proof of Algorithm 1

* `Alg.pendOp_run`: in a reachable configuration, the operation a process is running is the
  operation of its current instance `curOp (N H) p` (which has not completed);
* list surgery on sequential histories of registers: `FW L x o` (the entry `(x, o)` is
  immediately followed by a write), retracting a pending entry (`retract`).
-/

namespace Cslib.SharedMemory.NRL.Alg

open Cslib.SharedMemory

variable {P : Type} {O : ObjSpec} [DecidableEq P] {A : Alg P O}

-- CSLib candidate (NRL/Model.lean)
/-- The operation a process is running is the last one it invoked. -/
def PendOp (C : A.Cfg) : Prop :=
  ∀ p o pc v, C.st p = some (o, pc, v) → (opsOf (N C.hist) p).getLast? = some o

lemma pendOp_init : PendOp (A.init) := by
  intro p o pc v h; simp [init] at h

lemma PendOp.ev {C : A.Cfg} (hC : PendOp C) (e : Ev P O) : PendOp (C.ev e) := by
  rcases e with ⟨p, o⟩ | p | p
  · rcases hs : C.st p with _ | x
    · rw [ev_inv_of_none C o hs]
      intro q o' pc v h
      by_cases hq : q = p
      · subst hq; simp at h; simp [opsOf_append, h.1]
      · simp [Function.update_of_ne hq] at h
        simpa [opsOf_append, Ne.symm hq] using hC q o' pc v h
    · rw [ev_inv_of_some C o hs]; exact hC
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · rw [ev_step_of_none C hs]; exact hC
    · rcases ha : A.act p o pc v with ⟨i, op, pc', k⟩ | ⟨pc', v'⟩ | r
      · rw [ev_step_access C hs ha]
        intro q o' pc'' v'' h
        by_cases hq : q = p
        · subst hq; simp at h; rw [← h.1]; exact hC q o pc v hs
        · simp [Function.update_of_ne hq] at h; exact hC q o' pc'' v'' h
      · rw [ev_step_internal C hs ha]
        intro q o' pc'' v'' h
        by_cases hq : q = p
        · subst hq; simp at h; rw [← h.1]; exact hC q o pc v hs
        · simp [Function.update_of_ne hq] at h; exact hC q o' pc'' v'' h
      · rw [ev_step_ret C hs ha]
        intro q o' pc'' v'' h
        by_cases hq : q = p
        · subst hq; simp at h
        · simp [Function.update_of_ne hq] at h
          simpa [opsOf_append] using hC q o' pc'' v'' h
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · rw [ev_crash_of_none C hs]; exact hC
    · rw [ev_crash_of_some C hs]
      intro q o' pc'' v'' h
      by_cases hq : q = p
      · subst hq; simp at h; simp only [N_append, N_crash_rec, List.append_nil]
        rw [← h.1]; exact hC q o pc v hs
      · simp [Function.update_of_ne hq] at h
        simpa using hC q o' pc'' v'' h

lemma pendOp_run (es : List (Ev P O)) : PendOp (A.init.run es) := by
  suffices ∀ C : A.Cfg, PendOp C → PendOp (C.run es) from this _ pendOp_init
  induction es with
  | nil => intro C h; exact h
  | cons e es ih => intro C h; exact ih _ (h.ev e)

/-- In a configuration satisfying the invariants, the running operation of `p` is the operation
of its current instance, which has not completed. -/
lemma opOf_curOp {C : A.Cfg} (hw : WFInv C) (hp : PendOp C) {p : P} {o : O.Op} {pc : A.PC}
    {v : A.V} (h : C.st p = some (o, pc, v)) :
    opOf (N C.hist) (curOp (N C.hist) p) = some o ∧ ¬ Completed (N C.hist) (curOp (N C.hist) p) := by
  have hl := hw.pend p
  simp only [h, Option.isSome_some, ↓reduceIte] at hl
  refine ⟨?_, by simp [Completed]⟩
  have := hp p o pc v h
  rw [List.getLast?_eq_getElem?] at this
  simpa [opOf, hl] using this

end Cslib.SharedMemory.NRL.Alg

namespace Cslib.SharedMemory

open List

section Reg

variable {V : Type} {v₀ : V} {K : Type}

-- CSLib candidate (LinPoints.lean)
/-- The entry `(x, o)` occurs in `L` immediately followed by a write. -/
def FW (L : List (K × RWOp V)) (x : K) (o : RWOp V) : Prop :=
  ∃ L₁ y w L₂, L = L₁ ++ (x, o) :: (y, RWOp.write w) :: L₂

lemma FW.append {L : List (K × RWOp V)} {x : K} {o : RWOp V} (h : FW L x o)
    (M : List (K × RWOp V)) : FW (L ++ M) x o := by
  obtain ⟨L₁, y, w, L₂, rfl⟩ := h
  exact ⟨L₁, y, w, L₂ ++ M, by simp⟩

lemma FW.cons {L : List (K × RWOp V)} {x : K} {o : RWOp V} (h : FW L x o) (a : K × RWOp V) :
    FW (a :: L) x o := by
  obtain ⟨L₁, y, w, L₂, rfl⟩ := h
  exact ⟨a :: L₁, y, w, L₂, by simp⟩

/-- Erasing an entry that is followed by a write keeps the other entries followed by writes. -/
lemma FW.erase_absorbed {A B : List (K × RWOp V)} {z y : K} {oz : RWOp V} {w : V} {x : K}
    {o : RWOp V} (h : FW (A ++ (z, oz) :: (y, .write w) :: B) x o) (hxz : x ≠ z) :
    FW (A ++ (y, .write w) :: B) x o := by
  obtain ⟨L₁, y₁, w₁, L₂, h⟩ := h
  induction A generalizing L₁ with
  | nil =>
    rcases L₁ with _ | ⟨a, L₁⟩
    · simp only [nil_append, cons.injEq, Prod.mk.injEq] at h; exact absurd h.1.1.symm hxz
    · simp only [nil_append, cons_append, cons.injEq] at h
      exact ⟨L₁, y₁, w₁, L₂, by rw [h.2.symm]; rfl⟩
  | cons a A ih =>
    rcases L₁ with _ | ⟨c, L₁⟩
    · simp only [nil_append, cons_append, cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rcases A with _ | ⟨b, A⟩
      · simp only [nil_append, cons.injEq] at h
        exact ⟨[], y, w, B, rfl⟩
      · simp only [cons_append, cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨[], y₁, w₁, A ++ (y, .write w) :: B, rfl⟩
    · simp only [cons_append, cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact (ih L₁ h).cons _

/-- Erasing a read entry keeps the other entries followed by writes. -/
lemma FW.erase_read {A B : List (K × RWOp V)} {z : K} {x : K} {o : RWOp V}
    (h : FW (A ++ (z, .read) :: B) x o) (hxz : x ≠ z) : FW (A ++ B) x o := by
  obtain ⟨L₁, y₁, w₁, L₂, h⟩ := h
  induction A generalizing L₁ with
  | nil =>
    rcases L₁ with _ | ⟨a, L₁⟩
    · simp only [nil_append, cons.injEq, Prod.mk.injEq] at h; exact absurd h.1.1.symm hxz
    · simp only [nil_append, cons_append, cons.injEq] at h
      exact ⟨L₁, y₁, w₁, L₂, by simp [h.2]⟩
  | cons a A ih =>
    rcases L₁ with _ | ⟨c, L₁⟩
    · simp only [nil_append, cons_append, cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rcases A with _ | ⟨b, A⟩
      · simp at h
      · simp only [cons_append, cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨[], y₁, w₁, A ++ B, rfl⟩
    · simp only [cons_append, cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact (ih L₁ h).cons _

variable [DecidableEq K]

lemma respIn_erase_absorbed (q : V) (A B : List (K × RWOp V)) {z y k : K} (oz : RWOp V) (w : V)
    (hk : k ≠ z) :
    (register V v₀).respIn q (A ++ (z, oz) :: (y, .write w) :: B) k =
      (register V v₀).respIn q (A ++ (y, .write w) :: B) k := by
  by_cases hA : k ∈ A.map Prod.fst
  · rw [ObjSpec.respIn_append_of_mem hA, ObjSpec.respIn_append_of_mem hA]
  · rw [ObjSpec.respIn_append_of_not_mem hA, ObjSpec.respIn_append_of_not_mem hA,
      ObjSpec.respIn_cons_of_ne _ _ _ (Ne.symm hk)]
    by_cases hy : y = k
    · subst hy; cases oz <;> rfl
    · rw [ObjSpec.respIn_cons_of_ne _ _ _ hy, ObjSpec.respIn_cons_of_ne _ _ _ hy]

omit [DecidableEq K] in
lemma runOps_erase_absorbed (q : V) (A B : List (K × RWOp V)) {z y : K} (oz : RWOp V) (w : V) :
    (register V v₀).runOps q ((A ++ (z, oz) :: (y, .write w) :: B).map Prod.snd) =
      (register V v₀).runOps q ((A ++ (y, .write w) :: B).map Prod.snd) := by
  simp only [map_append, map_cons]; rw [ObjSpec.runOps_append, ObjSpec.runOps_append]
  cases oz <;> rfl

omit [DecidableEq K] in
lemma runOps_erase_read (q : V) (A B : List (K × RWOp V)) {z : K} :
    (register V v₀).runOps q ((A ++ (z, .read) :: B).map Prod.snd) =
      (register V v₀).runOps q ((A ++ B).map Prod.snd) := by
  simp only [map_append, map_cons]; rw [ObjSpec.runOps_append, ObjSpec.runOps_append]; rfl

/-- A write entry gets its own argument as response. -/
lemma respIn_write {L : List (K × RWOp V)} {x : K} {v : V} (q : V)
    (hop : ∀ y ∈ L, y.1 = x → y.2 = .write v) (hx : x ∈ L.map Prod.fst) :
    (register V v₀).respIn q L x = some v := by
  induction L generalizing q with
  | nil => simp at hx
  | cons a L ih =>
    obtain ⟨y, o⟩ := a
    by_cases hy : y = x
    · subst hy
      have := hop _ mem_cons_self rfl
      simp only at this; subst this; rw [ObjSpec.respIn_cons_self]
    · rw [ObjSpec.respIn_cons_of_ne _ _ _ hy]
      exact ih _ (fun z hz => hop z (mem_cons_of_mem _ hz))
        (by simp only [map_cons, mem_cons] at hx; rcases hx with h | h
            · exact absurd h.symm hy
            · exact h)

omit [DecidableEq K] in
lemma runOps_concat_write (q : V) (L : List (K × RWOp V)) (y : K) (w : V) :
    (register V v₀).runOps q ((L ++ [(y, RWOp.write w)]).map Prod.snd) = w := by
  simp only [map_append, map_cons, map_nil]; rw [ObjSpec.runOps_append]; rfl

omit [DecidableEq K] in
lemma runOps_concat_read (q : V) (L : List (K × RWOp V)) (y : K) :
    (register V v₀).runOps q ((L ++ [(y, RWOp.read)]).map Prod.snd) =
      (register V v₀).runOps q (L.map Prod.snd) := by
  simp only [map_append, map_cons, map_nil]; rw [ObjSpec.runOps_append]; rfl

omit [DecidableEq K] in
lemma mem_erase_middle {l₁ l₂ : List K} {x k : K} (h : (l₁ ++ x :: l₂).Nodup) :
    k ∈ l₁ ++ l₂ ↔ k ∈ l₁ ++ x :: l₂ ∧ k ≠ x := by
  have hx : x ∉ l₁ ++ l₂ := (nodup_cons.1 (nodup_middle.1 h)).1
  constructor
  · intro hk; refine ⟨?_, fun h => hx (h ▸ hk)⟩
    simp only [mem_append, mem_cons] at hk ⊢; tauto
  · rintro ⟨hk, hkx⟩; simp only [mem_append, mem_cons] at hk ⊢; tauto

variable {P : Type} [DecidableEq P]

/-- Retracting a pending entry of a register linearization: a read, or an entry immediately
followed by a write. -/
lemma IsLinearization.retract {α : List (Label P (register V v₀))} {L : List (OpId P × RWOp V)}
    (hL : IsLinearization α L) {x : OpId P} {o : RWOp V} (hxc : ¬ Completed α x)
    (hx : x ∈ L.map Prod.fst) (hph : o = .read ∨ FW L x o) (hox : opOf α x = some o) :
    ∃ L', IsLinearization α L' ∧
      (register V v₀).runOps v₀ (L'.map Prod.snd) = (register V v₀).runOps v₀ (L.map Prod.snd) ∧
      (∀ k, k ∈ L'.map Prod.fst ↔ k ∈ L.map Prod.fst ∧ k ≠ x) ∧
      (∀ k, k ≠ x → (register V v₀).respIn v₀ L' k = (register V v₀).respIn v₀ L k) ∧
      (∀ k o', k ≠ x → FW L k o' → FW L' k o') := by
  rcases hph with rfl | ⟨L₁, y, w, L₂, rfl⟩
  · obtain ⟨⟨x', o'⟩, he, rfl⟩ := mem_map.1 hx
    obtain ⟨L₁, L₂, rfl⟩ := mem_iff_append.1 he
    have ho' : o' = .read := by
      have := hL.op_eq _ he; rw [hox] at this; exact (Option.some.inj this).symm
    subst ho'
    have hnd := hL.nodup
    simp only [map_append, map_cons] at hnd
    refine ⟨L₁ ++ L₂, hL.erase_ro hxc rfl, (runOps_erase_read _ _ _).symm, ?_, ?_, ?_⟩
    · intro k; simp only [map_append, map_cons]; exact mem_erase_middle hnd
    · intro k hk; exact (ObjSpec.respIn_insert _ _ _ rfl (Ne.symm hk)).symm
    · intro k o' hk h; exact h.erase_read hk
  · have hnd := hL.nodup
    simp only [map_append, map_cons] at hnd
    refine ⟨L₁ ++ (y, .write w) :: L₂, hL.erase_absorbed hxc (by cases o <;> rfl),
      (runOps_erase_absorbed _ _ _ _ _).symm, ?_, ?_, ?_⟩
    · intro k
      have := mem_erase_middle (k := k) hnd
      simp only [map_append, map_cons] at this ⊢; exact this
    · intro k hk; exact (respIn_erase_absorbed _ _ _ _ _ hk).symm
    · intro k o' hk h; exact h.erase_absorbed hk

-- CSLib candidate (LinPoints.lean)
/-- A read or write that returns a value different from the starting state is preceded by a write
of that value. -/
lemma respIn_exists_write {V K : Type} [DecidableEq K] {v₀ : V} {l : List (K × RWOp V)} {s w : V}
    {k : K} (h : (register V v₀).respIn s l k = some w) (hs : s ≠ w) :
    ∃ y ∈ l, y.2 = .write w := by
  induction l generalizing s with
  | nil => cases h
  | cons a l ih =>
    obtain ⟨y, o⟩ := a
    by_cases hy : y = k
    · subst hy
      rw [ObjSpec.respIn_cons_self] at h
      cases o with
      | read => exact absurd (Option.some.inj h) hs
      | write u => exact ⟨(y, .write u), by simp, by simpa using Option.some.inj h⟩
    · rw [ObjSpec.respIn_cons_of_ne _ _ _ hy] at h
      cases o with
      | read =>
        obtain ⟨z, hz, hz'⟩ := ih h hs; exact ⟨z, List.mem_cons_of_mem _ hz, hz'⟩
      | write u =>
        by_cases hu : u = w
        · subst hu; exact ⟨(y, .write u), by simp, rfl⟩
        · obtain ⟨z, hz, hz'⟩ := ih h hu; exact ⟨z, List.mem_cons_of_mem _ hz, hz'⟩

end Reg

end Cslib.SharedMemory
