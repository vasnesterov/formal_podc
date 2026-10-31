import Podc.Computability.Distributed.SharedMemory.NRL.Model

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/NRL/Indist.lean

/-!
# Indistinguishability in the NRL crash-recovery model

* `Agree x C D`: same shared memory and same local state of `x` — then steps and crashes of `x`
  act in the same way on `C` and `D` (`ev_step_agree`, `ev_crash_agree`, `run_agree`);
* `Equiv C D`: same memory, same local states, same responses of every process so far — then
  every execution acts in the same way (`Equiv.ev`, `Equiv.run`);
* `step_comm`: steps of two different processes that do not access the same base object
  commute up to `Equiv`.
-/

namespace Cslib.SharedMemory.NRL.Alg

open Cslib.SharedMemory

variable {P : Type} {O : ObjSpec} [DecidableEq P] {A : Alg P O}

/-- `C` and `D` look the same to `x`: same shared memory and same local state of `x`. -/
def Agree (x : P) (C D : A.Cfg) : Prop := C.mem = D.mem ∧ C.st x = D.st x

/-- Same memory, same local states and the same responses of every process so far. -/
def Equiv (C D : A.Cfg) : Prop :=
  C.mem = D.mem ∧ C.st = D.st ∧ ∀ y, respsOf (N C.hist) y = respsOf (N D.hist) y

lemma Agree.symm {x : P} {C D : A.Cfg} (h : Agree x C D) : Agree x D C := ⟨h.1.symm, h.2.symm⟩

lemma Agree.trans {x : P} {C D E : A.Cfg} (h : Agree x C D) (h' : Agree x D E) : Agree x C E :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

lemma Equiv.symm {C D : A.Cfg} (h : Equiv C D) : Equiv D C :=
  ⟨h.1.symm, h.2.1.symm, fun y => (h.2.2 y).symm⟩

/-- The configuration with the same memory and local states and an empty history. -/
def Cfg.base (C : A.Cfg) : A.Cfg := ⟨C.mem, C.st, []⟩

/-- An event depends on the configuration only through memory and local states, and appends to
the history. -/
lemma ev_spec (C : A.Cfg) (e : Ev P O) :
    (C.ev e).mem = (C.base.ev e).mem ∧ (C.ev e).st = (C.base.ev e).st ∧
      (C.ev e).hist = C.hist ++ (C.base.ev e).hist := by
  have hb : C.base.st = C.st := rfl
  rcases e with ⟨p, o⟩ | p | p
  · rcases hs : C.st p with _ | x
    · rw [ev_inv_of_none C o hs, ev_inv_of_none C.base o (by rw [hb, hs])]; simp [Cfg.base]
    · rw [ev_inv_of_some C o hs, ev_inv_of_some C.base o (by rw [hb, hs])]; simp [Cfg.base]
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · rw [ev_step_of_none C hs, ev_step_of_none C.base (by rw [hb, hs])]; simp [Cfg.base]
    · have hs' : C.base.st p = some (o, pc, v) := by rw [hb, hs]
      rcases ha : A.act p o pc v with ⟨i, op, pc', k⟩ | ⟨pc', v'⟩ | r
      · rw [ev_step_access C hs ha, ev_step_access C.base hs' ha]; simp [Cfg.base]
      · rw [ev_step_internal C hs ha, ev_step_internal C.base hs' ha]; simp [Cfg.base]
      · rw [ev_step_ret C hs ha, ev_step_ret C.base hs' ha]; simp [Cfg.base]
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · rw [ev_crash_of_none C hs, ev_crash_of_none C.base (by rw [hb, hs])]; simp [Cfg.base]
    · rw [ev_crash_of_some C hs, ev_crash_of_some C.base (by rw [hb, hs])]; simp [Cfg.base]

lemma Equiv.ev {C D : A.Cfg} (h : Equiv C D) (e : Ev P O) : Equiv (C.ev e) (D.ev e) := by
  have hb : C.base = D.base := by simp [Cfg.base, h.1, h.2.1]
  obtain ⟨c1, c2, c3⟩ := ev_spec C e
  obtain ⟨d1, d2, d3⟩ := ev_spec D e
  refine ⟨by rw [c1, d1, hb], by rw [c2, d2, hb], fun y => ?_⟩
  rw [c3, d3, hb]; simp [respsOf_append, h.2.2 y]

lemma Equiv.run {C D : A.Cfg} (h : Equiv C D) (es : List (Ev P O)) :
    Equiv (C.run es) (D.run es) := by
  induction es generalizing C D with
  | nil => exact h
  | cons e es ih => exact ih (h.ev e)

/-- A step of `x` acts in the same way on configurations that look the same to `x`. -/
lemma ev_step_agree {x : P} {C D : A.Cfg} (h : Agree x C D) :
    Agree x (C.ev (.step x)) (D.ev (.step x)) ∧
      ∃ hs, (C.ev (.step x)).hist = C.hist ++ hs ∧ (D.ev (.step x)).hist = D.hist ++ hs := by
  obtain ⟨hm, hst⟩ := h
  rcases hs : C.st x with _ | ⟨o, pc, v⟩
  · rw [ev_step_of_none C hs, ev_step_of_none D (by rw [← hst, hs])]
    exact ⟨⟨hm, hst⟩, [], by simp, by simp⟩
  · have hs' : D.st x = some (o, pc, v) := by rw [← hst, hs]
    rcases ha : A.act x o pc v with ⟨i, op, pc', k⟩ | ⟨pc', v'⟩ | r
    · rw [ev_step_access C hs ha, ev_step_access D hs' ha]
      exact ⟨⟨by simp [hm], by simp [hm]⟩, [], by simp, by simp⟩
    · rw [ev_step_internal C hs ha, ev_step_internal D hs' ha]
      exact ⟨⟨hm, by simp⟩, [], by simp, by simp⟩
    · rw [ev_step_ret C hs ha, ev_step_ret D hs' ha]
      exact ⟨⟨hm, by simp⟩, _, rfl, rfl⟩

/-- A crash of `x` acts in the same way on configurations that look the same to `x`. -/
lemma ev_crash_agree {x : P} {C D : A.Cfg} (h : Agree x C D) :
    Agree x (C.ev (.crash x)) (D.ev (.crash x)) := by
  obtain ⟨hm, hst⟩ := h
  rcases hs : C.st x with _ | ⟨o, pc, v⟩
  · rw [ev_crash_of_none C hs, ev_crash_of_none D (by rw [← hst, hs])]; exact ⟨hm, hst⟩
  · rw [ev_crash_of_some C hs, ev_crash_of_some D (by rw [← hst, hs])]
    exact ⟨hm, by simp⟩

/-- Solo steps of `x` act in the same way on configurations that look the same to `x`. -/
lemma run_agree {x : P} {C D : A.Cfg} (h : Agree x C D) (n : ℕ) :
    Agree x (C.run (List.replicate n (.step x))) (D.run (List.replicate n (.step x))) ∧
      ∃ hs, (C.run (List.replicate n (.step x))).hist = C.hist ++ hs ∧
        (D.run (List.replicate n (.step x))).hist = D.hist ++ hs := by
  induction n generalizing C D with
  | zero => exact ⟨h, [], by simp, by simp⟩
  | succ n ih =>
    obtain ⟨h1, hs, e1, e2⟩ := ev_step_agree h
    obtain ⟨h2, hs', f1, f2⟩ := ih h1
    refine ⟨by simpa [List.replicate_succ] using h2, hs ++ hs', ?_, ?_⟩
    · simp only [List.replicate_succ, Cfg.run_cons]; rw [f1, e1]; simp
    · simp only [List.replicate_succ, Cfg.run_cons]; rw [f2, e2]; simp

/-! ### Events of other processes -/

lemma ev_step_st_ne {x y : P} (hxy : x ≠ y) (C : A.Cfg) : (C.ev (.step y)).st x = C.st x := by
  rcases hs : C.st y with _ | ⟨o, pc, v⟩
  · rw [ev_step_of_none C hs]
  · rcases ha : A.act y o pc v with ⟨i, op, pc', k⟩ | ⟨pc', v'⟩ | r
    · rw [ev_step_access C hs ha]; simp [hxy]
    · rw [ev_step_internal C hs ha]; simp [hxy]
    · rw [ev_step_ret C hs ha]; simp [hxy]

lemma ev_crash_st_ne {x y : P} (hxy : x ≠ y) (C : A.Cfg) : (C.ev (.crash y)).st x = C.st x := by
  rcases hs : C.st y with _ | ⟨o, pc, v⟩
  · rw [ev_crash_of_none C hs]
  · rw [ev_crash_of_some C hs]; simp [hxy]

lemma ev_crash_mem (y : P) (C : A.Cfg) : (C.ev (.crash y)).mem = C.mem := by
  rcases hs : C.st y with _ | ⟨o, pc, v⟩
  · rw [ev_crash_of_none C hs]
  · rw [ev_crash_of_some C hs]

/-- A crash of another process is invisible to `x`. -/
lemma agree_ev_crash_ne {x y : P} (hxy : x ≠ y) (C : A.Cfg) : Agree x (C.ev (.crash y)) C :=
  ⟨ev_crash_mem y C, ev_crash_st_ne hxy C⟩

/-! ### Commuting steps -/

/-- The base object accessed by an action, if any. -/
def _root_.Cslib.SharedMemory.NRL.Act.obj {ι : Type} {T : ι → ObjSpec} {PC V R : Type} : Act T PC V R → Option ι
  | .access i _ _ _ => some i
  | _ => none

open Classical in
/-- Steps of two different processes commute (up to `Equiv`) unless both access the same base
object. -/
lemma step_comm {p q : P} (hpq : p ≠ q) (C : A.Cfg) {op oq : O.Op} {pcp pcq : A.PC}
    {vp vq : A.V} (hp : C.st p = some (op, pcp, vp)) (hq : C.st q = some (oq, pcq, vq))
    (hobj : ∀ i, (A.act p op pcp vp).obj = some i → (A.act q oq pcq vq).obj ≠ some i) :
    Equiv ((C.ev (.step p)).ev (.step q)) ((C.ev (.step q)).ev (.step p)) := by
  have hq' : (C.ev (.step p)).st q = some (oq, pcq, vq) := by rw [ev_step_st_ne (Ne.symm hpq), hq]
  have hp' : (C.ev (.step q)).st p = some (op, pcp, vp) := by rw [ev_step_st_ne hpq, hp]
  rcases hap : A.act p op pcp vp with ⟨i, a, pc₁, k₁⟩ | ⟨pc₁, v₁⟩ | r₁ <;>
  rcases haq : A.act q oq pcq vq with ⟨j, b, pc₂, k₂⟩ | ⟨pc₂, v₂⟩ | r₂ <;>
  rw [hap] at hobj <;> rw [haq] at hobj
  · have hij : i ≠ j := fun h => hobj i rfl (by simp [Act.obj, h])
    have e1 := ev_step_access C hp hap
    have e2 := ev_step_access C hq haq
    rw [e1] at hq' ⊢; rw [e2] at hp' ⊢
    rw [ev_step_access _ hq' haq, ev_step_access _ hp' hap]
    refine ⟨?_, ?_, fun y => rfl⟩ <;>
      simp only [Function.update_of_ne (Ne.symm hij), Function.update_of_ne hij]
    · exact Function.update_comm hij _ _ _
    · exact Function.update_comm hpq _ _ _
  all_goals
    first
    | rw [ev_step_access C hp hap] at hq' ⊢
    | rw [ev_step_internal C hp hap] at hq' ⊢
    | rw [ev_step_ret C hp hap] at hq' ⊢
  all_goals
    first
    | rw [ev_step_access C hq haq] at hp' ⊢
    | rw [ev_step_internal C hq haq] at hp' ⊢
    | rw [ev_step_ret C hq haq] at hp' ⊢
  all_goals
    first
    | rw [ev_step_access _ hq' haq]
    | rw [ev_step_internal _ hq' haq]
    | rw [ev_step_ret _ hq' haq]
  all_goals
    first
    | rw [ev_step_access _ hp' hap]
    | rw [ev_step_internal _ hp' hap]
    | rw [ev_step_ret _ hp' hap]
  all_goals
    refine ⟨?_, ?_, fun y => ?_⟩ <;>
      simp only [respsOf_append, N_append, List.append_assoc]
  all_goals first
    | rfl
    | exact Function.update_comm hpq _ _ _
    | skip
  all_goals
    by_cases h1 : p = y
    · subst h1; simp [N, HStep.toLabel, respsOf, hpq, Ne.symm hpq]
    · by_cases h2 : q = y
      · subst h2; simp [N, HStep.toLabel, respsOf, h1]
      · simp [N, HStep.toLabel, respsOf, h1, h2]

end Cslib.SharedMemory.NRL.Alg
