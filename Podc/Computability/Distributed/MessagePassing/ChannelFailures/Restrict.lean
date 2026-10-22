import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Model

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/ChannelFailures/Restrict.lean

/-!
# Restricting executions to a closed set of processes

The indistinguishability tool of the lower bounds. Two configurations *agree on* `X` if the
processes of `X` have the same local states and pending operations and the channels inside `X`
have the same contents (`Agree`). If no event of `E` delivers a message into `X` from outside `X`,
then running only the events of `X` (`E.filter (owner ∈ X)`) from an agreeing configuration ends in
an agreeing configuration, with the history of `E` restricted to `X` (`agree_run_filter`).
-/

namespace Cslib.ChannelFailures

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} {M L : Type} [DecidableEq P]

/-- `Cs` and `Ct` agree on `X`: local states and pending operations of `X`, channels inside `X`. -/
def Agree (X : Set P) (Cs Ct : Config P A M L) : Prop :=
  (∀ p ∈ X, Cs.loc p = Ct.loc p ∧ Cs.pend p = Ct.pend p) ∧
    ∀ q ∈ X, ∀ p ∈ X, Cs.chan q p = Ct.chan q p

namespace Agree

variable {X Y : Set P} {C C₁ C₂ C₃ : Config P A M L}

omit [DecidableEq P] in
lemma refl (C : Config P A M L) : Agree X C C := ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl⟩

omit [DecidableEq P] in
lemma symm (h : Agree X C₁ C₂) : Agree X C₂ C₁ :=
  ⟨fun p hp => ⟨(h.1 p hp).1.symm, (h.1 p hp).2.symm⟩, fun q hq p hp => (h.2 q hq p hp).symm⟩

omit [DecidableEq P] in
lemma trans (h₁ : Agree X C₁ C₂) (h₂ : Agree X C₂ C₃) : Agree X C₁ C₃ :=
  ⟨fun p hp => ⟨(h₁.1 p hp).1.trans (h₂.1 p hp).1, (h₁.1 p hp).2.trans (h₂.1 p hp).2⟩,
    fun q hq p hp => (h₁.2 q hq p hp).trans (h₂.2 q hq p hp)⟩

omit [DecidableEq P] in
lemma mono (h : Agree X C₁ C₂) (hYX : Y ⊆ X) : Agree Y C₁ C₂ :=
  ⟨fun p hp => h.1 p (hYX hp), fun q hq p hp => h.2 q (hYX hq) p (hYX hp)⟩

end Agree

section Steps

variable {X : Set P} {Cs Ct : Config P A M L}

lemma agree_apply_apply (h : Agree X Cs Ct) {p : P} (hp : p ∈ X)
    (r : L × List (P × M) × Option A.Resp) : Agree X (Cs.apply p r).1 (Ct.apply p r).1 := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · simp only [Config.apply]
    by_cases hap : a = p
    · subst hap; simp [(h.1 a ha).2]
    · simp [Function.update_of_ne hap, h.1 a ha]
  · simp only [Config.apply]
    rw [h.2 a ha b hb]

lemma apply_labels_eq (h : Agree X Cs Ct) {p : P} (hp : p ∈ X)
    (r : L × List (P × M) × Option A.Resp) : (Cs.apply p r).2 = (Ct.apply p r).2 := by
  simp [Config.apply, (h.1 p hp).2]

lemma agree_apply_left (h : Agree X Cs Ct) {p : P} (hp : p ∉ X)
    (r : L × List (P × M) × Option A.Resp) : Agree X (Cs.apply p r).1 Ct := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · have hap : a ≠ p := fun e => hp (e ▸ ha)
    simp [Config.apply, Function.update_of_ne hap, h.1 a ha]
  · have hap : a ≠ p := fun e => hp (e ▸ ha)
    simp [Config.apply, hap, h.2 a ha b hb]

lemma agree_pop_pop (h : Agree X Cs Ct) (q p : P) (rest : List M) :
    Agree X (Cs.pop q p rest) (Ct.pop q p rest) := by
  refine ⟨fun a ha => h.1 a ha, fun a ha b hb => ?_⟩
  simp only [Config.pop]
  split_ifs
  · rfl
  · exact h.2 a ha b hb

lemma agree_pop_left (h : Agree X Cs Ct) {q p : P} (hp : p ∉ X) (rest : List M) :
    Agree X (Cs.pop q p rest) Ct := by
  refine ⟨fun a ha => h.1 a ha, fun a ha b hb => ?_⟩
  have hbp : b ≠ p := fun e => hp (e ▸ hb)
  simp only [Config.pop, hbp, and_false, ite_false]
  exact h.2 a ha b hb

variable (Alg : Algorithm P A M L)

/-- Every label produced by a step belongs to the owner of the event. -/
lemma proc_of_mem_step {C : Config P A M L} {e : Event P A} {l : Label P A}
    (hl : l ∈ (Alg.step C e).2) : l.proc = e.owner := by
  have key : ∀ (C' : Config P A M L) (p : P) (r : L × List (P × M) × Option A.Resp),
      l ∈ (C'.apply p r).2 → l.proc = p := by
    intro C' p r hl
    simp only [Config.apply] at hl
    unfold respOut at hl
    split at hl
    · simp only [List.mem_singleton] at hl; subst hl; rfl
    · simp at hl
  cases e with
  | invoke p o =>
    simp only [Algorithm.step] at hl
    split at hl
    · simp at hl
    · simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · rfl
      · exact key _ _ _ hl
  | tick p c => exact key _ _ _ hl
  | deliver q p =>
    simp only [Algorithm.step] at hl
    split at hl
    · simp at hl
    · exact key _ _ _ hl

/-- A step of a process in `X` that does not receive from outside `X` preserves agreement on `X`
and produces the same labels. -/
lemma agree_step_step (h : Agree X Cs Ct) (e : Event P A) (he : e.owner ∈ X)
    (hd : ∀ q p, e = .deliver q p → q ∈ X) :
    Agree X (Alg.step Cs e).1 (Alg.step Ct e).1 ∧ (Alg.step Cs e).2 = (Alg.step Ct e).2 := by
  cases e with
  | invoke p o =>
    simp only [Event.owner] at he
    have hl := (h.1 p he).1
    have hpd := (h.1 p he).2
    simp only [Algorithm.step, hpd, hl]
    split
    · exact ⟨h, rfl⟩
    · have h' : Agree X ({ Cs with pend := Function.update Cs.pend p (some o) } : Config P A M L)
          { Ct with pend := Function.update Ct.pend p (some o) } := by
        refine ⟨fun a ha => ?_, fun a ha b hb => h.2 a ha b hb⟩
        by_cases hap : a = p
        · subst hap; simp [hl]
        · simp [Function.update_of_ne hap, h.1 a ha]
      exact ⟨agree_apply_apply h' he _, by rw [apply_labels_eq h' he]⟩
  | tick p c =>
    simp only [Event.owner] at he
    simp only [Algorithm.step, (h.1 p he).1]
    exact ⟨agree_apply_apply h he _, apply_labels_eq h he _⟩
  | deliver q p =>
    simp only [Event.owner] at he
    have hq := hd q p rfl
    simp only [Algorithm.step, h.2 q hq p he, (h.1 p he).1]
    split
    · exact ⟨h, rfl⟩
    · rename_i rest _
      have h' := agree_pop_pop h q p rest
      exact ⟨agree_apply_apply h' he _, apply_labels_eq h' he _⟩

/-- A step of a process outside `X` preserves agreement on `X`. -/
lemma agree_step_left (h : Agree X Cs Ct) (e : Event P A) (he : e.owner ∉ X) :
    Agree X (Alg.step Cs e).1 Ct := by
  cases e with
  | invoke p o =>
    simp only [Event.owner] at he
    simp only [Algorithm.step]
    split
    · exact h
    · have h' : Agree X ({ Cs with pend := Function.update Cs.pend p (some o) } : Config P A M L)
          Ct := by
        refine ⟨fun a ha => ?_, fun a ha b hb => h.2 a ha b hb⟩
        have hap : a ≠ p := fun e => he (e ▸ ha)
        simp [Function.update_of_ne hap, h.1 a ha]
      exact agree_apply_left h' he _
  | tick p c => exact agree_apply_left h he _
  | deliver q p =>
    simp only [Event.owner] at he
    simp only [Algorithm.step]
    split
    · exact h
    · exact agree_apply_left (agree_pop_left h he _) he _

end Steps

variable (Alg : Algorithm P A M L)

/-- **Restriction lemma.** If no event of `E` delivers a message into `X` from outside `X`, then
running only the events of processes in `X` from a configuration agreeing on `X` ends in a
configuration agreeing on `X`, and produces the history of `E` restricted to `X`. -/
theorem agree_run_filter (X : Set P) [DecidablePred (· ∈ X)] (E : List (Event P A))
    (hE : ∀ q p, Event.deliver q p ∈ E → p ∈ X → q ∈ X) {Cs Ct : Config P A M L}
    (h : Agree X Cs Ct) :
    Agree X (Alg.run Cs E) (Alg.run Ct (E.filter fun e => decide (e.owner ∈ X))) ∧
      Alg.hist Ct (E.filter fun e => decide (e.owner ∈ X)) =
        (Alg.hist Cs E).filter fun l => decide (l.proc ∈ X) := by
  induction E generalizing Cs Ct with
  | nil => exact ⟨h, rfl⟩
  | cons e E ih =>
    have hE' : ∀ q p, Event.deliver q p ∈ E → p ∈ X → q ∈ X :=
      fun q p hm hp => hE q p (List.mem_cons_of_mem _ hm) hp
    by_cases he : e.owner ∈ X
    · have hd : ∀ q p, e = .deliver q p → q ∈ X := by
        intro q p hqp
        subst hqp
        exact hE q p (List.mem_cons_self) he
      obtain ⟨h1, h2⟩ := agree_step_step Alg h e he hd
      obtain ⟨ih1, ih2⟩ := ih hE' h1
      refine ⟨by simpa [List.filter_cons, he] using ih1, ?_⟩
      simp only [List.filter_cons, he, decide_true, ite_true, Algorithm.hist_cons, ih2,
        List.filter_append]
      congr 1
      rw [h2]; symm; rw [List.filter_eq_self]
      intro l hl
      simpa [proc_of_mem_step Alg hl] using he
    · have h1 := agree_step_left Alg h e he
      obtain ⟨ih1, ih2⟩ := ih hE' h1
      refine ⟨by simpa [List.filter_cons, he] using ih1, ?_⟩
      simp only [List.filter_cons, he, decide_false, Bool.false_eq_true, ite_false,
        Algorithm.hist_cons, ih2, List.filter_append]
      symm
      convert List.nil_append _
      rw [List.filter_eq_nil_iff]
      intro l hl
      simpa [proc_of_mem_step Alg hl] using he

end Cslib.ChannelFailures
