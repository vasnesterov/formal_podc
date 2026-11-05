import Podc.Computability.Distributed.SharedMemory.Arrival.Valency
import Cslib.Computability.Distributed.SharedMemory.ObjClasses

/-!
# Common lemmas for the impossibility results (Theorems 10 and 11)

Small facts about the arrival model `Cslib.SharedMemory.Arrival` used by both valency arguments:

* `Cfg.step_step_agreeOn_of_overwrites`: if `r` is poised to apply a blind overwrite to the
  object on which `s` is poised, then `s; r` and `r` are indistinguishable to `r`;
* `rw_pair`: two processes poised on the same read/write-like object whose steps lead to
  executions of opposite valencies give a contradiction (Herlihy's argument);
* `exists_fresh`: a process that has not taken a step in finitely many schedules.
-/

-- CSLib candidate: the whole file (generic lemmas for `Cslib.SharedMemory.Arrival`, Valency.lean)
namespace Podc.UnboundedConcurrency

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {P : Type} [DecidableEq P]

namespace Cfg

variable {X Y : Type} {A : Alg T P X Y}

/-- If `r` is poised to apply a blind overwrite `o` to the object `i`, on which `s ≠ r` is
poised, then after `s; r` and after `r` the memory and the local state of `r` are the same. -/
lemma step_step_agreeOn_of_overwrites (C : Cfg A) {r s : P} {i : ι} {o : (T i).Op}
    {k : (T i).Resp → A.L} (hr : A.act (C.loc r) = .access i o k) (hov : (T i).Overwrites o)
    (hs : C.Poised s i) (hrs : r ≠ s) :
    AgreeOn {r} ((C.step s).step r) (C.step r) := by
  obtain ⟨o', k', hs⟩ := hs
  have hr' : A.act ((C.step s).loc r) = .access i o k := by
    rw [Arrival.Cfg.step_loc_other C hrs]; exact hr
  rw [Arrival.Cfg.step_of_access hr', Arrival.Cfg.step_of_access hr]
  have hδ : (T i).δ ((C.step s).mem i) o = (T i).δ (C.mem i) o := hov _ _
  rw [hδ]
  refine ⟨?_, fun p hp => ?_⟩
  · rw [Arrival.Cfg.step_of_access hs]
    simp
  · simp only [Set.mem_singleton_iff] at hp; subst hp; simp

/-- Two steps of different processes on the same object whose state effects commute lead to the
same memory in both orders. -/
lemma mem_step_step_comm (C : Cfg A) {a b : P} {i : ι} {o o' : (T i).Op}
    {k k' : (T i).Resp → A.L} (ha : A.act (C.loc a) = .access i o k)
    (hb : A.act (C.loc b) = .access i o' k') (hab : a ≠ b)
    (hcomm : ((T i).δ ((T i).δ (C.mem i) o).1 o').1 = ((T i).δ ((T i).δ (C.mem i) o').1 o).1) :
    ((C.step a).step b).mem = ((C.step b).step a).mem := by
  have hb' : A.act ((C.step a).loc b) = .access i o' k' := by
    rw [Arrival.Cfg.step_loc_other C (Ne.symm hab)]; exact hb
  have ha' : A.act ((C.step b).loc a) = .access i o k := by
    rw [Arrival.Cfg.step_loc_other C hab]; exact ha
  rw [Arrival.Cfg.step_of_access hb', Arrival.Cfg.step_of_access ha',
    Arrival.Cfg.step_of_access ha, Arrival.Cfg.step_of_access hb]
  simp [hcomm]

end Cfg

/-- A process that does not occur in a given list (processes `ℕ`). -/
lemma exists_fresh (l : List ℕ) : ∃ r, r ∉ l := by
  have : ∀ a ∈ l, a ≤ l.foldr max 0 := by
    intro a ha
    induction l with
    | nil => simp at ha
    | cons b l ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.1 ha with rfl | ha
      · exact le_max_left _ _
      · exact le_trans (ih ha) (le_max_right _ _)
  exact ⟨l.foldr max 0 + 1, fun h => by have := this _ h; omega⟩

section Pair

variable {A : Alg T P Bool Bool} (hag : Agreement A (fun _ => True))
  (hwf : WaitFree A (fun s => (Set.range s).Finite))
include hag hwf

/-- A process of `Q` in a `Q`-bivalent execution is poised on some object. -/
lemma Biv.exists_access {Q : Set P} {x : P → Bool} {α : List P} (hb : Biv A Q x α) {p : P}
    (hp : p ∈ Q) : ∃ i o k, A.act ((A.exec x α).loc p) = .access i o k := by
  rcases Arrival.Cfg.out_or_poised (A.exec x α) p with ⟨v, hv⟩ | ⟨i, o, k, h⟩
  · exact absurd hv (hb.not_out hag (Or.inr hp) v)
  · exact ⟨i, o, k, h⟩

/-- **Herlihy's pair argument.** Let `α` be `Q`-bivalent, `r, s ∈ Q`, such that after `α r` only
`false` and after `α s` only `true` can be decided (by processes of `Q`). Then `r ≠ s`, and `r` and
`s` are poised on the same object, which is not read/write-like. -/
lemma rw_pair {Q : Set P} {x : P → Bool} {α : List P} (hb : Biv A Q x α) {r s : P}
    (hrQ : r ∈ Q) (hsQ : s ∈ Q)
    (hr : ¬ CanDec A Q x (α ++ [r]) true) (hs : ¬ CanDec A Q x (α ++ [s]) false) :
    r ≠ s ∧ ∃ i, (A.exec x α).Poised r i ∧ (A.exec x α).Poised s i ∧ ¬ (T i).RWLike := by
  have hrs : r ≠ s := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_canDec hwf hrQ x (α ++ [r])
    cases v
    · exact hs hv
    · exact hr hv
  refine ⟨hrs, ?_⟩
  set C := A.exec x α with hC
  have hexec1 : ∀ a b : P, A.exec x (α ++ [a] ++ [b]) = (C.step a).step b := by
    intro a b; rw [Alg.exec_concat, Alg.exec_concat]
  have hexec0 : ∀ a : P, A.exec x (α ++ [a] ++ []) = C.step a := by
    intro a; rw [List.append_nil, Alg.exec_concat]
  have hsQ' : ∀ q ∈ [s], q ∈ Q := by simp [hsQ]
  have hrQ' : ∀ q ∈ [r], q ∈ Q := by simp [hrQ]
  obtain ⟨i, o, k, hri⟩ := Biv.exists_access hag hwf hb hrQ
  obtain ⟨j, o', k', hsj⟩ := Biv.exists_access hag hwf hb hsQ
  by_cases hij : i = j
  · subst hij
    refine ⟨i, ⟨o, k, hri⟩, ⟨o', k', hsj⟩, fun hrw => ?_⟩
    rcases hrw o with hro | hov
    · have h := Arrival.Cfg.step_step_agreeOn_of_readOnly C hri (hro _) hrs
      exact false_of_agreeOn hwf hr hs hsQ' (by simp) hsQ (β := [s]) (γ := [])
        (by rw [hexec1, hexec0]; exact h)
    rcases hrw o' with hro' | hov'
    · have h := Arrival.Cfg.step_step_agreeOn_of_readOnly C hsj (hro' _) hrs.symm
      exact false_of_agreeOn hwf hr hs (by simp) hrQ' hrQ (β := []) (γ := [r])
        (by rw [hexec1, hexec0]; exact h.symm)
    · have h := Cfg.step_step_agreeOn_of_overwrites C hri hov ⟨o', k', hsj⟩ hrs
      exact false_of_agreeOn hwf hr hs (by simp) hrQ' hrQ (β := []) (γ := [r])
        (by rw [hexec1, hexec0]; exact h.symm)
  · exfalso
    have hcomm := Arrival.Cfg.step_comm C ⟨o, k, hri⟩ ⟨o', k', hsj⟩ hrs hij
    exact false_of_agreeOn hwf hr hs hsQ' hrQ' hrQ (β := [s]) (γ := [r])
      (by rw [hexec1, hexec1, hcomm]; exact AgreeOn.refl _ _)

end Pair

end Podc.UnboundedConcurrency
