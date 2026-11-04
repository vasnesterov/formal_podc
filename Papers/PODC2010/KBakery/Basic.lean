import Papers.PODC2010.KBakery.Model

/-!
# Basic step lemmas for the k-Bakery model
-/

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ} {s : Cfg P} {p i q : P}

@[simp] lemma setPc_pc (s : Cfg P) (p : P) (c : PC P) : (s.setPc p c).pc = Function.update s.pc p c := rfl
@[simp] lemma setPc_want (s : Cfg P) (p : P) (c : PC P) : (s.setPc p c).want = s.want := rfl
@[simp] lemma setPc_ticket (s : Cfg P) (p : P) (c : PC P) : (s.setPc p c).ticket = s.ticket := rfl
@[simp] lemma setPc_capture (s : Cfg P) (p : P) (c : PC P) :
    (s.setPc p c).capture = s.capture := rfl

@[simp] lemma stepAt_cached : (stepAt fife k s p i).cached = updCache s.cached p (access s p i) :=
  rfl
@[simp] lemma stepAt_pc : (stepAt fife k s p i).pc = (core fife k s p i).pc := rfl
@[simp] lemma stepAt_want : (stepAt fife k s p i).want = (core fife k s p i).want := rfl
@[simp] lemma stepAt_ticket : (stepAt fife k s p i).ticket = (core fife k s p i).ticket := rfl
@[simp] lemma stepAt_capture : (stepAt fife k s p i).capture = (core fife k s p i).capture := rfl

/-- Steps of `p` do not change the program counter of another process. -/
lemma core_pc_ne (h : q ≠ p) : (core fife k s p i).pc q = s.pc q := by
  unfold core; split <;> (try split_ifs) <;> simp [Function.update_of_ne h]

lemma core_ticket_ne (h : q ≠ p) : (core fife k s p i).ticket q = s.ticket q := by
  unfold core; split <;> (try split_ifs) <;> simp [Function.update_of_ne h]

lemma core_want_ne (h : q ≠ p) : (core fife k s p i).want q = s.want q := by
  unfold core; split <;> (try split_ifs) <;> simp [Function.update_of_ne h]

lemma core_capture_ne (h : q ≠ p) : (core fife k s p i).capture q = s.capture q := by
  unfold core; split <;> (try split_ifs) <;> simp [Function.update_of_ne h]

/-- Only line 15 changes a ticket. -/
lemma core_ticket_self_of_ne_d15 (h : ∀ acc rem, s.pc p ≠ .d15 acc rem) :
    (core fife k s p i).ticket p = s.ticket p := by
  unfold core; split <;> (try split_ifs) <;> simp_all

lemma core_capture_self_of_ne_cap23 (h : ∀ rem, s.pc p ≠ .cap23 rem) :
    (core fife k s p i).capture p = s.capture p := by
  unfold core; split <;> (try split_ifs) <;> simp_all

lemma core_want_self_of (h : ∀ rem, s.pc p ≠ .d14 rem ∧ s.pc p ≠ .d16 rem ∧ s.pc p ≠ .ex rem) :
    (core fife k s p i).want p = s.want p := by
  unfold core; split <;> (try split_ifs) <;> simp_all

lemma admissible_of_not_mem (ha : Admissible s p i) (hi : i ∉ (s.pc p).rem) :
    (s.pc p).rem = ∅ := by
  rcases ha with h | h
  · exact absurd h hi
  · exact h

end Podc.KBakery
