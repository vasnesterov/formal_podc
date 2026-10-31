import Papers.PODC2022.BluntingAdversary.Model

/-!
# Unfolding lemmas for the moves of `sys Pr O`
-/

set_option linter.unusedSectionVars false

namespace Podc.BluntingAdversary

open Cslib.SharedMemory
open scoped Classical

variable {P : Type} [DecidableEq P] {A : ObjSpec} {C L M : Type}
  (Pr : Program P A C) (O : ObjSem P A L M) (s : Cfg P C L M) (p : P)

section Client

variable (hb : s.busy p = false)
include hb

lemma move_loc {c : C} (h : Pr.next p (s.cl p) = .loc c) :
    (sys Pr O).move s p = .det { s with cl := Function.update s.cl p c } := by
  simp [sys, sysMove, hb, h]

lemma move_rnd {m : ℕ} {g : Fin (m + 1) → C} (h : Pr.next p (s.cl p) = .rnd m g) :
    (sys Pr O).move s p = .rand m fun i =>
      { s with cl := Function.update s.cl p (g i), coins := s.coins + 1,
               badCoin := s.badCoin || decide (s.inPreamble O) } := by
  simp [sys, sysMove, hb, h]

lemma move_call_inl {o : A.Op} {κ : A.Resp → C} {l : L} {m : M}
    (h : Pr.next p (s.cl p) = .call o κ) (hc : O.call p (s.lo p) o s.mem s.coins = .inl (l, m)) :
    (sys Pr O).move s p = .det { s with busy := Function.update s.busy p true,
                                        lo := Function.update s.lo p l, mem := m } := by
  simp [sys, sysMove, hb, h, hc]

lemma move_call_inr {o : A.Op} {κ : A.Resp → C} {r : A.Resp} {l : L} {m : M}
    (h : Pr.next p (s.cl p) = .call o κ) (hc : O.call p (s.lo p) o s.mem s.coins = .inr (r, l, m)) :
    (sys Pr O).move s p = .det { s with cl := Function.update s.cl p (κ r),
                                        lo := Function.update s.lo p l, mem := m } := by
  simp [sys, sysMove, hb, h, hc]

lemma move_done (h : Pr.next p (s.cl p) = .done) : (sys Pr O).move s p = .stop := by
  simp [sys, sysMove, hb, h]

end Client

section Busy

variable (hb : s.busy p = true)
include hb

lemma move_step {l : L} {m : M} (h : O.act p (s.lo p) s.mem s.coins = .step l m) :
    (sys Pr O).move s p = .det { s with lo := Function.update s.lo p l, mem := m } := by
  simp [sys, sysMove, hb, h]

lemma move_orand {n : ℕ} {g : Fin (n + 1) → L} (h : O.act p (s.lo p) s.mem s.coins = .rand n g) :
    (sys Pr O).move s p = .rand n fun i => { s with lo := Function.update s.lo p (g i) } := by
  simp [sys, sysMove, hb, h]

lemma move_ret {r : A.Resp} {l : L} {o : A.Op} {κ : A.Resp → C}
    (h : O.act p (s.lo p) s.mem s.coins = .ret r l) (hc : Pr.next p (s.cl p) = .call o κ) :
    (sys Pr O).move s p = .det { s with cl := Function.update s.cl p (κ r),
                                        busy := Function.update s.busy p false,
                                        lo := Function.update s.lo p l } := by
  simp [sys, sysMove, hb, h, hc]

end Busy

/-- Terminal configurations: every process is idle and done (given that busy processes are
always at a call instruction). -/
lemma terminal_iff {s : Cfg P C L M}
    (hinv : ∀ q, s.busy q = true → ∃ o κ, Pr.next q (s.cl q) = .call o κ) :
    (sys Pr O).Terminal s ↔ ∀ q, s.busy q = false ∧ Pr.next q (s.cl q) = .done := by
  constructor
  · intro ht q
    have hq := ht q
    cases hb : s.busy q
    · refine ⟨rfl, ?_⟩
      cases hn : Pr.next q (s.cl q) with
      | loc c => rw [move_loc Pr O s q hb hn] at hq; cases hq
      | rnd m g => rw [move_rnd Pr O s q hb hn] at hq; cases hq
      | call o κ =>
        cases hc : O.call q (s.lo q) o s.mem s.coins with
        | inl lm => rw [move_call_inl Pr O s q hb hn hc] at hq; cases hq
        | inr rlm =>
          obtain ⟨r, l, m⟩ := rlm
          rw [move_call_inr Pr O s q hb hn hc] at hq; cases hq
      | done => rfl
    · exfalso
      obtain ⟨o, κ, hn⟩ := hinv q hb
      cases ha : O.act q (s.lo q) s.mem s.coins with
      | step l m => rw [move_step Pr O s q hb ha] at hq; cases hq
      | rand n g => rw [move_orand Pr O s q hb ha] at hq; cases hq
      | ret r l => rw [move_ret Pr O s q hb ha hn] at hq; cases hq
  · intro h q
    exact move_done Pr O s q (h q).1 (h q).2

end Podc.BluntingAdversary
