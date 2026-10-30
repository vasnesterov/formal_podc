import Papers.PODC2020.RecoverableMutexRMR.Spec

/-!
# Lemma 2.1 (19) needs fairness

Lemma 2.1 (19): "Suppose there are only finitely many crashes. For every `p` and every
`w ∈ ℤ⁺`, if `W[p]` contains `(w, true)` at some time `t`, then `Token` contains `w` at some time
`t' > t`." Lemma 2.1 is stated for "any run `E`", but (19) only holds in runs where the
processes outside the remainder section keep taking steps (the fairness assumption of
deadlock-freedom). Counterexample with two processes and no crash: process `false` obtains
ticket 1 and grants it to itself (`W[false] = (1, true)`), then stops taking steps; process
`true` obtains ticket 2 and busy-waits forever. `Token` stays `0`.

The same remark applies to Lemmas 2.4–2.6 (they are used only under fairness, where they hold;
see `Liveness*.lean`).
-/

namespace Podc.RecoverableMutexRMR

namespace Lemma2_1_19

/-- The schedule of the counterexample. -/
def sched (t : ℕ) : Ev Bool := if t < 14 then .step false else .step true

lemma at28 : (exec sched 14).W false = (1, true) ∧ (exec sched 28).pc true = .w31 2 ∧
    (exec sched 28).W true = (2, false) ∧ (exec sched 28).T = 0 := by
  decide

lemma T_le28 (t : ℕ) (ht : t ≤ 28) : (exec sched t).T = 0 := by
  interval_cases t <;> decide

/-- A busy-waiting step that does not succeed changes nothing. -/
lemma spin_step {P : Type} [DecidableEq P] (s : Cfg P) (p : P) (w : ℕ) (h : s.pc p = .w31 w)
    (hW : s.W p ≠ (w, true)) : s.step p = s := by
  simp only [Cfg.step, h, hW, if_false, Cfg.setPc]
  rw [← h, Function.update_eq_self]

lemma const (k : ℕ) : exec sched (28 + k) = exec sched 28 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 28 + (k + 1) = (28 + k) + 1 from rfl, exec_succ, ih]
    have he : sched (28 + k) = .step true := by simp [sched]; omega
    rw [he, Cfg.next]
    exact spin_step _ true 2 at28.2.1 (by rw [at28.2.2.1]; decide)

/-- **Lemma 2.1 (19) fails without fairness**: there is a crash-free execution in which
`W[false] = (1, true)` at time 14 but `Token` never contains 1. -/
theorem lemma2_1_19_false :
    FinCrashes sched ∧ (exec sched 14).W false = (1, true) ∧ ∀ t, (exec sched t).T ≠ 1 := by
  refine ⟨⟨0, fun t _ p h => by simp [sched] at h; split_ifs at h⟩, at28.1, fun t => ?_⟩
  by_cases ht : t ≤ 28
  · rw [T_le28 t ht]; decide
  · obtain ⟨k, rfl⟩ : ∃ k, t = 28 + k := ⟨t - 28, by omega⟩
    rw [const k, at28.2.2.2]; decide

end Lemma2_1_19

end Podc.RecoverableMutexRMR
