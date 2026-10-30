import Papers.PODC2020.RecoverableMutexRMR.Invariant
import Papers.PODC2020.RecoverableMutexRMR.LivenessFinal

/-!
# Starvation freedom of the Chan–Woelfel algorithm (Lemma 2.13)

In a fair execution with finitely many crashes, every process is infinitely often in the
remainder or the critical section (`eventually_rem_or_cs`). Consequently, after its last crash,
a process executing `Enter()` enters the critical section (`enter_reaches_cs`), a process
executing `Exit()` returns to the remainder section (`exit_reaches_rem`), and a process
executing `Recover()` leaves it (`recover_terminates`).

The proof (files `Liveness*.lean`):

1. `LivenessTrace.exists_no_new_skip`: after the last crash, eventually no ticket gets skipped
   (at most `2 · #crashes` tickets are ever skipped, potential `Ψ`).
2. `LivenessTrace.stuck`: a process avoiding the remainder and critical sections is eventually
   stuck at line 31 forever (lexicographic measure of `LivenessMeasure.lean`; back edges of the
   program are paid for by skipped tickets and by tickets beyond `Token`).
3. Its ticket `w` bounds `Token < w`, so `Token` becomes constant, nobody is in the critical
   section any more (`no_cs`, via `progress`), and calls of `Move_Token()` stop (`calls_stop`).
4. The last call of `Move_Token()` (Lemma 2.5 of the paper) leads to a contradiction
   (`last_call_false`).
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

/-- **Lemma 2.13 of [Chan–Woelfel, PODC 2020] (starvation freedom).** In a fair execution with
finitely many crashes, every process is in the remainder or the critical section at
arbitrarily late times. -/
theorem eventually_rem_or_cs (e : ℕ → Ev P) (hF : Fair e) (hC : FinCrashes e) (p : P) (t : ℕ) :
    ∃ t', t ≤ t' ∧ ((exec e t').pc p = .rem ∨ (exec e t').pc p = .cs) :=
  Live.eventually_rem_or_cs_of_inv (inv_exec e) hF hC p t

/-- Starvation freedom for `Enter()`: a process executing `Enter()` that does not crash any
more eventually enters the critical section. -/
theorem enter_reaches_cs (e : ℕ → Ev P) (hF : Fair e) (hC : FinCrashes e) {p : P} {t : ℕ}
    (hE : ((exec e t).pc p).IsEnter) (hp : ∀ t', t ≤ t' → e t' ≠ .crash p) :
    ∃ t', t ≤ t' ∧ (exec e t').pc p = .cs :=
  Live.enter_reaches_cs_of_inv (inv_exec e) hF hC hE hp

/-- Wait-freedom of `Exit()` under fairness: a process executing `Exit()` that does not crash any
more eventually returns to the remainder section. -/
theorem exit_reaches_rem (e : ℕ → Ev P) (hF : Fair e) (hC : FinCrashes e) {p : P} {t : ℕ}
    (hE : ((exec e t).pc p).IsExit) (hp : ∀ t', t ≤ t' → e t' ≠ .crash p) :
    ∃ t', t ≤ t' ∧ (exec e t').pc p = .rem :=
  Live.exit_reaches_rem_of_inv (inv_exec e) hF hC hE hp

/-- A process executing `Recover()` eventually leaves it. -/
theorem recover_terminates (e : ℕ → Ev P) (hF : Fair e) (hC : FinCrashes e) (p : P) (t : ℕ) :
    ∃ t', t ≤ t' ∧ ¬ ((exec e t').pc p).IsRecover :=
  Live.recover_terminates_of_inv (inv_exec e) hF hC p t

end Podc.RecoverableMutexRMR
