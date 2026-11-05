import Papers.PODC2016.RWLockRMRTradeoff.Awareness

/-!
# Lemma 1 is false as stated (write-back CC model)

Lemma 1 of the paper: "Let `s` be a `C ↪ E` expanding step by some process `p`, then `p` incurs an
RMR when it executes `s`." With the paper's Definition 1 (the familiarity set of `v` is determined
by the last *non-trivial* step on `v`), this fails in the write-back protocol:

1. `q` writes `1` to `v` (non-trivial: `F(v) = {q}`);
2. `p` writes `1` to `v`: a *trivial* write, so `F(v)` stays `{q}`, but `p` now holds `v` in
   exclusive mode;
3. `p` reads `v`: it is a cache hit (no RMR), yet `AW(p)` grows from `{p}` to `{p, q}`.

The proof of Lemma 1 assumes that some process `q ≠ p` writes `v` while `p` holds a valid copy,
which is not the case here (the last non-trivial write precedes `p`'s caching step).
The counting version used by Theorem 5 (`lemma1_count`) is correct.
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

/-- Two processes and one register `v` (initially `0`): process `0` writes `1`; process `1` writes
`1` and then reads `v`. Local states are program counters. -/
def lemma1Impl : Impl mutexObj (Regs Unit ℕ 0) (Fin 2) ℕ where
  memInit _ := 0
  locInit _ := 0
  invoke _ _ _ := 0
  act p l :=
    if p = 0 then
      (if l = 0 then .access () (CASOp.write 1 : CASOp ℕ) (fun _ => 1) else .ret () 1)
    else
      (if l = 0 then .access () (CASOp.write 1 : CASOp ℕ) (fun _ => 1)
       else if l = 1 then .access () (CASOp.read : CASOp ℕ) (fun _ => 2) else .ret () 2)

/-- The execution: `q = 0` writes `1`, then `p = 1` writes `1` (trivially). -/
def lemma1Exec : List (Label (Fin 2) mutexObj) :=
  [.inv 0 .lock, .tau 0, .inv 1 .lock, .tau 1]

/-- **Lemma 1 is false** (write-back CC model, the paper's Definitions 1–3): after
`lemma1Exec` (a fragment from the initial configuration), the read of `v` by process `1` is an
expanding step that is not an RMR. -/
theorem lemma1_false :
    ∃ X : Ext lemma1Impl (writeBack (P := Fin 2) (ι := Unit)),
      xrun (Ext.init lemma1Impl writeBack) lemma1Exec = some X ∧
      (xstep X (.tau 1)).isSome ∧ Expanding X (.tau 1) ∧
      ¬ IsRMR lemma1Impl writeBack X.cfg X.cache (.tau 1) := by
  simp only [lemma1Exec, xrun_cons, xrun_nil]
  simp [xstep, Impl.step, lemma1Impl, Ext.init, Impl.initCfg]
  simp [Expanding, IsRMR, kstep, cacheStep, accessAt, accessOf, writeBack, Know.init, Label.proc]

/-- The same counterexample in the write-through protocol, when (as in `writeThrough`) a write
leaves the writer with a valid copy of the variable. -/
theorem lemma1_false_writeThrough :
    ∃ X : Ext lemma1Impl (writeThrough (P := Fin 2) (ι := Unit)),
      xrun (Ext.init lemma1Impl writeThrough) lemma1Exec = some X ∧
      (xstep X (.tau 1)).isSome ∧ Expanding X (.tau 1) ∧
      ¬ IsRMR lemma1Impl writeThrough X.cfg X.cache (.tau 1) := by
  simp only [lemma1Exec, xrun_cons, xrun_nil]
  simp [xstep, Impl.step, lemma1Impl, Ext.init, Impl.initCfg]
  simp [Expanding, IsRMR, kstep, cacheStep, accessAt, accessOf, writeThrough, Know.init, Label.proc]

end Podc.RWLockRMRTradeoff
