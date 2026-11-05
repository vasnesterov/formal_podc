import Papers.PODC2013.ConstantBarriersMutex.Starvation
import Papers.PODC2013.ConstantBarriersMutex.BoundedWaiting
import Papers.PODC2013.ConstantBarriersMutex.RMRMain
import Papers.PODC2013.ConstantBarriersMutex.Lemma2Literal

/-!
# Theorem 1 of Attiya, Hendler, Levy (PODC 2013)

"Algorithm 1 satisfies mutual exclusion, starvation-freedom and `(log n + 3)`-bounded waiting
under TSO. Each passage of the algorithm incurs `O(log n)` RMRs and a constant number of
barriers."

Here `n = 2^h` processes, `log n = h`; Algorithm 1 under TSO is modelled in `Model.lean`.
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- **Theorem 1 of [AHL13].** Algorithm 1 under TSO, for `n = 2^h` processes:
1. mutual exclusion (every reachable configuration);
2. starvation freedom (every fair execution);
3. `(log n + 3)`-bounded waiting (every execution): while `p` is in its waiting section, any other
   process enters the critical section at most `h + 3` times (`lemma8` gives `h + 2`);
4. every passage (or part of one) incurs at most `19 log n + 23` RMRs (CC model) and completes at
   most two barriers. -/
theorem theorem1 :
    (∀ s : Cfg h, Reachable s → ∀ p q, s.pc p = .cs → s.pc q = .cs → p = q) ∧
    (∀ r : Run h, r.Fair → ∀ p T, ((r.s T).pc p).Entry → ∃ t ≥ T, (r.s t).pc p = .cs) ∧
    (∀ r : Run h, ∀ p q, p ≠ q → ∀ t₁ t₂, (∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Waiting) →
      ((Finset.Ico t₁ t₂).filter
        (fun t => (r.s t).pc q ≠ .cs ∧ (r.s (t + 1)).pc q = .cs)).card ≤ h + 3) ∧
    (∀ r : Run h, ∀ p t₁ t₂, r.WithinPassage p t₁ t₂ →
      r.rmr p t₁ t₂ ≤ 19 * h + 23 ∧ r.barriers p t₁ t₂ ≤ 2) :=
  ⟨fun _ hs _ _ hp hq => mutual_exclusion hs hp hq,
   fun _ hf _ _ hE => Run.starvation_freedom hf hE,
   fun r _ _ hpq _ _ hW => lemma8_log_n_add_three r hpq hW,
   fun r p _ _ hw => ⟨lemma10_rmr r p hw, lemma10_barriers_le r p hw⟩⟩

end Podc.ConstantBarriersMutex

namespace Podc.ConstantBarriersMutex

/-! ### Non-vacuity: fair executions exist -/

/-- Round-robin schedule: at time `t`, process `t mod 2^h` takes a step. -/
def rrEv (h : ℕ) (t : ℕ) : Ev h := .step ⟨t % 2 ^ h, Nat.mod_lt _ (by positivity)⟩

/-- Configurations of the round-robin execution. -/
def rrCfg (h : ℕ) : ℕ → Cfg h
  | 0 => Cfg.init
  | t + 1 => (rrCfg h t).next (rrEv h t)

/-- The round-robin execution. -/
def rrRun (h : ℕ) : Run h where
  ev := rrEv h
  s := rrCfg h
  init := rfl
  step _ := rfl

/-- The round-robin execution is fair, so the hypothesis of `Run.starvation_freedom` is
satisfiable. -/
theorem rrRun_fair (h : ℕ) : (rrRun h).Fair := by
  intro p T _
  refine ⟨T * 2 ^ h + p.val, ?_, ?_⟩
  · have : 1 ≤ 2 ^ h := Nat.one_le_two_pow; nlinarith
  · simp only [rrRun, rrEv]
    congr 1; ext; simp [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt p.isLt]

end Podc.ConstantBarriersMutex
