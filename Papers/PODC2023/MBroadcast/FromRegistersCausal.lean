import Papers.PODC2023.MBroadcast.FromRegisters

/-!
# Algorithm 2 does not implement causal-MBroadcast

The full version claims that Algorithm 2 implements *reliable*-MBroadcast (and it implements
fifo-MBroadcast, `fifoOrdering`), but it does not implement causal-MBroadcast: with three
processes,

1. `p₂` starts a periodic `catch_up` and reads `SENT[0] = []`;
2. `p₀` invokes `mbroadcast(m₀)` (writes `SENT[0] = [m₀]`);
3. `p₁` runs a periodic `catch_up`: reads `SENT[0]`, mdelivers `m₀`, reads `SENT[2] = []`;
4. `p₁` invokes `mbroadcast(m₁)` (writes `SENT[1] = [m₁]`);
5. `p₂` continues its `catch_up` and reads `SENT[1]`: it mdelivers `m₁` from `p₁` without having
   mdelivered `m₀`, although `p₁` mdelivered `m₀` before mbroadcasting `m₁`.

(The paper does not claim causality for this algorithm; this documents that the causal variant
needs another algorithm.)
-/

namespace Podc.MBroadcast.FromRegisters

variable {n : ℕ} {M : Type} [DecidableEq M]

/-- Run a list of actions. -/
def run (c : Cfg n M) : List (Act n M) → Option (Cfg n M)
  | [] => some c
  | a :: as => (step c a).bind (run · as)

lemma Reachable.run {c c' : Cfg n M} (h : Reachable c) :
    ∀ {as : List (Act n M)}, FromRegisters.run c as = some c' → Reachable c'
  | [], hr => by cases hr; exact h
  | a :: as, hr => by
    simp only [FromRegisters.run, Option.bind_eq_some_iff] at hr
    obtain ⟨c1, h1, h2⟩ := hr
    exact (Reachable.step h h1).run h2

/-- The schedule of the counterexample (messages `m₀ = 0`, `m₁ = 1`). -/
def causalCexActs : List (Act 3 ℕ) :=
  [.tick 2, .tick 2, .invoke 0 0, .tick 1, .tick 1, .tick 1, .tick 1, .tick 1, .invoke 1 1,
    .tick 2]

/-- The MBroadcast trace of the counterexample. -/
def causalCexTrace : List (Ev (Fin 3) ℕ) :=
  [.bc 0 0, .dl 1 0 0, .bc 1 1, .dl 2 1 1]

lemma run_causalCex : (run init causalCexActs).map Cfg.log = some causalCexTrace := by
  decide

/-- **Algorithm 2 does not implement causal-MBroadcast**: a reachable configuration (three
processes, no crash) whose MBroadcast trace violates causal ordering. -/
theorem not_causalOrdering :
    ∃ c : Cfg 3 ℕ, Reachable c ∧ c.log = causalCexTrace ∧ ¬ CausalOrdering c.log := by
  have h := run_causalCex
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨c, hc, hlog⟩ := h
  refine ⟨c, Reachable.init.run hc, hlog, ?_⟩
  rw [hlog]
  intro hco
  have := hco 1 0 0 1 1 2 rfl rfl (by norm_num) 2 3 rfl
  revert this; decide

end Podc.MBroadcast.FromRegisters
