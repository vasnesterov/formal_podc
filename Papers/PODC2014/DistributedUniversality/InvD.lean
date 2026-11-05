import Papers.PODC2014.DistributedUniversality.InvCStep

/-!
# Bookkeeping of the processes' own operations

`InvD`: the operation a process proposes after line 28 is not in its local history (so an operation
committed in round `ρ` is never proposed again from round `ρ + 2` on), `LAST_OP[i][m]` is the
current operation of `pᵢ`, and every operation `c < cnt` of `pᵢ` has been returned (or will be at
line 31 of the current round).
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

structure InvD (M : Mode) (s : St n k) : Prop where
  my_nin : ∀ i x, pastLoc (s.loc i).pc → ¬ pastUpd (s.loc i).pc x →
    (i, (s.loc i).cnt x) ∉ (s.loc i).hist x
  oper_nin : ∀ i x, pastUpd (s.loc i).pc x → (s.loc i).oper x ∉ (s.loc i).hist x
  res_cnt : ∀ i x c, (x, c) ∈ (s.loc i).res → c + 1 = (s.loc i).cnt x ∧ pastUpd (s.loc i).pc x
  ret_cnt : ∀ i x c, c < (s.loc i).cnt x → s.retAt i x c ≠ none ∨ (x, c) ∈ (s.loc i).res
  last_cnt : ∀ i x, (s.loc i).pc ≠ .init → s.lastOp i x = some ((s.loc i).cnt x)

theorem invD_init (M : Mode) : InvD M (init : St n k) := by
  constructor <;> simp [init, initLoc]

/-- A fresh operation (not yet invoked) is in no history. -/
theorem InvC.not_mem_hist_of_fresh (C : InvC M s) {i : Fin n} {x : Fin k} {c : ℕ}
    (hc : s.invAt i x c = none) (p : Fin n) : (i, c) ∉ (s.loc p).hist x := by
  intro hm
  obtain ⟨t, ht⟩ := C.v_hist _ _ _ hm
  simp [ht] at hc

end Podc.DistributedUniversality
