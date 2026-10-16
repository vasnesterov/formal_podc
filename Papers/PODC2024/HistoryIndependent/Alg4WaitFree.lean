import Papers.PODC2024.HistoryIndependent.Alg4Inv
import Podc.SharedMemory.Potential

/-!
# Algorithm 4 is wait-free

* `Impl.waitFree_of_potential` (general, now in `Podc/SharedMemory/Potential.lean`): if a
  potential on local states strictly decreases with every base-object access of a process, the
  implementation is wait-free (each operation finishes within `μ p l` own steps).
* Every `Write` of Algorithm 4 takes at most `3K + 6` and every `Read` at most `6K + 6` low-level
  steps (`WPC.pot`, `RPC.pot`), hence `waitFree`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory


namespace Alg4

variable {K : ℕ} [NeZero K]

/-- Upper bound on the remaining steps of the writer. -/
def WPC.pot (K : ℕ) : WPC K → ℕ
  | .idle | .done _ => 0
  | .up _ j => K - j.val
  | .down _ j => K + j.val + 1
  | .setA _ => 2 * K + 1
  | .clrB _ => 2 * K + 2
  | .rdF1' _ => 2 * K + 3
  | .rdF2 _ => 2 * K + 4
  | .setB _ => 2 * K + 5
  | .rdF1 _ => 2 * K + 6
  | .scanB _ j => 3 * K + 6 - j.val

/-- Upper bound on the remaining steps of the reader. -/
def RPC.pot (K : ℕ) : RPC K → ℕ
  | .idle | .done _ => 0
  | .resF2 _ => 1
  | .resF1 _ => 2
  | .clr j _ => K + 2 - j.val
  | .setF2 _ => K + 3
  | .bscan j _ => 2 * K + 3 - j.val
  | .down _ j => 2 * K + 4 + j.val
  | .up true j => 4 * K + 4 - j.val
  | .up false j => 6 * K + 5 - j.val
  | .start => 6 * K + 6

/-- **Algorithm 4 is wait-free.** -/
theorem waitFree (v₀ : Fin K) : (alg4 v₀).WaitFree := by
  refine (alg4 v₀).waitFree_of_potential
    (fun p l => match p with | .w => l.wpc.pot K | .r => l.rpc.pot K) ?_
  intro p l i o k hact x
  cases p with
  | w =>
    simp only [alg4, act, actW] at hact
    cases hw : l.wpc with
    | idle => simp [hw] at hact
    | done v => simp [hw] at hact
    | scanB v j =>
      simp only [hw] at hact; cases hact; dsimp only
      have := j.isLt
      unfold WPC.scanNext; split_ifs <;> simp [WPC.pot] <;> omega
    | setA v =>
      simp only [hw] at hact; cases hact; dsimp only
      have := v.isLt
      rcases WPC.afterSetA_spec v with ⟨_, _, hf⟩ | ⟨_, _, hf⟩ | ⟨_, _, hf⟩ <;> rw [hf] <;>
        simp [WPC.pot] <;> omega
    | down v j =>
      simp only [hw] at hact; cases hact; dsimp only
      have := j.isLt
      rcases WPC.downNext_spec v j with ⟨_, _, hf⟩ | ⟨_, _, hf⟩ | ⟨_, _, hf⟩ <;> rw [hf] <;>
        simp [WPC.pot] <;> first | omega | exact Fin.pos_iff_ne_zero.2 (by rintro rfl; simp_all)
    | up v j =>
      simp only [hw] at hact; cases hact; dsimp only
      have := j.isLt
      rcases WPC.upNext_spec v j with ⟨_, hf⟩ | ⟨_, hf⟩ <;> rw [hf] <;>
        simp [WPC.pot] <;> omega
    | _ =>
      simp only [hw] at hact; cases hact; dsimp only
      first
        | (simp only [WPC.pot]; omega)
        | (cases x <;> simp [WPC.pot])
  | r =>
    simp only [alg4, act, actR] at hact
    cases hr : l.rpc with
    | idle => simp [hr] at hact
    | done val => simp [hr] at hact
    | up b j =>
      simp only [hr] at hact; cases hact; dsimp only
      have := j.isLt
      cases x
      · simp only [Bool.false_eq_true, ite_false]
        unfold RPC.upNext; cases b <;> split_ifs <;> simp [RPC.pot] <;> first | omega | simp_all
      · simp only [ite_true]
        rcases RPC.found_spec j with ⟨_, hf⟩ | ⟨_, _, hf⟩ <;> rw [hf] <;>
          cases b <;> simp [RPC.pot] <;> omega
    | down val j =>
      simp only [hr] at hact; cases hact; dsimp only
      have := j.isLt
      rcases RPC.downNext_spec val j x with ⟨_, hf⟩ | ⟨_, _, hf⟩ <;> rw [hf] <;>
        simp [RPC.pot] <;> first | omega | exact Fin.pos_iff_ne_zero.2 (by rintro rfl; simp_all)
    | bscan j val =>
      simp only [hr] at hact; cases hact; dsimp only
      have := j.isLt
      rcases RPC.bscanNext_spec j val x with ⟨_, hf⟩ | ⟨_, hf⟩ <;> rw [hf] <;>
        simp [RPC.pot] <;> omega
    | clr j val =>
      simp only [hr] at hact; cases hact; dsimp only
      have := j.isLt
      rcases RPC.clrNext_spec j val with ⟨_, hf⟩ | ⟨_, hf⟩ <;> rw [hf] <;>
        simp [RPC.pot] <;> omega
    | _ =>
      simp only [hr] at hact; cases hact; dsimp only
      simp [RPC.pot]

end Alg4

end Cslib.SharedMemory
