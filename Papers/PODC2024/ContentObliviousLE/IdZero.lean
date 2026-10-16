import Podc.ContentOblivious.Lockstep
import Papers.PODC2024.ContentObliviousLE.Alg2

/-!
# IDs must be positive

The paper takes `ID_v ∈ ℕ`. If `0` is an admissible ID, Algorithm 2 (and Algorithm 1) never
terminates: a node with ID `0` relays every CW pulse, so on the 1-node ring its initial pulse
circulates forever. We therefore assume positive IDs throughout (as the analysis implicitly does,
e.g. Lemma 5's base case and "k distinct IDs have maximum ≥ k" in the proof of Lemma 22).
-/

namespace Podc.ContentOblivious.Alg2

open Podc.ContentOblivious

lemma run_zero (j : ℕ) :
    run alg 0 (List.replicate j false) =
      (⟨0, j, 0, decide (1 ≤ j), false, false, false⟩,
        fun p => if p then j + 1 else if 1 ≤ j then 1 else 0) := by
  induction j with
  | zero => simp [run, alg]
  | succ j ih =>
    rw [List.replicate_succ', run_append, ih]
    simp only [alg, recvCW]
    refine Prod.ext ?_ ?_
    · simp
    · funext p; cases p <;> simp <;> cases j <;> simp

/-- With ID `0`, Algorithm 2 has an infinite execution on the 1-node ring. -/
theorem infinite_execution_id_zero :
    ∃ f : ℕ → Config (ZMod 1) S, f 0 = initCfg alg (fun _ => 0) ∧
      ∀ k, Step (oriented 1) alg (f k) (f (k + 1)) := by
  refine ⟨fun k => syncCfg (A := alg) (fun _ => 0) fun _ => List.replicate k false,
    syncCfg_nil _, fun k => ?_⟩
  have hen : Enabled (oriented 1) alg
      (syncCfg (A := alg) (fun _ => 0) fun _ => List.replicate k false) 0 false := by
    refine ⟨?_, ?_, ?_⟩
    · simp [syncCfg, run_zero]
    · simp [syncCfg, run_zero, alg]
    · have : (oriented 1).peer (0, false) = (0, true) := by
        rw [Prod.ext_iff]; exact ⟨Subsingleton.elim _ _, rfl⟩
      rw [this]; simp [syncCfg, run_zero]
  have := Step.mk _ 0 false hen
  rw [deliver_syncCfg] at this
  convert this using 2
  funext x
  rw [Subsingleton.elim x 0]
  simp [List.replicate_succ']

end Podc.ContentOblivious.Alg2
