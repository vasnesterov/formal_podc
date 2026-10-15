import Papers.PODC2024.HistoryIndependent.UniversalFlatWF
import Papers.PODC2024.HistoryIndependent.UniversalExample
import Cslib.Computability.Distributed.SharedMemory.Progress
import Mathlib

/-!
# The flattened implementation: a sanity check

With `n = 2` processes implementing a binary register over CAS objects, process `0` invokes
`write true` and runs solo: the operation completes (by wait-freedom, the solo run returns), and
afterwards all CAS objects hold the canonical representation of the state `true`.

(The CAS objects of `flat` decide equality classically, so the run is not evaluated by `rfl` as in
`UniversalExample`; its existence follows from `flat_waitFree`.)
-/

namespace Cslib.SharedMemory

namespace Universal

local notation "R" => binaryRegister false

/-- **Non-vacuity of Theorem 32**: there is an execution of the flattened implementation in
which process `0` invokes `write true` and gets a response, after which every CAS object holds
the canonical value for the state `true`. -/
theorem flat_ex_run : ∃ α C, (flat R 2).run α = some C ∧ opsOf α 0 = [.write true] ∧
    (respsOf α 0).length = 1 ∧ C.Quiescent ∧ C.mem = canon true := by
  have hof := Impl.WaitFree.obstructionFree (flat R 2) flat_waitFree
  obtain ⟨C', h1, h2, h3, h4, h5⟩ := (flat R 2).soloOp_spec hof 0 (.write true) trivial
    (α := []) (C := (flat R 2).initCfg) rfl rfl
  set α := (flat R 2).soloOp 0 (.write true) (flat R 2).initCfg
  have hrun : (flat R 2).run α = some C' := h1
  have hops1 : opsOf α 1 = [] :=
    opsOf_eq_nil_of_proc_ne fun ℓ hℓ => by rw [h3 ℓ hℓ]; decide
  have hresp1 : respsOf α 1 = [] :=
    respsOf_eq_nil_of_proc_ne fun ℓ hℓ => by rw [h3 ℓ hℓ]; decide
  have hq : C'.Quiescent := by
    intro r
    fin_cases r
    · exact h2
    · rcases (flat R 2).run_counts hrun 1 with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · rw [hops1, hresp1] at h; simp at h
  refine ⟨α, C', hrun, h4, h5, hq, ?_⟩
  rw [flat_mem_eq_canon hrun hq.stateQuiescent]
  have hv : (flat R 2).Valid α := ⟨C', hrun⟩
  rw [(flat_isLinFun α hv).linState_of_changer hv.wellFormed 0 ?_ ?_]
  · rw [h4]; rfl
  · intro r hr o ho
    fin_cases r
    · exact absurd rfl hr
    · exact absurd ho (by rw [show ((fun i => i) ⟨1, by decide⟩ : Fin 2) = 1 from rfl, hops1]; simp)
  · rw [h4, h5]; rfl

end Universal

end Cslib.SharedMemory
