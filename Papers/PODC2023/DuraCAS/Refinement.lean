import Papers.PODC2023.DuraCAS.CStepTop

/-!
# DurEC objects behave like atomic durable EC objects inside DuraCAS

(Theorem 4.10 of the full version — Lemmas A.1–A.11 — as used in Appendix A.3: every execution of
the concrete model, where the DurEC code is inlined, is matched by an execution of the A-level model
with the same history.)

The proof is a forward simulation with the invariant `Inv` of `CInv.lean`: every concrete step is
matched by 0–3 A-level steps (`sim_step`). The A-level `ECSC` of a process is linearized at the
move of its install (Definition A.8.1), even if the move is made by a helper or after a crash of
the installer (then as an orphan); a hitchhiker `ECSC` and a `RECOVER` complete at their return.
-/

set_option linter.unusedSectionVars false

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- **Simulation step.** Every concrete step is matched by a sequence of A-level steps
preserving the simulation invariant. -/
theorem sim_step {s s' : St P K V} {a : AS P K V} (hI : Inv s a) (h : Step s s') :
    ∃ a', Relation.ReflTransGen AStep a a' ∧ Inv s' a' := by
  obtain ⟨ℓ, hen, rfl⟩ := h
  cases ℓ with
  | step p =>
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hen
    cases hfr : (s.ps p).fr with
    | some f => exact sim_frame hI hfr
    | none => exact sim_top hI hfr hr
  | invoke p k op => exact sim_invoke hI hen
  | crash p => exact sim_crash hI hen

/-- Every reachable concrete state is related by `Inv` to a reachable A-level state. -/
theorem reach_inv {init : K → V} {hv0 : Hd P → V × Bool} {s : St P K V}
    (h : Reach init hv0 s) : ∃ a : AS P K V, AReach init a ∧ Inv s a := by
  induction h with
  | refl => exact ⟨ainit init, .refl, inv_init init hv0⟩
  | tail _ hst ih =>
    obtain ⟨a, ha, hI⟩ := ih
    obtain ⟨a', ha', hI'⟩ := sim_step hI hst
    exact ⟨a', ha.trans ha', hI'⟩

/-- **Refinement.** Every reachable concrete state (per-process recovery discipline) has an A-level
reachable counterpart with the same history. -/
theorem reach_aReach {init : K → V} {hv0 : Hd P → V × Bool} {s : St P K V}
    (h : Reach init hv0 s) : ∃ a : AS P K V, AReach init a ∧ a.hist = s.hist := by
  obtain ⟨a, ha, hI⟩ := reach_inv h
  exact ⟨a, ha, hI.hist⟩

end Podc.DuraCAS
