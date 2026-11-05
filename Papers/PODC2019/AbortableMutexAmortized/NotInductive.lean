import Papers.PODC2019.AbortableMutexAmortized.PaperInv

/-!
# The paper's invariant `I` is not inductive

Appendix A proves Theorem 4.1 by induction on steps, assuming `I` before a step and showing it
after. But `I = I1 ∧ … ∧ I12` is *not* preserved by every step from an arbitrary configuration
satisfying `I`: with `n = 3`, queue `Q = [r, x, π]` (`r = 0`, `x = 1`, `π = 2`), `r` at line 3
with `*a_r = &go_x`, `x` aborted at line 11 (`*a_x = pred_x = a_r`), `π` at line 3, all of `I`
holds; `π` executes line 3, splices `x` out and becomes `r`'s successor, but `*a_r = &go_x` is
neither `nil` nor `&go_π`: `I7` fails. (The configuration is unreachable: an aborted process has
erased `&go_x` from its predecessor node at line 9.) The proof's "the rest of the invariants
continue to hold since they are unaffected" (line 3, case 3) misses exactly this; it needs the
additional conjunct `Loc.x1` ("an aborted process's predecessor node does not hold its
go-address"), with which the invariant is inductive (`inv_step`).
-/

namespace Podc.AbortableMutexAmortized

/-- The counterexample-to-induction configuration (`n = 3`). -/
def ctiState : State 3 where
  pc := ![.l3, .l11, .l3]
  mynode p := some p
  pred := ![none, some 0, some 1]
  v := ![.nil, .go 2, .nil]
  node a := match a with
    | none => .token
    | some p => ![.go 1, .addr (some 0), .nil] p
  go _ := false
  tail := some 2

/-- `ctiState` satisfies the paper's invariant `I`, with `A = [a₀, a_r, a_x, a_π]`,
`Q = [r, x, π]`. -/
theorem ctiState_paperInv :
    PaperInv ctiState [none, some 0, some 1, some 2] [0, 1, 2] := by
  refine ⟨rfl, by decide, by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i p h; rcases i with _ | _ | _ | i <;> simp at h <;> subst h <;> rfl
  · intro i p h; rcases i with _ | _ | _ | i <;> simp at h <;> subst h <;> rfl
  · intro x; rcases x with _ | p
    · simp
    · exact Or.inr ⟨p, rfl⟩
  · intro p; fin_cases p <;> simp [ctiState]
  · intro p; fin_cases p <;> simp [ctiState]
  · intro p hp; simp at hp; subst hp; simp [ctiState, PC.inI7]
  · intro i x y hx hy
    rcases i with _ | _ | _ | i <;> simp at hx hy <;> subst hx <;> subst hy <;>
      simp [ctiState, PC.inI7]
  · intro p hp; fin_cases p <;> simp at hp
  · intro a ha; simp at ha; subst ha
    refine ⟨fun _ => rfl, fun q1 hq1 h7 => ?_⟩
    simp at hq1; subst hq1; simp [ctiState] at h7
  · intro p hp; fin_cases p <;> simp [ctiState] at hp ⊢
  · intro q1 hq1 h4; simp at hq1; subst hq1; simp [ctiState] at h4
  · intro i x y hx hy h4
    rcases i with _ | _ | _ | i <;> simp at hx hy <;> subst hx <;> subst hy <;>
      simp [ctiState] at h4
  · intro p hp; fin_cases p <;> simp [ctiState] at hp ⊢
  · intro p hp; fin_cases p <;> simp [ctiState] at hp

/-- **The induction step of Theorem 4.1 fails for `I` as stated**: from `ctiState`, which satisfies
`I`, the step of `π = 2` (line 3) leads to a configuration with no `A`, `Q` satisfying `I`. -/
theorem paperInv_not_inductive :
    PaperInv ctiState [none, some 0, some 1, some 2] [0, 1, 2] ∧
      ¬ ∃ A Q, PaperInv (step ctiState 2 false) A Q := by
  refine ⟨ctiState_paperInv, ?_⟩
  rintro ⟨A, Q, h⟩
  -- `I1`–`I4` force `A = [a₀, a_r, a_π]`, `Q = [r, π]`
  have hu := unique_of_I1_I4 (s := step ctiState 2 false) (A' := [none, some 0, some 2])
    (Q' := [0, 2]) h.len h.I1 h.I2 h.I3 h.I4 rfl (by decide)
    (by intro i p hp; rcases i with _ | _ | i <;> simp at hp <;> subst hp <;> decide)
    (by intro i p hp; rcases i with _ | _ | i <;> simp at hp <;> subst hp <;> decide)
    (by intro x; rcases x with _ | p
        · simp
        · exact Or.inr ⟨p, by decide +revert⟩)
  obtain ⟨rfl, rfl⟩ := hu
  have := (h.I7mid 0 0 2 rfl rfl).1 (by decide)
  revert this; decide

end Podc.AbortableMutexAmortized
