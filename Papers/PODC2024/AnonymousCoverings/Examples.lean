import Papers.PODC2024.AnonymousCoverings.WaitFree
import Papers.PODC2024.AnonymousCoverings.Counterexamples

/-!
# Non-vacuity: executions of the snapshot algorithm exist

With one processor and one register, the processor writes, reads its own value, reaches level
`1 = N` and terminates; afterwards it takes idle steps. This is an (infinite) execution of
Figure 3 from the initial configuration, so the hypotheses of `snapshot_waitFree` are satisfiable.
-/

namespace Podc.AnonymousCoverings

instance {R V : Type*} [Fintype R] [DecidableEq R] [DecidableEq V] : DecidableEq (SnapD R V) :=
  fun a b => decidable_of_iff (a.view = b.view ∧ a.level = b.level ∧ a.got = b.got)
    (by cases a; cases b; simp)

instance {R V : Type*} [Fintype R] [Nonempty R] [DecidableEq R] [DecidableEq V] (L : ℕ) :
    DecidablePred (snapshot (R := R) (V := V) L).stop :=
  fun d => inferInstanceAs (Decidable (L ≤ d.level))

/-- Solo run of one processor: write, read, terminate, idle forever. -/
def snapSolo : Exec (P := Fin 1) (snapshot (R := Fin 1) (V := Fin 1) 1) :=
  periodicExec (pre := [.write 0 0, .read 0 0]) (cyc := [.idle 0]) (dflt := .idle 0)
    (snapshot 1) (snapCfg fun _ => 0) (by decide) (by decide) (by decide)

/-- The solo execution starts in the initial configuration and its processor terminates with
output `{0}`. -/
theorem snapSolo_spec : snapSolo.cfg 0 = snapCfg (fun _ => 0) ∧
    (snapSolo.loc 2 0).scan = none ∧ 1 ≤ (snapSolo.loc 2 0).d.level ∧
    (snapSolo.loc 2 0).d.view = {0} := by
  refine ⟨rfl, ?_⟩
  decide

/-! ### Figure 2 -/

/-- Initial configuration of Figure 1 with three processors, inputs `0, 1, 2` (the paper's
`1, 2, 3`). -/
abbrev ws3 : Cfg (Fin 3) (Fin 3) (Finset (Fin 3)) (Finset (Fin 3)) :=
  initCfg (fun p : Fin 3 => ({p} : Finset (Fin 3))) ∅

/-- `p` writes `r` and then scans all registers. -/
def wscan (p : Fin 3) (r : Fin 3) : List (Act (Fin 3) (Fin 3)) :=
  [.write p r, .read p 0, .read p 1, .read p 2]

/-- Rows 1–4 of Figure 2 (registers `r₁, r₂, r₃` are `0, 1, 2`). -/
def fig2pre : List (Act (Fin 3) (Fin 3)) :=
  wscan 0 1 ++ wscan 0 2 ++ wscan 1 0 ++ wscan 2 0 ++ wscan 0 0

/-- Rows 5–13 of Figure 2, repeated forever. -/
def fig2cyc : List (Act (Fin 3) (Fin 3)) :=
  wscan 1 1 ++ wscan 2 1 ++ wscan 0 1 ++ wscan 1 2 ++ wscan 2 2 ++ wscan 0 2 ++
    wscan 1 0 ++ wscan 2 0 ++ wscan 0 0

theorem fig2_per : runOf fig2pre fig2cyc (.idle 0) writeScan ws3 (fig2pre.length + fig2cyc.length) =
    runOf fig2pre fig2cyc (.idle 0) writeScan ws3 fig2pre.length := by decide +kernel

/-- The execution of Figure 2. -/
def fig2 : Exec (P := Fin 3) (writeScan (R := Fin 3) (V := Fin 3)) :=
  periodicExec writeScan ws3 (by decide) fig2_per (by decide +kernel)

/-- **Figure 2 (Section 4.1).** The schedule of Figure 2 is an infinite execution of the write–scan
loop in which all three processors are live and, from row 4 on, the views of `p₁, p₂, p₃` are
`{1}`, `{1,2}`, `{1,3}` (here `{0}`, `{0,1}`, `{0,2}`): `p₂` and `p₃` keep incomparable views. -/
theorem figure_2 : fig2.cfg 0 = ws3 ∧ (∀ p, fig2.Live p) ∧
    ∀ t ≥ fig2pre.length, (fig2.loc t 0).d = {0} ∧ (fig2.loc t 1).d = {0, 1} ∧
      (fig2.loc t 2).d = {0, 2} := by
  refine ⟨rfl, fun p T => ?_, fun t ht => ?_⟩
  · obtain ⟨t, ht, h⟩ := exists_ge_actOf (pre := fig2pre) (cyc := fig2cyc) (dflt := .idle 0)
      (by decide) (i := 4 * ((p.val + 2) % 3)) (by have := p.isLt; simp [fig2cyc, wscan]; omega) T
    refine ⟨t, ht, 1, Or.inl ?_⟩
    change actOf fig2pre fig2cyc (.idle 0) t = _
    rw [h]; fin_cases p <;> rfl
  · exact periodic_forall_from (pre := fig2pre) (cyc := fig2cyc) (dflt := .idle 0) writeScan ws3
      (by decide) fig2_per
      (fun _ c => (c.loc 0).d = {0} ∧ (c.loc 1).d = {0, 1} ∧ (c.loc 2).d = {0, 2})
      (by decide +kernel) t ht

end Podc.AnonymousCoverings
