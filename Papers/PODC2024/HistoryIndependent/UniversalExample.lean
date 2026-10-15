import Papers.PODC2024.HistoryIndependent.UniversalWF
import Mathlib.Tactic.FinCases

/-!
# Algorithm 5: a sanity check

Guard against vacuity: with `n = 2` processes implementing a binary register, process `0`
invokes `write true` and runs solo; the operation completes (after 16 steps: announce, apply,
write the response, clear `head`, clear `announce[0]`) and returns `true`. The final memory is
the canonical representation of the state `true`.
-/

namespace Cslib.SharedMemory

namespace Universal

instance : DecidablePred (binaryRegister false).ReadOnly := fun o =>
  match o with
  | .read => isTrue fun _ => rfl
  | .write v => isFalse fun h => by have := h (!v); cases v <;> simp at this

local notation "R" => binaryRegister false

/-- The configuration after process `0` invokes `write true`. -/
noncomputable def C1 : Config R (B R 2) (Fin 2) (Loc R 2) :=
  { (alg5 R 2).initCfg with
    pend := Function.update (fun _ => none) 0 (some (.write true))
    loc := Function.update (alg5 R 2).locInit 0
      ⟨.ann (.write true), 0, (false, none), none, 0⟩ }

lemma step_inv : (alg5 R 2).step (alg5 R 2).initCfg (.inv 0 (.write true)) = some C1 := by
  have : ¬ ObjSpec.ReadOnly R (.write true) := fun h => by have := h false; simp at this
  simp [Impl.step, Impl.initCfg, C1, alg5, this]

lemma run_taus : ((alg5 R 2).runFrom C1 (List.replicate 16 (.tau 0))).map
    (fun C => ((C.loc 0).pc, C.pend 0, C.mem .head, C.mem (.ann 0), C.mem (.ann 1))) =
    some (.retSC true, some (.write true), ((true, none), ∅), (none, ∅), (none, ∅)) := by
  rfl

/-- Process `0` writes `true` solo; the last label is the response `r`. -/
def exLabels (r : Bool) : List (Label (Fin 2) R) :=
  .inv 0 (.write true) :: (List.replicate 16 (.tau 0) ++ [.ret 0 r])

/-- **Non-vacuity**: process `0`'s `write true` completes with response `true`, and the final
memory is the canonical representation `⟨true, ⊥⟩` with empty contexts and `announce = ⊥`. -/
theorem ex_run : ∃ C, (alg5 R 2).run (exLabels true) = some C ∧ C.pend 0 = none ∧
    C.mem .head = ((true, none), ∅) ∧ C.mem (.ann 0) = (none, ∅) ∧ C.mem (.ann 1) = (none, ∅) := by
  obtain ⟨C17, h17, he⟩ := Option.map_eq_some_iff.1 run_taus
  simp only [Prod.mk.injEq] at he
  obtain ⟨hpc, hpd, hh, ha0, ha1⟩ := he
  have hstep : (alg5 R 2).step C17 (.ret 0 true) = some
      { C17 with pend := Function.update C17.pend 0 none,
                 loc := Function.update C17.loc 0 { C17.loc 0 with pc := .idle } } := by
    simp [Impl.step, alg5, act, hpc, hpd]
  refine ⟨{ C17 with pend := Function.update C17.pend 0 none,
                     loc := Function.update C17.loc 0 { C17.loc 0 with pc := .idle } },
    ?_, by simp, hh, ha0, ha1⟩
  rw [Impl.run, exLabels, Impl.runFrom_cons, step_inv, Option.bind_some, Impl.runFrom_append,
    h17, Option.bind_some, Impl.runFrom_singleton, hstep]

/-- A wrong response is not a valid execution. -/
theorem ex_not_valid : ¬ (alg5 R 2).Valid (exLabels false) := by
  obtain ⟨C17, h17, he⟩ := Option.map_eq_some_iff.1 run_taus
  simp only [Prod.mk.injEq] at he
  obtain ⟨hpc, hpd, -⟩ := he
  rintro ⟨C, hC⟩
  rw [Impl.run, exLabels, Impl.runFrom_cons, step_inv, Option.bind_some, Impl.runFrom_append,
    h17, Option.bind_some, Impl.runFrom_singleton] at hC
  simp [Impl.step, alg5, act, hpc, hpd] at hC

/-! ## The release operations are necessary

Section 6.1 claims that Algorithm 5 *without the `RL` operations of lines 22 and 27* (marked in
red in the paper) is not even quiescent HI: a process that finds its operation already applied
leaves its link in `head.context`. We confirm this: in the variant `alg5NoRL` (lines 22 and 27
replaced by a `Load`, i.e. skipped), process `0` writing `true` solo and process `1` writing
`true` solo end in quiescent configurations with the same abstract state but different
memory (`head.context = {0}` resp. `{1}`).
-/

variable {A : ObjSpec} {n : ℕ} in
/-- Algorithm 5 without the `RL` operations of lines 22 and 27. -/
def actNoRL (p : Fin n) (l : Loc A n) : Action A (B A n) (Loc A n) :=
  match l.pc with
  | .rlHead x => accH .load fun _ => { l with pc := .storeBot x }
  | .rlAnn => accA l.aj .load fun _ => { l with pc := .loop }
  | _ => act p l

variable (A : ObjSpec) (n : ℕ) in
/-- Algorithm 5 without the `RL` operations (lines 22 and 27). -/
def alg5NoRL [DecidablePred A.ReadOnly] : Impl A (B A n) (Fin n) (Loc A n) :=
  { alg5 A n with act := actNoRL }

/-- The configuration after process `q` invokes `write true`. -/
noncomputable def D1 (q : Fin 2) : Config R (B R 2) (Fin 2) (Loc R 2) :=
  { (alg5NoRL R 2).initCfg with
    pend := Function.update (fun _ => none) q (some (.write true))
    loc := Function.update (alg5NoRL R 2).locInit q
      ⟨.ann (.write true), q, (false, none), none, q⟩ }

lemma stepNR_inv (q : Fin 2) :
    (alg5NoRL R 2).step (alg5NoRL R 2).initCfg (.inv q (.write true)) = some (D1 q) := by
  have : ¬ ObjSpec.ReadOnly R (.write true) := fun h => by have := h false; simp at this
  simp [Impl.step, Impl.initCfg, D1, alg5NoRL, alg5, this]

lemma runNR_taus0 : ((alg5NoRL R 2).runFrom (D1 0) (List.replicate 16 (.tau 0))).map
    (fun C => ((C.loc 0).pc, C.pend 0, C.pend 1, C.mem .head)) =
    some (.retSC true, some (.write true), none, ((true, none), {0})) := by
  rfl

lemma runNR_taus1 : ((alg5NoRL R 2).runFrom (D1 1) (List.replicate 16 (.tau 1))).map
    (fun C => ((C.loc 1).pc, C.pend 1, C.pend 0, C.mem .head)) =
    some (.retSC true, some (.write true), none, ((true, none), {1})) := by
  rfl

/-- Process `q` writes `true` solo. -/
def exNR (q : Fin 2) : List (Label (Fin 2) R) :=
  .inv q (.write true) :: (List.replicate 16 (.tau q) ++ [.ret q true])

lemma exNR_run (q : Fin 2) : ∃ C, (alg5NoRL R 2).run (exNR q) = some C ∧ C.Quiescent ∧
    C.mem .head = ((true, none), {q}) := by
  have key : ∃ C17, (alg5NoRL R 2).runFrom (D1 q) (List.replicate 16 (.tau q)) = some C17 ∧
      (C17.loc q).pc = .retSC true ∧ C17.pend q = some (.write true) ∧
      (∀ r, r ≠ q → C17.pend r = none) ∧ C17.mem .head = ((true, none), {q}) := by
    fin_cases q
    · obtain ⟨C17, h17, he⟩ := Option.map_eq_some_iff.1 runNR_taus0
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2, h3, h4⟩ := he
      exact ⟨C17, h17, h1, h2, fun r hr => by
        fin_cases r <;> first | exact absurd rfl hr | exact h3, h4⟩
    · obtain ⟨C17, h17, he⟩ := Option.map_eq_some_iff.1 runNR_taus1
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2, h3, h4⟩ := he
      exact ⟨C17, h17, h1, h2, fun r hr => by
        fin_cases r <;> first | exact absurd rfl hr | exact h3, h4⟩
  obtain ⟨C17, h17, hpc, hpd, hpo, hh⟩ := key
  have hstep : (alg5NoRL R 2).step C17 (.ret q true) = some
      { C17 with pend := Function.update C17.pend q none,
                 loc := Function.update C17.loc q { C17.loc q with pc := .idle } } := by
    simp [Impl.step, alg5NoRL, actNoRL, act, hpc, hpd]
  refine ⟨{ C17 with pend := Function.update C17.pend q none,
                     loc := Function.update C17.loc q { C17.loc q with pc := .idle } },
    ?_, fun r => ?_, hh⟩
  · rw [Impl.run, exNR, Impl.runFrom_cons, stepNR_inv, Option.bind_some, Impl.runFrom_append,
      h17, Option.bind_some, Impl.runFrom_singleton, hstep]
  · by_cases hr : r = q
    · subst hr; simp
    · simp [Function.update_of_ne hr, hpo r hr]

/-- **Section 6.1 (the `RL` operations are needed)**: Algorithm 5 without the release operations
of lines 22 and 27 is not quiescent HI (already for two processes and a binary register). -/
theorem alg5NoRL_not_quiescentHI : ¬ (alg5NoRL R 2).QuiescentHI := by
  rintro ⟨h, hlin, hmem⟩
  obtain ⟨C, hC, hqC, hhC⟩ := exNR_run 0
  obtain ⟨C', hC', hqC', hhC'⟩ := exNR_run 1
  have hst : ∀ q : Fin 2, ∀ C, (alg5NoRL R 2).run (exNR q) = some C →
      linState (h (exNR q)) = true := by
    intro q C hC
    have hv : (alg5NoRL R 2).Valid (exNR q) := ⟨C, hC⟩
    rw [(hlin _ hv).linState_of_changer hv.wellFormed q ?_ ?_]
    · simp [exNR, ObjSpec.runOps, List.replicate_succ]
    · intro r hr o ho
      simp [exNR, Ne.symm hr, List.replicate_succ] at ho
    · simp [exNR, List.replicate_succ]
  have := hmem _ _ _ _ hC hC' hqC hqC' (by rw [hst 0 C hC, hst 1 C' hC'])
  have e := congrFun this .head
  rw [hhC, hhC'] at e
  simp at e

end Universal

end Cslib.SharedMemory
