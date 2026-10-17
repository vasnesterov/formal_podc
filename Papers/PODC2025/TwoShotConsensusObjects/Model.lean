import Papers.PODC2025.TwoShotConsensusObjects.Defs
import Cslib.Computability.Distributed.SharedMemory.ObjClasses
import Cslib.Computability.Distributed.SharedMemory.Recoverable
import Podc.Computability.Distributed.SharedMemory.Recoverable

/-!
# Two-shot objects solving two-process consensus — the system model

Model (Section 3 of the paper), on top of CSLib's asynchronous shared-memory model
`Cslib.SharedMemory.Recoverable` used without crashes (`WFConsensus` = wait-free binary
consensus in the crash-stop model):

* two deterministic processes `0 = p₀` and `1 = p₁` (`Fin 2`), starting with binary inputs;
  a process outputs (decides) by entering an output state;
* asynchronous scheduling; executions are lists of events (we only use crash-free ones);
* shared objects (`withRW R O`): read/write objects `R j` (`j : ιR`, every operation read-only or
  a blind write, `ObjSpec.RWLike`; registers are an instance) and copies `k : ιS` (finitely many)
  of the deterministic type `O` under study; initial states are chosen freely by the algorithm
  (`Alg.mem₀`), as in Jayanti's model used by the paper;
* **two-shot** (`TwoShot`): in every execution each process applies at most two operations to
  each copy of `O`;
* **process-allowance map** (`Allowed m`): process `p` only applies operations of `m p` to the
  copies of `O`;
* wait-free consensus: agreement, validity and wait-freedom (`WFConsensus`).

`Solvable O m` — the paper's "objects of type `(O, m)` solve two-shot two-process consensus".
The object families `withRW`, access counts `accCount` and the generic correctness tools
(`prog_of_rank`, `wfConsensus_of_inv`, …) are in `Cslib.Computability.Distributed.SharedMemory.Recoverable`.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

section System

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}

/-- **Two-shot**: in every (crash-free) execution from an initial configuration, each process
applies at most two operations to each copy of `O`. -/
def TwoShot (A : Alg 2 (withRW (ιS := ιS) R O)) : Prop :=
  ∀ x α, CrashFree α → ∀ p (k : ιS), accCount (initCfg A x) α p (.inr k) ≤ 2

/-- **Process-allowance map**: in every reachable configuration, a process poised on a copy of
`O` is poised to apply an operation allowed by `m`. -/
def Allowed (m : Fin 2 → Set O.Op) (A : Alg 2 (withRW (ιS := ιS) R O)) : Prop :=
  ∀ x α, CrashFree α → ∀ p (k : ιS) (o : O.Op) (κ : O.Resp → A.L),
    A.act ((run (initCfg A x) α).loc p) = .access (.inr k) o κ → o ∈ m p

end System

/-- **Objects of type `(O, m)` solve two-shot two-process consensus** (Section 3): there is a
wait-free binary consensus algorithm for two processes using read/write objects and finitely many
two-shot copies of `O` accessed according to `m`. -/
def Solvable (O : ObjSpec) (m : Fin 2 → Set O.Op) : Prop :=
  ∃ (ιR ιS : Type) (_ : DecidableEq ιR) (_ : DecidableEq ιS) (_ : Fintype ιS)
    (R : ιR → ObjSpec) (_ : ∀ j, (R j).RWLike) (A : Alg 2 (withRW (ιS := ιS) R O)),
    WFConsensus A ∧ TwoShot A ∧ Allowed m A

/-! ## Generic tools for two-shot algorithms -/

section ToolsSys

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}
  {A : Alg 2 (withRW (ιS := ιS) R O)}

/-- **Two-shot from a budget**: a budget `bud l k` of remaining accesses to copy `k` that is at
most `2` initially, decreases by one at each access to `k` and never increases. -/
theorem twoShot_of_budget (bud : A.L → ιS → ℕ) (hinit : ∀ p b k, bud (A.init p b) k ≤ 2)
    (hstep : ∀ l i o (κ : ((withRW (ιS := ιS) R O) i).Resp → A.L) r k,
      A.act l = .access i o κ → bud (κ r) k + (if i = .inr k then 1 else 0) ≤ bud l k) :
    TwoShot A := by
  classical
  intro x α hα p k
  -- general statement from any configuration
  have gen : ∀ (α : List (Ev 2)) (C : Cfg A), CrashFree α →
      accCount C α p (.inr k) + bud ((run C α).loc p) k ≤ bud (C.loc p) k := by
    intro α
    induction α with
    | nil => intro C _; simp
    | cons e α ih =>
      intro C hcf
      have hcf' : CrashFree α := fun q hq => hcf q (by simp [hq])
      rw [accCount_cons, run_cons]
      have h1 := ih (C.next e) hcf'
      rcases e with q | q
      · by_cases hq : q = p
        · subst hq
          simp only [Cfg.next] at h1 ⊢
          rcases hact : A.act (C.loc q) with ⟨i, o, κ⟩ | v
          · rw [stepP_of_access _ hact] at h1 ⊢
            simp only [Function.update_self] at h1
            have h2 := hstep _ i o κ ((((withRW (ιS := ιS) R O) i).δ (C.mem i) o).2) k hact
            have hobj : objOf C q = some i := by simp [objOf, hact]
            simp only [hobj, Option.some.injEq, true_and]
            split_ifs at h2 ⊢ <;> simp_all <;> omega
          · rw [stepP_of_out C (show C.Out q v from hact)] at h1 ⊢
            have hobj : objOf C q = none := by simp [objOf, hact]
            simp [hobj]; omega
        · have hne : (Ev.step q : Ev 2) ≠ .step p := by simpa using hq
          rw [next_loc_other C _ (by simpa using Ne.symm hq)] at h1
          simp [hne]; omega
      · exact absurd (by simp) (hcf q)
  have := gen α (initCfg A x) hα
  have h0 := hinit p (x p) k
  have hl : (initCfg A x).loc p = A.init p (x p) := rfl
  rw [hl] at this
  omega

/-- **Allowance from an invariant of local states.** -/
theorem allowed_of_inv (m : Fin 2 → Set O.Op) (G : Fin 2 → A.L → Prop)
    (hinit : ∀ p b, G p (A.init p b))
    (hstep : ∀ p l i o (κ : ((withRW (ιS := ιS) R O) i).Resp → A.L) r,
      G p l → A.act l = .access i o κ → G p (κ r))
    (hok : ∀ p l (k : ιS) (o : O.Op) (κ : O.Resp → A.L), G p l →
      A.act l = .access (.inr k) o κ → o ∈ m p) : Allowed m A := by
  intro x α hα p k o κ hact
  refine hok p _ k o κ ?_ hact
  have gen : ∀ (α : List (Ev 2)) (C : Cfg A), CrashFree α → G p (C.loc p) →
      G p ((run C α).loc p) := by
    intro α
    induction α with
    | nil => intro C _ h; simpa using h
    | cons e α ih =>
      intro C hcf hG
      have hcf' : CrashFree α := fun q hq => hcf q (by simp [hq])
      rw [run_cons]
      apply ih _ hcf'
      rcases e with q | q
      · by_cases hq : q = p
        · subst hq
          simp only [Cfg.next]
          rcases hact : A.act (C.loc q) with ⟨i, o, κ⟩ | v
          · rw [stepP_of_access _ hact]; simp only [Function.update_self]
            exact hstep q _ i o κ _ hG hact
          · rwa [stepP_of_out C (show C.Out q v from hact)]
        · rwa [next_loc_other C _ (by simpa using Ne.symm hq)]
      · exact absurd (by simp) (hcf q)
  exact gen α _ hα (hinit p (x p))

end ToolsSys

end TwoShotCons
