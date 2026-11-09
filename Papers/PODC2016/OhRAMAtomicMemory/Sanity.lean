import Papers.PODC2016.OhRAMAtomicMemory.Statements
import Cslib.Computability.Distributed.MessagePassing.FairExec

/-!
# Sanity checks: concrete runs

With three servers, one writer and one reader, a `write(true)` followed by a `read()`, with every
message delivered, completes both operations and the read returns `true`, for all four algorithms
(`sanity_*`). The final configuration has no message in transit, so the run extends to a fair
execution without crashes (`Protocol.exists_fair_exec_of_quiescent`): the hypotheses of the
termination theorems are satisfiable.
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

/-- Encoding of history labels (CSLib `Label` has no `DecidableEq`). -/
def encLabel : Label (Node Unit Unit (Fin 3)) (register Bool false) → Bool × Bool × Option Bool
  | .inv (.wr _) _ => (true, true, none)
  | .inv _ _ => (true, false, none)
  | .ret (.wr _) v => (false, true, some v)
  | .ret _ v => (false, false, some v)
  | _ => (false, false, none)

section Runs

variable (T : Type) (t₁ : T) (bot : T)

/-- `write(true)` (tag `t₁`) and then `read()`, all messages delivered. `mw`: discover phase. -/
def goodRun (mw fast : Bool) :
    List (Step (Node Unit Unit (Fin 3)) (register Bool false) (Msg Unit T Bool) Empty) :=
  let srv : List (Fin 3) := [0, 1, 2]
  [.inv (.wr ()) (.write true)] ++
  (if mw then
    srv.map (fun i => .recv (.wr ()) (.sv i) (.discover 1)) ++
    srv.map (fun i => .recv (.sv i) (.wr ()) (.discoverAck bot false 1))
  else []) ++
  srv.map (fun i => .recv (.wr ()) (.sv i) (.writeRequest t₁ true (if mw then 2 else 0))) ++
  srv.map (fun i => .recv (.sv i) (.wr ()) (.writeAck t₁ true (if mw then 2 else 0))) ++
  [.inv (.rd ()) .read] ++
  srv.map (fun i => .recv (.rd ()) (.sv i) (.readRequest 1)) ++
  srv.flatMap (fun i => srv.map (fun j => .recv (.sv j) (.sv i) (.readRelay t₁ true () 1))) ++
  (if fast then srv.map (fun i => .recv (.sv i) (.rd ()) (.readRelay t₁ true () 1)) else []) ++
  srv.map (fun i => .recv (.sv i) (.rd ()) (.readAck t₁ true 1))

end Runs

/-- The expected history: `write(true)` returns, then `read()` returns `true`. -/
def goodHist : List (Bool × Bool × Option Bool) :=
  [(true, true, none), (false, true, some true), (true, false, none), (false, false, some true)]

/-- The run is valid, has the expected history, and leaves no message in transit. -/
def RunOK {L T : Type} [DecidableEq T]
    (Pr : Protocol (Node Unit Unit (Fin 3)) (register Bool false) L (Msg Unit T Bool) Empty)
    (ss : List (Step (Node Unit Unit (Fin 3)) (register Bool false) (Msg Unit T Bool) Empty)) :
    Prop :=
  ∃ C h, Pr.runFrom Pr.initCfg ss = some (C, h) ∧ h.map encLabel = goodHist ∧ C.net = 0 ∧
    C.crashed = ∅

lemma runOK_of {L T : Type} [DecidableEq T]
    {Pr : Protocol (Node Unit Unit (Fin 3)) (register Bool false) L (Msg Unit T Bool) Empty}
    {ss : List (Step (Node Unit Unit (Fin 3)) (register Bool false) (Msg Unit T Bool) Empty)}
    (h : ((Pr.runFrom Pr.initCfg ss).map fun x =>
      decide (x.2.map encLabel = goodHist ∧ Multiset.card x.1.net = 0 ∧ x.1.crashed.card = 0)) =
      some true) :
    RunOK Pr ss := by
  obtain ⟨⟨C, hC⟩, hrun, hc⟩ := Option.map_eq_some_iff.1 h
  simp only [decide_eq_true_eq, Multiset.card_eq_zero, Finset.card_eq_zero] at hc
  exact ⟨C, hC, hrun, hc⟩

theorem sanity_ohSam : RunOK (ohSam Unit (Fin 3) Bool false) (goodRun ℕ 1 0 false false) :=
  runOK_of (by decide +kernel)

theorem sanity_ohMam :
    RunOK (ohMam Unit Unit (Fin 3) Bool false) (goodRun (Tag Unit) (nextTag () ⊥) ⊥ true false) :=
  runOK_of (by decide +kernel)

theorem sanity_ohSam' : RunOK (ohSam' Unit (Fin 3) Bool false) (goodRun ℕ 1 0 false true) :=
  runOK_of (by decide +kernel)

theorem sanity_ohMam' :
    RunOK (ohMam' Unit Unit (Fin 3) Bool false) (goodRun (Tag Unit) (nextTag () ⊥) ⊥ true true) :=
  runOK_of (by decide +kernel)

/-- A run with no message in transit extends to a fair execution without crashes. -/
theorem fair_of_runOK {L T : Type} [DecidableEq T]
    {Pr : Protocol (Node Unit Unit (Fin 3)) (register Bool false) L (Msg Unit T Bool) Empty}
    {ss : List (Step (Node Unit Unit (Fin 3)) (register Bool false) (Msg Unit T Bool) Empty)}
    (h : RunOK Pr ss) :
    ∃ e : Pr.Exec, e.Fair ∧ ServerResilient e 0 ∧ (e.hist ss.length).map encLabel = goodHist := by
  obtain ⟨C, hC, hrun, hh, hnet, hcrash⟩ := h
  have hcr : C.crashed = ∅ := hcrash
  obtain ⟨e, hf, hhist, -, hcr'⟩ := Protocol.exists_fair_exec_of_quiescent hrun (fun s p hs => by
    cases s with
    | internal p a => exact a.elim
    | recv src dst m =>
      simp [Protocol.Enabled, Protocol.step, hnet]
    | _ => simp [Step.owner] at hs)
  refine ⟨e, hf, fun t => ?_, by rw [hhist, hh]⟩
  have := hcr' t
  rw [hcr] at this
  simp [Finset.subset_empty.1 this]

/-- Non-vacuity of the termination hypotheses: a fair execution without crashes in which a write
and a read complete exists, for each algorithm. -/
theorem fair_exec_exists :
    (∃ e : (ohSam Unit (Fin 3) Bool false).Exec, e.Fair ∧ ServerResilient e 0 ∧
      (e.hist (goodRun ℕ 1 0 false false).length).map encLabel = goodHist) ∧
    (∃ e : (ohMam Unit Unit (Fin 3) Bool false).Exec, e.Fair ∧ ServerResilient e 0 ∧
      (e.hist (goodRun (Tag Unit) (nextTag () ⊥) ⊥ true false).length).map encLabel = goodHist) ∧
    (∃ e : (ohSam' Unit (Fin 3) Bool false).Exec, e.Fair ∧ ServerResilient e 0 ∧
      (e.hist (goodRun ℕ 1 0 false true).length).map encLabel = goodHist) ∧
    (∃ e : (ohMam' Unit Unit (Fin 3) Bool false).Exec, e.Fair ∧ ServerResilient e 0 ∧
      (e.hist (goodRun (Tag Unit) (nextTag () ⊥) ⊥ true true).length).map encLabel = goodHist) :=
  ⟨fair_of_runOK sanity_ohSam, fair_of_runOK sanity_ohMam, fair_of_runOK sanity_ohSam',
    fair_of_runOK sanity_ohMam'⟩

end Podc.OhRAM
