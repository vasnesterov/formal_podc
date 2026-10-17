import Papers.PODC2024.HistoryIndependent.Perfect
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Podc.SharedMemory.Run
import Mathlib

/-!
# The impossibility results need two processes

With a single process, every object has a wait-free, perfectly history-independent
implementation that uses **no** shared memory: the process keeps the abstract state locally.
Hence the hypothesis `p ≠ p'` / `c ≠ r` of Proposition 14, Theorem 17, Theorem 20, … cannot be
dropped (the paper assumes `n ≥ 2` processes implicitly).
-/

namespace Cslib.SharedMemory

open List

variable {A : ObjSpec}

/-- Local states of the local (single-process) implementation: the abstract state and, if an
operation is pending, the operation. -/
structure LocalLoc (A : ObjSpec) where
  /-- The abstract state. -/
  st : A.State
  /-- The pending operation, if any. -/
  op : Option A.Op

/-- The single-process implementation without shared memory. -/
def localImpl (A : ObjSpec) (r₀ : A.Resp) :
    Impl A (Empty.elim : Empty → ObjSpec) Unit (LocalLoc A) where
  memInit e := e.elim
  locInit _ := ⟨A.init, none⟩
  invoke _ l o := ⟨l.st, some o⟩
  act _ l := match l.op with
    | some o => .ret (A.δ l.st o).2 ⟨(A.δ l.st o).1, none⟩
    | none => .ret r₀ l

namespace LocalImpl

variable {r₀ : A.Resp}

/-- Invariant: `L` linearizes the execution, its state is the local abstract state, and the
local pending operation is the pending operation of the process (not yet linearized). -/
structure Inv (α : List (Label Unit A)) (C : Config A (Empty.elim : Empty → ObjSpec) Unit (LocalLoc A))
    (L : List (OpId Unit × A.Op)) : Prop where
  lin : IsLinearization α L
  st : (C.loc ()).st = linState L
  op : (C.loc ()).op = C.pend ()
  notin : C.pend () ≠ none → curOp α () ∉ L.map Prod.fst

theorem inv_of_run {α : List (Label Unit A)}
    {C : Config A (Empty.elim : Empty → ObjSpec) Unit (LocalLoc A)}
    (h : (localImpl A r₀).run α = some C) : ∃ L, Inv α C L := by
  refine Impl.run_induction (Q := fun α C => ∃ L, Inv α C L)
    ⟨[], ⟨by simp, by simp, fun a ha => by simp [Completed] at ha,
      fun a b _ hb => by simp at hb, trivial⟩, rfl, rfl, fun h => by simp [Impl.initCfg] at h⟩
    (fun α C₀ ℓ C hα ⟨L, hI⟩ h => ?_) h
  cases ℓ with
  | inv p o =>
    cases p
    obtain ⟨h0, -, hpend, hloc, -⟩ := Impl.step_inv h
    have hlen : (opsOf α ()).length = (respsOf α ()).length := by
      rcases (localImpl A r₀).run_counts hα () with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd h0 h1
    refine ⟨L, ⟨hI.lin.append_inv () o, ?_, ?_, fun _ hm => ?_⟩⟩
    · rw [hloc]; simp [localImpl, hI.st]
    · rw [hloc, hpend]; simp [localImpl]
    · have := hI.lin.mem_invoked (by simpa using hm)
      simp [Invoked] at this; omega
  | tau p =>
    obtain ⟨-, -, i, -⟩ := Impl.step_tau h
    exact i.elim
  | ret p r =>
    cases p
    obtain ⟨h0, hpend, -, l, hact, hloc⟩ := Impl.step_ret h
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h0
    have hop : (C₀.loc ()).op = some o := by rw [hI.op, ho]
    simp only [localImpl, hop, Action.ret.injEq] at hact
    obtain ⟨hr, rfl⟩ := hact
    obtain ⟨-, hnc, hopx⟩ := Impl.run_pend_curOp hα ho
    refine ⟨L ++ [(curOp α (), o)], ⟨?_, ?_, ?_, ?_⟩⟩
    · exact (hI.lin.push hopx (hI.notin h0) hnc).append_ret L [] o rfl
        (by rw [← hr, hI.st]; rfl)
    · rw [hloc]; simp [hI.st]
    · rw [hloc, hpend]; simp
    · intro h'; rw [hpend] at h'; simp at h'

/-- The local implementation is wait-free, linearizable and perfectly HI (with a single
process, from no base objects at all). -/
theorem waitFree_perfectHI : (localImpl A r₀).WaitFree ∧ (localImpl A r₀).PerfectHI := by
  constructor
  · intro e p n _
    exact ⟨0, fun m _ heq => by
      have hs := e.step_eq m
      rw [heq] at hs
      obtain ⟨-, -, i, -⟩ := Impl.step_tau hs
      exact i.elim⟩
  · obtain ⟨h, hh⟩ := Impl.exists_linFun_of_run (fun α C hC => inv_of_run (r₀ := r₀) hC)
    exact ⟨h, fun α ⟨C, hC⟩ => (hh α C hC).lin, fun _ _ _ _ _ _ _ _ _ => funext fun e => e.elim⟩

end LocalImpl

/-- Proposition 14 (and the other impossibility results) fail with a single process: a
`3`-valued register has an obstruction-free (even wait-free) perfect HI implementation from base
objects with fewer than `3` states (there are none) when there is only one process. -/
theorem prop14_needs_two_processes :
    ∃ (I : Impl (register (Fin 3) 0) (Empty.elim : Empty → ObjSpec) Unit
        (LocalLoc (register (Fin 3) 0))),
      I.ObstructionFree ∧ I.WaitFree ∧ I.PerfectHI ∧
      ∀ j, Finite (Empty.elim j : ObjSpec).State ∧ Nat.card (Empty.elim j : ObjSpec).State < 3 :=
  ⟨localImpl (register (Fin 3) 0) (0 : Fin 3), LocalImpl.waitFree_perfectHI.1.obstructionFree,
    LocalImpl.waitFree_perfectHI.1, LocalImpl.waitFree_perfectHI.2, fun j => j.elim⟩

end Cslib.SharedMemory
