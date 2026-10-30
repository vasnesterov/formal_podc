import Cslib.Computability.Distributed.SharedMemory.Model
import Cslib.Computability.Distributed.SharedMemory.LinPoints

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/MetaConfig.lean

/-!
# Meta-configuration tracking (soundness)

The *meta-configuration tracking* technique of Jayanti, Jayanti, Yavuz and Hernandez (POPL 2024)
proves linearizability by augmenting an implementation with a set `P` of *possibilities*: an
abstract state of the object together with, for each process, either `⊥` ("the current operation
of this process is not yet linearized") or the response its current operation got when it was
linearized. Each possibility must correspond to a linearization of the run so far; then
"`P ≠ ∅` is an invariant" implies linearizability.

This file makes the correspondence precise in CSLib's shared-memory model and proves that the
correspondence is preserved by the update rules of the technique, so that any augmentation built
from these rules is sound.

* `Poss A P` — a possibility: an abstract state `st` and flags `fl : P → Option A.Resp`.
* `Poss.Realizes α L p` — `L` is a linearization of `α` that ends in the abstract state `p.st`
  and assigns to the current operation instance of every process `π` the response `p.fl π`
  (`none` iff that instance is not in `L`).
* `Poss.Tracked α p` — some linearization of `α` realizes `p`.

Closure rules (the rules of the technique):
* `Poss.tracked_init` — the initial possibility is tracked by the empty execution;
* `Poss.Tracked.append_inv`, `Poss.Tracked.append_tau` — invocations and internal steps
  keep every possibility;
* `Poss.Tracked.lin`, `Poss.Tracked.linSeq` — linearizing pending, not yet linearized operations
  (one, or a duplicate-free sequence of them) gives tracked possibilities;
* `Poss.Tracked.append_ret` — a return with response `r` keeps the possibilities with flag `r`
  (and clears the flag): this is the *filter* rule;
* `Poss.linearizable_of_tracked` — the tracker theorem: if every execution has a tracked
  possibility, the implementation is linearizable.
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {P : Type}

/-- A possibility of a meta-configuration: an abstract state, and for each process the response of
its current operation if that operation is linearized (`none` otherwise). -/
@[ext]
structure Poss (A : ObjSpec) (P : Type) where
  /-- The abstract state. -/
  st : A.State
  /-- Linearization flags: `some r` if the current operation of the process is linearized with
  response `r`. -/
  fl : P → Option A.Resp

namespace Poss

variable [DecidableEq P]

/-- The initial possibility: initial state, nothing linearized. -/
def init : Poss A P := ⟨A.init, fun _ => none⟩

/-- Linearize operation `o` of process `π` in possibility `p`. -/
def lin (p : Poss A P) (π : P) (o : A.Op) : Poss A P :=
  ⟨(A.δ p.st o).1, Function.update p.fl π (some (A.δ p.st o).2)⟩

/-- Linearize the operations (given by `ops`, e.g. the pending operations of a configuration) of
a sequence of processes, in order. Processes without an operation are skipped. -/
def linSeq (ops : P → Option A.Op) (p : Poss A P) : List P → Poss A P
  | [] => p
  | π :: l => linSeq ops (match ops π with
      | some o => p.lin π o
      | none => p) l

@[simp] lemma linSeq_nil (ops : P → Option A.Op) (p : Poss A P) : p.linSeq ops [] = p := rfl

lemma linSeq_cons_some {ops : P → Option A.Op} (p : Poss A P) {π : P} {o : A.Op}
    (h : ops π = some o) (l : List P) : p.linSeq ops (π :: l) = (p.lin π o).linSeq ops l := by
  simp [linSeq, h]

lemma linSeq_append (ops : P → Option A.Op) (p : Poss A P) (l l' : List P) :
    p.linSeq ops (l ++ l') = (p.linSeq ops l).linSeq ops l' := by
  induction l generalizing p with
  | nil => rfl
  | cons π l ih => simp only [List.cons_append, linSeq, ih]

/-- Clear the flag of `π` (after its operation returned). -/
def clear (p : Poss A P) (π : P) : Poss A P := ⟨p.st, Function.update p.fl π none⟩

/-- `L` is a linearization of `α` realizing the possibility `p`. -/
def Realizes (α : List (Label P A)) (L : List (OpId P × A.Op)) (p : Poss A P) : Prop :=
  IsLinearization α L ∧ linState L = p.st ∧ ∀ π, A.respIn A.init L (curOp α π) = p.fl π

/-- The possibility `p` corresponds to some linearization of `α`. -/
def Tracked (α : List (Label P A)) (p : Poss A P) : Prop := ∃ L, Realizes α L p

lemma tracked_init : Tracked ([] : List (Label P A)) (init : Poss A P) :=
  ⟨[], isLinearization_nil, rfl, fun _ => rfl⟩

variable {α : List (Label P A)} {p : Poss A P}

lemma Tracked.append_inv (h : Tracked α p) (π : P) (o : A.Op) :
    Tracked (α ++ [.inv π o]) p := by
  obtain ⟨L, hL, hs, hf⟩ := h
  exact ⟨L, hL.append_inv π o, hs, fun π' => by rw [curOp_append_inv]; exact hf π'⟩

lemma Tracked.append_tau (h : Tracked α p) (π : P) : Tracked (α ++ [.tau π]) p := by
  obtain ⟨L, hL, hs, hf⟩ := h
  exact ⟨L, hL.append_tau π, hs, fun π' => by rw [curOp_append_tau]; exact hf π'⟩

variable {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι] {I : Impl A B P L}
  {C : Config A B P L}

/-- Linearizing the pending, not yet linearized operation of `π`. -/
lemma Tracked.lin (h : Tracked α p) (hrun : I.run α = some C) {π : P} {o : A.Op}
    (hp : C.pend π = some o) (hfl : p.fl π = none) : Tracked α (p.lin π o) := by
  obtain ⟨L, hL, hs, hf⟩ := h
  obtain ⟨-, hnc, hop⟩ := I.run_pend_curOp hrun hp
  have hx : curOp α π ∉ L.map Prod.fst := by
    rw [← ObjSpec.respIn_eq_none_iff (A := A) (q := A.init), hf, hfl]
  refine ⟨L ++ [(curOp α π, o)], hL.push hop hx hnc, ?_, fun π' => ?_⟩
  · simp [Poss.lin, linState_append, hs]
  · by_cases hπ : π' = π
    · subst hπ
      rw [ObjSpec.respIn_concat_self hx]
      rw [show A.runOps A.init (L.map Prod.snd) = linState L from rfl, hs]; simp [Poss.lin]
    · have hne : curOp α π' ∉ [(curOp α π, o)].map Prod.fst := by
        simp [curOp, hπ]
      rw [ObjSpec.respIn_append_of_not_mem_right hne, hf π']
      simp [Poss.lin, Function.update_of_ne hπ]

/-- Linearizing a duplicate-free sequence of pending, not yet linearized operations. -/
lemma Tracked.linSeq (h : Tracked α p) (hrun : I.run α = some C) {l : List P}
    (hnd : l.Nodup) (hl : ∀ π ∈ l, C.pend π ≠ none ∧ p.fl π = none) :
    Tracked α (p.linSeq C.pend l) := by
  induction l generalizing p with
  | nil => exact h
  | cons π l ih =>
    obtain ⟨hpend, hfl⟩ := hl π (by simp)
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpend
    rw [linSeq_cons_some p ho]
    have hnd' := List.nodup_cons.1 hnd
    refine ih (h.lin hrun ho hfl) hnd'.2 (fun π' hπ' => ⟨(hl π' (by simp [hπ'])).1, ?_⟩)
    have hne : π' ≠ π := fun he => hnd'.1 (he ▸ hπ')
    simp [Poss.lin, Function.update_of_ne hne, (hl π' (by simp [hπ'])).2]

/-- The filter rule: when `π` returns `r`, possibilities in which `π`'s operation is linearized
with response `r` survive (with the flag of `π` cleared). -/
lemma Tracked.append_ret (h : Tracked α p) (hrun : I.run α = some C) {π : P} {r : A.Resp}
    (hpend : C.pend π ≠ none) (hfl : p.fl π = some r) :
    Tracked (α ++ [.ret π r]) (p.clear π) := by
  obtain ⟨L, hL, hs, hf⟩ := h
  have hcnt := I.run_pend_counts hrun hpend
  refine ⟨L, hL.append_ret_of_respIn (by rw [hf π, hfl]), hs, fun π' => ?_⟩
  by_cases hπ : π' = π
  · subst hπ
    rw [curOp_append_ret_self]
    simp only [Poss.clear, Function.update_self]
    rw [ObjSpec.respIn_eq_none_iff]
    intro hm
    have := hL.mem_invoked hm
    simp only [Invoked] at this; omega
  · rw [curOp_append_ret_of_ne α r (Ne.symm hπ), hf π']
    simp [Poss.clear, Function.update_of_ne hπ]

/-- **The tracker theorem** (soundness of meta-configuration tracking): if every finite execution
has a tracked possibility, the implementation is linearizable. -/
theorem linearizable_of_tracked (h : ∀ α C, I.run α = some C → ∃ p : Poss A P, Tracked α p) :
    I.Linearizable :=
  I.linearizable_of_run fun α C hC => by
    obtain ⟨p, L, hL, -⟩ := h α C hC
    exact ⟨L, hL⟩

end Poss

end Cslib.SharedMemory
