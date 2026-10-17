import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Objects.LLSC
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Foundations.Data.Finset.SumUpdate
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Mathlib

/-!
# A lock-free perfect-HI R-LLSC object from one atomic CAS (Algorithm 6)

Section 6.3 and Appendix D.2 of Attiya, Bender, Farach-Colton, Oshman, Schiller,
*History-Independent Concurrent Objects*, PODC 2024.

The R-LLSC object (`rllsc P V v₀`, state `(val, context) : V × Finset P`) is implemented from a
single CAS object `X` (`casObject (V × Finset P) (v₀, ∅)`). The paper stores the bit vector
`(v, c₁, …, cₙ) ∈ V × {0,1}ⁿ` in `X`; we store `(v, {pᵢ | cᵢ = 1}) : V × Finset P`, which is the
same encoding (the paper's translation `state(x)` of Lemma 40 becomes the identity).

Code for process `p` (`Loc` is the program counter together with the local variable `cur`):

* `LL`: `cur ← Read(X)`; `while ¬CAS(X, cur, (cur.val, cur.ctx ∪ {p})) do cur ← Read(X)`;
  return `cur.val` (Lines 1–6);
* `SC(v)`: `cur ← Read(X)`; `while p ∈ cur.ctx do (if CAS(X, cur, (v, ∅)) then return true;
  cur ← Read(X))`; return `false` (Lines 7–11);
* `VL`: `cur ← Read(X)`; return `p ∈ cur.ctx` (Lines 12–13);
* `RL`: `cur ← Read(X)`; `while p ∈ cur.ctx do (if CAS(X, cur, (cur.val, cur.ctx \ {p})) then
  return true; cur ← Read(X))`; return `true` (Lines 14–20);
* `Load`: `cur ← Read(X)`; return `cur.val` (Lines 21–22);
* `Store(v)`: `Write(X, (v, ∅))`; return `true` (Lines 23–24).

A process may only invoke `LL`/`VL`/`SC`/`RL` with its own id (`Impl.allowed`).

## Main results

* `RLLSCFromCAS.isLinFun` and `RLLSCFromCAS.mem_eq_linState`: Lemma 40 — the paper's
  linearization function `h_llsc` (`RLLSCFromCAS.lin`, defined by the paper's linearization
  points, `RLLSCFromCAS.IsLinStep`) is a linearization function, and the CAS value equals the
  abstract state of `h_llsc(α)`.
* `RLLSCFromCAS.perfectHI`, `RLLSCFromCAS.lockFree`: Theorem 28 (lock-freedom assumes finitely
  many processes, `[Fintype P]`; it is proved by a potential function that strictly decreases
  at every non-response step, without using the invariant).
* `RLLSCFromCAS.lemma29`: Lemma 29 (in our model, where responses are separate steps:
  infinitely many context-changing operations are *linearized*).
* `RLLSCFromCAS.lemma30`: Lemma 30 (in the form: once `p ∉ X.ctx` while `p`'s `SC`/`RL` is
  pending, `p` takes at most two more steps before returning).
* `RLLSCFromCAS.exLLSC_run`, `exLLSC_bad`, `exContention`: concrete executions (non-vacuity).
-/

namespace Cslib.SharedMemory

namespace RLLSCFromCAS

variable {P V : Type} [DecidableEq P] [DecidableEq V] {v₀ : V}

/-- The single base object: a CAS object holding `(val, context)` (the paper's
`(v, c₁, …, cₙ)`), initially `(v₀, ∅)`. -/
abbrev base (P V : Type) [DecidableEq P] [DecidableEq V] (v₀ : V) : Unit → ObjSpec :=
  fun _ => casObject (V × Finset P) (v₀, ∅)

/-- Local state of a process: the program counter, together with the local variable `cur`
where it is live. -/
inductive Loc (P V : Type) where
  /-- No pending operation. -/
  | idle
  /-- `LL`: about to read `X` (Line 1 / Line 4). -/
  | llRead
  /-- `LL`: about to `CAS(X, cur, (cur.val, cur.ctx ∪ {p}))` (Line 3). -/
  | llCAS (cur : V × Finset P)
  /-- `VL`: about to read `X` (Line 12). -/
  | vlRead
  /-- `SC(v)`: about to read `X` (Line 7 / Line 10). -/
  | scRead (v : V)
  /-- `SC(v)`: about to `CAS(X, cur, (v, ∅))` (Line 9). -/
  | scCAS (v : V) (cur : V × Finset P)
  /-- `RL`: about to read `X` (Line 14 / Line 18). -/
  | rlRead
  /-- `RL`: about to `CAS(X, cur, (cur.val, cur.ctx \ {p}))` (Line 17). -/
  | rlCAS (cur : V × Finset P)
  /-- `Load`: about to read `X` (Line 21). -/
  | loadRead
  /-- `Store(v)`: about to write `(v, ∅)` to `X` (Line 23). -/
  | store (v : V)
  /-- About to return `r`. -/
  | done (r : V ⊕ Bool)

/-- The local state right after invoking `o`. -/
def invokeLoc : RLLSCOp P V → Loc P V
  | .ll _ => .llRead
  | .vl _ => .vlRead
  | .sc _ v => .scRead v
  | .rl _ => .rlRead
  | .load => .loadRead
  | .store v => .store v

/-- The code of Algorithm 6 for process `p`. (Branches on impossible primitive responses, e.g. a
`Read` returning a Boolean, go to `idle`; they are never taken.) -/
def act (p : P) : Loc P V → Action (rllsc P V v₀) (base P V v₀) (Loc P V)
  | .idle => .ret (.inr false) .idle
  | .llRead => .access () CASOp.read fun r => match r with
      | Sum.inl cur => .llCAS cur
      | Sum.inr _ => .idle
  | .llCAS cur => .access () (CASOp.cas cur (cur.1, insert p cur.2)) fun r => match r with
      | Sum.inr true => .done (.inl cur.1)
      | _ => .llRead
  | .vlRead => .access () CASOp.read fun r => match r with
      | Sum.inl cur => .done (.inr (decide (p ∈ cur.2)))
      | Sum.inr _ => .idle
  | .scRead v => .access () CASOp.read fun r => match r with
      | Sum.inl cur => if p ∈ cur.2 then .scCAS v cur else .done (.inr false)
      | Sum.inr _ => .idle
  | .scCAS v cur => .access () (CASOp.cas cur (v, ∅)) fun r => match r with
      | Sum.inr true => .done (.inr true)
      | _ => .scRead v
  | .rlRead => .access () CASOp.read fun r => match r with
      | Sum.inl cur => if p ∈ cur.2 then .rlCAS cur else .done (.inr true)
      | Sum.inr _ => .idle
  | .rlCAS cur => .access () (CASOp.cas cur (cur.1, cur.2.erase p)) fun r => match r with
      | Sum.inr true => .done (.inr true)
      | _ => .rlRead
  | .loadRead => .access () CASOp.read fun r => match r with
      | Sum.inl cur => .done (.inl cur.1)
      | Sum.inr _ => .idle
  | .store v => .access () (CASOp.write (v, ∅)) fun _ => .done (.inr true)
  | .done r => .ret r .idle

variable (P V v₀) in
/-- **Algorithm 6**: a lock-free perfect-HI R-LLSC object from a single atomic CAS object. -/
def impl : Impl (rllsc P V v₀) (base P V v₀) P (Loc P V) where
  memInit _ := (v₀, ∅)
  locInit _ := .idle
  invoke _ _ o := invokeLoc o
  act := act
  allowed p o := RLLSCOp.proc o = none ∨ RLLSCOp.proc o = some p


/-! ## Basic step lemmas -/

/-- Configurations of Algorithm 6. -/
abbrev Cfg (P V : Type) [DecidableEq P] [DecidableEq V] (v₀ : V) :=
  Config (rllsc P V v₀) (base P V v₀) P (Loc P V)

variable (v₀) in
/-- The effect of the next internal step of `p` in local state `l` when `X` holds `m`: the new
local state and the new value of `X`. (Unchanged if `p` is about to return.) -/
def tauNext (p : P) (l : Loc P V) (m : V × Finset P) : Loc P V × (V × Finset P) :=
  match act (v₀ := v₀) p l with
  | .access _ o k => (k ((casObject (V × Finset P) (v₀, ∅)).δ m o).2,
      ((casObject (V × Finset P) (v₀, ∅)).δ m o).1)
  | .ret _ _ => (l, m)

lemma step_tau {C C' : Cfg P V v₀} {p : P} (h : (impl P V v₀).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ C'.pend = C.pend ∧ C.loc p ≠ .idle ∧ (∀ r, C.loc p ≠ .done r) ∧
      C'.mem () = (tauNext v₀ p (C.loc p) (C.mem ())).2 ∧
      C'.loc = Function.update C.loc p (tauNext v₀ p (C.loc p) (C.mem ())).1 := by
  obtain ⟨h0, h1, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  cases i
  have ha : act (v₀ := v₀) p (C.loc p) = .access () o k := hact
  refine ⟨h0, h1, ?_, ?_, ?_, ?_⟩
  · intro hl; rw [hl] at ha; simp [act] at ha
  · intro r hl; rw [hl] at ha; simp [act] at ha
  · rw [hmem]; simp [tauNext, ha]
  · rw [hloc]; simp [tauNext, ha]

section tauNext
variable (p : P) (m cur : V × Finset P) (v : V)

@[simp] lemma tauNext_llRead : tauNext v₀ p .llRead m = (.llCAS m, m) := rfl
@[simp] lemma tauNext_llCAS : tauNext v₀ p (.llCAS cur) m =
    if m = cur then (.done (.inl cur.1), (cur.1, insert p cur.2)) else (.llRead, m) := by
  by_cases h : m = cur <;> simp [tauNext, act, h]
@[simp] lemma tauNext_vlRead : tauNext v₀ p .vlRead m = (.done (.inr (decide (p ∈ m.2))), m) := rfl
@[simp] lemma tauNext_scRead : tauNext v₀ p (.scRead v) m =
    if p ∈ m.2 then (.scCAS v m, m) else (.done (.inr false), m) := by
  by_cases h : p ∈ m.2 <;> simp [tauNext, act, h]
@[simp] lemma tauNext_scCAS : tauNext v₀ p (.scCAS v cur) m =
    if m = cur then (.done (.inr true), (v, ∅)) else (.scRead v, m) := by
  by_cases h : m = cur <;> simp [tauNext, act, h]
@[simp] lemma tauNext_rlRead : tauNext v₀ p .rlRead m =
    if p ∈ m.2 then (.rlCAS m, m) else (.done (.inr true), m) := by
  by_cases h : p ∈ m.2 <;> simp [tauNext, act, h]
@[simp] lemma tauNext_rlCAS : tauNext v₀ p (.rlCAS cur) m =
    if m = cur then (.done (.inr true), (cur.1, cur.2.erase p)) else (.rlRead, m) := by
  by_cases h : m = cur <;> simp [tauNext, act, h]
@[simp] lemma tauNext_loadRead : tauNext v₀ p .loadRead m = (.done (.inl m.1), m) := rfl
@[simp] lemma tauNext_store : tauNext v₀ p (.store v) m = (.done (.inr true), (v, ∅)) := rfl

end tauNext

/-! ## The linearization points and the linearization function `h_llsc` -/

/-- The high-level operation `p` is executing in local state `l` (`none` if `p` is idle or about
to return). -/
def Loc.pendOp (p : P) : Loc P V → Option (RLLSCOp P V)
  | .llRead | .llCAS _ => some (.ll p)
  | .vlRead => some (.vl p)
  | .scRead v | .scCAS v _ => some (.sc p v)
  | .rlRead | .rlCAS _ => some (.rl p)
  | .loadRead => some .load
  | .store v => some (.store v)
  | .idle | .done _ => none

/-- The paper's linearization points (Section 6.3): the next step of `p`, in local state `l`
with `X = m`, is the linearization point of `p`'s current operation iff it is
* a successful `CAS` of `LL` (Line 3), `SC` (Line 9) or `RL` (Line 17);
* the `Read` of `VL` (Line 12) or `Load` (Line 21);
* a `Read` of `SC` (Lines 7, 10) or `RL` (Lines 14, 18) returning a value with `p ∉ ctx`;
* the `Write` of `Store` (Line 23). -/
def IsLinStep (p : P) : Loc P V → V × Finset P → Prop
  | .llCAS cur, m => m = cur
  | .vlRead, _ => True
  | .scRead _, m => p ∉ m.2
  | .scCAS _ cur, m => m = cur
  | .rlRead, m => p ∉ m.2
  | .rlCAS cur, m => m = cur
  | .loadRead, _ => True
  | .store _, _ => True
  | _, _ => False

/-- Lemma 40, case analysis (linearization point): the step linearizes `o` and has the effect
and response prescribed by the sequential specification. -/
lemma tauNext_of_linStep {p : P} {l : Loc P V} {m : V × Finset P} {o : RLLSCOp P V}
    (ho : l.pendOp p = some o) (hsc : ∀ v cur, l = .scCAS v cur → p ∈ cur.2)
    (hl : IsLinStep p l m) :
    tauNext v₀ p l m = (.done ((rllsc P V v₀).δ m o).2, ((rllsc P V v₀).δ m o).1) := by
  cases l <;> simp only [Loc.pendOp, Option.some.injEq, reduceCtorEq] at ho <;> subst ho <;>
    simp_all [IsLinStep, rllsc, Finset.erase_eq_of_notMem]

/-- Lemma 40, case analysis (other steps): the step does not change `X` and `p` keeps
executing `o`. -/
lemma tauNext_of_not_linStep {p : P} {l : Loc P V} {m : V × Finset P} {o : RLLSCOp P V}
    (ho : l.pendOp p = some o) (hl : ¬ IsLinStep p l m) :
    (tauNext v₀ p l m).2 = m ∧ (tauNext v₀ p l m).1.pendOp p = some o ∧
      ∀ v cur, (tauNext v₀ p l m).1 = .scCAS v cur → p ∈ cur.2 := by
  cases l <;> simp only [Loc.pendOp, Option.some.injEq, reduceCtorEq] at ho <;> subst ho <;>
    simp_all [IsLinStep, Loc.pendOp]

/-- Shorthand for the operation type of the implemented object. -/
abbrev Op (P V : Type) [DecidableEq P] (v₀ : V) := (rllsc P V v₀).Op

/-- Labels of executions of Algorithm 6. -/
abbrev Lbl (P V : Type) [DecidableEq P] (v₀ : V) := Label P (rllsc P V v₀)

open Classical in
/-- The operation (if any) whose linearization point is the step `ℓ` taken after the
execution `α`. -/
noncomputable def linPt (α : List (Lbl P V v₀)) : Lbl P V v₀ → List (OpId P × Op P V v₀)
  | .tau p => match (impl P V v₀).run α with
    | some C => match (C.loc p).pendOp p with
      | some o => if IsLinStep p (C.loc p) (C.mem ()) then [(curOp α p, o)] else []
      | none => []
    | none => []
  | _ => []

/-- `h_llsc` on reversed executions. -/
noncomputable def linRev : List (Lbl P V v₀) → List (OpId P × Op P V v₀)
  | [] => []
  | ℓ :: β => linRev β ++ linPt β.reverse ℓ

/-- The linearization function `h_llsc` of the paper (Section 6.3): the operations whose
linearization point (`IsLinStep`) occurs in `α`, ordered by their linearization points. -/
noncomputable def lin (α : List (Lbl P V v₀)) : List (OpId P × Op P V v₀) := linRev α.reverse

@[simp] lemma lin_nil : lin ([] : List (Lbl P V v₀)) = [] := rfl

lemma lin_append (α : List (Lbl P V v₀)) (ℓ : Lbl P V v₀) :
    lin (α ++ [ℓ]) = lin α ++ linPt α ℓ := by
  simp [lin, linRev]

/-! ## The invariant (Lemma 40) -/

/-- The per-process part of the invariant: the local state `l` and pending operation `pd` of
`p` are consistent with the linearization `L` of `α`. -/
structure ProcOK (α : List (Lbl P V v₀)) (L : List (OpId P × Op P V v₀)) (p : P) (l : Loc P V)
    (pd : Option (Op P V v₀)) : Prop where
  idle : l = .idle ↔ pd = none
  active : ∀ o, l.pendOp p = some o → pd = some o ∧
    curOp α p ∉ L.map Prod.fst ∧ opOf α (curOp α p) = some o
  sc : ∀ v cur, l = .scCAS v cur → p ∈ cur.2
  done : ∀ r, l = .done r → pd ≠ none ∧ ∃ L₁ L₂ o,
    L = L₁ ++ (curOp α p, o) :: L₂ ∧
    ((rllsc P V v₀).δ ((rllsc P V v₀).runOps (rllsc P V v₀).init (L₁.map Prod.snd)) o).2 = r

/-- The invariant of Lemma 40: `h_llsc(α)` is a linearization of `α`, the CAS value is its
abstract state, and every process is consistent with it. -/
structure Inv (α : List (Lbl P V v₀)) (C : Cfg P V v₀) : Prop where
  isLin : IsLinearization α (lin α)
  mem : C.mem () = linState (lin α)
  proc : ∀ p, ProcOK α (lin α) p (C.loc p) (C.pend p)

omit [DecidableEq V] in
lemma ProcOK.extend {α : List (Lbl P V v₀)} {L : List (OpId P × Op P V v₀)} {q : P}
    {l : Loc P V} {pd : Option (Op P V v₀)} (h : ProcOK α L q l pd) (ℓ : Lbl P V v₀)
    (hℓ : ℓ.proc ≠ q) (E : List (OpId P × Op P V v₀)) (hE : ∀ y ∈ E, y.1.1 ≠ q) :
    ProcOK (α ++ [ℓ]) (L ++ E) q l pd := by
  have hr : curOp (α ++ [ℓ]) q = curOp α q := curOp_append_of_proc_ne α hℓ
  refine ⟨h.idle, fun o ho => ?_, h.sc, fun r hr' => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h.active o ho
    have hinv : Invoked α (curOp α q) := Invoked.of_opOf_eq_some h3
    refine ⟨h1, ?_, ?_⟩
    · rw [hr]; simp only [List.map_append, List.mem_append, not_or]
      exact ⟨h2, fun hm => by obtain ⟨y, hy, hy'⟩ := List.mem_map.1 hm; exact hE y hy (by rw [hy'])⟩
    · rw [hr, opOf_append_of_invoked hinv]; exact h3
  · obtain ⟨h1, L₁, L₂, o, hs, hres⟩ := h.done r hr'
    exact ⟨h1, L₁, L₂ ++ E, o, by rw [hr, hs]; simp, hres⟩

omit [DecidableEq P] [DecidableEq V] in
lemma pendOp_invokeLoc {p : P} {o : RLLSCOp P V} (h : o.proc = none ∨ o.proc = some p) :
    (invokeLoc o).pendOp p = some o := by
  cases o <;> simp_all [invokeLoc, Loc.pendOp, RLLSCOp.proc]

/-- Lemma 40 (as an invariant): every reachable configuration satisfies `Inv`. -/
theorem inv_of_run {α : List (Lbl P V v₀)} {C : Cfg P V v₀}
    (h : (impl P V v₀).run α = some C) : Inv α C := by
  refine Impl.run_induction (Q := fun α C => Inv α C) ?_
    (fun α C₀ ℓ C hα hI h => ?_) h
  · refine ⟨⟨by simp, by simp, fun a ha => by simp [Completed] at ha,
      fun a b _ hb => by simp at hb, trivial⟩, rfl, fun p => ⟨by simp [Impl.initCfg, impl], ?_, ?_, ?_⟩⟩
    · intro o ho; simp [Impl.initCfg, impl, Loc.pendOp] at ho
    · intro v cur h; simp [Impl.initCfg, impl] at h
    · intro r h; simp [Impl.initCfg, impl] at h
  have hcnt := (impl P V v₀).run_counts hα
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hL : lin (α ++ [.inv p o]) = lin α := by rw [lin_append]; simp [linPt]
    have hlen : (opsOf α p).length = (respsOf α p).length := by
      rcases hcnt p with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd h0 h1
    refine ⟨by rw [hL]; exact hI.isLin.append_inv p o, by rw [hL, hmem]; exact hI.mem,
      fun q => ?_⟩
    rw [hL]
    by_cases hq : q = p
    · subst hq
      rw [hloc, hpend, Function.update_self, Function.update_self]
      have hr : curOp (α ++ [.inv q o]) q = curOp α q := curOp_append_inv α q q o
      refine ⟨by cases o <;> simp [impl, invokeLoc], fun o' ho' => ?_, ?_, ?_⟩
      · have ho : o' = o := by
          rw [show (impl P V v₀).invoke q (C₀.loc q) o = invokeLoc o from rfl,
            pendOp_invokeLoc hal] at ho'
          exact (Option.some.inj ho').symm
        subst ho
        refine ⟨rfl, fun hm => ?_, ?_⟩
        · have := hI.isLin.mem_invoked (by rw [hr] at hm; exact hm)
          simp [Invoked] at this; omega
        · simp [opOf, respsOf_append, opsOf_append, ← hlen]
      · intro v cur h; cases o <;> simp [impl, invokeLoc] at h
      · intro r h; cases o <;> simp [impl, invokeLoc] at h
    · rw [hloc, hpend, Function.update_of_ne hq, Function.update_of_ne hq]
      simpa using (hI.proc q).extend (.inv p o) (Ne.symm hq) [] (by simp)
  | tau p =>
    obtain ⟨h0, hpend, hidle, hdone, hmem, hloc⟩ := step_tau h
    have hP := hI.proc p
    obtain ⟨o, ho⟩ : ∃ o, (C₀.loc p).pendOp p = some o := by
      cases hl : C₀.loc p <;> simp_all [Loc.pendOp]
    obtain ⟨hpo, hx, hop⟩ := hP.active o ho
    have hr : curOp (α ++ [.tau p]) p = curOp α p := curOp_append_tau α p p
    by_cases hls : IsLinStep p (C₀.loc p) (C₀.mem ())
    · set x : OpId P := curOp α p with hxdef
      have hL : lin (α ++ [.tau p]) = lin α ++ [(x, o)] := by
        rw [lin_append]; simp [linPt, hα, ho, hls, x]
      have hT := tauNext_of_linStep (v₀ := v₀) ho hP.sc hls
      have hnc : ¬ Completed α x := by simp [Completed, x]
      refine ⟨by rw [hL]; exact (hI.isLin.push hop hx hnc).append_tau p, ?_, fun q => ?_⟩
      · rw [hL, hmem, hT, hI.mem, linState, linState, List.map_append,
          ObjSpec.runOps_append]
        rfl
      rw [hL]
      by_cases hq : q = p
      · subst hq
        rw [hloc, hpend, Function.update_self, hpo, hT]
        refine ⟨by simp, fun o' ho' => by simp [Loc.pendOp] at ho', fun v cur h => by simp at h,
          fun r' hr' => ⟨by simp, lin α, [], o, by rw [hr], ?_⟩⟩
        simp only [Loc.done.injEq] at hr'
        rw [← hr', hI.mem]; rfl
      · rw [hloc, hpend, Function.update_of_ne hq]
        exact (hI.proc q).extend (.tau p) (Ne.symm hq) _
          (by simp only [List.mem_singleton]; rintro y rfl; exact Ne.symm hq)
    · have hL : lin (α ++ [.tau p]) = lin α := by
        rw [lin_append]; simp [linPt, hα, ho, hls]
      obtain ⟨hm, ho', hsc'⟩ := tauNext_of_not_linStep (v₀ := v₀) ho hls
      refine ⟨by rw [hL]; exact hI.isLin.append_tau p, by rw [hL, hmem, hm, hI.mem],
        fun q => ?_⟩
      rw [hL]
      by_cases hq : q = p
      · subst hq
        rw [hloc, hpend, Function.update_self, hpo]
        refine ⟨⟨fun h => by rw [h] at ho'; simp [Loc.pendOp] at ho', by simp⟩,
          fun o' ho'' => ?_, hsc', fun r h => by rw [h] at ho'; simp [Loc.pendOp] at ho'⟩
        rw [ho'] at ho''; cases ho''
        refine ⟨rfl, by rw [hr]; exact hx, ?_⟩
        have hinv : Invoked α (curOp α q) := Invoked.of_opOf_eq_some hop
        rw [hr, opOf_append_of_invoked hinv]; exact hop
      · rw [hloc, hpend, Function.update_of_ne hq]
        simpa using (hI.proc q).extend (.tau p) (Ne.symm hq) [] (by simp)
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    have hP := hI.proc p
    have hL : lin (α ++ [.ret p r]) = lin α := by rw [lin_append]; simp [linPt]
    obtain ⟨hl, rfl⟩ : C₀.loc p = .done r ∧ l = .idle := by
      cases hl : C₀.loc p with
      | idle => exact absurd (hP.idle.1 hl) h0
      | done r' =>
        rw [hl] at hact
        simp only [impl, act, Action.ret.injEq] at hact
        exact ⟨by rw [hact.1], hact.2.symm⟩
      | _ => rw [hl] at hact; simp [impl, act] at hact
    obtain ⟨-, L₁, L₂, o, hs, hres⟩ := hP.done r hl
    refine ⟨by rw [hL]; exact hI.isLin.append_ret L₁ L₂ o hs hres,
      by rw [hL, hmem]; exact hI.mem, fun q => ?_⟩
    rw [hL]
    by_cases hq : q = p
    · subst hq
      rw [hloc, hpend, Function.update_self, Function.update_self]
      exact ⟨by simp, fun o' ho' => by simp [Loc.pendOp] at ho', fun v cur h => by simp at h,
        fun r h => by simp at h⟩
    · rw [hloc, hpend, Function.update_of_ne hq, Function.update_of_ne hq]
      simpa using (hI.proc q).extend (.ret p r) (Ne.symm hq) [] (by simp)

/-! ## Theorem 28: linearizability and perfect history independence -/

/-- **Lemma 40** (first part): `h_llsc` is a linearization function for Algorithm 6. -/
theorem isLinFun : (impl P V v₀).IsLinFun lin :=
  fun _ ⟨_, hC⟩ => (inv_of_run hC).isLin

/-- **Lemma 40** (second part): the value of the CAS object `X` is the abstract state of
`h_llsc(α)` (the paper's `state(mem(α)) = state(h_llsc(α))`, with the identity as `state`). -/
theorem mem_eq_linState {α : List (Lbl P V v₀)} {C : Cfg P V v₀}
    (h : (impl P V v₀).run α = some C) : C.mem () = linState (lin α) :=
  (inv_of_run h).mem

/-- **Theorem 28** (linearizability). -/
theorem linearizable : (impl P V v₀).Linearizable := ⟨lin, isLinFun⟩

/-- **Theorem 28** (perfect HI): Algorithm 6 is perfectly history independent, w.r.t. the
linearization function `h_llsc`. -/
theorem perfectHI : (impl P V v₀).PerfectHI := by
  refine ⟨lin, isLinFun, fun α α' C C' h1 h2 _ _ hl => ?_⟩
  funext i
  cases i
  rw [mem_eq_linState h1, mem_eq_linState h2, hl]

/-! ## Theorem 28: lock-freedom

Potential argument: every step except a response strictly decreases
`Ψ(C) = Σ_q w(C, q)`, where a process about to `CAS` with an up-to-date `cur` has the smallest
positive weight, a process about to read has a larger one, and a process about to `CAS` with a
stale `cur` (its `CAS` will fail) the largest one; finishing an operation (a successful `CAS` or a
`Write`) may make the `cur` of all other processes stale, which is paid for by the large drop
of the finishing process's weight. -/

/-- The progress measure of an active local state: `1` if about to `CAS` with `cur = X`,
`3` if about to `CAS` with a stale `cur`, `2` otherwise. -/
def phi : Loc P V → V × Finset P → ℕ
  | .idle, _ | .done _, _ => 0
  | .llCAS cur, m | .scCAS _ cur, m | .rlCAS cur, m => if m = cur then 1 else 3
  | _, _ => 2

/-- Weight of a local state (`K` is chosen larger than twice the number of processes). -/
def wLoc (K : ℕ) : Loc P V → V × Finset P → ℕ
  | .done _, _ => 0
  | .idle, _ => K + 3
  | l, m => K + phi l m

lemma wLoc_le (K : ℕ) (l : Loc P V) (m m' : V × Finset P) : wLoc K l m' ≤ wLoc K l m + 2 := by
  cases l <;> simp only [wLoc, phi] <;> (try split_ifs) <;> omega

lemma wLoc_active (K : ℕ) {l : Loc P V} (m : V × Finset P) (h1 : l ≠ .idle)
    (h2 : ∀ r, l ≠ .done r) : K + 1 ≤ wLoc K l m := by
  cases l <;> simp only [wLoc, phi] <;> (try split_ifs) <;> first | omega | simp_all

/-- One internal step either finishes the operation, or leaves `X` unchanged and decreases the
weight of the stepping process. -/
lemma tauNext_cases (K : ℕ) {p : P} {l : Loc P V} (m : V × Finset P) (h1 : l ≠ .idle)
    (h2 : ∀ r, l ≠ .done r) :
    (∃ r, (tauNext v₀ p l m).1 = .done r) ∨
      ((tauNext v₀ p l m).2 = m ∧ wLoc K (tauNext v₀ p l m).1 m < wLoc K l m) := by
  cases l with
  | idle => exact absurd rfl h1
  | done r => exact absurd rfl (h2 r)
  | llCAS cur | scCAS v cur | rlCAS cur =>
    by_cases h : m = cur <;> simp [h, wLoc, phi]
  | scRead v | rlRead =>
    by_cases h : p ∈ m.2 <;> simp [h, wLoc, phi]
  | _ => simp [wLoc, phi]

/-- The weight of process `q` in configuration `C`. -/
def wCfg (K : ℕ) (C : Cfg P V v₀) (q : P) : ℕ :=
  if C.pend q = none then K + 3 else wLoc K (C.loc q) (C.mem ())

/-- The potential `Ψ`. -/
def pot [Fintype P] (C : Cfg P V v₀) : ℕ := ∑ q, wCfg (2 * Fintype.card P) C q

/-- Every step that is not a response strictly decreases the potential. -/
lemma pot_lt [Fintype P] {C C' : Cfg P V v₀} {ℓ : Lbl P V v₀}
    (h : (impl P V v₀).step C ℓ = some C') (hℓ : ∀ p r, ℓ ≠ .ret p r) : pot C' < pot C := by
  cases ℓ with
  | ret p r => exact absurd rfl (hℓ p r)
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    apply Fintype.sum_lt_sum_of_eq_off p
    · intro q hq
      simp [wCfg, hpend, hloc, hmem, Function.update_of_ne hq]
    · simp only [wCfg, hpend, hloc, hmem, Function.update_self, h0]
      cases o <;> simp [impl, invokeLoc, wLoc, phi]
  | tau p =>
    obtain ⟨h0, hpend, hidle, hdone, hmem, hloc⟩ := step_tau h
    have hp : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    rcases tauNext_cases (v₀ := v₀) (2 * Fintype.card P) (C.mem ()) hidle hdone with ⟨r, hr⟩ | ⟨hm, hlt⟩
    · apply Fintype.sum_lt_sum_of_le_add (c := 2) p
      · intro q hq
        simp only [wCfg, hpend, hp q hq]
        split_ifs
        · omega
        · exact wLoc_le (2 * Fintype.card P) _ _ _
      · have h3 : wCfg (2 * Fintype.card P) C' p = 0 := by
          rw [wCfg, hpend, hloc, Function.update_self, hr]; simp [h0, wLoc]
        have h4 : wCfg (2 * Fintype.card P) C p = wLoc (2 * Fintype.card P) (C.loc p) (C.mem ()) := by simp [wCfg, h0]
        have := wLoc_active (2 * Fintype.card P) (C.mem ()) hidle hdone
        rw [smul_eq_mul]
        omega
    · have hm' : C'.mem = C.mem := by funext i; cases i; rw [hmem, hm]
      apply Fintype.sum_lt_sum_of_eq_off p
      · intro q hq; simp [wCfg, hpend, hp q hq, hm']
      · simp only [wCfg, hpend, h0, ite_false, hloc, Function.update_self, hm']
        exact hlt

/-- **Theorem 28** (lock-freedom), for finitely many processes: in every infinite execution,
infinitely many operations return. -/
theorem lockFree [Fintype P] : (impl P V v₀).LockFree :=
  (impl P V v₀).lockFree_of_potential pot fun _ _ _ _ _ hs hr => pot_lt hs hr

/-! ## Lemma 29 -/

/-- Context-changing operations (paper, before Lemma 29): `LL`, `RL`, `SC` and `Store`. -/
def RLLSCOp.ContextChanging : RLLSCOp P V → Prop
  | .ll _ | .rl _ | .sc _ _ | .store _ => True
  | .vl _ | .load => False

/-- A step that changes the CAS value is the linearization point of a context-changing
operation (a successful `CAS` of `LL`/`SC`/`RL`, or the `Write` of `Store`), which then is about
to return. -/
lemma mem_change {C C' : Cfg P V v₀} {q : P} {ℓ : Lbl P V v₀}
    (h : (impl P V v₀).step C ℓ = some C') (hm : C'.mem () ≠ C.mem ()) :
    ℓ = .tau q → (∃ o, (C.loc q).pendOp q = some o ∧ RLLSCOp.ContextChanging o ∧
      IsLinStep q (C.loc q) (C.mem ())) ∧ ∃ r, C'.loc q = .done r := by
  rintro rfl
  obtain ⟨-, -, hidle, hdone, hmem, hloc⟩ := step_tau h
  rw [hloc, Function.update_self]
  rw [hmem] at hm
  cases hl : C.loc q with
  | idle => exact absurd hl hidle
  | done r => exact absurd hl (hdone r)
  | llCAS cur | scCAS v cur | rlCAS cur =>
    rw [hl] at hm
    by_cases h' : C.mem () = cur <;> simp_all [Loc.pendOp, RLLSCOp.ContextChanging, IsLinStep]
  | scRead v | rlRead =>
    rw [hl] at hm
    by_cases h' : q ∈ (C.mem ()).2 <;> simp_all
  | store v => simp [Loc.pendOp, RLLSCOp.ContextChanging, IsLinStep]
  | _ => rw [hl] at hm; simp at hm

/-- A step of `p` that does not change `X` decreases `phi` of `p`. -/
lemma phi_tauNext_lt {p : P} {l : Loc P V} {m : V × Finset P} (h1 : l ≠ .idle)
    (h2 : ∀ r, l ≠ .done r) (hm : (tauNext v₀ p l m).2 = m) :
    phi (tauNext v₀ p l m).1 m < phi l m := by
  cases l with
  | idle => exact absurd rfl h1
  | done r => exact absurd rfl (h2 r)
  | llCAS cur | scCAS v cur | rlCAS cur =>
    by_cases h : m = cur <;> simp [h, phi]
  | scRead v | rlRead =>
    by_cases h : p ∈ m.2 <;> simp [h, phi]
  | _ => simp [phi]

/-- **Lemma 29**: if a process `p` with a pending operation (that never returns) takes infinitely
many steps, then the CAS value changes infinitely often, i.e. (`mem_change`) infinitely many
context-changing operations are linearized. (The paper says "return"; in our model a response
is a separate step that may never be scheduled, so we count linearization points.) -/
theorem lemma29 (e : (impl P V v₀).InfExec) (p : P) (n : ℕ)
    (hpend : ∀ m ≥ n, (e.cfg m).pend p ≠ none) (hsteps : ∀ N, ∃ m ≥ N, e.lbl m = .tau p) :
    ∀ N, ∃ m ≥ N, (e.cfg (m + 1)).mem () ≠ (e.cfg m).mem () := by
  intro N
  by_contra hcon
  push Not at hcon
  set N' := max N n
  let ph : ℕ → ℕ := fun m => phi ((e.cfg m).loc p) ((e.cfg m).mem ())
  have hstep : ∀ m ≥ N', ph (m + 1) ≤ ph m ∧ (e.lbl m = .tau p → ph (m + 1) < ph m) := by
    intro m hm
    have hs := e.step_eq m
    have hmem := hcon m (by omega)
    by_cases hq : (e.lbl m).proc = p
    · cases hl : e.lbl m with
      | inv q o =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (Impl.step_inv hs).1 (hpend m (by omega))
      | ret q r =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (by simp [(Impl.step_ret hs).2.1]) (hpend (m + 1) (by omega))
      | tau q =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        obtain ⟨-, -, hidle, hdone, hm', hloc⟩ := step_tau hs
        have hlt : ph (m + 1) < ph m := by
          simp only [ph, hloc, Function.update_self, hmem]
          exact phi_tauNext_lt hidle hdone (by rw [← hm', hmem])
        exact ⟨hlt.le, fun _ => hlt⟩
    · have := (Impl.step_other hs hq).1
      refine ⟨by simp only [ph, this, hmem]; rfl, fun h => by rw [h] at hq; exact absurd rfl hq⟩
  have hmono : ∀ m ≥ N', ∀ k, ph (m + k) ≤ ph m := by
    intro m hm k
    induction k with
    | zero => rfl
    | succ k ih => exact ((hstep (m + k) (by omega)).1).trans ih
  have key : ∀ v m, N' ≤ m → ph m ≤ v → False := by
    intro v
    induction v with
    | zero =>
      intro m hm hv
      obtain ⟨m', hm', hl⟩ := hsteps m
      have h1 := hmono m hm (m' - m)
      rw [show m + (m' - m) = m' by omega] at h1
      have := (hstep m' (by omega)).2 hl
      omega
    | succ v ih =>
      intro m hm hv
      obtain ⟨m', hm', hl⟩ := hsteps m
      have h1 := hmono m hm (m' - m)
      rw [show m + (m' - m) = m' by omega] at h1
      have := (hstep m' (by omega)).2 hl
      exact ih (m' + 1) (by omega) (by omega)
  exact key _ N' le_rfl le_rfl

/-! ## Lemma 30 -/

/-- Local states of a process executing `SC`/`RL`, or about to return. -/
def SCRLLoc : Loc P V → Prop
  | .scRead _ | .scCAS _ _ | .rlRead | .rlCAS _ | .done _ => True
  | _ => False

/-- Upper bound on the number of remaining internal steps of an `SC`/`RL` once `p ∉ ctx`. -/
def mu : Loc P V → ℕ
  | .scCAS _ _ | .rlCAS _ => 2
  | .scRead _ | .rlRead => 1
  | _ => 0

/-- Steps of other processes never add `p` to the context. -/
lemma notMem_tauNext_other {p q : P} (l : Loc P V) {m : V × Finset P} (hq : q ≠ p)
    (hp : p ∉ m.2) : p ∉ (tauNext v₀ q l m).2.2 := by
  classical
  cases l with
  | llCAS cur | scCAS v cur | rlCAS cur =>
    by_cases h : m = cur
    · subst h; simp [hp, Ne.symm hq, Finset.mem_erase]
    · simp [h, hp]
  | scRead v | rlRead => by_cases h : q ∈ m.2 <;> simp [h, hp]
  | idle | done r => simpa [tauNext, act] using hp
  | _ => simp [hp]

/-- The invariant of Lemma 30 for process `p`. -/
def Good30 (p : P) (C : Cfg P V v₀) : Prop :=
  C.pend p ≠ none ∧ p ∉ (C.mem ()).2 ∧ SCRLLoc (C.loc p)

lemma good30_step {p : P} {C C' : Cfg P V v₀} {ℓ : Lbl P V v₀} (hG : Good30 p C)
    (h : (impl P V v₀).step C ℓ = some C') (hℓ : ∀ r, ℓ ≠ .ret p r) :
    Good30 p C' ∧ mu (C'.loc p) + (if ℓ.proc = p then 1 else 0) ≤ mu (C.loc p) := by
  obtain ⟨h0, hp, hl⟩ := hG
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv h).1 h0
    | ret q r => simp only [Label.proc] at hq; subst hq; exact absurd rfl (hℓ r)
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, hpend, hidle, hdone, hmem, hloc⟩ := step_tau h
      simp only [Good30, hpend, hmem, hloc, Function.update_self, Label.proc, ite_true]
      cases hc : C.loc q with
      | scCAS v cur | rlCAS cur =>
        by_cases h' : C.mem () = cur
        · subst h'; simp [h0, mu, SCRLLoc]
        · simp [h', h0, hp, mu, SCRLLoc]
      | scRead v | rlRead => simp [h0, hp, mu, SCRLLoc]
      | done r => exact absurd hc (hdone r)
      | _ => rw [hc] at hl; simp [SCRLLoc] at hl
  · obtain ⟨h1, h2⟩ := Impl.step_other h hq
    simp only [Good30, h1, h2, hq, ite_false, add_zero, le_refl, and_true]
    refine ⟨h0, ?_, hl⟩
    cases ℓ with
    | inv q o => rw [(Impl.step_inv h).2.2.2.2]; exact hp
    | ret q r => rw [(Impl.step_ret h).2.2.1]; exact hp
    | tau q =>
      rw [(step_tau h).2.2.2.2.1]
      exact notMem_tauNext_other _ hq hp

lemma good30_run {p : P} {β : List (Lbl P V v₀)} {C C' : Cfg P V v₀} (hG : Good30 p C)
    (h : (impl P V v₀).runFrom C β = some C') (hret : ∀ r, Label.ret p r ∉ β) :
    β.countP (fun ℓ => decide (ℓ.proc = p)) + mu (C'.loc p) ≤ mu (C.loc p) := by
  induction β generalizing C with
  | nil => simp at h; subst h; simp
  | cons ℓ β ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (impl P V v₀).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have hℓ : ∀ r, ℓ ≠ .ret p r := fun r he => hret r (by simp [he])
      obtain ⟨hG1, hmu⟩ := good30_step hG hs hℓ
      have := ih hG1 h (fun r hr => hret r (by simp [hr]))
      rw [List.countP_cons]
      by_cases hq : ℓ.proc = p
      · simp [hq] at hmu ⊢; omega
      · simp [hq] at hmu ⊢; omega

/-- **Lemma 30**: let `p` have a pending `SC` or `RL` in a reachable configuration `C` in which
`p ∉ ctx` (this holds, by Lemma 40, right after the linearization point of a successful `SC` or
`Store` invoked after `p`'s operation, since these reset the context, and remains true until
`p`'s operation returns). Then in every extension `β` of `C` in which `p`'s operation does not
return, `p` takes at most two steps; i.e. `p`'s operation returns within at most three steps
of `p`. -/
theorem lemma30 {α : List (Lbl P V v₀)} {C : Cfg P V v₀} (hα : (impl P V v₀).run α = some C)
    {p : P} (hop : (∃ v, C.pend p = some (.sc p v)) ∨ C.pend p = some (.rl p))
    (hctx : p ∉ (C.mem ()).2) {β : List (Lbl P V v₀)} {C' : Cfg P V v₀}
    (h : (impl P V v₀).runFrom C β = some C') (hret : ∀ r, Label.ret p r ∉ β) :
    β.countP (fun ℓ => decide (ℓ.proc = p)) ≤ 2 := by
  have hP := (inv_of_run hα).proc p
  have hG : Good30 p C := by
    refine ⟨by rcases hop with ⟨v, h⟩ | h <;> simp [h], hctx, ?_⟩
    cases hl : C.loc p with
    | idle =>
      have := hP.idle.1 hl
      rcases hop with ⟨v, h⟩ | h <;> simp [h] at this
    | done r => trivial
    | scRead v | scCAS v cur | rlRead | rlCAS cur => trivial
    | _ =>
      rw [hl] at hP
      have := (hP.active _ rfl).1
      rcases hop with ⟨v, h⟩ | h <;> simp [h] at this
  have := good30_run hG h hret
  have hmu : mu (C.loc p) ≤ 2 := by cases C.loc p <;> simp [mu]
  omega

/-! ## Non-vacuity -/

/-- A concrete execution with two processes and Boolean values: process `0` performs `LL`
(returning `false`) and then a successful `SC(true)`. -/
def exLLSC : List (Lbl (Fin 2) Bool false) :=
  [.inv 0 (.ll 0), .tau 0, .tau 0, .ret 0 (.inl false),
   .inv 0 (.sc 0 true), .tau 0, .tau 0, .ret 0 (.inr true)]

/-- `exLLSC` is an execution of Algorithm 6, ending with `X = (true, ∅)`. -/
theorem exLLSC_run : ∃ C, (impl (Fin 2) Bool false).run exLLSC = some C ∧
    C.mem () = (true, ∅) := by
  simp [exLLSC, Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, impl, act, invokeLoc,
    RLLSCOp.proc, Function.update]

/-- Sanity check: in the same schedule, `SC` cannot return `false`. -/
theorem exLLSC_bad : (impl (Fin 2) Bool false).run
    [.inv 0 (.ll 0), .tau 0, .tau 0, .ret 0 (.inl false),
     .inv 0 (.sc 0 true), .tau 0, .tau 0, .ret 0 (.inr false)] = none := by
  simp [Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, impl, act, invokeLoc,
    RLLSCOp.proc, Function.update]

/-- Contention: process `1`'s `LL` between process `0`'s `LL` and its `SC` read does not make
the `SC` fail (the context only gains `1`), and the `SC` succeeds and clears the context. -/
theorem exContention : ∃ C, (impl (Fin 2) Bool false).run
    [.inv 0 (.ll 0), .tau 0, .tau 0, .ret 0 (.inl false),
     .inv 0 (.sc 0 true), .tau 0,
     .inv 1 (.ll 1), .tau 1, .tau 1, .ret 1 (.inl false),
     .tau 0, .tau 0, .tau 0, .ret 0 (.inr true)] = some C ∧ C.mem () = (true, ∅) := by
  simp [Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, impl, act, invokeLoc,
    RLLSCOp.proc, Function.update]

end RLLSCFromCAS

end Cslib.SharedMemory
