import Papers.PODC2024.HistoryIndependent.UniversalWF

/-!
# Theorem 32: Algorithm 5 over Algorithm 6, flattened

Section 6.4 of Attiya, Bender, Farach-Colton, Oshman, Schiller, *History-Independent Concurrent
Objects*, PODC 2024.

Theorem 32 is an existence claim: *there is* a linearizable, wait-free, state-quiescent HI
universal implementation from atomic CAS objects. We prove it for the **flattened**
implementation `flat A n`: Algorithm 5 in which every operation on an R-LLSC object is inlined as
the code of Algorithm 6 on a CAS object holding the R-LLSC state `(val, context)` (one CAS object
per R-LLSC object `head`, `announce[j]`).

## The `∥` construct

Lines 6, 18 and 25 of Algorithm 5 run an `LL` (left) in parallel with a waiting loop (right),
"with some unspecified but finite number of steps taken on each side before the process
switches". We fix one admissible schedule: **strict alternation**, starting with the left side,
one step of the left side (a `Read` or a `CAS` of Algorithm 6's `LL`), then one step of the right
side (a `Load`), and so on, until one side finishes:

* the left side finishes when its `CAS` succeeds (the `LL` returns); the right side is then
  abandoned (it only performed `Load`s);
* the right side finishes when its waiting condition holds; then the left `LL` is abandoned, and
  the right side runs to completion (line 18R.2's `RL(announce[j])` is executed with the left
  side suspended forever).

Under this schedule an abandoned `LL` never took effect (its only effect is the successful
`CAS`, which ends it), so the "pending forever" operation on the R-LLSC object does not matter.

The local state `FLoc` consists of the local state of Algorithm 5 (`l5`, whose program counter is
the R-LLSC operation in progress), the stage `st` of the current Algorithm 6 operation (`true`:
`cur` has been read, next step is the `CAS`), the turn `turn` of the `∥` (`true`: right side) and
the local variable `cur` of Algorithm 6 (one copy per object type).

## Modelling details

* The CAS objects (`casC`) decide equality classically, so that no decidable equality on the
  abstract object's states, operations and responses is needed.
* In Algorithm 6's `SC` and `RL` the loop condition `cur.context[i] = 1` is evaluated after the
  `Read` (as in the paper) and re-evaluated before the `CAS` (it always holds there).
* Line 18R.2 (`RL(announce[j])` after the right-hand side of line 18 ends) is the program counter
  `PC.rl18 j` of Algorithm 5 (unreachable in the atomic `alg5`).

## Main results

* `flat_tau`: every step is a stutter, a step of `alg5` (at the linearization point of an
  Algorithm 6 operation, Lemma 40), or the end of a right-hand side of `∥` (`Jump`).
* `flat_invL`: the invariant of Algorithm 5 (`InvL`, extended to the jumps by `InvC.jump`) holds
  for the abstract configuration `absC C` of every reachable configuration.
* `flat_isLinFun`, `flat_stateQuiescentHI`: linearizability and state-quiescent HI (Theorem 32).
* Wait-freedom: `UniversalFlatWF.flat_waitFree`; everything together: `theorem32`.
-/

namespace Cslib.SharedMemory

namespace Universal

open List

variable (A : ObjSpec) (n : ℕ)

/-- An atomic compare-and-swap object over `V` (as `casObject`, with classical equality
decision, so that no decidable equality on the abstract object's states is needed). -/
@[reducible] noncomputable def casC (V : Type) (v₀ : V) : ObjSpec where
  State := V
  Op := CASOp V
  Resp := V ⊕ Bool
  init := v₀
  δ q
    | .read => (q, .inl q)
    | .write v => (v, .inr true)
    | .cas old new => @ite _ (q = old) (Classical.propDecidable _) (new, .inr true) (q, .inr false)

/-- The base objects of the flattened implementation: one CAS object per R-LLSC object, holding
the R-LLSC state `(val, context)` (Algorithm 6's encoding). -/
@[reducible] noncomputable def BF (i : Obj n) : ObjSpec :=
  casC (B A n i).State (B A n i).init

/-- Local state of the flattened implementation. -/
structure FLoc where
  l5 : Loc A n
  st : Bool
  turn : Bool
  curH : HeadVal A n × Finset (Fin n)
  curA : AnnVal A × Finset (Fin n)

variable {A n}

/-- `a ∈ R`. -/
def isResp : AnnVal A → Bool
  | some (.inr _) => true
  | _ => false

/-- One step of Algorithm 6 for the R-LLSC operation `o` with continuation `k` (the code of
Algorithm 5 after the operation returns): the CAS primitive to apply and the new local state as a
function of its response. `cur` is Algorithm 6's local variable, `setCur` stores a new value. -/
def stepOp {V : Type} (o : RLLSCOp (Fin n) V) (k : V ⊕ Bool → Loc A n)
    (fl : FLoc A n) (cur : V × Finset (Fin n)) (setCur : FLoc A n → V × Finset (Fin n) → FLoc A n) :
    CASOp (V × Finset (Fin n)) × ((V × Finset (Fin n)) ⊕ Bool → FLoc A n) :=
  match o with
  | .load => (.read, fun
      | .inl s => { fl with l5 := k (.inl s.1), st := false, turn := false }
      | .inr _ => fl)
  | .store v => (.write (v, ∅), fun _ => { fl with l5 := k (.inr true), st := false, turn := false })
  | .vl q => (.read, fun
      | .inl s => { fl with l5 := k (.inr (decide (q ∈ s.2))), st := false, turn := false }
      | .inr _ => fl)
  | .ll q =>
    if fl.st then
      (.cas cur (cur.1, insert q cur.2), fun
        | .inr true => { fl with l5 := k (.inl cur.1), st := false, turn := false }
        | _ => { fl with st := false, turn := true })
    else
      (.read, fun
        | .inl s => { setCur fl s with st := true, turn := true }
        | .inr _ => fl)
  | .sc q v =>
    if fl.st ∧ q ∈ cur.2 then
      (.cas cur (v, ∅), fun
        | .inr true => { fl with l5 := k (.inr true), st := false, turn := false }
        | _ => { fl with st := false })
    else
      (.read, fun
        | .inl s => if q ∈ s.2 then { setCur fl s with st := true }
          else { fl with l5 := k (.inr false), st := false, turn := false }
        | .inr _ => fl)
  | .rl q =>
    if fl.st ∧ q ∈ cur.2 then
      (.cas cur (cur.1, cur.2.erase q), fun
        | .inr true => { fl with l5 := k (.inr true), st := false, turn := false }
        | _ => { fl with st := false })
    else
      (.read, fun
        | .inl s => if q ∈ s.2 then { setCur fl s with st := true }
          else { fl with l5 := k (.inr true), st := false, turn := false }
        | .inr _ => fl)

/-- Store `cur` for `head`. -/
def setCurH (fl : FLoc A n) (c : HeadVal A n × Finset (Fin n)) : FLoc A n := { fl with curH := c }
/-- Store `cur` for `announce[j]`. -/
def setCurA (fl : FLoc A n) (c : AnnVal A × Finset (Fin n)) : FLoc A n := { fl with curA := c }

/-- Right side of line 6: `wait until Load(announce[i]) ∈ R; goto 24`. -/
def right6 (p : Fin n) (fl : FLoc A n) : Action A (BF A n) (FLoc A n) :=
  .access (.ann p) .read fun
    | .inl s => if isResp s.1 then
        { fl with l5 := { fl.l5 with pc := .resp }, st := false, turn := false }
      else { fl with turn := false }
    | .inr _ => fl

/-- Right side of line 18: `wait until Load(announce[i]) ∈ R; RL(announce[j]); goto 24`. -/
def right18 (p : Fin n) (fl : FLoc A n) : Action A (BF A n) (FLoc A n) :=
  .access (.ann p) .read fun
    | .inl s => if isResp s.1 then
        { fl with l5 := { fl.l5 with pc := match fl.l5.hd.2 with
            | some (_, j) => .rl18 j
            | none => .resp }, st := false, turn := false }
      else { fl with turn := false }
    | .inr _ => fl

/-- Right side of line 25: `wait until Load(head) ≠ ⟨_, ⟨_, i⟩⟩; goto 27`. -/
def right25 (p : Fin n) (r : A.Resp) (fl : FLoc A n) : Action A (BF A n) (FLoc A n) :=
  .access .head .read fun
    | .inl s => if ownerIs p s.1.2 then { fl with turn := false }
      else { fl with l5 := { fl.l5 with pc := .rlHead r }, st := false, turn := false }
    | .inr _ => fl

/-- The left side / ordinary code: Algorithm 5's next R-LLSC operation, run by Algorithm 6. -/
def leftAct (p : Fin n) (fl : FLoc A n) : Action A (BF A n) (FLoc A n) :=
  match act p fl.l5 with
  | .access .head o k =>
    .access .head (stepOp o k fl fl.curH setCurH).1 (stepOp o k fl fl.curH setCurH).2
  | .access (.ann j) o k =>
    .access (.ann j) (stepOp o k fl fl.curA setCurA).1 (stepOp o k fl fl.curA setCurA).2
  | .ret r l => .ret r { fl with l5 := l, st := false, turn := false }

/-- The code of process `p` in the flattened implementation. -/
def fact (p : Fin n) (fl : FLoc A n) : Action A (BF A n) (FLoc A n) :=
  if fl.turn then
    match fl.l5.pc with
    | .llHead => right6 p fl
    | .llAnn => right18 p fl
    | .llHead2 r => right25 p r fl
    | _ => leftAct p fl
  else leftAct p fl

variable (A n) in
/-- **The flattened implementation**: Algorithm 5 with R-LLSC objects implemented by
Algorithm 6, from `n + 1` atomic CAS objects. -/
noncomputable def flat [DecidablePred A.ReadOnly] : Impl A (BF A n) (Fin n) (FLoc A n) where
  memInit := (alg5 A n).memInit
  locInit p := ⟨(alg5 A n).locInit p, false, false, ((A.init, none), ∅), (none, ∅)⟩
  invoke p fl o := { fl with l5 := (alg5 A n).invoke p fl.l5 o, st := false, turn := false }
  act := fact

/-! ## One step of Algorithm 6 simulates an atomic R-LLSC operation or nothing -/

section StepOp

variable {V : Type}

/-- **A step of Algorithm 6** either changes neither the CAS object nor the Algorithm 5 state
(a stutter: a `Read` that is not the linearization point, or a failed `CAS`), or it changes both
exactly as the atomic R-LLSC operation would (its linearization point). -/
lemma stepOp_spec (o : RLLSCOp (Fin n) V) (k : V ⊕ Bool → Loc A n) (fl : FLoc A n)
    (cur : V × Finset (Fin n)) (setCur : FLoc A n → V × Finset (Fin n) → FLoc A n)
    (hset : ∀ f c, (setCur f c).l5 = f.l5)
    (v₀ s : V × Finset (Fin n)) (w₀ : V) :
    (((casC (V × Finset (Fin n)) v₀).δ s (stepOp o k fl cur setCur).1).1 = s ∧
      ((stepOp o k fl cur setCur).2
        ((casC (V × Finset (Fin n)) v₀).δ s (stepOp o k fl cur setCur).1).2).l5 = fl.l5) ∨
    (((casC (V × Finset (Fin n)) v₀).δ s (stepOp o k fl cur setCur).1).1 =
        ((rllsc (Fin n) V w₀).δ s o).1 ∧
      ((stepOp o k fl cur setCur).2
        ((casC (V × Finset (Fin n)) v₀).δ s (stepOp o k fl cur setCur).1).2).l5 =
        k ((rllsc (Fin n) V w₀).δ s o).2) := by
  cases o with
  | load => right; simp [stepOp]
  | store v => right; simp [stepOp]
  | vl q => right; simp [stepOp]
  | ll q =>
    cases hs : fl.st
    · left; simp [stepOp, hs, hset]
    · by_cases h : s = cur
      · right; subst h; simp [stepOp, hs]
      · left; simp [stepOp, hs, h]
  | sc q v =>
    by_cases hs : fl.st = true ∧ q ∈ cur.2
    · by_cases h : s = cur
      · right; subst h; simp [stepOp, hs]
      · left; simp [stepOp, hs, h]
    · by_cases h : q ∈ s.2
      · left; simp [stepOp, hs, h, hset]
      · right; simp [stepOp, hs, h]
  | rl q =>
    by_cases hs : fl.st = true ∧ q ∈ cur.2
    · by_cases h : s = cur
      · right; subst h; simp [stepOp, hs]
      · left; simp [stepOp, hs, h]
    · by_cases h : q ∈ s.2
      · left; simp [stepOp, hs, h, hset]
      · right; simp [stepOp, hs, h]

end StepOp

/-! ## The abstraction to Algorithm 5 with atomic R-LLSC objects -/

/-- The abstract configuration: Algorithm 5's local states, the same pending operations, and
the same memory (the CAS objects hold exactly the R-LLSC states). -/
def absC (C : Config A (BF A n) (Fin n) (FLoc A n)) : Config A (B A n) (Fin n) (Loc A n) :=
  ⟨fun q => (C.loc q).l5, C.pend, C.mem⟩

/-- The three ways the right-hand side of `∥` ends (lines 6R, 18R, 25R), as transitions of
Algorithm 5's local state. -/
def Jump (p : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) (l' : Loc A n) : Prop :=
  ((D.loc p).pc = .llHead ∧ isResp (av D.mem p) = true ∧ l' = { D.loc p with pc := .resp }) ∨
  ((D.loc p).pc = .llAnn ∧ isResp (av D.mem p) = true ∧
    ∃ rsp j, (D.loc p).hd.2 = some (rsp, j) ∧ l' = { D.loc p with pc := .rl18 j }) ∨
  (∃ r, (D.loc p).pc = .llHead2 r ∧ ownerIs p (hv D.mem).2 = false ∧
    l' = { D.loc p with pc := .rlHead r })

variable [DecidablePred A.ReadOnly]

lemma alg5_step_tau_of_act {D : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} {i : Obj n}
    {o : (B A n i).Op} {k : (B A n i).Resp → Loc A n} (hp : D.pend p ≠ none)
    (ha : act p (D.loc p) = .access i o k) :
    (alg5 A n).step D (.tau p) = some { D with
      mem := Function.update D.mem i ((B A n i).δ (D.mem i) o).1,
      loc := Function.update D.loc p (k ((B A n i).δ (D.mem i) o).2) } := by
  simp only [Impl.step, hp, ↓reduceIte, alg5, ha]

lemma absC_eq_of {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n} {l : Loc A n}
    {M : Mem A n} {P : Fin n → Option A.Op} (hpend : C'.pend = P)
    (hlr : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (hl : (C'.loc p).l5 = l) (hm : C'.mem = M) :
    absC C' = { absC C with pend := P, mem := M, loc := Function.update (absC C).loc p l } := by
  simp only [absC, hpend, hm, Config.mk.injEq, and_true, true_and]
  funext q
  by_cases hq : q = p
  · subst hq; simp [hl]
  · simp [Function.update_of_ne hq, hlr q hq]

/-- `leftAct` when the next operation is on `head`. -/
lemma leftAct_head {p : Fin n} {fl : FLoc A n} {o : (B A n .head).Op}
    {k : (B A n .head).Resp → Loc A n} (h : act p fl.l5 = .access .head o k) :
    leftAct p fl = .access .head (stepOp o k fl fl.curH setCurH).1
      (stepOp o k fl fl.curH setCurH).2 := by
  simp only [leftAct, h]

/-- `leftAct` when the next operation is on `announce[j]`. -/
lemma leftAct_ann {p j : Fin n} {fl : FLoc A n} {o : (B A n (.ann j)).Op}
    {k : (B A n (.ann j)).Resp → Loc A n} (h : act p fl.l5 = .access (.ann j) o k) :
    leftAct p fl = .access (.ann j) (stepOp o k fl fl.curA setCurA).1
      (stepOp o k fl fl.curA setCurA).2 := by
  simp only [leftAct, h]

/-- **Simulation**: a step of the flattened implementation is a stutter (no change of the memory
or of Algorithm 5's local state), a step of Algorithm 5 with atomic R-LLSC objects (at the
linearization point of an Algorithm 6 operation), or the end of a right-hand side of `∥`. -/
theorem flat_tau {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n}
    (hloc5 : LocInv p (C.loc p).l5) (h : (flat A n).step C (.tau p) = some C') :
    C'.pend = C.pend ∧ (∀ q, q ≠ p → C'.loc q = C.loc q) ∧
    ((C'.mem = C.mem ∧ (C'.loc p).l5 = (C.loc p).l5) ∨
      (alg5 A n).step (absC C) (.tau p) = some (absC C') ∨
      (C'.mem = C.mem ∧ Jump p (absC C) (C'.loc p).l5)) := by
  obtain ⟨hp, hpend, i, o', k', hact, hmem, hloc⟩ := Impl.step_tau h
  have hlr : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
    rw [hloc]; exact Function.update_of_ne hq _ _
  have hlp : C'.loc p = k' ((BF A n i).δ (C.mem i) o').2 := by rw [hloc]; simp
  refine ⟨hpend, hlr, ?_⟩
  simp only [flat, fact] at hact
  have left : leftAct p (C.loc p) = .access i o' k' →
      (C'.mem = C.mem ∧ (C'.loc p).l5 = (C.loc p).l5) ∨
        (alg5 A n).step (absC C) (.tau p) = some (absC C') := by
    intro hL
    rcases hA : act p (C.loc p).l5 with ⟨i₀, o, k⟩ | ⟨r, l⟩
    · cases i₀ with
      | head =>
        rw [leftAct_head hA] at hL
        cases hL
        rcases stepOp_spec o k (C.loc p) (C.loc p).curH setCurH (fun _ _ => rfl)
          (B A n .head).init (C.mem .head) (A.init, none) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨by rw [hmem]; erw [h1]; simp, by rw [hlp]; exact h2⟩
        · right
          rw [alg5_step_tau_of_act (D := absC C) hp hA]
          congr 1
          refine (absC_eq_of hpend hlr (by rw [hlp]; exact h2) (by rw [hmem]; erw [h1]; rfl)).symm
      | ann j =>
        rw [leftAct_ann hA] at hL
        cases hL
        rcases stepOp_spec o k (C.loc p) (C.loc p).curA setCurA (fun _ _ => rfl)
          (B A n (.ann j)).init (C.mem (.ann j)) none with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨by rw [hmem]; erw [h1]; simp, by rw [hlp]; exact h2⟩
        · right
          rw [alg5_step_tau_of_act (D := absC C) hp hA]
          congr 1
          refine (absC_eq_of hpend hlr (by rw [hlp]; exact h2) (by rw [hmem]; erw [h1]; rfl)).symm
    · simp only [leftAct, hA] at hL; cases hL
  have lift : leftAct p (C.loc p) = .access i o' k' →
      (C'.mem = C.mem ∧ (C'.loc p).l5 = (C.loc p).l5) ∨
      (alg5 A n).step (absC C) (.tau p) = some (absC C') ∨
      (C'.mem = C.mem ∧ Jump p (absC C) (C'.loc p).l5) :=
    fun hL => (left hL).elim Or.inl (fun h => Or.inr (Or.inl h))
  by_cases ht : (C.loc p).turn = true
  · rw [if_pos ht] at hact
    cases hpc : (C.loc p).l5.pc with
    | llHead =>
      simp only [hpc, right6] at hact; cases hact
      have hm : C'.mem = C.mem := by rw [hmem]; simp
      by_cases hr : isResp (av C.mem p) = true
      · right; right
        refine ⟨hm, Or.inl ⟨hpc, hr, ?_⟩⟩
        rw [hlp]; simp [hr, absC]
      · left
        refine ⟨hm, ?_⟩
        rw [hlp]; simp [hr]
    | llAnn =>
      simp only [hpc, right18] at hact; cases hact
      have hm : C'.mem = C.mem := by rw [hmem]; simp
      have hl5 := hloc5; simp only [LocInv, hpc] at hl5
      obtain ⟨⟨rsp, j⟩, hj⟩ := Option.isSome_iff_exists.1 hl5
      by_cases hr : isResp (av C.mem p) = true
      · right; right
        refine ⟨hm, Or.inr (Or.inl ⟨hpc, hr, rsp, j, hj, ?_⟩)⟩
        rw [hlp]; simp [hr, absC, hj]
      · left
        refine ⟨hm, ?_⟩
        rw [hlp]; simp [hr]
    | llHead2 r =>
      simp only [hpc, right25] at hact; cases hact
      have hm : C'.mem = C.mem := by rw [hmem]; simp
      by_cases hr : ownerIs p (hv C.mem).2 = true
      · left
        refine ⟨hm, ?_⟩
        rw [hlp]; simp [hr]
      · right; right
        refine ⟨hm, Or.inr (Or.inr ⟨r, hpc, (by simpa using hr : ownerIs p (hv C.mem).2 = false), ?_⟩)⟩
        rw [hlp]; simp [hr, absC]
    | _ => simp only [hpc] at hact; exact lift hact
  · rw [if_neg ht] at hact; exact lift hact

omit [DecidablePred A.ReadOnly] in
lemma isResp_iff (a : AnnVal A) : isResp a = true ↔ ∃ r, a = some (.inr r) := by
  rcases a with _ | v
  · simp [isResp]
  · cases v <;> simp [isResp]

omit [DecidablePred A.ReadOnly] in
/-- The ends of the right-hand sides of `∥` preserve the invariant of Algorithm 5. -/
theorem InvC.jump {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {D : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} {l' : Loc A n}
    (hI : InvC L cur D.pend D.mem D.loc) (hJ : Jump p D l') :
    InvC L cur D.pend D.mem (Function.update D.loc p l') := by
  refine ⟨hI.h1, fun q => ?_⟩
  by_cases hq : q = p
  · subst hq
    simp only [Function.update_self]
    obtain ⟨pinv, ch, ca1, ca2, k3, k4, k5, k6, loc, h2⟩ := hI.proc q
    rcases hJ with ⟨hpc, hr, rfl⟩ | ⟨hpc, hr, rsp, j, hj, rfl⟩ | ⟨r, hpc, hown, rfl⟩
    · simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
      obtain ⟨r, hr⟩ := (isResp_iff _).1 hr
      rw [PInv_loop rfl] at pinv
      obtain ⟨o, h1, h2', h3 | h3⟩ := pinv
      · rw [hr] at h3; cases h3.1
      refine ⟨⟨⟨o, h1, h2'⟩, h3⟩, fun hh => ⟨(ch hh).1, rfl⟩, ca1, ?_, by simp [PC.inK3],
        by simp, by simp, by simp, by simp [LocInv], fun rsp hr => ⟨(h2 rsp hr).1, by simp⟩⟩
      intro j hj; rcases ca2 j hj with e | e
      · simp [PC.inVL] at e
      · exact Or.inr e
    · simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
      obtain ⟨r, hr⟩ := (isResp_iff _).1 hr
      rw [PInv_loop rfl] at pinv
      obtain ⟨o, h1, h2', h3 | h3⟩ := pinv
      · rw [hr] at h3; cases h3.1
      refine ⟨⟨⟨o, h1, h2'⟩, h3⟩, fun hh => ⟨(ch hh).1, rfl⟩, ca1, ?_, by simp [PC.inK3],
        by simp, by simp, by simp, by simp [LocInv], fun rsp hr => ⟨(h2 rsp hr).1, by simp⟩⟩
      intro j hj; rcases ca2 j hj with e | e
      · simp [PC.inVL] at e
      · exact Or.inr e
    · simp only [hpc] at pinv ch ca1 ca2 k3 k4 k5 k6 loc h2
      refine ⟨by simpa [PInv] using pinv, fun hh => ⟨(ch hh).1, rfl⟩, ca1, ?_, by simp [PC.inK3],
        by simp, by simp, by simp, by simp [LocInv], fun rsp hr => ?_⟩
      · intro j hj; rcases ca2 j hj with e | e
        · simp [PC.inVL] at e
        · exact Or.inr e
      · exfalso; rw [hr] at hown; simp [ownerIs] at hown
  · rw [Function.update_of_ne hq]; exact hI.proc q

/-! ## Invocations and responses -/

theorem flat_inv {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n} {o : A.Op}
    (h : (flat A n).step C (.inv p o) = some C') :
    (alg5 A n).step (absC C) (.inv p o) = some (absC C') := by
  obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  have : (alg5 A n).step (absC C) (.inv p o) = some { absC C with
      pend := Function.update C.pend p (some o),
      loc := Function.update (absC C).loc p ((alg5 A n).invoke p (C.loc p).l5 o) } := by
    simp only [Impl.step]
    rw [if_pos ⟨hp, trivial⟩]
    rfl
  rw [this, absC_eq_of (p := p) (l := (alg5 A n).invoke p (C.loc p).l5 o) hpend _ _ hmem]
  · rfl
  · intro q hq; rw [hloc]; exact Function.update_of_ne hq _ _
  · rw [hloc]; simp [flat]

lemma fact_ret {p : Fin n} {fl l : FLoc A n} {r : A.Resp} (h : fact p fl = .ret r l) :
    act p fl.l5 = .ret r l.l5 ∧ l = { fl with l5 := l.l5, st := false, turn := false } := by
  have hL : leftAct p fl = .ret r l := by
    unfold fact at h
    split_ifs at h
    · split at h
      · simp [right6] at h
      · simp [right18] at h
      · simp [right25] at h
      · exact h
    · exact h
  unfold leftAct at hL
  split at hL
  · cases hL
  · cases hL
  · rename_i r' l' hA
    cases hL
    exact ⟨hA, rfl⟩

theorem flat_ret {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n} {r : A.Resp}
    (h : (flat A n).step C (.ret p r) = some C') :
    (alg5 A n).step (absC C) (.ret p r) = some (absC C') := by
  obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  obtain ⟨hA, -⟩ := fact_ret hact
  have : (alg5 A n).step (absC C) (.ret p r) = some { absC C with
      pend := Function.update C.pend p none,
      loc := Function.update (absC C).loc p l.l5 } := by
    simp [Impl.step, absC, hp, alg5, hA]
  rw [this, absC_eq_of (p := p) (l := l.l5) hpend _ _ hmem]
  · rfl
  · intro q hq; rw [hloc]; exact Function.update_of_ne hq _ _
  · rw [hloc]; simp

/-! ## The linearization function and the invariant of the flattened implementation -/

open Classical in
/-- The contribution of a step of the flattened implementation to the linearization: the
contribution of the simulated step of Algorithm 5, if the step simulates one. -/
noncomputable def contribFl (α : List (Label (Fin n) A)) (ℓ : Label (Fin n) A) :
    List (OpId (Fin n) × A.Op) :=
  match (flat A n).run α, ℓ with
  | some C, .tau p =>
    if ∃ C', (flat A n).step C (.tau p) = some C' ∧
        (alg5 A n).step (absC C) (.tau p) = some (absC C') then
      contribT (curOf α) (absC C) p
    else []
  | _, _ => []

/-- Auxiliary: `hlinF` on the reversed execution. -/
noncomputable def hlinFRev : List (Label (Fin n) A) → List (OpId (Fin n) × A.Op)
  | [] => []
  | ℓ :: β => hlinFRev β ++ contribFl β.reverse ℓ

variable (A n) in
/-- The linearization function of the flattened implementation: an operation is linearized at
the linearization point (Algorithm 6) of the R-LLSC operation at which Algorithm 5 linearizes
it, i.e. the successful `CAS` of `SC(head, ⟨q', ⟨r, j⟩⟩)` (line 14) for state-changing
operations, and the `Read` of `Load(head)` (line 1) for read-only ones. -/
noncomputable def hlinF (α : List (Label (Fin n) A)) : List (OpId (Fin n) × A.Op) :=
  hlinFRev α.reverse

lemma hlinF_snoc (α : List (Label (Fin n) A)) (ℓ : Label (Fin n) A) :
    hlinF A n (α ++ [ℓ]) = hlinF A n α ++ contribFl α ℓ := by
  simp [hlinF, hlinFRev]

lemma InvL.extend_tau {α : List (Label (Fin n) A)} {L : List (OpId (Fin n) × A.Op)}
    {D : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} (hI : InvL α L D)
    {D' : Config A (B A n) (Fin n) (Loc A n)} (hC : InvC L (curOf α) D'.pend D'.mem D'.loc) :
    InvL (α ++ [.tau p]) L D' := by
  have hops := opsOf_snoc_of_ne (α := α) (ℓ := .tau p) (by simp)
  have hresps := respsOf_snoc_of_ne (α := α) (ℓ := .tau p) (by simp)
  have hcurE : curOf (α ++ [.tau p]) = curOf α := by funext q; simp [curOf, hops]
  refine ⟨by rw [hcurE]; exact hC, hI.nodup, fun y hy => ?_, fun x hx => ?_, fun x r hx => ?_⟩
  · rw [opOf_append_of_invoked (hI.invoked (List.mem_map_of_mem hy))]; exact hI.op_eq y hy
  · exact hI.complete x (by simpa [Completed, hresps] using hx)
  · exact hI.resp x r (by simpa [respOf, hresps] using hx)

lemma flat_opOf_curOf {α : List (Label (Fin n) A)} {C : Config A (BF A n) (Fin n) (FLoc A n)}
    (h : (flat A n).run α = some C) {j : Fin n} {o : A.Op} (hj : C.pend j = some o) :
    opOf α (curOf α j) = some o := by
  have := (flat A n).run_pend h hj
  simp only [opOf, curOf]
  rw [List.getLast?_eq_getElem?] at this
  exact this

open Classical in
/-- **The invariant of the flattened implementation**: the abstract configuration satisfies the
invariant of Algorithm 5, with the linearization `hlinF`. -/
theorem flat_invL {α : List (Label (Fin n) A)} {C : Config A (BF A n) (Fin n) (FLoc A n)}
    (h : (flat A n).run α = some C) : InvL α (hlinF A n α) (absC C) := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp [Impl.run] at h; subst h
    exact inv_init
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (flat A n).runFrom (flat A n).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      have hI := ih hα
      rw [hlinF_snoc]
      cases ℓ with
      | tau p =>
        have hcon : contribFl α (.tau p) = if ∃ C', (flat A n).step C₀ (.tau p) = some C' ∧
            (alg5 A n).step (absC C₀) (.tau p) = some (absC C') then
            contribT (curOf α) (absC C₀) p else [] := by
          simp only [contribFl]; rw [show (flat A n).run α = some C₀ from hα]
        rw [hcon]
        have hloc5 : LocInv p (C₀.loc p).l5 := (hI.invC.proc p).loc
        obtain ⟨hpend, hlr, hS | hE | hJ⟩ := flat_tau hloc5 h
        · split_ifs with hE'
          · obtain ⟨C'', h'', hE''⟩ := hE'
            rw [h] at h''; cases h''
            exact hI.tauStep (fun j o hj => flat_opOf_curOf hα hj) hE''
          · rw [append_nil]
            refine hI.extend_tau ?_
            have : absC C = absC C₀ := by
              rw [absC_eq_of (p := p) (l := (C₀.loc p).l5) hpend hlr hS.2 hS.1]
              simp [absC]
            rw [this]; exact hI.invC
        · rw [if_pos ⟨C, h, hE⟩]
          exact hI.tauStep (fun j o hj => flat_opOf_curOf hα hj) hE
        · split_ifs with hE'
          · obtain ⟨C'', h'', hE''⟩ := hE'
            rw [h] at h''; cases h''
            exact hI.tauStep (fun j o hj => flat_opOf_curOf hα hj) hE''
          · rw [append_nil]
            refine hI.extend_tau ?_
            rw [absC_eq_of (p := p) (l := (C.loc p).l5) hpend hlr rfl hJ.1]
            exact hI.invC.jump hJ.2
      | inv p o =>
        rw [show contribFl α (.inv p o) = [] by simp [contribFl], append_nil]
        exact hI.invStep (flat_inv h)
      | ret p r =>
        rw [show contribFl α (.ret p r) = [] by simp [contribFl], append_nil]
        refine hI.retStep (fun hp => ?_) (flat_ret h)
        rcases (flat A n).run_counts hα p with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact absurd h1 hp
        · exact h2

/-! ## Linearizability and state-quiescent history independence (Theorem 32) -/

lemma hlinF_append (α β : List (Label (Fin n) A)) :
    ∃ M, hlinF A n (α ++ β) = hlinF A n α ++ M := by
  induction β using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton β ℓ ih =>
    obtain ⟨M, hM⟩ := ih
    exact ⟨M ++ contribFl (α ++ β) ℓ, by rw [← List.append_assoc, hlinF_snoc, hM, List.append_assoc]⟩

/-- **Theorem 32** (linearizability): `hlinF` is a linearization function of the flattened
implementation. -/
theorem flat_isLinFun : (flat A n).IsLinFun (hlinF A n) := by
  intro α ⟨C, hC⟩
  have hI := flat_invL hC
  refine ⟨hI.nodup, hI.op_eq, hI.complete, ?_, ?_⟩
  · rintro a b ⟨β, γ, rfl, ha, hb⟩ hbL
    obtain ⟨Cβ, hCβ⟩ := (flat A n).valid_of_prefix ⟨C, hC⟩ (List.prefix_append β γ)
    have hIβ := flat_invL hCβ
    obtain ⟨M, hM⟩ := hlinF_append β γ
    rw [hM] at hbL ⊢
    have haβ := hIβ.complete a ha
    have hbβ : b ∉ (hlinF A n β).map Prod.fst := fun hm => hb (hIβ.invoked hm)
    simp only [map_append, mem_append] at hbL ⊢
    rcases hbL with hbL | hbL
    · exact absurd hbL hbβ
    · exact (List.Sublist.append (List.singleton_sublist.2 haβ) (List.singleton_sublist.2 hbL) :
        [a] ++ [b] <+ _)
  · exact seqOK_of_specResp _ _ hI.nodup fun x r _ hr => hI.resp x r hr

/-- **Theorem 32** (state-quiescent HI): in a state-quiescent configuration every CAS object
holds the canonical value: `head = (⟨q, ⊥⟩, ∅)`, `announce[j] = (⊥, ∅)`, where `q` is the state
of the linearization. -/
theorem flat_mem_eq_canon {α : List (Label (Fin n) A)} {C : Config A (BF A n) (Fin n) (FLoc A n)}
    (h : (flat A n).run α = some C) (hq : C.StateQuiescent) :
    C.mem = canon (linState (hlinF A n α)) := by
  have hI := flat_invL h
  rw [hI.invC.h1]
  exact mem_eq_canon hI.invC hq

/-- **Theorem 32** (state-quiescent history independence of the flattened implementation). -/
theorem flat_stateQuiescentHI : (flat A n).StateQuiescentHI := by
  refine ⟨hlinF A n, flat_isLinFun, fun α α' C C' h h' hq hq' he => ?_⟩
  rw [flat_mem_eq_canon h hq, flat_mem_eq_canon h' hq', he]

end Universal

end Cslib.SharedMemory
