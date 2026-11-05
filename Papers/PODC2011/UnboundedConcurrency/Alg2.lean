import Papers.PODC2011.UnboundedConcurrency.IteratorStack
import Mathlib.Data.Set.Card

/-!
# Algorithm 2 of Afek–Morrison–Wertheim (PODC 2011): bounded-concurrency consensus from an
iterator stack

Section 5.2. Shared objects: a register `result` (initially `⊥ = none`) and an iterator stack.
Code of `propose(value)`:
```
1: if result ≠ ⊥ then return result
2: itr := IteratorStack.write(value)
   repeat
3:   last := cur
4:   cur := IteratorStack.read(itr)
   until cur = ⊥
5: result := last
6: return result
```
Every shared access is one step (local computation is folded into the continuation). One process
performs one `propose` invocation (a new invocation is a new process).

## Main definitions

* `Obj`, `objs`, `Loc`, `act`, `alg2`: the algorithm;
* `active`, `BoundedConcurrency`, `BCWaitFree`: the paper's *bounded concurrency model*: in an
  infinite execution, the number of processes that have started and not yet returned is bounded
  by some `n` (not known to the algorithm, depending on the execution).

## Main statements

* `agreement`, `validity`: safety at any concurrency (all finite schedules);
* `bcWaitFree`: every process taking infinitely many steps of an infinite execution with bounded
  concurrency returns;
* `theorem_12`: Theorem 12 (Algorithm 2 is a wait-free bounded-concurrency consensus algorithm);
* `solvesCons_boundedBy`: consequence: for every `n`, Algorithm 2 solves `n`-process consensus
  (the iterator stack has consensus number `∞`);
* `not_waitFree_infArrival`: Algorithm 2 is not wait-free under unbounded concurrency.
-/

namespace Podc.UnboundedConcurrency.Alg2

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

/-! ### The bounded concurrency model (generic) -/

section BC

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {X Y : Type}

-- CSLib candidate (with `Cslib.SharedMemory.Arrival`)
/-- The *active* processes after the finite schedule `σ`: those that took a step and are not in
an output state. -/
def active (A : Alg T ℕ X Y) (x : ℕ → X) (σ : List ℕ) : Set ℕ :=
  {p | p ∈ σ ∧ ∀ v, ¬ (A.exec x σ).Out p v}

/-- The infinite schedule `s` (with inputs `x`) has *bounded concurrency*: there is a bound `n`
(depending on the execution) on the number of active processes at every time. -/
def BoundedConcurrency (A : Alg T ℕ X Y) (x : ℕ → X) (s : ℕ → ℕ) : Prop :=
  ∃ n, ∀ t, Set.ncard (active A x (pre s t)) ≤ n

/-- Wait-freedom in the bounded concurrency model: in every infinite execution with bounded
concurrency, every process that takes infinitely many steps eventually outputs. -/
def BCWaitFree (A : Alg T ℕ X Y) : Prop :=
  ∀ x s, BoundedConcurrency A x s → ∀ p, InfOften s p → ∃ t v, (A.exec x (pre s t)).Out p v

/-- In the model `Mⁿ₁` (`boundedBy n`: only `p₀, …, p_{n-1}` take steps), the concurrency is
bounded by `n`. -/
lemma boundedConcurrency_of_boundedBy (A : Alg T ℕ X Y) (x : ℕ → X) {n : ℕ} {s : ℕ → ℕ}
    (hs : boundedBy n s) : BoundedConcurrency A x s := by
  refine ⟨n, fun t => ?_⟩
  calc Set.ncard (active A x (pre s t)) ≤ (↑(Finset.range n) : Set ℕ).ncard := by
        apply Set.ncard_le_ncard _ (Finset.finite_toSet _)
        rintro p ⟨hp, -⟩
        obtain ⟨u, -, rfl⟩ := mem_pre.1 hp
        simpa using hs u
    _ = n := by rw [Set.ncard_coe_finset, Finset.card_range]

lemma BCWaitFree.waitFree_boundedBy {A : Alg T ℕ X Y} (h : BCWaitFree A) (n : ℕ) :
    WaitFree A (boundedBy n) :=
  fun x s hs => h x s (boundedConcurrency_of_boundedBy A x hs)

end BC

/-! ### The algorithm -/

/-- Shared objects: the register `result` and the iterator stack. -/
inductive Obj
  | result
  | stack
  deriving DecidableEq

variable {V : Type}

/-- The sequential specifications of the shared objects. -/
abbrev objs (V : Type) : Obj → ObjSpec
  | .result => register (Option V) none
  | .stack => itStack V

/-- Local states of a process with input `v`. -/
inductive Loc (V : Type)
  /-- Line 1: about to read `result`. -/
  | start (v : V)
  /-- Line 2: about to write `v` to the iterator stack. -/
  | write (v : V)
  /-- Lines 3–4: about to read iterator `k`; `prev` is the value of `cur` (initially `⊥`). -/
  | loop (v : V) (k : ℕ) (prev : Option V)
  /-- Line 5: about to write `result := w`. -/
  | fin (w : V)
  /-- Returned `w`. -/
  | done (w : V)

/-- The code of Algorithm 2. If the last read value `last` is `⊥` at line 5 (impossible, see
`Inv`) the process writes its own input instead. -/
def act (V : Type) : Loc V → Act (objs V) (Loc V) V
  | .start v => .access .result .read
      (fun r => match r with | some w => .done w | none => .write v)
  | .write v => .access .stack (.write v)
      (fun r => match r with | .idx k => .loop v k none | .val _ => .loop v 0 none)
  | .loop v k prev => .access .stack (.read k)
      (fun r => match r with
        | .val (some w) => .loop v k (some w)
        | .val none => .fin (prev.getD v)
        | .idx _ => .fin v)
  | .fin w => .access .result (.write (some w)) (fun _ => .done w)
  | .done w => .out w

/-- Algorithm 2: process `p` with input `v` starts at line 1; `result = ⊥`, the iterator stack is
empty. -/
abbrev alg2 (V : Type) : Alg (objs V) ℕ V V where
  L := Loc V
  init _ v := .start v
  act := act V
  mem₀
    | .result => (none : Option V)
    | .stack => (⟨[], []⟩ : ISState V)

/-- Configurations of Algorithm 2. -/
abbrev Conf (V : Type) := Cfg (alg2 V)

/-- The content of `result`. -/
def res (C : Conf V) : Option V := C.mem .result

/-- The state of the iterator stack. -/
def stk (C : Conf V) : ISState V := C.mem .stack

@[simp] lemma act_eq (l : Loc V) : (alg2 V).act l = act V l := rfl

/-- What a read of `result` returns to a process at line 1. -/
def afterRead (v : V) : Option V → Loc V
  | some w => .done w
  | none => .write v

/-- What a read of iterator `k` returns to a process in the loop. -/
def afterIt (v : V) (k : ℕ) (prev : Option V) : Option V → Loc V
  | some w => .loop v k (some w)
  | none => .fin (prev.getD v)

/-! ### One step of each kind -/

section Steps

open Function

variable {C : Conf V} {p : ℕ} {v w : V} {k : ℕ} {prev : Option V}

lemma step_start (h : C.loc p = .start v) :
    C.step p = ⟨update C.loc p (afterRead v (res C)), C.mem⟩ := by
  rw [Cfg.step_of_access (A := alg2 V) (i := Obj.result) (o := RWOp.read) (k := afterRead v)
    (by change act V (C.loc p) = _; rw [h]; rfl)]
  congr 1
  exact update_eq_self _ _

lemma step_write (h : C.loc p = .write v) :
    C.step p = ⟨update C.loc p (.loop v (stk C).its.length none),
      update C.mem .stack (⟨v :: (stk C).vals, (stk C).its ++ [1]⟩ : ISState V)⟩ := by
  rw [Cfg.step_of_access (A := alg2 V) (i := Obj.stack) (o := ISOp.write v)
    (k := fun (r : ISResp V) => match r with | .idx k => Loc.loop v k none | .val _ => .loop v 0 none)
    (by change act V (C.loc p) = _; rw [h]; rfl)]
  rfl

lemma step_loop (h : C.loc p = .loop v k prev) {pos : ℕ} (hk : (stk C).its[k]? = some pos) :
    C.step p = ⟨update C.loc p (afterIt v k prev ((stk C).at pos)),
      update C.mem .stack (⟨(stk C).vals, (stk C).its.set k (pos + 1)⟩ : ISState V)⟩ := by
  rw [Cfg.step_of_access (A := alg2 V) (i := Obj.stack) (o := ISOp.read k)
    (k := fun (r : ISResp V) => match r with
        | .val (some w) => Loc.loop v k (some w)
        | .val none => .fin (prev.getD v)
        | .idx _ => .fin v)
    (by change act V (C.loc p) = _; rw [h]; rfl)]
  have : (objs V Obj.stack).δ (C.mem .stack) (.read k) =
      (⟨(stk C).vals, (stk C).its.set k (pos + 1)⟩, .val ((stk C).at pos)) := by
    change ISState.δ (stk C) (.read k) = _
    simp [ISState.δ, hk]
  rw [this]
  congr 2
  cases (stk C).at pos <;> rfl

lemma step_fin (h : C.loc p = .fin w) :
    C.step p = ⟨update C.loc p (.done w), update C.mem .result (some w : Option V)⟩ := by
  rw [Cfg.step_of_access (A := alg2 V) (i := Obj.result) (o := RWOp.write (some w)) (k := fun _ => Loc.done w)
    (by change act V (C.loc p) = _; rw [h]; rfl)]

lemma step_done (h : C.loc p = .done w) : C.step p = C :=
  Cfg.step_of_out (v := w) (by unfold Cfg.Out; change act V (C.loc p) = _; rw [h]; rfl)

end Steps

@[simp] lemma stk_mk (l : ℕ → Loc V) (m : (o : Obj) → (objs V o).State) :
    stk (⟨l, m⟩ : Conf V) = m .stack := rfl

@[simp] lemma res_mk (l : ℕ → Loc V) (m : (o : Obj) → (objs V o).State) :
    res (⟨l, m⟩ : Conf V) = m .result := rfl

/-! ### The invariant -/

/-- The invariant of a process in the loop with iterator `k`, at position `pos`: the iterator
is valid; before the first read (`prev = ⊥`) it is at position `1`; afterwards the iterator is at
most one past the end, and if it is exactly one past the end then the last value read (`prev`) is
the *first* value written to the stack. -/
def LoopOK (s : ISState V) (k : ℕ) (prev : Option V) : Prop :=
  ∃ pos, s.its[k]? = some pos ∧ (prev = none → pos = 1) ∧
    ∀ w, prev = some w → 2 ≤ pos ∧ pos ≤ s.vals.length + 1 ∧
      (pos = s.vals.length + 1 → s.vals.getLast? = some w)

/-- The invariant of the local state of a process with input `xp`: the value it carries is its
input, and values to be written to `result` or returned are the first value written to the
stack. -/
def LocOK (xp : V) (s : ISState V) : Loc V → Prop
  | .start v => v = xp
  | .write v => v = xp
  | .loop v k prev => v = xp ∧ LoopOK s k prev
  | .fin w => s.vals.getLast? = some w
  | .done w => s.vals.getLast? = some w

/-- About to write to the stack. -/
def isW : Loc V → Bool
  | .write _ => true
  | _ => false

/-- About to write to the stack, or wrote to it and has not yet written `result`. -/
def isWLF : Loc V → Bool
  | .write _ | .loop .. | .fin _ => true
  | _ => false

/-- The number of processes of `σ` whose local state satisfies `f`. -/
def cnt (σ : List ℕ) (l : ℕ → Loc V) (f : Loc V → Bool) : ℕ :=
  ∑ q ∈ σ.toFinset, if f (l q) then 1 else 0

/-- The invariant of Algorithm 2 after the schedule `σ`. While `result = ⊥`, no process has
returned and every writer to the stack is still in the loop or at line 5 (`cnt`). -/
structure Inv (x : ℕ → V) (σ : List ℕ) (C : Conf V) : Prop where
  len : (stk C).its.length = (stk C).vals.length
  vals_in : ∀ w ∈ (stk C).vals, ∃ q ∈ σ, x q = w
  res_first : ∀ w, res C = some w → (stk C).vals.getLast? = some w
  loc_ok : ∀ p, LocOK (x p) (stk C) (C.loc p)
  uniq : ∀ p q v v' k prev prev', C.loc p = .loop v k prev → C.loc q = .loop v' k prev' → p = q
  fresh : ∀ p ∉ σ, C.loc p = .start (x p)
  count : res C = none →
    (stk C).its.length + cnt σ C.loc isW = cnt σ C.loc isWLF ∧ ∀ q w, C.loc q ≠ .done w

lemma LocOK.write {xp v : V} {s : ISState V} {l : Loc V} (h : LocOK xp s l) :
    LocOK xp ⟨v :: s.vals, s.its ++ [1]⟩ l := by
  cases l with
  | start => exact h
  | write => exact h
  | loop v' k prev =>
    obtain ⟨hv, pos, hk, h1, h2⟩ := h
    have hlt : k < s.its.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hk; cases hk
    refine ⟨hv, pos, ?_, h1, fun w hw => ?_⟩
    · simpa [List.getElem?_append_left hlt] using hk
    · obtain ⟨a, b, -⟩ := h2 w hw
      refine ⟨a, by simp; omega, fun hc => by simp at hc; omega⟩
  | fin w => simp only [LocOK, List.getLast?_cons] at h ⊢; rw [h]; rfl
  | done w => simp only [LocOK, List.getLast?_cons] at h ⊢; rw [h]; rfl

lemma LocOK.set_other {xp : V} {s : ISState V} {l : Loc V} {k a : ℕ} (h : LocOK xp s l)
    (hk : ∀ v k' prev, l = .loop v k' prev → k' ≠ k) :
    LocOK xp ⟨s.vals, s.its.set k a⟩ l := by
  cases l with
  | start => exact h
  | write => exact h
  | loop v' k' prev =>
    obtain ⟨hv, pos, hpos, h1, h2⟩ := h
    have hne := hk v' k' prev rfl
    exact ⟨hv, pos, by rw [List.getElem?_set_ne (Ne.symm hne)]; exact hpos, h1, h2⟩
  | fin w => exact h
  | done w => exact h

lemma cnt_step (σ : List ℕ) (p : ℕ) (l l' : ℕ → Loc V) (f : Loc V → Bool)
    (hl : ∀ q, q ≠ p → l' q = l q) (hp : p ∉ σ → f (l p) = false) :
    cnt (σ ++ [p]) l' f + (if f (l p) then 1 else 0) = cnt σ l f + (if f (l' p) then 1 else 0) := by
  unfold cnt
  have hset : (σ ++ [p]).toFinset = insert p σ.toFinset := by ext; simp
  rw [hset]
  by_cases hpσ : p ∈ σ
  · have hm : p ∈ σ.toFinset := by simpa using hpσ
    rw [Finset.insert_eq_of_mem hm, ← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ _ hm,
      Finset.sum_congr rfl (g := fun q => if f (l q) then 1 else 0)
        (fun q hq => by rw [hl q (Finset.ne_of_mem_erase hq)])]
    omega
  · rw [Finset.sum_insert (by simpa using hpσ), hp hpσ,
      Finset.sum_congr rfl (g := fun q => if f (l q) then 1 else 0)
        (fun q hq => by rw [hl q (by rintro rfl; exact hpσ (by simpa using hq))])]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

lemma cnt_mono (σ : List ℕ) (p : ℕ) (l : ℕ → Loc V) (f : Loc V → Bool)
    (hp : p ∉ σ → f (l p) = false) : cnt (σ ++ [p]) l f = cnt σ l f := by
  have := cnt_step σ p l l f (fun _ _ => rfl) hp
  omega

lemma Inv.init (x : ℕ → V) : Inv x [] ((alg2 V).initCfg x) where
  len := rfl
  vals_in := fun w hw => by simp [stk, Alg.initCfg, alg2] at hw
  res_first := fun w hw => by simp [res, Alg.initCfg, alg2] at hw
  loc_ok := fun p => rfl
  uniq := fun p q v v' k prev prev' hp => by cases hp
  fresh := fun p _ => rfl
  count := fun _ => ⟨by simp [stk, Alg.initCfg, alg2, cnt], fun q w h => by cases h⟩

section StepInv

open Function

variable {x : ℕ → V} {σ : List ℕ} {C : Conf V}

lemma Inv.mem_of_ne_start (h : Inv x σ C) {p : ℕ} (hp : ∀ v, C.loc p ≠ .start v) : p ∈ σ := by
  by_contra hc; exact hp _ (h.fresh p hc)

lemma Inv.lt_of_loop (h : Inv x σ C) {p : ℕ} {v : V} {k : ℕ} {prev : Option V}
    (hp : C.loc p = .loop v k prev) : k < (stk C).its.length := by
  have := h.loc_ok p
  rw [hp] at this
  obtain ⟨-, pos, hk, -⟩ := this
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at hk; cases hk

/-- The local state after a read of the own iterator satisfies the invariant (this is where
"the last value read before `⊥` is the first value written" is proved). -/
lemma locOK_afterIt {xp v : V} {s : ISState V} {k pos : ℕ} {prev : Option V}
    (hlen : s.its.length = s.vals.length) (hv : v = xp) (hpos : s.its[k]? = some pos)
    (h1 : prev = none → pos = 1)
    (h2 : ∀ w, prev = some w → 2 ≤ pos ∧ pos ≤ s.vals.length + 1 ∧
      (pos = s.vals.length + 1 → s.vals.getLast? = some w)) :
    LocOK xp ⟨s.vals, s.its.set k (pos + 1)⟩ (afterIt v k prev (s.at pos)) := by
  have hk : k < s.its.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hpos; cases hpos
  have hpos1 : 1 ≤ pos := by
    cases prev with
    | none => rw [h1 rfl]
    | some w => have := (h2 w rfl).1; omega
  unfold ISState.at
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  rcases hval : s.vals[pos - 1]? with _ | w'
  · have hle : s.vals.length ≤ pos - 1 := List.getElem?_eq_none_iff.1 hval
    cases prev with
    | none => have := h1 rfl; omega
    | some w =>
      obtain ⟨-, b, c⟩ := h2 w rfl
      exact c (by omega)
  · have hlt : pos - 1 < s.vals.length := (List.getElem?_eq_some_iff.1 hval).1
    refine ⟨hv, pos + 1, by simp [hk], (fun h => by cases h), fun w hw => ?_⟩
    cases hw
    refine ⟨by omega, by simp; omega, fun he => ?_⟩
    rw [List.getLast?_eq_getElem?, show s.vals.length - 1 = pos - 1 by simp at he; omega]
    exact hval

lemma afterIt_ne_done {v : V} {k : ℕ} {prev r : Option V} {w : V} :
    afterIt v k prev r ≠ .done w := by
  cases r <;> simp [afterIt]

lemma afterIt_loop {v v' : V} {k k' : ℕ} {prev prev' r : Option V}
    (h : afterIt v k prev r = .loop v' k' prev') : k' = k := by
  cases r <;> simp_all [afterIt]

lemma Inv.step (h : Inv x σ C) (p : ℕ) : Inv x (σ ++ [p]) (C.step p) := by
  have hσ : ∀ q ∈ σ, q ∈ σ ++ [p] := fun q hq => by simp [hq]
  have hfresh : ∀ q ∉ σ ++ [p], q ≠ p ∧ q ∉ σ := fun q hq => by
    simp only [List.mem_append, List.mem_singleton, not_or] at hq; exact ⟨hq.2, hq.1⟩
  have hok := h.loc_ok p
  rcases hl : C.loc p with v | v | ⟨v, k, prev⟩ | w | w <;> rw [hl] at hok
  · -- line 1: read `result`
    rw [step_start hl]
    have hnew : ∀ v' k' prev', afterRead v (res C) ≠ .loop v' k' prev' := by
      intro v' k' prev'; cases res C <;> simp [afterRead]
    refine ⟨h.len, fun w hw => ?_, h.res_first, fun q => ?_, ?_, fun q hq => ?_, fun hr => ?_⟩
    · obtain ⟨q, hq, e⟩ := h.vals_in w hw; exact ⟨q, hσ q hq, e⟩
    · by_cases hq : q = p
      · subst hq; simp only [update_self, stk_mk]
        rcases hr : res C with _ | w
        · exact hok
        · exact h.res_first w hr
      · simp only [update_of_ne hq, stk_mk]; exact h.loc_ok q
    · intro q q' v₁ v₂ k₁ p₁ p₂ h1 h2
      simp only at h1 h2
      by_cases hq : q = p
      · subst hq; simp at h1; exact absurd h1 (hnew _ _ _)
      by_cases hq' : q' = p
      · subst hq'; simp at h2; exact absurd h2 (hnew _ _ _)
      rw [update_of_ne hq] at h1; rw [update_of_ne hq'] at h2
      exact h.uniq _ _ _ _ _ _ _ h1 h2
    · obtain ⟨h1, h2⟩ := hfresh q hq
      simp only [update_of_ne h1]; exact h.fresh q h2
    · simp only [res_mk] at hr
      obtain ⟨hc1, hc2⟩ := h.count hr
      have e1 := cnt_step σ p C.loc (update C.loc p (afterRead v (res C))) isW
        (fun q hq => update_of_ne hq _ _) (fun _ => by rw [hl]; rfl)
      have e2 := cnt_step σ p C.loc (update C.loc p (afterRead v (res C))) isWLF
        (fun q hq => update_of_ne hq _ _) (fun _ => by rw [hl]; rfl)
      have hr' : res C = none := hr
      simp only [update_self, hl, hr', afterRead, isW, isWLF] at e1 e2
      refine ⟨?_, fun q w' => ?_⟩
      · simp only [hr', afterRead] at e1 e2 ⊢
        change (stk C).its.length + _ = _
        simp at e1 e2
        omega
      by_cases hq : q = p
      · subst hq; simp [hr', afterRead]
      · simp only [update_of_ne hq]; exact hc2 q w'
  · -- line 2: write to the stack
    rw [step_write hl]
    have hp : p ∈ σ := h.mem_of_ne_start (by rw [hl]; simp)
    have hres : res (⟨update C.loc p (.loop v (stk C).its.length none),
        update C.mem .stack (⟨v :: (stk C).vals, (stk C).its ++ [1]⟩ : ISState V)⟩ : Conf V) =
        res C := by simp [res]
    refine ⟨by simp [h.len], fun w hw => ?_, fun w hw => ?_, fun q => ?_, ?_, fun q hq => ?_,
      fun hr => ?_⟩
    · simp only [stk_mk, update_self, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨p, by simp, hok.symm⟩
      · obtain ⟨q, hq, e⟩ := h.vals_in w hw; exact ⟨q, hσ q hq, e⟩
    · rw [hres] at hw
      simp only [stk_mk, update_self, List.getLast?_cons, h.res_first w hw]; rfl
    · by_cases hq : q = p
      · subst hq; simp only [update_self, stk_mk]
        exact ⟨hok, 1, by simp, fun _ => rfl, fun w hw => by cases hw⟩
      · simp only [update_of_ne hq, stk_mk, update_self]; exact (h.loc_ok q).write
    · intro q q' v₁ v₂ k₁ p₁ p₂ h1 h2
      simp only at h1 h2
      by_cases hq : q = p
      · by_cases hq' : q' = p
        · rw [hq, hq']
        · subst hq; rw [update_self] at h1; rw [update_of_ne hq'] at h2
          cases h1; have := h.lt_of_loop h2; omega
      · by_cases hq' : q' = p
        · subst hq'; rw [update_self] at h2; rw [update_of_ne hq] at h1
          cases h2; have := h.lt_of_loop h1; omega
        · rw [update_of_ne hq] at h1; rw [update_of_ne hq'] at h2
          exact h.uniq _ _ _ _ _ _ _ h1 h2
    · obtain ⟨h1, h2⟩ := hfresh q hq
      simp only [update_of_ne h1]; exact h.fresh q h2
    · rw [hres] at hr
      obtain ⟨hc1, hc2⟩ := h.count hr
      have e1 := cnt_step σ p C.loc (update C.loc p (.loop v (stk C).its.length none)) isW
        (fun q hq => update_of_ne hq _ _) (fun hn => absurd hp hn)
      have e2 := cnt_step σ p C.loc (update C.loc p (.loop v (stk C).its.length none)) isWLF
        (fun q hq => update_of_ne hq _ _) (fun hn => absurd hp hn)
      simp only [update_self, hl, isW, isWLF] at e1 e2
      refine ⟨?_, fun q w' => ?_⟩
      · simp only [stk_mk, update_self, List.length_append, List.length_singleton]
        simp at e1 e2
        omega
      · by_cases hq : q = p
        · subst hq; simp
        · simp only [update_of_ne hq]; exact hc2 q w'
  · -- lines 3–4: read the own iterator
    obtain ⟨hv, pos, hpos, h1, h2⟩ := hok
    rw [step_loop hl hpos]
    have hp : p ∈ σ := h.mem_of_ne_start (by rw [hl]; simp)
    set l' := afterIt v k prev ((stk C).at pos) with hl'
    have hres : res (⟨update C.loc p l',
        update C.mem .stack (⟨(stk C).vals, (stk C).its.set k (pos + 1)⟩ : ISState V)⟩ : Conf V) =
        res C := by simp [res]
    have hold : ∀ q v₁ k₁ p₁, update C.loc p l' q = .loop v₁ k₁ p₁ →
        ∃ v₂ p₂, C.loc q = .loop v₂ k₁ p₂ := by
      intro q v₁ k₁ p₁ hq
      by_cases hqp : q = p
      · subst hqp; rw [update_self] at hq
        have := afterIt_loop (hl' ▸ hq); subst this; exact ⟨v, prev, hl⟩
      · rw [update_of_ne hqp] at hq; exact ⟨v₁, p₁, hq⟩
    refine ⟨by simp [h.len], fun w hw => ?_, fun w hw => ?_, fun q => ?_, ?_, fun q hq => ?_,
      fun hr => ?_⟩
    · simp only [stk_mk, update_self] at hw
      obtain ⟨q, hq, e⟩ := h.vals_in w hw; exact ⟨q, hσ q hq, e⟩
    · rw [hres] at hw
      simp only [stk_mk, update_self]; exact h.res_first w hw
    · by_cases hq : q = p
      · subst hq; simp only [update_self, stk_mk]
        exact locOK_afterIt h.len hv hpos h1 h2
      · simp only [update_of_ne hq, stk_mk, update_self]
        exact (h.loc_ok q).set_other (fun v' k' prev' hq' hk' => hq
          (h.uniq q p v' v k prev' prev (hk' ▸ hq') hl))
    · intro q q' v₁ v₂ k₁ p₁ p₂ hq hq'
      obtain ⟨_, _, e1⟩ := hold q _ _ _ hq
      obtain ⟨_, _, e2⟩ := hold q' _ _ _ hq'
      exact h.uniq _ _ _ _ _ _ _ e1 e2
    · obtain ⟨h1, h2⟩ := hfresh q hq
      simp only [update_of_ne h1]; exact h.fresh q h2
    · rw [hres] at hr
      obtain ⟨hc1, hc2⟩ := h.count hr
      have hW : isW l' = false := by rw [hl']; cases (stk C).at pos <;> rfl
      have hWLF : isWLF l' = true := by rw [hl']; cases (stk C).at pos <;> rfl
      have e1 := cnt_step σ p C.loc (update C.loc p l') isW
        (fun q hq => update_of_ne hq _ _) (fun hn => absurd hp hn)
      have e2 := cnt_step σ p C.loc (update C.loc p l') isWLF
        (fun q hq => update_of_ne hq _ _) (fun hn => absurd hp hn)
      simp only [update_self, hW, hWLF] at e1 e2
      simp only [hl, isW, isWLF] at e1 e2
      refine ⟨?_, fun q w' => ?_⟩
      · simp only [stk_mk, update_self, List.length_set]
        simp at e1 e2
        omega
      · by_cases hq : q = p
        · subst hq; simp only [update_self]; exact afterIt_ne_done
        · simp only [update_of_ne hq]; exact hc2 q w'
  · -- line 5: write `result`
    rw [step_fin hl]
    refine ⟨h.len, fun w hw => ?_, fun w' hw => ?_, fun q => ?_, ?_, fun q hq => ?_,
      fun hr => ?_⟩
    · obtain ⟨q, hq, e⟩ := h.vals_in w hw; exact ⟨q, hσ q hq, e⟩
    · simp only [res_mk, update_self, Option.some.injEq] at hw
      subst hw; exact hok
    · by_cases hq : q = p
      · subst hq; simp only [update_self]; exact hok
      · simp only [update_of_ne hq]; exact h.loc_ok q
    · intro q q' v₁ v₂ k₁ p₁ p₂ hq hq'
      simp only at hq hq'
      by_cases hqp : q = p
      · subst hqp; simp at hq
      by_cases hqp' : q' = p
      · subst hqp'; simp at hq'
      rw [update_of_ne hqp] at hq; rw [update_of_ne hqp'] at hq'
      exact h.uniq _ _ _ _ _ _ _ hq hq'
    · obtain ⟨h1, h2⟩ := hfresh q hq
      simp only [update_of_ne h1]; exact h.fresh q h2
    · simp at hr
  · -- returned: no-op
    rw [step_done hl]
    have hp : p ∈ σ := h.mem_of_ne_start (by rw [hl]; simp)
    refine ⟨h.len, fun w hw => ?_, h.res_first, h.loc_ok, h.uniq, fun q hq => ?_,
      fun hr => ?_⟩
    · obtain ⟨q, hq, e⟩ := h.vals_in w hw; exact ⟨q, hσ q hq, e⟩
    · exact h.fresh q (hfresh q hq).2
    · exact absurd hl ((h.count hr).2 p w)

end StepInv

lemma inv_exec (x : ℕ → V) (σ : List ℕ) : Inv x σ ((alg2 V).exec x σ) := by
  induction σ using List.reverseRecOn with
  | nil => exact Inv.init x
  | append_singleton σ p ih => rw [Alg.exec_concat]; exact ih.step p

lemma out_iff {C : Conf V} {p : ℕ} {v : V} : C.Out p v ↔ C.loc p = .done v := by
  unfold Cfg.Out
  change act V (C.loc p) = _ ↔ _
  cases C.loc p <;> simp [act]

/-! ### Agreement and validity (any concurrency) -/

/-- Agreement of Algorithm 2, for all finite schedules (any concurrency): every returned value is
the first value written to the iterator stack. -/
theorem agreement : Agreement (alg2 V) anySched := by
  intro x σ _ p _ q _ v w hv hw
  have h := inv_exec x σ
  have h1 := h.loc_ok p
  have h2 := h.loc_ok q
  rw [out_iff.1 hv] at h1
  rw [out_iff.1 hw] at h2
  simp only [LocOK] at h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- Validity of Algorithm 2, for all finite schedules (any concurrency). -/
theorem validity : Validity (alg2 V) anySched := by
  intro x σ _ p _ v hv
  have h := inv_exec x σ
  have h1 := h.loc_ok p
  rw [out_iff.1 hv] at h1
  exact h.vals_in v (List.mem_of_getLast? h1)

/-! ### Wait-freedom under bounded concurrency -/

/-- Potential number of writes to the iterator stack: the writes performed so far plus the
processes poised to write. -/
def pot (σ : List ℕ) (C : Conf V) : ℕ := (stk C).its.length + cnt σ C.loc isW

/-- While `result = ⊥`, all writers to the stack (and processes poised to write) are active. -/
lemma pot_le_active (x : ℕ → V) (σ : List ℕ) (hr : res ((alg2 V).exec x σ) = none) :
    pot σ ((alg2 V).exec x σ) ≤ (active (alg2 V) x σ).ncard := by
  have h := inv_exec x σ
  unfold pot
  rw [(h.count hr).1]
  unfold cnt
  rw [← Finset.card_filter, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ ((σ.toFinset.finite_toSet).subset (fun q hq => List.mem_toFinset.2 hq.1))
  intro q hq
  simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_ofPred_eq] at hq
  refine ⟨hq.1, fun v hv => ?_⟩
  rw [out_iff.1 hv] at hq
  simp [isWLF] at hq

lemma pot_step {x : ℕ → V} {σ : List ℕ} {C : Conf V} (h : Inv x σ C) (p : ℕ) :
    res (C.step p) = none ∨ pot (σ ++ [p]) (C.step p) ≤ pot σ C := by
  have hcnt : ∀ (l : ℕ → Loc V), (∀ q, q ≠ p → l q = C.loc q) → (p ∉ σ → isW (C.loc p) = false) →
      cnt (σ ++ [p]) l isW + (if isW (C.loc p) then 1 else 0) =
        cnt σ C.loc isW + (if isW (l p) then 1 else 0) :=
    fun l hl hp => cnt_step σ p C.loc l isW hl hp
  have hfr : p ∉ σ → isW (C.loc p) = false := fun hp => by rw [h.fresh p hp]; rfl
  rcases hl : C.loc p with v | v | ⟨v, k, prev⟩ | w | w
  · rw [step_start hl]
    rcases hr : res C with _ | w
    · left; exact hr
    · right
      have := hcnt (Function.update C.loc p (afterRead v (res C)))
        (fun q hq => Function.update_of_ne hq _ _) hfr
      simp only [hr, afterRead] at this ⊢
      simp only [Function.update_self, hl, isW] at this
      simp only [pot, stk_mk]
      simp at this; change (stk C).its.length + _ ≤ (stk C).its.length + _; omega
  · right
    rw [step_write hl]
    have := hcnt (Function.update C.loc p (.loop v (stk C).its.length none))
      (fun q hq => Function.update_of_ne hq _ _) hfr
    simp only [Function.update_self, hl, isW] at this
    simp only [pot, stk_mk, Function.update_self, List.length_append, List.length_singleton]
    simp at this; change _ ≤ (stk C).its.length + _; omega
  · right
    obtain ⟨-, pos, hpos, -⟩ := (show LocOK (x p) (stk C) (.loop v k prev) from hl ▸ h.loc_ok p)
    rw [step_loop hl hpos]
    have := hcnt (Function.update C.loc p (afterIt v k prev ((stk C).at pos)))
      (fun q hq => Function.update_of_ne hq _ _) hfr
    have hW : isW (afterIt v k prev ((stk C).at pos)) = false := by
      cases (stk C).at pos <;> rfl
    simp only [Function.update_self, hW] at this
    simp only [hl, isW] at this
    simp only [pot, stk_mk, Function.update_self, List.length_set]
    simp at this; change _ ≤ (stk C).its.length + _; omega
  · right
    rw [step_fin hl]
    have := hcnt (Function.update C.loc p (.done w)) (fun q hq => Function.update_of_ne hq _ _) hfr
    simp only [Function.update_self, hl, isW] at this
    simp only [pot, stk_mk]
    simp at this
    have e : (Function.update C.mem Obj.result (some w : Option V) Obj.stack : ISState V) =
      stk C := by simp [stk]
    rw [e]; omega
  · right
    rw [step_done hl]
    simp only [pot, cnt_mono σ p C.loc isW hfr, le_refl]

/-- Under bounded concurrency `n`, at most `n` values are ever written to the iterator stack. -/
lemma pot_bound (x : ℕ → V) (s : ℕ → ℕ) (n : ℕ)
    (hn : ∀ t, (active (alg2 V) x (pre s t)).ncard ≤ n) (t : ℕ) :
    pot (pre s t) ((alg2 V).exec x (pre s t)) ≤ n := by
  induction t with
  | zero => simp [pot, cnt, stk, Alg.initCfg, alg2]
  | succ t ih =>
    rcases pot_step (inv_exec x (pre s t)) (s t) with hr | hr
    · rw [← Alg.exec_concat, ← pre_succ] at hr
      exact (pot_le_active x _ hr).trans (hn _)
    · rw [pre_succ, Alg.exec_concat]; exact hr.trans ih

/-- A progress measure of process `p`, given a bound `n` on the number of writes to the stack: it
decreases at every step of `p` (until `p` returns) and is not changed by steps of the other
processes. In the loop, it decreases with the position of the own iterator, which is at most
`n + 1`. -/
def μ (n : ℕ) (C : Conf V) (p : ℕ) : ℕ :=
  match C.loc p with
  | .start _ => n + 5
  | .write _ => n + 4
  | .loop _ k _ => 2 + (n + 2 - ((stk C).its[k]?.getD 0))
  | .fin _ => 1
  | .done _ => 0

lemma μ_self {x : ℕ → V} {σ : List ℕ} {C : Conf V} (h : Inv x σ C) {n : ℕ}
    (hn : (stk C).its.length ≤ n) {p : ℕ} (hp : ∀ w, C.loc p ≠ .done w) :
    μ n (C.step p) p < μ n C p := by
  have hok := h.loc_ok p
  rcases hl : C.loc p with v | v | ⟨v, k, prev⟩ | w | w <;> rw [hl] at hok
  · rw [step_start hl]
    simp only [μ, Function.update_self, hl]
    cases res C <;> simp [afterRead]
  · rw [step_write hl]
    simp only [μ, Function.update_self, hl, stk_mk]
    simp; omega
  · obtain ⟨hv, pos, hpos, h1, h2⟩ := hok
    rw [step_loop hl hpos]
    have hk : k < (stk C).its.length := h.lt_of_loop hl
    have hle : pos ≤ (stk C).its.length + 1 := by
      rw [h.len]
      cases prev with
      | none => rw [h1 rfl]; omega
      | some w => exact (h2 w rfl).2.1
    rcases hat : (stk C).at pos with _ | w'
    · simp only [μ, Function.update_self, hl, hpos, Option.getD_some, afterIt]
      omega
    · have hpl : pos ≤ (stk C).its.length := by
        unfold ISState.at at hat
        split_ifs at hat
        have := (List.getElem?_eq_some_iff.1 hat).1
        rw [h.len]; omega
      simp only [μ, Function.update_self, hl, stk_mk, hpos, Option.getD_some, afterIt]
      simp [hk]; omega
  · rw [step_fin hl]
    simp [μ, hl]
  · exact absurd hl (hp w)

lemma stk_step_its_of_loop {x : ℕ → V} {σ : List ℕ} {C : Conf V} (h : Inv x σ C) {p q : ℕ}
    (hqp : q ≠ p) {v : V} {k : ℕ} {prev : Option V} (hl : C.loc p = .loop v k prev) :
    (stk (C.step q)).its[k]? = (stk C).its[k]? := by
  have hk := h.lt_of_loop hl
  have hok := h.loc_ok q
  rcases hq : C.loc q with v' | v' | ⟨v', k', prev'⟩ | w | w <;> rw [hq] at hok
  · rw [step_start hq]; rfl
  · rw [step_write hq]; simp [List.getElem?_append_left hk]
  · obtain ⟨-, pos, hpos, -⟩ := hok
    rw [step_loop hq hpos]
    have hne : k' ≠ k := fun e => hqp (h.uniq _ _ _ _ _ _ _ hq (e ▸ hl))
    simp [List.getElem?_set_ne hne]
  · rw [step_fin hq]; simp [stk]
  · rw [step_done hq]

lemma μ_other {x : ℕ → V} {σ : List ℕ} {C : Conf V} (h : Inv x σ C) (n : ℕ) {p q : ℕ}
    (hqp : q ≠ p) : μ n (C.step q) p = μ n C p := by
  have hloc : (C.step q).loc p = C.loc p := Cfg.step_loc_other C (Ne.symm hqp)
  unfold μ
  rw [hloc]
  rcases hl : C.loc p with v | v | ⟨v, k, prev⟩ | w | w
  · rfl
  · rfl
  · simp only; rw [stk_step_its_of_loop h hqp hl]
  · rfl
  · rfl

/-- **Wait-freedom of Algorithm 2 in the bounded concurrency model.** -/
theorem bcWaitFree : BCWaitFree (alg2 V) := by
  intro x s ⟨n, hn⟩ p hinf
  by_contra hno
  push Not at hno
  have hW : ∀ t, (stk ((alg2 V).exec x (pre s t))).its.length ≤ n := fun t =>
    le_trans (Nat.le_add_right _ _) (pot_bound x s n hn t)
  set m : ℕ → ℕ := fun t => μ n ((alg2 V).exec x (pre s t)) p with hm
  have hstep : ∀ t, m (t + 1) ≤ m t ∧ (s t = p → m (t + 1) < m t) := by
    intro t
    simp only [hm, pre_succ, Alg.exec_concat]
    by_cases ht : s t = p
    · rw [ht]
      have := μ_self (inv_exec x (pre s t)) (hW t)
        (fun w hw => hno t w (out_iff.2 hw))
      exact ⟨this.le, fun _ => this⟩
    · rw [μ_other (inv_exec x (pre s t)) n ht]
      exact ⟨le_rfl, fun e => absurd e ht⟩
  have hanti : Antitone m := antitone_nat_of_succ_le (fun t => (hstep t).1)
  have hdec : ∀ j, ∃ t, m t + j ≤ m 0 := by
    intro j
    induction j with
    | zero => exact ⟨0, le_rfl⟩
    | succ j ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨u, hu, hsu⟩ := hinf t
      refine ⟨u + 1, ?_⟩
      have h1 := (hstep u).2 hsu
      have h2 := hanti hu
      omega
  obtain ⟨t, ht⟩ := hdec (m 0 + 1)
  omega

/-! ### Theorem 12 -/

/-- **Theorem 12 of [AMW11]** (Afek, Morrison, Wertheim, *From bounded to unbounded concurrency
objects and back*, PODC 2011): Algorithm 2 (a register and one iterator stack) is a wait-free
bounded-concurrency consensus implementation. Agreement and validity hold for every finite
schedule (at any concurrency); every process that takes infinitely many steps of an infinite
execution with bounded concurrency (bound unknown to the algorithm) returns. -/
theorem theorem_12 :
    Agreement (alg2 V) anySched ∧ Validity (alg2 V) anySched ∧ BCWaitFree (alg2 V) :=
  ⟨agreement, validity, bcWaitFree⟩

/-- Consequence of Theorem 12 (Section 5.2: "the iterator stack's consensus number is
infinite"): for every `n`, Algorithm 2 solves wait-free consensus among `n` processes
`p₀, …, p_{n-1}`. -/
theorem solvesCons_boundedBy (n : ℕ) : SolvesCons (alg2 V) anySched (boundedBy n) :=
  ⟨agreement, validity, bcWaitFree.waitFree_boundedBy n⟩

/-! ### Algorithm 2 is not wait-free under unbounded concurrency -/

/-- The bad schedule: `p₀` reads `result` and writes; then, for `i = 1, 2, …`, the new process
`pᵢ` reads `result = ⊥` and writes to the stack, and `p₀` reads its iterator once. -/
def badSched (t : ℕ) : ℕ :=
  if t < 2 then 0 else if (t - 2) % 3 = 2 then 0 else (t - 2) / 3 + 1

lemma pre_badSched_succ (i : ℕ) :
    pre badSched (2 + 3 * (i + 1)) = pre badSched (2 + 3 * i) ++ [i + 1, i + 1, 0] := by
  rw [show 2 + 3 * (i + 1) = (2 + 3 * i) + 3 by omega, pre_add]
  congr 1
  have h0 : badSched (2 + 3 * i) = i + 1 := by
    unfold badSched
    split_ifs <;> omega
  have h1 : badSched (2 + 3 * i + 1) = i + 1 := by
    unfold badSched
    split_ifs <;> omega
  have h2 : badSched (2 + 3 * i + 2) = 0 := by
    unfold badSched
    split_ifs <;> omega
  simp [pre, List.range_succ, h0, h1, h2]

/-- The configuration of the bad execution after `i` rounds. -/
lemma bad_inv (x : ℕ → V) (i : ℕ) :
    res ((alg2 V).exec x (pre badSched (2 + 3 * i))) = none ∧
    (∃ prev, ((alg2 V).exec x (pre badSched (2 + 3 * i))).loc 0 = .loop (x 0) 0 prev) ∧
    (stk ((alg2 V).exec x (pre badSched (2 + 3 * i)))).its[0]? = some (i + 1) ∧
    (stk ((alg2 V).exec x (pre badSched (2 + 3 * i)))).vals.length = i + 1 ∧
    ∀ q, i < q → ((alg2 V).exec x (pre badSched (2 + 3 * i))).loc q = .start (x q) := by
  induction i with
  | zero =>
    have hpre : pre badSched 2 = [0, 0] := by simp [pre, List.range_succ, badSched]
    simp only [Nat.mul_zero, Nat.add_zero, hpre]
    set C0 := (alg2 V).initCfg x
    have hl0 : C0.loc 0 = .start (x 0) := rfl
    have hr0 : res C0 = none := rfl
    have e1 := step_start hl0
    rw [hr0] at e1
    have hl1 : (C0.step 0).loc 0 = .write (x 0) := by rw [e1]; simp [afterRead]
    have e2 := step_write hl1
    rw [show [0, 0] = ([] ++ [0]) ++ [0] from rfl, Alg.exec_concat, Alg.exec_concat,
      Alg.exec_nil, e2]
    refine ⟨?_, ⟨none, by simp [e1]; rfl⟩, ?_, ?_, fun q hq => ?_⟩
    · simp [res, e1]; rfl
    · simp [e1]; rfl
    · simp [e1]; rfl
    · simp only [Function.update_of_ne (show q ≠ 0 by omega), e1]; rfl
  | succ i ih =>
    obtain ⟨hr, ⟨prev, hl0⟩, hit, hlen, hq⟩ := ih
    rw [pre_badSched_succ, show [i + 1, i + 1, 0] = [i + 1] ++ [i + 1] ++ [0] from rfl,
      ← List.append_assoc, ← List.append_assoc, Alg.exec_concat, Alg.exec_concat, Alg.exec_concat]
    set C := (alg2 V).exec x (pre badSched (2 + 3 * i))
    have e1 := step_start (hq (i + 1) (by omega))
    rw [hr] at e1
    have hl1 : (C.step (i + 1)).loc (i + 1) = .write (x (i + 1)) := by rw [e1]; simp [afterRead]
    have e2 := step_write hl1
    set C2 := (C.step (i + 1)).step (i + 1)
    have hl2 : C2.loc 0 = .loop (x 0) 0 prev := by
      simp only [C2, e2, Function.update_of_ne (show (0 : ℕ) ≠ i + 1 by omega), e1]; exact hl0
    have hstk2 : stk C2 = ⟨x (i + 1) :: (stk C).vals, (stk C).its ++ [1]⟩ := by
      simp only [C2, e2, stk_mk, Function.update_self, e1]; rfl
    have hit2 : (stk C2).its[0]? = some (i + 1) := by
      rw [hstk2]
      have : 0 < (stk C).its.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hit; cases hit
      simp only
      rw [List.getElem?_append_left this]; exact hit
    have e3 := step_loop hl2 hit2
    have hat : (stk C2).at (i + 1) = (x (i + 1) :: (stk C).vals)[i]? := by
      rw [hstk2]; simp [ISState.at]
    have hlt : i < (x (i + 1) :: (stk C).vals).length := by simp; omega
    set w := (x (i + 1) :: (stk C).vals)[i] with hw'
    have hw : (x (i + 1) :: (stk C).vals)[i]? = some w := List.getElem?_eq_getElem hlt
    rw [e3]
    refine ⟨?_, ⟨some w, ?_⟩, ?_, ?_, fun q hq' => ?_⟩
    · simp only [res_mk, C2, e2, e1]
      simp [res] at hr ⊢; exact hr
    · simp [hat, hw, afterIt]
    · simp [hstk2]
    · simp [hstk2, hlen]
    · simp only [Function.update_of_ne (show q ≠ 0 by omega), C2, e2,
        Function.update_of_ne (show q ≠ i + 1 by omega), e1]
      exact hq q (by omega)

/-- Algorithm 2 is **not** wait-free under unbounded concurrency (all infinite schedules, model
`M₃`): new processes keep arriving, reading `result = ⊥` and writing to the stack, and `p₀`'s
iterator never runs off the end of the stack. (Section 5.2 of [AMW11].) -/
theorem not_waitFree_infArrival [Inhabited V] : ¬ WaitFree (alg2 V) infArrival := by
  intro hwf
  have hinf : InfOften badSched 0 := by
    intro N
    refine ⟨2 + 3 * N + 2, by omega, ?_⟩
    unfold badSched
    split_ifs <;> omega
  obtain ⟨t, v, hv⟩ := hwf (fun _ => default) badSched trivial 0 hinf
  obtain ⟨τ, hτ⟩ := pre_prefix badSched (show t ≤ 2 + 3 * t by omega)
  have hout := Alg.Cfg.Out.run hv τ
  rw [← Alg.exec_append, hτ, out_iff] at hout
  obtain ⟨-, ⟨prev, hl⟩, -⟩ := bad_inv (V := V) (fun _ => default) t
  rw [hl] at hout
  cases hout

end Podc.UnboundedConcurrency.Alg2
