import Mathlib
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Progress
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Objects.MaxRegister

/-!
# A max register from a single CAS object (Appendix B)

Chockler, Spiegelman. *Space Complexity of Fault-Tolerant Register Emulations.* PODC 2017
(arXiv 1705.07212v1), Appendix B, Algorithm 1:

```
write-max(v):  while true do
                 tmp ← b.CAS(v₀, v₀)          -- line 3
                 if tmp ≥ v then return ok    -- lines 4–5
                 b.CAS(tmp, v)                -- line 6
read-max():    tmp ← b.CAS(v₀, v₀); return tmp   -- lines 8–9
```

The base object `b` is a compare-and-swap object that returns its previous value (`casPrev`).

## Model
CSLib's asynchronous shared-memory model (`Cslib.SharedMemory`): deterministic processes, atomic
base objects, executions as label lists, linearizability (`Impl.Linearizable`), wait-freedom
(`Impl.WaitFree`). The algorithm is parametrized by a linear order `V` of values with initial
value `v₀`, and by any high-level object `A` that *is* a max register over `(V, v₀)` up to the
naming of operations and responses (`MaxIface`). Instances: CSLib's `maxRegObj` over `ℕ`
(`natIface`) and the generic max register `maxRegLin V v₀` (`linIface`).

## Results
* `linearizable` — **Lemma 5**: every execution has a linearization, built at the linearization
  points of Definition 4 (see `Inv`). Holds over every linear order.
* `waitFree_iff` — wait-freedom holds **iff** every interval `[v₀, c)` of `V` has no infinite
  strictly increasing sequence (`WellFoundedGT (Set.Ico v₀ c)`), for any set of at least two
  processes.
* `waitFree_of_locallyFinite`, `natImpl_waitFree` — **Theorem 4** for locally finite orders
  (the paper's proof: "assume there are `k` values between `v'` and `v`") and for `ℕ`.
* `ratImpl_not_waitFree` — **Theorem 4 fails over `ℚ`**: one `write-max(1)` takes infinitely many
  steps while another process completes `write-max(1 - 1/(k+2))` for `k = 0, 1, …` between each
  of its reads and CASes (`not_waitFree_of_strictMono`).
* `lockFree`, `ratImpl_lockFree` — over every linear order (finitely many processes) the
  algorithm is lock-free; so over `ℚ` it is a lock-free but not wait-free max register.
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.MaxRegisterCAS

open Cslib.SharedMemory

/-! ### The base object and the emulated object -/

/-- A compare-and-swap object over `V` (initially `v₀`) whose single operation `CAS (exp, new)`
sets the value to `new` if it equals `exp`, and returns the *previous* value (as in the paper).
-- CSLib candidate (CSLib's `casObject` returns a success flag instead). -/
abbrev casPrev (V : Type) [DecidableEq V] (v₀ : V) : ObjSpec where
  State := V
  Op := V × V
  Resp := V
  init := v₀
  δ q o := (if q = o.1 then o.2 else q, q)

/-- Operations of the generic max register. -/
inductive LinMaxOp (V : Type) where
  | writeMax (v : V)
  | readMax

/-- The max register over a linear order `V`, initially `v₀`; `writeMax` returns `v₀` as an
acknowledgement. -/
abbrev maxRegLin (V : Type) [LinearOrder V] (v₀ : V) : ObjSpec where
  State := V
  Op := LinMaxOp V
  Resp := V
  init := v₀
  δ q
    | .writeMax v => (max q v, v₀)
    | .readMax => (q, q)

/-- An object `A` *is a max register over `(V, v₀)`*: its operations are `writeMax v`
(`arg o = some v`, response `ack`) and `readMax` (`arg o = none`, response `out` of the
current value), and its state abstracts to the current maximum `val`. -/
structure MaxIface (A : ObjSpec) (V : Type) [LinearOrder V] (v₀ : V) where
  /-- The argument of a `writeMax` (`none` for `readMax`). -/
  arg : A.Op → Option V
  /-- The `writeMax` operation with a given argument. -/
  wr : V → A.Op
  /-- The current value of the max register. -/
  val : A.State → V
  /-- The response of `readMax` returning a value. -/
  out : V → A.Resp
  /-- The response of `writeMax` (`ok`). -/
  ack : A.Resp
  arg_wr : ∀ v, arg (wr v) = some v
  val_init : val A.init = v₀
  δ_write : ∀ q o v, arg o = some v → val (A.δ q o).1 = max (val q) v ∧ (A.δ q o).2 = ack
  δ_read : ∀ q o, arg o = none → val (A.δ q o).1 = val q ∧ (A.δ q o).2 = out (val q)

/-- CSLib's max register over `ℕ` is a max register over `(ℕ, 0)`. -/
def natIface : MaxIface maxRegObj ℕ 0 where
  arg | .writeMax v => some v | .readMax => none
  wr v := .writeMax v
  val q := q
  out r := r
  ack := 0
  arg_wr _ := rfl
  val_init := rfl
  δ_write q o v h := by cases o <;> simp_all
  δ_read q o h := by cases o <;> simp_all

/-- The generic max register over `(V, v₀)`. -/
def linIface (V : Type) [LinearOrder V] (v₀ : V) : MaxIface (maxRegLin V v₀) V v₀ where
  arg | .writeMax v => some v | .readMax => none
  wr v := .writeMax v
  val q := q
  out r := r
  ack := v₀
  arg_wr _ := rfl
  val_init := rfl
  δ_write q o v h := by cases o <;> simp_all
  δ_read q o h := by cases o <;> simp_all

/-! ### Algorithm 1 -/

/-- Local states of Algorithm 1 (program counters). -/
inductive Loc (V : Type) where
  /-- No pending operation. -/
  | idle
  /-- `write-max(v)` about to execute line 3. -/
  | wRead (v : V)
  /-- `write-max(v)` about to execute line 6 with `tmp`. -/
  | wCas (v tmp : V)
  /-- `write-max` about to return `ok` (line 5). -/
  | wDone
  /-- `read-max()` about to execute line 8. -/
  | rRead
  /-- `read-max()` about to return `r` (line 9). -/
  | rDone (r : V)

variable {A : ObjSpec} {V : Type} [LinearOrder V] {v₀ : V}

/-- **Algorithm 1** of [CS17]: a max register `A` (over `(V, v₀)`) from the single CAS object
`casPrev V v₀`, for processes `P`. -/
def alg (M : MaxIface A V v₀) (P : Type) : Impl A (fun _ : Unit => casPrev V v₀) P (Loc V) where
  memInit _ := v₀
  locInit _ := .idle
  invoke _ _ o := match M.arg o with
    | some v => .wRead v
    | none => .rRead
  act _ l := match l with
    | .idle => .ret M.ack .idle
    | .wRead v => .access () (v₀, v₀) (fun tmp => if v ≤ tmp then .wDone else .wCas v tmp)
    | .wCas v tmp => .access () (tmp, v) (fun _ => .wRead v)
    | .wDone => .ret M.ack .idle
    | .rRead => .access () (v₀, v₀) (fun tmp => .rDone tmp)
    | .rDone r => .ret (M.out r) .idle

/-- Algorithm 1 implementing CSLib's max register `maxRegObj` over `ℕ` (CAS over `ℕ`, `v₀ = 0`). -/
abbrev natImpl (P : Type) : Impl maxRegObj (fun _ : Unit => casPrev ℕ 0) P (Loc ℕ) :=
  alg natIface P

/-- Algorithm 1 over `ℚ` (initial value `0`). -/
abbrev ratImpl (P : Type) : Impl (maxRegLin ℚ 0) (fun _ : Unit => casPrev ℚ 0) P (Loc ℚ) :=
  alg (linIface ℚ 0) P

/-! ### Lemma 5: linearizability -/

section Lin

variable (M : MaxIface A V v₀) {P : Type} [DecidableEq P]

/-- The status of a process with local state `l`, pending operation `pd` and current instance `x`,
relative to the linearization `L` built so far and the value `m` of `b`. It encodes the
linearization points of **Definition 4**: a `write-max(v)` is linearized at its successful
`b.CAS(tmp, v)` (line 6) if it has one, and otherwise at the (last) `b.CAS(v₀, v₀)` of line 3,
which returns a value `≥ v`; a `read-max` is linearized at line 8. In particular a `write-max(v)`
waiting at line 3 that is already linearized sees `v ≤ m`, and one waiting at line 6 is not
linearized yet. -/
def Good (L : List (OpId P × A.Op)) (m : V) (x : OpId P) (pd : Option A.Op) : Loc V → Prop
  | .idle => pd = none
  | .wRead v => ∃ o, pd = some o ∧ M.arg o = some v ∧ (x ∈ L.map Prod.fst → v ≤ m)
  | .wCas v tmp => ∃ o, pd = some o ∧ M.arg o = some v ∧ x ∉ L.map Prod.fst ∧ tmp < v
  | .wDone => ∃ o v, pd = some o ∧ M.arg o = some v ∧ x ∈ L.map Prod.fst
  | .rRead => ∃ o, pd = some o ∧ M.arg o = none ∧ x ∉ L.map Prod.fst
  | .rDone r => pd ≠ none ∧ ∃ L₁ L₂ o, L = L₁ ++ (x, o) :: L₂ ∧
      (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).2 = M.out r

/-- The invariant of Algorithm 1: `L` is a linearization of `α`, built at the linearization
points of Definition 4 (`Good`), and `b` holds the value of the max register after `L`. -/
structure Inv (α : List (Label P A)) (C : Config A (fun _ : Unit => casPrev V v₀) P (Loc V))
    (L : List (OpId P × A.Op)) : Prop where
  lin : IsLinearization α L
  mem : C.mem () = M.val (linState L)
  good : ∀ p, Good M L (C.mem ()) (curOp α p) (C.pend p) (C.loc p)

variable {M}

lemma good_frame {L N : List (OpId P × A.Op)} {m m' : V} {x : OpId P} {pd : Option A.Op}
    {l : Loc V} (hN : x ∉ N.map Prod.fst) (hm : m ≤ m') (h : Good M L m x pd l) :
    Good M (L ++ N) m' x pd l := by
  cases l with
  | idle => exact h
  | wRead v =>
    obtain ⟨o, h1, h2, h3⟩ := h
    refine ⟨o, h1, h2, fun hx => (h3 ?_).trans hm⟩
    simp only [List.map_append, List.mem_append] at hx; exact hx.resolve_right hN
  | wCas v tmp =>
    obtain ⟨o, h1, h2, h3, h4⟩ := h
    exact ⟨o, h1, h2, by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h3, hN⟩, h4⟩
  | wDone =>
    obtain ⟨o, v, h1, h2, h3⟩ := h
    exact ⟨o, v, h1, h2, by simp only [List.map_append, List.mem_append]; exact Or.inl h3⟩
  | rRead =>
    obtain ⟨o, h1, h2, h3⟩ := h
    exact ⟨o, h1, h2, by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h3, hN⟩⟩
  | rDone r =>
    obtain ⟨h1, L₁, L₂, o, rfl, h2⟩ := h
    exact ⟨h1, L₁, L₂ ++ N, o, by simp, h2⟩

lemma good_frame' {L : List (OpId P × A.Op)} {m m' : V} {x : OpId P} {pd : Option A.Op}
    {l : Loc V} (hm : m ≤ m') (h : Good M L m x pd l) : Good M L m' x pd l := by
  simpa using good_frame (N := []) (by simp) hm h

lemma curOp_append_of_ne {α : List (Label P A)} {ℓ : Label P A} {q : P} (h : ℓ.proc ≠ q) :
    curOp (α ++ [ℓ]) q = curOp α q := by
  cases ℓ <;> simp_all [curOp, Label.proc]

lemma curOp_append_tau (α : List (Label P A)) (p q : P) :
    curOp (α ++ [.tau p]) q = curOp α q := by
  simp [curOp]

lemma curOp_append_inv (α : List (Label P A)) (p q : P) (o : A.Op) :
    curOp (α ++ [.inv p o]) q = curOp α q := by
  simp [curOp]

lemma linState_concat (L : List (OpId P × A.Op)) (x : OpId P) (o : A.Op) :
    linState (L ++ [(x, o)]) = (A.δ (linState L) o).1 := by
  simp [linState, ObjSpec.runOps]

/-- The invariant is preserved by every step; the value of `b` never decreases
(Observation 2 of [CS17]). -/
theorem inv_step {α : List (Label P A)} {C C' : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)}
    {L : List (OpId P × A.Op)} {ℓ : Label P A} (hα : (alg M P).run α = some C) (hI : Inv M α C L)
    (h : (alg M P).step C ℓ = some C') :
    ∃ L', Inv M (α ++ [ℓ]) C' L' ∧ C.mem () ≤ C'.mem () := by
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hx : curOp α p ∉ L.map Prod.fst := fun hm =>
      (alg M P).not_invoked_curOp_of_idle hα h0 (hI.lin.mem_invoked hm)
    refine ⟨L, ⟨hI.lin.append_inv p o, by rw [hmem]; exact hI.mem, fun q => ?_⟩, by rw [hmem]⟩
    rw [hmem, hpend, hloc, curOp_append_inv]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self, alg]
      cases ha : M.arg o with
      | some v => exact ⟨o, rfl, ha, fun h => absurd h hx⟩
      | none => exact ⟨o, rfl, ha, hx⟩
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]; exact hI.good q
  | tau p =>
    have h0 := (Impl.step_tau h).1
    have hgp := hI.good p
    set m := C.mem () with hm
    set x := curOp α p with hx
    cases hl : C.loc p with
    | wRead v =>
      rw [hl] at hgp
      obtain ⟨o, hpo, hav, hxv⟩ := hgp
      obtain ⟨-, hnc, hop⟩ := (alg M P).run_pend_curOp hα hpo
      have hact : (alg M P).act p (C.loc p) =
          .access () (v₀, v₀) (fun tmp => if v ≤ tmp then .wDone else .wCas v tmp) := by
        rw [hl]; rfl
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      have hm1 : (if m = v₀ then v₀ else m) = m := by split_ifs with h1 <;> simp [h1]
      by_cases hvm : v ≤ m
      · by_cases hxL : x ∈ L.map Prod.fst
        · refine ⟨L, ⟨hI.lin.append_tau p, ?_, fun q => ?_⟩, ?_⟩
          · simpa [hm1, ← hm] using hI.mem
          · simp only [Function.update_self, hm1, ← hm, curOp_append_tau]
            by_cases hq : q = p
            · subst hq; simp only [Function.update_self, hvm, ite_true]
              exact ⟨o, v, hpo, hav, hxL⟩
            · rw [Function.update_of_ne hq]; exact hI.good q
          · simp [hm1, ← hm]
        · refine ⟨L ++ [(x, o)], ⟨(hI.lin.push hop hxL hnc).append_tau p, ?_, fun q => ?_⟩, ?_⟩
          · simp only [Function.update_self, hm1, ← hm, linState_concat,
              (M.δ_write _ _ _ hav).1, ← hI.mem, max_eq_left hvm]
          · simp only [Function.update_self, hm1, ← hm, curOp_append_tau]
            by_cases hq : q = p
            · subst hq; simp only [Function.update_self, hvm, ite_true]
              exact ⟨o, v, hpo, hav, by simp [x]⟩
            · rw [Function.update_of_ne hq]
              refine good_frame ?_ le_rfl (hI.good q)
              simp [x, curOp, hq]
          · simp [hm1, ← hm]
      · refine ⟨L, ⟨hI.lin.append_tau p, ?_, fun q => ?_⟩, ?_⟩
        · simpa [hm1, ← hm] using hI.mem
        · simp only [Function.update_self, hm1, ← hm, curOp_append_tau]
          by_cases hq : q = p
          · subst hq; simp only [Function.update_self, hvm, ite_false]
            exact ⟨o, hpo, hav, fun h => hvm (hxv h), lt_of_not_ge hvm⟩
          · rw [Function.update_of_ne hq]; exact hI.good q
        · simp [hm1, ← hm]
    | wCas v tmp =>
      rw [hl] at hgp
      obtain ⟨o, hpo, hav, hxL, htv⟩ := hgp
      obtain ⟨-, hnc, hop⟩ := (alg M P).run_pend_curOp hα hpo
      have hact : (alg M P).act p (C.loc p) = .access () (tmp, v) (fun _ => .wRead v) := by
        rw [hl]; rfl
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      by_cases hmt : m = tmp
      · have hmv : m ≤ v := hmt ▸ htv.le
        refine ⟨L ++ [(x, o)], ⟨(hI.lin.push hop hxL hnc).append_tau p, ?_, fun q => ?_⟩, ?_⟩
        · simp only [Function.update_self, ← hm, hmt, ite_true, linState_concat,
            (M.δ_write _ _ _ hav).1, ← hI.mem, max_eq_right htv.le]
        · simp only [Function.update_self, ← hm, hmt, ite_true, curOp_append_tau]
          by_cases hq : q = p
          · subst hq; simp only [Function.update_self]
            exact ⟨o, hpo, hav, fun _ => le_rfl⟩
          · rw [Function.update_of_ne hq]
            refine good_frame ?_ hmv (hI.good q)
            simp [x, curOp, hq]
        · simp [← hm, hmt, htv.le]
      · refine ⟨L, ⟨hI.lin.append_tau p, ?_, fun q => ?_⟩, ?_⟩
        · simpa [← hm, hmt] using hI.mem
        · simp only [Function.update_self, ← hm, hmt, ite_false, curOp_append_tau]
          by_cases hq : q = p
          · subst hq; simp only [Function.update_self]
            exact ⟨o, hpo, hav, fun h => absurd h hxL⟩
          · rw [Function.update_of_ne hq]; exact hI.good q
        · simp [← hm, hmt]
    | rRead =>
      rw [hl] at hgp
      obtain ⟨o, hpo, hao, hxL⟩ := hgp
      obtain ⟨-, hnc, hop⟩ := (alg M P).run_pend_curOp hα hpo
      have hact : (alg M P).act p (C.loc p) = .access () (v₀, v₀) (fun tmp => .rDone tmp) := by
        rw [hl]; rfl
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      have hm1 : (if m = v₀ then v₀ else m) = m := by split_ifs with h1 <;> simp [h1]
      refine ⟨L ++ [(x, o)], ⟨(hI.lin.push hop hxL hnc).append_tau p, ?_, fun q => ?_⟩, ?_⟩
      · simp only [Function.update_self, hm1, ← hm, linState_concat,
          (M.δ_read _ _ hao).1, ← hI.mem]
      · simp only [Function.update_self, hm1, ← hm, curOp_append_tau]
        by_cases hq : q = p
        · subst hq; simp only [Function.update_self]
          refine ⟨by simp [hpo], L, [], o, rfl, ?_⟩
          rw [(M.δ_read _ _ hao).2]; exact congrArg M.out hI.mem.symm
        · rw [Function.update_of_ne hq]
          refine good_frame ?_ le_rfl (hI.good q)
          simp [x, curOp, hq]
      · simp [hm1, ← hm]
    | idle =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
      rw [hl] at hact; simp [alg] at hact
    | wDone =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
      rw [hl] at hact; simp [alg] at hact
    | rDone r =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
      rw [hl] at hact; simp [alg] at hact
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    have hgp := hI.good p
    have hrest : ∀ q, q ≠ p → Good M L (C'.mem ()) (curOp (α ++ [.ret p r]) q) (C'.pend q)
        (C'.loc q) := by
      intro q hq
      rw [hmem, hpend, hloc, Function.update_of_ne hq, Function.update_of_ne hq,
        curOp_append_of_ne (Ne.symm hq)]
      exact hI.good q
    cases hl : C.loc p with
    | wDone =>
      rw [hl] at hgp hact
      simp only [alg, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      obtain ⟨o, v, hpo, hav, hxL⟩ := hgp
      obtain ⟨y, hyL, hyx⟩ := List.mem_map.1 hxL
      obtain ⟨L₁, L₂, hs⟩ := List.append_of_mem hyL
      have hop := hI.lin.op_eq y hyL
      rw [hyx, ((alg M P).run_pend_curOp hα hpo).2.2] at hop
      have hs' : L = L₁ ++ ((p, (respsOf α p).length), o) :: L₂ := by
        rw [hs]; obtain ⟨y1, y2⟩ := y
        simp only [Option.some.injEq] at hyx hop
        rw [hyx, hop]
      refine ⟨L, ⟨hI.lin.append_ret L₁ L₂ o hs' (M.δ_write _ _ _ hav).2,
        by rw [hmem]; exact hI.mem, fun q => ?_⟩, by rw [hmem]⟩
      by_cases hq : q = p
      · subst hq; rw [hpend, hloc]; simp [Good]
      · exact hrest q hq
    | rDone r' =>
      rw [hl] at hgp hact
      simp only [alg, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      obtain ⟨-, L₁, L₂, o, hs, hr⟩ := hgp
      refine ⟨L, ⟨hI.lin.append_ret L₁ L₂ o hs hr, by rw [hmem]; exact hI.mem, fun q => ?_⟩,
        by rw [hmem]⟩
      by_cases hq : q = p
      · subst hq; rw [hpend, hloc]; simp [Good]
      · exact hrest q hq
    | idle => rw [hl] at hgp; exact absurd hgp h0
    | wRead v => rw [hl] at hact; simp [alg] at hact
    | wCas v tmp => rw [hl] at hact; simp [alg] at hact
    | rRead => rw [hl] at hact; simp [alg] at hact

/-- **Lemma 5** of [CS17] (with the linearization points of Definition 4): in every finite
execution `α` of Algorithm 1 there is a linearization `L` of `α`, obtained by appending each
operation at its linearization point (`Inv`, `Good`); moreover `b` holds the value of the max
register after `L`. -/
theorem lemma5 {α : List (Label P A)} {C : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)}
    (h : (alg M P).run α = some C) : ∃ L, Inv M α C L := by
  refine Impl.run_induction (Q := fun α C => ∃ L, Inv M α C L) ?_ ?_ h
  · exact ⟨[], isLinearization_nil, M.val_init.symm, fun _ => rfl⟩
  · rintro α C ℓ C' hα ⟨L, hI⟩ hs
    obtain ⟨L', hI', -⟩ := inv_step hα hI hs
    exact ⟨L', hI'⟩

/-- **Lemma 5** of [CS17]: Algorithm 1 is linearizable (atomic), over every linear order. -/
theorem linearizable : (alg M P).Linearizable :=
  (alg M P).linearizable_of_run fun _ _ h => (lemma5 h).elim fun L hL => ⟨L, hL.lin⟩

/-- **Lemma 5** of [CS17] over `ℕ`: Algorithm 1 implements CSLib's max register `maxRegObj`
linearizably from one CAS object over `ℕ`. -/
theorem natImpl_linearizable : (natImpl P).Linearizable := linearizable

/-- The value of `b` never decreases (Observation 2) and is always `≥ v₀`. -/
theorem mem_le_of_step {α : List (Label P A)}
    {C C' : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)} {ℓ : Label P A}
    (hα : (alg M P).run α = some C) (h : (alg M P).step C ℓ = some C') :
    C.mem () ≤ C'.mem () := by
  obtain ⟨L, hI⟩ := lemma5 hα
  obtain ⟨-, -, hle⟩ := inv_step hα hI h
  exact hle

theorem v₀_le_mem {α : List (Label P A)} {C : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)}
    (h : (alg M P).run α = some C) : v₀ ≤ C.mem () := by
  refine Impl.run_induction (Q := fun _ C => v₀ ≤ C.mem ()) le_rfl ?_ h
  intro α C ℓ C' hα hC hs
  exact hC.trans (mem_le_of_step hα hs)

end Lin

/-! ### Theorem 4: wait-freedom -/

section WaitFree

variable {M : MaxIface A V v₀} {P : Type} [DecidableEq P]

/-- A `ℕ`-valued sequence that never increases after `T` and strictly decreases whenever
`lbl t = x` (for `t ≥ T`) sees `x` only finitely often. -- CSLib candidate -/
lemma eventually_ne_of_descent {X : Type*} (lbl : ℕ → X) (x : X) (μ : ℕ → ℕ) (T : ℕ)
    (hle : ∀ t ≥ T, μ (t + 1) ≤ μ t) (hlt : ∀ t ≥ T, lbl t = x → μ (t + 1) < μ t) :
    ∃ N, ∀ m ≥ N, lbl m ≠ x := by
  by_contra hcon
  push Not at hcon
  have hanti : ∀ t ≥ T, ∀ m ≥ t, μ m ≤ μ t := by
    intro t ht m hm
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih => exact (hle m (by omega)).trans ih
  have key : ∀ k, ∃ t ≥ T, μ t + k ≤ μ T := by
    intro k
    induction k with
    | zero => exact ⟨T, le_rfl, by simp⟩
    | succ k ih =>
      obtain ⟨t, ht, hk⟩ := ih
      obtain ⟨m, hm, hx⟩ := hcon t
      have h1 := hlt m (by omega) hx
      have h2 := hanti t ht m hm
      exact ⟨m + 1, by omega, by omega⟩
  obtain ⟨t, -, ht⟩ := key (μ T + 1)
  omega

/-- A monotone sequence in `[v₀, ∞)` eventually either stays constant or exceeds `c`, provided
`[v₀, c)` has no infinite strictly increasing sequence. -/
lemma eventually_stable {c : V} (hwf : WellFoundedGT (Set.Ico v₀ c)) (f : ℕ → V)
    (hmono : Monotone f) (h0 : ∀ t, v₀ ≤ f t) (n : ℕ) :
    ∃ T ≥ n, ∀ t ≥ T, f t = f T ∨ c ≤ f t := by
  by_cases hc : ∃ T ≥ n, c ≤ f T
  · obtain ⟨T, hT, hcT⟩ := hc
    exact ⟨T, hT, fun t ht => Or.inr (hcT.trans (hmono ht))⟩
  · push Not at hc
    let g : ℕ → Set.Ico v₀ c := fun t => ⟨f (t + n), h0 _, hc _ (by omega)⟩
    obtain ⟨_, ⟨T, rfl⟩, hmin⟩ := hwf.has_min (Set.range g) ⟨g 0, 0, rfl⟩
    refine ⟨T + n, by omega, fun t ht => Or.inl ?_⟩
    have h1 := hmono ht
    by_contra hne
    have hlt : g T < g (t - n) := by
      show f (T + n) < f (t - n + n)
      rw [Nat.sub_add_cancel (by omega)]
      exact lt_of_le_of_ne h1 (Ne.symm hne)
    exact hmin _ ⟨t - n, rfl⟩ hlt

omit [LinearOrder V] in
lemma ite_eq_self' [DecidableEq V] (q : V) : (if q = v₀ then v₀ else q) = q := by
  split_ifs with h <;> simp [h]

/-- The potential of process `p` used for wait-freedom (once `b` has stabilized). -/
def pot (p : P) (C : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)) : ℕ :=
  match C.loc p with
  | .wRead v => if v ≤ C.mem () then 1 else 4
  | .wCas v tmp => if tmp = C.mem () ∨ v ≤ C.mem () then 2 else 5
  | .rRead => 1
  | _ => 0

lemma pot_step (c : V) {α : List (Label P A)}
    {C C' : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)} {ℓ : Label P A} {p : P}
    (hα : (alg M P).run α = some C) (hs : (alg M P).step C ℓ = some C')
    (hp : C.pend p ≠ none) (hp' : C'.pend p ≠ none)
    (hc : ∀ v tmp, C.loc p = .wCas v tmp → v = c)
    (hstab : ¬ c ≤ C.mem () → C'.mem () = C.mem () ∨ c ≤ C'.mem ()) :
    pot p C' ≤ pot p C ∧ (ℓ = .tau p → pot p C' < pot p C) := by
  have hle := mem_le_of_step hα hs
  rcases (alg M P).step_tau_or_other hs hp hp' with rfl | ⟨hq, hloc⟩
  · have h0 := hp
    obtain ⟨L, hI⟩ := lemma5 hα
    have hgp := hI.good p
    cases hl : C.loc p with
    | wRead v =>
      have hact : (alg M P).act p (C.loc p) =
          .access () (v₀, v₀) (fun tmp => if v ≤ tmp then .wDone else .wCas v tmp) := by
        rw [hl]; rfl
      rw [Impl.step_tau_eq_some h0 hact] at hs
      obtain rfl := Option.some.inj hs
      by_cases hvm : v ≤ C.mem () <;> simp [pot, hl, hvm, ite_eq_self']
    | wCas v tmp =>
      rw [hl] at hgp
      obtain ⟨o, -, -, -, htv⟩ := hgp
      have hact : (alg M P).act p (C.loc p) = .access () (tmp, v) (fun _ => .wRead v) := by
        rw [hl]; rfl
      rw [Impl.step_tau_eq_some h0 hact] at hs
      obtain rfl := Option.some.inj hs
      by_cases hmt : C.mem () = tmp
      · simp [pot, hl, hmt]
      · by_cases hvm : v ≤ C.mem ()
        · simp [pot, hl, hmt, hvm]
        · simp [pot, hl, hmt, hvm, Ne.symm hmt]
    | rRead =>
      have hact : (alg M P).act p (C.loc p) = .access () (v₀, v₀) (fun tmp => .rDone tmp) := by
        rw [hl]; rfl
      rw [Impl.step_tau_eq_some h0 hact] at hs
      obtain rfl := Option.some.inj hs
      simp [pot, hl]
    | idle =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      rw [hl] at hact; simp [alg] at hact
    | wDone =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      rw [hl] at hact; simp [alg] at hact
    | rDone r =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      rw [hl] at hact; simp [alg] at hact
  · refine ⟨?_, fun h => absurd (by rw [h]; rfl) hq⟩
    unfold pot
    rw [hloc]
    cases hl : C.loc p with
    | wRead v =>
      dsimp only
      by_cases h1 : v ≤ C.mem ()
      · simp [h1, h1.trans hle]
      · split_ifs <;> omega
    | wCas v tmp =>
      obtain rfl := hc v tmp hl
      dsimp only
      by_cases h1 : tmp = C.mem () ∨ v ≤ C.mem ()
      · rw [ite_eq_left h1]
        rcases h1 with h1 | h1
        · by_cases h2 : v ≤ C.mem ()
          · simp [h2.trans hle]
          · rcases hstab h2 with h3 | h3
            · simp [h3, h1]
            · simp [h3]
        · simp [h1.trans hle]
      · split_ifs <;> omega
    | _ => simp

/-- Wait-freedom of Algorithm 1 over any linear order in which every interval `[v₀, c)` has no
infinite strictly increasing sequence. This is what the paper's proof of Theorem 4 uses: a
`write-max(v)` whose CAS fails re-reads a strictly larger value, and the values read stay in
`[v₀, v)`. -/
theorem waitFree_of_wellFoundedGT (hwf : ∀ c : V, WellFoundedGT (Set.Ico v₀ c)) :
    (alg M P).WaitFree := by
  intro e p n hpend
  have hrun := e.run_pre
  have hmono : Monotone (fun t => (e.cfg t).mem ()) :=
    monotone_nat_of_le_succ fun t => mem_le_of_step (hrun t) (e.step_eq t)
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (hpend n le_rfl)
  have hconst : ∀ t ≥ n, (e.cfg t).pend p = some o := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ho
    | succ t ht ih =>
      obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 (hpend (t + 1) (by omega))
      rcases Impl.step_pend_some (e.step_eq t) ho' with h | h
      · rw [ih] at h; rw [ho', h]
      · have hs := e.step_eq t
        rw [h] at hs
        have := (Impl.step_inv hs).1
        rw [ih] at this; cases this
  set c := (M.arg o).getD v₀
  have hc : ∀ t ≥ n, ∀ v tmp, (e.cfg t).loc p = .wCas v tmp → v = c := by
    intro t ht v tmp hl
    obtain ⟨L, hI⟩ := lemma5 (hrun t)
    have hg := hI.good p
    rw [hl, hconst t ht] at hg
    obtain ⟨o', h1, h2, -⟩ := hg
    cases h1
    simp [c, h2]
  obtain ⟨T, hTn, hT⟩ := eventually_stable (hwf c) _ hmono (fun t => v₀_le_mem (hrun t)) n
  have hps : ∀ t ≥ T, pot p (e.cfg (t + 1)) ≤ pot p (e.cfg t) ∧
      (e.lbl t = .tau p → pot p (e.cfg (t + 1)) < pot p (e.cfg t)) := by
    intro t ht
    refine pot_step c (hrun t) (e.step_eq t) (hpend t (by omega)) (hpend (t + 1) (by omega))
      (hc t (by omega)) fun hnc => ?_
    rcases hT t ht with h1 | h1
    · rcases hT (t + 1) (by omega) with h2 | h2
      · exact Or.inl (h2.trans h1.symm)
      · exact Or.inr h2
    · exact absurd h1 hnc
  exact eventually_ne_of_descent e.lbl (.tau p) (fun t => pot p (e.cfg t)) T
    (fun t ht => (hps t ht).1) (fun t ht => (hps t ht).2)

/-- **Theorem 4** of [CS17] for locally finite value orders (finitely many values between any
two values, the hypothesis implicit in the paper's proof): Algorithm 1 is wait-free. -/
theorem waitFree_of_locallyFinite [LocallyFiniteOrder V] : (alg M P).WaitFree :=
  waitFree_of_wellFoundedGT fun c => by
    have : Finite (Set.Ico v₀ c) := (Set.finite_Ico v₀ c).to_subtype
    infer_instance

/-- **Theorem 4** of [CS17] over `ℕ`: Algorithm 1 emulates a wait-free atomic max register
(`maxRegObj`) from one CAS object. -/
theorem natImpl_waitFree : (natImpl P).WaitFree := waitFree_of_locallyFinite

/-- **Theorem 4** of [CS17] over `ℕ`, both parts: linearizable and wait-free. -/
theorem theorem4_nat : (natImpl P).Linearizable ∧ (natImpl P).WaitFree :=
  ⟨natImpl_linearizable, natImpl_waitFree⟩

/-! ### Lock-freedom (over every linear order) -/

/-- `1` if `p` runs a `write-max(v)` that may still perform a successful CAS (`v > b`). -/
def armed (p : P) (C : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)) : ℕ :=
  match C.loc p with
  | .wRead v => if v ≤ C.mem () then 0 else 1
  | .wCas v _ => if v ≤ C.mem () then 0 else 1
  | _ => 0

lemma armed_le_of_mem_le {p : P} {C C' : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)}
    (hloc : C'.loc p = C.loc p) (hle : C.mem () ≤ C'.mem ()) : armed p C' ≤ armed p C := by
  unfold armed
  rw [hloc]
  cases C.loc p with
  | wRead v | wCas v _ =>
    dsimp only
    by_cases h : v ≤ C.mem ()
    · simp [h, h.trans hle]
    · split_ifs <;> omega
  | _ => exact le_rfl

lemma pot_le_five (p : P) (C : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)) :
    pot p C ≤ 5 := by
  unfold pot; split <;> (try split_ifs) <;> omega

/-- A step of `p` either leaves `b` unchanged and decreases `p`'s potential without arming it, or
disarms `p` (its successful CAS). -/
lemma tau_progress {α : List (Label P A)} {C C' : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)}
    {p : P} (hα : (alg M P).run α = some C) (hs : (alg M P).step C (.tau p) = some C') :
    (C'.mem () = C.mem () ∧ armed p C' ≤ armed p C ∧ pot p C' < pot p C) ∨
      armed p C' < armed p C := by
  have h0 := (Impl.step_tau hs).1
  obtain ⟨L, hI⟩ := lemma5 hα
  have hgp := hI.good p
  cases hl : C.loc p with
  | wRead v =>
    have hact : (alg M P).act p (C.loc p) =
        .access () (v₀, v₀) (fun tmp => if v ≤ tmp then .wDone else .wCas v tmp) := by
      rw [hl]; rfl
    rw [Impl.step_tau_eq_some h0 hact] at hs
    obtain rfl := Option.some.inj hs
    left
    by_cases hvm : v ≤ C.mem () <;> simp [pot, armed, hl, hvm, ite_eq_self']
  | wCas v tmp =>
    rw [hl] at hgp
    obtain ⟨o, -, -, -, htv⟩ := hgp
    have hact : (alg M P).act p (C.loc p) = .access () (tmp, v) (fun _ => .wRead v) := by
      rw [hl]; rfl
    rw [Impl.step_tau_eq_some h0 hact] at hs
    obtain rfl := Option.some.inj hs
    by_cases hmt : C.mem () = tmp
    · right
      have : ¬ v ≤ tmp := not_le.2 htv
      simp [armed, hl, hmt, this]
    · left
      by_cases hvm : v ≤ C.mem ()
      · simp [pot, armed, hl, hmt, hvm]
      · simp [pot, armed, hl, hmt, hvm, Ne.symm hmt]
  | rRead =>
    have hact : (alg M P).act p (C.loc p) = .access () (v₀, v₀) (fun tmp => .rDone tmp) := by
      rw [hl]; rfl
    rw [Impl.step_tau_eq_some h0 hact] at hs
    obtain rfl := Option.some.inj hs
    left
    simp [pot, armed, hl, ite_eq_self']
  | idle =>
    obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
    rw [hl] at hact; simp [alg] at hact
  | wDone =>
    obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
    rw [hl] at hact; simp [alg] at hact
  | rDone r =>
    obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
    rw [hl] at hact; simp [alg] at hact

/-- The global potential for lock-freedom. -/
def gpot [Fintype P] (C : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)) : ℕ :=
  ∑ q, ((5 * Fintype.card P + 1) * armed q C + pot q C)

lemma gpot_lt [Fintype P] {α : List (Label P A)}
    {C C' : Config A (fun _ : Unit => casPrev V v₀) P (Loc V)} {p : P}
    (hα : (alg M P).run α = some C) (hs : (alg M P).step C (.tau p) = some C') :
    gpot C' < gpot C := by
  have hle := mem_le_of_step hα hs
  have hother : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq =>
    (Impl.step_other hs (by simpa [Label.proc] using Ne.symm hq)).1
  rcases tau_progress hα hs with ⟨hmem, ha, hp⟩ | ha
  · refine Finset.sum_lt_sum (fun q _ => ?_) ⟨p, Finset.mem_univ _, ?_⟩
    · by_cases hq : q = p
      · subst hq; gcongr
      · unfold armed pot; rw [hother q hq, hmem]
    · exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left _ ha) hp
  · have h1 : ∑ q, armed q C' < ∑ q, armed q C := by
      refine Finset.sum_lt_sum (fun q _ => ?_) ⟨p, Finset.mem_univ _, ha⟩
      by_cases hq : q = p
      · subst hq; exact ha.le
      · exact armed_le_of_mem_le (hother q hq) hle
    have h2 : ∑ q, pot q C' ≤ 5 * Fintype.card P := by
      calc ∑ q, pot q C' ≤ ∑ _q : P, 5 := Finset.sum_le_sum fun q _ => pot_le_five q C'
        _ = 5 * Fintype.card P := by simp [mul_comm]
    unfold gpot
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h3 : (5 * Fintype.card P + 1) * ∑ q, armed q C' + (5 * Fintype.card P + 1) ≤
        (5 * Fintype.card P + 1) * ∑ q, armed q C := by
      have := Nat.mul_le_mul_left (5 * Fintype.card P + 1) (Nat.succ_le_of_lt h1)
      rw [Nat.mul_succ] at this; exact this
    omega

/-- Algorithm 1 is **lock-free** over every linear order of values (finitely many processes):
an infinite execution has infinitely many responses. Hence over dense orders such as `ℚ` it
emulates a lock-free, but not wait-free, atomic max register. -/
theorem lockFree [Fintype P] : (alg M P).LockFree := by
  intro e _ N
  by_contra hcon
  push Not at hcon
  have hrun := e.run_pre
  have hpers : ∀ p t, N ≤ t → (e.cfg t).pend p ≠ none → ∀ t' ≥ t, (e.cfg t').pend p ≠ none := by
    intro p t ht hp t' ht'
    induction t', ht' using Nat.le_induction with
    | base => exact hp
    | succ t' ht' ih =>
      have hs := e.step_eq t'
      cases hl : e.lbl t' with
      | inv q o =>
        rw [hl] at hs
        obtain ⟨-, -, hpend, -⟩ := Impl.step_inv hs
        rw [hpend]
        by_cases hq : p = q
        · subst hq; simp
        · rw [Function.update_of_ne hq]; exact ih
      | tau q =>
        rw [hl] at hs
        rw [(Impl.step_tau hs).2.1]; exact ih
      | ret q r => exact absurd hl (hcon t' (by omega) q r)
  have hT : ∀ p, ∃ T, ∀ m ≥ T, ∀ o, e.lbl m ≠ .inv p o := by
    intro p
    by_cases h : ∃ t ≥ N, ∃ o, e.lbl t = .inv p o
    · obtain ⟨t, ht, o, hto⟩ := h
      have hs := e.step_eq t
      rw [hto] at hs
      have hp1 : (e.cfg (t + 1)).pend p ≠ none := by
        rw [(Impl.step_inv hs).2.2.1]; simp
      refine ⟨t + 1, fun m hm o' hmo => ?_⟩
      have hs' := e.step_eq m
      rw [hmo] at hs'
      exact hpers p (t + 1) (by omega) hp1 m hm (Impl.step_inv hs').1
    · push Not at h
      exact ⟨N, fun m hm o => h m hm o⟩
  choose T hT using hT
  set N₁ := max N (Finset.univ.sup T)
  have hdec : ∀ m ≥ N₁, gpot (e.cfg (m + 1)) < gpot (e.cfg m) := by
    intro m hm
    have hs := e.step_eq m
    cases hl : e.lbl m with
    | inv p o =>
      exact absurd hl (hT p m ((Finset.le_sup (Finset.mem_univ p)).trans (le_of_max_le_right hm)) o)
    | ret p r => exact absurd hl (hcon m (le_of_max_le_left hm) p r)
    | tau p => rw [hl] at hs; exact gpot_lt (hrun m) hs
  have key : ∀ k, gpot (e.cfg (N₁ + k)) + k ≤ gpot (e.cfg N₁) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hdec (N₁ + k) (by omega)
      rw [show N₁ + (k + 1) = N₁ + k + 1 by omega]; omega
  have := key (gpot (e.cfg N₁) + 1)
  omega

/-- Algorithm 1 over `ℚ` is lock-free (but not wait-free, `ratImpl_not_waitFree`). -/
theorem ratImpl_lockFree [Fintype P] : (ratImpl P).LockFree := lockFree

end WaitFree

/-! ### Theorem 4 fails over dense orders -/

section Counterexample

variable (M : MaxIface A V v₀) {P : Type} [DecidableEq P]

/-- The configuration after round `k` of the bad schedule: `p` runs `write-max(c)` and is about
to execute line 6 with `tmp = a k`, every other process is idle, and `b = a k`. -/
def badCfg (p : P) (c : V) (a : ℕ → V) (k : ℕ) : Config A (fun _ : Unit => casPrev V v₀) P (Loc V) where
  loc := Function.update (fun _ => .idle) p (.wCas c (a k))
  pend := Function.update (fun _ => none) p (some (M.wr c))
  mem := fun _ => a k

/-- The first two steps: `p` invokes `write-max(c)` and reads `b = v₀`. -/
def badPre (p : P) (c : V) : List (Label P A) := [.inv p (M.wr c), .tau p]

/-- Round `k`: process `q` runs a complete `write-max(a (k+1))` (read `a k`, successful
`CAS(a k, a (k+1))`, read `a (k+1)`, return); then `p`'s `CAS(a k, c)` fails and `p` reads
`a (k+1) < c`. -/
def badRound (p q : P) (a : ℕ → V) (k : ℕ) : List (Label P A) :=
  [.inv q (M.wr (a (k + 1))), .tau q, .tau q, .tau q, .ret q M.ack, .tau p, .tau p]

variable {M}

lemma run_badPre {p : P} {c : V} {a : ℕ → V} (ha0 : a 0 = v₀) (hc : v₀ < c) :
    (alg M P).run (badPre M p c) = some (badCfg M p c a 0) := by
  have hcv : ¬ c ≤ v₀ := not_le.2 hc
  simp [badPre, Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, alg, badCfg, M.arg_wr, hcv, ha0]

lemma runFrom_badRound {p q : P} (hpq : p ≠ q) {c : V} {a : ℕ → V} (ha : StrictMono a)
    (hc : ∀ k, a k < c) (k : ℕ) :
    (alg M P).runFrom (badCfg M p c a k) (badRound M p q a k) = some (badCfg M p c a (k + 1)) := by
  have h1 : ¬ a (k + 1) ≤ a k := not_le.2 (ha (Nat.lt_succ_self k))
  have h2 : a (k + 1) ≠ a k := ne_of_gt (ha (Nat.lt_succ_self k))
  have h3 : ¬ c ≤ a (k + 1) := not_le.2 (hc _)
  simp [badRound, Impl.runFrom, Impl.step, alg, badCfg, M.arg_wr, hpq, Ne.symm hpq, h1, h2, h3,
    ite_eq_self']
  refine ⟨?_, ?_⟩ <;> funext r
  · by_cases hr : r = p
    · subst hr; simp
    · by_cases hrq : r = q
      · subst hrq; simp [hr]
      · simp [hr, hrq]
  · simp

variable (M) in
/-- The first `k` rounds of the bad schedule. -/
def badExec (p q : P) (c : V) (a : ℕ → V) (k : ℕ) : List (Label P A) :=
  badPre M p c ++ (List.range k).flatMap (badRound M p q a)

lemma badExec_succ (p q : P) (c : V) (a : ℕ → V) (k : ℕ) :
    badExec M p q c a (k + 1) = badExec M p q c a k ++ badRound M p q a k := by
  simp [badExec, List.range_succ, List.flatMap_append]

lemma length_badExec (p q : P) (c : V) (a : ℕ → V) (k : ℕ) :
    (badExec M p q c a k).length = 2 + 7 * k := by
  induction k with
  | zero => simp [badExec, badPre]
  | succ k ih => rw [badExec_succ, List.length_append, ih]; simp [badRound]; ring

lemma run_badExec {p q : P} (hpq : p ≠ q) {c : V} {a : ℕ → V} (ha : StrictMono a)
    (ha0 : a 0 = v₀) (hc : ∀ k, a k < c) (k : ℕ) :
    (alg M P).run (badExec M p q c a k) = some (badCfg M p c a k) := by
  induction k with
  | zero => simpa [badExec] using run_badPre (M := M) (p := p) ha0 (ha0 ▸ hc 0)
  | succ k ih => rw [badExec_succ, Impl.run_append_of_eq _ ih]; exact runFrom_badRound hpq ha hc k

/-- **Theorem 4 of [CS17] fails without a finiteness assumption on the values.** If some
interval `[v₀, c)` contains an infinite strictly increasing sequence `v₀ = a 0 < a 1 < ⋯ < c`,
then Algorithm 1 is **not** wait-free (with at least two processes): process `p` runs
`write-max(c)` forever, because between each of its reads (line 3) and CASes (line 6),
process `q` completes `write-max(a (k+1))`, so every `CAS(a k, c)` of `p` fails and `p` then
reads `a (k+1) < c`. -/
theorem not_waitFree_of_strictMono {p q : P} (hpq : p ≠ q) {a : ℕ → V} (ha : StrictMono a)
    (ha0 : a 0 = v₀) {c : V} (hc : ∀ k, a k < c) : ¬ (alg M P).WaitFree := by
  obtain ⟨e, hlbl, hcfg⟩ := (alg M P).exists_infExec_of_chain (badExec M p q c a)
    (fun k => by rw [badExec_succ]; exact List.prefix_append _ _)
    (fun k => by rw [length_badExec]; omega)
    (fun k => ⟨_, run_badExec hpq ha ha0 hc k⟩)
  have hpend : ∀ m ≥ 1, (e.cfg m).pend p ≠ none := by
    intro m hm
    have hr := hcfg m m (by rw [length_badExec]; omega)
    have hresp : respsOf ((badExec M p q c a m).take m) p = [] := by
      simp only [respsOf, List.filterMap_eq_nil_iff]
      intro ℓ hℓ
      have := List.mem_of_mem_take hℓ
      simp only [badExec, badPre, badRound, List.mem_append, List.mem_cons, List.mem_flatMap,
        List.mem_range, List.not_mem_nil, or_false] at this
      rcases this with (rfl | rfl) | ⟨j, -, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ <;>
        simp [hpq.symm]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hops : opsOf ((badExec M p q c a (m' + 1)).take (m' + 1)) p ≠ [] := by
      simp [badExec, badPre, List.take_succ_cons, opsOf_cons]
    rcases (alg M P).run_counts hr p with ⟨-, h⟩ | ⟨h, -⟩
    · rw [hresp, List.length_nil, List.length_eq_zero_iff] at h; exact absurd h hops
    · exact h
  intro hwf
  obtain ⟨N, hN⟩ := hwf e p 1 hpend
  apply hN (2 + 7 * N + 6) (by omega)
  rw [hlbl (N + 1) _ (by rw [length_badExec]; omega)]
  simp only [badExec_succ]
  rw [List.getElem_append_right (by rw [length_badExec]; omega)]
  simp [badRound, length_badExec]

/-- **Characterization of wait-freedom of Algorithm 1** (with at least two processes): it is
wait-free iff no interval `[v₀, c)` of the value order contains an infinite strictly increasing
sequence. Theorem 4 of [CS17] ("Algorithm 1 emulates a wait-free atomic max-register" over "some
domain of ordered values") therefore holds only under this extra hypothesis. -/
theorem waitFree_iff {p q : P} (hpq : p ≠ q) :
    (alg M P).WaitFree ↔ ∀ c : V, WellFoundedGT (Set.Ico v₀ c) := by
  refine ⟨fun hwf c => ?_, waitFree_of_wellFoundedGT⟩
  by_contra hnwf
  have hnwf' : ¬ WellFounded ((· > ·) : Set.Ico v₀ c → Set.Ico v₀ c → Prop) :=
    fun h => hnwf h
  rw [RelEmbedding.wellFounded_iff_isEmpty, not_isEmpty_iff] at hnwf'
  obtain ⟨f⟩ := hnwf'
  have hf : ∀ n, (f n : V) < f (n + 1) := fun n => f.map_rel_iff.2 (Nat.lt_succ_self n)
  refine not_waitFree_of_strictMono hpq (a := fun k => if k = 0 then v₀ else (f k : V))
    ?_ (by simp) (c := c) ?_ hwf
  · refine strictMono_nat_of_lt_succ fun n => ?_
    rcases n with _ | n
    · simpa using lt_of_le_of_lt (f 0).2.1 (hf 0)
    · simpa using hf (n + 1)
  · intro k
    split_ifs
    · exact lt_of_le_of_lt (f 0).2.1 (f 0).2.2
    · exact (f k).2.2

/-- **Theorem 4 of [CS17] is false over `ℚ`**: Algorithm 1 over the rationals (initial value
`0`) is not wait-free as soon as there are two processes. In the bad execution, `p` runs
`write-max(1)` forever while `q` completes `write-max(1 - 1/(k+2))`, `k = 0, 1, …`, between
each read and CAS of `p`. -/
theorem ratImpl_not_waitFree {p q : P} (hpq : p ≠ q) : ¬ (ratImpl P).WaitFree := by
  refine not_waitFree_of_strictMono hpq (a := fun k => 1 - 1 / ((k : ℚ) + 1)) ?_ (by simp)
    (c := 1) fun k => ?_
  · refine strictMono_nat_of_lt_succ fun n => ?_
    have h : 1 / ((n : ℚ) + 1 + 1) < 1 / ((n : ℚ) + 1) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    push_cast
    linarith
  · have : (0 : ℚ) < 1 / ((k : ℚ) + 1) := by positivity
    linarith

/-- The two-process instance of `ratImpl_not_waitFree`. -/
example : ¬ (ratImpl (Fin 2)).WaitFree := ratImpl_not_waitFree (p := 0) (q := 1) (by decide)

end Counterexample

end Podc.RegisterEmulationSpace.MaxRegisterCAS
