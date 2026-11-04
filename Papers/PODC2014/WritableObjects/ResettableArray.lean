import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Model
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Group.Fin.Basic

/-!
# A sequentially resettable `(k,b)`-array (Lemma 4.2, Figure 4.15)

Aghazadeh, Golab, Woelfel, *Making Objects Writable*, PODC 2014; numbering of Chapter 4 of
Aghazadeh's PhD thesis (Section 4.5).

The type `(k,b)`-Array (`kbArray k V v₀`) stores an array `S` of `k` entries with values in `V`
(the `b`-bit values), all initially `⊥ = v₀`; `Read(i)` returns `S[i]`, `Write(i,x)` sets
`S[i] := x`, `Reset()` sets every entry back to `v₀`.

Implementation of Figure 4.15 (`resettableArray`), for any set of processes: a register
`Ver : Fin k` (initially `0`) and registers `A[i] : V × Option (Fin k)` (initially `(⊥,⊥)`, the
second `⊥` being `none`):

* `SReset()`: `v := (Ver.Read() + 1) mod k; Ver.Write(v); A[v].Write(⊥,⊥)`
* `Read(i)`: `(x,v) := A[i].Read(); ver := Ver.Read(); if v ≠ ver then x := ⊥; return x`
* `Write(i,x)`: `ver := Ver.Read(); A[i].Write(x, ver)`

Lemma 4.2: every execution in which no `Reset` instance overlaps any other instance
(`ResetsIsolated`) is linearizable (`lemma_4_2`). The implementation uses `k + 1` base
registers (`card_baseObjects`) and every operation performs at most 3 base-object accesses
(`stepBound_invoke`, `stepBound_access`).

## Proof

Linearization points: a `Read` at its read of `A[i]` (line 59), a `Write` at its write of `A[i]`
(line 64), a `Reset` at its write of `A[v]` (line 58). The invariant (`Inv`) says that, except
between lines 57 and 58 of a reset, the abstract state is decoded from the memory
(`S[i] = x` if `A[i] = (x, some Ver)` and `⊥` otherwise) and the *wrap-around invariant*
`WrapOK` holds: if `A[i]` carries version `v`, then `Ver` has advanced from `v` fewer times
than it takes to reach index `i` (`(Ver - v) < (i - v)` in `Fin k`) unless `i = v`. This is the
invariant form of the paper's wrap-around argument in Part (b2).
-/

namespace Podc.WritableObjects

open Cslib.SharedMemory

/-! ## The type `(k,b)`-Array -/

/-- Operations of a `(k,b)`-array: `Read(i)`, `Write(i,x)`, `Reset()`. -/
inductive ArrOp (k : ℕ) (V : Type) where
  | read (i : Fin k)
  | write (i : Fin k) (x : V)
  | reset

/-- The sequential specification of the type `(k,b)`-Array with initial value `v₀ = ⊥` of every
entry. `Read(i)` returns `some S[i]`; `Write` and `Reset` return the acknowledgement `none`. -/
abbrev kbArray (k : ℕ) (V : Type) (v₀ : V) : ObjSpec where
  State := Fin k → V
  Op := ArrOp k V
  Resp := Option V
  init := fun _ => v₀
  δ S
    | .read i => (S, some (S i))
    | .write i x => (Function.update S i x, none)
    | .reset => (fun _ => v₀, none)

/-! ## The implementation of Figure 4.15 -/

/-- The base objects: `none` is the register `Ver` (initially `0`), `some i` is the register
`A[i]` storing a pair (value, version), initially `(⊥, ⊥)`. -/
abbrev raBase (k : ℕ) [NeZero k] (V : Type) (v₀ : V) : Option (Fin k) → ObjSpec
  | none => register (Fin k) 0
  | some _ => register (V × Option (Fin k)) (v₀, none)

/-- Local states (program counters with local variables). -/
inductive RLoc (k : ℕ) (V : Type) where
  /-- no pending operation -/
  | idle
  /-- `Read(i)`, before line 59 -/
  | rd0 (i : Fin k)
  /-- `Read`, read the pair `a` from `A[i]`, before line 60 -/
  | rd1 (a : V × Option (Fin k))
  /-- about to return `r` -/
  | done (r : Option V)
  /-- `Write(i,x)`, before line 63 -/
  | wr0 (i : Fin k) (x : V)
  /-- `Write(i,x)`, read `c` from `Ver`, before line 64 -/
  | wr1 (i : Fin k) (x : V) (c : Fin k)
  /-- `SReset()`, before line 56 -/
  | rs0
  /-- `SReset()` with `v = Ver + 1`, before line 57 -/
  | rs1 (v : Fin k)
  /-- `SReset()`, wrote `v` to `Ver`, before line 58 -/
  | rs2 (v : Fin k)

/-- The value returned by `Read` after reading the pair `a` from `A[i]` and `c` from `Ver`
(lines 61–62). -/
def decode {k : ℕ} {V : Type} (v₀ : V) (a : V × Option (Fin k)) (c : Fin k) : V :=
  if a.2 = some c then a.1 else v₀

/-- The implementation of Figure 4.15 for processes `P`. -/
def resettableArray (k : ℕ) [NeZero k] (V : Type) (v₀ : V) (P : Type) :
    Impl (kbArray k V v₀) (raBase k V v₀) P (RLoc k V) where
  memInit
    | none => (0 : Fin k)
    | some _ => ((v₀, none) : V × Option (Fin k))
  locInit _ := .idle
  invoke _ _ o := match o with
    | .read i => .rd0 i
    | .write i x => .wr0 i x
    | .reset => .rs0
  act _ l := match l with
    | .idle => .ret none .idle
    | .rd0 i => .access (some i) RWOp.read (fun a => .rd1 a)
    | .rd1 a => .access none RWOp.read (fun c => .done (some (decode v₀ a c)))
    | .done r => .ret r .idle
    | .wr0 i x => .access none RWOp.read (fun c => .wr1 i x c)
    | .wr1 i x c => .access (some i) (RWOp.write (x, some c)) (fun _ => .done none)
    | .rs0 => .access none RWOp.read (fun c => .rs1 (c + 1))
    | .rs1 v => .access none (RWOp.write v) (fun _ => .rs2 v)
    | .rs2 v => .access (some v) (RWOp.write (v₀, none)) (fun _ => .done none)

/-! ## Space and step complexity -/

/-- The implementation uses `k + 1` registers (`Ver` and `A[0..k-1]`). -/
theorem card_baseObjects (k : ℕ) : Fintype.card (Option (Fin k)) = k + 1 := by simp

/-- Upper bound on the number of base-object accesses a process still performs before its
pending operation returns. -/
def stepBound {k : ℕ} {V : Type} : RLoc k V → ℕ
  | .idle => 0
  | .rd0 _ => 2
  | .rd1 _ => 1
  | .done _ => 0
  | .wr0 _ _ => 2
  | .wr1 _ _ _ => 1
  | .rs0 => 3
  | .rs1 _ => 2
  | .rs2 _ => 1

/-- Constant step complexity (Lemma 4.2), part 1: right after an invocation, at most 3
accesses remain. -/
theorem stepBound_invoke (k : ℕ) [NeZero k] (V : Type) (v₀ : V) (P : Type) (p : P)
    (l : RLoc k V) (o : ArrOp k V) :
    stepBound ((resettableArray k V v₀ P).invoke p l o) ≤ 3 := by
  cases o <;> simp [resettableArray, stepBound]

/-- Constant step complexity (Lemma 4.2), part 2: every base-object access decreases the bound,
and a process whose bound is `0` returns next (`act` is a `ret`). Hence every operation performs
at most 3 accesses of base objects. -/
theorem stepBound_access (k : ℕ) [NeZero k] (V : Type) (v₀ : V) (P : Type) (p : P)
    (l : RLoc k V) :
    (∀ i o c, (resettableArray k V v₀ P).act p l = .access i o c →
      ∀ r, stepBound (c r) < stepBound l) ∧
    (stepBound l = 0 → ∃ r l', (resettableArray k V v₀ P).act p l = .ret r l') := by
  constructor
  · intro i o c h r
    cases l <;> simp only [resettableArray, Action.access.injEq, reduceCtorEq] at h <;>
      obtain ⟨rfl, -, h⟩ := h <;> cases eq_of_heq h <;> simp [stepBound]
  · intro h
    cases l <;> simp [stepBound, resettableArray] at h ⊢

/-! ## Isolated resets -/

/-- No `Reset` instance overlaps any other operation instance: for every reset instance `x` and
every other invoked instance `y`, one of them precedes the other in real time. -/
def ResetsIsolated {k : ℕ} {V : Type} {v₀ : V} {P : Type} [DecidableEq P]
    (α : List (Label P (kbArray k V v₀))) : Prop :=
  ∀ x y : OpId P, x ≠ y → opOf α x = some ArrOp.reset → Invoked α y →
    Precedes α x y ∨ Precedes α y x

/-! ## The invariant -/

namespace RArray

variable {k : ℕ} [NeZero k] {V : Type} {v₀ : V} {P : Type} [DecidableEq P]

/-- The wrap-around invariant for entry `i` when `Ver = c`: if `A[i]` carries version `v`, then
either `i = v` or the resets since `Ver` was `v` (there are `c - v` of them, mod `k`) have not yet
reached index `i` (they reset `A[v+1], …, A[c]`). -/
def WrapOK (c i : Fin k) (a : V × Option (Fin k)) : Prop :=
  ∀ v, a.2 = some v → i = v ∨ (c - v).val < (i - v).val

lemma wrapOK_fresh (c i : Fin k) (x : V) : WrapOK c i (x, some c) := by
  intro v hv
  simp only [Option.some.injEq] at hv; subst hv
  by_cases h : i = c
  · exact Or.inl h
  · right
    simp only [sub_self, Fin.val_zero]
    rw [Nat.pos_iff_ne_zero, Fin.val_ne_zero_iff]; exact sub_ne_zero.mpr h

omit [NeZero k] in
lemma wrapOK_none (c i : Fin k) (x : V) : WrapOK c i (x, (none : Option (Fin k))) := by
  intro v hv; cases hv

/-- One reset (`Ver := c + 1`) keeps the wrap-around invariant of every entry other than
`c + 1`, and such an entry does not carry the new version (so it reads as `⊥`). This is the
paper's wrap-around argument of Part (b2). -/
lemma WrapOK.shift {c i : Fin k} {a : V × Option (Fin k)} (h : WrapOK c i a) (hi : i ≠ c + 1) :
    WrapOK (c + 1) i a ∧ a.2 ≠ some (c + 1) := by
  by_cases hiv : ∃ v, a.2 = some v ∧ i ≠ v
  · obtain ⟨v, hv, hne⟩ := hiv
    have hlt := (h v hv).resolve_left hne
    have hik := (i - v).isLt
    have hd : (c + 1 - v).val = (c - v).val + 1 := by
      rw [show c + 1 - v = (c - v) + 1 from add_sub_right_comm c 1 v, Fin.val_add, Fin.val_one',
        Nat.one_mod_eq_one.mpr (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hne2 : (c + 1 - v).val ≠ (i - v).val := by
      intro he
      have : c + 1 - v = i - v := Fin.ext he
      exact hi (sub_left_inj.mp this).symm
    refine ⟨fun v' hv' => ?_, ?_⟩
    · rw [hv] at hv'; cases hv'
      right; omega
    · rw [hv]; intro he
      simp only [Option.some.injEq] at he; subst he
      simp at hd
  · push Not at hiv
    exact ⟨fun v hv => Or.inl (hiv v hv), fun he => hi (hiv _ he)⟩

/-- The memory `(Ver = c, A)` represents the abstract state `S`, and the wrap-around invariant
holds. -/
def Good (v₀ : V) (c : Fin k) (A : Fin k → V × Option (Fin k)) (S : Fin k → V) : Prop :=
  ∀ i, WrapOK c i (A i) ∧ S i = decode v₀ (A i) c

/-- Configurations of the implementation. -/
abbrev RCfg (k : ℕ) [NeZero k] (V : Type) (v₀ : V) (P : Type) :=
  Config (kbArray k V v₀) (raBase k V v₀) P (RLoc k V)

/-- The value of `Ver`. -/
abbrev verOf (C : RCfg k V v₀ P) : Fin k := C.mem none

/-- The contents of the array `A`. -/
abbrev arrOf (C : RCfg k V v₀ P) : Fin k → V × Option (Fin k) := fun i => C.mem (some i)

/-- The per-process part of the invariant: what the local state `l` of `p` (with pending
operation `pd`) says about the linearization `L` and the memory `(Ver = c, A)`. -/
def LocOK (v₀ : V) (β : List (Label P (kbArray k V v₀)))
    (L : List (OpId P × (kbArray k V v₀).Op)) (c : Fin k) (A : Fin k → V × Option (Fin k))
    (p : P) : RLoc k V → Option (ArrOp k V) → Prop
  | .idle, pd => pd = none
  | .rd0 i, pd => pd = some (.read i) ∧ curOp β p ∉ L.map Prod.fst
  | .rd1 a, pd => (∃ i, pd = some (.read i)) ∧
      (kbArray k V v₀).respIn (kbArray k V v₀).init L (curOp β p) = some (some (decode v₀ a c))
  | .done r, pd => pd ≠ none ∧
      (kbArray k V v₀).respIn (kbArray k V v₀).init L (curOp β p) = some r
  | .wr0 i x, pd => pd = some (.write i x) ∧ curOp β p ∉ L.map Prod.fst
  | .wr1 i x c', pd => pd = some (.write i x) ∧ curOp β p ∉ L.map Prod.fst ∧ c' = c
  | .rs0, pd => pd = some .reset ∧ curOp β p ∉ L.map Prod.fst
  | .rs1 v, pd => pd = some .reset ∧ curOp β p ∉ L.map Prod.fst ∧ v = c + 1
  | .rs2 v, pd => pd = some .reset ∧ curOp β p ∉ L.map Prod.fst ∧ c = v ∧
      ∀ i, i ≠ v → WrapOK v i (A i) ∧ (A i).2 ≠ some v

/-- The invariant of the executions `β` (with final configuration `C`) satisfying
`ResetsIsolated`: `L` is a linearization of `β`, every process satisfies `LocOK`, and, unless a
reset is between lines 57 and 58, the memory represents the abstract state `linState L`. -/
structure Inv (β : List (Label P (kbArray k V v₀))) (C : RCfg k V v₀ P)
    (L : List (OpId P × (kbArray k V v₀).Op)) : Prop where
  lin : IsLinearization β L
  loc : ∀ p, LocOK v₀ β L (verOf C) (arrOf C) p (C.loc p) (C.pend p)
  good : (∀ p v, C.loc p ≠ .rs2 v) → Good v₀ (verOf C) (arrOf C) (linState L)

lemma LocOK.eq_idle {β : List (Label P (kbArray k V v₀))}
    {L : List (OpId P × (kbArray k V v₀).Op)} {c : Fin k} {A : Fin k → V × Option (Fin k)}
    {p : P} {l : RLoc k V} (h : LocOK v₀ β L c A p l none) : l = .idle := by
  cases l <;> simp_all [LocOK]

/-- Frame lemma: the clause of a process is preserved by steps of other processes, provided
`Ver` is unchanged (if the process is not idle) and `A` is unchanged (if it is in line 58). -/
lemma LocOK.frame {β β' : List (Label P (kbArray k V v₀))}
    {L M : List (OpId P × (kbArray k V v₀).Op)} {c c' : Fin k}
    {A A' : Fin k → V × Option (Fin k)} {p : P} {l : RLoc k V} {pd : Option (ArrOp k V)}
    (h : LocOK v₀ β L c A p l pd) (hcur : curOp β' p = curOp β p)
    (hM : curOp β p ∉ M.map Prod.fst)
    (hc : l ≠ .idle → c' = c) (hA : ∀ v, l = .rs2 v → A' = A) :
    LocOK v₀ β' (L ++ M) c' A' p l pd := by
  have hnm : curOp β p ∉ L.map Prod.fst → curOp β p ∉ (L ++ M).map Prod.fst := by
    intro hL; simp only [List.map_append, List.mem_append, not_or]; exact ⟨hL, hM⟩
  cases l with
  | idle => exact h
  | rd0 i => exact ⟨h.1, hcur ▸ hnm h.2⟩
  | rd1 a =>
    rw [hc (by simp)]
    exact ⟨h.1, by rw [hcur, ObjSpec.respIn_append_of_eq_some h.2]⟩
  | done r => exact ⟨h.1, by rw [hcur, ObjSpec.respIn_append_of_eq_some h.2]⟩
  | wr0 i x => exact ⟨h.1, hcur ▸ hnm h.2⟩
  | wr1 i x c'' => rw [hc (by simp)]; exact ⟨h.1, hcur ▸ hnm h.2.1, h.2.2⟩
  | rs0 => exact ⟨h.1, hcur ▸ hnm h.2⟩
  | rs1 v => rw [hc (by simp)]; exact ⟨h.1, hcur ▸ hnm h.2.1, h.2.2⟩
  | rs2 v =>
    rw [hc (by simp), hA v rfl]; exact ⟨h.1, hcur ▸ hnm h.2.1, h.2.2⟩

omit [NeZero k] in
lemma _root_.Podc.WritableObjects.ResetsIsolated.of_append
    {β γ : List (Label P (kbArray k V v₀))}
    (h : ResetsIsolated (β ++ γ)) : ResetsIsolated β := by
  intro x y hxy hx hy
  rcases h x y hxy (opOf_append_of_eq_some hx γ) hy.mono with h' | h'
  · exact Or.inl (h'.of_append_of_invoked hy)
  · exact Or.inr (h'.of_append_of_invoked (Invoked.of_opOf_eq_some hx))

/-- While a reset is pending, every other process is idle. -/
lemma excl {β : List (Label P (kbArray k V v₀))} {C : RCfg k V v₀ P}
    (hrun : (resettableArray k V v₀ P).run β = some C) (hRI : ResetsIsolated β) {p q : P}
    (hp : C.pend p = some .reset) (hq : q ≠ p) : C.pend q = none := by
  by_contra hne
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨-, hpc, hpo⟩ := (resettableArray k V v₀ P).run_pend_curOp hrun hp
  obtain ⟨hqi, hqc, -⟩ := (resettableArray k V v₀ P).run_pend_curOp hrun ho
  have hxy : curOp β p ≠ curOp β q := fun h => hq (congrArg Prod.fst h).symm
  rcases hRI _ _ hxy hpo hqi with h | h
  · exact hpc h.completed
  · exact hqc h.completed


/-! ## Preservation of the invariant -/

lemma inv_init :
    Inv ([] : List (Label P (kbArray k V v₀))) (resettableArray k V v₀ P).initCfg [] :=
  ⟨isLinearization_nil, fun _ => rfl, fun _ _ => ⟨wrapOK_none _ _ _, by
    simp [decode, linState, Impl.initCfg, resettableArray]; rfl⟩⟩

lemma ver_update_some (m : (j : Option (Fin k)) → (raBase k V v₀ j).State) (i : Fin k)
    (x : (raBase k V v₀ (some i)).State) : Function.update m (some i) x none = m none :=
  Function.update_of_ne (by simp) _ _

lemma arr_update_some (m : (j : Option (Fin k)) → (raBase k V v₀ j).State) (i : Fin k)
    (x : V × Option (Fin k)) :
    (fun j => (Function.update m (some i) x (some j) : V × Option (Fin k))) =
      Function.update (fun j => (m (some j) : V × Option (Fin k))) i x := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_of_ne (by simpa using hj), Function.update_of_ne hj]

lemma arr_update_none (m : (j : Option (Fin k)) → (raBase k V v₀ j).State) (x : Fin k) :
    (fun j => (Function.update m none x (some j) : V × Option (Fin k))) =
      fun j => (m (some j) : V × Option (Fin k)) := by
  funext j; exact Function.update_of_ne (by simp) _ _

omit [DecidableEq P] in
lemma ver_eq_of_mem {C C' : RCfg k V v₀ P} (h : C.mem = C'.mem) : verOf C = verOf C' := by
  show C.mem none = C'.mem none; rw [h]

omit [DecidableEq P] in
lemma arr_eq_of_mem {C C' : RCfg k V v₀ P} (h : C.mem = C'.mem) : arrOf C = arrOf C' := by
  funext i; show C.mem (some i) = C'.mem (some i); rw [h]

section Step

variable {β : List (Label P (kbArray k V v₀))} {C₀ : RCfg k V v₀ P}
  {L : List (OpId P × (kbArray k V v₀).Op)}

/-- If a non-reset operation is pending, no process is between lines 57 and 58. -/
lemma noRS2_of_pending (hrun : (resettableArray k V v₀ P).run β = some C₀) (hI : Inv β C₀ L)
    (hRI : ResetsIsolated β) {p : P} (hp : C₀.pend p ≠ none) (hnr : C₀.pend p ≠ some .reset) :
    ∀ q v, C₀.loc q ≠ .rs2 v := by
  intro q v hq
  have h := hI.loc q
  rw [hq] at h
  by_cases hqp : q = p
  · subst hqp; exact hnr h.1
  · exact hp (excl hrun hRI h.1 (Ne.symm hqp))

/-- While a reset is pending, all other processes are idle. -/
lemma idle_of_reset (hrun : (resettableArray k V v₀ P).run β = some C₀) (hI : Inv β C₀ L)
    (hRI : ResetsIsolated β) {p q : P} (hp : C₀.pend p = some .reset) (hq : q ≠ p) :
    C₀.loc q = .idle := by
  have h := hI.loc q
  rw [excl hrun hRI hp hq] at h
  exact h.eq_idle

/-- Steps of other processes: the clause of `q` survives. -/
lemma locOK_other {β' : List (Label P (kbArray k V v₀))} {C : RCfg k V v₀ P}
    {M : List (OpId P × (kbArray k V v₀).Op)} {q : P} (hI : Inv β C₀ L)
    (hloc : C.loc q = C₀.loc q) (hpend : C.pend q = C₀.pend q)
    (hcur : curOp β' q = curOp β q) (hM : curOp β q ∉ M.map Prod.fst)
    (hc : C₀.loc q ≠ .idle → verOf C = verOf C₀)
    (hA : ∀ v, C₀.loc q = .rs2 v → arrOf C = arrOf C₀) :
    LocOK v₀ β' (L ++ M) (verOf C) (arrOf C) q (C.loc q) (C.pend q) := by
  rw [hloc, hpend]; exact (hI.loc q).frame hcur hM hc hA

lemma inv_step_inv (hrun : (resettableArray k V v₀ P).run β = some C₀) (hI : Inv β C₀ L)
    {C : RCfg k V v₀ P} {p : P} {o : ArrOp k V}
    (hs : (resettableArray k V v₀ P).step C₀ (.inv p o) = some C) :
    Inv (β ++ [.inv p o]) C L := by
  obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hl0 : C₀.loc p = .idle := by
    have h := hI.loc p; rw [h0] at h; exact h.eq_idle
  have hnot : curOp β p ∉ L.map Prod.fst := fun hm =>
    (resettableArray k V v₀ P).not_invoked_curOp_of_idle hrun h0 (hI.lin.mem_invoked hm)
  refine ⟨hI.lin.append_inv p o, fun q => ?_, fun hno => ?_⟩
  · by_cases hq : q = p
    · subst hq
      rw [hloc, hpend, Function.update_self, Function.update_self, hl0]
      cases o <;> exact ⟨rfl, by rwa [curOp_append_inv]⟩
    · have h := locOK_other (β' := β ++ [.inv p o]) (M := []) hI
        (by rw [hloc, Function.update_of_ne hq]) (by rw [hpend, Function.update_of_ne hq])
        (curOp_append_inv _ _ _ _) (by simp) (fun _ => ver_eq_of_mem hmem)
        (fun _ _ => arr_eq_of_mem hmem)
      rwa [List.append_nil] at h
  · have h := hI.good (fun q v hqv => by
      by_cases hq : q = p
      · subst hq; rw [hl0] at hqv; cases hqv
      · exact hno q v (by rw [hloc, Function.update_of_ne hq]; exact hqv))
    rwa [ver_eq_of_mem hmem, arr_eq_of_mem hmem]

lemma inv_step_ret (hI : Inv β C₀ L)
    {C : RCfg k V v₀ P} {p : P} {r : Option V}
    (hs : (resettableArray k V v₀ P).step C₀ (.ret p r) = some C) :
    Inv (β ++ [.ret p r]) C L := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  have hcl := hI.loc p
  cases hl : C₀.loc p with
  | idle => rw [hl] at hcl; exact absurd hcl h0
  | done r' =>
    rw [hl] at hcl
    simp only [resettableArray, hl, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact
    refine ⟨hI.lin.append_ret_of_respIn hcl.2, fun q => ?_, fun hno => ?_⟩
    · by_cases hq : q = p
      · subst hq; rw [hpend, hloc, Function.update_self, Function.update_self]; rfl
      · have h := locOK_other (M := []) hI
          (by rw [hloc, Function.update_of_ne hq]) (by rw [hpend, Function.update_of_ne hq])
          (curOp_append_ret_of_ne _ r' (Ne.symm hq)) (by simp) (fun _ => ver_eq_of_mem hmem)
          (fun _ _ => arr_eq_of_mem hmem)
        rwa [List.append_nil] at h
    · have h := hI.good (fun q v hqv => by
        by_cases hq : q = p
        · subst hq; rw [hl] at hqv; cases hqv
        · exact hno q v (by rw [hloc, Function.update_of_ne hq]; exact hqv))
      rwa [ver_eq_of_mem hmem, arr_eq_of_mem hmem]
  | rd0 _ | rd1 _ | wr0 _ _ | wr1 _ _ _ | rs0 | rs1 _ | rs2 _ =>
    simp [resettableArray, hl] at hact

lemma noRS2_prev {C : RCfg k V v₀ P} {p : P} {l' : RLoc k V}
    (hno : ∀ q v, C.loc q ≠ .rs2 v) (hloc : C.loc = Function.update C₀.loc p l')
    (hl : ∀ v, C₀.loc p ≠ .rs2 v) : ∀ q v, C₀.loc q ≠ .rs2 v := by
  intro q v hq
  by_cases hqp : q = p
  · subst hqp; exact hl v hq
  · exact hno q v (by rw [hloc, Function.update_of_ne hqp]; exact hq)

/-- A linearization point at a step of `p`. -/
lemma push_tau {C : RCfg k V v₀ P} {p : P} {o : ArrOp k V}
    (hrun' : (resettableArray k V v₀ P).run (β ++ [.tau p]) = some C) (hI : Inv β C₀ L)
    (hpd : C.pend p = some o) (hnot : curOp β p ∉ L.map Prod.fst) :
    IsLinearization (β ++ [.tau p]) (L ++ [(curOp β p, o)]) := by
  have h := (resettableArray k V v₀ P).run_pend_curOp hrun' hpd
  rw [curOp_append_tau] at h
  exact (hI.lin.append_tau p).push h.2.2 hnot h.2.1

lemma inv_step_tau (hrun : (resettableArray k V v₀ P).run β = some C₀) (hI : Inv β C₀ L)
    (hRI : ResetsIsolated β) {C : RCfg k V v₀ P} {p : P}
    (hs : (resettableArray k V v₀ P).step C₀ (.tau p) = some C) :
    ∃ L', Inv (β ++ [.tau p]) C L' := by
  have hrun' : (resettableArray k V v₀ P).run (β ++ [.tau p]) = some C := by
    rw [Impl.run_concat, hrun]; exact hs
  obtain ⟨h0, hpend, i', o', κ, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hcl := hI.loc p
  have hcur : ∀ q, curOp (β ++ [.tau p]) q = curOp β q := fun q => curOp_append_tau _ _ _
  have hlocq : ∀ q, q ≠ p → C.loc q = C₀.loc q := fun q hq => by
    rw [hloc, Function.update_of_ne hq]
  have hpendq : ∀ q, C.pend q = C₀.pend q := fun q => by rw [hpend]
  have hnotM : ∀ q, q ≠ p → ∀ o : ArrOp k V, curOp β q ∉ [(curOp β p, o)].map Prod.fst :=
    fun q hq o h => hq (by simpa using congrArg Prod.fst (List.mem_singleton.1 h))
  cases hl : C₀.loc p with
  | idle => simp [resettableArray, hl] at hact
  | done _ => simp [resettableArray, hl] at hact
  | rd0 i =>
    rw [hl] at hcl hact
    obtain ⟨hpd, hnot⟩ := hcl
    cases hact
    have hno := noRS2_of_pending hrun hI hRI h0 (by rw [hpd]; simp)
    have hG := hI.good hno
    have hmem' : C.mem = C₀.mem := by rw [hmem]; exact Function.update_eq_self _ _
    refine ⟨L ++ [(curOp β p, .read i)], push_tau hrun' hI (by rw [hpendq, hpd]) hnot,
      fun q => ?_, fun _ => ?_⟩
    · by_cases hq : q = p
      · subst hq
        rw [hloc, Function.update_self, hpendq, hpd]
        refine ⟨⟨i, rfl⟩, ?_⟩
        rw [hcur, ObjSpec.respIn_concat_self hnot, ver_eq_of_mem hmem']
        exact congrArg some (congrArg some (hG i).2)
      · exact locOK_other hI (hlocq q hq) (hpendq q) (hcur q) (hnotM q hq _)
          (fun _ => ver_eq_of_mem hmem') (fun _ _ => arr_eq_of_mem hmem')
    · rw [ver_eq_of_mem hmem', arr_eq_of_mem hmem', linState_concat]; exact hG
  | rd1 a =>
    rw [hl] at hcl hact
    obtain ⟨⟨i, hpd⟩, hresp⟩ := hcl
    cases hact
    have hno := noRS2_of_pending hrun hI hRI h0 (by rw [hpd]; simp)
    have hmem' : C.mem = C₀.mem := by rw [hmem]; exact Function.update_eq_self _ _
    refine ⟨L, hI.lin.append_tau p, fun q => ?_, fun _ => ?_⟩
    · by_cases hq : q = p
      · subst hq
        rw [hloc, Function.update_self, hpendq, hpd]
        exact ⟨by simp, by rw [hcur]; exact hresp⟩
      · have h := locOK_other (M := []) hI (hlocq q hq) (hpendq q) (hcur q) (by simp)
          (fun _ => ver_eq_of_mem hmem') (fun _ _ => arr_eq_of_mem hmem')
        rwa [List.append_nil] at h
    · rw [ver_eq_of_mem hmem', arr_eq_of_mem hmem']; exact hI.good hno
  | wr0 i x =>
    rw [hl] at hcl hact
    obtain ⟨hpd, hnot⟩ := hcl
    cases hact
    have hno := noRS2_of_pending hrun hI hRI h0 (by rw [hpd]; simp)
    have hmem' : C.mem = C₀.mem := by rw [hmem]; exact Function.update_eq_self _ _
    refine ⟨L, hI.lin.append_tau p, fun q => ?_, fun _ => ?_⟩
    · by_cases hq : q = p
      · subst hq
        rw [hloc, Function.update_self, hpendq, hpd]
        exact ⟨rfl, by rwa [hcur], (ver_eq_of_mem hmem').symm⟩
      · have h := locOK_other (M := []) hI (hlocq q hq) (hpendq q) (hcur q) (by simp)
          (fun _ => ver_eq_of_mem hmem') (fun _ _ => arr_eq_of_mem hmem')
        rwa [List.append_nil] at h
    · rw [ver_eq_of_mem hmem', arr_eq_of_mem hmem']; exact hI.good hno
  | wr1 i x c =>
    rw [hl] at hcl hact
    obtain ⟨hpd, hnot, hc⟩ := hcl
    cases hact
    have hno := noRS2_of_pending hrun hI hRI h0 (by rw [hpd]; simp)
    have hG := hI.good hno
    have hver : verOf C = verOf C₀ := by
      show C.mem none = C₀.mem none; rw [hmem]; exact ver_update_some _ _ _
    have harr : arrOf C = Function.update (arrOf C₀) i (x, some c) := by
      show (fun j => C.mem (some j)) = _; rw [hmem]; exact arr_update_some _ _ _
    refine ⟨L ++ [(curOp β p, .write i x)], push_tau hrun' hI (by rw [hpendq, hpd]) hnot,
      fun q => ?_, fun _ => ?_⟩
    · by_cases hq : q = p
      · subst hq
        rw [hloc, Function.update_self, hpendq, hpd]
        exact ⟨by simp, by rw [hcur, ObjSpec.respIn_concat_self hnot]⟩
      · exact locOK_other hI (hlocq q hq) (hpendq q) (hcur q) (hnotM q hq _)
          (fun _ => hver) (fun v hv => absurd hv (hno q v))
    · rw [hver, harr, linState_concat]
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        rw [hc]
        exact ⟨wrapOK_fresh _ _ _, by simp [decode]⟩
      · simp only [Function.update_of_ne hj]
        exact hG j
  | rs0 =>
    rw [hl] at hcl hact
    obtain ⟨hpd, hnot⟩ := hcl
    cases hact
    have hmem' : C.mem = C₀.mem := by rw [hmem]; exact Function.update_eq_self _ _
    refine ⟨L, hI.lin.append_tau p, fun q => ?_, fun hno => ?_⟩
    · by_cases hq : q = p
      · subst hq
        rw [hloc, Function.update_self, hpendq, hpd]
        exact ⟨rfl, by rwa [hcur], by rw [ver_eq_of_mem hmem']⟩
      · have h := locOK_other (M := []) hI (hlocq q hq) (hpendq q) (hcur q) (by simp)
          (fun _ => ver_eq_of_mem hmem') (fun _ _ => arr_eq_of_mem hmem')
        rwa [List.append_nil] at h
    · rw [ver_eq_of_mem hmem', arr_eq_of_mem hmem']
      exact hI.good (noRS2_prev hno hloc (by rw [hl]; simp))
  | rs1 v =>
    rw [hl] at hcl hact
    obtain ⟨hpd, hnot, hv⟩ := hcl
    cases hact
    have hidle := fun q (hq : q ≠ p) => idle_of_reset hrun hI hRI hpd hq
    have hG := hI.good (fun q w hq => by
      by_cases hqp : q = p
      · subst hqp; rw [hl] at hq; cases hq
      · rw [hidle q hqp] at hq; cases hq)
    have hver : verOf C = v := by
      show C.mem none = v; rw [hmem]; exact Function.update_self _ _ _
    have harr : arrOf C = arrOf C₀ := by
      show (fun j => C.mem (some j)) = _; rw [hmem]; exact arr_update_none _ _
    refine ⟨L, hI.lin.append_tau p, fun q => ?_, fun hno => ?_⟩
    · by_cases hq : q = p
      · subst hq
        rw [hloc, Function.update_self, hpendq, hpd, harr, hver]
        refine ⟨rfl, by rwa [hcur], rfl, fun j hj => ?_⟩
        rw [hv] at hj ⊢
        exact (hG j).1.shift hj
      · have h := locOK_other (M := []) hI (hlocq q hq) (hpendq q) (hcur q) (by simp)
          (fun h => absurd (hidle q hq) h) (fun w hw => by rw [hidle q hq] at hw; cases hw)
        rwa [List.append_nil] at h
    · exact absurd (by rw [hloc, Function.update_self]) (hno p v)
  | rs2 v =>
    rw [hl] at hcl hact
    obtain ⟨hpd, hnot, hv, hW⟩ := hcl
    cases hact
    have hidle := fun q (hq : q ≠ p) => idle_of_reset hrun hI hRI hpd hq
    have hver : verOf C = verOf C₀ := by
      show C.mem none = C₀.mem none; rw [hmem]; exact ver_update_some _ _ _
    have harr : arrOf C = Function.update (arrOf C₀) v (v₀, none) := by
      show (fun j => C.mem (some j)) = _; rw [hmem]; exact arr_update_some _ _ _
    refine ⟨L ++ [(curOp β p, .reset)], push_tau hrun' hI (by rw [hpendq, hpd]) hnot,
      fun q => ?_, fun _ => ?_⟩
    · by_cases hq : q = p
      · subst hq
        rw [hloc, Function.update_self, hpendq, hpd]
        exact ⟨by simp, by rw [hcur, ObjSpec.respIn_concat_self hnot]⟩
      · exact locOK_other hI (hlocq q hq) (hpendq q) (hcur q) (hnotM q hq _)
          (fun h => absurd (hidle q hq) h) (fun w hw => by rw [hidle q hq] at hw; cases hw)
    · rw [hver, harr, linState_concat, hv]
      intro j
      by_cases hj : j = v
      · subst hj
        simp only [Function.update_self]
        exact ⟨wrapOK_none _ _ _, by simp [decode]⟩
      · simp only [Function.update_of_ne hj]
        exact ⟨(hW j hj).1, by simp [decode, (hW j hj).2]⟩

end Step

/-- The invariant holds after every finite execution in which resets are isolated. -/
theorem inv_of_run {β : List (Label P (kbArray k V v₀))} {C : RCfg k V v₀ P}
    (h : (resettableArray k V v₀ P).run β = some C) (hRI : ResetsIsolated β) :
    ∃ L, Inv β C L := by
  revert hRI
  refine (resettableArray k V v₀ P).run_induction
    (Q := fun β C => ResetsIsolated β → ∃ L, Inv β C L) (fun _ => ⟨[], inv_init⟩) ?_ h
  intro β C₀ ℓ C hrun ih hs hRI
  obtain ⟨L, hI⟩ := ih hRI.of_append
  cases ℓ with
  | inv p o => exact ⟨L, inv_step_inv hrun hI hs⟩
  | ret p r => exact ⟨L, inv_step_ret hI hs⟩
  | tau p => exact inv_step_tau hrun hI hRI.of_append hs

omit [NeZero k] in
/-- Non-vacuity of the hypothesis: an execution without `Reset` invocations satisfies
`ResetsIsolated` (so Lemma 4.2 contains the linearizability of the reset-free array). Every
sequential execution satisfies it as well. -/
theorem _root_.Podc.WritableObjects.resetsIsolated_of_no_reset
    (α : List (Label P (kbArray k V v₀)))
    (h : ∀ p, Label.inv p ArrOp.reset ∉ α) : ResetsIsolated α := by
  intro x y _ hx _
  exfalso
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hx
  have hmem : ArrOp.reset ∈ opsOf α x.1 := by rw [← hget]; exact List.getElem_mem hlt
  simp only [opsOf, List.mem_filterMap] at hmem
  obtain ⟨ℓ, hℓ, hinv⟩ := hmem
  rw [Label.eq_inv_of_invOf_eq_some hinv] at hℓ
  exact h _ hℓ

end RArray

/-- **Lemma 4.2 of [AGW14] (thesis numbering).** The implementation of Figure 4.15 is a
sequentially resettable `(k,b)`-array: for `k ≥ 1` (`NeZero k`), any set of processes `P` and
every execution `α` in which no `Reset` instance overlaps any other operation instance, the
history of `α` is linearizable with respect to the type `(k,b)`-Array.

The remaining claims of Lemma 4.2 hold by construction: the base objects are the `k + 1`
registers `Ver`, `A[0..k-1]` (`card_baseObjects`), `A[i]` stores a `b`-bit value and a version
in `Option (Fin k)` (`b + O(log k)` bits), and every operation performs at most 3 base-object
accesses (`stepBound_invoke`, `stepBound_access`). -/
theorem lemma_4_2 (k : ℕ) [NeZero k] (V : Type) (v₀ : V) (P : Type) [DecidableEq P]
    (α : List (Label P (kbArray k V v₀))) (hα : (resettableArray k V v₀ P).Valid α)
    (hiso : ResetsIsolated α) : ∃ L, IsLinearization α L := by
  obtain ⟨C, hC⟩ := hα
  obtain ⟨L, hI⟩ := RArray.inv_of_run hC hiso
  exact ⟨L, hI.lin⟩

end Podc.WritableObjects
