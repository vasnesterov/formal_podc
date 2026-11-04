import Podc.Computability.Distributed.SharedMemory.Awareness
import Cslib.Computability.Distributed.SharedMemory.Objects.MaxRegister
import Mathlib.Tactic.IntervalCases

/-!
# The paper's Definitions 1–5 taken literally, and counterexamples to Lemma 2 and Claim 1

Hendler–Khait (PODC'14) define (Definition 1) an event `e` of process `p` on object `o` in `E` to be
*invisible* if it does not change the value of `o`, or if it is followed by a `write` `e'` to `o`
such that no event between `e` and `e'` is applied to `o` and `p` takes no step in between.
Definition 2 makes a read/CAS event *aware* of a write/CAS event `e_q` on the same object that is
visible in a prefix containing both, and closes awareness under chaining; Definition 3 makes `p`
aware of `q` if some event of `p` is aware of some event of `q`; Definition 5 calls `p` *hidden* if
no other process is aware of `p`.

Here the definitions are transcribed on finite event sequences (`Ev`) and evaluated on a concrete
execution of a single-writer max register (`toyImpl`): the writer `q` writes `5` twice in a row
(the second write is trivial and overwrites the first), then the reader `r` reads `5`. Neither
write is visible, so nobody is aware of `q`: `q` is hidden, and no event is aware of an event of
`q`. Yet removing `q`'s events does not leave an execution (the reader would read `0`).

* `lemma2_false` — Lemma 2 is false as stated (with `p := q`, nothing is aware of `q`);
* `claim1_false` — Claim 1 is false as stated (`{q}` is a set of hidden processes).

(For Lemma 2 we even use a *more generous* closure than the paper's Definition 2, which in its
transitive clause also requires `e_p` to access `o`; fewer awareness pairs would only make the
counterexample easier.) The flaw is the combination of the two invisibility clauses of
Definition 1: an overwritten write is invisible, and so is the trivial write that overwrites it.
`Cslib.SharedMemory.Awareness` replaces these definitions by a sound data-flow semantics.
-/

namespace Podc.ReadUpdateTradeoffs.PaperDefs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

/-! ### Events and the paper's definitions -/

/-- An event: process, base object, primitive. -/
structure Ev (P ι V : Type) where
  proc : P
  obj : ι
  prim : CASOp V

variable {P ι V : Type} [DecidableEq ι] [DecidableEq V]

/-- The memory before the `n`-th event of `E`, starting from `m₀`. -/
def memBefore (v₀ : V) (m₀ : ι → V) (E : List (Ev P ι V)) (n : ℕ) : ι → V :=
  (E.take n).foldl (fun m e =>
    Function.update m e.obj ((casObject V v₀).δ (m e.obj) e.prim).1) m₀

/-- The `n`-th event changes the value of its object. -/
def Changes (v₀ : V) (m₀ : ι → V) (E : List (Ev P ι V)) (n : ℕ) : Prop :=
  ∃ e, E[n]? = some e ∧
    ((casObject V v₀).δ (memBefore v₀ m₀ E n e.obj) e.prim).1 ≠ memBefore v₀ m₀ E n e.obj

/-- `e` is a write. -/
def IsWrite (e : Ev P ι V) : Prop := ∃ v, e.prim = .write v

/-- `e` is a read. -/
def IsRead (e : Ev P ι V) : Prop := e.prim = .read

/-- `e` is a CAS. -/
def IsCAS (e : Ev P ι V) : Prop := ∃ a b, e.prim = .cas a b

/-- **Definition 1** (invisible event). -/
def Invisible (v₀ : V) (m₀ : ι → V) (E : List (Ev P ι V)) (n : ℕ) : Prop :=
  ¬ Changes v₀ m₀ E n ∨
    ∃ e, E[n]? = some e ∧ ∃ m e', n < m ∧ E[m]? = some e' ∧ IsWrite e' ∧ e'.obj = e.obj ∧
      ∀ k f, n < k → k < m → E[k]? = some f → f.proc ≠ e.proc ∧ f.obj ≠ e.obj

/-- Visible = not invisible. -/
def Visible (v₀ : V) (m₀ : ι → V) (E : List (Ev P ι V)) (n : ℕ) : Prop :=
  n < E.length ∧ ¬ Invisible v₀ m₀ E n

/-- **Definition 2** (event `a` is aware of event `b`), with a generous transitive closure. -/
inductive Aware (v₀ : V) (m₀ : ι → V) (E : List (Ev P ι V)) : ℕ → ℕ → Prop
  | base {a b : ℕ} {ea eb : Ev P ι V} : E[a]? = some ea → E[b]? = some eb →
      (IsWrite eb ∨ IsCAS eb) → ea.obj = eb.obj → b < a → (IsRead ea ∨ IsCAS ea) →
      (∃ m, a < m ∧ m ≤ E.length ∧ Visible v₀ m₀ (E.take m) b) → Aware v₀ m₀ E a b
  | trans {a b c : ℕ} : Aware v₀ m₀ E c b → Aware v₀ m₀ E a c → Aware v₀ m₀ E a b

/-- **Definition 3** (process `p` is aware of process `q`). -/
def AwareOf (v₀ : V) (m₀ : ι → V) (E : List (Ev P ι V)) (p q : P) : Prop :=
  p = q ∨ ∃ a b ea eb, E[a]? = some ea ∧ E[b]? = some eb ∧ ea.proc = p ∧ eb.proc = q ∧
    Aware v₀ m₀ E a b

/-- **Definition 5** (hidden process). -/
def HiddenProc (v₀ : V) (m₀ : ι → V) (E : List (Ev P ι V)) (p : P) : Prop :=
  ∀ p', AwareOf v₀ m₀ E p' p → p = p'

/-! ### The trace of an execution -/

variable {A : ObjSpec} {L : Type} [DecidableEq P]

/-- The base-object events of an execution, in order. -/
noncomputable def traceFrom (I : Impl A (RWC ι V v₀) P L) :
    Config A (RWC ι V v₀) P L → List (Label P A) → List (Ev P ι V)
  | _, [] => []
  | C, ℓ :: α =>
    match I.step C ℓ with
    | none => []
    | some C' =>
      (match ℓ with
        | .tau p => match I.act p (C.loc p) with
          | .access i o _ => [⟨p, i, o⟩]
          | .ret _ _ => []
        | _ => []) ++ traceFrom I C' α

/-! ### A single-writer max register -/

/-- Local states of the toy implementation. -/
inductive Loc where
  | idle (mx : ℕ)
  | w₁ (mx : ℕ)
  | w₂ (mx : ℕ)
  | done (mx : ℕ)
  | rd (mx : ℕ)
  | rdone (mx v : ℕ)
  deriving DecidableEq

/-- The maximum written so far by this process. -/
def Loc.mx : Loc → ℕ
  | .idle m | .w₁ m | .w₂ m | .done m | .rd m | .rdone m _ => m

/-- A single-writer max register on one CAS object (initially `0`): process `0` is the only
writer; `WriteMax(v)` writes `max(previous, v)` **twice**; `ReadMax` reads the register. -/
def toyImpl : Impl maxRegObj (RWC Unit ℕ 0) (Fin 2) Loc where
  memInit := fun _ => 0
  locInit := fun _ => .idle 0
  invoke := fun _ l o => match o with
    | .writeMax v => .w₁ (max l.mx v)
    | .readMax => .rd l.mx
  act := fun _ l => match l with
    | .w₁ m => .access () (.write m) (fun _ => .w₂ m)
    | .w₂ m => .access () (.write m) (fun _ => .done m)
    | .done m => .ret 0 (.idle m)
    | .rd m => .access () .read (fun x => .rdone m (x.elim id (fun _ => 0)))
    | .rdone m v => .ret v (.idle m)
    | .idle m => .ret 0 (.idle m)
  allowed := fun p o => ∀ v, o = .writeMax v → p = 0

instance (p : Fin 2) (o : maxRegObj.Op) : Decidable (toyImpl.allowed p o) := by
  unfold toyImpl
  cases o with
  | writeMax v => exact decidable_of_iff (p = 0) (by simp)
  | readMax => exact isTrue (by simp)

/-- The writer `q = 0` writes `5` twice, then the reader `r = 1` reads `5`. -/
def execE : List (Label (Fin 2) maxRegObj) :=
  [.inv 0 (.writeMax 5), .tau 0, .tau 0, .ret 0 0, .inv 1 .readMax, .tau 1, .ret 1 5]

/-- Its events. -/
def evE : List (Ev (Fin 2) Unit ℕ) := [⟨0, (), .write 5⟩, ⟨0, (), .write 5⟩, ⟨1, (), .read⟩]

lemma execE_valid : toyImpl.Valid execE :=
  Impl.valid_of_crun toyImpl (by decide)

lemma execE_erase_not_valid :
    ¬ toyImpl.Valid (execE.filter (fun ℓ => decide (ℓ.proc ≠ 0))) := by
  rintro ⟨C, hC⟩
  rw [Impl.run_eq_crun toyImpl] at hC
  have : (toyImpl.crun (execE.filter (fun ℓ => decide (ℓ.proc ≠ 0)))).isNone = true := by decide
  rw [hC] at this
  simp at this

lemma trace_execE : traceFrom toyImpl toyImpl.initCfg execE = evE := by
  simp [traceFrom, execE, evE, Impl.step, toyImpl, Impl.initCfg, Function.update, Loc.mx]

/-- No event of `evE` is (directly) aware of another one: the first write is overwritten by the
second (no access in between, and the writer takes no step in between), and the second write
does not change the value. -/
lemma no_base (a b : ℕ) (ea eb : Ev (Fin 2) Unit ℕ) (ha : evE[a]? = some ea)
    (hb : evE[b]? = some eb) (hw : IsWrite eb ∨ IsCAS eb) (hab : b < a)
    (hv : ∃ m, a < m ∧ m ≤ evE.length ∧ Visible 0 (fun _ => 0) (evE.take m) b) : False := by
  obtain ⟨m, ham, hm, hlt, hvis⟩ := hv
  simp only [evE, List.length_cons, List.length_nil] at hm
  have ha3 : a < 3 := by
    by_contra h; push_neg at h; rw [List.getElem?_eq_none (by simpa [evE] using h)] at ha; cases ha
  interval_cases m <;> (try omega) <;> interval_cases a <;> (try omega) <;> interval_cases b <;>
    (try omega) <;> apply hvis <;>
  first
    | (right
       exact ⟨⟨0, (), .write 5⟩, rfl, 1, ⟨0, (), .write 5⟩, by omega, rfl, ⟨5, rfl⟩, rfl,
         fun k f hk1 hk2 => by omega⟩)
    | (left
       rintro ⟨e, he, hne⟩
       simp only [List.take, evE] at he
       cases he
       exact hne (by simp [memBefore, evE]))

lemma not_aware (a b : ℕ) : ¬ Aware 0 (fun _ => 0) evE a b := by
  intro h
  induction h with
  | base ha hb hw _ hab _ hv => exact no_base _ _ _ _ ha hb hw hab hv
  | trans _ _ ih _ => exact ih

/-- **Lemma 2 of Hendler–Khait is false as stated.** In an execution `E` of the single-writer
max register `toyImpl`, no event is aware of an event of the writer `q = 0`, so the `E'` of
Lemma 2 (remove `q`'s events and the events aware of `q`) is `E` without `q`'s labels — and it is
not an execution. -/
theorem lemma2_false :
    toyImpl.Valid execE ∧ traceFrom toyImpl toyImpl.initCfg execE = evE ∧
      (∀ a b eb, evE[b]? = some eb → eb.proc = 0 → ¬ Aware 0 (fun _ => 0) evE a b) ∧
      ¬ toyImpl.Valid (execE.filter (fun ℓ => decide (ℓ.proc ≠ 0))) :=
  ⟨execE_valid, trace_execE, fun a b _ _ _ => not_aware a b, execE_erase_not_valid⟩

/-- **Claim 1 of Hendler–Khait is false as stated.** The writer `q = 0` is hidden after `E`
(Definition 5: no other process is aware of it; also no object is familiar with it, as no write
is visible), but `E − {q}` is not an execution. -/
theorem claim1_false :
    toyImpl.Valid execE ∧ traceFrom toyImpl toyImpl.initCfg execE = evE ∧
      HiddenProc 0 (fun _ => 0) evE (0 : Fin 2) ∧
      (∀ n, ¬ Visible 0 (fun _ => 0) evE n) ∧
      ¬ toyImpl.Valid (execE.filter (fun ℓ => decide (ℓ.proc ≠ 0))) := by
  refine ⟨execE_valid, trace_execE, ?_, ?_, execE_erase_not_valid⟩
  · rintro p' (h | ⟨a, b, ea, eb, -, -, -, -, hab⟩)
    · exact h.symm
    · exact absurd hab (not_aware a b)
  · intro n ⟨hn, hvis⟩
    simp only [evE, List.length_cons, List.length_nil] at hn
    apply hvis
    interval_cases n
    · right
      refine ⟨⟨0, (), .write 5⟩, rfl, 1, ⟨0, (), .write 5⟩, by omega, rfl, ⟨5, rfl⟩, rfl, ?_⟩
      intro k f hk1 hk2; omega
    · left
      rintro ⟨e, he, hne⟩
      simp only [evE] at he; cases he
      exact hne (by simp [memBefore, evE])
    · left
      rintro ⟨e, he, hne⟩
      simp only [evE] at he; cases he
      exact hne (by simp [memBefore, evE])

end Podc.ReadUpdateTradeoffs.PaperDefs
