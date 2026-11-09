import Papers.PODC2012.OptimismConcurrency.LLCorrect
import Papers.PODC2012.OptimismConcurrency.HistLemmas

/-!
# The lookahead reader–writer-lock implementation `I_LA` (refutation of Theorem 7)

`I_LA` keeps the list in an honest shared memory and protects it by one global reader–writer
lock; the lock is acquired at the response to the *first* read (of `head`) of an operation and
released at its response:
* if the operation is *read-only* on the current set `q` (`(setδ q o).1 = q`: `contains`,
  `insert v` with `v ∈ q`, `remove v` with `v ∉ q`), it acquires the lock in shared mode (allowed
  iff there is no writer);
* otherwise it acquires it in exclusive mode (allowed iff there is no holder at all).
Responses to the other reads and writes of a holder are always enabled, every read returns the
current content of the memory, a write takes effect at its response, nothing ever returns `⊥`.
The implementation keeps the current set `q` (updated when a writer returns).

Since two read-only `insert`s hold the lock concurrently, `I_LA` accepts the schedule of
Figure 2(a), and it is a deadlock-free pessimistic LS-linearizable implementation: Theorem 7
(part 2 of Theorem 2) is false.
-/

namespace Podc.OptimismConcurrency

open Cslib.SharedMemory

/-! ## The state machine -/

/-- Locations mentioned by an event. -/
def Ev.locs : LEv ℕ → List Loc
  | .rinv _ _ y => [y]
  | .rres _ _ (some n) => [n.next]
  | .winv _ _ y n => [y, n.next]
  | _ => []

lemma Ev.mentions_iff (X : Loc) (e : LEv ℕ) : Ev.mentions X e = true ↔ X ∈ e.locs := by
  rcases e with _ | _ | _ | ⟨_, _, _ | _⟩ | _ | _ <;> simp [Ev.mentions, Ev.locs] <;> tauto

/-- Configurations of `I_LA`: memory, client states, the lock (readers, writer), the current
set, the locations mentioned so far, and the processes that invoked an operation. -/
structure LACfg where
  mem : Mem
  cl : ℕ → CSt
  rd : Finset ℕ
  wr : Option ℕ
  q : Finset ℤ
  used : Finset Loc
  procs : Finset ℕ

/-- The initial configuration. -/
def LACfg.init : LACfg := ⟨mem0, fun _ => .idle, ∅, none, ∅, ∅, ∅⟩

/-- `p` holds the lock. -/
def LACfg.holds (c : LACfg) (p : ℕ) : Prop := p ∈ c.rd ∨ c.wr = some p

instance LACfg.decHolds (c : LACfg) (p : ℕ) : Decidable (c.holds p) := by
  unfold LACfg.holds; infer_instance

/-- Bookkeeping common to every event. -/
def LACfg.adv (c : LACfg) (e : LEv ℕ) : LACfg :=
  { c with cl := Function.update c.cl e.proc (cstep (c.cl e.proc) e),
           used := c.used ∪ e.locs.toFinset, procs := insert e.proc c.procs }

/-- One step of `I_LA`. -/
def laStep (c : LACfg) : LEv ℕ → Option LACfg
  | e@(.inv p _ _) => if c.cl p = .idle then some (c.adv e) else none
  | e@(.rinv p _ y) => match c.cl p with
    | .run o s => if act o s = .read y then some (c.adv e) else none
    | _ => none
  | e@(.winv p _ y n) => match c.cl p with
    | .run o s =>
      if act o s = .write y n ∨ (act o s = .alloc n ∧ y ≠ headL ∧ y ≠ tailL ∧ y ∉ c.used) then
        some (c.adv e) else none
    | _ => none
  | e@(.res p _ r) => match c.cl p with
    | .run o s =>
      if act o s = .ret r then
        some { c.adv e with rd := c.rd.erase p, wr := if c.wr = some p then none else c.wr,
                            q := if c.wr = some p then (setδ c.q o).1 else c.q }
      else none
    | _ => none
  | e@(.rres p _ v) => match c.cl p, v with
    | .pend o _ (.rd y), some n =>
      if c.mem y = some n then
        if c.holds p then some (c.adv e)
        else if (setδ c.q o).1 = c.q then
          (if c.wr = none then some { c.adv e with rd := insert p c.rd } else none)
        else if c.rd = ∅ ∧ c.wr = none then some { c.adv e with wr := some p } else none
      else none
    | _, _ => none
  | e@(.wres p _ ok) => match c.cl p, ok with
    | .pend _ _ (.wr y n), true => some { c.adv e with mem := Function.update c.mem y (some n) }
    | _, _ => none

/-- Run `I_LA` along a history. -/
def laRun (c : LACfg) : LHist ℕ → Option LACfg
  | [] => some c
  | e :: l => (laStep c e).bind (fun c' => laRun c' l)

/-- **The lookahead implementation** `I_LA`: the histories it can export. -/
def I_LA : Set (LHist ℕ) := {H | (laRun LACfg.init H).isSome}

instance decMemI_LA (H : LHist ℕ) : Decidable (H ∈ I_LA) :=
  inferInstanceAs (Decidable ((laRun LACfg.init H).isSome = true))

lemma laRun_concat (c : LACfg) (H : LHist ℕ) (e : LEv ℕ) :
    laRun c (H ++ [e]) = (laRun c H).bind (fun c' => laStep c' e) := by
  induction H generalizing c with
  | nil => simp only [List.nil_append, laRun, Option.bind_some]; cases laStep c e <;> rfl
  | cons e' H ih => simp only [List.cons_append, laRun, ih]; cases laStep c e' <;> simp

/-! ## Characterization of the steps -/

/-- The steps of `I_LA`, explicitly. -/
lemma laStep_some {c c' : LACfg} {e : LEv ℕ} (h : laStep c e = some c') :
    (∃ p o, e = .inv p () o ∧ c.cl p = .idle ∧ c' = c.adv e) ∨
    (∃ p y o s, e = .rinv p () y ∧ c.cl p = .run o s ∧ act o s = .read y ∧ c' = c.adv e) ∨
    (∃ p y n o s, e = .winv p () y n ∧ c.cl p = .run o s ∧
      (act o s = .write y n ∨ (act o s = .alloc n ∧ y ≠ headL ∧ y ≠ tailL ∧ y ∉ c.used)) ∧
      c' = c.adv e) ∨
    (∃ p r o s, e = .res p () r ∧ c.cl p = .run o s ∧ act o s = .ret r ∧
      c' = { c.adv e with rd := c.rd.erase p, wr := if c.wr = some p then none else c.wr,
                          q := if c.wr = some p then (setδ c.q o).1 else c.q }) ∨
    (∃ p n o s y, e = .rres p () (some n) ∧ c.cl p = .pend o s (.rd y) ∧ c.mem y = some n ∧
      c.holds p ∧ c' = c.adv e) ∨
    (∃ p n o s y, e = .rres p () (some n) ∧ c.cl p = .pend o s (.rd y) ∧ c.mem y = some n ∧
      ¬ c.holds p ∧ (setδ c.q o).1 = c.q ∧ c.wr = none ∧
      c' = { c.adv e with rd := insert p c.rd }) ∨
    (∃ p n o s y, e = .rres p () (some n) ∧ c.cl p = .pend o s (.rd y) ∧ c.mem y = some n ∧
      ¬ c.holds p ∧ (setδ c.q o).1 ≠ c.q ∧ c.rd = ∅ ∧ c.wr = none ∧
      c' = { c.adv e with wr := some p }) ∨
    (∃ p y n o s, e = .wres p () true ∧ c.cl p = .pend o s (.wr y n) ∧
      c' = { c.adv e with mem := Function.update c.mem y (some n) }) := by
  cases e with
  | inv p x o =>
    cases x
    simp only [laStep] at h; split_ifs at h with h1; cases h
    exact Or.inl ⟨p, o, rfl, h1, rfl⟩
  | rinv p x y =>
    cases x
    rcases hcl : c.cl p with _ | ⟨o, s⟩ | ⟨o, s, pd⟩ <;> simp [laStep, hcl] at h
    obtain ⟨h1, rfl⟩ := h
    exact Or.inr (Or.inl ⟨p, y, o, s, rfl, hcl, h1, rfl⟩)
  | winv p x y n =>
    cases x
    rcases hcl : c.cl p with _ | ⟨o, s⟩ | ⟨o, s, pd⟩ <;> simp only [laStep, hcl, reduceCtorEq] at h
    split_ifs at h with h1; cases h
    exact Or.inr (Or.inr (Or.inl ⟨p, y, n, o, s, rfl, hcl, h1, rfl⟩))
  | res p x r =>
    cases x
    rcases hcl : c.cl p with _ | ⟨o, s⟩ | ⟨o, s, pd⟩ <;> simp only [laStep, hcl, reduceCtorEq] at h
    by_cases h1 : act o s = .ret r
    · rw [ite_eq_left h1, Option.some.injEq] at h; subst h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, r, o, s, rfl, hcl, h1, rfl⟩)))
    · rw [ite_eq_right h1] at h; cases h
  | rres p x v =>
    cases x
    rcases hcl : c.cl p with _ | ⟨o, s⟩ | ⟨o, s, ⟨y⟩ | ⟨y, n'⟩⟩ <;> rcases v with _ | n <;>
      simp only [laStep, hcl, reduceCtorEq] at h
    by_cases h1 : c.mem y = some n
    · rw [ite_eq_left h1] at h
      by_cases h2 : c.holds p
      · rw [ite_eq_left h2, Option.some.injEq] at h; subst h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, n, o, s, y, rfl, hcl, h1, h2, rfl⟩))))
      · by_cases h3 : (setδ c.q o).1 = c.q
        · by_cases h4 : c.wr = none
          · rw [ite_eq_right h2, ite_eq_left h3, ite_eq_left h4, Option.some.injEq] at h; subst h
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨p, n, o, s, y, rfl, hcl, h1, h2, h3, h4, rfl⟩)))))
          · rw [ite_eq_right h2, ite_eq_left h3, ite_eq_right h4] at h; cases h
        · by_cases h4 : c.rd = ∅ ∧ c.wr = none
          · rw [ite_eq_right h2, ite_eq_right h3, ite_eq_left h4, Option.some.injEq] at h; subst h
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨p, n, o, s, y, rfl, hcl, h1, h2, h3, h4.1, h4.2, rfl⟩))))))
          · rw [ite_eq_right h2, ite_eq_right h3, ite_eq_right h4] at h; cases h
    · rw [ite_eq_right h1] at h; cases h
  | wres p x ok =>
    cases x
    rcases hcl : c.cl p with _ | ⟨o, s⟩ | ⟨o, s, ⟨y⟩ | ⟨y, n⟩⟩ <;> rcases ok with _ | _ <;>
      simp only [laStep, hcl, reduceCtorEq] at h
    simp only [Option.some.injEq] at h; subst h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨p, y, n, o, s, rfl, hcl, rfl⟩))))))

instance laDecEqResp : DecidableEq setObj.Resp := inferInstanceAs (DecidableEq Bool)

/-! ## The invariant -/

/-- The operation of a client state. -/
def CSt.op? : CSt → Option SetOp
  | .idle => none
  | .run o _ => some o
  | .pend o _ _ => some o

@[simp] lemma CSt.op?_idle : CSt.idle.op? = none := rfl
@[simp] lemma CSt.op?_run (o : SetOp) (s : St) : (CSt.run o s).op? = some o := rfl
@[simp] lemma CSt.op?_pend (o : SetOp) (s : St) (pd : Pend) : (CSt.pend o s pd).op? = some o := rfl

/-- Status of `p` for the linearization-point checker: readers are linearized at the
acquisition of the lock, writers at their response. -/
def LACfg.lpSt (c : LACfg) (p : ℕ) : LPStatus setObj :=
  match (c.cl p).op? with
  | none => .idle
  | some o => if p ∈ c.rd then .linearized (setδ c.q o).2 else .pending o

/-- The configuration of a sequential execution of `LL` in which `p` is in client state `x`. -/
def seqCfgOf (m : Mem) (p : ℕ) : CSt → SCfg ℕ
  | .idle => ⟨m, none, none⟩
  | .run o s => ⟨m, some (p, o, s), none⟩
  | .pend o s pd => ⟨m, some (p, o, s), some pd⟩

/-- The pending read or write of a client state. -/
def pendOf : CSt → Option Pend
  | .pend _ _ pd => some pd
  | _ => none

/-- The invariant of `I_LA` (relating a history `H` to the configuration `c` reached by it). -/
structure LAInv (H : LHist ℕ) (c : LACfg) : Prop where
  cl : ∀ p, c.cl p = clientSt H p
  used : ∀ y, y ∈ c.used ↔ ∃ e ∈ H, Ev.mentions y e = true
  alloc : ∀ y, c.mem y ≠ none → y = headL ∨ y = tailL ∨ y ∈ c.used
  noAbort : ∀ e ∈ H, e.isAbort = false
  pendRd : ∀ p o s y, c.cl p = .pend o s (.rd y) → act o s = .read y
  pendWr : ∀ p o s y n, c.cl p = .pend o s (.wr y n) →
    (act o s = .write y n ∨ (act o s = .alloc n ∧ c.mem y = none)) ∧ y ∈ c.used
  wrRd : ∀ w, c.wr = some w → c.rd = ∅
  nonHolder : ∀ p, ¬ c.holds p →
    c.cl p = .idle ∨ ∃ o, c.cl p = .run o .start ∨ c.cl p = .pend o .start (.rd headL)
  holder : ∀ p o s, c.holds p → (c.cl p = .run o s ∨ ∃ pd, c.cl p = .pend o s pd) →
    (∃ zs : List ℤ, zs.Pairwise (· < ·) ∧ zs.toFinset = c.q ∧ LLI zs o c.mem s) ∧
    (p ∈ c.rd → (setδ c.q o).1 = c.q)
  holderBusy : ∀ p, c.holds p → c.cl p ≠ .idle
  rep : c.wr = none → Rep c.mem c.q
  procs : ∀ p, c.cl p ≠ .idle → p ∈ c.procs
  lin : ∃ ann : List (LPLabel ℕ setObj),
    lpRun (setObj.init, fun _ => .idle) ann = some (c.q, c.lpSt) ∧
    ann.filterMap LPLabel.erase = HerlihyWing.ofHist (hl H)
  log : ∃ log : LHist ℕ, (c.wr = none → seqRun scfg0 log = some ⟨c.mem, none, none⟩) ∧
    ∀ p, c.holds p → seqRun scfg0 (log ++ curOp H p) = some (seqCfgOf c.mem p (c.cl p))
  nonHolderOp : ∀ p o, ¬ c.holds p →
    (c.cl p = .run o .start → curOp H p = [.inv p () o]) ∧
    (c.cl p = .pend o .start (.rd headL) → curOp H p = [.inv p () o, .rinv p () headL])
  opsNe : ∀ p, c.cl p ≠ .idle → opsP H p ≠ []
  done : ∀ p k, k < (opsP H p).length → (k + 1 < (opsP H p).length ∨ c.cl p = .idle) →
    ∃ S₀, S₀ ++ (opsP H p).getD k [] ∈ (SigLL : Set (LHist ℕ))
  hon : honRun hcfg0 H = some ⟨c.mem, fun p => pendOf (c.cl p)⟩

/-! ## Auxiliary lemmas -/

@[simp] lemma LACfg.adv_mem (c : LACfg) (e : LEv ℕ) : (c.adv e).mem = c.mem := rfl
@[simp] lemma LACfg.adv_rd (c : LACfg) (e : LEv ℕ) : (c.adv e).rd = c.rd := rfl
@[simp] lemma LACfg.adv_wr (c : LACfg) (e : LEv ℕ) : (c.adv e).wr = c.wr := rfl
@[simp] lemma LACfg.adv_q (c : LACfg) (e : LEv ℕ) : (c.adv e).q = c.q := rfl
@[simp] lemma LACfg.adv_used (c : LACfg) (e : LEv ℕ) :
    (c.adv e).used = c.used ∪ e.locs.toFinset := rfl
@[simp] lemma LACfg.adv_procs (c : LACfg) (e : LEv ℕ) :
    (c.adv e).procs = insert e.proc c.procs := rfl
@[simp] lemma LACfg.adv_cl (c : LACfg) (e : LEv ℕ) :
    (c.adv e).cl = Function.update c.cl e.proc (cstep (c.cl e.proc) e) := rfl

lemma modifyLast_getD {α : Type*} (f : α → α) (L : List α) (k : ℕ) (d : α)
    (hk : k + 1 < L.length) : (L.modifyLast f).getD k d = L.getD k d := by
  rcases List.eq_nil_or_concat L with rfl | ⟨L', x, rfl⟩
  · simp at hk
  · rw [List.concat_eq_append, List.modifyLast_concat]
    rw [List.concat_eq_append, List.length_append, List.length_singleton] at hk
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]

lemma modifyLast_length {α : Type*} (f : α → α) (L : List α) :
    (L.modifyLast f).length = L.length := by
  rcases List.eq_nil_or_concat L with rfl | ⟨L', x, rfl⟩
  · rfl
  · rw [List.concat_eq_append, List.modifyLast_concat]; simp

lemma opsP_append_other (H : LHist ℕ) (e : LEv ℕ) {q : ℕ} (hq : e.proc ≠ q) :
    opsP (H ++ [e]) q = opsP H q := by
  rw [opsP_append]; simp [hq]

lemma curOp_append_other (H : LHist ℕ) (e : LEv ℕ) {q : ℕ} (hq : e.proc ≠ q) :
    curOp (H ++ [e]) q = curOp H q := by
  unfold curOp; rw [opsP_append_other _ _ hq]

lemma opsP_append_inv' (H : LHist ℕ) (e : LEv ℕ) (he : e.isInv = true) :
    opsP (H ++ [e]) e.proc = opsP H e.proc ++ [[e]] := by
  rw [opsP_append]; simp [he]

lemma opsP_append_non (H : LHist ℕ) (e : LEv ℕ) (he : e.isInv = false) :
    opsP (H ++ [e]) e.proc = (opsP H e.proc).modifyLast (· ++ [e]) := by
  rw [opsP_append]; simp [he]

lemma curOp_append_non (H : LHist ℕ) (e : LEv ℕ) (he : e.isInv = false)
    (hne : opsP H e.proc ≠ []) : curOp (H ++ [e]) e.proc = curOp H e.proc ++ [e] := by
  unfold curOp; rw [opsP_append_non _ _ he]
  rcases List.eq_nil_or_concat (opsP H e.proc) with h | ⟨L', x, h⟩
  · exact absurd h hne
  · rw [h, List.concat_eq_append, List.modifyLast_concat]; simp

lemma clientSt_append_self (H : LHist ℕ) (e : LEv ℕ) :
    clientSt (H ++ [e]) e.proc = cstep (clientSt H e.proc) e := by
  rw [clientSt_append]; simp

lemma clientSt_append_other (H : LHist ℕ) (e : LEv ℕ) {q : ℕ} (hq : e.proc ≠ q) :
    clientSt (H ++ [e]) q = clientSt H q := by
  rw [clientSt_append]; simp [hq]

lemma opsP_nil (p : ℕ) : opsP ([] : LHist ℕ) p = [] := rfl

/-- The common bookkeeping of all steps. -/
lemma laStep_basic {c c' : LACfg} {e : LEv ℕ} (h : laStep c e = some c') :
    c'.cl = Function.update c.cl e.proc (cstep (c.cl e.proc) e) ∧
    c'.used = c.used ∪ e.locs.toFinset ∧ c'.procs = insert e.proc c.procs ∧
    e.isAbort = false := by
  rcases laStep_some h with ⟨p, o, rfl, -, rfl⟩ | ⟨p, y, o, s, rfl, -, -, rfl⟩ |
    ⟨p, y, n, o, s, rfl, -, -, rfl⟩ | ⟨p, r, o, s, rfl, -, -, rfl⟩ |
    ⟨p, n, o, s, y, rfl, -, -, -, rfl⟩ | ⟨p, n, o, s, y, rfl, -, -, -, -, -, rfl⟩ |
    ⟨p, n, o, s, y, rfl, -, -, -, -, -, -, rfl⟩ | ⟨p, y, n, o, s, rfl, -, rfl⟩ <;>
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The invariant holds initially -/

lemma rep_mem0 : Rep mem0 ∅ :=
  ⟨[], by simp, by simp, tailL, tailL, ⟨tailL, by simp [mem0, headL, tailL], rfl⟩,
    by simp [mem0, headL, tailL]⟩

lemma LAInv.init : LAInv [] LACfg.init where
  cl _ := rfl
  used _ := by simp [LACfg.init]
  alloc y hy := by
    simp only [LACfg.init, mem0, ne_eq] at hy
    split_ifs at hy with h1 h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact absurd rfl hy
  noAbort := by simp
  pendRd := by simp [LACfg.init]
  pendWr := by simp [LACfg.init]
  wrRd := by simp [LACfg.init]
  nonHolder _ _ := Or.inl rfl
  holder := by simp [LACfg.init, LACfg.holds]
  holderBusy := by simp [LACfg.init, LACfg.holds]
  rep _ := rep_mem0
  procs := by simp [LACfg.init]
  lin := ⟨[], rfl, rfl⟩
  log := ⟨[], fun _ => rfl, by simp [LACfg.init, LACfg.holds]⟩
  nonHolderOp := by simp [LACfg.init]
  opsNe := by simp [LACfg.init]
  done := by simp [opsP_nil]
  hon := rfl

/-! ## Consequences of the invariant -/

namespace LAInv

variable {H : LHist ℕ} {c : LACfg}

lemma holds_of_ne_start (hI : LAInv H c) {p : ℕ} {o : SetOp} {s : St}
    (hcl : c.cl p = .run o s ∨ ∃ pd, c.cl p = .pend o s pd) (hs : s ≠ .start) : c.holds p := by
  by_contra hh
  rcases hI.nonHolder p hh with h | ⟨o', h | h⟩ <;> rcases hcl with h' | ⟨pd, h'⟩ <;>
    rw [h'] at h <;> cases h <;> exact hs rfl

lemma notHolder_of_idle (hI : LAInv H c) {p : ℕ} (h : c.cl p = .idle) : ¬ c.holds p :=
  fun hh => hI.holderBusy p hh h

lemma notReader_of_idle (hI : LAInv H c) {p : ℕ} (h : c.cl p = .idle) : p ∉ c.rd :=
  fun hh => hI.holderBusy p (Or.inl hh) h

/-- Only the writer writes. -/
lemma writer_of_act (hI : LAInv H c) {p : ℕ} {o : SetOp} {s : St}
    (hcl : c.cl p = .run o s ∨ ∃ pd, c.cl p = .pend o s pd)
    (ha : (∃ y n, act o s = .write y n) ∨ (∃ n, act o s = .alloc n)) : c.wr = some p := by
  have hs : s ≠ .start := by
    rintro rfl; rcases ha with ⟨y, n, h⟩ | ⟨n, h⟩ <;> simp [act] at h
  have hh := hI.holds_of_ne_start hcl hs
  rcases hh with hr | hw
  · exfalso
    obtain ⟨⟨zs, hzs, hq, hL⟩, hro⟩ := hI.holder p o s (Or.inl hr) hcl
    exact hL.readOnly ha (by rw [hq]; exact hro hr)
  · exact hw

lemma writer_of_pendWr (hI : LAInv H c) {p : ℕ} {o : SetOp} {s : St} {y : Loc} {n : NodeV}
    (hcl : c.cl p = .pend o s (.wr y n)) : c.wr = some p := by
  refine hI.writer_of_act (Or.inr ⟨_, hcl⟩) ?_
  rcases (hI.pendWr p o s y n hcl).1 with h | h
  · exact Or.inl ⟨y, n, h⟩
  · exact Or.inr ⟨n, h.1⟩

lemma holds_iff_writer (hI : LAInv H c) {p w : ℕ} (hw : c.wr = some w) : c.holds p ↔ p = w := by
  unfold LACfg.holds; rw [hI.wrRd w hw, hw]; simp [eq_comm]

end LAInv

/-! ## Preservation of the invariant -/

section Step

variable {H : LHist ℕ} {c c' : LACfg} {e : LEv ℕ}

lemma step_cl (hI : LAInv H c)
    (hcl' : c'.cl = Function.update c.cl e.proc (cstep (c.cl e.proc) e)) :
    ∀ q, c'.cl q = clientSt (H ++ [e]) q := by
  intro q; rw [hcl', clientSt_append]
  by_cases hq : e.proc = q
  · subst hq; simp [hI.cl]
  · simp [Function.update_of_ne (Ne.symm hq), hq, hI.cl]

lemma step_used (hI : LAInv H c) (h : c'.used = c.used ∪ e.locs.toFinset) :
    ∀ y, y ∈ c'.used ↔ ∃ e' ∈ H ++ [e], Ev.mentions y e' = true := by
  intro y; rw [h, Finset.mem_union, hI.used, List.mem_toFinset, ← Ev.mentions_iff]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro (⟨e', h1, h2⟩ | h)
    · exact ⟨e', Or.inl h1, h2⟩
    · exact ⟨e, Or.inr rfl, h⟩
  · rintro ⟨e', h1 | rfl, h2⟩
    · exact Or.inl ⟨e', h1, h2⟩
    · exact Or.inr h2

lemma step_noAbort (hI : LAInv H c) (he : e.isAbort = false) :
    ∀ e' ∈ H ++ [e], e'.isAbort = false := by
  intro e' h; simp only [List.mem_append, List.mem_singleton] at h
  rcases h with h | rfl
  · exact hI.noAbort e' h
  · exact he

lemma step_procs (hI : LAInv H c)
    (hcl' : c'.cl = Function.update c.cl e.proc (cstep (c.cl e.proc) e))
    (hpr : c'.procs = insert e.proc c.procs) : ∀ q, c'.cl q ≠ .idle → q ∈ c'.procs := by
  intro q hq; rw [hpr, Finset.mem_insert]
  by_cases h : q = e.proc
  · exact Or.inl h
  · rw [hcl', Function.update_of_ne h] at hq; exact Or.inr (hI.procs q hq)

lemma step_alloc_same (hI : LAInv H c) (hm : c'.mem = c.mem) (hu : c.used ⊆ c'.used) :
    ∀ y, c'.mem y ≠ none → y = headL ∨ y = tailL ∨ y ∈ c'.used := by
  intro y hy; rw [hm] at hy
  exact (hI.alloc y hy).imp_right (Or.imp_right (fun h => hu h))

lemma hl_step (hI : LAInv H c) (he : e.isAbort = false) :
    hl (H ++ [e]) = hl H ++ (toHW e).toList := hl_concat H e (step_noAbort hI he)

/-- `done` for a step of `p = e.proc` that is not an invocation. -/
lemma step_done_non (hI : LAInv H c) (he : e.isInv = false)
    (hne : opsP H e.proc ≠ [])
    (hcl' : ∀ q, q ≠ e.proc → c'.cl q = c.cl q)
    (hlast : c'.cl e.proc = .idle → ∃ S₀, S₀ ++ (curOp H e.proc ++ [e]) ∈ (SigLL : Set (LHist ℕ))) :
    ∀ q k, k < (opsP (H ++ [e]) q).length →
      (k + 1 < (opsP (H ++ [e]) q).length ∨ c'.cl q = .idle) →
      ∃ S₀, S₀ ++ (opsP (H ++ [e]) q).getD k [] ∈ (SigLL : Set (LHist ℕ)) := by
  intro q k hk hk'
  by_cases hq : q = e.proc
  · subst hq
    rw [opsP_append_non _ _ he] at hk hk' ⊢
    rw [modifyLast_length] at hk hk'
    rcases hk' with hk' | hidle
    · rw [modifyLast_getD _ _ _ _ hk']; exact hI.done _ k hk (Or.inl hk')
    · by_cases hk2 : k + 1 < (opsP H e.proc).length
      · rw [modifyLast_getD _ _ _ _ hk2]; exact hI.done _ k hk (Or.inl hk2)
      · have hk3 : k = (opsP H e.proc).length - 1 := by omega
        obtain ⟨S₀, hS⟩ := hlast hidle
        refine ⟨S₀, ?_⟩
        rcases List.eq_nil_or_concat (opsP H e.proc) with h | ⟨L', x, h⟩
        · exact absurd h hne
        · rw [h, List.concat_eq_append, List.modifyLast_concat]
          rw [h, List.concat_eq_append, List.length_append, List.length_singleton] at hk3
          have : curOp H e.proc = x := by simp [curOp, h]
          rw [hk3, Nat.add_sub_cancel, List.getD_append_right _ _ _ _ le_rfl]
          simpa [this] using hS
  · rw [opsP_append_other _ _ (Ne.symm hq)] at hk hk' ⊢
    rw [hcl' q hq] at hk'
    exact hI.done q k hk hk'

section LP

variable {A : ObjSpec} [DecidableEq A.Resp]

lemma lpRun_snoc {c₀ c₁ c₂ : A.State × (ℕ → LPStatus A)} {l : List (LPLabel ℕ A)}
    {ℓ : LPLabel ℕ A} (h : lpRun c₀ l = some c₁) (h2 : lpStep c₁ ℓ = some c₂) :
    lpRun c₀ (l ++ [ℓ]) = some c₂ := by
  rw [lpRun_append, h]; simp [lpRun, h2]

lemma lpStep_inv {s : A.State} {st : ℕ → LPStatus A} {p : ℕ} {o : A.Op} (hst : st p = .idle) :
    lpStep (s, st) (.inv p o) = some (s, Function.update st p (.pending o)) := by
  simp [lpStep, hst]

lemma lpStep_lin {s : A.State} {st : ℕ → LPStatus A} {p : ℕ} {o : A.Op}
    (hst : st p = .pending o) :
    lpStep (s, st) (.lin p) =
      some ((A.δ s o).1, Function.update st p (.linearized (A.δ s o).2)) := by
  simp [lpStep, hst]

lemma lpStep_ret {s : A.State} {st : ℕ → LPStatus A} {p : ℕ} {r : A.Resp}
    (hst : st p = .linearized r) :
    lpStep (s, st) (.ret p r) = some (s, Function.update st p .idle) := by
  simp [lpStep, hst]

end LP

/-- The labels of the high-level history. -/
abbrev hlLab (H : LHist ℕ) : List (Label ℕ setObj) := HerlihyWing.ofHist (A := setObj) (hl H)

lemma hlLab_concat (H : LHist ℕ) (e : LEv ℕ) (h : ∀ e' ∈ H ++ [e], e'.isAbort = false) :
    hlLab (H ++ [e]) = hlLab H ++ ((toHW e).map (HerlihyWing.eventLabel (A := setObj))).toList := by
  unfold hlLab HerlihyWing.ofHist
  erw [hl_concat H e h]
  exact List.map_append.trans (by cases toHW e <;> rfl)

lemma lpSt_eq_of (c c' : LACfg) (q : ℕ) (hcl : (c'.cl q).op? = (c.cl q).op?)
    (hrd : q ∈ c'.rd ↔ q ∈ c.rd) (hq : c'.q = c.q) : c'.lpSt q = c.lpSt q := by
  unfold LACfg.lpSt; rw [hcl, hq]
  by_cases h : q ∈ c.rd <;> simp [h, hrd]

lemma lpSt_eq_of_rdq (c c' : LACfg) (hcl : ∀ q, (c'.cl q).op? = (c.cl q).op?)
    (hrd : c'.rd = c.rd) (hq : c'.q = c.q) : c'.lpSt = c.lpSt := by
  funext q; exact lpSt_eq_of c c' q (hcl q) (by rw [hrd]) hq

/-- `lin` for a step that changes neither the operations, the readers, the set, nor the
high-level history. -/
lemma step_lin_same (hI : LAInv H c) (he : e.isAbort = false) (hhw : toHW e = none)
    (hcl : ∀ q, (c'.cl q).op? = (c.cl q).op?) (hrd : c'.rd = c.rd) (hq : c'.q = c.q) :
    ∃ ann : List (LPLabel ℕ setObj),
      lpRun (setObj.init, fun _ => .idle) ann = some (c'.q, c'.lpSt) ∧
      ann.filterMap LPLabel.erase = HerlihyWing.ofHist (hl (H ++ [e])) := by
  obtain ⟨ann, hrun, herase⟩ := hI.lin
  refine ⟨ann, ?_, ?_⟩
  · rw [hrun, hq, lpSt_eq_of_rdq c c' hcl hrd hq]
  · rw [herase]
    have := hlLab_concat H e (step_noAbort hI he)
    rw [hhw] at this
    exact (this.trans (List.append_nil _)).symm

lemma hon_step (hI : LAInv H c)
    (h : honStep (⟨c.mem, fun q => pendOf (c.cl q)⟩ : HCfg ℕ) e =
      some ⟨c'.mem, fun q => pendOf (c'.cl q)⟩) :
    honRun hcfg0 (H ++ [e]) = some ⟨c'.mem, fun q => pendOf (c'.cl q)⟩ := by
  rw [honRun_concat, hI.hon, Option.bind_some, h]

lemma log_step_seq (log cur : LHist ℕ) (e : LEv ℕ) {x y : SCfg ℕ}
    (h : seqRun scfg0 (log ++ cur) = some x) (h2 : seqStep x e = some y) :
    seqRun scfg0 (log ++ (cur ++ [e])) = some y := by
  rw [← List.append_assoc, seqRun_concat, h, Option.bind_some, h2]

lemma seqStep_cfgOf_rinv (m : Mem) (p : ℕ) (o : SetOp) (s : St) (y : Loc)
    (ha : act o s = .read y) :
    seqStep (seqCfgOf m p (.run o s)) (.rinv p () y) = some (seqCfgOf m p (.pend o s (.rd y))) := by
  simp [seqStep, seqCfgOf, ha]

lemma opsP_append_self (H : LHist ℕ) (e : LEv ℕ) {p : ℕ} (hp : e.proc = p) :
    opsP (H ++ [e]) p =
      if e.isInv then opsP H p ++ [[e]] else (opsP H p).modifyLast (· ++ [e]) := by
  rw [opsP_append]; simp [hp]

/-- The invariant after an invocation. -/
lemma step_inv (hI : LAInv H c) {p : ℕ} {o : SetOp} (hcl : c.cl p = .idle) :
    LAInv (H ++ [.inv p () o]) (c.adv (.inv p () o)) := by
  have hcl' : (c.adv (.inv p () o)).cl = Function.update c.cl p (.run o .start) := by
    simp [cstep]
  have hnh := hI.notHolder_of_idle hcl
  have hnr := hI.notReader_of_idle hcl
  have hother : ∀ q, q ≠ p → (c.adv (.inv p () o)).cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hops : opsP (H ++ [.inv p () o]) p = opsP H p ++ [[.inv p () o]] := by
    rw [opsP_append_self H (.inv p () o) (p := p) rfl]; rfl
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := step_alloc_same hI rfl Finset.subset_union_left
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := hI.wrRd, nonHolder := ?_, holder := ?_,
      holderBusy := ?_, rep := hI.rep, procs := step_procs hI rfl rfl, lin := ?_, log := ?_,
      nonHolderOp := ?_, opsNe := ?_, done := ?_, hon := ?_ }
  · intro q o' s y h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h; exact hI.pendRd q o' s y h
  · intro q o' s y n h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h
      exact ⟨(hI.pendWr q o' s y n h).1, Finset.mem_union_left _ (hI.pendWr q o' s y n h).2⟩
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq]; exact hI.nonHolder q hq'
  · intro q o' s hq' h
    have hq : q ≠ p := fun h => hnh (h ▸ hq')
    rw [hother q hq] at h; exact hI.holder q o' s hq' h
  · intro q hq'
    have hq : q ≠ p := fun h => hnh (h ▸ hq')
    rw [hother q hq]; exact hI.holderBusy q hq'
  · obtain ⟨ann, hrun, herase⟩ := hI.lin
    refine ⟨ann ++ [.inv p o], ?_, ?_⟩
    · have hst : c.lpSt p = .idle := by simp [LACfg.lpSt, hcl]
      refine (lpRun_snoc hrun (lpStep_inv (o := o) hst)).trans ?_
      congr 2
      funext q
      by_cases hq : q = p
      · subst hq; simp [LACfg.lpSt, hnr, cstep]
      · rw [Function.update_of_ne hq]
        exact (lpSt_eq_of c (c.adv (.inv p () o)) q (by rw [hother q hq]) Iff.rfl rfl).symm
    · rw [List.filterMap_append, herase]
      exact (hlLab_concat H _ (step_noAbort (e := .inv p () o) hI rfl)).symm
  · obtain ⟨log, h1, h2⟩ := hI.log
    refine ⟨log, h1, fun q hq' => ?_⟩
    have hq : q ≠ p := fun h => hnh (h ▸ hq')
    rw [curOp_append_other _ _ (Ne.symm hq), hother q hq]
    exact h2 q hq'
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq
      rw [hcl']
      refine ⟨fun h => ?_, fun h => by simp at h⟩
      simp only [Function.update_self, CSt.run.injEq, and_true] at h; subst h
      simp [curOp, hops]
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]
      exact hI.nonHolderOp q o' hq'
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hops]; simp
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · intro q k hk hk'
    by_cases hq : q = p
    · subst hq
      rw [hops] at hk hk' ⊢
      rw [hcl'] at hk'
      simp only [List.length_append, List.length_singleton, Function.update_self,
        reduceCtorEq, or_false] at hk hk'
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hI.done _ k (by omega) (Or.inr hcl)
    · rw [opsP_append_other _ _ (Ne.symm hq)] at hk hk' ⊢
      rw [hother q hq] at hk'
      exact hI.done q k hk hk'
  · rw [honRun_concat, hI.hon]
    simp only [Option.bind_some, honStep]
    congr 2; funext q
    by_cases hq : q = p
    · subst hq; simp [hcl, pendOf, cstep]
    · rw [hother q hq]

/-- The invariant after a read invocation. -/
lemma step_rinv (hI : LAInv H c) {p : ℕ} {y : Loc} {o : SetOp} {s : St}
    (hcl : c.cl p = .run o s) (ha : act o s = .read y) :
    LAInv (H ++ [.rinv p () y]) (c.adv (.rinv p () y)) := by
  have hcl' : (c.adv (.rinv p () y)).cl = Function.update c.cl p (.pend o s (.rd y)) := by
    simp [cstep, hcl]
  have hother : ∀ q, q ≠ p → (c.adv (.rinv p () y)).cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hne : opsP H p ≠ [] := hI.opsNe p (by rw [hcl]; simp)
  have hcur : curOp (H ++ [.rinv p () y]) p = curOp H p ++ [.rinv p () y] :=
    curOp_append_non H (.rinv p () y) rfl hne
  have hops : opsP (H ++ [.rinv p () y]) p = (opsP H p).modifyLast (· ++ [.rinv p () y]) :=
    opsP_append_non H (.rinv p () y) rfl
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := step_alloc_same hI rfl Finset.subset_union_left
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := hI.wrRd, nonHolder := ?_, holder := ?_,
      holderBusy := ?_, rep := hI.rep, procs := step_procs hI rfl rfl,
      lin := step_lin_same hI rfl rfl ?_ rfl rfl, log := ?_,
      nonHolderOp := ?_, opsNe := ?_, done := ?_, hon := ?_ }
  · intro q o' s' y' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp only [Function.update_self, CSt.pend.injEq,
        Pend.rd.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact ha
    · rw [hother q hq] at h; exact hI.pendRd q o' s' y' h
  · intro q o' s' y' n h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h
      exact ⟨(hI.pendWr q o' s' y' n h).1, Finset.mem_union_left _ (hI.pendWr q o' s' y' n h).2⟩
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']
      rcases hI.nonHolder q hq' with h | ⟨o', h | h⟩ <;> rw [hcl] at h <;> cases h
      simp only [act, Act.read.injEq] at ha; subst ha
      simp
    · rw [hother q hq]; exact hI.nonHolder q hq'
  · intro q o' s' hq' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h
      simp only [Function.update_self, reduceCtorEq, false_or, CSt.pend.injEq] at h
      obtain ⟨pd, rfl, rfl, -⟩ := h
      exact hI.holder q o s hq' (Or.inl hcl)
    · rw [hother q hq] at h; exact hI.holder q o' s' hq' h
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq]; exact hI.holderBusy q hq'
  · intro q; by_cases hq : q = p
    · subst hq; rw [hcl', hcl]; simp
    · rw [hother q hq]
  · obtain ⟨log, h1, h2⟩ := hI.log
    refine ⟨log, h1, fun q hq' => ?_⟩
    by_cases hq : q = p
    · subst hq; rw [hcur, hcl', Function.update_self]
      have := h2 q hq'; rw [hcl] at this
      exact log_step_seq _ _ _ this (seqStep_cfgOf_rinv _ _ _ _ _ ha)
    · rw [curOp_append_other _ _ (Ne.symm hq), hother q hq]; exact h2 q hq'
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']
      refine ⟨fun h => by simp at h, fun h => ?_⟩
      simp only [Function.update_self, CSt.pend.injEq, Pend.rd.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [hcur, (hI.nonHolderOp q o hq').1 hcl]
      rfl
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]; exact hI.nonHolderOp q o' hq'
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hops]; intro h
      rw [← List.length_eq_zero_iff, modifyLast_length, List.length_eq_zero_iff] at h
      exact hne h
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · exact step_done_non hI rfl hne (fun q hq => hother q hq) (fun h => by rw [hcl'] at h; simp at h)
  · refine hon_step hI ?_
    simp only [honStep, Option.some.injEq, HCfg.mk.injEq, LACfg.adv_mem, true_and]
    funext q
    by_cases hq : q = p
    · subst hq; simp [hcl, pendOf, cstep]
    · rw [Function.update_of_ne hq, hother q hq]

/-- The invariant after a write invocation. -/
lemma step_winv (hI : LAInv H c) {p : ℕ} {y : Loc} {n : NodeV} {o : SetOp} {s : St}
    (hcl : c.cl p = .run o s)
    (ha : act o s = .write y n ∨ (act o s = .alloc n ∧ y ≠ headL ∧ y ≠ tailL ∧ y ∉ c.used)) :
    LAInv (H ++ [.winv p () y n]) (c.adv (.winv p () y n)) := by
  have hcl' : (c.adv (.winv p () y n)).cl = Function.update c.cl p (.pend o s (.wr y n)) := by
    simp [cstep, hcl]
  have hother : ∀ q, q ≠ p → (c.adv (.winv p () y n)).cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hne : opsP H p ≠ [] := hI.opsNe p (by rw [hcl]; simp)
  have hcur : curOp (H ++ [.winv p () y n]) p = curOp H p ++ [.winv p () y n] :=
    curOp_append_non H (.winv p () y n) rfl hne
  have hops : opsP (H ++ [.winv p () y n]) p = (opsP H p).modifyLast (· ++ [.winv p () y n]) :=
    opsP_append_non H (.winv p () y n) rfl
  have hw : c.wr = some p := hI.writer_of_act (Or.inl hcl)
    (ha.imp (fun h => ⟨y, n, h⟩) (fun h => ⟨n, h.1⟩))
  have hholds : c.holds p := Or.inr hw
  have ha' : act o s = .write y n ∨ (act o s = .alloc n ∧ c.mem y = none) := by
    refine ha.imp_right (fun h => ⟨h.1, ?_⟩)
    by_contra hy
    rcases hI.alloc y hy with h' | h' | h'
    · exact h.2.1 h'
    · exact h.2.2.1 h'
    · exact h.2.2.2 h'
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := step_alloc_same hI rfl Finset.subset_union_left
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := hI.wrRd, nonHolder := ?_, holder := ?_,
      holderBusy := ?_, rep := hI.rep, procs := step_procs hI rfl rfl,
      lin := step_lin_same hI rfl rfl ?_ rfl rfl, log := ?_,
      nonHolderOp := ?_, opsNe := ?_, done := ?_, hon := ?_ }
  · intro q o' s' y' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h; exact hI.pendRd q o' s' y' h
  · intro q o' s' y' n' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h
      simp only [Function.update_self, CSt.pend.injEq, Pend.wr.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨ha', by simp [Ev.locs]⟩
    · rw [hother q hq] at h
      exact ⟨(hI.pendWr q o' s' y' n' h).1, Finset.mem_union_left _ (hI.pendWr q o' s' y' n' h).2⟩
  · intro q hq'
    by_cases hq : q = p
    · subst hq; exact absurd hholds hq'
    · rw [hother q hq]; exact hI.nonHolder q hq'
  · intro q o' s' hq' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h
      simp only [Function.update_self, reduceCtorEq, false_or, CSt.pend.injEq] at h
      obtain ⟨pd, rfl, rfl, -⟩ := h
      exact hI.holder q o s hq' (Or.inl hcl)
    · rw [hother q hq] at h; exact hI.holder q o' s' hq' h
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq]; exact hI.holderBusy q hq'
  · intro q; by_cases hq : q = p
    · subst hq; rw [hcl', hcl]; simp
    · rw [hother q hq]
  · obtain ⟨log, h1, h2⟩ := hI.log
    refine ⟨log, h1, fun q hq' => ?_⟩
    by_cases hq : q = p
    · subst hq; rw [hcur, hcl', Function.update_self]
      have := h2 q hq'; rw [hcl] at this
      refine log_step_seq _ _ _ this ?_
      simp [seqStep, seqCfgOf, ha']
    · rw [curOp_append_other _ _ (Ne.symm hq), hother q hq]; exact h2 q hq'
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; exact absurd hholds hq'
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]; exact hI.nonHolderOp q o' hq'
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hops]; intro h
      rw [← List.length_eq_zero_iff, modifyLast_length, List.length_eq_zero_iff] at h
      exact hne h
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · exact step_done_non hI rfl hne (fun q hq => hother q hq) (fun h => by rw [hcl'] at h; simp at h)
  · refine hon_step hI ?_
    simp only [honStep, Option.some.injEq, HCfg.mk.injEq, LACfg.adv_mem, true_and]
    funext q
    by_cases hq : q = p
    · subst hq; simp [hcl, pendOf, cstep]
    · rw [Function.update_of_ne hq, hother q hq]

/-- The invariant after a write response. -/
lemma step_wres (hI : LAInv H c) {p : ℕ} {y : Loc} {n : NodeV} {o : SetOp} {s : St}
    (hcl : c.cl p = .pend o s (.wr y n)) :
    LAInv (H ++ [.wres p () true])
      { c.adv (.wres p () true) with mem := Function.update c.mem y (some n) } := by
  set c' : LACfg := { c.adv (.wres p () true) with mem := Function.update c.mem y (some n) }
    with hc'
  have hcl' : c'.cl = Function.update c.cl p (.run o (onWrite s y)) := by
    simp [c', cstep, hcl]
  have hother : ∀ q, q ≠ p → c'.cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hne : opsP H p ≠ [] := hI.opsNe p (by rw [hcl]; simp)
  have hcur : curOp (H ++ [.wres p () true]) p = curOp H p ++ [.wres p () true] :=
    curOp_append_non H (.wres p () true) rfl hne
  have hops : opsP (H ++ [.wres p () true]) p =
      (opsP H p).modifyLast (· ++ [.wres p () true]) :=
    opsP_append_non H (.wres p () true) rfl
  have hw : c.wr = some p := hI.writer_of_pendWr hcl
  have hholds : ∀ q, c'.holds q ↔ q = p := fun q => hI.holds_iff_writer (p := q) hw
  have hrd : c.rd = ∅ := hI.wrRd p hw
  obtain ⟨ha, hyu⟩ := hI.pendWr p o s y n hcl
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := ?_
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := hI.wrRd, nonHolder := ?_, holder := ?_,
      holderBusy := ?_, rep := fun h => by simp [c', hw] at h, procs := step_procs hI rfl rfl,
      lin := step_lin_same hI rfl rfl ?_ rfl rfl, log := ?_,
      nonHolderOp := ?_, opsNe := ?_, done := ?_, hon := ?_ }
  · intro y' hy'
    by_cases hyy : y' = y
    · subst hyy; exact Or.inr (Or.inr (Finset.mem_union_left _ hyu))
    · simp only [c', Function.update_of_ne hyy] at hy'
      exact (hI.alloc y' hy').imp_right (Or.imp_right (Finset.mem_union_left _))
  · intro q o' s' y' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h; exact hI.pendRd q o' s' y' h
  · intro q o' s' y' n' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h
      have := hI.writer_of_pendWr h; rw [hw] at this; cases this; exact absurd rfl hq
  · intro q hq'
    by_cases hq : q = p
    · subst hq; exact absurd ((hholds q).2 rfl) hq'
    · rw [hother q hq]; exact hI.nonHolder q hq'
  · intro q o' s' hq' h
    have hq := (hholds q).1 hq'; subst hq
    rw [hcl'] at h
    simp only [Function.update_self, CSt.run.injEq, reduceCtorEq, exists_false,
      or_false] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨zs, hzs, hq, hL⟩, -⟩ := hI.holder q o s (Or.inr hw) (Or.inr ⟨_, hcl⟩)
    refine ⟨⟨zs, hzs, hq, ?_⟩, fun h => by simp [c', hrd] at h⟩
    rcases ha with ha | ha
    · exact (hL.write ha).1
    · exact (hL.alloc hzs ha.1 ha.2).1
  · intro q hq'
    have hq := (hholds q).1 hq'; subst hq
    rw [hcl']; simp
  · intro q; by_cases hq : q = p
    · subst hq; rw [hcl', hcl]; simp
    · rw [hother q hq]
  · obtain ⟨log, -, h2⟩ := hI.log
    refine ⟨log, fun h => by simp [c', hw] at h, fun q hq' => ?_⟩
    have hq := (hholds q).1 hq'; subst hq
    rw [hcur, hcl', Function.update_self]
    have := h2 q (Or.inr hw); rw [hcl] at this
    refine log_step_seq _ _ _ this ?_
    simp [seqStep, seqCfgOf, onWrite, c']
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; exact absurd ((hholds q).2 rfl) hq'
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]; exact hI.nonHolderOp q o' hq'
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hops]; intro h
      rw [← List.length_eq_zero_iff, modifyLast_length, List.length_eq_zero_iff] at h
      exact hne h
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · exact step_done_non hI rfl hne (fun q hq => hother q hq) (fun h => by rw [hcl'] at h; simp at h)
  · refine hon_step hI ?_
    simp only [honStep, hcl, pendOf, Option.some.injEq, HCfg.mk.injEq, ite_true]
    refine ⟨rfl, ?_⟩
    funext q
    by_cases hq : q = p
    · subst hq; simp [hcl']
    · rw [Function.update_of_ne hq, hother q hq]

/-- The invariant after a read response to a lock holder. -/
lemma step_rres_holder (hI : LAInv H c) {p : ℕ} {n : NodeV} {o : SetOp} {s : St} {y : Loc}
    (hcl : c.cl p = .pend o s (.rd y)) (hm : c.mem y = some n) (hh : c.holds p) :
    LAInv (H ++ [.rres p () (some n)]) (c.adv (.rres p () (some n))) := by
  have hcl' : (c.adv (.rres p () (some n))).cl =
      Function.update c.cl p (.run o (onRead o s y n)) := by
    simp [cstep, hcl]
  have hother : ∀ q, q ≠ p → (c.adv (.rres p () (some n))).cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hne : opsP H p ≠ [] := hI.opsNe p (by rw [hcl]; simp)
  have hcur : curOp (H ++ [.rres p () (some n)]) p = curOp H p ++ [.rres p () (some n)] :=
    curOp_append_non H (.rres p () (some n)) rfl hne
  have hops : opsP (H ++ [.rres p () (some n)]) p =
      (opsP H p).modifyLast (· ++ [.rres p () (some n)]) :=
    opsP_append_non H (.rres p () (some n)) rfl
  have ha := hI.pendRd p o s y hcl
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := step_alloc_same hI rfl Finset.subset_union_left
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := hI.wrRd, nonHolder := ?_, holder := ?_,
      holderBusy := ?_, rep := hI.rep, procs := step_procs hI rfl rfl,
      lin := step_lin_same hI rfl rfl ?_ rfl rfl, log := ?_,
      nonHolderOp := ?_, opsNe := ?_, done := ?_, hon := ?_ }
  · intro q o' s' y' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h; exact hI.pendRd q o' s' y' h
  · intro q o' s' y' n' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h
      exact ⟨(hI.pendWr q o' s' y' n' h).1, Finset.mem_union_left _ (hI.pendWr q o' s' y' n' h).2⟩
  · intro q hq'
    by_cases hq : q = p
    · subst hq; exact absurd hh hq'
    · rw [hother q hq]; exact hI.nonHolder q hq'
  · intro q o' s' hq' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h
      simp only [Function.update_self, CSt.run.injEq, reduceCtorEq, exists_false,
        or_false] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨⟨zs, hzs, hq, hL⟩, hro⟩ := hI.holder q o s hq' (Or.inr ⟨_, hcl⟩)
      exact ⟨⟨zs, hzs, hq, (hL.read hzs ha hm).1⟩, hro⟩
    · rw [hother q hq] at h; exact hI.holder q o' s' hq' h
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq]; exact hI.holderBusy q hq'
  · intro q; by_cases hq : q = p
    · subst hq; rw [hcl', hcl]; simp
    · rw [hother q hq]
  · obtain ⟨log, h1, h2⟩ := hI.log
    refine ⟨log, h1, fun q hq' => ?_⟩
    by_cases hq : q = p
    · subst hq; rw [hcur, hcl', Function.update_self]
      have := h2 q hq'; rw [hcl] at this
      refine log_step_seq _ _ _ this ?_
      simp [seqStep, seqCfgOf, hm]
    · rw [curOp_append_other _ _ (Ne.symm hq), hother q hq]; exact h2 q hq'
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; exact absurd hh hq'
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]; exact hI.nonHolderOp q o' hq'
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hops]; intro h
      rw [← List.length_eq_zero_iff, modifyLast_length, List.length_eq_zero_iff] at h
      exact hne h
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · exact step_done_non hI rfl hne (fun q hq => hother q hq) (fun h => by rw [hcl'] at h; simp at h)
  · refine hon_step hI ?_
    simp only [honStep, hcl, pendOf, hm, Option.some.injEq, HCfg.mk.injEq, LACfg.adv_mem,
      true_and, or_true, ite_true]
    funext q
    by_cases hq : q = p
    · subst hq; simp [hcl, cstep]
    · rw [Function.update_of_ne hq, hother q hq]

/-- Facts about a lock acquisition (the response to the first read of an operation). -/
lemma acquire_facts (hI : LAInv H c) {p : ℕ} {n : NodeV} {o : SetOp} {s : St} {y : Loc}
    (hcl : c.cl p = .pend o s (.rd y)) (hm : c.mem y = some n) (hnh : ¬ c.holds p)
    (hw : c.wr = none) :
    s = .start ∧ y = headL ∧
    (∃ zs : List ℤ, zs.Pairwise (· < ·) ∧ zs.toFinset = c.q ∧
      LLI zs o c.mem (onRead o .start headL n)) ∧
    ∃ log : LHist ℕ, seqRun scfg0 log = some ⟨c.mem, none, none⟩ ∧
      (∀ q, c.holds q → seqRun scfg0 (log ++ curOp H q) = some (seqCfgOf c.mem q (c.cl q))) ∧
      seqRun scfg0 (log ++ (curOp H p ++ [.rres p () (some n)])) =
        some (seqCfgOf c.mem p (.run o (onRead o .start headL n))) := by
  have hst : s = .start ∧ y = headL := by
    rcases hI.nonHolder p hnh with h | ⟨o', h | h⟩ <;> rw [hcl] at h <;> cases h
    exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hst
  refine ⟨rfl, rfl, ?_, ?_⟩
  · obtain ⟨zs, hzs, hq, hch⟩ := hI.rep hw
    exact ⟨zs, hzs, hq, ((LLI.start hch).read hzs (by rfl) hm).1⟩
  · obtain ⟨log, h1, h2⟩ := hI.log
    refine ⟨log, h1 hw, h2, ?_⟩
    rw [(hI.nonHolderOp p o hnh).2 hcl, seqRun_append_la, h1 hw]
    simp [seqRun, seqStep, act, hm, seqCfgOf]

/-- The invariant after a lock acquisition in shared mode. -/
lemma step_acq_reader (hI : LAInv H c) {p : ℕ} {n : NodeV} {o : SetOp} {s : St} {y : Loc}
    (hcl : c.cl p = .pend o s (.rd y)) (hm : c.mem y = some n) (hnh : ¬ c.holds p)
    (hro : (setδ c.q o).1 = c.q) (hw : c.wr = none) :
    LAInv (H ++ [.rres p () (some n)])
      { c.adv (.rres p () (some n)) with rd := insert p c.rd } := by
  obtain ⟨rfl, rfl, ⟨zs, hzs, hzq, hL⟩, log, hlog, hlogh, hlogp⟩ :=
    acquire_facts hI hcl hm hnh hw
  set c' : LACfg := { c.adv (.rres p () (some n)) with rd := insert p c.rd } with hc'
  have hcl' : c'.cl = Function.update c.cl p (.run o (onRead o .start headL n)) := by
    simp [c', cstep, hcl]
  have hother : ∀ q, q ≠ p → c'.cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hne : opsP H p ≠ [] := hI.opsNe p (by rw [hcl]; simp)
  have hcur : curOp (H ++ [.rres p () (some n)]) p = curOp H p ++ [.rres p () (some n)] :=
    curOp_append_non H (.rres p () (some n)) rfl hne
  have hops : opsP (H ++ [.rres p () (some n)]) p =
      (opsP H p).modifyLast (· ++ [.rres p () (some n)]) :=
    opsP_append_non H (.rres p () (some n)) rfl
  have hnr : p ∉ c.rd := fun h => hnh (Or.inl h)
  have hholds : ∀ q, q ≠ p → (c'.holds q ↔ c.holds q) := fun q hq => by
    simp [c', LACfg.holds, hq]
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := step_alloc_same hI rfl Finset.subset_union_left
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := fun w h => by simp [c', hw] at h, nonHolder := ?_,
      holder := ?_, holderBusy := ?_, rep := hI.rep, procs := step_procs hI rfl rfl,
      lin := ?_, log := ?_, nonHolderOp := ?_, opsNe := ?_, done := ?_, hon := ?_ }
  · intro q o' s' y' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h; exact hI.pendRd q o' s' y' h
  · intro q o' s' y' n' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h
      exact ⟨(hI.pendWr q o' s' y' n' h).1, Finset.mem_union_left _ (hI.pendWr q o' s' y' n' h).2⟩
  · intro q hq'
    by_cases hq : q = p
    · subst hq; exact absurd (Or.inl (Finset.mem_insert_self _ _)) hq'
    · rw [hother q hq]; exact hI.nonHolder q ((not_congr (hholds q hq)).1 hq')
  · intro q o' s' hq' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h
      simp only [Function.update_self, CSt.run.injEq, reduceCtorEq, exists_false,
        or_false] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨zs, hzs, hzq, hL⟩, fun _ => hro⟩
    · rw [hother q hq] at h
      have h' := hI.holder q o' s' ((hholds q hq).1 hq') h
      refine ⟨h'.1, fun hr => h'.2 ?_⟩
      simpa [c', hq] using hr
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq]; exact hI.holderBusy q ((hholds q hq).1 hq')
  · obtain ⟨ann, hrun, herase⟩ := hI.lin
    refine ⟨ann ++ [.lin p], ?_, ?_⟩
    · have hst : c.lpSt p = .pending o := by simp [LACfg.lpSt, hcl, hnr]
      refine (lpRun_snoc hrun (lpStep_lin hst)).trans ?_
      have hro' : (setObj.δ c.q o).1 = c.q := hro
      rw [hro']
      congr 2
      funext q
      by_cases hq : q = p
      · subst hq; simp [c', LACfg.lpSt, cstep, hcl]; rfl
      · rw [Function.update_of_ne hq]
        exact (lpSt_eq_of c c' q (by rw [hother q hq]) (by simp [c', hq]) rfl).symm
    · rw [List.filterMap_append, herase]
      have := hlLab_concat H (.rres p () (some n)) (step_noAbort hI rfl)
      exact (List.append_nil _).trans (this.trans (List.append_nil _)).symm
  · refine ⟨log, fun _ => hlog, fun q hq' => ?_⟩
    by_cases hq : q = p
    · subst hq; rw [hcur, hcl', Function.update_self]; exact hlogp
    · rw [curOp_append_other _ _ (Ne.symm hq), hother q hq]
      exact hlogh q ((hholds q hq).1 hq')
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; exact absurd (Or.inl (Finset.mem_insert_self _ _)) hq'
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]
      exact hI.nonHolderOp q o' ((not_congr (hholds q hq)).1 hq')
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hops]; intro h
      rw [← List.length_eq_zero_iff, modifyLast_length, List.length_eq_zero_iff] at h
      exact hne h
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · exact step_done_non hI rfl hne (fun q hq => hother q hq) (fun h => by rw [hcl'] at h; simp at h)
  · refine hon_step hI ?_
    simp only [honStep, hcl, pendOf, hm, Option.some.injEq, HCfg.mk.injEq,
      or_true, ite_true]
    refine ⟨rfl, ?_⟩
    funext q
    by_cases hq : q = p
    · subst hq; simp [hcl']
    · rw [Function.update_of_ne hq, hother q hq]

/-- The invariant after a lock acquisition in exclusive mode. -/
lemma step_acq_writer (hI : LAInv H c) {p : ℕ} {n : NodeV} {o : SetOp} {s : St} {y : Loc}
    (hcl : c.cl p = .pend o s (.rd y)) (hm : c.mem y = some n) (hnh : ¬ c.holds p)
    (hrd : c.rd = ∅) (hw : c.wr = none) :
    LAInv (H ++ [.rres p () (some n)])
      { c.adv (.rres p () (some n)) with wr := some p } := by
  obtain ⟨rfl, rfl, ⟨zs, hzs, hzq, hL⟩, log, hlog, -, hlogp⟩ :=
    acquire_facts hI hcl hm hnh hw
  set c' : LACfg := { c.adv (.rres p () (some n)) with wr := some p } with hc'
  have hcl' : c'.cl = Function.update c.cl p (.run o (onRead o .start headL n)) := by
    simp [c', cstep, hcl]
  have hother : ∀ q, q ≠ p → c'.cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hne : opsP H p ≠ [] := hI.opsNe p (by rw [hcl]; simp)
  have hcur : curOp (H ++ [.rres p () (some n)]) p = curOp H p ++ [.rres p () (some n)] :=
    curOp_append_non H (.rres p () (some n)) rfl hne
  have hops : opsP (H ++ [.rres p () (some n)]) p =
      (opsP H p).modifyLast (· ++ [.rres p () (some n)]) :=
    opsP_append_non H (.rres p () (some n)) rfl
  have hholds : ∀ q, c'.holds q ↔ q = p := fun q => by
    simp [c', LACfg.holds, hrd, eq_comm]
  have hnh' : ∀ q, q ≠ p → ¬ c.holds q := fun q hq h => by
    rcases h with h | h
    · simp [hrd] at h
    · simp [hw] at h
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := step_alloc_same hI rfl Finset.subset_union_left
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := fun w h => hrd, nonHolder := ?_,
      holder := ?_, holderBusy := ?_, rep := fun h => by simp [c'] at h,
      procs := step_procs hI rfl rfl,
      lin := step_lin_same hI rfl rfl ?_ rfl rfl, log := ?_, nonHolderOp := ?_, opsNe := ?_,
      done := ?_, hon := ?_ }
  · intro q o' s' y' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h; exact hI.pendRd q o' s' y' h
  · intro q o' s' y' n' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h
      exact ⟨(hI.pendWr q o' s' y' n' h).1, Finset.mem_union_left _ (hI.pendWr q o' s' y' n' h).2⟩
  · intro q hq'
    by_cases hq : q = p
    · subst hq; exact absurd ((hholds q).2 rfl) hq'
    · rw [hother q hq]; exact hI.nonHolder q (hnh' q hq)
  · intro q o' s' hq' h
    have hq := (hholds q).1 hq'; subst hq
    rw [hcl'] at h
    simp only [Function.update_self, CSt.run.injEq, reduceCtorEq, exists_false,
      or_false] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨zs, hzs, hzq, hL⟩, fun h => by simp [c', hrd] at h⟩
  · intro q hq'
    have hq := (hholds q).1 hq'; subst hq
    rw [hcl']; simp
  · intro q; by_cases hq : q = p
    · subst hq; rw [hcl', hcl]; simp
    · rw [hother q hq]
  · refine ⟨log, fun h => by simp [c'] at h, fun q hq' => ?_⟩
    have hq := (hholds q).1 hq'; subst hq
    rw [hcur, hcl', Function.update_self]; exact hlogp
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; exact absurd ((hholds q).2 rfl) hq'
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]
      exact hI.nonHolderOp q o' (hnh' q hq)
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hops]; intro h
      rw [← List.length_eq_zero_iff, modifyLast_length, List.length_eq_zero_iff] at h
      exact hne h
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · exact step_done_non hI rfl hne (fun q hq => hother q hq) (fun h => by rw [hcl'] at h; simp at h)
  · refine hon_step hI ?_
    simp only [honStep, hcl, pendOf, hm, Option.some.injEq, HCfg.mk.injEq,
      or_true, ite_true]
    refine ⟨rfl, ?_⟩
    funext q
    by_cases hq : q = p
    · subst hq; simp [hcl']
    · rw [Function.update_of_ne hq, hother q hq]

lemma res_facts (hI : LAInv H c) {p : ℕ} {r : Bool} {o : SetOp} {s : St}
    (hcl : c.cl p = .run o s) (ha : act o s = .ret r) :
    s = .done r ∧ c.holds p ∧ Rep c.mem (setδ c.q o).1 ∧ r = (setδ c.q o).2 := by
  have hs : s = .done r := by cases s <;> simp_all [act]
  subst hs
  have hh := hI.holds_of_ne_start (Or.inl hcl) (by simp)
  obtain ⟨⟨zs, hzs, hq, hL⟩, -⟩ := hI.holder p o _ hh (Or.inl hcl)
  rw [← hq]; exact ⟨rfl, hh, hL.done⟩

lemma hon_res (hI : LAInv H c) {c' : LACfg} {p : ℕ} {r : Bool} {o : SetOp} {s : St}
    (hcl : c.cl p = .run o s) (hm : c'.mem = c.mem)
    (hcl' : c'.cl = Function.update c.cl p .idle) :
    honRun hcfg0 (H ++ [.res p () r]) = some ⟨c'.mem, fun q => pendOf (c'.cl q)⟩ := by
  refine hon_step hI ?_
  simp only [honStep, Option.some.injEq, HCfg.mk.injEq, hm, true_and]
  funext q
  by_cases hq : q = p
  · subst hq; simp [hcl', hcl, pendOf]
  · rw [hcl', Function.update_of_ne hq]

/-- The invariant after the response of the writer. -/
lemma step_res_writer (hI : LAInv H c) {p : ℕ} {r : Bool} {o : SetOp} {s : St}
    (hcl : c.cl p = .run o s) (ha : act o s = .ret r) (hw : c.wr = some p) :
    LAInv (H ++ [.res p () r])
      { c.adv (.res p () r) with rd := c.rd.erase p, wr := none, q := (setδ c.q o).1 } := by
  obtain ⟨rfl, -, hrep, hr⟩ := res_facts hI hcl ha
  set c' : LACfg :=
    { c.adv (.res p () r) with rd := c.rd.erase p, wr := none, q := (setδ c.q o).1 } with hc'
  have hcl' : c'.cl = Function.update c.cl p .idle := by simp [c', cstep]
  have hother : ∀ q, q ≠ p → c'.cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hne : opsP H p ≠ [] := hI.opsNe p (by rw [hcl]; simp)
  have hrd : c.rd = ∅ := hI.wrRd p hw
  have hrd' : c'.rd = ∅ := by simp [c', hrd]
  have hnh' : ∀ q, ¬ c'.holds q := fun q h => by
    rcases h with h | h
    · simp [hrd'] at h
    · simp [c'] at h
  have hnh : ∀ q, q ≠ p → ¬ c.holds q := fun q hq h => hq ((hI.holds_iff_writer hw).1 h)
  obtain ⟨log, -, h2⟩ := hI.log
  have hlog : seqRun scfg0 (log ++ (curOp H p ++ [.res p () r])) = some ⟨c.mem, none, none⟩ := by
    have := h2 p (Or.inr hw); rw [hcl] at this
    refine log_step_seq _ _ _ this ?_
    simp [seqStep, seqCfgOf, act]
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := step_alloc_same hI rfl Finset.subset_union_left
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := fun w h => by simp [c'] at h, nonHolder := ?_,
      holder := fun q _ _ h => absurd h (hnh' q), holderBusy := fun q h => absurd h (hnh' q),
      rep := fun _ => hrep, procs := step_procs hI rfl rfl,
      lin := ?_, log := ?_, nonHolderOp := ?_, opsNe := ?_, done := ?_,
      hon := hon_res hI hcl rfl hcl' }
  · intro q o' s' y' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h; exact hI.pendRd q o' s' y' h
  · intro q o' s' y' n' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h
      exact ⟨(hI.pendWr q o' s' y' n' h).1, Finset.mem_union_left _ (hI.pendWr q o' s' y' n' h).2⟩
  · intro q _
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq]; exact hI.nonHolder q (hnh q hq)
  · obtain ⟨ann, hrun, herase⟩ := hI.lin
    refine ⟨ann ++ [.lin p] ++ [.ret p r], ?_, ?_⟩
    · have hst : c.lpSt p = .pending o := by simp [LACfg.lpSt, hcl, hrd]
      refine (lpRun_snoc (lpRun_snoc hrun (lpStep_lin hst)) (lpStep_ret (r := r) ?_)).trans ?_
      · simp only [Function.update_self]; rw [hr]; rfl
      · congr 2
        funext q
        by_cases hq : q = p
        · subst hq; simp [c', LACfg.lpSt, cstep]
        · rw [Function.update_of_ne hq, Function.update_of_ne hq]
          simp only [LACfg.lpSt, hother q hq, hrd', hrd, Finset.notMem_empty, ite_false]
    · rw [List.filterMap_append, List.filterMap_append, herase]
      have := hlLab_concat H (.res p () r) (step_noAbort hI rfl)
      refine (?_ : _ = hlLab H ++ _).trans this.symm
      exact congrArg (· ++ _) (List.append_nil _)
  · refine ⟨log ++ (curOp H p ++ [.res p () r]), fun _ => hlog, fun q h => absurd h (hnh' q)⟩
  · intro q o' _
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]; exact hI.nonHolderOp q o' (hnh q hq)
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl'] at hq'; simp at hq'
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · exact step_done_non hI rfl hne (fun q hq => hother q hq)
      (fun _ => ⟨log, by simp [SigLL, hlog]⟩)

/-- The invariant after the response of a reader. -/
lemma step_res_reader (hI : LAInv H c) {p : ℕ} {r : Bool} {o : SetOp} {s : St}
    (hcl : c.cl p = .run o s) (ha : act o s = .ret r) (hrp : p ∈ c.rd) :
    LAInv (H ++ [.res p () r]) { c.adv (.res p () r) with rd := c.rd.erase p } := by
  obtain ⟨rfl, -, -, hr⟩ := res_facts hI hcl ha
  set c' : LACfg := { c.adv (.res p () r) with rd := c.rd.erase p } with hc'
  have hcl' : c'.cl = Function.update c.cl p .idle := by simp [c', cstep]
  have hother : ∀ q, q ≠ p → c'.cl q = c.cl q := fun q hq => by
    rw [hcl', Function.update_of_ne hq]
  have hne : opsP H p ≠ [] := hI.opsNe p (by rw [hcl]; simp)
  have hw : c.wr = none := by
    cases hw : c.wr with
    | none => rfl
    | some w => have := hI.wrRd w hw; simp [this] at hrp
  have hholds : ∀ q, q ≠ p → (c'.holds q ↔ c.holds q) := fun q hq => by
    simp [c', LACfg.holds, hq]
  have hnh : ¬ c'.holds p := by simp [c', LACfg.holds, hw]
  obtain ⟨log, h1, h2⟩ := hI.log
  have hlog : seqRun scfg0 (log ++ (curOp H p ++ [.res p () r])) = some ⟨c.mem, none, none⟩ := by
    have := h2 p (Or.inl hrp); rw [hcl] at this
    refine log_step_seq _ _ _ this ?_
    simp [seqStep, seqCfgOf, act]
  refine
    { cl := step_cl hI rfl
      used := step_used hI rfl
      alloc := step_alloc_same hI rfl Finset.subset_union_left
      noAbort := step_noAbort hI rfl
      pendRd := ?_, pendWr := ?_, wrRd := fun w h => by simp [c', hw] at h, nonHolder := ?_,
      holder := ?_, holderBusy := ?_, rep := hI.rep, procs := step_procs hI rfl rfl,
      lin := ?_, log := ?_, nonHolderOp := ?_, opsNe := ?_, done := ?_,
      hon := hon_res hI hcl rfl hcl' }
  · intro q o' s' y' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h; exact hI.pendRd q o' s' y' h
  · intro q o' s' y' n' h
    by_cases hq : q = p
    · subst hq; rw [hcl'] at h; simp at h
    · rw [hother q hq] at h
      exact ⟨(hI.pendWr q o' s' y' n' h).1, Finset.mem_union_left _ (hI.pendWr q o' s' y' n' h).2⟩
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq]; exact hI.nonHolder q ((not_congr (hholds q hq)).1 hq')
  · intro q o' s' hq' h
    have hq : q ≠ p := fun h => hnh (h ▸ hq')
    rw [hother q hq] at h
    have h' := hI.holder q o' s' ((hholds q hq).1 hq') h
    refine ⟨h'.1, fun hr => h'.2 ?_⟩
    simpa [c', hq] using hr
  · intro q hq'
    have hq : q ≠ p := fun h => hnh (h ▸ hq')
    rw [hother q hq]; exact hI.holderBusy q ((hholds q hq).1 hq')
  · obtain ⟨ann, hrun, herase⟩ := hI.lin
    refine ⟨ann ++ [.ret p r], ?_, ?_⟩
    · have hst : c.lpSt p = .linearized r := by simp [LACfg.lpSt, hcl, hrp, hr]
      refine (lpRun_snoc hrun (lpStep_ret hst)).trans ?_
      congr 2
      funext q
      by_cases hq : q = p
      · subst hq; simp [c', LACfg.lpSt, cstep]
      · rw [Function.update_of_ne hq]
        exact (lpSt_eq_of c c' q (by rw [hother q hq]) (by simp [c', hq]) rfl).symm
    · rw [List.filterMap_append, herase]
      have := hlLab_concat H (.res p () r) (step_noAbort hI rfl)
      exact this.symm
  · refine ⟨log, fun _ => h1 hw, fun q hq' => ?_⟩
    have hq : q ≠ p := fun h => hnh (h ▸ hq')
    rw [curOp_append_other _ _ (Ne.symm hq), hother q hq]
    exact h2 q ((hholds q hq).1 hq')
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; rw [hcl']; simp
    · rw [hother q hq, curOp_append_other _ _ (Ne.symm hq)]
      exact hI.nonHolderOp q o' ((not_congr (hholds q hq)).1 hq')
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hcl'] at hq'; simp at hq'
    · rw [opsP_append_other _ _ (Ne.symm hq)]; rw [hother q hq] at hq'; exact hI.opsNe q hq'
  · exact step_done_non hI rfl hne (fun q hq => hother q hq)
      (fun _ => ⟨log, by simp [SigLL, hlog]⟩)

/-- **The invariant is preserved by every step of `I_LA`.** -/
theorem LAInv.step (hI : LAInv H c) (h : laStep c e = some c') : LAInv (H ++ [e]) c' := by
  rcases laStep_some h with ⟨p, o, rfl, hcl, rfl⟩ | ⟨p, y, o, s, rfl, hcl, ha, rfl⟩ |
    ⟨p, y, n, o, s, rfl, hcl, ha, rfl⟩ | ⟨p, r, o, s, rfl, hcl, ha, rfl⟩ |
    ⟨p, n, o, s, y, rfl, hcl, hm, hh, rfl⟩ | ⟨p, n, o, s, y, rfl, hcl, hm, hh, hro, hw, rfl⟩ |
    ⟨p, n, o, s, y, rfl, hcl, hm, hh, hro, hrd, hw, rfl⟩ | ⟨p, y, n, o, s, rfl, hcl, rfl⟩
  · exact step_inv hI hcl
  · exact step_rinv hI hcl ha
  · exact step_winv hI hcl ha
  · by_cases hw : c.wr = some p
    · simp only [hw, ite_true]; exact step_res_writer hI hcl ha hw
    · have hrp : p ∈ c.rd := (res_facts hI hcl ha).2.1.resolve_right hw
      simp only [hw, ite_false]; exact step_res_reader hI hcl ha hrp
  · exact step_rres_holder hI hcl hm hh
  · exact step_acq_reader hI hcl hm hh hro hw
  · exact step_acq_writer hI hcl hm hh hrd hw
  · exact step_wres hI hcl

end Step

lemma laRun_append (c : LACfg) (H E : LHist ℕ) :
    laRun c (H ++ E) = (laRun c H).bind (fun c' => laRun c' E) := by
  induction H generalizing c with
  | nil => simp [laRun]
  | cons e H ih => simp only [List.cons_append, laRun, ih]; cases laStep c e <;> simp

/-- Every configuration reached by `I_LA` satisfies the invariant. -/
theorem laRun_inv : ∀ (H : LHist ℕ) (c : LACfg), laRun LACfg.init H = some c → LAInv H c := by
  intro H
  induction H using List.reverseRecOn with
  | nil => intro c h; cases h; exact LAInv.init
  | append_singleton H e ih =>
    intro c h
    rw [laRun_concat] at h
    cases hH : laRun LACfg.init H with
    | none => rw [hH] at h; cases h
    | some c₀ => rw [hH, Option.bind_some] at h; exact (ih c₀ hH).step h

lemma mem_I_LA {H : LHist ℕ} : H ∈ I_LA ↔ ∃ c, laRun LACfg.init H = some c := by
  simp only [I_LA, Set.mem_ofPred_eq, Option.isSome_iff_exists]

end Podc.OptimismConcurrency
