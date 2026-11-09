import Papers.PODC2012.OptimismConcurrency.IRM

/-!
# Invariants of `I_RM`

* `RStep.rf_mono`, `RRun.rf_mono`: deletion marks are never removed.
* `RRun.split`: locate an event of the history in an execution.
* `RRun.rd_preserved`: a pending read of `p` stays a pending read of the same object (with the
  same ghost) as long as `p` emits no event.
* `Inv`, `RRun.inv`: the main invariant relating a configuration to the history so far: `rbuf`
  holds the objects of the last two successful reads; `kind` is the last invoked operation; a
  pending read/write is the last event of its process; a read invoked when `r[y]` was set returns
  `⊥`; a `remove` write that passed line 27 has set `r[ℓ']`, where `ℓ'` is the other object of
  `rbuf`.
-/

namespace Podc.OptimismConcurrency

/-! ## Basic lemmas on configurations -/

@[simp] lemma RCfg.setLoc_loc (c : RCfg) (p q : ℕ) (l : RLoc) :
    (c.setLoc p l).loc q = if q = p then l else c.loc q := by
  simp [RCfg.setLoc, Function.update_apply]

@[simp] lemma RCfg.setLoc_rf (c : RCfg) (p : ℕ) (l : RLoc) : (c.setLoc p l).rf = c.rf := rfl
@[simp] lemma RCfg.setLoc_lk (c : RCfg) (p : ℕ) (l : RLoc) : (c.setLoc p l).lk = c.lk := rfl
@[simp] lemma RCfg.setLoc_tvar (c : RCfg) (p : ℕ) (l : RLoc) : (c.setLoc p l).tvar = c.tvar := rfl

@[simp] lemma RCfg.setPc_loc (c : RCfg) (p q : ℕ) (x : Option RPc) :
    (c.setPc p x).loc q = if q = p then { c.loc p with pc := x } else c.loc q := by
  simp [RCfg.setPc]

@[simp] lemma RCfg.setPc_rf (c : RCfg) (p : ℕ) (x : Option RPc) : (c.setPc p x).rf = c.rf := rfl

lemma RStep.rf_mono {c c' : RCfg} {l : Option (LEv ℕ)} (h : RStep c l c') {z : Loc}
    (hz : c.rf z = true) : c'.rf z = true := by
  cases h <;> simp [hz, Function.update_apply] <;> split_ifs <;> simp [hz]

lemma RRun.rf_mono {c c' : RCfg} {L : List (Option (LEv ℕ))} (h : RRun c L c') {z : Loc}
    (hz : c.rf z = true) : c'.rf z = true := by
  induction h with
  | nil => exact hz
  | snoc _ hs ih => exact hs.rf_mono ih

lemma RRun.single {c c' : RCfg} {l : Option (LEv ℕ)} (h : RStep c l c') : RRun c [l] c' := by
  simpa using RRun.snoc RRun.nil h

lemma RRun.eq_of_nil {c c' : RCfg} {L : List (Option (LEv ℕ))} (h : RRun c L c') (hL : L = []) :
    c' = c := by
  induction h with
  | nil => rfl
  | snoc _ _ _ => simp at hL

lemma RRun.step_of_single {c c' : RCfg} {L : List (Option (LEv ℕ))} {l : Option (LEv ℕ)}
    (h : RRun c L c') (hL : L = [l]) : RStep c l c' := by
  induction h with
  | nil => simp at hL
  | @snoc c₁ c₂ L' l' hr hs _ =>
    have hlen := congrArg List.length hL
    simp only [List.length_append, List.length_singleton, Nat.add_eq_right,
      List.length_eq_zero_iff] at hlen
    subst hlen
    simp only [List.nil_append, List.cons.injEq, and_true] at hL
    subst hL
    rw [hr.eq_of_nil rfl] at hs; exact hs

lemma RRun.append {c c₁ c₂ : RCfg} {A B : List (Option (LEv ℕ))} (hA : RRun c A c₁)
    (hB : RRun c₁ B c₂) : RRun c (A ++ B) c₂ := by
  induction hB with
  | nil => simpa using hA
  | snoc _ hs ih => rw [← List.append_assoc]; exact ih.snoc hs

lemma RRun.of_append {c c' : RCfg} {L : List (Option (LEv ℕ))} (h : RRun c L c') :
    ∀ A B, L = A ++ B → ∃ c₁, RRun c A c₁ ∧ RRun c₁ B c' := by
  induction h with
  | nil => intro A B h; obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm; exact ⟨c, .nil, .nil⟩
  | @snoc c₁ c₂ L l hr hs ih =>
    intro A B h
    rcases List.eq_nil_or_concat' B with rfl | ⟨B', b, rfl⟩
    · simp only [List.append_nil] at h; subst h; exact ⟨c₂, hr.snoc hs, .nil⟩
    · rw [← List.append_assoc] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at h2; subst h2
      obtain ⟨c₃, hA, hB⟩ := ih A B' h1
      exact ⟨c₃, hA, hB.snoc hs⟩

/-- Locate an event of the history in an execution. -/
lemma RRun.split {c c' : RCfg} {L : List (Option (LEv ℕ))} (h : RRun c L c')
    {A B : LHist ℕ} {e : LEv ℕ} (hL : L.filterMap id = A ++ e :: B) :
    ∃ L₁ L₂ c₁ c₂, RRun c L₁ c₁ ∧ RStep c₁ (some e) c₂ ∧ RRun c₂ L₂ c' ∧
      L₁.filterMap id = A ∧ L₂.filterMap id = B := by
  obtain ⟨L₁, R, rfl, h1, h2⟩ := List.filterMap_eq_append_iff.1 hL
  obtain ⟨M, x, L₂, rfl, hM, hx, h3⟩ := List.filterMap_eq_cons_iff.1 h2
  obtain ⟨c₁, hr1, hr2⟩ := h.of_append L₁ _ rfl
  obtain ⟨c₀, hr3, hr4⟩ := hr2.of_append (M ++ [x]) L₂ (by simp)
  obtain ⟨c₀', hr5, hr6⟩ := hr3.of_append M [x] rfl
  refine ⟨L₁ ++ M, L₂, c₀', c₀, hr1.append hr5, ?_, hr4, ?_, h3⟩
  · have hx' : x = some e := by simpa using hx
    subst hx'; exact hr6.step_of_single rfl
  · rw [List.filterMap_append, h1]
    have : M.filterMap id = [] := by
      rw [List.filterMap_eq_nil_iff]; intro a ha; simpa using hM a ha
    simp only [List.append_assoc, this, List.nil_append, List.append_nil]

/-- A step that emits no event of `p` keeps a pending read of `p` a pending read of the same
object with the same ghost. -/
lemma RStep.rd_preserved {c c' : RCfg} {l : Option (LEv ℕ)} (h : RStep c l c') {p : ℕ}
    (hl : ∀ e, l = some e → e.proc ≠ p) {y : Loc} {g : Bool} {s : RdSt}
    (hp : (c.loc p).pc = some (.rd y g s)) : ∃ s', (c'.loc p).pc = some (.rd y g s') := by
  cases h
  all_goals
    try simp only [RCfg.setPc_loc, RCfg.setLoc_loc]
    try split_ifs
    all_goals first
      | exact ⟨s, hp⟩
      | (exfalso; subst_vars; exact hl _ rfl rfl)
      | (subst_vars; simp_all)

lemma RRun.rd_preserved {c c' : RCfg} {L : List (Option (LEv ℕ))} (h : RRun c L c') {p : ℕ}
    (hl : ∀ e ∈ L.filterMap id, e.proc ≠ p) {y : Loc} {g : Bool} {s : RdSt}
    (hp : (c.loc p).pc = some (.rd y g s)) : ∃ s', (c'.loc p).pc = some (.rd y g s') := by
  induction h with
  | nil => exact ⟨s, hp⟩
  | @snoc c₁ c₂ L l hr hs ih =>
    obtain ⟨s₁, h₁⟩ := ih (fun e he => hl e (by rw [List.filterMap_append]; exact List.mem_append_left _ he))
    exact hs.rd_preserved (fun e he => hl e (by subst he; simp)) h₁

/-! ## History bookkeeping -/

/-- Events of `p`. -/
def evOf (H : LHist ℕ) (p : ℕ) : LHist ℕ := H.filter (fun e => decide (e.proc = p))

/-- The last event of `p`. -/
def lastEv (H : LHist ℕ) (p : ℕ) : Option (LEv ℕ) := (evOf H p).getLast?

/-- The operation of an invocation. -/
def invOp : LEv ℕ → Option SetOp
  | .inv _ _ o => some o
  | _ => none

/-- The last operation invoked by `p`. -/
def lastInv (H : LHist ℕ) (p : ℕ) : Option SetOp := ((evOf H p).filterMap invOp).getLast?

/-- Bookkeeping of successful reads: pending read object, objects of successful reads (newest
first). -/
def rdStep : Option Loc × List Loc → LEv ℕ → Option Loc × List Loc
  | (_, l), .rinv _ _ y => (some y, l)
  | (some y, l), .rres _ _ (some _) => (none, y :: l)
  | (_, l), .rres _ _ none => (none, l)
  | s, _ => s

/-- Read bookkeeping of `p` after `H`. -/
def rdState (H : LHist ℕ) (p : ℕ) : Option Loc × List Loc := (evOf H p).foldl rdStep (none, [])

/-- Objects of the successful reads of `p`, newest first. -/
def readObjs (H : LHist ℕ) (p : ℕ) : List Loc := (rdState H p).2

lemma evOf_concat (H : LHist ℕ) (e : LEv ℕ) (p : ℕ) :
    evOf (H ++ [e]) p = if e.proc = p then evOf H p ++ [e] else evOf H p := by
  unfold evOf; rw [List.filter_append]; split_ifs with h <;> simp [h]

lemma lastEv_concat (H : LHist ℕ) (e : LEv ℕ) (p : ℕ) :
    lastEv (H ++ [e]) p = if e.proc = p then some e else lastEv H p := by
  unfold lastEv; rw [evOf_concat]; split_ifs <;> simp

lemma lastInv_concat (H : LHist ℕ) (e : LEv ℕ) (p : ℕ) :
    lastInv (H ++ [e]) p = if e.proc = p ∧ (invOp e).isSome then invOp e else lastInv H p := by
  unfold lastInv; rw [evOf_concat]
  by_cases h : e.proc = p
  · cases e <;> simp_all [invOp]
  · simp [h]

lemma rdState_concat (H : LHist ℕ) (e : LEv ℕ) (p : ℕ) :
    rdState (H ++ [e]) p = if e.proc = p then rdStep (rdState H p) e else rdState H p := by
  unfold rdState; rw [evOf_concat]; split_ifs <;> simp

lemma rdState_fst_of_lastEv {H : LHist ℕ} {p : ℕ} {y : Loc}
    (h : lastEv H p = some (.rinv p () y)) : (rdState H p).1 = some y := by
  unfold lastEv at h; unfold rdState
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 h
  rw [hl, List.foldl_append]; simp [rdStep]

/-! ## The invariant -/

/-- Facts about a pending read whose object was marked at the invocation. -/
def RdGood (c : RCfg) (y : Loc) : RdSt → Prop
  | .l11 | .l12 _ | .l13 _ _ => c.rf y = true
  | .l14 _ _ f => f = true
  | .fin _ res => res = none

/-- Facts about a pending `remove` write of `p` to `y`. -/
def RmGood (c : RCfg) (p : ℕ) (y : Loc) : RmSt → Prop
  | .l25 _ z _ | .l27 _ z _ => ∃ w, (c.loc p).rbuf.find? (fun e => decide (e.1 ≠ y)) = some (z, w)
  | .l28 _ z _ | .l29 _ z _ | .l30 _ z _ | .ok z =>
      (∃ w, (c.loc p).rbuf.find? (fun e => decide (e.1 ≠ y)) = some (z, w)) ∧ c.rf z = true
  | _ => True

/-- The main invariant of `I_RM` at process `p`, relating a configuration to the history so far. -/
structure InvAt (c : RCfg) (H : LHist ℕ) (p : ℕ) : Prop where
  rbuf : (c.loc p).rbuf.map Prod.fst = (readObjs H p).take 2
  kind : (c.loc p).kind = lastInv H p
  rd : ∀ y g s, (c.loc p).pc = some (.rd y g s) →
    lastEv H p = some (.rinv p () y) ∧ (g = true → RdGood c y s)
  rm : ∀ y n s, (c.loc p).pc = some (.rm y n s) →
    lastEv H p = some (.winv p () y n) ∧ (∃ v, (c.loc p).kind = some (.remove v)) ∧ RmGood c p y s
  ins : ∀ y n s, (c.loc p).pc = some (.ins y n s) →
    lastEv H p = some (.winv p () y n) ∧ ∀ v, (c.loc p).kind ≠ some (.remove v)
  alc : ∀ y n b, (c.loc p).pc = some (.alc y n b) →
    lastEv H p = some (.winv p () y n) ∧ ∀ v, (c.loc p).kind ≠ some (.remove v)

/-- The main invariant of `I_RM`. -/
def Inv (c : RCfg) (H : LHist ℕ) : Prop := ∀ p, InvAt c H p

lemma inv_init (tv : Loc → NodeV) : Inv (rcfg0 tv) [] := fun p => by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [rcfg0, readObjs, rdState, evOf, lastInv]

lemma RdGood.mono {c c' : RCfg} (hm : ∀ z, c.rf z = true → c'.rf z = true) {y : Loc} {s : RdSt}
    (h : RdGood c y s) : RdGood c' y s := by
  cases s <;> simp_all [RdGood]

lemma RmGood.mono {c c' : RCfg} {p : ℕ} (hm : ∀ z, c.rf z = true → c'.rf z = true)
    (hl : c'.loc p = c.loc p) {y : Loc} {s : RmSt} (h : RmGood c p y s) : RmGood c' p y s := by
  cases s <;> simp_all [RmGood]

/-- The process taking a step; other processes keep their local state. -/
lemma RStep.frame {c c' : RCfg} {l : Option (LEv ℕ)} (h : RStep c l c') :
    ∃ q, (∀ e, l = some e → e.proc = q) ∧ ∀ p, p ≠ q → c'.loc p = c.loc p := by
  cases h with
  | inv q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | res q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | rinv q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | winv q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | r11 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | r12 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | r13 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | r14 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | rret q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m22ok q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m22noz q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m22fail q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m22retry q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m25ok q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m25fail q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m25retry q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m27 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m28 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m29 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | m30 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | mok q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | mfail q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | i35ok q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | i35fail q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | i35retry q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | i37 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | i38 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | iok q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | ifail q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | a1 q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩
  | aok q => exact ⟨q, by simp, fun p hp => by simp [hp]⟩

lemma evOf_toList_ne {H : LHist ℕ} {l : Option (LEv ℕ)} {p q : ℕ}
    (hq : ∀ e, l = some e → e.proc = q) (hp : p ≠ q) : evOf (H ++ l.toList) p = evOf H p := by
  cases l with
  | none => simp
  | some e => rw [Option.toList_some, evOf_concat, if_neg (by rw [hq e rfl]; exact Ne.symm hp)]

lemma InvAt.frame {c c' : RCfg} {H H' : LHist ℕ} {p : ℕ} (h : InvAt c H p)
    (hm : ∀ z, c.rf z = true → c'.rf z = true) (hl : c'.loc p = c.loc p)
    (he : evOf H' p = evOf H p) : InvAt c' H' p := by
  have h1 : lastEv H' p = lastEv H p := by simp [lastEv, he]
  have h2 : lastInv H' p = lastInv H p := by simp [lastInv, he]
  have h3 : readObjs H' p = readObjs H p := by simp [readObjs, rdState, he]
  refine ⟨?_, ?_, fun y g s hp => ?_, fun y n s hp => ?_, fun y n s hp => ?_, fun y n b hp => ?_⟩
  · rw [hl, h3]; exact h.rbuf
  · rw [hl, h2]; exact h.kind
  · rw [hl] at hp; obtain ⟨a, b⟩ := h.rd y g s hp; exact ⟨h1 ▸ a, fun hg => (b hg).mono hm⟩
  · rw [hl] at hp ⊢; obtain ⟨a, b, d⟩ := h.rm y n s hp; exact ⟨h1 ▸ a, b, d.mono hm hl⟩
  · rw [hl] at hp ⊢; obtain ⟨a, b⟩ := h.ins y n s hp; exact ⟨h1 ▸ a, b⟩
  · rw [hl] at hp ⊢; obtain ⟨a, b⟩ := h.alc y n b hp; exact ⟨h1 ▸ a, b⟩

/-- The facts the invariant requires about a pending operation `X` of `p`. -/
def PcOK (c : RCfg) (H : LHist ℕ) (p : ℕ) : RPc → Prop
  | .rd y g s => lastEv H p = some (.rinv p () y) ∧ (g = true → RdGood c y s)
  | .rm y n s => lastEv H p = some (.winv p () y n) ∧ (∃ v, (c.loc p).kind = some (.remove v)) ∧
      RmGood c p y s
  | .ins y n _ => lastEv H p = some (.winv p () y n) ∧ ∀ v, (c.loc p).kind ≠ some (.remove v)
  | .alc y n _ => lastEv H p = some (.winv p () y n) ∧ ∀ v, (c.loc p).kind ≠ some (.remove v)

lemma InvAt.pcOK {c : RCfg} {H : LHist ℕ} {p : ℕ} (h : InvAt c H p) {X : RPc}
    (hX : (c.loc p).pc = some X) : PcOK c H p X := by
  cases X with
  | rd y g s => exact h.rd y g s hX
  | rm y n s => exact h.rm y n s hX
  | ins y n s => exact h.ins y n s hX
  | alc y n b => exact h.alc y n b hX

/-- An internal step of `p` changing only its pending operation. -/
lemma InvAt.of_pc {c c' : RCfg} {H : LHist ℕ} {p : ℕ} (h : InvAt c H p) {X : RPc}
    (hl : c'.loc p = { c.loc p with pc := some X }) (hX : PcOK c' H p X) : InvAt c' H p := by
  refine ⟨?_, ?_, fun y g s hp => ?_, fun y n s hp => ?_, fun y n s hp => ?_, fun y n b hp => ?_⟩
  · rw [hl]; exact h.rbuf
  · rw [hl]; exact h.kind
  all_goals rw [hl] at hp; simp only [Option.some.injEq] at hp; subst hp; exact hX

/-- `p` has no pending operation afterwards. -/
lemma InvAt.of_none {c' : RCfg} {H : LHist ℕ} {p : ℕ}
    (hr : (c'.loc p).rbuf.map Prod.fst = (readObjs H p).take 2)
    (hk : (c'.loc p).kind = lastInv H p) (hn : (c'.loc p).pc = none) : InvAt c' H p :=
  ⟨hr, hk, by simp [hn], by simp [hn], by simp [hn], by simp [hn]⟩

lemma readObjs_concat_ne_rres (H : LHist ℕ) (e : LEv ℕ) (p : ℕ)
    (he : ∀ x v, e ≠ .rres p x v) : readObjs (H ++ [e]) p = readObjs H p := by
  unfold readObjs; rw [rdState_concat]
  split_ifs with h
  · rcases hs : rdState H p with ⟨a, l⟩
    cases e with
    | rres q x v => subst h; exact absurd rfl (he x v)
    | _ => simp [rdStep]
  · rfl

lemma lastInv_concat_ne_inv (H : LHist ℕ) (e : LEv ℕ) (p : ℕ) (he : invOp e = none) :
    lastInv (H ++ [e]) p = lastInv H p := by
  rw [lastInv_concat]; simp [he]

lemma InvAt.mk' {c' : RCfg} {H : LHist ℕ} {p : ℕ}
    (hr : (c'.loc p).rbuf.map Prod.fst = (readObjs H p).take 2)
    (hk : (c'.loc p).kind = lastInv H p)
    (hpc : ∀ X, (c'.loc p).pc = some X → PcOK c' H p X) : InvAt c' H p :=
  ⟨hr, hk, fun y g s hp => hpc _ hp, fun y n s hp => hpc _ hp, fun y n s hp => hpc _ hp,
    fun y n b hp => hpc _ hp⟩

/-- One step preserves the invariant. -/
theorem Inv.step {c c' : RCfg} {H : LHist ℕ} {l : Option (LEv ℕ)} (hI : Inv c H)
    (hs : RStep c l c') : Inv c' (H ++ l.toList) := by
  have hm : ∀ z, c.rf z = true → c'.rf z = true := fun z hz => hs.rf_mono hz
  intro p
  cases hs with
  | inv q o hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.of_none ?_ ?_ (by simp [hpc])
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simp [lastInv_concat, invOp]
  | res q r hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.of_none ?_ ?_ hpc
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simpa [lastInv_concat, invOp] using h.kind
  | rinv q y hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.mk' ?_ ?_ fun X hX => ?_
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simpa [lastInv_concat, invOp] using h.kind
    · simp only [RCfg.setPc_loc, if_true, Option.some.injEq] at hX; subst hX
      simp [PcOK, lastEv_concat, RdGood]
  | winv q y n hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.mk' ?_ ?_ fun X hX => ?_
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simpa [lastInv_concat, invOp] using h.kind
    · simp only [RCfg.setPc_loc, if_true, Option.some.injEq] at hX; subst hX
      unfold wstart
      rcases hk : (c.loc p).kind with _ | ⟨v | v | v⟩ <;>
        rcases (c.loc p).rbuf.lookup y with _ | ver <;>
        simp [PcOK, lastEv_concat, RmGood, hk]
  | rret q y g v1 res hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨hlast, -⟩ := h.rd y g _ hpc
    have h1 := rdState_fst_of_lastEv hlast
    refine InvAt.of_none ?_ ?_ (by simp)
    · have hr := h.rbuf
      unfold readObjs at hr ⊢
      simp only [Option.toList_some, rdState_concat, Ev.proc_rres, if_true]
      rcases hst : rdState H p with ⟨a, L⟩
      rw [hst] at h1 hr; simp only at h1; subst h1
      cases res with
      | none => simpa [rdStep] using hr
      | some n =>
        simp only [RCfg.setLoc_loc, if_true, Option.isSome_some, rdStep, List.map_cons,
          List.map_take, hr, List.take_succ_cons, List.take_take]
        rfl
    · simpa [lastInv_concat, invOp] using h.kind
  | r11 q y g hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.rd y g _ hpc
    refine InvAt.of_pc h (X := .rd y g (.l12 (c.lk y).1)) (by simp) ⟨h1, fun hg => by simpa [RdGood] using h2 hg⟩
  | r12 q y g v1 hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.rd y g _ hpc
    refine InvAt.of_pc h (X := .rd y g (.l13 v1 (c.tvar y))) (by simp) ⟨h1, fun hg => by simpa [RdGood] using h2 hg⟩
  | r13 q y g v1 val hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.rd y g _ hpc
    refine InvAt.of_pc h (X := .rd y g (.l14 v1 val (c.rf y))) (by simp) ⟨h1, fun hg => by simpa [RdGood] using h2 hg⟩
  | r14 q y g v1 val f hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.rd y g _ hpc
    refine InvAt.of_pc h (X := .rd y g (.fin v1 (if v1 ≠ (c.lk y).1 ∨ f = true then none else some val)))
      (by simp) ⟨h1, fun hg => ?_⟩
    have := h2 hg; simp only [RdGood] at this ⊢; simp [this]
  | m22ok q y n ver z vz hpc hl hz =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n (.l25 ver z vz)) (by simp) ⟨h1, by simpa using h2, by simpa [RmGood] using ⟨vz, hz⟩⟩
  | m22noz q y n ver hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n .fail) (by simp) ⟨h1, by simpa using h2, by simp [RmGood]⟩
  | m22fail q y n ver hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n .fail) (by simp) ⟨h1, by simpa using h2, by simp [RmGood]⟩
  | m22retry q y n ver hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n (.l22 (c.lk y).1)) (by simp) ⟨h1, by simpa using h2, by simp [RmGood]⟩
  | m25ok q y n ver z vz hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n (.l27 ver z vz)) (by simp) ⟨h1, by simpa using h2, by simpa [RmGood] using h3⟩
  | m25fail q y n ver z vz hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n .fail) (by simp) ⟨h1, by simpa using h2, by simp [RmGood]⟩
  | m25retry q y n ver z vz hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n (.l25 ver z (c.lk z).1)) (by simp) ⟨h1, by simpa using h2, by simpa [RmGood] using h3⟩
  | m27 q y n ver z vz hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n (.l28 ver z vz)) (by simp) ⟨h1, by simpa using h2, ?_⟩
    simp only [RmGood] at h3 ⊢; exact ⟨by simpa using h3, by simp⟩
  | m28 q y n ver z vz hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n (.l29 ver z vz)) (by simp) ⟨h1, by simpa using h2, by simpa [RmGood] using h3⟩
  | m29 q y n ver z vz hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n (.l30 ver z vz)) (by simp) ⟨h1, by simpa using h2, by simpa [RmGood] using h3⟩
  | m30 q y n ver z vz hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2, h3⟩ := h.rm y n _ hpc
    refine InvAt.of_pc h (X := .rm y n (.ok z)) (by simp) ⟨h1, by simpa using h2, by simpa [RmGood] using h3⟩
  | mok q y n z hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.of_none ?_ ?_ (by simp)
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simpa [lastInv_concat, invOp] using h.kind
  | mfail q y n hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.of_none ?_ ?_ (by simp)
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simpa [lastInv_concat, invOp] using h.kind
  | iok q y n hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.of_none ?_ ?_ (by simp)
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simpa [lastInv_concat, invOp] using h.kind
  | ifail q y n hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.of_none ?_ ?_ (by simp)
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simpa [lastInv_concat, invOp] using h.kind
  | aok q y n hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    refine InvAt.of_none ?_ ?_ (by simp)
    · simpa [readObjs_concat_ne_rres] using h.rbuf
    · simpa [lastInv_concat, invOp] using h.kind
  | i35ok q y n ver hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.ins y n _ hpc
    refine InvAt.of_pc h (X := .ins y n (.l37 ver)) (by simp) ⟨h1, by simpa using h2⟩
  | i35fail q y n ver hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.ins y n _ hpc
    refine InvAt.of_pc h (X := .ins y n .fail) (by simp) ⟨h1, by simpa using h2⟩
  | i35retry q y n ver hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.ins y n _ hpc
    refine InvAt.of_pc h (X := .ins y n (.l35 (c.lk y).1)) (by simp) ⟨h1, by simpa using h2⟩
  | i37 q y n ver hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.ins y n _ hpc
    refine InvAt.of_pc h (X := .ins y n (.l38 ver)) (by simp) ⟨h1, by simpa using h2⟩
  | i38 q y n ver hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.ins y n _ hpc
    refine InvAt.of_pc h (X := .ins y n .ok) (by simp) ⟨h1, by simpa using h2⟩
  | a1 q y n hpc =>
    by_cases hpq : p = q
    swap
    · exact (hI p).frame hm (by simp [hpq]) (evOf_toList_ne (by simp) hpq)
    subst hpq
    have h := hI p
    try simp only [Option.toList_none, List.append_nil]
    obtain ⟨h1, h2⟩ := h.alc y n _ hpc
    refine InvAt.of_pc h (X := .alc y n true) (by simp) ⟨h1, by simpa using h2⟩

theorem RRun.inv {tv : Loc → NodeV} {c : RCfg} {L : List (Option (LEv ℕ))}
    (h : RRun (rcfg0 tv) L c) : Inv c (L.filterMap id) := by
  induction h with
  | nil => exact inv_init tv
  | snoc _ hs ih =>
    rename_i l _
    have := ih.step hs
    rw [List.filterMap_append]
    cases l <;> simpa using this

end Podc.OptimismConcurrency
