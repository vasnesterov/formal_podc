import Papers.PODC2026.GeneralizedCAS.Ghost

/-!
# Algorithm 1: the state invariant

`Inv loc pend M G` collects the facts of Appendix B.1 that hold in every reachable state (with
the ghost variables), stated without reference to time:

* structure of timestamps (`ts`): Observations B.1.9, B.1.14;
* the contents of `A`, `S`, the cells and of the local copies (`snap`, `ann`): Observations
  B.1.10, B.1.12, B.1.13, B.1.15;
* the linearization `lin`: `S.state` is the state after `lin`, and the response stored with an
  operation is its response in `lin` (Claims B.3.1.3–B.3.1.5);
* `copied`: after line 7, if `S` is unchanged then its operation is done (Lemma B.1.21);
* `l13`: a process about to perform a successful CAS on line 13 does so for a pending operation
  that is not yet linearized (Lemmas B.1.16, B.1.25 and Proposition B.1.24).

`Inv.step` proves that the invariant is preserved by every step; `reach_inv` that it holds in
every reachable state.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]

namespace PC

variable {R : Type}

/-- Line 3 has been executed in the current operation. -/
def Past3 : PC R → Prop
  | .l2 | .l3 => False
  | _ => True

/-- Inside the loop of lines 5–15. -/
def Loop : PC R → Prop
  | .l5 | .l6 | .l7 | .l8 | .l9 | .l10 | .l13 | .l15 => True
  | _ => False

/-- `snap` holds the value read from `S` on line 6. -/
def HasSnap : PC R → Prop
  | .l7 | .l8 | .l9 | .l10 | .l13 | .l15 => True
  | _ => False

/-- Line 7 has been executed in the current iteration. -/
def Copied : PC R → Prop
  | .l8 | .l9 | .l10 | .l13 | .l15 => True
  | _ => False

/-- `ann` holds the value read from `A` on line 9. -/
def HasAnn : PC R → Prop
  | .l10 | .l13 | .l15 => True
  | _ => False

@[simp] lemma past3_l2 : ¬ (PC.l2 : PC R).Past3 := id
@[simp] lemma past3_l3 : ¬ (PC.l3 : PC R).Past3 := id

end PC

variable (T) in
/-- The response of the instance `x` in the linearization `L`. -/
abbrev linResp (L : List (OpId P × T.Op)) (x : OpId P) : Option T.Resp := T.respIn T.init L x

/-- The state invariant of Algorithm 1 (with ghost variables). -/
structure Inv (loc : P → Loc T) (pend : P → Option T.Op) (M : Mem T) (G : Ghost T P) : Prop where
  cnt_pos : 1 ≤ M.cnt
  ptr : ∀ q x, (loc q).ptr = some x → ∃ n : ℕ, x = (n : Ptr) ∧ n < M.mm
  ptr_inj : ∀ q q' x, (loc q).ptr = some x → (loc q').ptr = some x → q = q'
  pc_ptr : ∀ q, pend q ≠ none → ((loc q).pc = .l2 ↔ (loc q).ptr = none)
  op : ∀ q o, pend q = some o → (loc q).op = (o : WithBot T.Op)
  cur : ∀ q o, pend q = some o → (loc q).pc.Past3 → G.ts (loc q).t = some (q, G.k q, o)
  ts_range : ∀ τ, G.ts τ ≠ none ↔ 1 ≤ τ ∧ τ < M.cnt
  ts_k : ∀ τ q k o, G.ts τ = some (q, k, o) → k ≤ G.k q
  ts_cur : ∀ τ q o, G.ts τ = some (q, G.k q, o) →
    pend q = some o ∧ (loc q).pc.Past3 ∧ (loc q).t = τ
  ts_mono : ∀ τ τ' q k k' o o', G.ts τ = some (q, k, o) → G.ts τ' = some (q, k', o') →
    k < k' → τ < τ'
  ts_ptr : ∀ τ q k o, G.ts τ = some (q, k, o) → (loc q).ptr ≠ none
  dummy : M.cell ⊥ = ⟨0, .bot⟩
  cell : ∀ τ q k o, G.ts τ = some (q, k, o) → WrittenAt loc G q k →
    τ ≤ (M.cell (loc q).me).time ∧
    (τ < (M.cell (loc q).me).time → k < G.k q ∧ ∃ r, linResp T G.lin (q, k) = some r) ∧
    ((M.cell (loc q).me).time = τ →
      ((M.cell (loc q).me).resp = .null ∧ k = G.k q ∧ (loc q).pc.Loop) ∨
      ∃ r, (M.cell (loc q).me).resp = .val r ∧ linResp T G.lin (q, k) = some r)
  lin_nodup : (G.lin.map Prod.fst).Nodup
  lin_ts : ∀ x o, (x, o) ∈ G.lin → ∃ τ, G.ts τ = some (x.1, x.2, o)
  lin_done : ∀ τ q k o, G.ts τ = some (q, k, o) → (q, k) ∈ G.lin.map Prod.fst →
    M.cell (loc q).me = ⟨τ, .null⟩ → WrittenAt loc G q k → M.S.time = τ
  S_state : M.S.state = T.runOps T.init (G.lin.map Prod.snd)
  S_zero : M.S.time = 0 → G.lin = [] ∧ M.S.ptr = ⊥ ∧ M.S.resp = .bot
  S_pos : M.S.time ≠ 0 → ∃ q k o, G.ts M.S.time = some (q, k, o) ∧ WrittenAt loc G q k ∧
    G.lin.getLast? = some ((q, k), o) ∧ M.S.ptr = (loc q).me ∧
    ∃ r, M.S.resp = .val r ∧ linResp T G.lin (q, k) = some r
  A_zero : M.A.time = 0 → M.A = ⟨0, ⊥, ⊥⟩
  A_pos : M.A.time ≠ 0 → ∃ q k o, G.ts M.A.time = some (q, k, o) ∧ WrittenAt loc G q k ∧
    M.A.op = (o : WithBot T.Op) ∧ M.A.ptr = (loc q).me
  snap_zero : ∀ q, pend q ≠ none → (loc q).pc.HasSnap → (loc q).snap.time = 0 →
    (loc q).snap.ptr = ⊥ ∧ (loc q).snap.resp = .bot
  snap_pos : ∀ q, pend q ≠ none → (loc q).pc.HasSnap → (loc q).snap.time ≠ 0 →
    ∃ q' k o, G.ts (loc q).snap.time = some (q', k, o) ∧ WrittenAt loc G q' k ∧
      (loc q).snap.ptr = (loc q').me ∧
      ∃ r, (loc q).snap.resp = .val r ∧ linResp T G.lin (q', k) = some r
  copied : ∀ q, pend q ≠ none → (loc q).pc.Copied → M.S = (loc q).snap →
    DoneL loc M G (loc q).snap.time
  ann_zero : ∀ q, pend q ≠ none → (loc q).pc.HasAnn → (loc q).ann.time = 0 →
    (loc q).ann = ⟨0, ⊥, ⊥⟩
  ann_pos : ∀ q, pend q ≠ none → (loc q).pc.HasAnn → (loc q).ann.time ≠ 0 →
    ∃ q' k o, G.ts (loc q).ann.time = some (q', k, o) ∧ WrittenAt loc G q' k ∧
      (loc q).ann.op = (o : WithBot T.Op) ∧ (loc q).ann.ptr = (loc q').me
  l13 : ∀ q, pend q ≠ none → (loc q).pc = .l13 → M.S = (loc q).snap →
    ∃ q' o, G.ts (loc q).ann.time = some (q', G.k q', o) ∧ (q', G.k q') ∉ G.lin.map Prod.fst ∧
      M.cell (loc q').me = ⟨(loc q).ann.time, .null⟩
  ret : ∀ q r, pend q ≠ none → (loc q).pc = .l16 r → linResp T G.lin (q, G.k q) = some r
  lin_written : ∀ q k o, ((q, k), o) ∈ G.lin → WrittenAt loc G q k

/-- The invariant in a configuration. -/
abbrev CInv (C : Cfg T P) (G : Ghost T P) : Prop := Inv C.loc C.pend C.M G

/-! ## Frame lemmas -/

section frame

variable {loc : P → Loc T} {p : P} {L' : Loc T} {G : Ghost T P}

lemma ptr_upd (h : L'.ptr = (loc p).ptr) (q : P) :
    (Function.update loc p L' q).ptr = (loc q).ptr := by
  by_cases hq : q = p
  · subst hq; simp [h]
  · simp [Function.update_of_ne hq]

lemma t_upd (h : L'.t = (loc p).t) (q : P) :
    (Function.update loc p L' q).t = (loc q).t := by
  by_cases hq : q = p
  · subst hq; simp [h]
  · simp [Function.update_of_ne hq]

lemma op_upd (h : L'.op = (loc p).op) (q : P) :
    (Function.update loc p L' q).op = (loc q).op := by
  by_cases hq : q = p
  · subst hq; simp [h]
  · simp [Function.update_of_ne hq]

lemma me_upd (h : L'.ptr = (loc p).ptr) (q : P) :
    (Function.update loc p L' q).me = (loc q).me := by
  by_cases hq : q = p
  · subst hq; simp [Loc.me, h]
  · simp [Function.update_of_ne hq]

lemma writtenAt_upd (h : L'.pc = .l4 ↔ (loc p).pc = .l4) {q : P} {k : ℕ} :
    WrittenAt (Function.update loc p L') G q k ↔ WrittenAt loc G q k := by
  unfold WrittenAt
  by_cases hq : q = p
  · subst hq; simp [h]
  · simp [Function.update_of_ne hq]

lemma doneL_upd (h₁ : L'.ptr = (loc p).ptr) (h₂ : L'.pc = .l4 ↔ (loc p).pc = .l4) {M : Mem T}
    {τ : ℕ} : DoneL (Function.update loc p L') M G τ ↔ DoneL loc M G τ := by
  unfold DoneL
  simp only [writtenAt_upd h₂, me_upd h₁]

lemma inv_ghost_congr {pend : P → Option T.Op} {M : Mem T} {G G' : Ghost T P}
    (h₁ : G'.ts = G.ts) (h₂ : G'.lin = G.lin) (h₃ : G'.k = G.k) (h : Inv loc pend M G) :
    Inv loc pend M G' := by
  obtain ⟨ts, lin, k, it, ns, wd, cl, lt⟩ := G
  obtain ⟨ts', lin', k', it', ns', wd', cl', lt'⟩ := G'
  simp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  cases h
  constructor <;> assumption

end frame

/-! ## Preservation, step by step -/

set_option hygiene false in
/-- Split a goal `∀ q, …` on `q = p`; close the case `q ≠ p` with `h q` (after rewriting the
updated local states). -/
macro "fq " h:term : tactic => `(tactic| (
  intro q
  rcases eq_or_ne q p with rfl | hq
  rotate_left
  · simp only [Function.update_of_ne hq]; exact $h q))

set_option hygiene false in
/-- Split a goal `∀ q, …` on `q = p`, rewriting the updated local state in the case `q ≠ p`. -/
macro "fq' " h:term : tactic => `(tactic| (
  intro q
  rcases eq_or_ne q p with rfl | hq
  rotate_left
  simp only [Function.update_of_ne hq]
  rotate_left))

lemma upd_ne {loc : P → Loc T} {p q : P} {L' : Loc T} (h : q ≠ p) :
    Function.update loc p L' q = loc q := Function.update_of_ne h _ _

section steps

variable {loc : P → Loc T} {pend : P → Option T.Op} {M : Mem T} {G : Ghost T P} {p : P}

set_option hygiene false in
/-- Close the fields of `Inv` that follow verbatim from `hI`. -/
macro "inv_triv" : tactic => `(tactic| first
  | exact hI.cnt_pos | exact hI.ptr | exact hI.ptr_inj | exact hI.pc_ptr | exact hI.op
  | exact hI.cur | exact hI.ts_range | exact hI.ts_k | exact hI.ts_cur | exact hI.ts_mono
  | exact hI.ts_ptr | exact hI.dummy | exact hI.cell | exact hI.lin_nodup | exact hI.lin_ts
  | exact hI.lin_done | exact hI.S_state | exact hI.S_zero | exact hI.S_pos | exact hI.A_zero
  | exact hI.A_pos | exact hI.snap_zero | exact hI.snap_pos | exact hI.copied | exact hI.ann_zero
  | exact hI.ann_pos | exact hI.l13 | exact hI.ret | exact hI.lin_written)

/-- Line 9: read `A`. -/
lemma Inv.tau_l9 (hI : Inv loc pend M G) (hp : pend p ≠ none) (hpc : (loc p).pc = .l9) :
    Inv (Function.update loc p { loc p with ann := M.A, pc := .l10 }) pend M G := by
  set L' : Loc T := { loc p with ann := M.A, pc := .l10 } with hL'
  have hptr : L'.ptr = (loc p).ptr := rfl
  have h4 : L'.pc = .l4 ↔ (loc p).pc = .l4 := by simp [L', hpc]
  constructor
  all_goals try simp only [me_upd hptr, writtenAt_upd h4, doneL_upd hptr h4, ptr_upd hptr,
    t_upd (L' := L') rfl, op_upd (L' := L') rfl]
  all_goals try inv_triv
  case pc_ptr => fq hI.pc_ptr; simpa [L', hpc] using hI.pc_ptr q
  case op => fq hI.op; simpa [L'] using hI.op q
  case cur => fq hI.cur; simpa [L', hpc, PC.Past3] using hI.cur q
  case ts_cur =>
    intro τ q o h; obtain ⟨h1, h2, h3⟩ := hI.ts_cur τ q o h
    rcases eq_or_ne q p with rfl | hq
    · simp_all [L', PC.Past3]
    · simp [upd_ne hq, h1, h2, h3]
  case cell =>
    intro τ q k o h hw'; obtain ⟨h1, h2, h3⟩ := hI.cell τ q k o h hw'
    refine ⟨h1, h2, fun hτ => ?_⟩
    rcases eq_or_ne q p with rfl | hq
    · simpa [L', hpc, PC.Loop] using h3 hτ
    · simpa [upd_ne hq] using h3 hτ
  case snap_zero => fq hI.snap_zero; simpa [L', hpc, PC.HasSnap] using hI.snap_zero q
  case snap_pos => fq hI.snap_pos; simpa [L', hpc, PC.HasSnap] using hI.snap_pos q
  case copied => fq hI.copied; simpa [L', hpc, PC.Copied] using hI.copied q
  case ann_zero => fq hI.ann_zero; simp only [Function.update_self, L']; intro _ _ h; exact hI.A_zero h
  case ann_pos => fq hI.ann_pos; simp only [Function.update_self, L']; intro _ _ h; exact hI.A_pos h
  case l13 => fq hI.l13; simp [L']
  case ret => fq hI.ret; simp [L']

/-- A step that only changes the program counter of `p` (used for lines 5 and 10). -/
lemma Inv.pc_move (hI : Inv loc pend M G) (hp : pend p ≠ none) {pc' : PC T.Resp}
    (h3 : (loc p).pc.Past3) (h3' : pc'.Past3) (h4 : (loc p).pc ≠ .l4) (h4' : pc' ≠ .l4)
    (hloop : (loc p).pc.Loop) (hloop' : pc'.Loop ∨ (M.cell (loc p).me).resp ≠ .null)
    (hsnap : pc'.HasSnap → (loc p).pc.HasSnap)
    (hcop : pc'.Copied → M.S = (loc p).snap → DoneL loc M G (loc p).snap.time)
    (hann : pc'.HasAnn → (loc p).pc.HasAnn)
    (h13 : pc' = .l13 → M.S = (loc p).snap →
      ∃ q' o, G.ts (loc p).ann.time = some (q', G.k q', o) ∧ (q', G.k q') ∉ G.lin.map Prod.fst ∧
        M.cell (loc q').me = ⟨(loc p).ann.time, .null⟩)
    (h16 : ∀ r, pc' = .l16 r → linResp T G.lin (p, G.k p) = some r) :
    Inv (Function.update loc p { loc p with pc := pc' }) pend M G := by
  set L' : Loc T := { loc p with pc := pc' } with hL'
  have hptr : L'.ptr = (loc p).ptr := rfl
  have h4'' : L'.pc = .l4 ↔ (loc p).pc = .l4 := by simp [L', h4, h4']
  have h2 : pc' ≠ .l2 := by rintro rfl; exact h3'
  have h2' : (loc p).pc ≠ .l2 := by intro h; rw [h] at h3; exact h3
  constructor
  all_goals try simp only [me_upd hptr, writtenAt_upd h4'', doneL_upd hptr h4'', ptr_upd hptr,
    t_upd (L' := L') rfl, op_upd (L' := L') rfl]
  all_goals try inv_triv
  case pc_ptr => fq hI.pc_ptr; have := hI.pc_ptr q hp; simp_all [L']
  case op => fq hI.op; simpa [L'] using hI.op q
  case cur => fq hI.cur; simpa [L', h3'] using fun o h => hI.cur q o h h3
  case ts_cur =>
    intro τ q o h; obtain ⟨c1, c2, c3⟩ := hI.ts_cur τ q o h
    rcases eq_or_ne q p with rfl | hq
    · simp_all [L']
    · simp [upd_ne hq, c1, c2, c3]
  case cell =>
    intro τ q k o h hw'; obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o h hw'
    refine ⟨c1, c2, fun hτ => ?_⟩
    rcases eq_or_ne q p with rfl | hq
    · rcases c3 hτ with h | h
      · rcases hloop' with hl | hl
        · exact Or.inl ⟨h.1, h.2.1, by simpa [L'] using hl⟩
        · exact absurd h.1 hl
      · exact Or.inr h
    · simpa [upd_ne hq] using c3 hτ
  case snap_zero => fq hI.snap_zero; simpa [L'] using fun h h' => hI.snap_zero q h (hsnap h')
  case snap_pos => fq hI.snap_pos; simpa [L'] using fun h h' => hI.snap_pos q h (hsnap h')
  case copied => fq hI.copied; simpa [L'] using fun _ h' => hcop h'
  case ann_zero => fq hI.ann_zero; simpa [L'] using fun h h' => hI.ann_zero q h (hann h')
  case ann_pos => fq hI.ann_pos; simpa [L'] using fun h h' => hI.ann_pos q h (hann h')
  case l13 => fq hI.l13; simpa [L'] using fun _ h => h13 h
  case ret => fq hI.ret; simpa [L'] using fun r _ h => h16 r h

/-- Facts about the cell of a process inside its loop: it holds the current timestamp, and its
response is `Null` or the response of the current operation in the linearization. -/
lemma Inv.own_cell (hI : Inv loc pend M G) {o : T.Op} (ho : pend p = some o)
    (h3 : (loc p).pc.Past3) (h4 : (loc p).pc ≠ .l4) :
    (M.cell (loc p).me).time = (loc p).t ∧
    ((M.cell (loc p).me).resp = .null ∨
      ∃ r, (M.cell (loc p).me).resp = .val r ∧ linResp T G.lin (p, G.k p) = some r) := by
  have hcur := hI.cur p o ho h3
  obtain ⟨c1, c2, c3⟩ := hI.cell _ p _ o hcur (Or.inr h4)
  have ht : (M.cell (loc p).me).time = (loc p).t := by
    rcases lt_or_eq_of_le c1 with h | h
    · exact absurd (c2 h).1 (lt_irrefl _)
    · exact h.symm
  refine ⟨ht, ?_⟩
  rcases c3 ht with h | h
  · exact Or.inl h.1
  · exact Or.inr h

/-- Line 5: test the own cell; continue the loop, or go to line 16. -/
lemma Inv.tau_l5 (hI : Inv loc pend M G) (hp : pend p ≠ none) (hpc : (loc p).pc = .l5) :
    Inv (Function.update loc p { loc p with pc := pc5 (loc p) M }) pend M G := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨ht, hr⟩ := hI.own_cell ho (by simp [hpc, PC.Past3]) (by simp [hpc])
  have key : pc5 (loc p) M = .l6 ∨ ∃ r, pc5 (loc p) M = .l16 r ∧
      linResp T G.lin (p, G.k p) = some r ∧ (M.cell (loc p).me).resp = .val r := by
    unfold pc5
    split_ifs with h
    · exact Or.inl rfl
    · rcases hr with hr | ⟨r, hr, hl⟩
      · exact absurd (CellVal.ext ht hr) h
      · simp only [hr]; exact Or.inr ⟨r, rfl, hl, rfl⟩
  rcases key with h | ⟨r, h, hl, hv⟩ <;> rw [h] <;>
    refine hI.pc_move hp (by simp [hpc, PC.Past3]) (by simp [PC.Past3]) (by simp [hpc])
      (by simp) (by simp [hpc, PC.Loop]) ?_ (by simp [PC.HasSnap]) (by simp [PC.Copied])
      (by simp [PC.HasAnn]) (by simp) ?_
  · exact Or.inl (by simp [PC.Loop])
  · simp
  · exact Or.inr (by simp [hv])
  · rintro r' ⟨⟩; exact hl

open Classical in
/-- Line 10: read the cell of the announced operation. -/
lemma Inv.tau_l10 (hI : Inv loc pend M G) (hp : pend p ≠ none) (hpc : (loc p).pc = .l10) :
    Inv (Function.update loc p { loc p with pc := (if M.cell (loc p).ann.ptr =
      ⟨(loc p).ann.time, .null⟩ then .l13 else .l15) }) pend M G := by
  split_ifs with hc
  · refine hI.pc_move hp (by simp [hpc, PC.Past3]) (by simp [PC.Past3]) (by simp [hpc])
      (by simp) (by simp [hpc, PC.Loop]) (Or.inl (by simp [PC.Loop])) (by simp [hpc, PC.HasSnap])
      (fun _ => hI.copied p hp (by simp [hpc, PC.Copied])) (by simp [hpc, PC.HasAnn]) ?_ (by simp)
    intro _ hS
    have hann : (loc p).ann.time ≠ 0 := by
      intro h0
      have := hI.ann_zero p hp (by simp [hpc, PC.HasAnn]) h0
      rw [this, hI.dummy] at hc
      simp at hc
    obtain ⟨q', k, o, hts, hw, -, hptr⟩ := hI.ann_pos p hp (by simp [hpc, PC.HasAnn]) hann
    rw [hptr] at hc
    obtain ⟨c1, c2, c3⟩ := hI.cell _ q' k o hts hw
    rw [hc] at c3
    have hk : k = G.k q' := by
      rcases c3 rfl with h | ⟨r, h, -⟩
      · exact h.2.1
      · cases h
    subst hk
    refine ⟨q', o, hts, fun hmem => ?_, hc⟩
    have hSt := hI.lin_done _ q' _ o hts hmem hc hw
    have hd := hI.copied p hp (by simp [hpc, PC.Copied]) hS
    rw [← hS, hSt] at hd
    rcases hd with h0 | ⟨q'', k'', o'', hts', -, hne⟩
    · exact hann h0
    · rw [hts] at hts'
      simp only [Option.some.injEq, Prod.mk.injEq] at hts'
      obtain ⟨rfl, rfl, rfl⟩ := hts'
      exact hne hc
  · exact hI.pc_move hp (by simp [hpc, PC.Past3]) (by simp [PC.Past3]) (by simp [hpc])
      (by simp) (by simp [hpc, PC.Loop]) (Or.inl (by simp [PC.Loop])) (by simp [hpc, PC.HasSnap])
      (fun _ => hI.copied p hp (by simp [hpc, PC.Copied])) (by simp [hpc, PC.HasAnn]) (by simp) (by simp)

/-- Line 6: read `S`. -/
lemma Inv.tau_l6 (hI : Inv loc pend M G) (hp : pend p ≠ none) (hpc : (loc p).pc = .l6) :
    Inv (Function.update loc p { loc p with snap := M.S, pc := .l7 }) pend M G := by
  set L' : Loc T := { loc p with snap := M.S, pc := .l7 } with hL'
  have hptr : L'.ptr = (loc p).ptr := rfl
  have h4 : L'.pc = .l4 ↔ (loc p).pc = .l4 := by simp [L', hpc]
  constructor
  all_goals try simp only [me_upd hptr, writtenAt_upd h4, doneL_upd hptr h4, ptr_upd hptr,
    t_upd (L' := L') rfl, op_upd (L' := L') rfl]
  all_goals try inv_triv
  case pc_ptr => fq hI.pc_ptr; simpa [L', hpc] using hI.pc_ptr q
  case op => fq hI.op; simpa [L'] using hI.op q
  case cur => fq hI.cur; simpa [L', hpc, PC.Past3] using hI.cur q
  case ts_cur =>
    intro τ q o h; obtain ⟨c1, c2, c3⟩ := hI.ts_cur τ q o h
    rcases eq_or_ne q p with rfl | hq
    · simp_all [L', PC.Past3]
    · simp [upd_ne hq, c1, c2, c3]
  case cell =>
    intro τ q k o h hw'; obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o h hw'
    refine ⟨c1, c2, fun hτ => ?_⟩
    rcases eq_or_ne q p with rfl | hq
    · simpa [L', hpc, PC.Loop] using c3 hτ
    · simpa [upd_ne hq] using c3 hτ
  case snap_zero =>
    fq hI.snap_zero; simp only [Function.update_self, L']; intro _ _ h; exact (hI.S_zero h).2
  case snap_pos =>
    fq hI.snap_pos; simp only [Function.update_self, L']; intro _ _ h
    obtain ⟨q', k, o, h1, h2, -, h3, h4⟩ := hI.S_pos h
    exact ⟨q', k, o, h1, h2, h3, h4⟩
  case copied => fq hI.copied; simp [L', PC.Copied]
  case ann_zero => fq hI.ann_zero; simp [L', PC.HasAnn]
  case ann_pos => fq hI.ann_pos; simp [L', PC.HasAnn]
  case l13 => fq hI.l13; simp [L']
  case ret => fq hI.ret; simp [L']

/-- Writing a triple of the form `(t, o, ptr)` of a current operation into `A` (lines 8, 15). -/
lemma Inv.write_A (hI : Inv loc pend M G) (hp : pend p ≠ none) (hpc : (loc p).pc.Past3)
    (hpc4 : (loc p).pc ≠ .l4) {pc' : PC T.Resp} (h3' : pc'.Past3) (h4' : pc' ≠ .l4)
    (hloop' : pc'.Loop) (hsnap : pc'.HasSnap → (loc p).pc.HasSnap)
    (hcop : pc'.Copied → (loc p).pc.Copied) (hann : pc'.HasAnn → (loc p).pc.HasAnn)
    (h13 : pc' ≠ .l13) (h16 : ∀ r, pc' ≠ .l16 r) {a : AVal T.Op}
    (ha : a = M.A ∨ a = (loc p).mine) (hloop : (loc p).pc.Loop) :
    Inv (Function.update loc p { loc p with pc := pc' }) pend { M with A := a } G := by
  have hM : Inv loc pend { M with A := a } G := by
    rcases ha with rfl | rfl
    · exact hI
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hp
    have hcur := hI.cur p o ho hpc
    have h1 := ((hI.ts_range (loc p).t).1 (by simp [hcur])).1
    refine { hI with A_zero := ?_, A_pos := ?_ }
    · intro h; simp [Loc.mine] at h; omega
    · intro _; exact ⟨p, G.k p, o, hcur, Or.inr hpc4, by simp [Loc.mine, hI.op p o ho], rfl⟩
  exact hM.pc_move hp hpc h3' hpc4 h4' hloop (Or.inl hloop') hsnap
    (fun h => hM.copied p hp (hcop h)) hann
    (fun h => absurd h h13) (fun r h => absurd h (h16 r))

/-- Owners of timestamps have allocated their cell. -/
lemma Inv.owner_ne (hI : Inv loc pend M G) (hptr : (loc p).ptr = none) {τ : ℕ} {q : P} {k : ℕ}
    {o : T.Op} (h : G.ts τ = some (q, k, o)) : q ≠ p := by
  rintro rfl; exact hI.ts_ptr τ q k o h hptr

/-- Line 2: allocate a cell. -/
lemma Inv.tau_l2 (hI : Inv loc pend M G) (hp : pend p ≠ none) (hpc : (loc p).pc = .l2) :
    Inv (Function.update loc p { loc p with ptr := some (M.mm : Ptr), pc := .l3 }) pend
      { M with mm := M.mm + 1 } G := by
  set L' : Loc T := { loc p with ptr := some (M.mm : Ptr), pc := .l3 } with hL'
  have hnone : (loc p).ptr = none := (hI.pc_ptr p hp).1 hpc
  have hown := fun {τ q k o} (h : G.ts τ = some (q, k, o)) => hI.owner_ne hnone h
  have hme : ∀ {τ q k o}, G.ts τ = some (q, k, o) → (Function.update loc p L' q).me = (loc q).me :=
    fun h => by rw [upd_ne (hown h)]
  have hw : ∀ {τ q k o}, G.ts τ = some (q, k, o) →
      (WrittenAt (Function.update loc p L') G q k ↔ WrittenAt loc G q k) :=
    fun h => by unfold WrittenAt; rw [upd_ne (hown h)]
  have hd : ∀ τ, DoneL (Function.update loc p L') M G τ ↔ DoneL loc M G τ := by
    intro τ; unfold DoneL
    constructor
    · rintro (h | ⟨q, k, o, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, k, o, h1, (hw h1).1 h2, by rwa [← hme h1]⟩
    · rintro (h | ⟨q, k, o, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, k, o, h1, (hw h1).2 h2, by rwa [hme h1]⟩
  constructor
  case cnt_pos => exact hI.cnt_pos
  case ptr =>
    intro q x h
    rcases eq_or_ne q p with rfl | hq
    · simp [L'] at h; exact ⟨M.mm, h.symm, by simp⟩
    · rw [upd_ne hq] at h; obtain ⟨n, h1, h2⟩ := hI.ptr q x h; exact ⟨n, h1, by simp; omega⟩
  case ptr_inj =>
    intro q q' x h h'
    have key : ∀ r, r ≠ p → (Function.update loc p L' r).ptr = some x → ∃ n : ℕ, x = ↑n ∧ n < M.mm :=
      fun r hr h => hI.ptr r x (by rwa [upd_ne hr] at h)
    rcases eq_or_ne q p with rfl | hq <;> rcases eq_or_ne q' q with rfl | hq'
    · rfl
    · have hx : x = (M.mm : Ptr) := by simp [L'] at h; exact h.symm
      obtain ⟨n, h1, h2⟩ := key q' hq' h'; rw [hx] at h1; simp at h1; omega
    · rfl
    · rcases eq_or_ne q' p with rfl | hq''
      · have hx : x = (M.mm : Ptr) := by simp [L'] at h'; exact h'.symm
        obtain ⟨n, h1, h2⟩ := key q hq h; rw [hx] at h1; simp at h1; omega
      · rw [upd_ne hq] at h; rw [upd_ne hq''] at h'; exact hI.ptr_inj q q' x h h'
  case pc_ptr => fq hI.pc_ptr; simp [L']
  case op => fq hI.op; simpa [L'] using hI.op q
  case cur => fq hI.cur; simp [L', PC.Past3]
  case ts_range => exact hI.ts_range
  case ts_k => exact hI.ts_k
  case ts_cur =>
    intro τ q o h; rw [upd_ne (hown h)]; exact hI.ts_cur τ q o h
  case ts_mono => exact hI.ts_mono
  case ts_ptr => intro τ q k o h; rw [upd_ne (hown h)]; exact hI.ts_ptr τ q k o h
  case dummy => exact hI.dummy
  case cell =>
    intro τ q k o h hw'; rw [hme h]; rw [hw h] at hw'
    obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o h hw'
    exact ⟨c1, c2, by rw [upd_ne (hown h)]; exact c3⟩
  case lin_nodup => exact hI.lin_nodup
  case lin_ts => exact hI.lin_ts
  case lin_done =>
    intro τ q k o h hm hc hw'; rw [hme h] at hc; rw [hw h] at hw'
    exact hI.lin_done τ q k o h hm hc hw'
  case S_state => exact hI.S_state
  case S_zero => exact hI.S_zero
  case S_pos =>
    intro h0; obtain ⟨q, k, o, h1, h2, h3, h4, h5⟩ := hI.S_pos h0
    exact ⟨q, k, o, h1, (hw h1).2 h2, h3, by rw [hme h1]; exact h4, h5⟩
  case A_zero => exact hI.A_zero
  case A_pos =>
    intro h0; obtain ⟨q, k, o, h1, h2, h3, h4⟩ := hI.A_pos h0
    exact ⟨q, k, o, h1, (hw h1).2 h2, h3, by rw [hme h1]; exact h4⟩
  case snap_zero => fq hI.snap_zero; simp [L', PC.HasSnap]
  case snap_pos =>
    intro q; rcases eq_or_ne q p with rfl | hq
    · simp [L', PC.HasSnap]
    · rw [upd_ne hq]; intro h1 h2 h3
      obtain ⟨q', k, o, c1, c2, c3, c4⟩ := hI.snap_pos q h1 h2 h3
      exact ⟨q', k, o, c1, (hw c1).2 c2, by rw [hme c1]; exact c3, c4⟩
  case copied =>
    intro q; rcases eq_or_ne q p with rfl | hq
    · simp [L', PC.Copied]
    · rw [upd_ne hq]; intro h1 h2 h3; exact (hd _).2 (hI.copied q h1 h2 h3)
  case ann_zero => fq hI.ann_zero; simp [L', PC.HasAnn]
  case ann_pos =>
    intro q; rcases eq_or_ne q p with rfl | hq
    · simp [L', PC.HasAnn]
    · rw [upd_ne hq]; intro h1 h2 h3
      obtain ⟨q', k, o, c1, c2, c3, c4⟩ := hI.ann_pos q h1 h2 h3
      exact ⟨q', k, o, c1, (hw c1).2 c2, c3, by rw [hme c1]; exact c4⟩
  case l13 =>
    intro q; rcases eq_or_ne q p with rfl | hq
    · simp [L']
    · rw [upd_ne hq]; intro h1 h2 h3
      obtain ⟨q', o, c1, c2, c3⟩ := hI.l13 q h1 h2 h3
      exact ⟨q', o, c1, c2, by rw [hme c1]; exact c3⟩
  case ret => fq hI.ret; simp [L']
  case lin_written =>
    intro q k o h
    obtain ⟨τ, hτ⟩ := hI.lin_ts _ _ h
    exact (hw hτ).2 (hI.lin_written q k o h)

/-- Line 3: obtain a timestamp. -/
lemma Inv.tau_l3 (hI : Inv loc pend M G) {o : T.Op} (ho : pend p = some o)
    (hpc : (loc p).pc = .l3) :
    Inv (Function.update loc p { loc p with t := M.cnt, pc := .l4 }) pend
      { M with cnt := M.cnt + 1 }
      { G with ts := Function.update G.ts M.cnt (some (p, G.k p, o)) } := by
  set L' : Loc T := { loc p with t := M.cnt, pc := .l4 } with hL'
  set G' : Ghost T P := { G with ts := Function.update G.ts M.cnt (some (p, G.k p, o)) } with hG'
  have hp : pend p ≠ none := by simp [ho]
  have hptr : L'.ptr = (loc p).ptr := rfl
  have hme := me_upd hptr
  have hfresh : G.ts M.cnt = none := by
    by_contra h; have := (hI.ts_range _).1 h; omega
  have hts : ∀ {τ}, G.ts τ ≠ none → G'.ts τ = G.ts τ := by
    intro τ h; have : τ ≠ M.cnt := by rintro rfl; exact h hfresh
    simp [G', Function.update_of_ne this]
  have hnotcur : ∀ {τ q o'}, G.ts τ = some (q, G.k q, o') → q ≠ p := by
    rintro τ q o' h rfl; have := (hI.ts_cur τ q o' h).2.1; rw [hpc] at this; exact this
  have hlt : ∀ {τ k o'}, G.ts τ = some (p, k, o') → k < G.k p := by
    intro τ k o' h
    rcases lt_or_eq_of_le (hI.ts_k τ p k o' h) with h' | h'
    · exact h'
    · subst h'; exact absurd rfl (hnotcur h)
  have hw : ∀ {τ q k o'}, G.ts τ = some (q, k, o') →
      (WrittenAt (Function.update loc p L') G' q k ↔ WrittenAt loc G q k) := by
    intro τ q k o' h; unfold WrittenAt
    rcases eq_or_ne q p with rfl | hq
    · simp [G', hlt h]
    · simp [G', upd_ne hq]
  have hd : ∀ τ, DoneL (Function.update loc p L') { M with cnt := M.cnt + 1 } G' τ ↔
      DoneL loc M G τ := by
    intro τ; unfold DoneL
    by_cases hτ : τ = M.cnt
    · subst hτ
      have h0 : M.cnt ≠ 0 := by have := hI.cnt_pos; omega
      simp only [h0, false_or, G', Function.update_self, Option.some.injEq, Prod.mk.injEq,
        hfresh, reduceCtorEq, false_and, exists_false, iff_false, not_exists, not_and]
      rintro q k o' ⟨rfl, rfl, rfl⟩ hw'
      simp [WrittenAt, L'] at hw'
    · have hτ' : G'.ts τ = G.ts τ := by simp [G', Function.update_of_ne hτ]
      simp only [hτ']
      constructor
      · rintro (h | ⟨q, k, o', h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨q, k, o', h1, (hw h1).1 h2, by rwa [hme] at h3⟩
      · rintro (h | ⟨q, k, o', h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨q, k, o', h1, (hw h1).2 h2, by rwa [hme]⟩
  have hdef : ∀ {τ q k o'}, G.ts τ = some (q, k, o') → G'.ts τ = some (q, k, o') :=
    fun h => by rw [hts (by simp [h]), h]
  constructor
  case cnt_pos => simp
  case ptr => intro q x h; rw [ptr_upd hptr] at h; obtain ⟨n, h1, h2⟩ := hI.ptr q x h; exact ⟨n, h1, h2⟩
  case ptr_inj => intro q q' x h h'; rw [ptr_upd hptr] at h h'; exact hI.ptr_inj q q' x h h'
  case pc_ptr =>
    fq hI.pc_ptr
    have := (hI.pc_ptr q hp).not.1 (by simp [hpc]); simp [L', this]
  case op => fq hI.op; simpa [L'] using hI.op q
  case cur =>
    fq' hI.cur
    · intro o' ho' _; rw [ho] at ho'; cases ho'; simp [L', G']
    · intro o' ho' h3; have := hI.cur q o' ho' h3
      rw [hts (by simp [this])]; exact this
  case ts_range =>
    intro τ
    by_cases hτ : τ = M.cnt
    · subst hτ; simp [G']; exact hI.cnt_pos
    · simp only [G', Function.update_of_ne hτ]; rw [hI.ts_range τ]; omega
  case ts_k =>
    intro τ q k o' h
    by_cases hτ : τ = M.cnt
    · subst hτ; simp [G'] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact le_rfl
    · simp only [G', Function.update_of_ne hτ] at h; exact hI.ts_k τ q k o' h
  case ts_cur =>
    intro τ q o' h
    by_cases hτ : τ = M.cnt
    · subst hτ; simp [G'] at h; obtain ⟨rfl, -, rfl⟩ := h
      simp [L', ho, PC.Past3]
    · simp only [G', Function.update_of_ne hτ] at h
      rw [upd_ne (hnotcur h)]; exact hI.ts_cur τ q o' h
  case ts_mono =>
    intro τ τ' q k k' o₁ o₂ h h' hk
    by_cases hτ : τ = M.cnt <;> by_cases hτ' : τ' = M.cnt
    · subst hτ hτ'; simp [G'] at h h'; omega
    · subst hτ; simp [G'] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [G', Function.update_of_ne hτ'] at h'
      have := hI.ts_k τ' p k' o₂ h'; omega
    · subst hτ'; simp [G'] at h'; obtain ⟨rfl, rfl, rfl⟩ := h'
      simp only [G', Function.update_of_ne hτ] at h
      have := (hI.ts_range τ).1 (by simp [h]); omega
    · simp only [G', Function.update_of_ne hτ, Function.update_of_ne hτ'] at h h'
      exact hI.ts_mono τ τ' q k k' o₁ o₂ h h' hk
  case ts_ptr =>
    intro τ q k o' h; rw [ptr_upd hptr]
    by_cases hτ : τ = M.cnt
    · subst hτ; simp [G'] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact (hI.pc_ptr p hp).not.1 (by simp [hpc])
    · simp only [G', Function.update_of_ne hτ] at h; exact hI.ts_ptr τ q k o' h
  case dummy => exact hI.dummy
  case cell =>
    intro τ q k o' h hw'
    by_cases hτ : τ = M.cnt
    · subst hτ; simp [G'] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp [WrittenAt, L', G'] at hw'
    · simp only [G', Function.update_of_ne hτ] at h
      have hw'' := (hw h).1 hw'
      simp only [hme]
      obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o' h hw''
      refine ⟨c1, c2, fun ht => ?_⟩
      rcases c3 ht with c | c
      · left; refine ⟨c.1, c.2.1, ?_⟩
        rcases eq_or_ne q p with rfl | hq
        · exact absurd c.2.1 (hlt h).ne
        · rw [upd_ne hq]; exact c.2.2
      · exact Or.inr c
  case lin_nodup => exact hI.lin_nodup
  case lin_ts => intro x o' h; obtain ⟨τ, hτ⟩ := hI.lin_ts x o' h; exact ⟨τ, hdef hτ⟩
  case lin_done =>
    intro τ q k o' h hm hc hw'
    by_cases hτ : τ = M.cnt
    · subst hτ; simp [G'] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp [WrittenAt, L', G'] at hw'
    · simp only [G', Function.update_of_ne hτ] at h
      rw [hme] at hc; exact hI.lin_done τ q k o' h hm hc ((hw h).1 hw')
  case S_state => exact hI.S_state
  case S_zero => exact hI.S_zero
  case S_pos =>
    intro h0; obtain ⟨q, k, o', h1, h2, h3, h4, h5⟩ := hI.S_pos h0
    exact ⟨q, k, o', hdef h1, (hw h1).2 h2, h3, by rw [hme]; exact h4, h5⟩
  case A_zero => exact hI.A_zero
  case A_pos =>
    intro h0; obtain ⟨q, k, o', h1, h2, h3, h4⟩ := hI.A_pos h0
    exact ⟨q, k, o', hdef h1, (hw h1).2 h2, h3, by rw [hme]; exact h4⟩
  case snap_zero => fq hI.snap_zero; simp [L', PC.HasSnap]
  case snap_pos =>
    fq' hI.snap_pos
    · simp [L', PC.HasSnap]
    · intro h1 h2 h3
      obtain ⟨q', k, o', c1, c2, c3, c4⟩ := hI.snap_pos q h1 h2 h3
      exact ⟨q', k, o', hdef c1, (hw c1).2 c2, by rw [hme]; exact c3, c4⟩
  case copied =>
    fq' hI.copied
    · simp [L', PC.Copied]
    · intro h1 h2 h3; exact (hd _).2 (hI.copied q h1 h2 h3)
  case ann_zero => fq hI.ann_zero; simp [L', PC.HasAnn]
  case ann_pos =>
    fq' hI.ann_pos
    · simp [L', PC.HasAnn]
    · intro h1 h2 h3
      obtain ⟨q', k, o', c1, c2, c3, c4⟩ := hI.ann_pos q h1 h2 h3
      exact ⟨q', k, o', hdef c1, (hw c1).2 c2, c3, by rw [hme]; exact c4⟩
  case l13 =>
    fq' hI.l13
    · simp [L']
    · intro h1 h2 h3
      obtain ⟨q', o', c1, c2, c3⟩ := hI.l13 q h1 h2 h3
      exact ⟨q', o', hdef c1, c2, by rw [hme]; exact c3⟩
  case ret => fq hI.ret; simp [L']
  case lin_written =>
    intro q k o' h
    obtain ⟨τ, hτ⟩ := hI.lin_ts _ _ h
    exact (hw hτ).2 (hI.lin_written q k o' h)

/-- Distinct processes that have allocated have distinct cells; unallocated processes point to
the dummy cell. -/
lemma Inv.me_ne (hI : Inv loc pend M G) {q : P} (hq : q ≠ p) (hp : (loc p).ptr ≠ none) :
    (loc q).me ≠ (loc p).me := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨n, rfl, -⟩ := hI.ptr p x hx
  intro h
  cases hy : (loc q).ptr with
  | none => simp [Loc.me, hy, hx] at h
  | some y =>
    simp only [Loc.me, hy, hx, Option.getD_some] at h
    subst h; exact hq (hI.ptr_inj q p _ hy hx)

lemma Inv.me_ne_bot (hI : Inv loc pend M G) (hp : (loc p).ptr ≠ none) : (loc p).me ≠ ⊥ := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨n, rfl, -⟩ := hI.ptr p x hx
  simp [Loc.me, hx]

/-- `ts` is injective on the current operation. -/
lemma Inv.ts_cur_inj (hI : Inv loc pend M G) {τ τ' : ℕ} {q : P} {o o' : T.Op}
    (h : G.ts τ = some (q, G.k q, o)) (h' : G.ts τ' = some (q, G.k q, o')) : τ = τ' :=
  (hI.ts_cur τ q o h).2.2.symm.trans (hI.ts_cur τ' q o' h').2.2

/-- Line 4: initialize the own cell. -/
lemma Inv.tau_l4 (hI : Inv loc pend M G) {o : T.Op} (ho : pend p = some o)
    (hpc : (loc p).pc = .l4) :
    Inv (Function.update loc p { loc p with pc := .l5 }) pend
      { M with cell := Function.update M.cell (loc p).me ⟨(loc p).t, .null⟩ } G := by
  set L' : Loc T := { loc p with pc := .l5 } with hL'
  set M' : Mem T := { M with cell := Function.update M.cell (loc p).me ⟨(loc p).t, .null⟩ } with hM'
  have hp : pend p ≠ none := by simp [ho]
  have hptr : L'.ptr = (loc p).ptr := rfl
  have hme := me_upd hptr
  have hpp : (loc p).ptr ≠ none := (hI.pc_ptr p hp).not.1 (by simp [hpc])
  have hcur := hI.cur p o ho (by simp [hpc, PC.Past3])
  have hcellq : ∀ {q}, q ≠ p → M'.cell (loc q).me = M.cell (loc q).me := fun hq => by
    simp [M', Function.update_of_ne (hI.me_ne hq hpp)]
  have hcellp : M'.cell (loc p).me = ⟨(loc p).t, .null⟩ := by simp [M']
  have hdummy : M'.cell ⊥ = M.cell ⊥ := by
    simp [M', Function.update_of_ne (hI.me_ne_bot hpp).symm]
  have hnw : ¬ WrittenAt loc G p (G.k p) := by simp [WrittenAt, hpc]
  have hwmono : ∀ {q k}, WrittenAt loc G q k → WrittenAt (Function.update loc p L') G q k := by
    intro q k h; unfold WrittenAt at *
    rcases eq_or_ne q p with rfl | hq
    · simp [L']
    · rw [upd_ne hq]; exact h
  -- old operations of `p` are done (with a response in `lin`)
  have hold : ∀ {τ k o'}, G.ts τ = some (p, k, o') → k < G.k p →
      M.cell (loc p).me ≠ ⟨τ, .null⟩ ∧ ∃ r, linResp T G.lin (p, k) = some r := by
    intro τ k o' h hk
    obtain ⟨c1, c2, c3⟩ := hI.cell τ p k o' h (Or.inl hk)
    rcases lt_or_eq_of_le c1 with h' | h'
    · exact ⟨fun he => by rw [he] at h'; exact lt_irrefl _ h', (c2 h').2⟩
    · rcases c3 h'.symm with c | ⟨r, hr, hl⟩
      · exact absurd c.2.1 hk.ne
      · exact ⟨fun he => (by rw [he] at hr; cases hr), r, hl⟩
  have hd : ∀ τ, DoneL loc M G τ → DoneL (Function.update loc p L') M' G τ := by
    rintro τ (h | ⟨q, k, o', h1, h2, h3⟩)
    · exact Or.inl h
    · refine Or.inr ⟨q, k, o', h1, hwmono h2, ?_⟩
      rw [hme]
      rcases eq_or_ne q p with rfl | hq
      · rw [hcellp]
        have hk : k < G.k q := by
          rcases h2 with h2 | h2
          · exact h2
          · exact absurd hpc h2
        intro he; simp only [CellVal.mk.injEq] at he
        have := hI.ts_mono τ (loc q).t q k (G.k q) o' o h1 hcur hk; omega
      · rw [hcellq hq]; exact h3
  constructor
  all_goals try simp only [hme, ptr_upd hptr, t_upd (L' := L') rfl, op_upd (L' := L') rfl]
  all_goals try inv_triv
  case pc_ptr => fq hI.pc_ptr; simpa [L', hpc] using hI.pc_ptr q
  case op => fq hI.op; simpa [L'] using hI.op q
  case cur => fq hI.cur; simpa [L', hpc, PC.Past3] using hI.cur q
  case ts_cur =>
    intro τ q o' h; obtain ⟨c1, c2, c3⟩ := hI.ts_cur τ q o' h
    rcases eq_or_ne q p with rfl | hq
    · simp_all [L', PC.Past3]
    · simp [upd_ne hq, c1, c2, c3]
  case dummy => rw [hdummy]; exact hI.dummy
  case cell =>
    intro τ q k o' h hw'
    rcases eq_or_ne q p with rfl | hq
    · rw [hcellp]
      rcases lt_or_eq_of_le (hI.ts_k τ q k o' h) with hk | hk
      · have hlt := hI.ts_mono τ (loc q).t q k (G.k q) o' o h hcur hk
        obtain ⟨-, r, hr⟩ := hold h hk
        exact ⟨hlt.le, fun _ => ⟨hk, r, hr⟩, fun h' => absurd h' hlt.ne'⟩
      · subst hk
        have : τ = (loc q).t := hI.ts_cur_inj h hcur
        subst this
        exact ⟨le_rfl, fun h' => absurd h' (lt_irrefl _),
          fun _ => Or.inl ⟨rfl, rfl, by simp [L', PC.Loop]⟩⟩
    · rw [hcellq hq]
      have hw'' : WrittenAt loc G q k := by unfold WrittenAt at hw' ⊢; rwa [upd_ne hq] at hw'
      obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o' h hw''
      exact ⟨c1, c2, by rw [upd_ne hq]; exact c3⟩
  case lin_done =>
    intro τ q k o' h hm hc hw'
    rcases eq_or_ne q p with rfl | hq
    · rw [hcellp] at hc; simp only [CellVal.mk.injEq, and_true] at hc
      subst hc
      have hk : k = G.k q := by
        rcases lt_or_eq_of_le (hI.ts_k _ q k o' h) with hk | hk
        · have := hI.ts_mono _ _ q k (G.k q) o' o h hcur hk; omega
        · exact hk
      subst hk
      obtain ⟨⟨⟨q₀, k₀⟩, o''⟩, hmem, hx⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact absurd (hI.lin_written _ _ _ hmem) hnw
    · rw [hcellq hq] at hc
      have hw'' : WrittenAt loc G q k := by unfold WrittenAt at hw' ⊢; rwa [upd_ne hq] at hw'
      exact hI.lin_done τ q k o' h hm hc hw''
  case S_pos =>
    intro h0; obtain ⟨q, k, o', h1, h2, h3, h4, h5⟩ := hI.S_pos h0
    exact ⟨q, k, o', h1, hwmono h2, h3, h4, h5⟩
  case A_pos =>
    intro h0; obtain ⟨q, k, o', h1, h2, h3, h4⟩ := hI.A_pos h0
    exact ⟨q, k, o', h1, hwmono h2, h3, h4⟩
  case snap_zero => fq hI.snap_zero; simp [L', PC.HasSnap]
  case snap_pos =>
    fq' hI.snap_pos
    · simp [L', PC.HasSnap]
    · intro h1 h2 h3
      obtain ⟨q', k, o', c1, c2, c3, c4⟩ := hI.snap_pos q h1 h2 h3
      exact ⟨q', k, o', c1, hwmono c2, c3, c4⟩
  case copied =>
    fq' hI.copied
    · simp [L', PC.Copied]
    · intro h1 h2 h3; exact hd _ (hI.copied q h1 h2 h3)
  case ann_zero => fq hI.ann_zero; simp [L', PC.HasAnn]
  case ann_pos =>
    fq' hI.ann_pos
    · simp [L', PC.HasAnn]
    · intro h1 h2 h3
      obtain ⟨q', k, o', c1, c2, c3, c4⟩ := hI.ann_pos q h1 h2 h3
      exact ⟨q', k, o', c1, hwmono c2, c3, c4⟩
  case l13 =>
    fq' hI.l13
    · simp [L']
    · intro h1 h2 h3
      obtain ⟨q', o', c1, c2, c3⟩ := hI.l13 q h1 h2 h3
      have hq' : q' ≠ p := by
        rintro rfl
        have hann : (loc q).ann.time ≠ 0 := by
          intro h0; have := (hI.ts_range (loc q).ann.time).1 (by simp [c1]); omega
        obtain ⟨q'', k'', o'', d1, d2, -⟩ := hI.ann_pos q h1 (by simp [h2, PC.HasAnn]) hann
        rw [c1] at d1; simp only [Option.some.injEq, Prod.mk.injEq] at d1
        obtain ⟨rfl, rfl, rfl⟩ := d1
        exact hnw d2
      exact ⟨q', o', c1, c2, by rw [hcellq hq']; exact c3⟩
  case ret => fq hI.ret; simp [L']
  case lin_written => intro q k o' h; exact hwmono (hI.lin_written q k o' h)

open Classical in
/-- Line 7: copy the response of the operation in `S` into its cell. -/
lemma Inv.tau_l7 (hI : Inv loc pend M G) (hp : pend p ≠ none) (hpc : (loc p).pc = .l7) :
    Inv (Function.update loc p { loc p with pc := .l8 }) pend { M with cell := (Function.update
      M.cell (loc p).snap.ptr (cellCAS (M.cell (loc p).snap.ptr) ⟨(loc p).snap.time, .null⟩
        ⟨(loc p).snap.time, (loc p).snap.resp⟩)) } G := by
  set sn := (loc p).snap with hsn
  set c' : CellVal T.Resp := cellCAS (M.cell sn.ptr) ⟨sn.time, .null⟩ ⟨sn.time, sn.resp⟩ with hc'
  have hsnap := hI.snap_zero p hp (by simp [hpc, PC.HasSnap])
  have hsnap' := hI.snap_pos p hp (by simp [hpc, PC.HasSnap])
  by_cases hsucc : M.cell sn.ptr = ⟨sn.time, .null⟩
  swap
  · -- the CAS fails: memory unchanged
    have hc : c' = M.cell sn.ptr := by simp [c', cellCAS, hsucc]
    have hM : { M with cell := Function.update M.cell sn.ptr c' } = M := by
      rw [hc, Function.update_eq_self]
    rw [hM]
    refine hI.pc_move hp (by simp [hpc, PC.Past3]) (by simp [PC.Past3]) (by simp [hpc])
      (by simp) (by simp [hpc, PC.Loop]) (Or.inl (by simp [PC.Loop])) (by simp [hpc, PC.HasSnap])
      ?_ (by simp [PC.HasAnn]) (by simp) (by simp)
    intro _ _
    by_cases h0 : sn.time = 0
    · exact Or.inl h0
    · obtain ⟨q', k, o, h1, h2, h3, -⟩ := hsnap' h0
      exact Or.inr ⟨q', k, o, h1, h2, by rw [← h3]; exact hsucc⟩
  -- the CAS succeeds
  have h0 : sn.time ≠ 0 := by
    intro h0; obtain ⟨hb, -⟩ := hsnap h0
    rw [hb, hI.dummy] at hsucc; simp [h0] at hsucc
  obtain ⟨q', k, o, h1, h2, h3, r, h4, h5⟩ := hsnap' h0
  rw [← hsn] at h1 h3 h4
  have hc : c' = ⟨sn.time, .val r⟩ := by simp [c', cellCAS, hsucc, h4]
  have hq'p : (loc q').ptr ≠ none := hI.ts_ptr _ q' k o h1
  set M' : Mem T := { M with cell := Function.update M.cell sn.ptr c' } with hM'
  have hcq' : M'.cell (loc q').me = ⟨sn.time, .val r⟩ := by simp [M', h3, hc]
  have hcq : ∀ {q}, q ≠ q' → M'.cell (loc q).me = M.cell (loc q).me := fun hq => by
    simp [M', h3, Function.update_of_ne (hI.me_ne hq hq'p)]
  have hcb : M'.cell ⊥ = M.cell ⊥ := by
    simp [M', h3, Function.update_of_ne (hI.me_ne_bot hq'p).symm]
  have hkk : k = G.k q' := by
    obtain ⟨-, -, c3⟩ := hI.cell _ q' k o h1 h2
    rw [← h3, hsucc] at c3
    rcases c3 rfl with c | ⟨r', c, -⟩
    · exact c.2.1
    · cases c
  have hd : ∀ τ, DoneL loc M G τ → DoneL loc M' G τ := by
    rintro τ (h | ⟨q, k', o', d1, d2, d3⟩)
    · exact Or.inl h
    · refine Or.inr ⟨q, k', o', d1, d2, ?_⟩
      rcases eq_or_ne q q' with rfl | hq
      · rw [hcq']; simp
      · rw [hcq hq]; exact d3
  have hM : Inv loc pend M' G := by
    refine
      { hI with
        dummy := by rw [hcb]; exact hI.dummy
        cell := ?_
        lin_done := ?_
        copied := fun q h1 h2 h3 => hd _ (hI.copied q h1 h2 h3)
        l13 := ?_ }
    · intro τ q k' o' d1 d2
      rcases eq_or_ne q q' with rfl | hq
      · rw [hcq']
        obtain ⟨c1, c2, c3⟩ := hI.cell τ q k' o' d1 d2
        rw [← h3, hsucc] at c1 c2 c3
        refine ⟨c1, c2, fun ht => Or.inr ⟨r, rfl, ?_⟩⟩
        simp only at ht; subst ht
        rw [h1] at d1; simp only [Option.some.injEq, Prod.mk.injEq] at d1
        obtain ⟨-, rfl, -⟩ := d1; exact h5
      · rw [hcq hq]; exact hI.cell τ q k' o' d1 d2
    · intro τ q k' o' d1 d2 d3 d4
      rcases eq_or_ne q q' with rfl | hq
      · rw [hcq'] at d3; simp at d3
      · rw [hcq hq] at d3; exact hI.lin_done τ q k' o' d1 d2 d3 d4
    · intro q d1 d2 d3
      obtain ⟨q'', o'', e1, e2, e3⟩ := hI.l13 q d1 d2 d3
      refine ⟨q'', o'', e1, e2, ?_⟩
      rcases eq_or_ne q'' q' with rfl | hq
      · exfalso
        rw [← h3, hsucc] at e3; simp only [CellVal.mk.injEq, and_true] at e3
        rw [← e3, h1] at e1; simp only [Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨-, rfl, -⟩ := e1
        exact e2 (ObjSpec.mem_of_respIn_eq_some h5)
      · rw [hcq hq]; exact e3
  refine hM.pc_move hp (by simp [hpc, PC.Past3]) (by simp [PC.Past3]) (by simp [hpc])
    (by simp) (by simp [hpc, PC.Loop]) (Or.inl (by simp [PC.Loop])) (by simp [hpc, PC.HasSnap])
    ?_ (by simp [PC.HasAnn]) (by simp) (by simp)
  intro _ _
  exact Or.inr ⟨q', k, o, h1, h2, by rw [hcq']; simp⟩

/-- The value `S` takes after a successful CAS on line 13 differs from every local copy `snap`
(the new operation is not yet linearized, the operations of the copies are). -/
lemma Inv.newS_ne (hI : Inv loc pend M G) {q' : P} {o' : T.Op} {τ : ℕ}
    (hts : G.ts τ = some (q', G.k q', o')) (hnot : (q', G.k q') ∉ G.lin.map Prod.fst)
    {q : P} (hq : pend q ≠ none) (hs : (loc q).pc.HasSnap) : τ ≠ (loc q).snap.time := by
  intro h
  have hτ : τ ≠ 0 := by intro h0; have := (hI.ts_range τ).1 (by simp [hts]); omega
  rw [h] at hτ hts
  obtain ⟨q'', k, o, d1, -, -, r, -, d2⟩ := hI.snap_pos q hq hs hτ
  rw [hts] at d1; simp only [Option.some.injEq, Prod.mk.injEq] at d1
  obtain ⟨rfl, rfl, rfl⟩ := d1
  exact hnot (ObjSpec.mem_of_respIn_eq_some d2)

open Classical in
/-- Line 13: try to linearize the announced operation by a CAS on `S`. -/
lemma Inv.tau_l13 (hI : Inv loc pend M G) (hp : pend p ≠ none) (hpc : (loc p).pc = .l13) :
    Inv (Function.update loc p { loc p with pc := .l5 }) pend
      { M with S := if M.S = (loc p).snap then (loc p).newS else M.S }
      (if M.S = (loc p).snap then
        match G.ts (loc p).ann.time with
        | some (q, k, o) => { G with lin := G.lin ++ [((q, k), o)] }
        | none => G
      else G) := by
  by_cases hS : M.S = (loc p).snap
  swap
  · simp only [hS, if_false]
    exact hI.pc_move hp (by simp [hpc, PC.Past3]) (by simp [PC.Past3]) (by simp [hpc])
      (by simp) (by simp [hpc, PC.Loop]) (Or.inl (by simp [PC.Loop])) (by simp [PC.HasSnap])
      (by simp [PC.Copied]) (by simp [PC.HasAnn]) (by simp) (by simp)
  simp only [hS, if_true]
  obtain ⟨q', o', hts, hnot, hcell⟩ := hI.l13 p hp hpc hS
  simp only [hts]
  have hτ : (loc p).ann.time ≠ 0 := by
    intro h0; have := (hI.ts_range (loc p).ann.time).1 (by simp [hts]); omega
  obtain ⟨q', k'', o', d1, hw, hop, hptr⟩ := hI.ann_pos p hp (by simp [hpc, PC.HasAnn]) hτ
  rw [hts] at d1; simp only [Option.some.injEq, Prod.mk.injEq] at d1
  obtain ⟨rfl, rfl, rfl⟩ := d1
  set x : OpId P := (q', G.k q') with hx
  set G' : Ghost T P := { G with lin := G.lin ++ [(x, o')] } with hG'
  set M' : Mem T := { M with S := (loc p).newS } with hM'
  have hst : M.S.state = T.runOps T.init (G.lin.map Prod.snd) := hI.S_state
  have hnewS : (loc p).newS = ⟨(loc p).ann.time, (T.δ M.S.state o').1, .val (T.δ M.S.state o').2,
      (loc q').me⟩ := by
    simp [Loc.newS, hop, applyT, hptr, hS]
  have hlr : ∀ {y r}, linResp T G.lin y = some r → linResp T G'.lin y = some r :=
    fun h => ObjSpec.respIn_append_of_eq_some h _
  have hne : ∀ {q}, pend q ≠ none → (loc q).pc.HasSnap → M'.S ≠ (loc q).snap := by
    intro q hq hs he
    exact hI.newS_ne hts hnot hq hs (by rw [← he]; simp [M', hnewS])
  have hM : Inv loc pend M' G' := by
    refine
      { hI with
        cell := ?_
        lin_nodup := ?_
        lin_ts := ?_
        lin_done := ?_
        S_state := ?_
        S_zero := ?_
        S_pos := ?_
        snap_pos := ?_
        copied := fun q h1 h2 h3 => absurd h3 (hne h1 (by
          revert h2; generalize (loc q).pc = c; cases c <;> simp [PC.Copied, PC.HasSnap]))
        l13 := fun q h1 h2 h3 => absurd h3 (hne h1 (by simp [h2, PC.HasSnap]))
        ret := fun q r h1 h2 => hlr (hI.ret q r h1 h2)
        lin_written := ?_ }
    · intro τ q k o d1 d2
      obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o d1 d2
      refine ⟨c1, fun h => ?_, fun h => ?_⟩
      · obtain ⟨a, r, b⟩ := c2 h; exact ⟨a, r, hlr b⟩
      · rcases c3 h with c | ⟨r, c, d⟩
        · exact Or.inl c
        · exact Or.inr ⟨r, c, hlr d⟩
    · simp only [G', List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨hI.lin_nodup, List.nodup_singleton _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb
      exact fun h => hnot (h ▸ ha)
    · intro y o d1
      simp only [G', List.mem_append, List.mem_singleton] at d1
      rcases d1 with d1 | d1
      · exact hI.lin_ts y o d1
      · simp only [Prod.mk.injEq] at d1; obtain ⟨rfl, rfl⟩ := d1; exact ⟨_, hts⟩
    · intro τ q k o d1 d2 d3 d4
      simp only [G', List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_singleton] at d2
      rcases d2 with d2 | d2
      · -- an old entry whose response is not copied would be the operation of `snap`
        exfalso
        have hSt := hI.lin_done τ q k o d1 d2 d3 d4
        have hd := hI.copied p hp (by simp [hpc, PC.Copied]) hS
        rw [← hS, hSt] at hd
        rcases hd with h0 | ⟨q₁, k₁, o₁, e1, -, e3⟩
        · have := (hI.ts_range τ).1 (by simp only [G'] at d1; simp [d1]); omega
        · rw [d1] at e1; simp only [Option.some.injEq, Prod.mk.injEq] at e1
          obtain ⟨rfl, rfl, rfl⟩ := e1; exact e3 d3
      · simp only [x, Prod.mk.injEq] at d2; obtain ⟨rfl, rfl⟩ := d2
        simp only [M', hnewS]
        exact hI.ts_cur_inj hts d1
    · simp only [M', G', hnewS, List.map_append, List.map_cons, List.map_nil, ObjSpec.runOps_append,
        hst]
      rfl
    · simp [M', hnewS, hτ]
    · intro _
      refine ⟨q', G.k q', o', hts, hw, ?_, by simp [M', hnewS], (T.δ M.S.state o').2,
        by simp [M', hnewS], ?_⟩
      · simp [G', x]
      · simp only [G']; rw [← hx, linResp, ObjSpec.respIn_concat_self hnot, ← hst]
    · intro q h1 h2 h3
      obtain ⟨a, b, c, d, e, f, r, g, h⟩ := hI.snap_pos q h1 h2 h3
      exact ⟨a, b, c, d, e, f, r, g, hlr h⟩
    · intro q k o d
      simp only [G', List.mem_append, List.mem_singleton] at d
      rcases d with d | d
      · exact hI.lin_written q k o d
      · simp only [x, Prod.mk.injEq] at d; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := d; exact hw
  exact hM.pc_move (pc' := .l5) hp (by simp [hpc, PC.Past3]) (by simp [PC.Past3]) (by simp [hpc])
    (by simp) (by simp [hpc, PC.Loop]) (Or.inl (by simp [PC.Loop])) (by simp [PC.HasSnap])
    (by simp [PC.Copied]) (by simp [PC.HasAnn]) (by simp) (by simp)

/-- An invocation. -/
lemma Inv.inv_step (hI : Inv loc pend M G) {o : T.Op} (hp : pend p = none) :
    Inv (Function.update loc p ((loc p).invoke o)) (Function.update pend p (some o)) M G := by
  set L' : Loc T := (loc p).invoke o with hL'
  have hptr : L'.ptr = (loc p).ptr := rfl
  have hme := me_upd hptr
  have hpc' : L'.pc = .l2 ∨ L'.pc = .l3 := by
    simp only [L', Loc.invoke]; split_ifs <;> simp
  have hnc : ∀ {τ q o'}, G.ts τ = some (q, G.k q, o') → q ≠ p := by
    rintro τ q o' h rfl; have := (hI.ts_cur τ q o' h).1; rw [hp] at this; cases this
  have hlt : ∀ {τ k o'}, G.ts τ = some (p, k, o') → k < G.k p := by
    intro τ k o' h
    rcases lt_or_eq_of_le (hI.ts_k τ p k o' h) with h' | h'
    · exact h'
    · subst h'; exact absurd rfl (hnc h)
  have hw : ∀ {τ q k o'}, G.ts τ = some (q, k, o') →
      (WrittenAt (Function.update loc p L') G q k ↔ WrittenAt loc G q k) := by
    intro τ q k o' h; unfold WrittenAt
    rcases eq_or_ne q p with rfl | hq
    · simp [hlt h]
    · simp [upd_ne hq]
  have hd : ∀ τ, DoneL loc M G τ → DoneL (Function.update loc p L') M G τ := by
    rintro τ (h | ⟨q, k, o', h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, k, o', h1, (hw h1).2 h2, by rwa [hme]⟩
  have hpq : ∀ {q}, q ≠ p → Function.update pend p (some o) q = pend q := fun hq => by
    simp [Function.update_of_ne hq]
  constructor
  case cnt_pos => exact hI.cnt_pos
  case ptr => intro q x h; rw [ptr_upd hptr] at h; exact hI.ptr q x h
  case ptr_inj => intro q q' x h h'; rw [ptr_upd hptr] at h h'; exact hI.ptr_inj q q' x h h'
  case pc_ptr =>
    fq' hI.pc_ptr
    · intro _; simp only [Function.update_self, L', Loc.invoke]; split_ifs with h <;> simp [h]
    · exact hI.pc_ptr q
  case op =>
    fq' hI.op
    · intro o' h; simp at h; subst h; simp [L', Loc.invoke]
    · exact hI.op q
  case cur =>
    fq' hI.cur
    · intro _ _ h; simp only [Function.update_self] at h
      rcases hpc' with h' | h' <;> rw [h'] at h <;> exact absurd h id
    · exact hI.cur q
  case ts_range => exact hI.ts_range
  case ts_k => exact hI.ts_k
  case ts_cur =>
    intro τ q o' h; rw [upd_ne (hnc h), hpq (hnc h)]; exact hI.ts_cur τ q o' h
  case ts_mono => exact hI.ts_mono
  case ts_ptr => intro τ q k o' h; rw [ptr_upd hptr]; exact hI.ts_ptr τ q k o' h
  case dummy => exact hI.dummy
  case cell =>
    intro τ q k o' h hw'
    rw [hme]; obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o' h ((hw h).1 hw')
    refine ⟨c1, c2, fun ht => ?_⟩
    rcases c3 ht with c | c
    · left; refine ⟨c.1, c.2.1, ?_⟩
      rcases eq_or_ne q p with rfl | hq
      · exact absurd c.2.1 (hlt h).ne
      · rw [upd_ne hq]; exact c.2.2
    · exact Or.inr c
  case lin_nodup => exact hI.lin_nodup
  case lin_ts => exact hI.lin_ts
  case lin_done =>
    intro τ q k o' h hm hc hw'; rw [hme] at hc
    exact hI.lin_done τ q k o' h hm hc ((hw h).1 hw')
  case S_state => exact hI.S_state
  case S_zero => exact hI.S_zero
  case S_pos =>
    intro h0; obtain ⟨q, k, o', h1, h2, h3, h4, h5⟩ := hI.S_pos h0
    exact ⟨q, k, o', h1, (hw h1).2 h2, h3, by rw [hme]; exact h4, h5⟩
  case A_zero => exact hI.A_zero
  case A_pos =>
    intro h0; obtain ⟨q, k, o', h1, h2, h3, h4⟩ := hI.A_pos h0
    exact ⟨q, k, o', h1, (hw h1).2 h2, h3, by rw [hme]; exact h4⟩
  case snap_zero =>
    fq' hI.snap_zero
    · intro _ h; simp only [Function.update_self] at h
      rcases hpc' with h' | h' <;> rw [h'] at h <;> exact absurd h id
    · exact hI.snap_zero q
  case snap_pos =>
    fq' hI.snap_pos
    · intro _ h; simp only [Function.update_self] at h
      rcases hpc' with h' | h' <;> rw [h'] at h <;> exact absurd h id
    · intro h1 h2 h3
      obtain ⟨q', k, o', c1, c2, c3, c4⟩ := hI.snap_pos q h1 h2 h3
      exact ⟨q', k, o', c1, (hw c1).2 c2, by rw [hme]; exact c3, c4⟩
  case copied =>
    fq' hI.copied
    · intro _ h; simp only [Function.update_self] at h
      rcases hpc' with h' | h' <;> rw [h'] at h <;> exact absurd h id
    · intro h1 h2 h3; exact hd _ (hI.copied q h1 h2 h3)
  case ann_zero =>
    fq' hI.ann_zero
    · intro _ h; simp only [Function.update_self] at h
      rcases hpc' with h' | h' <;> rw [h'] at h <;> exact absurd h id
    · exact hI.ann_zero q
  case ann_pos =>
    fq' hI.ann_pos
    · intro _ h; simp only [Function.update_self] at h
      rcases hpc' with h' | h' <;> rw [h'] at h <;> exact absurd h id
    · intro h1 h2 h3
      obtain ⟨q', k, o', c1, c2, c3, c4⟩ := hI.ann_pos q h1 h2 h3
      exact ⟨q', k, o', c1, (hw c1).2 c2, c3, by rw [hme]; exact c4⟩
  case l13 =>
    fq' hI.l13
    · intro _ h; simp only [Function.update_self] at h
      rcases hpc' with h' | h' <;> rw [h'] at h <;> cases h
    · intro h1 h2 h3
      obtain ⟨q', o', c1, c2, c3⟩ := hI.l13 q h1 h2 h3
      exact ⟨q', o', c1, c2, by rw [hme]; exact c3⟩
  case ret =>
    fq' hI.ret
    · intro r _ h; simp only [Function.update_self] at h
      rcases hpc' with h' | h' <;> rw [h'] at h <;> cases h
    · exact hI.ret q
  case lin_written =>
    intro q k o' h
    obtain ⟨τ, hτ⟩ := hI.lin_ts _ _ h
    exact (hw hτ).2 (hI.lin_written q k o' h)

/-- A response (line 16). -/
lemma Inv.ret_step (hI : Inv loc pend M G) (hp : pend p ≠ none) {r : T.Resp}
    (hpc : (loc p).pc = .l16 r) :
    Inv (Function.update loc p { loc p with pc := .l2 }) (Function.update pend p none) M
      { G with k := Function.update G.k p (G.k p + 1) } := by
  set L' : Loc T := { loc p with pc := .l2 } with hL'
  set G' : Ghost T P := { G with k := Function.update G.k p (G.k p + 1) } with hG'
  have hptr : L'.ptr = (loc p).ptr := rfl
  have hme := me_upd hptr
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hp
  have hcur := hI.cur p o ho (by simp [hpc, PC.Past3])
  have hret := hI.ret p r hp hpc
  -- the own cell holds the response
  have hcellp : M.cell (loc p).me = ⟨(loc p).t, .val r⟩ := by
    obtain ⟨c1, c2, c3⟩ := hI.cell _ p _ o hcur (Or.inr (by simp [hpc]))
    have ht : (M.cell (loc p).me).time = (loc p).t := by
      rcases lt_or_eq_of_le c1 with h | h
      · exact absurd (c2 h).1 (lt_irrefl _)
      · exact h.symm
    rcases c3 ht with c | ⟨r', c, hl⟩
    · exact absurd c.2.2 (by simp [hpc, PC.Loop])
    · rw [hret] at hl; cases hl; exact CellVal.ext ht c
  have hk' : ∀ q, G'.k q = if q = p then G.k p + 1 else G.k q := by
    intro q; simp only [G', Function.update_apply]
  have hw : ∀ q k, WrittenAt (Function.update loc p L') G' q k ↔ WrittenAt loc G q k := by
    intro q k; unfold WrittenAt
    rcases eq_or_ne q p with rfl | hq
    · simp [L', G', hpc]
    · simp [G', upd_ne hq, Function.update_of_ne hq]
  have hd : ∀ τ, DoneL loc M G τ → DoneL (Function.update loc p L') M G' τ := by
    rintro τ (h | ⟨q, k, o', h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, k, o', h1, (hw q k).2 h2, by rwa [hme]⟩
  have hkq : ∀ {q}, q ≠ p → G'.k q = G.k q := fun hq => by simp [G', Function.update_of_ne hq]
  have hpq : ∀ {q}, q ≠ p → Function.update pend p none q = pend q := fun hq => by
    simp [Function.update_of_ne hq]
  constructor
  case cnt_pos => exact hI.cnt_pos
  case ptr => intro q x h; rw [ptr_upd hptr] at h; exact hI.ptr q x h
  case ptr_inj => intro q q' x h h'; rw [ptr_upd hptr] at h h'; exact hI.ptr_inj q q' x h h'
  case pc_ptr =>
    fq' hI.pc_ptr
    · simp
    · exact hI.pc_ptr q
  case op =>
    fq' hI.op
    · simp
    · exact hI.op q
  case cur =>
    fq' hI.cur
    · simp
    · rw [hkq hq]; exact hI.cur q
  case ts_range => exact hI.ts_range
  case ts_k =>
    intro τ q k o' h; have := hI.ts_k τ q k o' h
    rcases eq_or_ne q p with rfl | hq
    · simp [G']; omega
    · rw [hkq hq]; exact this
  case ts_cur =>
    intro τ q o' h
    rcases eq_or_ne q p with rfl | hq
    · have := hI.ts_k τ q _ o' h; simp [G'] at this
    · rw [hkq hq] at h; rw [upd_ne hq, hpq hq]; exact hI.ts_cur τ q o' h
  case ts_mono => exact hI.ts_mono
  case ts_ptr => intro τ q k o' h; rw [ptr_upd hptr]; exact hI.ts_ptr τ q k o' h
  case dummy => exact hI.dummy
  case cell =>
    intro τ q k o' h hw'
    rw [hme]; obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o' h ((hw q k).1 hw')
    have hle : G.k q ≤ G'.k q := by
      rcases eq_or_ne q p with rfl | hq
      · simp [G']
      · rw [hkq hq]
    refine ⟨c1, fun h' => ?_, fun ht => ?_⟩
    · obtain ⟨a, b⟩ := c2 h'; exact ⟨lt_of_lt_of_le a hle, b⟩
    · rcases c3 ht with c | c
      · rcases eq_or_ne q p with rfl | hq
        · exact absurd c.2.2 (by simp [hpc, PC.Loop])
        · left; rw [upd_ne hq, hkq hq]; exact c
      · exact Or.inr c
  case lin_nodup => exact hI.lin_nodup
  case lin_ts => exact hI.lin_ts
  case lin_done =>
    intro τ q k o' h hm hc hw'; rw [hme] at hc
    exact hI.lin_done τ q k o' h hm hc ((hw q k).1 hw')
  case S_state => exact hI.S_state
  case S_zero => exact hI.S_zero
  case S_pos =>
    intro h0; obtain ⟨q, k, o', h1, h2, h3, h4, h5⟩ := hI.S_pos h0
    exact ⟨q, k, o', h1, (hw q k).2 h2, h3, by rw [hme]; exact h4, h5⟩
  case A_zero => exact hI.A_zero
  case A_pos =>
    intro h0; obtain ⟨q, k, o', h1, h2, h3, h4⟩ := hI.A_pos h0
    exact ⟨q, k, o', h1, (hw q k).2 h2, h3, by rw [hme]; exact h4⟩
  case snap_zero =>
    fq' hI.snap_zero
    · simp
    · exact hI.snap_zero q
  case snap_pos =>
    fq' hI.snap_pos
    · simp
    · intro h1 h2 h3
      obtain ⟨q', k, o', c1, c2, c3, c4⟩ := hI.snap_pos q h1 h2 h3
      exact ⟨q', k, o', c1, (hw q' k).2 c2, by rw [hme]; exact c3, c4⟩
  case copied =>
    fq' hI.copied
    · simp
    · intro h1 h2 h3; exact hd _ (hI.copied q h1 h2 h3)
  case ann_zero =>
    fq' hI.ann_zero
    · simp
    · exact hI.ann_zero q
  case ann_pos =>
    fq' hI.ann_pos
    · simp
    · intro h1 h2 h3
      obtain ⟨q', k, o', c1, c2, c3, c4⟩ := hI.ann_pos q h1 h2 h3
      exact ⟨q', k, o', c1, (hw q' k).2 c2, c3, by rw [hme]; exact c4⟩
  case l13 =>
    fq' hI.l13
    · simp
    · intro h1 h2 h3
      obtain ⟨q', o', c1, c2, c3⟩ := hI.l13 q h1 h2 h3
      have hq' : q' ≠ p := by
        rintro rfl; rw [hcellp] at c3; simp at c3
      exact ⟨q', o', by rw [hkq hq']; exact c1, by rw [hkq hq']; exact c2, by rw [hme]; exact c3⟩
  case ret =>
    fq' hI.ret
    · simp
    · rw [hkq hq]; exact hI.ret q
  case lin_written => intro q k o' h; exact (hw q k).2 (hI.lin_written q k o' h)

end steps


/-! ## The invariant holds in every reachable state -/

section reach

variable (cellInit : ℕ → CellVal T.Resp)

lemma cinv_init : CInv (alg T P cellInit).initCfg (ginit T P) := by
  constructor <;> simp [Impl.initCfg, alg, ginit, Cfg.M, view, WrittenAt, DoneL] <;> (try intros) <;>
    (try simp_all) <;> omega

/-- **The invariant is preserved by every step.** -/
theorem CInv.step {C C' : Cfg T P} {G : Ghost T P} (hI : CInv C G) {ℓ : Label P T}
    (h : (alg T P cellInit).step C ℓ = some C') : CInv C' (augStep C ℓ G) := by
  cases ℓ with
  | inv p o =>
    obtain ⟨hp, hpend, hmem, hloc⟩ := step_inv_eff cellInit h
    have hM : C'.M = C.M := by simp [Cfg.M, hmem]
    simp only [CInv, hpend, hloc, hM]
    exact inv_ghost_congr (G := G) (G' := augStep C (.inv p o) G) rfl rfl rfl (hI.inv_step hp)
  | ret p r =>
    obtain ⟨hp, hpc, hpend, hmem, hloc⟩ := step_ret_eff cellInit h
    have hM : C'.M = C.M := by simp [Cfg.M, hmem]
    simp only [CInv, hpend, hloc, hM]
    exact inv_ghost_congr (G := { G with k := Function.update G.k p (G.k p + 1) })
      (G' := augStep C (.ret p r) G) rfl rfl rfl (hI.ret_step hp hpc)
  | tau p =>
    obtain ⟨hp, hmemS, hpend, hM, hloc⟩ := step_tau_eff cellInit h
    simp only [CInv, hpend, hM, hloc]
    cases hpc : (C.loc p).pc with
    | l2 => simp only [effect, hpc]; exact inv_ghost_congr (by simp [augStep, hpc])
              (by simp [augStep, hpc]) (by simp [augStep, hpc]) (hI.tau_l2 hp hpc)
    | l3 =>
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hp
      simp only [effect, hpc]
      exact inv_ghost_congr (by simp [augStep, hpc, ho]) (by simp [augStep, hpc])
        (by simp [augStep, hpc]) (hI.tau_l3 ho hpc)
    | l4 =>
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hp
      simp only [effect, hpc]
      exact inv_ghost_congr (by simp [augStep, hpc]) (by simp [augStep, hpc])
        (by simp [augStep, hpc]) (hI.tau_l4 ho hpc)
    | l5 => simp only [effect, hpc]; exact inv_ghost_congr (by simp [augStep, hpc])
              (by simp [augStep, hpc]) (by simp [augStep, hpc]) (hI.tau_l5 hp hpc)
    | l6 => simp only [effect, hpc]; exact inv_ghost_congr (by simp [augStep, hpc])
              (by simp [augStep, hpc]) (by simp [augStep, hpc]) (hI.tau_l6 hp hpc)
    | l7 => simp only [effect, hpc]; exact inv_ghost_congr (by simp [augStep, hpc])
              (by simp [augStep, hpc]) (by simp [augStep, hpc]) (hI.tau_l7 hp hpc)
    | l8 =>
      simp only [effect, hpc]
      refine inv_ghost_congr (by simp only [augStep, hpc]; split_ifs <;> rfl)
        (by simp only [augStep, hpc]; split_ifs <;> rfl)
        (by simp only [augStep, hpc]; split_ifs <;> rfl)
        (hI.write_A hp (by simp [hpc, PC.Past3]) (by simp [hpc]) (by simp [PC.Past3]) (by simp)
          (by simp [PC.Loop]) (by simp [hpc, PC.HasSnap]) (by simp [hpc, PC.Copied])
          (by simp [PC.HasAnn]) (by simp) (by simp) ?_ (by simp [hpc, PC.Loop]))
      split_ifs <;> simp
    | l9 => simp only [effect, hpc]; exact inv_ghost_congr (by simp [augStep, hpc])
              (by simp [augStep, hpc]) (by simp [augStep, hpc]) (hI.tau_l9 hp hpc)
    | l10 => simp only [effect, hpc]; exact inv_ghost_congr (by simp [augStep, hpc])
              (by simp [augStep, hpc]) (by simp [augStep, hpc]) (hI.tau_l10 hp hpc)
    | l13 =>
      simp only [effect, hpc]
      refine inv_ghost_congr ?_ ?_ ?_ (hI.tau_l13 hp hpc) <;>
        (simp only [augStep, hpc]; split_ifs <;> (try (cases G.ts (C.loc p).ann.time <;> rfl)) <;> rfl)
    | l15 =>
      simp only [effect, hpc]
      refine inv_ghost_congr (by simp only [augStep, hpc]; split_ifs <;> rfl)
        (by simp only [augStep, hpc]; split_ifs <;> rfl)
        (by simp only [augStep, hpc]; split_ifs <;> rfl)
        (hI.write_A hp (by simp [hpc, PC.Past3]) (by simp [hpc]) (by simp [PC.Past3]) (by simp)
          (by simp [PC.Loop]) (by simp [PC.HasSnap]) (by simp [PC.Copied])
          (by simp [PC.HasAnn]) (by simp) (by simp) ?_ (by simp [hpc, PC.Loop]))
      split_ifs <;> simp
    | l16 r => exact absurd hpc (hmemS r)

/-- The invariant holds in every state of an augmented run. -/
theorem arun_inv {α : List (Label P T)} {C : Cfg T P} {G : Ghost T P}
    (h : arun cellInit α = some (C, G)) : CInv C G :=
  arun_induction cellInit (Q := fun _ C G => CInv C G) (cinv_init cellInit)
    (fun _ _ _ _ _ _ hI hs => hI.step cellInit hs) h

end reach

end Podc.GeneralizedCAS
