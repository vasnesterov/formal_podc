import Papers.PODC2023.DuraCAS.Model

/-!
# Wait-freedom with a constant step bound (Theorem 4.1(2) of the brief announcement)

Every operation of DuraCAS, and `RECOVER`, completes within `55` steps of the executing process
(DurEC steps included), whatever the other processes do: `rank` of the local state strictly decreases
with every step of the process (`rank_pstep_lt`), is not changed by steps of other processes
(`ps_other`), and is at most `55` (`rank_le`).
-/

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- Remaining steps of an active DurEC call. -/
def frRank (f : Frame P K V) : ℕ :=
  match f.pc with
  | .l7 => 10
  | .l8 => 9
  | .l9 _ => 8
  | .l10 _ => 7
  | .f13 => 6
  | .f14 _ => 5
  | .f15 .. => 4
  | .f16 .. => 3
  | .f17 .. => 2
  | .f18 .. => 1

/-- Remaining steps after `TRANSFER-WRITE` returns to `ret`. -/
def retRank : Ret V → ℕ
  | .casT i _ => 11 + (if i then 0 else 25)
  | .wr1 => 13
  | .wr2 => 0
  | .rec1 => 13
  | .rec2 => 0

/-- Remaining steps at a DuraCAS line without an active DurEC call. -/
def pcRank : Pc V → ℕ
  | .idle => 0
  | .read => 1
  | .cas7 i => 25 + (if i then 0 else 25)
  | .cas10 i _ => 11 + (if i then 0 else 25)
  | .wr12 => 39
  | .wr13 _ => 38
  | .wr15 _ => 37
  | .tw19 ret => 13 + retRank ret
  | .tw20 ret _ => 12 + retRank ret
  | .tw21 ret _ _ => 11 + retRank ret
  | .recv j => 6 * (4 - j.val) + 26

/-- Remaining steps after the DurEC call issued at `pc` returns. -/
def contRank : Pc V → ℕ
  | .cas10 i _ => if i then 0 else 25
  | .wr15 _ => 26
  | .tw21 ret _ _ => retRank ret
  | .recv j => 6 * (3 - j.val) + 26
  | _ => 0

/-- Remaining steps of a process (an upper bound). -/
def rank (st : PState P K V) : ℕ :=
  match st.op, st.fr with
  | none, _ => 0
  | some _, none => pcRank st.pc
  | some _, some f => frRank f + contRank st.pc

/-- A return address of `TRANSFER-WRITE` fits the operation. -/
def RetOk (r : OpRec K V) : Ret V → Prop
  | .casT _ _ => ∃ o n, r.op = .cas o n
  | _ => True

/-- Local consistency of a process state (an invariant of reachable states). -/
def Cons (st : PState P K V) : Prop :=
  match st.op with
  | none => st.pc = .idle ∧ st.fr = none
  | some r =>
    match st.pc with
    | .idle => False
    | .read => r.op = .read ∧ st.fr = none
    | .cas7 _ => (∃ o n, r.op = .cas o n) ∧ st.fr = none
    | .cas10 _ _ => (∃ o n, r.op = .cas o n) ∧ ∀ f, st.fr = some f → f.kind = .sc
    | .wr12 => (∃ v, r.op = .write v) ∧ st.fr = none
    | .wr13 _ => (∃ v, r.op = .write v) ∧ st.fr = none
    | .wr15 _ => (∃ v, r.op = .write v) ∧ ∀ f, st.fr = some f → f.kind = .sc
    | .tw19 ret => RetOk r ret ∧ st.fr = none
    | .tw20 ret _ => RetOk r ret ∧ st.fr = none
    | .tw21 ret _ _ => RetOk r ret ∧
        ∀ f, st.fr = some f → f.kind = .sc
    | .recv _ => ∀ f, st.fr = some f → f.kind = .recov


/-- The local state after a continuation. -/
def nextPS (st : PState P K V) : Next V → PState P K V
  | .go pc => { st with pc := pc, fr := none }
  | .ret _ => ⟨.idle, none, none⟩
  | .rdone => ⟨.idle, none, none⟩

omit [DecidableEq K] [DecidableEq V] in
@[simp] theorem applyNext_ps_self (s : St P K V) (p : P) (m) (n : Next V) :
    (applyNext s p m n).ps p = nextPS (s.ps p) n := by
  cases n <;> simp [applyNext, nextPS]

omit [DecidableEq K] [DecidableEq V] in
@[simp] theorem applyNext_ps_ne (s : St P K V) {p q : P} (h : q ≠ p) (m) (n : Next V) :
    (applyNext s p m n).ps q = s.ps q := by
  cases n <;> simp [applyNext, Function.update_of_ne h]

omit [DecidableEq K] [DecidableEq V] in
@[simp] theorem setFrame_ps_self (s : St P K V) (p : P) (m) (f : Frame P K V) :
    (setFrame s p m f).ps p = { s.ps p with fr := some f } := by
  simp [setFrame]

omit [DecidableEq K] [DecidableEq V] in
@[simp] theorem setFrame_ps_ne (s : St P K V) {p q : P} (h : q ≠ p) (m) (f : Frame P K V) :
    (setFrame s p m f).ps q = s.ps q := by
  simp [setFrame, Function.update_of_ne h]

/-- Steps of `p` do not change the local states of other processes. -/
theorem pstep_ps_ne (s : St P K V) {p q : P} (h : q ≠ p) : (pstep s p).ps q = s.ps q := by
  unfold pstep startSC
  simp only []
  repeat' split
  all_goals simp_all

theorem fstep_cont {m m' : Mem P K V} {f f' : Frame P K V} (h : fstep m f = (m', .cont f')) :
    frRank f' < frRank f ∧ f'.kind = f.kind := by
  unfold fstep at h
  repeat' split at h
  all_goals simp_all
  all_goals (obtain ⟨-, rfl⟩ := h; simp_all [frRank])

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
theorem frRank_pos (f : Frame P K V) : 1 ≤ frRank f := by
  unfold frRank; split <;> omega

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
@[simp] theorem nextPS_go (st : PState P K V) (pc : Pc V) :
    nextPS st (.go pc) = ⟨pc, none, st.op⟩ := rfl

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
@[simp] theorem nextPS_ret (st : PState P K V) (x : Resp V) :
    nextPS st (.ret x) = ⟨.idle, none, none⟩ := rfl

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
@[simp] theorem nextPS_rdone (st : PState P K V) :
    nextPS st .rdone = ⟨.idle, none, none⟩ := rfl

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
@[simp] theorem cons_idle : Cons (⟨.idle, none, none⟩ : PState P K V) := by simp [Cons]

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
@[simp] theorem rank_idle : rank (⟨.idle, none, none⟩ : PState P K V) = 0 := rfl

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
@[simp] theorem rank_none (pc : Pc V) (r : OpRec K V) :
    rank (⟨pc, none, some r⟩ : PState P K V) = pcRank pc := rfl

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
@[simp] theorem rank_some (pc : Pc V) (f : Frame P K V) (r : OpRec K V) :
    rank (⟨pc, some f, some r⟩ : PState P K V) = frRank f + contRank pc := rfl

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
/-- Continuations after `TRANSFER-WRITE`. -/
theorem afterTW_ok (r : OpRec K V) (fr : Option (Frame P K V)) (pc : Pc V) (ret : Ret V)
    (hr : RetOk r ret) :
    Cons (nextPS ⟨pc, fr, some r⟩ (afterTW ret)) ∧
      rank (nextPS ⟨pc, fr, some r⟩ (afterTW ret)) ≤ retRank ret := by
  cases ret with
  | casT i z =>
    obtain ⟨o, n, h⟩ := hr
    simp [afterTW, Cons, retRank, pcRank, h]
  | wr1 => simp [afterTW, Cons, retRank, pcRank, RetOk]
  | wr2 => simp [afterTW, retRank]
  | rec1 => simp [afterTW, Cons, retRank, pcRank, RetOk]
  | rec2 => simp [afterTW, retRank]

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
/-- Continuations after a DurEC call. -/
theorem afterCall_ok (r : OpRec K V) (fr : Option (Frame P K V)) (pc : Pc V) (b : Bool)
    (hc : Cons (⟨pc, some f, some r⟩ : PState P K V)) :
    Cons (nextPS ⟨pc, fr, some r⟩ (afterCall pc b)) ∧
      rank (nextPS ⟨pc, fr, some r⟩ (afterCall pc b)) ≤ contRank pc := by
  cases pc with
  | cas10 i z =>
    obtain ⟨⟨o, n, h⟩, -⟩ := hc
    cases b <;> cases i <;> simp [afterCall, Cons, contRank, pcRank, h]
  | wr15 w =>
    obtain ⟨⟨v, h⟩, -⟩ := hc
    simp [afterCall, Cons, contRank, pcRank, retRank, RetOk, h]
  | tw21 ret zh wh => exact afterTW_ok r fr _ ret hc.1
  | recv j =>
    simp only [afterCall, contRank]
    split_ifs with hj
    · simp [Cons, pcRank]
    · simp [Cons, pcRank, retRank, RetOk]
  | _ => simp [Cons] at hc

/-- Each step of a busy process strictly decreases its `rank` and preserves consistency. -/
theorem pstep_self (s : St P K V) (p : P) (hc : Cons (s.ps p)) (hb : (s.ps p).op.isSome) :
    Cons ((pstep s p).ps p) ∧ rank ((pstep s p).ps p) < rank (s.ps p) := by
  rcases hst : s.ps p with ⟨pc, fr, op⟩
  rw [hst] at hc hb
  obtain ⟨r, rfl⟩ := Option.isSome_iff_exists.1 hb
  cases fr with
  | some f =>
    rcases hf : fstep s.m f with ⟨m', res⟩
    cases res with
    | cont f' =>
      have := fstep_cont hf
      simp only [pstep, hst, hf, setFrame_ps_self]
      refine ⟨?_, by simp only [rank]; omega⟩
      cases pc <;> simp_all [Cons]
    | done b =>
      simp only [pstep, hst, hf, applyNext_ps_self, rank_some]
      have h1 := frRank_pos f
      have := afterCall_ok r (some f) pc b hc
      exact ⟨this.1, by omega⟩
  | none =>
    cases pc with
    | idle => simp [Cons] at hc
    | read =>
      simp only [pstep, hst, applyNext_ps_self]
      simp [pcRank]
    | cas7 i =>
      obtain ⟨⟨o, n, hop⟩, -⟩ := hc
      simp only [pstep, hst, hop]
      split_ifs <;> simp [Cons, pcRank, RetOk, retRank, hop, hst] <;> cases i <;> simp
    | cas10 i z =>
      obtain ⟨⟨o, n, hop⟩, -⟩ := hc
      simp only [pstep, hst, hop, startSC]
      split_ifs
      · have := afterCall_ok (f := ⟨.sc, (r.k, .Z), (p, .crit), z.1, (n, z.2.2), 0, false, .l7⟩)
          r none (.cas10 i z) false ⟨⟨o, n, hop⟩, by simp⟩
        simp only [applyNext_ps_self, hst, rank_none, pcRank]
        exact ⟨this.1, by simp [contRank] at this; omega⟩
      · simp [Cons, frRank, contRank, pcRank, hop, hst]
    | wr12 =>
      obtain ⟨⟨v, hop⟩, -⟩ := hc
      simp [pstep, hst, Cons, pcRank, hop]
    | wr13 w =>
      obtain ⟨⟨v, hop⟩, -⟩ := hc
      simp only [pstep, hst, hop]
      split_ifs <;> simp [Cons, pcRank, RetOk, retRank, hop, hst]
    | wr15 w =>
      obtain ⟨⟨v, hop⟩, -⟩ := hc
      simp only [pstep, hst, hop, startSC]
      split_ifs
      · have := afterCall_ok (f := ⟨.sc, (r.k, .W), (p, .crit), w.1, (v, !w.2.2), 0, false, .l7⟩)
          r none (.wr15 w) false ⟨⟨v, hop⟩, by simp⟩
        simp only [applyNext_ps_self, hst, rank_none, pcRank]
        exact ⟨this.1, by simp [contRank] at this; omega⟩
      · simp [Cons, frRank, contRank, pcRank, hop, hst]
    | tw19 ret =>
      obtain ⟨hr, -⟩ := hc
      simp [pstep, hst, Cons, pcRank, hr]
    | tw20 ret zh =>
      obtain ⟨hr, -⟩ := hc
      simp only [pstep, hst]
      split_ifs
      · simp [Cons, pcRank, hr, hst]
      · have := afterTW_ok r (none : Option (Frame P K V)) (.tw20 ret zh) ret hr
        simp only [applyNext_ps_self, hst, rank_none, pcRank]
        exact ⟨this.1, by omega⟩
    | tw21 ret zh wh =>
      obtain ⟨hr, -⟩ := hc
      simp only [pstep, hst, startSC]
      split_ifs
      · have := afterCall_ok (f := ⟨.sc, (r.k, .Z), (p, .cas), zh.1, wh.2, 0, false, .l7⟩)
          r none (.tw21 ret zh wh) false ⟨hr, by simp⟩
        simp only [applyNext_ps_self, hst, rank_none, pcRank]
        exact ⟨this.1, by simp [contRank] at this; omega⟩
      · simp [Cons, frRank, contRank, pcRank, hr, hst]
    | recv j =>
      simp only [pstep, hst, setFrame_ps_self]
      refine ⟨by simp [Cons], ?_⟩
      simp [frRank, contRank, pcRank]
      omega

omit [DecidableEq P] [DecidableEq K] [DecidableEq V] in
theorem rank_le (st : PState P K V) : rank st ≤ 54 := by
  rcases st with ⟨pc, fr, op⟩
  have hr : ∀ ret : Ret V, retRank ret ≤ 36 := by
    intro ret; cases ret <;> simp [retRank] <;> split <;> omega
  have hf : ∀ f : Frame P K V, frRank f ≤ 10 := by
    intro f; unfold frRank; split <;> omega
  cases op with
  | none => simp [rank]
  | some r =>
    cases fr with
    | none =>
      cases pc <;> simp [pcRank] <;> (try split) <;> (try omega)
      all_goals (first | (have := hr ‹_›; omega) | omega)
    | some f =>
      have := hf f
      cases pc <;> simp [contRank] <;> (try split) <;> (try omega)
      have := hr ‹_›; omega

/-- Run a list of labels from `s` (`none` if a label is not enabled). -/
def runL (s : St P K V) : List (Lbl P K V) → Option (St P K V)
  | [] => some s
  | ℓ :: ls => if ℓ.En s then runL (ℓ.apply s) ls else none

theorem cons_apply_ne (s : St P K V) (ℓ : Lbl P K V) {p : P}
    (hne : ∀ k op, ℓ ≠ .invoke p k op) (hnc : ℓ ≠ .crash p) (hns : ℓ ≠ .step p) :
    (ℓ.apply s).ps p = s.ps p := by
  cases ℓ with
  | step q => exact pstep_ps_ne s (fun h => hns (h ▸ rfl))
  | invoke q k op =>
    simp only [Lbl.apply, doInvoke]
    rw [Function.update_of_ne (fun h => hne k op (by rw [h]))]
  | crash q =>
    simp only [Lbl.apply, doCrash]
    rw [Function.update_of_ne (fun h => hnc (by rw [h]))]

/-- **Theorem 4.1(2) (wait-freedom, constant time).** If a process neither crashes nor invokes a
new operation during a run, the number of its steps in the run plus its final `rank` is at most its
initial `rank` (≤ 54): an operation, and `RECOVER`, completes within 54 steps of its process. -/
theorem steps_le_rank (s s' : St P K V) (p : P) (ls : List (Lbl P K V)) (hc : Cons (s.ps p))
    (hrun : runL s ls = some s') (hnc : ∀ ℓ ∈ ls, ℓ ≠ .crash p ∧ ∀ k op, ℓ ≠ .invoke p k op) :
    ls.count (.step p) + rank (s'.ps p) ≤ rank (s.ps p) := by
  induction ls generalizing s with
  | nil => simp [runL] at hrun; subst hrun; simp
  | cons ℓ ls ih =>
    simp only [runL] at hrun
    split_ifs at hrun with hen
    have hnc' : ∀ ℓ ∈ ls, ℓ ≠ .crash p ∧ ∀ k op, ℓ ≠ .invoke p k op :=
      fun ℓ h => hnc ℓ (List.mem_cons_of_mem _ h)
    by_cases hs : ℓ = .step p
    · subst hs
      have hb : (s.ps p).op.isSome := hen
      have h1 := pstep_self s p hc hb
      have := ih (pstep s p) h1.1 hrun hnc'
      simp only [List.count_cons_self]
      omega
    · have heq := cons_apply_ne s ℓ (hnc ℓ List.mem_cons_self).2 (hnc ℓ List.mem_cons_self).1 hs
      have := ih (ℓ.apply s) (heq ▸ hc) hrun hnc'
      rw [List.count_cons_of_ne hs]
      rw [heq] at this
      exact this

/-- Consistency of the local states holds in every reachable state. -/
theorem reach_cons {init : K → V} {hv0 : Hd P → V × Bool} {s : St P K V}
    (h : Reach init hv0 s) (p : P) : Cons (s.ps p) := by
  induction h generalizing p with
  | refl => simp [initSt, Cons]
  | tail _ hst ih =>
    obtain ⟨ℓ, hen, rfl⟩ := hst
    cases ℓ with
    | step q =>
      by_cases hq : p = q
      · subst hq; exact (pstep_self _ _ (ih p) hen).1
      · simp only [Lbl.apply]; rw [pstep_ps_ne _ hq]; exact ih p
    | invoke q k op =>
      simp only [Lbl.apply, doInvoke]
      by_cases hq : p = q
      · subst hq; simp only [Function.update_self]
        cases op <;> simp [Cons, firstPc]
      · rw [Function.update_of_ne hq]; exact ih p
    | crash q =>
      simp only [Lbl.apply, doCrash]
      by_cases hq : p = q
      · subst hq; simp only [Function.update_self]
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hen
        simp [Cons, hr]
      · rw [Function.update_of_ne hq]; exact ih p

/-- **Theorem 4.1(2).** From a reachable state, a process that neither crashes nor invokes a new
operation takes at most `54` steps: every operation and every `RECOVER` completes within `54` own
steps, whatever the other processes do (wait-free, constant time). -/
theorem waitFree {init : K → V} {hv0 : Hd P → V × Bool} {s s' : St P K V}
    (hs : Reach init hv0 s) (p : P) (ls : List (Lbl P K V)) (hrun : runL s ls = some s')
    (hnc : ∀ ℓ ∈ ls, ℓ ≠ .crash p ∧ ∀ k op, ℓ ≠ .invoke p k op) :
    ls.count (.step p) ≤ 54 := by
  have := steps_le_rank s s' p ls (reach_cons hs p) hrun hnc
  have := rank_le (s.ps p)
  omega

end Podc.DuraCAS
