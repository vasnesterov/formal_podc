import Papers.PODC2013.ConstantBarriersMutex.RMR

/-!
# Consequences of the invariant used by the RMR analysis

Everything here is derived from `Inv` (`InvDefs.lean`):

* `Inv.lock_of_buf`: writes to `lock`, `promQ`, `exits` are buffered only by the lock owner.
* `Inv.perf_cases`: an event performs no write, or the oldest buffered write of its actor (and is
  then equal to a flush), or it is a successful CAS (with an empty buffer).
* The lock-protocol counter `mu s = 2·exits + [Pend s]` (`Pend`: the current lock owner has not
  yet performed its `exits` increment). It never decreases; a performed write to `lock` either
  increases it from an even value by one and leaves `lock ≠ −1` (a successful CAS, or a
  hand-over `lock ← next`), or sets `lock` to `−1` (statement 43). This is the formal content of
  "the lock changes a bounded number of times between two increments of `exits`".
-/

-- The case analyses below use generic tactic combinators; some branches do not need every
-- simp lemma or tactic.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Podc.ConstantBarriersMutex

variable {h : ℕ} {s : Cfg h}

lemma doorList_mem_cases {q : Proc h} {w : W h} (hw : w ∈ doorList q) :
    w = .signal q false ∨ w = .apply q true ∨ ∃ l, w = .node (anc q l) q := by
  simp only [doorList, List.mem_cons, List.mem_map, List.mem_reverse, List.mem_range] at hw
  rcases hw with hw | hw | ⟨l, -, hw⟩
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr ⟨l, hw.symm⟩)

lemma DoorLI.mem_doorList_of_buf {q : Proc h} {k : ℕ} (hd : DoorLI s q k) {w : W h} (hw : w ∈ s.buf q) :
    w ∈ doorList q := by
  obtain ⟨i, -, hb, -⟩ := hd
  rw [hb] at hw
  exact List.mem_of_mem_take (List.mem_of_mem_drop hw)

lemma DoorLI.var_of_buf {q : Proc h} {k : ℕ} (hd : DoorLI s q k) {w : W h} (hw : w ∈ s.buf q) :
    w.var = .signal q ∨ w.var = .apply q ∨ ∃ i, w.var = .node i := by
  rcases doorList_mem_cases (hd.mem_doorList_of_buf hw) with rfl | rfl | ⟨l, rfl⟩ <;> simp [W.var]

/-- Writes to `lock`, `promQ` and `exits` are buffered only by the lock owner. -/
lemma Inv.lock_of_buf (hI : Inv s) {a : Proc h} {w : W h} (hw : w ∈ s.buf a)
    (hv : w.var = .lock ∨ w.var = .promQ ∨ w.var = .exits) : s.mem.lock = some a := by
  have hL := hI.loc a
  rcases hpc : s.pc a with _ | _ | l | _ | _ | _ | e | e | _ | _ | _ | _ | _ | ⟨l, j, acc⟩ |
    ⟨l, c⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | _ | _ | _ | nx | nx | nx | (_ | nx) <;>
    simp only [LI, hpc] at hL
  all_goals first
    | exact hL.1
    | (simp [hL.1] at hw)
    | (rcases hL.2 with ⟨B, -, -, hl⟩ | ⟨hb, -⟩
       · exact hl
       · simp [hb] at hw)
    | (rcases hL with ⟨B, -, -, hl⟩ | ⟨hb, -⟩
       · exact hl
       · simp [hb] at hw)
    | (rcases hL.2 with ⟨B, -, -, hl⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
       · exact hl
       · simp only [hb, List.mem_singleton] at hw; subst hw; simp [W.var] at hv
       · simp [hb] at hw)
    | (obtain ⟨i, -, hb, -⟩ := hL
       rw [hb] at hw
       rcases doorList_mem_cases (List.mem_of_mem_take (List.mem_of_mem_drop hw)) with rfl | rfl | ⟨l, rfl⟩ <;>
         simp [W.var] at hv)
    | (obtain ⟨-, i, -, hb, -⟩ := hL
       rw [hb] at hw
       rcases doorList_mem_cases (List.mem_of_mem_take (List.mem_of_mem_drop hw)) with rfl | rfl | ⟨l, rfl⟩ <;>
         simp [W.var] at hv)

/-- A buffered write that is neither to `lock` nor to `signal[q]` for `q ≠ a`. -/
def Plain (a : Proc h) (w : W h) : Prop := w.var ≠ .lock ∧ ∀ q, w.var = .signal q → q = a

lemma ExitType.plain {a : Proc h} {w : W h} (hw : ExitType a w) : Plain a w := by
  rcases hw with rfl | hw | hw | ⟨r, b, rfl⟩
  · simp [Plain, W.var]
  · cases w <;> simp_all [Plain, W.var, W.isExits]
  · cases w <;> simp_all [Plain, W.var, W.isPromQ]
  · simp [Plain, W.var]

lemma plain_of_doorList {a : Proc h} {w : W h} (hw : w ∈ doorList a) : Plain a w := by
  rcases doorList_mem_cases hw with rfl | rfl | ⟨l, rfl⟩ <;> simp [Plain, W.var]

/-- The shape of a store buffer: only plain writes, possibly followed by the lock write of
statement 43/47 and the signal of statement 48. -/
lemma Inv.buf_cases (hI : Inv s) (a : Proc h) :
    (∀ w ∈ s.buf a, Plain a w) ∨
    (∃ B o, s.buf a = B ++ [.lock o] ∧ (∀ w ∈ B, Plain a w) ∧ s.mem.lock = some a ∧
      (∀ nx, o = some nx → (s.pc nx).Entry) ∧ ((∃ nx, s.pc a = .x48 nx) ∨ s.pc a = .x50 none)) ∨
    (∃ B nx, s.buf a = B ++ [.lock (some nx), .signal nx true] ∧ (∀ w ∈ B, Plain a w) ∧
      s.mem.lock = some a ∧ (s.pc nx).Entry ∧ s.pc a = .x50 (some nx)) ∨
    (∃ nx, s.buf a = [.signal nx true] ∧ s.mem.signal nx = false ∧ nx ≠ a ∧
      s.pc a = .x50 (some nx)) := by
  have hL := hI.loc a
  have hC := hI.hc a
  rcases hpc : s.pc a with _ | _ | l | _ | _ | _ | e | e | _ | _ | _ | _ | _ | ⟨l, j, acc⟩ |
    ⟨l, c⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | _ | _ | _ | nx | nx | nx | (_ | nx) <;>
    simp only [LI, hpc] at hL <;> simp only [HC, hpc] at hC
  all_goals first
    | (left; intro w hw; simp [hL.1] at hw)
    | (left; intro w hw; exact (hL.2.1.1 w hw).plain)
    | (left; intro w hw; exact plain_of_doorList (DoorLI.mem_doorList_of_buf hL hw))
    | (left; intro w hw; exact plain_of_doorList (DoorLI.mem_doorList_of_buf hL.2 hw))
    | (left; intro w hw; exact (hL.2.1 w hw).plain)
    | (left; intro w hw
       rcases hL.2 with ⟨hb, -⟩ | ⟨hb, -⟩ <;> simp [hb] at hw
       subst hw; simp [Plain, W.var])
    | (rcases hL with ⟨hne, ⟨B, hb, hB, hl⟩ | ⟨hb, -⟩⟩
       · exact Or.inr (Or.inl ⟨B, _, hb, fun w hw => (hB.1 w hw).plain, hl,
           by rintro _ ⟨⟩; exact hC.1, Or.inl ⟨_, rfl⟩⟩)
       · left; simp [hb])
    | (rcases hL with ⟨B, hb, hB, hl⟩ | ⟨hb, -⟩
       · exact Or.inr (Or.inl ⟨B, _, hb, fun w hw => (hB.1 w hw).plain, hl,
           by rintro _ ⟨⟩, Or.inr rfl⟩)
       · left; simp [hb])
    | (rcases hL with ⟨hne, ⟨B, hb, hB, hl⟩ | ⟨hb, -, -, hs⟩ | ⟨hb, -⟩⟩
       · exact Or.inr (Or.inr (Or.inl ⟨B, _, hb, fun w hw => (hB.1 w hw).plain, hl,
           (hC (by simp [hb])).1, rfl⟩))
       · exact Or.inr (Or.inr (Or.inr ⟨nx, hb, hs, hne, rfl⟩))
       · left; simp [hb])

/-- A successful CAS by `a` (with an empty store buffer). -/
def CasSucc (s : Cfg h) (e : Ev h) : Prop :=
  e = .step e.actor ∧ (s.pc e.actor = .e23 ∨ s.pc e.actor = .e26) ∧ s.buf e.actor = [] ∧
    s.mem.lock = none ∧ s.perf e = [.lock (some e.actor)] ∧ (s.next e).ent = s.ent + 1 ∧
    (s.next e).pc e.actor = .cs ∧ (s.next e).mem = s.mem.write (.lock (some e.actor))

/-- The writes performed by an event: none, the oldest buffered write of the actor (the event
then acts as a flush), or the write of a successful CAS. -/
lemma Inv.perf_cases (hI : Inv s) (e : Ev h) :
    s.perf e = [] ∨
    (∃ w rest, s.buf e.actor = w :: rest ∧ s.perf e = [w] ∧ s.next e = s.flush e.actor) ∨
    CasSucc s e := by
  cases e with
  | flush p =>
    rcases hb : s.buf p with _ | ⟨w, rest⟩
    · left; simp [Cfg.perf, hb]
    · right; left; exact ⟨w, rest, hb, by simp [Cfg.perf, hb], rfl⟩
  | step p =>
    have hL := hI.loc p
    rcases hpc : s.pc p with _ | _ | l | _ | _ | _ | e | e | _ | _ | _ | _ | _ | ⟨l, j, acc⟩ |
      ⟨l, c⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | _ | _ | _ | nx | nx | nx | o <;>
      simp only [LI, hpc] at hL
    all_goals first
      | (left; simp [Cfg.perf, hpc]; done)
      | (rcases hb : s.buf p with _ | ⟨w, rest⟩
         · left; simp [Cfg.perf, hpc, hb]
         · right; left
           exact ⟨w, rest, hb, by simp [Cfg.perf, hpc, hb],
             by simp [Cfg.next, Cfg.stepProc, hpc, Cfg.barrier, hb, Ev.actor]⟩)
      | (by_cases hl : s.mem.lock = none
         · right; right
           simp [CasSucc, Ev.actor, Cfg.perf, Cfg.next, Cfg.stepProc, Cfg.cas, Cfg.view, hpc, hL.1,
             hl, Mem.write]
         · left; simp [Cfg.perf, hpc, hL.1, Cfg.view, hl])

/-- Processes in statements `cs`, 31, 32 own the lock. -/
lemma Inv.lock_of_cs31 (hI : Inv s) {g : Proc h} (hg : s.pc g = .cs ∨ s.pc g = .x31 ∨ s.pc g = .x32) :
    s.mem.lock = some g := by
  have hL := hI.loc g
  rcases hg with hg | hg | hg <;> simp only [LI, hg] at hL
  · exact hL.2.2
  · exact hL.2.2
  · exact hL.1

/-- If the lock owner (if any) has performed its `exits` increment, then `ent = exits`. -/
lemma Inv.ent_eq_exits_of (hI : Inv s)
    (H : ∀ g, s.mem.lock = some g → s.pc g ≠ .cs ∧ s.pc g ≠ .x31 ∧ s.pc g ≠ .x32 ∧
      ∀ v, .exits v ∉ s.buf g) : s.ent = s.mem.exits := by
  apply hI.ex3
  intro g
  have hcs : ¬ (s.pc g = .cs ∨ s.pc g = .x31 ∨ s.pc g = .x32) := fun hg =>
    by have := H g (hI.lock_of_cs31 hg); tauto
  refine ⟨fun h1 => hcs (Or.inl h1), fun h1 => hcs (Or.inr (Or.inl h1)),
    fun h1 => hcs (Or.inr (Or.inr h1)), fun v hv => ?_⟩
  exact (H g (hI.lock_of_buf hv (by simp [W.var]))).2.2.2 v hv

lemma Inv.exits_le_ent_rmr (hI : Inv s) : s.mem.exits ≤ s.ent := by
  by_cases H : ∀ g, s.pc g ≠ .cs ∧ s.pc g ≠ .x31 ∧ s.pc g ≠ .x32 ∧ ∀ v, .exits v ∉ s.buf g
  · exact (hI.ex3 H).ge
  · push Not at H
    obtain ⟨g, hg⟩ := H
    by_cases hc : s.pc g = .cs ∨ s.pc g = .x31 ∨ s.pc g = .x32
    · have := hI.ex1 g hc; omega
    · push Not at hc
      obtain ⟨v, hv⟩ := hg hc.1 hc.2.1 hc.2.2
      have := hI.ex2 g v hv; omega

/-- The oldest buffered write of `a` is to `lock`: statement 43 or 47 of the lock owner `a`. -/
lemma Inv.head_lock (hI : Inv s) {a : Proc h} {w : W h} {rest : List (W h)}
    (hb : s.buf a = w :: rest) (hw : w.var = .lock) :
    ∃ o, w = .lock o ∧ s.mem.lock = some a ∧ s.ent = s.mem.exits ∧ ¬ (s.pc a).Entry ∧
      (∀ nx, o = some nx → (s.pc nx).Entry) := by
  have hnp : ¬ Plain a w := fun hp => hp.1 hw
  rcases hI.buf_cases a with hP | ⟨B, o, hB, hBP, hl, hnx, hpc⟩ | ⟨B, nx, hB, hBP, hl, hnx, hpc⟩ |
    ⟨nx, hB, -, -, -⟩
  · exact absurd (hP w (by simp [hb])) hnp
  · rcases B with _ | ⟨b, B⟩
    · simp only [List.nil_append, hb, List.cons.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      refine ⟨o, rfl, hl, hI.ent_eq_exits_of fun g hg => ?_, ?_, hnx⟩
      · obtain rfl : g = a := by rw [hl] at hg; exact (Option.some_inj.1 hg).symm
        rcases hpc with ⟨nx, hpc⟩ | hpc <;> simp [hpc, hb]
      · rcases hpc with ⟨nx, hpc⟩ | hpc <;> simp [hpc, PC.Entry]
    · simp only [List.cons_append, hb, List.cons.injEq] at hB
      exact absurd (hBP b (by simp)) (hB.1 ▸ hnp)
  · rcases B with _ | ⟨b, B⟩
    · simp only [List.nil_append, hb, List.cons.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      refine ⟨some nx, rfl, hl, hI.ent_eq_exits_of fun g hg => ?_, by simp [hpc, PC.Entry], by simp [hnx]⟩
      obtain rfl : g = a := by rw [hl] at hg; exact (Option.some_inj.1 hg).symm
      simp [hpc, hb]
    · simp only [List.cons_append, hb, List.cons.injEq] at hB
      exact absurd (hBP b (by simp)) (hB.1 ▸ hnp)
  · rw [hb] at hB; simp only [List.cons.injEq] at hB
    rw [hB.1] at hw; simp [W.var] at hw

/-- The oldest buffered write of `a` is to `signal[q]` with `q ≠ a`: statement 48, and
`signal[q]` is `false` in memory. -/
lemma Inv.head_signal (hI : Inv s) {a q : Proc h} {w : W h} {rest : List (W h)}
    (hb : s.buf a = w :: rest) (hw : w.var = .signal q) (hqa : q ≠ a) :
    w = .signal q true ∧ s.mem.signal q = false := by
  have hnp : ¬ Plain a w := fun hp => hqa (hp.2 q hw)
  rcases hI.buf_cases a with hP | ⟨B, o, hB, hBP, -⟩ | ⟨B, nx, hB, hBP, -⟩ | ⟨nx, hB, hs, -, -⟩
  · exact absurd (hP w (by simp [hb])) hnp
  · rcases B with _ | ⟨b, B⟩
    · simp only [List.nil_append, hb, List.cons.injEq] at hB
      rw [hB.1] at hw; simp [W.var] at hw
    · simp only [List.cons_append, hb, List.cons.injEq] at hB
      exact absurd (hBP b (by simp)) (hB.1 ▸ hnp)
  · rcases B with _ | ⟨b, B⟩
    · simp only [List.nil_append, hb, List.cons.injEq] at hB
      rw [hB.1] at hw; simp [W.var] at hw
    · simp only [List.cons_append, hb, List.cons.injEq] at hB
      exact absurd (hBP b (by simp)) (hB.1 ▸ hnp)
  · rw [hb] at hB; simp only [List.cons.injEq] at hB
    obtain ⟨rfl, -⟩ := hB
    simp only [W.var, Var.signal.injEq] at hw
    subst hw; exact ⟨rfl, hs⟩

/-! ### Fields that are not written do not change -/

lemma view_field_of_not_written {m : Mem h} {l : List (W h)} {v : Var h}
    (hl : ¬ ∃ w ∈ l, w.var = v) :
    (v = .lock → (m.view l).lock = m.lock) ∧ (v = .exits → (m.view l).exits = m.exits) ∧
    (v = .promQ → (m.view l).promQ = m.promQ) ∧
    (∀ q, v = .signal q → (m.view l).signal q = m.signal q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl; exact view_lock_of fun w hw => by
      cases w <;> simp_all [W.isLock, W.var] <;> exact hl _ hw rfl
  · rintro rfl; exact view_exits_of fun w hw => by
      cases w <;> simp_all [W.isExits, W.var] <;> exact hl _ hw rfl
  · rintro rfl; exact view_promQ_of fun w hw => by
      cases w <;> simp_all [W.isPromQ, W.var] <;> exact hl _ hw rfl
  · rintro q rfl; exact view_signal_of fun w hw => by
      cases w <;> simp_all [W.isSignal, W.var] <;> exact fun h => hl _ hw (by rw [h])

/-- Fields of memory that the event does not write keep their values. -/
lemma Cfg.next_not_written (s : Cfg h) (e : Ev h) {v : Var h}
    (hl : ¬ ∃ w ∈ s.perf e, w.var = v) :
    (v = .lock → (s.next e).mem.lock = s.mem.lock) ∧
    (v = .exits → (s.next e).mem.exits = s.mem.exits) ∧
    (v = .promQ → (s.next e).mem.promQ = s.mem.promQ) ∧
    (∀ q, v = .signal q → (s.next e).mem.signal q = s.mem.signal q) := by
  rw [Cfg.mem_next_perf]; exact view_field_of_not_written hl

/-- The three kinds of events, with their effect. -/
lemma Inv.next_cases (hI : Inv s) (e : Ev h) :
    (s.perf e = [] ∧ (s.next e).mem = s.mem) ∨
    (∃ w rest, s.buf e.actor = w :: rest ∧ s.perf e = [w] ∧ (s.next e).mem = s.mem.write w ∧
      (s.next e).pc = s.pc ∧ (s.next e).ent = s.ent) ∨
    CasSucc s e := by
  rcases hI.perf_cases e with h0 | ⟨w, rest, hb, hp, hn⟩ | hc
  · left; exact ⟨h0, by rw [Cfg.mem_next_perf, h0]; rfl⟩
  · right; left
    refine ⟨w, rest, hb, hp, ?_, ?_, ?_⟩ <;> rw [hn] <;> simp [flush_of_cons _ _ hb]
  · right; right; exact hc

/-! ### The lock-protocol counter -/

/-- The current lock owner has not yet performed its `exits` increment: it has entered the
critical section and its increment (statement 32) is not yet performed (`exits < ent`), or it
has been handed the lock and has not entered the critical section yet. -/
def Pend (s : Cfg h) : Prop := s.mem.exits < s.ent ∨ ∃ g, s.mem.lock = some g ∧ (s.pc g).Entry

open Classical in
/-- The lock-protocol counter `2·exits + [Pend]`. It increases by one at every performed
`exits` increment and at every acquisition of the lock (successful CAS or hand-over). -/
noncomputable def mu (s : Cfg h) : ℕ := 2 * s.mem.exits + if Pend s then 1 else 0

lemma mu_le (s : Cfg h) : mu s ≤ 2 * s.mem.exits + 1 := by unfold mu; split_ifs <;> omega
lemma le_mu (s : Cfg h) : 2 * s.mem.exits ≤ mu s := by unfold mu; split_ifs <;> omega
lemma mu_of_not_pend {s : Cfg h} (hp : ¬ Pend s) : mu s = 2 * s.mem.exits := by simp [mu, hp]
lemma mu_of_pend {s : Cfg h} (hp : Pend s) : mu s = 2 * s.mem.exits + 1 := by simp [mu, hp]

lemma Inv.not_pend_of_head_lock (hI : Inv s) {a : Proc h} {w : W h} {rest : List (W h)}
    (hb : s.buf a = w :: rest) (hw : w.var = .lock) : ¬ Pend s := by
  obtain ⟨o, -, hl, he, hE, -⟩ := hI.head_lock hb hw
  rintro (h1 | ⟨g, hg, hgE⟩)
  · omega
  · rw [hl] at hg; obtain rfl := Option.some_inj.1 hg; exact hE hgE

lemma Inv.not_pend_of_free (hI : Inv s) (hl : s.mem.lock = none) : ¬ Pend s := by
  have he := hI.ent_eq_exits_of fun g hg => by simp [hl] at hg
  rintro (h1 | ⟨g, hg, -⟩)
  · omega
  · simp [hl] at hg

/-- `mu` never decreases. -/
lemma Inv.mu_mono (hI : Inv s) (e : Ev h) : mu s ≤ mu (s.next e) := by
  have hle := hI.exits_le_ent_rmr
  rcases hI.next_cases e with ⟨-, hm⟩ | ⟨w, rest, hb, -, hm, hpc, hent⟩ | hc
  · have hmono : Pend s → Pend (s.next e) := by
      rintro (h1 | ⟨g, hg, hE⟩)
      · left; rw [hm]; rcases (s.ent_next_cases e) with h2 | h2 <;> omega
      · by_cases hga : e.actor = g
        · subst hga
          rcases s.entry_next_cases e hE with h2 | h2
          · right; exact ⟨e.actor, by rw [hm]; exact hg, h2⟩
          · left; rw [hm, h2]; omega
        · right; exact ⟨g, by rw [hm]; exact hg, by rw [s.pc_next_of_ne_actor e hga]; exact hE⟩
    unfold mu; rw [hm]; split_ifs <;> simp_all
  · cases w with
    | exits v =>
      have := (hI.ex2 _ v (by rw [hb]; simp)).1
      have h1 := mu_le s
      have h2 := le_mu (s.next e)
      rw [hm] at h2; simp only [write_exits] at h2; omega
    | lock o =>
      rw [mu_of_not_pend (hI.not_pend_of_head_lock hb rfl)]
      have := le_mu (s.next e); rw [hm] at this; simpa using this
    | _ =>
      have hP : Pend (s.next e) ↔ Pend s := by simp [Pend, hm, hpc, hent]
      have hx : (s.next e).mem.exits = s.mem.exits := by rw [hm]; simp
      unfold mu; rw [hx]; split_ifs <;> simp_all
  · obtain ⟨-, -, -, hl, -, hent, -, hm⟩ := hc
    rw [mu_of_not_pend (hI.not_pend_of_free hl)]
    have := le_mu (s.next e); rw [hm] at this; simpa using this

/-- A performed write to `lock` is an acquisition (successful CAS or hand-over, from an even
`mu`, which then increases by one) or a release (statement 43, `lock ← −1`). -/
lemma Inv.lock_written (hI : Inv s) (e : Ev h) (hw : ∃ w ∈ s.perf e, w.var = .lock) :
    (Even (mu s) ∧ mu (s.next e) = mu s + 1 ∧ (s.next e).mem.lock ≠ none) ∨
      (s.next e).mem.lock = none := by
  rcases hI.next_cases e with ⟨h0, -⟩ | ⟨w, rest, hb, hp, hm, hpc, hent⟩ | hc
  · simp [h0] at hw
  · rw [hp] at hw; simp only [List.mem_singleton, exists_eq_left] at hw
    obtain ⟨o, rfl, hl, he, hE, hnx⟩ := hI.head_lock hb hw
    have hmu := mu_of_not_pend (hI.not_pend_of_head_lock hb rfl)
    rcases o with _ | nx
    · right; rw [hm]; simp
    · left
      have hP : Pend (s.next e) := Or.inr ⟨nx, by rw [hm]; simp, by rw [hpc]; exact hnx nx rfl⟩
      refine ⟨⟨s.mem.exits, by omega⟩, ?_, by rw [hm]; simp⟩
      rw [mu_of_pend hP, hmu, hm]; simp
  · obtain ⟨-, -, -, hl, -, hent, -, hm⟩ := hc
    have hmu := mu_of_not_pend (hI.not_pend_of_free hl)
    have he := hI.ent_eq_exits_of fun g hg => by simp [hl] at hg
    left
    have hP : Pend (s.next e) := Or.inl (by rw [hm, hent]; simp; omega)
    refine ⟨⟨s.mem.exits, by omega⟩, ?_, by rw [hm]; simp⟩
    rw [mu_of_pend hP, hmu, hm]; simp

/-- A performed write to `exits` increments it. -/
lemma Inv.exits_written (hI : Inv s) (e : Ev h) (hw : ∃ w ∈ s.perf e, w.var = .exits) :
    (s.next e).mem.exits = s.mem.exits + 1 := by
  rcases hI.next_cases e with ⟨h0, -⟩ | ⟨w, rest, hb, hp, hm, -, -⟩ | hc
  · simp [h0] at hw
  · rw [hp] at hw; simp only [List.mem_singleton, exists_eq_left] at hw
    cases w with
    | exits v =>
      have := (hI.ex2 _ v (by rw [hb]; simp)).1
      rw [hm]; simpa using this
    | _ => simp [W.var] at hw
  · rw [hc.2.2.2.2.1] at hw; simp [W.var] at hw

/-- A performed write of another process to `signal[q]` sets it from `false` to `true`. -/
lemma Inv.signal_written (hI : Inv s) (e : Ev h) {q : Proc h} (hq : e.actor ≠ q)
    (hw : ∃ w ∈ s.perf e, w.var = .signal q) :
    s.mem.signal q = false ∧ (s.next e).mem.signal q = true := by
  rcases hI.next_cases e with ⟨h0, -⟩ | ⟨w, rest, hb, hp, hm, -, -⟩ | hc
  · simp [h0] at hw
  · rw [hp] at hw; simp only [List.mem_singleton, exists_eq_left] at hw
    obtain ⟨rfl, hs⟩ := hI.head_signal hb hw (Ne.symm hq)
    exact ⟨hs, by rw [hm]; simp [Mem.write]⟩
  · rw [hc.2.2.2.2.1] at hw; simp [W.var] at hw

/-- A process other than the lock owner performs no write to `promQ`. -/
lemma Inv.promQ_not_written (hI : Inv s) (e : Ev h) {g : Proc h} (hg : s.mem.lock = some g)
    (hga : e.actor ≠ g) : ¬ ∃ w ∈ s.perf e, w.var = .promQ := by
  rintro ⟨w, hw, hv⟩
  rcases hI.next_cases e with ⟨h0, -⟩ | ⟨w', rest, hb, hp, -, -, -⟩ | hc
  · simp [h0] at hw
  · rw [hp, List.mem_singleton] at hw; subst hw
    have := hI.lock_of_buf (a := e.actor) (w := w) (by rw [hb]; simp) (Or.inr (Or.inl hv))
    rw [hg] at this; exact hga (Option.some_inj.1 this).symm
  · rw [hc.2.2.2.2.1, List.mem_singleton] at hw; subst hw; simp [W.var] at hv

/-! ### An auxiliary invariant: at statement 45 the queue is non-empty -/

lemma rmr_view_promQ_congr {m m' : Mem h} (hm : m.promQ = m'.promQ) (b : List (W h)) :
    (m.view b).promQ = (m'.view b).promQ := by
  induction b generalizing m m' with
  | nil => exact hm
  | cons w b ih =>
    simp only [Mem.view_cons]
    exact ih (by cases w <;> simp [hm])

lemma Cfg.step_to_x45 (s : Cfg h) (p : Proc h) (hp : (s.stepProc p).pc p = .x45) :
    s.pc p = .x42 ∧ (s.view p).promQ ≠ [] ∧ s.stepProc p = s.goto p .x45 := by
  rcases hpc : s.pc p <;> simp only [Cfg.stepProc, hpc] at hp ⊢
  all_goals first
    | (simp at hp; done)
    | (simp only [Cfg.barrier, Cfg.cas] at hp; split_ifs at hp <;> simp at hp; done)
    | (split_ifs at hp <;> simp at hp; done)
    | (rw [barrier_pc] at hp; split_ifs at hp <;> simp [hpc] at hp; done)
    | (split_ifs at hp <;> simp [hpc] at hp; done)
    | skip
  case x35 l c =>
    rcases c with _ | ⟨q, c⟩ <;> simp only at hp <;> split_ifs at hp <;> simp at hp
  case x42 =>
    split_ifs at hp ⊢ with h1
    · simp at hp
    · exact ⟨trivial, h1, rfl⟩
  case x45 =>
    split at hp <;> simp [hpc] at hp

/-- At statement 45 the promotion queue (in the view of the process) is non-empty. -/
def X45 (s : Cfg h) : Prop := ∀ p, s.pc p = .x45 → (s.view p).promQ ≠ []

lemma Inv.x45_next (hI : Inv s) (hX : X45 s) (e : Ev h) : X45 (s.next e) := by
  intro p hp
  by_cases ha : e.actor = p
  · cases e with
    | flush q =>
      simp only [Ev.actor] at ha; subst ha
      simp only [Cfg.next, flush_pc] at hp ⊢
      rw [Cfg.view_self_flush]; exact hX _ hp
    | step q =>
      simp only [Ev.actor] at ha; subst ha
      simp only [Cfg.next] at hp ⊢
      obtain ⟨-, hne, heq⟩ := s.step_to_x45 q hp
      rw [heq]; simpa [Cfg.view] using hne
  · have hpc : s.pc p = .x45 := by rwa [s.pc_next_of_ne_actor e ha] at hp
    have hl : s.mem.lock = some p := by
      have := hI.loc p; simp only [LI, hpc] at this; exact this.1
    have hm := (s.next_not_written e (hI.promQ_not_written e hl ha)).2.2.1 rfl
    simp only [Cfg.view, s.buf_next_of_ne_actor e ha]
    rw [rmr_view_promQ_congr hm]; exact hX p hpc

theorem Run.x45_of_inv (r : Run h) (hinv : ∀ t, Inv (r.s t)) (t : ℕ) : X45 (r.s t) := by
  induction t with
  | zero => rw [r.init]; intro p hp; simp [Cfg.init] at hp
  | succ t ih => rw [r.step t]; exact (hinv t).x45_next ih _

end Podc.ConstantBarriersMutex
