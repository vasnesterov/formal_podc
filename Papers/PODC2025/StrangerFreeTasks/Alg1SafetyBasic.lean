import Papers.PODC2025.StrangerFreeTasks.Alg1
import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Safety of Algorithm 1: step lemmas and basic invariants
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P] {k : ℕ}

/-- Configurations of Algorithm 1. -/
abbrev Cfg (P : Type) (k : ℕ) := Config (laObj P) (Regs P k) P (Loc P k)

variable (k) in
/-- The local state after the write of line 9. -/
def wrNext (l : Loc P k) : Loc P k :=
  { l with phase := .col1, j := 0, i := l.i + 1, seq := l.seq + 1 }

lemma step_inv_alg1 {C C' : Cfg P k} {p : P} {o : Unit}
    (h : (alg1 (P := P) k).step C (.inv p o) = some C') :
    C.pend p = none ∧ C'.pend = Function.update C.pend p (some o) ∧
      C'.loc = Function.update C.loc p
        (if (C.loc p).phase = .idle then { C.loc p with phase := .wr } else C.loc p) ∧
      C'.mem = C.mem := by
  obtain ⟨h1, -, h2, h3, h4⟩ := Impl.step_inv h
  exact ⟨h1, h2, h3, h4⟩

lemma step_ret_alg1 {C C' : Cfg P k} {p : P} {o : Finset P}
    (h : (alg1 (P := P) k).step C (.ret p o) = some C') :
    C.pend p ≠ none ∧ C'.pend = Function.update C.pend p none ∧ C'.mem = C.mem ∧
      C'.loc = C.loc ∧
      (((C.loc p).phase = .done ∧ o = (C.loc p).out) ∨ (C.loc p).phase = .idle) := by
  obtain ⟨h1, h2, h3, l, h4, h5⟩ := Impl.step_ret h
  refine ⟨h1, h2, h3, ?_⟩
  simp only [alg1] at h4
  cases hph : (C.loc p).phase <;> simp [hph] at h4
  · obtain ⟨-, rfl⟩ := h4; simp [h5]
  · obtain ⟨rfl, rfl⟩ := h4; simp [h5]

lemma step_tau_alg1 {C C' : Cfg P k} {p : P}
    (h : (alg1 (P := P) k).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ C'.pend = C.pend ∧
      (((C.loc p).phase = .wr ∧
        C'.mem = Function.update C.mem (C.loc p).i ⟨some p, (C.loc p).seq, (C.loc p).seen⟩ ∧
        C'.loc = Function.update C.loc p (wrNext k (C.loc p))) ∨
      ((C.loc p).phase = .col1 ∧ C'.mem = C.mem ∧
        C'.loc = Function.update C.loc p (afterCol1 k (C.loc p) (C.mem (C.loc p).j))) ∨
      ((C.loc p).phase = .col2 ∧ C'.mem = C.mem ∧
        C'.loc = Function.update C.loc p (afterCol2 k (C.loc p) (C.mem (C.loc p).j)))) := by
  obtain ⟨h1, h2, i, o, κ, h4, h5, h6⟩ := Impl.step_tau h
  refine ⟨h1, h2, ?_⟩
  simp only [alg1] at h4
  cases hph : (C.loc p).phase <;> simp only [hph] at h4
  all_goals cases h4
  · exact Or.inl ⟨rfl, h5, h6⟩
  · exact Or.inr (Or.inl ⟨rfl, by rw [h5]; exact Function.update_eq_self _ _, h6⟩)
  · exact Or.inr (Or.inr ⟨rfl, by rw [h5]; exact Function.update_eq_self _ _, h6⟩)


/-! ### Fields of the local states after a step -/

section Fields

variable (l : Loc P k) (v : Triple P)

@[simp] lemma wrNext_phase : (wrNext k l).phase = .col1 := rfl
@[simp] lemma wrNext_seen : (wrNext k l).seen = l.seen := rfl
@[simp] lemma wrNext_seq : (wrNext k l).seq = l.seq + 1 := rfl
@[simp] lemma wrNext_collect : (wrNext k l).collect = l.collect := rfl
@[simp] lemma wrNext_out : (wrNext k l).out = l.out := rfl
@[simp] lemma wrNext_j : (wrNext k l).j = 0 := rfl

@[simp] lemma afterCol1_seen : (afterCol1 k l v).seen = l.seen ∪ v.seen := by
  unfold afterCol1; split_ifs <;> rfl
@[simp] lemma afterCol1_seq : (afterCol1 k l v).seq = l.seq := by
  unfold afterCol1; split_ifs <;> rfl
@[simp] lemma afterCol1_out : (afterCol1 k l v).out = l.out := by
  unfold afterCol1; split_ifs <;> rfl
@[simp] lemma afterCol1_collect :
    (afterCol1 k l v).collect = Function.update l.collect l.j v := by
  unfold afterCol1; split_ifs <;> rfl
lemma afterCol1_phase :
    (afterCol1 k l v).phase = if l.j.val = k then .col2 else l.phase := by
  unfold afterCol1; split_ifs <;> rfl
lemma afterCol1_j :
    (afterCol1 k l v).j = if l.j.val = k then 0 else l.j + 1 := by
  unfold afterCol1; split_ifs <;> rfl
lemma afterCol1_snap :
    (afterCol1 k l v).snap = if l.j.val = k then true else l.snap := by
  unfold afterCol1; split_ifs <;> rfl

@[simp] lemma decision_seen : (decision k l).seen = l.seen := by
  unfold decision; split_ifs <;> rfl
@[simp] lemma decision_seq : (decision k l).seq = l.seq := by
  unfold decision; split_ifs <;> rfl
@[simp] lemma decision_collect : (decision k l).collect = l.collect := by
  unfold decision; split_ifs <;> rfl

@[simp] lemma afterCol2_seen :
    (afterCol2 k l v).seen = l.seen ∪ (l.collect l.j).seen := by
  unfold afterCol2; split_ifs <;> simp
@[simp] lemma afterCol2_seq : (afterCol2 k l v).seq = l.seq := by
  unfold afterCol2; split_ifs <;> simp
@[simp] lemma afterCol2_collect : (afterCol2 k l v).collect = l.collect := by
  unfold afterCol2; split_ifs <;> simp

lemma afterCol2_phase (h : l.phase = .col2) :
    (afterCol2 k l v).phase = .col2 ∨ (afterCol2 k l v).phase = .wr ∨
      ((afterCol2 k l v).phase = .done ∧ (afterCol2 k l v).out = (afterCol2 k l v).seen) := by
  simp only [afterCol2, decision]; split_ifs <;> simp [h]

lemma afterCol2_out (h : (afterCol2 k l v).phase ≠ .done) : (afterCol2 k l v).out = l.out := by
  revert h; simp only [afterCol2, decision]; split_ifs <;> simp

lemma fin_val_add_one {j : Fin (k + 1)} (h : j.val ≠ k) : (j + 1).val = j.val + 1 := by
  rw [Fin.val_add_one_of_lt]
  exact Fin.lt_last_iff_ne_last.2 (by intro h'; apply h; rw [h']; simp)

/-- After a non-final read of the second collect the process stays in `col2`. -/
lemma afterCol2_col2 (h : l.phase = .col2) (h' : (afterCol2 k l v).phase = .col2) :
    l.j.val ≠ k ∧ (afterCol2 k l v).j = l.j + 1 ∧
      ((afterCol2 k l v).snap = true → l.snap = true ∧ v = l.collect l.j) := by
  revert h'; simp only [afterCol2, decision]; split_ifs <;> simp_all

/-- The decision after the second collect. -/
lemma afterCol2_done (h : l.phase = .col2) (h' : (afterCol2 k l v).phase = .done) :
    (afterCol2 k l v).out = (afterCol2 k l v).seen ∧
    (k < (afterCol2 k l v).seen.card ∨
      (l.j.val = k ∧ l.snap = true ∧ v = l.collect l.j ∧
        ∀ r, (afterCol2 k l v).seen = (l.collect r).seen)) := by
  revert h'; simp only [afterCol2, decision]
  split_ifs with h1 h2 h3
  · intro _; exact ⟨rfl, Or.inl h2⟩
  · intro _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    exact ⟨rfl, Or.inr ⟨h1, h3.1.1, h3.1.2, h3.2⟩⟩
  · simp
  · simp [h]

end Fields


/-! ### Basic invariants -/

/-- A triple is *fresh* in `C`: its writer has since incremented its sequence number. -/
def Fresh (C : Cfg P k) (v : Triple P) : Prop := ∀ w, v.id = some w → v.seq < (C.loc w).seq

/-- Basic invariants of Algorithm 1 (B1–B4 of the safety proof). -/
structure BInv (α : List (Label P (laObj P))) (C : Cfg P k) : Prop where
  idle_iff : ∀ q, (C.loc q).phase = .idle ↔ opsOf α q = []
  idle_seen : ∀ q, (C.loc q).phase = .idle → (C.loc q).seen = {q}
  pend : ∀ q, C.pend q ≠ none → (C.loc q).phase ≠ .idle
  seen_inv : ∀ q, (C.loc q).phase ≠ .idle → ∀ x ∈ (C.loc q).seen, opsOf α x ≠ []
  mem_inv : ∀ r, ∀ x ∈ (C.mem r).seen, opsOf α x ≠ []
  col_inv : ∀ q r, ∀ x ∈ ((C.loc q).collect r).seen, opsOf α x ≠ []
  self : ∀ q, q ∈ (C.loc q).seen
  fresh_mem : ∀ r, Fresh C (C.mem r)
  fresh_col : ∀ q r, Fresh C ((C.loc q).collect r)
  out_eq : ∀ q, (C.loc q).phase = .done → (C.loc q).out = (C.loc q).seen
  resp : ∀ q, ∀ o ∈ respsOf α q, (C.loc q).phase = .done ∧ o = (C.loc q).out

lemma Fresh.mono {C C' : Cfg P k} {v : Triple P} (h : Fresh C v)
    (hs : ∀ w, (C.loc w).seq ≤ (C'.loc w).seq) : Fresh C' v :=
  fun w hw => lt_of_lt_of_le (h w hw) (hs w)

lemma opsOf_ne_nil_mono {α : List (Label P (laObj P))} {x : P} (ℓ : Label P (laObj P))
    (h : opsOf α x ≠ []) : opsOf (α ++ [ℓ]) x ≠ [] := by
  simp [opsOf_append, h]

lemma bInv_init : BInv (k := k) ([] : List (Label P (laObj P))) (alg1 k).initCfg where
  idle_iff q := by simp [Impl.initCfg, alg1, locInit]
  idle_seen q _ := rfl
  pend q h := absurd rfl h
  seen_inv q h := absurd rfl h
  mem_inv r x hx := by simp [Impl.initCfg, alg1, Triple.init] at hx
  col_inv q r x hx := by simp [Impl.initCfg, alg1, locInit, Triple.init] at hx
  self q := by simp [Impl.initCfg, alg1, locInit]
  fresh_mem r w hw := by simp [Impl.initCfg, alg1, Triple.init] at hw
  fresh_col q r w hw := by simp [Impl.initCfg, alg1, locInit, Triple.init] at hw
  out_eq q h := by simp [Impl.initCfg, alg1, locInit] at h
  resp q o ho := by simp at ho


lemma BInv.inv {α : List (Label P (laObj P))} {C C' : Cfg P k} {p : P} {o : Unit}
    (hI : BInv α C) (h : (alg1 k).step C (.inv p o) = some C') :
    BInv (α ++ [.inv p o]) C' := by
  obtain ⟨h1, h2, h3, h4⟩ := step_inv_alg1 h
  have hmono : ∀ x, opsOf α x ≠ [] → opsOf (α ++ [.inv p o]) x ≠ [] :=
    fun x hx => opsOf_ne_nil_mono _ hx
  have hp : opsOf (α ++ [.inv p o]) p ≠ [] := by simp [Label.invOf]
  have hseq : ∀ w, (C.loc w).seq ≤ (C'.loc w).seq := by
    intro w; rw [h3]; by_cases hw : w = p
    · subst hw; simp only [Function.update_self]; split_ifs <;> simp
    · simp [Function.update_of_ne hw]
  -- the new local state of `p`
  have hlp : C'.loc p = if (C.loc p).phase = .idle then { C.loc p with phase := .wr }
      else C.loc p := by rw [h3]; simp
  have hlq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by rw [h3]; simp [hq]
  have hph : (C'.loc p).phase ≠ .idle := by rw [hlp]; split_ifs with hh <;> simp [hh]
  constructor
  · intro q
    by_cases hq : q = p
    · subst hq; simp only [hph, false_iff]; exact hp
    · rw [hlq q hq, hI.idle_iff q, opsOf_concat]; simp [Label.invOf, Ne.symm hq]
  · intro q hq'
    by_cases hq : q = p
    · subst hq; exact absurd hq' hph
    · rw [hlq q hq] at hq' ⊢; exact hI.idle_seen q hq'
  · intro q _
    by_cases hq : q = p
    · subst hq; exact hph
    · rw [hlq q hq]; exact hI.pend q (by rw [h2, Function.update_of_ne hq] at *; assumption)
  · intro q hq' x hx
    by_cases hq : q = p
    · subst hq
      by_cases hid : (C.loc q).phase = .idle
      · rw [hlp, ite_eq_left hid] at hx
        simp only [hI.idle_seen q hid, Finset.mem_singleton] at hx; subst hx; exact hp
      · rw [hlp, ite_eq_right hid] at hx; exact hmono x (hI.seen_inv q hid x hx)
    · rw [hlq q hq] at hq' hx; exact hmono x (hI.seen_inv q hq' x hx)
  · intro r x hx; rw [h4] at hx; exact hmono x (hI.mem_inv r x hx)
  · intro q r x hx
    by_cases hq : q = p
    · subst hq; rw [hlp] at hx; split_ifs at hx <;> exact hmono x (hI.col_inv q r x hx)
    · rw [hlq q hq] at hx; exact hmono x (hI.col_inv q r x hx)
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hlp]; split_ifs <;> exact hI.self q
    · rw [hlq q hq]; exact hI.self q
  · intro r; rw [h4]; exact (hI.fresh_mem r).mono hseq
  · intro q r
    by_cases hq : q = p
    · subst hq; rw [hlp]; split_ifs <;> exact (hI.fresh_col q r).mono hseq
    · rw [hlq q hq]; exact (hI.fresh_col q r).mono hseq
  · intro q hq'
    by_cases hq : q = p
    · subst hq
      by_cases hid : (C.loc q).phase = .idle
      · rw [hlp, ite_eq_left hid] at hq'; simp at hq'
      · rw [hlp, ite_eq_right hid] at hq' ⊢; exact hI.out_eq q hq'
    · rw [hlq q hq] at hq' ⊢; exact hI.out_eq q hq'
  · intro q o' ho'
    have hr : respsOf (α ++ [.inv p o]) q = respsOf α q := by
      rw [respsOf_concat]; exact List.append_nil _
    rw [hr] at ho'
    obtain ⟨hd, he⟩ := hI.resp q o' ho'
    by_cases hq : q = p
    · subst hq; rw [hlp, ite_eq_right (by simp [hd])]; exact ⟨hd, he⟩
    · rw [hlq q hq]; exact ⟨hd, he⟩


lemma BInv.ret {α : List (Label P (laObj P))} {C C' : Cfg P k} {p : P} {o : Finset P}
    (hI : BInv α C) (h : (alg1 k).step C (.ret p o) = some C') :
    BInv (α ++ [.ret p o]) C' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := step_ret_alg1 h
  have hops : ∀ x, opsOf (α ++ [.ret p o]) x = opsOf α x := fun x => by
    rw [opsOf_concat]; exact List.append_nil _
  have hdone : (C.loc p).phase = .done ∧ o = (C.loc p).out := by
    rcases h5 with h5 | h5
    · exact h5
    · exact absurd h5 (hI.pend p h1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [h4, hops]; exact hI.idle_iff q
  · intro q; rw [h4]; exact hI.idle_seen q
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [h4]; exact hI.pend q h1
    · rw [h4]; exact hI.pend q (by rw [h2, Function.update_of_ne hqp] at hq; exact hq)
  · intro q; simp only [h4, hops]; exact hI.seen_inv q
  · intro r; simp only [h3, hops]; exact hI.mem_inv r
  · intro q r; simp only [h4, hops]; exact hI.col_inv q r
  · intro q; rw [h4]; exact hI.self q
  · intro r; rw [h3]; exact fun w hw => by rw [h4]; exact hI.fresh_mem r w hw
  · intro q r; rw [Fresh, h4]; exact fun w hw => hI.fresh_col q r w hw
  · intro q; rw [h4]; exact hI.out_eq q
  · intro q o' ho'
    rw [h4]
    rw [respsOf_concat, List.mem_append] at ho'
    rcases ho' with ho' | ho'
    · exact hI.resp q o' ho'
    · by_cases hqp : q = p
      · subst hqp
        have : o' = o := by simp [Label.retOf] at ho'; exact Option.some_injective _ ho'.symm
        subst this; exact hdone
      · simp [Label.retOf, Ne.symm hqp] at ho'


/-- Generic preservation of `BInv` by an internal step of `p` that replaces its local state by
`l'`. -/
lemma BInv.tau_gen {α : List (Label P (laObj P))} {C C' : Cfg P k} {p : P} {l' : Loc P k}
    (hI : BInv α C) (hpend : C'.pend = C.pend) (hloc : C'.loc = Function.update C.loc p l')
    (hph : (C.loc p).phase ≠ .idle) (hnd : (C.loc p).phase ≠ .done)
    (hph' : l'.phase ≠ .idle) (hout : l'.phase = .done → l'.out = l'.seen)
    (hself : p ∈ l'.seen) (hseen : ∀ x ∈ l'.seen, opsOf α x ≠ [])
    (hcol : ∀ r, ∀ x ∈ (l'.collect r).seen, opsOf α x ≠ [])
    (hseq : (C.loc p).seq ≤ l'.seq)
    (hfcol : ∀ r, Fresh C' (l'.collect r))
    (hmem : ∀ r, ∀ x ∈ (C'.mem r).seen, opsOf α x ≠ [])
    (hfmem : ∀ r, Fresh C' (C'.mem r)) :
    BInv (α ++ [.tau p]) C' := by
  have hops : ∀ x, opsOf (α ++ [.tau p]) x = opsOf α x := fun x => by
    rw [opsOf_concat]; exact List.append_nil _
  have hresps : ∀ x, respsOf (α ++ [.tau p]) x = respsOf α x := fun x => by
    rw [respsOf_concat]; exact List.append_nil _
  have hlq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by rw [hloc]; simp [hq]
  have hlp : C'.loc p = l' := by rw [hloc]; simp
  have hsq : ∀ w, (C.loc w).seq ≤ (C'.loc w).seq := by
    intro w; by_cases hw : w = p
    · subst hw; rw [hlp]; exact hseq
    · rw [hlq w hw]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hops]
    by_cases hq : q = p
    · subst hq; rw [hlp, ← hI.idle_iff q]; simp [hph, hph']
    · rw [hlq q hq]; exact hI.idle_iff q
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hlp] at hq'; exact absurd hq' hph'
    · rw [hlq q hq] at hq' ⊢; exact hI.idle_seen q hq'
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hlp]; exact hph'
    · rw [hlq q hq]; exact hI.pend q (by rw [hpend] at hq'; exact hq')
  · intro q hq' x hx; rw [hops]
    by_cases hq : q = p
    · subst hq; rw [hlp] at hx; exact hseen x hx
    · rw [hlq q hq] at hq' hx; exact hI.seen_inv q hq' x hx
  · intro r x hx; rw [hops]; exact hmem r x hx
  · intro q r x hx; rw [hops]
    by_cases hq : q = p
    · subst hq; rw [hlp] at hx; exact hcol r x hx
    · rw [hlq q hq] at hx; exact hI.col_inv q r x hx
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hlp]; exact hself
    · rw [hlq q hq]; exact hI.self q
  · exact hfmem
  · intro q r
    by_cases hq : q = p
    · subst hq; rw [hlp]; exact hfcol r
    · rw [hlq q hq]; exact (hI.fresh_col q r).mono hsq
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hlp] at hq' ⊢; exact hout hq'
    · rw [hlq q hq] at hq' ⊢; exact hI.out_eq q hq'
  · intro q o ho; rw [hresps] at ho
    by_cases hq : q = p
    · subst hq; exact absurd (hI.resp q o ho).1 hnd
    · rw [hlq q hq]; exact hI.resp q o ho

lemma BInv.seq_le_of_tau {C C' : Cfg P k} {p : P} {l' : Loc P k}
    (hloc : C'.loc = Function.update C.loc p l') (hseq : (C.loc p).seq ≤ l'.seq) (w : P) :
    (C.loc w).seq ≤ (C'.loc w).seq := by
  rw [hloc]; by_cases hw : w = p
  · subst hw; simpa using hseq
  · simp [hw]

lemma BInv.tau {α : List (Label P (laObj P))} {C C' : Cfg P k} {p : P}
    (hI : BInv α C) (h : (alg1 k).step C (.tau p) = some C') :
    BInv (α ++ [.tau p]) C' := by
  obtain ⟨h1, h2, h3⟩ := step_tau_alg1 h
  have hpi := hI.pend p h1
  rcases h3 with ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩
  · have hsq := BInv.seq_le_of_tau hl (by simp)
    refine hI.tau_gen h2 hl hpi (by simp [hph]) (by simp) (by simp) (by simpa using hI.self p)
      (by simpa using hI.seen_inv p hpi) (by simpa using hI.col_inv p) (by simp) ?_ ?_ ?_
    · intro r; simpa using (hI.fresh_col p r).mono hsq
    · intro r x hx; rw [hm] at hx
      by_cases hr : r = (C.loc p).i
      · subst hr; simp only [Function.update_self] at hx; exact hI.seen_inv p hpi x hx
      · rw [Function.update_of_ne hr] at hx; exact hI.mem_inv r x hx
    · intro r w hw
      rw [hm] at hw ⊢
      by_cases hr : r = (C.loc p).i
      · subst hr; simp only [Function.update_self, Option.some.injEq] at hw ⊢; subst hw
        rw [hl]; simp
      · rw [Function.update_of_ne hr] at hw ⊢
        exact lt_of_lt_of_le (hI.fresh_mem r w hw) (hsq w)
  · have hsq := BInv.seq_le_of_tau hl (by simp)
    refine hI.tau_gen h2 hl hpi (by simp [hph]) ?_ ?_ ?_ ?_ ?_ (by simp) ?_ ?_ ?_
    · rw [afterCol1_phase]; split_ifs <;> simp [hph]
    · rw [afterCol1_phase]; split_ifs <;> simp [hph]
    · simp [hI.self p]
    · intro x hx; simp only [afterCol1_seen, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hI.seen_inv p hpi x hx
      · exact hI.mem_inv _ x hx
    · intro r x hx; simp only [afterCol1_collect] at hx
      by_cases hr : r = (C.loc p).j
      · subst hr; simp only [Function.update_self] at hx; exact hI.mem_inv _ x hx
      · rw [Function.update_of_ne hr] at hx; exact hI.col_inv p r x hx
    · intro r; simp only [afterCol1_collect]
      by_cases hr : r = (C.loc p).j
      · subst hr; simp only [Function.update_self]; exact (hI.fresh_mem _).mono hsq
      · rw [Function.update_of_ne hr]; exact (hI.fresh_col p r).mono hsq
    · rw [hm]; exact hI.mem_inv
    · rw [hm]; exact fun r => (hI.fresh_mem r).mono hsq
  · have hsq := BInv.seq_le_of_tau hl (by simp)
    have hph2 := afterCol2_phase (C.loc p) (C.mem (C.loc p).j) hph
    refine hI.tau_gen h2 hl hpi (by simp [hph]) ?_ ?_ ?_ ?_ ?_ (by simp) ?_ ?_ ?_
    · rcases hph2 with h' | h' | ⟨h', -⟩ <;> simp [h']
    · intro hd; rcases hph2 with h' | h' | ⟨h', h''⟩
      · simp [h'] at hd
      · simp [h'] at hd
      · exact h''
    · simp [hI.self p]
    · intro x hx; simp only [afterCol2_seen, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hI.seen_inv p hpi x hx
      · exact hI.col_inv p _ x hx
    · intro r x hx; simp only [afterCol2_collect] at hx; exact hI.col_inv p r x hx
    · intro r; simp only [afterCol2_collect]; exact (hI.fresh_col p r).mono hsq
    · rw [hm]; exact hI.mem_inv
    · rw [hm]; exact fun r => (hI.fresh_mem r).mono hsq

/-- The basic invariants hold along every execution of Algorithm 1. -/
theorem bInv_of_run {α : List (Label P (laObj P))} {C : Cfg P k}
    (h : (alg1 k).run α = some C) : BInv α C := by
  refine Impl.run_induction (I := alg1 k) (Q := BInv) bInv_init ?_ h
  intro α C ℓ C' _ hI hs
  cases ℓ with
  | inv p o => exact hI.inv hs
  | ret p o => exact hI.ret hs
  | tau p => exact hI.tau hs

end Cslib.SharedMemory.StrangerFree
