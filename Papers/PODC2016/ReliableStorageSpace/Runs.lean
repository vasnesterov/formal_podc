import Papers.PODC2016.ReliableStorageSpace.Adversary

/-!
# Bookkeeping lemmas for runs

How `cur`, `hist`, `tick` and the pending list evolve; the invariants `CurInv` (an outstanding operation
was invoked in the history) and `WriteOnly` (no read was invoked).
-/

noncomputable section

namespace Podc.ReliableStorageSpace

open Finset Classical

variable {C N J V : Type}

namespace Alg

variable (A : Alg C N J V)

/-- How `cur c` changes in a step. -/
theorem cur_step_cases (X : A.Config) (e : Event C) (c : C) :
    (A.step X e).cur c = X.cur c ∨
    ((A.step X e).cur c = none ∧ X.cur c ≠ none ∧ e = .step c ∧
      ∃ out, (A.step X e).hist = X.hist ++ [.ret c (X.cnt c) out]) ∨
    (∃ op, e = .inv c op ∧ X.cur c = none ∧ (A.step X e).cur c = some op) := by
  rcases step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o, r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1]
  · exact Or.inl rfl
  · exact Or.inl rfl
  · by_cases hcc : c = c'
    · subst hcc; exact Or.inr (Or.inr ⟨op, rfl, hc, by simp⟩)
    · exact Or.inl (by simp [Function.update_apply, hcc])
  · exact Or.inl rfl
  · by_cases hcc : c = c'
    · subst hcc
      exact Or.inr (Or.inl ⟨by simp, by simp [hc], rfl, _, rfl⟩)
    · exact Or.inl (by simp [Function.update_apply, hcc])
  · exact Or.inl rfl

/-- An outstanding operation was invoked in the history. -/
def CurInv (X : A.Config) : Prop := ∀ c op, X.cur c = some op → Label.inv c (X.cnt c) op ∈ X.hist

theorem curInv_step {X : A.Config} (h : A.CurInv X) (e : Event C) : A.CurInv (A.step X e) := by
  intro c op hc
  rcases step_cases X e with h1 | h1 | ⟨c', op', rfl, hc', h1⟩ | ⟨c', op', o, r, l, rfl, hc', ha, h1⟩ |
    ⟨c', op', l, rfl, hc', ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1] at hc ⊢
  · exact h c op hc
  · exact h c op hc
  · by_cases hcc : c = c'
    · subst hcc; simp at hc; subst hc; simp
    · simp only [Function.update_apply, hcc, if_false] at hc
      exact List.mem_append_left _ (h c op hc)
  · exact h c op hc
  · by_cases hcc : c = c'
    · subst hcc; simp at hc
    · simp only [Function.update_apply, hcc, if_false] at hc ⊢
      exact List.mem_append_left _ (h c op hc)
  · exact h c op hc

theorem curInv_runFrom {X : A.Config} (h : A.CurInv X) (evs : List (Event C)) :
    A.CurInv (A.runFrom X evs) := by
  induction evs generalizing X with
  | nil => exact h
  | cons e evs ih => exact ih (A.curInv_step h e)

theorem curInv_init : A.CurInv A.init := by intro c op h; simp [init] at h

theorem curInv_srun {X : A.Config} (h : A.CurInv X) (σ : A.Config → Event C) (t : ℕ) :
    A.CurInv (A.srun X σ t) := by
  induction t with
  | zero => exact h
  | succ t ih => exact A.curInv_step ih _

/-- Only writes are outstanding. -/
def WriteOnly (X : A.Config) : Prop := ∀ c, X.cur c = none ∨ X.cur c = some .write

theorem writeOnly_step {X : A.Config} (h : A.WriteOnly X) (e : Event C)
    (he : ∀ c, e ≠ .inv c .read) : A.WriteOnly (A.step X e) := by
  intro c
  rcases A.cur_step_cases X e c with h1 | ⟨h1, -⟩ | ⟨op, rfl, -, h1⟩
  · rw [h1]; exact h c
  · exact Or.inl h1
  · cases op
    · exact Or.inr h1
    · exact absurd rfl (he c)

/-- `tick` counts `step` events. -/
theorem tick_step (X : A.Config) (e : Event C) :
    (A.step X e).tick = X.tick + (match e with | .step _ => 1 | _ => 0) := by
  rcases step_cases X e with h1 | h1 | ⟨c', op', rfl, hc', h1⟩ | ⟨c', op', o, r, l, rfl, hc', ha, h1⟩ |
    ⟨c', op', l, rfl, hc', ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1]
  · rcases e with ⟨c, op⟩ | c | ⟨c, m⟩ | _
    · rfl
    · exfalso
      rcases hc : X.cur c with _ | op
      · rw [step_step_none hc] at h1
        have := congrArg Config.tick h1; simp at this
      · rcases ha : A.act c (X.cnt c) op (X.loc c) with ⟨o, r, l⟩ | l | _
        · rw [step_step_trigger hc ha] at h1
          have := congrArg Config.tick h1; simp at this
        · rw [step_step_ret hc ha] at h1
          have := congrArg Config.tick h1; simp at this
        · rw [step_step_idle hc ha] at h1
          have := congrArg Config.tick h1; simp at this
    · rfl
    · rfl
  · rcases e with ⟨c, op⟩ | c | ⟨c, m⟩ | _
    · exfalso
      by_cases hc : X.cur c = none
      · rw [step_inv_free hc] at h1
        have := congrArg Config.tick h1; simp at this
      · rw [step_inv_busy hc] at h1
        have := congrArg Config.tick h1; simp at this
    · rfl
    · exfalso
      rcases hp : A.findP X c m with _ | p
      · rw [step_exec_none hp] at h1
        have := congrArg Config.tick h1; simp at this
      · rw [step_exec_some hp] at h1
        have := congrArg Config.tick h1; simp at this
    · exfalso
      have := congrArg Config.tick h1; simp at this
  all_goals rfl

/-- How the pending list evolves. -/
theorem pend_step (X : A.Config) (e : Event C) (p : Pend C N A.R)
    (hp : p ∈ (A.step X e).pend) :
    p ∈ X.pend ∨ (e = .step p.cl ∧ p.idx = X.nrmw p.cl) := by
  rcases step_cases X e with h1 | h1 | ⟨c', op', rfl, hc', h1⟩ | ⟨c', op', o, r, l, rfl, hc', ha, h1⟩ |
    ⟨c', op', l, rfl, hc', ha, h1⟩ | ⟨c', m, q, rfl, hq, h1⟩ <;> rw [h1] at hp
  · exact Or.inl hp
  · exact Or.inl hp
  · exact Or.inl hp
  · simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact Or.inl hp
    · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl hp
  · exact Or.inl (List.mem_of_mem_filter hp)

theorem nrmw_step_mono (X : A.Config) (e : Event C) (c : C) : X.nrmw c ≤ (A.step X e).nrmw c := by
  rcases step_cases X e with h1 | h1 | ⟨c', op', rfl, hc', h1⟩ | ⟨c', op', o, r, l, rfl, hc', ha, h1⟩ |
    ⟨c', op', l, rfl, hc', ha, h1⟩ | ⟨c', m, q, rfl, hq, h1⟩ <;> rw [h1]
  · simp only [Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> omega

/-- A step of another client does not change `c`'s local state and counter. -/
theorem step_other (X : A.Config) {c c' : C} (h : c' ≠ c) :
    (A.step X (.step c')).loc c = X.loc c ∧ (A.step X (.step c')).cnt c = X.cnt c := by
  rcases hc : X.cur c' with _ | op
  · rw [step_step_none hc]; exact ⟨rfl, rfl⟩
  · rcases ha : A.act c' (X.cnt c') op (X.loc c') with ⟨o, r, l⟩ | l | _
    · rw [step_step_trigger hc ha]; simp [Function.update_apply, Ne.symm h]
    · rw [step_step_ret hc ha]; simp [Function.update_apply, Ne.symm h]
    · rw [step_step_idle hc ha]; exact ⟨rfl, rfl⟩

/-! ### Crashing clients: removing the steps of dead clients -/

/-- `X'` is `X` with the steps of the clients in `D` (after their crash) removed. -/
structure Rel (D : C → Prop) (X X' : A.Config) : Prop where
  obj : X'.obj = X.obj
  cur : X'.cur = X.cur
  cnt : X'.cnt = X.cnt
  hist : X'.hist = X.hist
  loc : ∀ c, ¬ D c → X'.loc c = X.loc c
  nrmw : ∀ c, ¬ D c → X'.nrmw c = X.nrmw c
  sub : X'.pend.Sublist X.pend
  miss : ∀ p ∈ X.pend, p ∉ X'.pend → D p.cl

variable {A}

theorem Rel.mono {D D' : C → Prop} {X X' : A.Config} (h : A.Rel D X X') (hD : ∀ c, D c → D' c) :
    A.Rel D' X X' :=
  ⟨h.obj, h.cur, h.cnt, h.hist, fun c hc => h.loc c (fun h' => hc (hD c h')),
    fun c hc => h.nrmw c (fun h' => hc (hD c h')), h.sub, fun p hp hp' => hD _ (h.miss p hp hp')⟩

/-- A step of a dead client that does not return can be dropped. -/
theorem Rel.skip {D : C → Prop} {X X' : A.Config} (h : A.Rel D X X') {c : C} (hc : D c)
    (hcur : (A.step X (.step c)).cur c = X.cur c) : A.Rel D (A.step X (.step c)) X' := by
  rcases hcc : X.cur c with _ | op
  · rw [step_step_none hcc]; exact ⟨h.obj, h.cur, h.cnt, h.hist, h.loc, h.nrmw, h.sub, h.miss⟩
  · rcases ha : A.act c (X.cnt c) op (X.loc c) with ⟨o, r, l⟩ | l | _
    · rw [step_step_trigger hcc ha]
      refine ⟨h.obj, h.cur, h.cnt, h.hist, fun c' hc' => ?_, fun c' hc' => ?_,
        h.sub.trans (List.sublist_append_left _ _), fun p hp hp' => ?_⟩
      · have : c' ≠ c := fun e => hc' (e ▸ hc)
        simp [Function.update_apply, this, h.loc c' hc']
      · have : c' ≠ c := fun e => hc' (e ▸ hc)
        simp [Function.update_apply, this, h.nrmw c' hc']
      · simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact h.miss p hp hp'
        · exact hc
    · rw [step_step_ret hcc ha] at hcur; simp [hcc] at hcur
    · rw [step_step_idle hcc ha]; exact ⟨h.obj, h.cur, h.cnt, h.hist, h.loc, h.nrmw, h.sub, h.miss⟩

/-- Events of live clients (and effective executions of their RMWs) keep the relation. -/
theorem Rel.step {D : C → Prop} {X X' : A.Config} (h : A.Rel D X X') (hok : A.PendOK X)
    (hok' : A.PendOK X') (e : Event C) (hstep : ∀ c, e = .step c → ¬ D c)
    (hexec : ∀ c m p, e = .exec c m → A.findP X c m = some p → ¬ D c) :
    A.Rel D (A.step X e) (A.step X' e) := by
  rcases e with ⟨c, op⟩ | c | ⟨c, m⟩ | _
  · by_cases hc : X.cur c = none
    · have hc' : X'.cur c = none := by rw [h.cur]; exact hc
      rw [step_inv_free hc, step_inv_free hc']
      refine ⟨h.obj, by rw [h.cur], h.cnt, by rw [h.hist, h.cnt], fun c' hc'' => ?_, h.nrmw, h.sub,
        h.miss⟩
      simp only [Function.update_apply]
      split_ifs with hcc
      · subst hcc; rw [h.loc c' hc'', h.cnt]
      · exact h.loc c' hc''
    · have hc' : X'.cur c ≠ none := by rw [h.cur]; exact hc
      rw [step_inv_busy hc, step_inv_busy hc']; exact h
  · have hD := hstep c rfl
    rcases hcc : X.cur c with _ | op
    · have hcc' : X'.cur c = none := by rw [h.cur]; exact hcc
      rw [step_step_none hcc, step_step_none hcc']
      exact ⟨h.obj, h.cur, h.cnt, h.hist, h.loc, h.nrmw, h.sub, h.miss⟩
    · have hcc' : X'.cur c = some op := by rw [h.cur]; exact hcc
      rcases ha : A.act c (X.cnt c) op (X.loc c) with ⟨o, r, l⟩ | l | _ <;>
      have ha' := ha <;> rw [← h.cnt, ← h.loc c hD] at ha'
      · rw [step_step_trigger hcc ha, step_step_trigger hcc' ha']
        refine ⟨h.obj, h.cur, h.cnt, h.hist, fun c' hc' => ?_, fun c' hc' => ?_, ?_, ?_⟩
        · simp only [Function.update_apply]; split_ifs
          · rfl
          · exact h.loc c' hc'
        · simp only [Function.update_apply]; split_ifs with hh
          · subst hh; rw [h.nrmw c' hD]
          · exact h.nrmw c' hc'
        · rw [h.nrmw c hD]; exact h.sub.append_right _
        · intro p hp hp'
          simp only [List.mem_append, List.mem_singleton] at hp hp'
          rcases hp with hp | rfl
          · exact h.miss p hp (fun h' => hp' (Or.inl h'))
          · exact absurd (Or.inr (by rw [h.nrmw _ hD])) hp'
      · rw [step_step_ret hcc ha, step_step_ret hcc' ha']
        refine ⟨h.obj, by rw [h.cur], by rw [h.cnt], by rw [h.hist, h.cnt, h.loc c hD],
          fun c' hc' => ?_, h.nrmw, h.sub, h.miss⟩
        simp only [Function.update_apply]; split_ifs
        · rfl
        · exact h.loc c' hc'
      · rw [step_step_idle hcc ha, step_step_idle hcc' ha']
        exact ⟨h.obj, h.cur, h.cnt, h.hist, h.loc, h.nrmw, h.sub, h.miss⟩
  · rcases hp : A.findP X c m with _ | p
    · have hp' : A.findP X' c m = none := by
        rcases hq : A.findP X' c m with _ | q
        · rfl
        · obtain ⟨hq1, rfl, rfl⟩ := findP_spec hq
          rw [hok.findP_eq (h.sub.subset hq1)] at hp
          cases hp
      rw [step_exec_none hp, step_exec_none hp']; exact h
    · have hD := hexec c m p rfl hp
      obtain ⟨hp1, hpc, hpm⟩ := findP_spec hp
      have hpX' : p ∈ X'.pend := by
        by_contra hn
        exact hD (hpc ▸ h.miss p hp1 hn)
      have hp' : A.findP X' c m = some p := by
        rw [← hpc, ← hpm]; exact hok'.findP_eq hpX'
      rw [step_exec_some hp, step_exec_some hp']
      refine ⟨by rw [h.obj], h.cur, h.cnt, h.hist, fun c' hc' => ?_, h.nrmw, h.sub.filter _,
        fun q hq hq' => ?_⟩
      · simp only [Function.update_apply]; split_ifs with hh
        · subst hh; rw [h.loc c' hD, h.obj]
        · exact h.loc c' hc'
      · rw [List.mem_filter] at hq
        exact h.miss q hq.1 (fun h' => hq' (List.mem_filter.2 ⟨h', hq.2⟩))
  · exact h

end Alg

end Podc.ReliableStorageSpace

end
