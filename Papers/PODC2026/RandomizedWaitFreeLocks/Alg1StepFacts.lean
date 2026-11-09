import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1Safety

/-!
# Algorithm 1: elementary facts about single steps (used by the probabilistic analysis)
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

/-- The process acting in a step. -/
def Act.actor : Act P D → P
  | .invoke p _ => p
  | .sched p => p

lemma step_loc_ne (c : Cfg P D) (a : Act P D) (b : Bool) (x : P) (hx : x ≠ a.actor) :
    (step own c a b).1.loc x = c.loc x := by
  cases a with
  | invoke q δ =>
    simp only [Act.actor] at hx
    simp only [step]; split_ifs <;> simp [Cfg.tick, Cfg.upd, hx]
  | sched q =>
    simp only [Act.actor] at hx
    simp only [step]
    split <;> (try split) <;> (try split) <;> simp [Cfg.tick, Cfg.upd, hx]

lemma step_sched_fixed (c : Cfg P D) (q : P) (b : Bool) :
    ((step own c (.sched q) b).1.loc q).call = (c.loc q).call ∧
    ((step own c (.sched q) b).1.loc q).b = (c.loc q).b ∧
    ((step own c (.sched q) b).1.loc q).fT = (c.loc q).fT := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> simp [Cfg.tick, Cfg.upd]

lemma step_sched_dsc (c : Cfg P D) (q : P) (b : Bool) (h : (c.loc q).pc ≠ .ret) :
    ((step own c (.sched q) b).1.loc q).dsc = (c.loc q).dsc := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> simp_all [Cfg.tick, Cfg.upd]

lemma step_sched_l6 (c : Cfg P D) (q : P) (b : Bool) (h : (c.loc q).pc ≠ .wr) :
    ((step own c (.sched q) b).1.loc q).l6 = (c.loc q).l6 := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> simp_all [Cfg.tick, Cfg.upd]

lemma step_sched_hap (c : Cfg P D) (q : P) (b : Bool) (h : (c.loc q).pc ≠ .wr) :
    (((step own c (.sched q) b).1.loc q).pc.hap = true → (c.loc q).pc.hap = true) ∧
    ((c.loc q).pc.hap = true → ((step own c (.sched q) b).1.loc q).pc.hap = true ∨
      ((step own c (.sched q) b).1.loc q).pc = .rd8) := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> simp_all [Cfg.tick, Cfg.upd, PC.hap]

lemma step_sched_failed (c : Cfg P D) (q : P) (b : Bool) (h : (c.loc q).pc ≠ .ret) :
    (step own c (.sched q) b).1.failed = c.failed := by
  simp only [step]
  split <;> (try split) <;> (try split) <;> simp_all [Cfg.tick, Cfg.upd]

lemma step_failed_ne (c : Cfg P D) (a : Act P D) (b : Bool) (x : P) (hx : x ≠ a.actor) :
    (step own c a b).1.failed x = c.failed x := by
  cases a with
  | invoke q δ => simp only [step]; split_ifs <;> simp [Cfg.tick, Cfg.upd]
  | sched q =>
    simp only [Act.actor] at hx
    simp only [step]
    split <;> (try split) <;> (try split) <;> simp [Cfg.tick, Cfg.upd, hx, Function.update_apply]

lemma step_invoke_failed (c : Cfg P D) (q : P) (δ : D) (b : Bool) :
    (step own c (.invoke q δ) b).1.failed = c.failed := by
  simp only [step]; split_ifs <;> simp [Cfg.tick, Cfg.upd]

lemma step_act_ne (c : Cfg P D) (a : Act P D) (b : Bool) (x : P) (hx : x ≠ a.actor) :
    x ∈ (step own c a b).1.act ↔ x ∈ c.act := by
  cases a with
  | invoke q δ =>
    simp only [Act.actor] at hx
    simp only [step]; split_ifs <;> simp [Cfg.tick, Cfg.upd, hx]
  | sched q =>
    simp only [Act.actor] at hx
    simp only [step]
    split <;> (try split) <;> (try split) <;> simp [Cfg.tick, Cfg.upd, hx]

lemma step_RW (c : Cfg P D) (a : Act P D) (b : Bool)
    (h : ¬ (∃ q, a = .sched q ∧ (c.loc q).pc = .wr ∧ b = true)) :
    (step own c a b).1.R = c.R ∧ (step own c a b).1.lastW = c.lastW := by
  cases a with
  | invoke q δ => simp only [step]; split_ifs <;> simp [Cfg.tick, Cfg.upd]
  | sched q =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> simp_all [Cfg.tick, Cfg.upd]

lemma step_eT_ne (c : Cfg P D) (a : Act P D) (b : Bool) (d : D) (h : c.eT d ≠ 0) :
    (step own c a b).1.eT d ≠ 0 := by
  cases a with
  | invoke q δ => simp only [step]; split_ifs <;> simpa [Cfg.tick, Cfg.upd]
  | sched q =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      simp_all [Cfg.tick, Cfg.upd, Function.update_apply] <;> (try split_ifs) <;> (try simp_all)

lemma step_ret (c : Cfg P D) (q : P) (b : Bool) (h : (c.loc q).pc = .ret) :
    ((step own c (.sched q) b).1.loc q).dsc = none ∧
    ∀ j, (step own c (.sched q) b).1.failed q j = true → c.failed q j = true ∨
      (j = (c.loc q).call ∧ ∃ d, (c.loc q).dsc = some d ∧ c.done d = false) := by
  simp only [step, h]
  split
  · rename_i d hd
    split_ifs with hdn
    · refine ⟨by simp [Cfg.tick, Cfg.upd], fun j hj => Or.inl (by simpa [Cfg.tick, Cfg.upd] using hj)⟩
    · refine ⟨by simp [Cfg.tick, Cfg.upd], fun j hj => ?_⟩
      simp only [Function.update_apply, if_true] at hj
      split_ifs at hj with hjk
      · right; exact ⟨hjk, d, hd, by simpa using hdn⟩
      · left; exact hj
  · rename_i hd
    exact ⟨by simpa [Cfg.tick] using hd, fun j hj => Or.inl (by simpa [Cfg.tick] using hj)⟩

/-- Ghost bookkeeping of the call counters: the `j`-th call of `x` can have failed only if it
is over. -/
def FailInv (c : Cfg P D) : Prop :=
  ∀ x j, c.failed x j = true → j ≤ (c.loc x).call ∧ (j = (c.loc x).call → (c.loc x).pc = .idle)

lemma failInv_reach {c : Cfg P D} (hc : Reach own c) : FailInv c := by
  refine Reachable.induction (init := init) (step := step own) (Q := FailInv) ?_ ?_ hc
  · intro x j h; simp [init] at h
  · intro c a b _ hJ x j hj
    by_cases hx : x = a.actor
    · subst hx
      cases a with
      | invoke q δ =>
        simp only [Act.actor] at hj ⊢
        rw [step_invoke_failed] at hj
        obtain ⟨h1, h2⟩ := hJ q j hj
        simp only [step]
        split_ifs with hg
        · simp [Cfg.tick, Cfg.upd]; omega
        · exact ⟨h1, h2⟩
      | sched q =>
        simp only [Act.actor] at hj ⊢
        obtain ⟨hc1, -, -⟩ := step_sched_fixed own c q b
        rw [hc1]
        by_cases hr : (c.loc q).pc = .ret
        · obtain ⟨hd, hf⟩ := step_ret own c q b hr
          have hidle : ((step own c (.sched q) b).1.loc q).pc = .idle := by
            simp only [step, hr]; split
            · split_ifs <;> simp [Cfg.tick, Cfg.upd]
            · rename_i hdn
              have := (inv_reach own ‹_›).idle_iff q
              exact absurd (this.2 (by simpa using hdn)) (by rw [hr]; simp)
          rcases hf j hj with h | ⟨rfl, -⟩
          · exact ⟨(hJ q j h).1, fun _ => hidle⟩
          · exact ⟨le_rfl, fun _ => hidle⟩
        · rw [step_sched_failed own c q b hr] at hj
          obtain ⟨h1, h2⟩ := hJ q j hj
          refine ⟨h1, fun e => ?_⟩
          have := h2 e
          simp only [step, this, Cfg.tick]
    · rw [step_failed_ne own c a b x hx] at hj
      rw [step_loc_ne own c a b x hx]
      exact hJ x j hj

end Podc.RandomizedWaitFreeLocks.Alg1
