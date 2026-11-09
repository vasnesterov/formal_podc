import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1StepC

/-!
# Algorithm 1: safety — Observation 4.1, Lemma 4.3, Observation 4.2, Lemma 4.5 (state form)
and Theorem 4.4 ((S1) and (S2) for every execution)
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

lemma step_T (c : Cfg P D) (a : Act P D) (b : Bool) : (step own c a b).1.T = c.T + 1 := by
  cases a with
  | invoke p δ => simp only [step]; split_ifs <;> rfl
  | sched p =>
    simp only [step]
    split <;> (try split) <;> (try split) <;> rfl

lemma step_started (c : Cfg P D) (a : Act P D) (b : Bool) (d : D) :
    (step own c a b).1.started d = true ↔ c.started d = true ∨ (step own c a b).2 = .exS d := by
  cases a with
  | invoke p δ => simp only [step]; split_ifs <;> simp [Cfg.tick, Cfg.upd]
  | sched p =>
    simp only [step]
    split <;> (try split) <;> (try split) <;>
      (simp [Cfg.tick, Cfg.upd, Function.update_apply]; try (constructor <;> intro h <;> aesop))

lemma step_done (c : Cfg P D) (a : Act P D) (b : Bool) (d : D) :
    (step own c a b).1.done d = true ↔ c.done d = true ∨ (step own c a b).2 = .exE d := by
  cases a with
  | invoke p δ => simp only [step]; split_ifs <;> simp [Cfg.tick, Cfg.upd]
  | sched p =>
    simp only [step]
    split <;> (try split) <;> (try split) <;>
      (simp [Cfg.tick, Cfg.upd, Function.update_apply]; try (constructor <;> intro h <;> aesop))

lemma step_inv {c : Cfg P D} (hI : Inv own c) {a : Act P D} {b : Bool} {p : P} {d : D}
    (h : (step own c a b).2 = .inv p d) :
    (c.loc p).dsc = none ∧ ((step own c a b).1.loc p).dsc = some d ∧
      ((step own c a b).1.loc p).cidx = c.T := by
  cases a with
  | invoke q δ =>
    simp only [step] at h ⊢
    split_ifs at h ⊢ with hg
    cases h; refine ⟨(hI.idle_iff _).1 hg.1, ?_, ?_⟩ <;> simp [Cfg.tick, Cfg.upd]
  | sched q =>
    simp only [step] at h
    split at h <;> (try split at h) <;> (try split at h) <;> simp_all

lemma step_resp {c : Cfg P D} {a : Act P D} {b : Bool} {p : P} {d : D} {r : Bool}
    (h : (step own c a b).2 = .resp p d r) :
    (c.loc p).dsc = some d ∧ ((step own c a b).1.loc p).dsc = none ∧ (r = true ↔ c.done d = true) := by
  cases a with
  | invoke q δ =>
    simp only [step] at h; split_ifs at h <;> cases h
  | sched q =>
    simp only [step] at h ⊢
    split at h <;> (try split at h) <;> (try split at h) <;>
      simp_all [Cfg.tick, Cfg.upd]

lemma step_other {c : Cfg P D} {a : Act P D} {b : Bool} {p : P}
    (h1 : ∀ d, (step own c a b).2 ≠ .inv p d) (h2 : ∀ d r, (step own c a b).2 ≠ .resp p d r) :
    ((step own c a b).1.loc p).dsc = (c.loc p).dsc ∧
      ((step own c a b).1.loc p).cidx = (c.loc p).cidx := by
  cases a with
  | invoke q δ =>
    simp only [step] at h1 ⊢
    split_ifs at h1 ⊢ with hg
    · by_cases e : p = q
      · subst e; exact absurd rfl (h1 δ)
      · simp [Cfg.tick, Cfg.upd, e]
    · simp [Cfg.tick]
  | sched q =>
    by_cases e : p = q
    · subst e
      simp only [step] at h2 ⊢
      split <;> (try split) <;> (try split) <;> simp_all [Cfg.tick, Cfg.upd]
    · simp only [step]
      split <;> (try split) <;> (try split) <;> simp [Cfg.tick, Cfg.upd, e]

/-- The ghost observations of Algorithm 1 are coherent with its events. -/
lemma coherent : Coherent (P := P) (D := D) init (step own) (fun c d => c.started d = true)
    (fun c d => c.done d = true) (fun c p => (c.loc p).dsc) (fun c p => (c.loc p).cidx)
    (fun c => c.T) where
  clock_init := rfl
  clock_step c a b _ := step_T own c a b
  started_init d := by simp [init]
  started_step c a b d _ := step_started own c a b d
  done_init d := by simp [init]
  done_step c a b d _ := step_done own c a b d
  call_init p := rfl
  call_inv c a b p d hc h := step_inv own (inv_reach own hc) h
  call_resp c a b p d r _ h := step_resp own h
  call_other c a b p _ h1 h2 := step_other own h1 h2

/-- **Observation 4.1** (state form): throughout the execution interval of `ω.T`
(`ω` started, not yet done), `L = ω`. -/
theorem obs_4_1 {c : Cfg P D} (hc : Reach own c) (ω : D) (h1 : c.started ω = true)
    (h2 : c.done ω = false) : c.L = some ω :=
  (inv_reach own hc).e4 ω h1 h2

/-- **Observation 4.2** (state form): once `ω` has been promoted, its owner cannot reach
line 9 of its `TryLock(ω)` call before `ω` is done. -/
theorem obs_4_2 {c : Cfg P D} (hc : Reach own c) (ω : D) (h1 : c.eT ω ≠ 0)
    (h2 : (c.loc (own ω)).dsc = some ω)
    (h3 : (c.loc (own ω)).pc = .fad ∨ (c.loc (own ω)).pc = .ret) : c.done ω = true :=
  (inv_reach own hc).o2 ω h1 h2 h3

/-- **Lemma 4.3** (state form).  (a) a promoted descriptor is not written to `R` again: its
owner is never at line 6 of a call on it; (b) every promotion (non-trivial successful CAS of
line 4) installs a descriptor that has never been the value of `L`; (c) at that moment the
owner of the descriptor is inside its `TryLock` call, between lines 6 and 8. -/
theorem lemma_4_3 {c : Cfg P D} (hc : Reach own c) :
    (∀ δ, c.eT δ ≠ 0 → ¬ ((c.loc (own δ)).pc = .wr ∧ (c.loc (own δ)).dsc = some δ)) ∧
    (∀ x i, (c.loc x).pc = .cas i → c.L = (c.loc x).w → (c.loc x).d ≠ (c.loc x).w →
      ∃ δ, (c.loc x).d = some δ ∧ c.eT δ = 0 ∧ (c.loc (own δ)).dsc = some δ ∧
        (c.loc (own δ)).pc.hap = true) := by
  have hI := inv_reach own hc
  refine ⟨fun δ he ⟨h1, h2⟩ => he (hI.eT_wr own h1 h2), fun x i => hI.f4 x i⟩

/-- **Lemma 4.5** (state form): while the last value written to `R` has not been promoted, no
process whose line 6 is not older than that write has completed its two `HelpAndPromote()`
calls (it is still inside lines 1–4). -/
theorem lemma_4_5 {c : Cfg P D} (hc : Reach own c) (x : P) (δ : D) (hR : c.R = some δ)
    (he : c.eT δ = 0) (hx : ((c.loc x).pc.hap || (c.loc x).pc.post) = true)
    (hl : c.lastW ≤ (c.loc x).l6) : (c.loc x).pc.hap = true :=
  (inv_reach own hc).g1 x δ hR he hx hl

/-- **Theorem 4.4.** Algorithm 1 satisfies (S1) and (S2) in every execution (for every
adversary and every outcome of the coin flips). -/
theorem theorem_4_4 (xs : List (Act P D × Bool)) :
    S1 (run init (step own) xs).2 ∧ S2 (run init (step own) xs).2 := by
  refine s1_s2_of_invariants (coherent own) ?_ ?_ ?_ xs
  · intro c hc d₁ d₂ hne h1 h2 h3 h4
    have hI := inv_reach own hc
    simp only [Bool.not_eq_true] at h2 h4
    have e1 := hI.e4 d₁ h1 h2
    have e2 := hI.e4 d₂ h3 h4
    rw [e1] at e2; exact hne (Option.some_injective _ e2)
  · intro c hc d h1 h2
    have hI := inv_reach own hc
    simp only [Bool.not_eq_true] at h2
    have hL := hI.e4 d h1 h2
    rcases hI.o1 d (hI.f1 d hL).2 with h3 | ⟨h3, -⟩
    · rw [hI.o4 d h3] at h2; cases h2
    · exact ⟨own d, h3⟩
  · intro c a b p d r hc h h1
    have hI := inv_reach own hc
    obtain ⟨hd, -, -⟩ := step_resp own h
    by_contra h2
    simp only [Bool.not_eq_true] at h2
    have hL := hI.e4 d h1 h2
    have hown := hI.own_dsc p d hd
    have hpc : (c.loc p).pc = .ret := by
      cases a with
      | invoke q δ => simp only [step] at h; split_ifs at h <;> cases h
      | sched q =>
        simp only [step] at h
        split at h <;> (try split at h) <;> (try split at h) <;> simp_all
    have := hI.o2 d (hI.f1 d hL).2 (by rw [hown]; exact hd) (by rw [hown, hpc]; simp)
    rw [this] at h2; cases h2

end Podc.RandomizedWaitFreeLocks.Alg1
