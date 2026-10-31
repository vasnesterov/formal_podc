import Papers.PODC2012.TMLiveness.Strategy
import Cslib.Foundations.Data.Nat.Descent

/-!
# Runs of the strategy: step-by-step bookkeeping

Tools to reason about the infinite run `stratRun M S sched` of the environment's strategy: the
transaction information `RI t` after `t` steps, how one step changes it, and which events can
change the state of a process. This file is independent of the scheduler.
-/

namespace Podc.TMLiveness

variable {P X V : Type*} [DecidableEq P] [DecidableEq X] [DecidableEq V]
variable {M : TM P X V} {S : Setup P X V} {sched : List (Step P X V) → P}

/-- The transaction information after `t` steps of the run. -/
noncomputable def RI (M : TM P X V) (S : Setup P X V) (sched : List (Step P X V) → P) (t : ℕ) :
    HInfo P X V :=
  info (hist (stratPre M S sched t))

/-- The effect of a step on the transaction information. -/
def HInfo.apply (I : HInfo P X V) : Step P X V → HInfo P X V
  | .ev e => I.step e
  | .tau _ => I

theorem RI_succ (t : ℕ) :
    RI M S sched (t + 1) = (RI M S sched t).apply (stratRun M S sched t) := by
  simp only [RI, stratPre]
  rw [show stratStep M S sched (stratPre M S sched t) = stratRun M S sched t from rfl]
  cases stratRun M S sched t <;> simp [HInfo.apply, RI]

theorem RI_zero : RI M S sched 0 = HInfo.init := rfl

theorem run_cases (t : ℕ) :
    (∃ k i, (RI M S sched t).pend k = none ∧ i = S.script (RI M S sched t) k ∧
      stratRun M S sched t = .ev (.inv k i)) ∨
    (∃ k i r, (RI M S sched t).pend k = some i ∧ r.Fits i ∧
      stratRun M S sched t = .ev (.res k i r)) ∨
    (∃ k, (RI M S sched t).pend k ≠ none ∧ stratRun M S sched t = .tau k) := by
  rcases stratStep_cases (M := M) (S := S) (sched := sched) (stratPre M S sched t) with
    ⟨hp, he⟩ | ⟨i, r, hp, hr, he⟩ | ⟨i, hp, -, he⟩
  · exact Or.inl ⟨_, _, hp, rfl, he⟩
  · exact Or.inr (Or.inl ⟨_, i, r, hp, M.next_fits _ _ _ _ hp hr, he⟩)
  · exact Or.inr (Or.inr ⟨_, by simp [RI, pending] at hp ⊢; simp [hp], he⟩)

theorem run_proc (t : ℕ) : (stratRun M S sched t).proc = sched (stratPre M S sched t) := by
  unfold stratRun
  rcases stratStep_cases (M := M) (S := S) (sched := sched) (stratPre M S sched t) with
    ⟨_, he⟩ | ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he] <;> rfl

theorem run_inv {t : ℕ} {k : P} {i : Inv X V} (h : stratRun M S sched t = .ev (.inv k i)) :
    (RI M S sched t).pend k = none ∧ i = S.script (RI M S sched t) k := by
  rcases run_cases (M := M) (S := S) (sched := sched) t with ⟨k', i', h1, h2, he⟩ |
    ⟨k', i', r, -, -, he⟩ | ⟨k', -, he⟩ <;> rw [he] at h <;> simp at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨h1, h2⟩

theorem run_res {t : ℕ} {k : P} {i : Inv X V} {r : Res V}
    (h : stratRun M S sched t = .ev (.res k i r)) :
    (RI M S sched t).pend k = some i ∧ r.Fits i := by
  rcases run_cases (M := M) (S := S) (sched := sched) t with ⟨k', i', -, -, he⟩ |
    ⟨k', i', r', h1, h2, he⟩ | ⟨k', -, he⟩ <;> rw [he] at h <;> simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨h1, h2⟩

theorem run_tau {t : ℕ} {k : P} (h : stratRun M S sched t = .tau k) :
    (RI M S sched t).pend k ≠ none := by
  rcases run_cases (M := M) (S := S) (sched := sched) t with ⟨k', i', -, -, he⟩ |
    ⟨k', i', r', -, -, he⟩ | ⟨k', h1, he⟩ <;> rw [he] at h <;> simp at h
  subst h; exact h1

theorem stratEv_run {t : ℕ} {e : Ev P X V} (h : stratRun M S sched t = .ev e) :
    S.StratEv (RI M S sched t) e := by
  cases e with
  | inv k i => exact run_inv h
  | res k i r => exact run_res h

theorem run_commit_tryC {t : ℕ} {k : P} {i : Inv X V}
    (h : stratRun M S sched t = .ev (.res k i .commit)) : i = .tryC := by
  have := (run_res h).2; cases i <;> simp_all [Res.Fits]

theorem good_RI {init : X → V} (hM : EnsuresSafety M (Serializable init)) (t : ℕ) :
    WF (RI M S sched t) ∧ S.Good (RI M S sched t) :=
  good_stratPre hM t

/-! ### Locality -/

/-- The step at time `t` is an event of process `k`. -/
def IsEvOf (s : Step P X V) (k : P) : Prop := ∃ e, s = .ev e ∧ e.proc = k

theorem RI_succ_local {t : ℕ} {k : P} (h : ¬ IsEvOf (stratRun M S sched t) k) :
    (RI M S sched (t + 1)).pend k = (RI M S sched t).pend k ∧
    (RI M S sched (t + 1)).cnt k = (RI M S sched t).cnt k ∧
    (∀ j, (RI M S sched (t + 1)).ops (k, j) = (RI M S sched t).ops (k, j)) ∧
    (∀ j, (RI M S sched (t + 1)).committed (k, j) = (RI M S sched t).committed (k, j)) ∧
    (∀ j, (RI M S sched (t + 1)).began (k, j) = (RI M S sched t).began (k, j)) := by
  rw [RI_succ]
  cases hs : stratRun M S sched t with
  | tau k' => simp [HInfo.apply]
  | ev e =>
    have hne : e.proc ≠ k := fun he => h ⟨e, hs, he⟩
    cases e with
    | inv k' i =>
      simp only [Ev.proc] at hne
      simp [HInfo.apply, Function.update_of_ne (Ne.symm hne), Ne.symm hne]
    | res k' i r =>
      simp only [Ev.proc] at hne
      refine ⟨by simp [HInfo.apply, Function.update_of_ne (Ne.symm hne)],
        Setup.step_res_cnt_ne (Ne.symm hne), fun j => ?_, fun j => ?_, fun j => by simp [HInfo.apply]⟩
      · simp [HInfo.apply, Ne.symm hne]
      · simp [HInfo.apply, Ne.symm hne]

theorem ops_succ (t : ℕ) (q : TxId P) :
    ∃ l, (RI M S sched (t + 1)).ops q = (RI M S sched t).ops q ++ l := by
  rw [RI_succ]
  cases stratRun M S sched t with
  | tau k => exact ⟨[], by simp [HInfo.apply]⟩
  | ev e =>
    cases e with
    | inv k i => exact ⟨[], by simp [HInfo.apply]⟩
    | res k i r =>
      simp only [HInfo.apply, step_res_ops]
      split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨[], by simp⟩

theorem ops_mono {t t' : ℕ} (h : t ≤ t') (q : TxId P) :
    ∃ l, (RI M S sched t').ops q = (RI M S sched t).ops q ++ l := by
  induction t', h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ t' _ ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨l', hl'⟩ := ops_succ (M := M) (S := S) (sched := sched) t' q
    exact ⟨l ++ l', by rw [hl', hl, List.append_assoc]⟩

theorem cnt_succ_ne {t : ℕ} {k : P}
    (h : (RI M S sched (t + 1)).cnt k ≠ (RI M S sched t).cnt k) :
    ∃ i r, stratRun M S sched t = .ev (.res k i r) ∧ r.isEnd = true := by
  by_cases hk : IsEvOf (stratRun M S sched t) k
  · obtain ⟨e, he, hp⟩ := hk
    rw [RI_succ, he] at h
    cases e with
    | inv k' i => simp [HInfo.apply] at h
    | res k' i r =>
      simp only [Ev.proc] at hp
      subst hp
      refine ⟨i, r, he, ?_⟩
      by_contra hr
      simp [HInfo.apply, Setup.step_res_cnt_self, hr] at h
  · exact absurd (RI_succ_local hk).2.1 h

theorem began_succ {t : ℕ} {q : TxId P} (h : (RI M S sched t).began q = true) :
    (RI M S sched (t + 1)).began q = true := by
  rw [RI_succ]
  cases stratRun M S sched t with
  | tau k => simpa [HInfo.apply] using h
  | ev e => cases e <;> simp [HInfo.apply, h]

theorem run_inv_of_pend {t : ℕ} {k : P} {i : Inv X V} (h1 : (RI M S sched t).pend k ≠ some i)
    (h2 : (RI M S sched (t + 1)).pend k = some i) : stratRun M S sched t = .ev (.inv k i) := by
  by_cases hk : IsEvOf (stratRun M S sched t) k
  · obtain ⟨e, he, hp⟩ := hk
    rw [RI_succ, he] at h2
    cases e with
    | inv k' i' =>
      simp only [Ev.proc] at hp; subst hp
      simp [HInfo.apply] at h2; rw [he, h2]
    | res k' i' r =>
      simp only [Ev.proc] at hp; subst hp
      simp [HInfo.apply] at h2
  · exact absurd ((RI_succ_local hk).1 ▸ h2) h1

theorem run_res_of_pend {t : ℕ} {k : P} {i : Inv X V} (h1 : (RI M S sched t).pend k = some i)
    (h2 : (RI M S sched (t + 1)).pend k ≠ some i) :
    ∃ r, stratRun M S sched t = .ev (.res k i r) := by
  by_cases hk : IsEvOf (stratRun M S sched t) k
  · obtain ⟨e, he, hp⟩ := hk
    cases e with
    | inv k' i' =>
      simp only [Ev.proc] at hp; subst hp
      have := (run_inv he).1; rw [h1] at this; simp at this
    | res k' i' r =>
      simp only [Ev.proc] at hp; subst hp
      have := (run_res he).1; rw [h1] at this
      simp only [Option.some.injEq] at this; subst this
      exact ⟨r, he⟩
  · exact absurd ((RI_succ_local hk).1 ▸ h1) h2

/-- An invocation is answered before the process is idle again. -/
theorem exists_res_between {t₁ t₂ : ℕ} {k : P} {i : Inv X V}
    (h1 : stratRun M S sched t₁ = .ev (.inv k i)) (h12 : t₁ < t₂)
    (h2 : (RI M S sched t₂).pend k = none) :
    ∃ s, t₁ < s ∧ s < t₂ ∧ ∃ r, stratRun M S sched s = .ev (.res k i r) := by
  have hp : (RI M S sched (t₁ + 1)).pend k = some i := by
    rw [RI_succ, h1]; simp [HInfo.apply]
  obtain ⟨m, hm1, hm2, hpm, hlast⟩ :=
    Nat.exists_last_of_le (p := fun m => (RI M S sched m).pend k = some i) h12 hp
  have hmt : m < t₂ := by
    rcases hm2.lt_or_eq with h | h
    · exact h
    · subst h; rw [h2] at hpm; simp at hpm
  obtain ⟨r, hr⟩ := run_res_of_pend hpm (hlast (m + 1) (by omega) hmt)
  exact ⟨m, by omega, hmt, r, hr⟩

/-! ### Sets of times -/

theorem infinite_iff {p : ℕ → Prop} : {t | p t}.Infinite ↔ ∀ T, ∃ t ≥ T, p t := by
  constructor
  · intro h T
    obtain ⟨t, ht, hlt⟩ := h.exists_gt T
    exact ⟨t, hlt.le, ht⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨t, ht, hp⟩ := h (a + 1)
    exact ⟨t, hp, by omega⟩

theorem finite_iff {p : ℕ → Prop} : {t | p t}.Finite ↔ ∃ T, ∀ t ≥ T, ¬ p t := by
  constructor
  · intro h
    obtain ⟨T, hT⟩ := h.bddAbove
    exact ⟨T + 1, fun t ht hp => by have := hT hp; omega⟩
  · rintro ⟨T, hT⟩
    refine (Set.finite_lt_nat T).subset (fun t hp => ?_)
    by_contra h
    exact hT t (by simpa using h) hp

end Podc.TMLiveness
