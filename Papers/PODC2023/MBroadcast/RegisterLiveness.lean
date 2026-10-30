import Papers.PODC2023.MBroadcast.RegisterSafety

/-!
# Theorem 2, liveness: the operations of Algorithm 3 terminate

Infinite executions of Algorithm 3 (`Exec`: a step or a stuttering step at each time). We
assume

* weak fairness for the local steps of correct processes (`Exec.Fair`): a local continuation
  (end of a `wait`, i.e. `line2`, `line5`, `retW`, `retR`) that stays enabled is eventually
  taken (observed as a change of the control position); and
* the liveness of the MBroadcast layer (`Exec.CSTermination`, Global CS-termination): a message
  mbroadcast by a correct process is eventually mdelivered by every correct process.

Then every operation of a correct process terminates (`alg3_terminates`), for any number of
crashes. Only the "own delivery" part of CS-termination is used: a correct process eventually
mdelivers its own messages.
-/

set_option linter.unusedSectionVars false

namespace Podc.MBroadcast.Alg3

open Cslib.SharedMemory

variable {P V : Type} [LinearOrder P] [DecidableEq V] {v₀ : V}

/-- An infinite execution of Algorithm 3. -/
structure Exec (v₀ : V) where
  cfg : ℕ → Cfg P V
  lbl : ℕ → Option (Label P (register V v₀))
  init : cfg 0 = initCfg v₀
  step : ∀ t, Step v₀ (cfg t) (lbl t) (cfg (t + 1)) ∨ (cfg (t + 1) = cfg t ∧ lbl t = none)

/-- A local continuation of `p` is enabled: its current `wait` condition holds. -/
def LocalEnabled (C : Cfg P V) (p : P) : Prop :=
  ((∃ v, (C.loc p).phase = .wSync v) ∨ (C.loc p).phase = .rSync) ∧
      .dl p p (.synch (C.loc p).k) ∈ C.log ∨
    ∃ v c, ((C.loc p).phase = .wFin v c ∨ (C.loc p).phase = .rFin v c) ∧
      .dl p p (.write (C.loc p).k v c) ∈ C.log

namespace Exec

variable (e : Exec (P := P) v₀)

/-- `p` never crashes. -/
def Correct (p : P) : Prop := ∀ t, p ∉ (e.cfg t).crashed

/-- Weak fairness of local steps: a local continuation of a correct process that is enabled at
all times from `T` on is taken at some time `≥ T` (the control position changes). -/
def Fair : Prop :=
  ∀ p, e.Correct p → ∀ T, (∀ t ≥ T, LocalEnabled (e.cfg t) p) →
    ∃ t ≥ T, ((e.cfg (t + 1)).loc p).phase ≠ ((e.cfg t).loc p).phase

/-- Global CS-termination of the MBroadcast layer. -/
def CSTermination : Prop :=
  ∀ p q m t, e.Correct p → e.Correct q → Ev.bc p m ∈ (e.cfg t).log →
    ∃ t', Ev.dl q p m ∈ (e.cfg t').log

end Exec

/-! ## Step facts -/

/-- The message a waiting process waits for has been mbroadcast. -/
def WaitOK (C : Cfg P V) (p : P) : Prop :=
  match (C.loc p).phase with
  | .idle => True
  | .wSync _ => .bc p (.synch (C.loc p).k) ∈ C.log
  | .rSync => .bc p (.synch (C.loc p).k) ∈ C.log
  | .wFin v c => .bc p (.write (C.loc p).k v c) ∈ C.log
  | .rFin v c => .bc p (.write (C.loc p).k v c) ∈ C.log

lemma WaitOK.mono_log {C : Cfg P V} {p : P} (h : WaitOK C p) (es) :
    WaitOK ⟨C.loc, C.log ++ es, C.crashed⟩ p := by
  unfold WaitOK at *
  split <;> simp_all

lemma Step.waitOK {C C' : Cfg P V} {ℓ} (hs : Step v₀ C ℓ C') (h : ∀ p, WaitOK C p) (p : P) :
    WaitOK C' p := by
  cases hs with
  | invW q v hp hi =>
    rcases eq_or_ne p q with rfl | hq
    · simp [WaitOK, Cfg.upd]
    · have := (h p).mono_log [.bc q (.synch (C.loc q).k)]
      simpa [Cfg.upd, WaitOK, hq] using this
  | invR q hp hi =>
    rcases eq_or_ne p q with rfl | hq
    · simp [WaitOK, Cfg.upd]
    · have := (h p).mono_log [.bc q (.synch (C.loc q).k)]
      simpa [Cfg.upd, WaitOK, hq] using this
  | dlv q r m hp =>
    have := (h p).mono_log [.dl q r m]
    rcases eq_or_ne p q with rfl | hq
    · simpa [Cfg.upd, WaitOK] using this
    · simpa [Cfg.upd, WaitOK, hq] using this
  | line2 q v d hp hph hs hd =>
    rcases eq_or_ne p q with rfl | hq
    · simp [WaitOK, Cfg.upd]
    · have := (h p).mono_log [.bc q (.write (C.loc q).k v (ts d q))]
      simpa [Cfg.upd, WaitOK, hq] using this
  | line5 q hp hph hs =>
    rcases eq_or_ne p q with rfl | hq
    · simp [WaitOK, Cfg.upd]
    · have := (h p).mono_log [.bc q (.write (C.loc q).k (C.loc q).val (C.loc q).clock)]
      simpa [Cfg.upd, WaitOK, hq] using this
  | retW q v c hp hph hs =>
    rcases eq_or_ne p q with rfl | hq
    · simp [WaitOK, Cfg.upd]
    · simpa [Cfg.upd, WaitOK, hq] using h p
  | retR q v c hp hph hs =>
    rcases eq_or_ne p q with rfl | hq
    · simp [WaitOK, Cfg.upd]
    · simpa [Cfg.upd, WaitOK, hq] using h p
  | crash q => simpa [WaitOK] using h p

/-- How the control position and the operation counter of `p` can change in one step. -/
lemma Step.loc_change {C C' : Cfg P V} {ℓ} (hs : Step v₀ C ℓ C') (p : P)
    (hne : ((C'.loc p).phase, (C'.loc p).k) ≠ ((C.loc p).phase, (C.loc p).k)) :
    (C.loc p).phase = .idle ∨
    ((∃ v, (C.loc p).phase = .wSync v) ∨ (C.loc p).phase = .rSync) ∧
      (C'.loc p).phase.isFin = true ∧ (C'.loc p).k = (C.loc p).k ∨
    (C.loc p).phase.isFin = true ∧ (C'.loc p).phase = .idle ∧ (C'.loc p).k = (C.loc p).k + 1 := by
  cases hs with
  | invW q v hp hi =>
    rcases eq_or_ne p q with rfl | hq
    · exact Or.inl hi
    · simp [Cfg.upd, hq] at hne
  | invR q hp hi =>
    rcases eq_or_ne p q with rfl | hq
    · exact Or.inl hi
    · simp [Cfg.upd, hq] at hne
  | dlv q r m hp =>
    rcases eq_or_ne p q with rfl | hq
    · simp [Cfg.upd] at hne
    · simp [Cfg.upd, hq] at hne
  | line2 q v d hp hph hs hd =>
    rcases eq_or_ne p q with rfl | hq
    · right; left; exact ⟨Or.inl ⟨v, hph⟩, by simp [Phase.isFin], by simp⟩
    · simp [Cfg.upd, hq] at hne
  | line5 q hp hph hs =>
    rcases eq_or_ne p q with rfl | hq
    · right; left; exact ⟨Or.inr hph, by simp [Phase.isFin], by simp⟩
    · simp [Cfg.upd, hq] at hne
  | retW q v c hp hph hs =>
    rcases eq_or_ne p q with rfl | hq
    · right; right; exact ⟨by rw [hph]; rfl, by simp, by simp⟩
    · simp [Cfg.upd, hq] at hne
  | retR q v c hp hph hs =>
    rcases eq_or_ne p q with rfl | hq
    · right; right; exact ⟨by rw [hph]; rfl, by simp, by simp⟩
    · simp [Cfg.upd, hq] at hne
  | crash q => simp at hne

lemma Step.log_prefix {C C' : Cfg P V} {ℓ} (hs : Step v₀ C ℓ C') : C.log <+: C'.log := by
  obtain ⟨es, hes⟩ := hs.log_eq; rw [hes]; exact List.prefix_append _ _

namespace Exec

variable (e : Exec (P := P) v₀)

lemma log_prefix {a b : ℕ} (hab : a ≤ b) : (e.cfg a).log <+: (e.cfg b).log := by
  induction b, hab using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ b _ ih =>
    refine ih.trans ?_
    rcases e.step b with hs | ⟨hs, -⟩
    · exact hs.log_prefix
    · rw [hs]

lemma waitOK (t : ℕ) (p : P) : WaitOK (e.cfg t) p := by
  induction t generalizing p with
  | zero => rw [e.init]; simp [WaitOK, initCfg]
  | succ t ih =>
    rcases e.step t with hs | ⟨hs, -⟩
    · exact hs.waitOK ih p
    · rw [hs]; exact ih p

/-- The local view `(phase, k)` of `p` at time `t`. -/
def view (p : P) (t : ℕ) : Phase P V × ℕ := (((e.cfg t).loc p).phase, ((e.cfg t).loc p).k)

lemma view_change (p : P) (t : ℕ) (hne : e.view p (t + 1) ≠ e.view p t) :
    ((e.cfg t).loc p).phase = .idle ∨
    ((∃ v, ((e.cfg t).loc p).phase = .wSync v) ∨ ((e.cfg t).loc p).phase = .rSync) ∧
      ((e.cfg (t + 1)).loc p).phase.isFin = true ∧
      ((e.cfg (t + 1)).loc p).k = ((e.cfg t).loc p).k ∨
    ((e.cfg t).loc p).phase.isFin = true ∧ ((e.cfg (t + 1)).loc p).phase = .idle ∧
      ((e.cfg (t + 1)).loc p).k = ((e.cfg t).loc p).k + 1 := by
  rcases e.step t with hs | ⟨hs, -⟩
  · exact hs.loc_change p hne
  · exact absurd (by simp [view, hs]) hne

/-- If the view of `p` at `T` is eventually left, there is a first step that leaves it. -/
lemma exists_first_change (p : P) (T : ℕ) (h : ∃ t ≥ T, e.view p t ≠ e.view p T) :
    ∃ t ≥ T, e.view p t = e.view p T ∧ e.view p (t + 1) ≠ e.view p T := by
  classical
  have hex : ∃ n, e.view p (T + n) ≠ e.view p T := by
    obtain ⟨t, ht, hne⟩ := h; exact ⟨t - T, by rwa [Nat.add_sub_cancel' ht]⟩
  set n := Nat.find hex with hn
  have hspec : e.view p (T + n) ≠ e.view p T := Nat.find_spec hex
  have hpos : n ≠ 0 := by intro h0; rw [h0] at hspec; exact hspec rfl
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmin : e.view p (T + m) = e.view p T := by
    by_contra hc; exact Nat.find_min hex (show m < n by omega) hc
  exact ⟨T + m, by omega, hmin, by rw [show T + m + 1 = T + n by omega]; exact hspec⟩

/-- A waiting correct process eventually leaves its current view. -/
lemma leaves_wait (hf : e.Fair) (hcs : e.CSTermination) {p : P} (hp : e.Correct p) (T : ℕ)
    (hw : ((e.cfg T).loc p).phase ≠ .idle) : ∃ t ≥ T, e.view p t ≠ e.view p T := by
  by_contra hcon
  push Not at hcon
  -- the awaited message
  obtain ⟨m, hbc, hen⟩ : ∃ m, Ev.bc p m ∈ (e.cfg T).log ∧
      ∀ t, Ev.dl p p m ∈ (e.cfg t).log → e.view p t = e.view p T → LocalEnabled (e.cfg t) p := by
    have hwo := e.waitOK T p
    unfold WaitOK at hwo
    split at hwo
    · exact absurd ‹_› hw
    · rename_i v hph
      refine ⟨_, hwo, fun t hd hv => ?_⟩
      simp only [view, Prod.mk.injEq] at hv
      left; exact ⟨Or.inl ⟨v, hv.1.trans hph⟩, by rw [hv.2]; exact hd⟩
    · rename_i hph
      refine ⟨_, hwo, fun t hd hv => ?_⟩
      simp only [view, Prod.mk.injEq] at hv
      left; exact ⟨Or.inr (hv.1.trans hph), by rw [hv.2]; exact hd⟩
    · rename_i v c hph
      refine ⟨_, hwo, fun t hd hv => ?_⟩
      simp only [view, Prod.mk.injEq] at hv
      right; exact ⟨v, c, Or.inl (hv.1.trans hph), by rw [hv.2]; exact hd⟩
    · rename_i v c hph
      refine ⟨_, hwo, fun t hd hv => ?_⟩
      simp only [view, Prod.mk.injEq] at hv
      right; exact ⟨v, c, Or.inr (hv.1.trans hph), by rw [hv.2]; exact hd⟩
  obtain ⟨t₁, ht₁⟩ := hcs p p m T hp hp hbc
  obtain ⟨t, ht, hch⟩ := hf p hp (max T t₁) (fun t ht => hen t
    ((e.log_prefix (le_of_max_le_right ht)).subset ht₁) (hcon t (le_of_max_le_left ht)))
  have h1 := hcon t (le_of_max_le_left ht)
  have h2 := hcon (t + 1) (by have := le_of_max_le_left ht; omega)
  simp only [view, Prod.mk.injEq] at h1 h2
  exact hch (h2.1.trans h1.1.symm)

end Exec

/-- **Theorem 2 (liveness).** In a fair execution of Algorithm 3 on top of an MBroadcast layer
satisfying Global CS-termination, every operation of a correct process terminates: if `p` is in
the middle of its `k`-th operation at time `T`, then at some later time it has completed it
(its counter of completed operations is `k + 1`; `Inv.resps` identifies it with the number of
responses in the history). No assumption on the number of crashes. -/
theorem alg3_terminates (e : Exec (P := P) v₀) (hf : e.Fair) (hcs : e.CSTermination) {p : P}
    (hp : e.Correct p) (T : ℕ) (hw : ((e.cfg T).loc p).phase ≠ .idle) :
    ∃ t ≥ T, ((e.cfg t).loc p).k = ((e.cfg T).loc p).k + 1 := by
  -- leaving a final wait completes the operation
  have fin_step : ∀ T₁, ((e.cfg T₁).loc p).phase.isFin = true →
      ∃ t ≥ T₁, ((e.cfg t).loc p).k = ((e.cfg T₁).loc p).k + 1 := by
    intro T₁ hfin
    have hw₁ : ((e.cfg T₁).loc p).phase ≠ .idle := by intro h0; rw [h0] at hfin; cases hfin
    obtain ⟨t, ht, hv, hv'⟩ := e.exists_first_change p T₁ (e.leaves_wait hf hcs hp T₁ hw₁)
    have hv1 := hv; simp only [Exec.view, Prod.mk.injEq] at hv1
    rcases e.view_change p t (by rw [hv]; exact hv') with h | ⟨⟨v, h⟩ | h, -, -⟩ | ⟨-, -, hk⟩
    · rw [hv1.1] at h; exact absurd h hw₁
    · rw [hv1.1] at h; rw [h] at hfin; cases hfin
    · rw [hv1.1] at h; rw [h] at hfin; cases hfin
    · exact ⟨t + 1, by omega, by rw [hk, hv1.2]⟩
  by_cases hfin : ((e.cfg T).loc p).phase.isFin = true
  · exact fin_step T hfin
  · obtain ⟨t, ht, hv, hv'⟩ := e.exists_first_change p T (e.leaves_wait hf hcs hp T hw)
    have hv1 := hv; simp only [Exec.view, Prod.mk.injEq] at hv1
    rcases e.view_change p t (by rw [hv]; exact hv') with h | ⟨-, hf', hk⟩ | ⟨h, -, -⟩
    · rw [hv1.1] at h; exact absurd h hw
    · obtain ⟨t', ht', hk'⟩ := fin_step (t + 1) hf'
      exact ⟨t', by omega, by rw [hk', hk, hv1.2]⟩
    · rw [hv1.1] at h; exact absurd h hfin

end Podc.MBroadcast.Alg3
