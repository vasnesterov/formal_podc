import Papers.PODC2019.AnonymousMutex.Alg2Inv

/-!
# Algorithm 2, deadlock-freedom: basic facts about infinite executions

Throughout, `e` is an infinite client-well-formed execution of Algorithm 2 and `t₀` a time after
which no operation completes (the hypothesis to be refuted by Theorem 4). We collect:
* the invariant at every time (`inv_at`);
* frame properties: other processes change neither the local state nor the own registers of `p`;
* after `t₀` nobody is in the critical section, nobody executes `unlock()` and nobody is about to
  return from `lock()`; every process is in the remainder section or in `lock()` at one of the
  program counters `cas`, `read`, `wr`, `wait` (`phase_after`);
* a process with a pending operation takes infinitely many internal steps (`exists_tau`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P]
  {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

/-- The program counters of `lock()` other than `retLock`. -/
def Busy : PC → Prop
  | .cas _ | .read _ | .wr _ | .wait _ _ => True
  | _ => False

section Exec

variable (hid : Function.Injective ids) (hm : 0 < m) (e : ((alg2 Id m).impl ids π).InfExec)
  (hwf : ∀ t, ClientWF (e.pre t))

include hid hm hwf in
lemma inv_at (t : ℕ) : Inv ids π (e.pre t) (e.cfg t) :=
  inv_of_run ids π hid hm (hwf t) (e.run_pre t)

lemma loc_other {t : ℕ} {p : P} (h : (e.lbl t).proc ≠ p) :
    (e.cfg (t + 1)).loc p = (e.cfg t).loc p ∧ (e.cfg (t + 1)).pend p = (e.cfg t).pend p :=
  Impl.step_other (e.step_eq t) h

include hid hm hwf in
/-- Only internal steps of `p` change the registers holding `p`'s identifier. -/
lemma own_frame {t : ℕ} {p : P} (h : e.lbl t ≠ .tau p) (y : Fin m) :
    (e.cfg (t + 1)).mem () y = some (ids p) ↔ (e.cfg t).mem () y = some (ids p) := by
  have hstep := e.step_eq t
  cases hl : e.lbl t with
  | inv q o =>
    rw [hl] at hstep
    obtain ⟨-, h'⟩ := SymAlg.impl_step_inv_cases hstep
    rw [h']
  | ret q r =>
    rw [hl] at hstep
    obtain ⟨-, s, -, h'⟩ := SymAlg.impl_step_ret_cases hstep
    rw [h']
  | tau q =>
    rw [hl] at hstep
    have hqp : q ≠ p := fun hq => h (by rw [hl, hq])
    obtain ⟨-, hcase⟩ := SymAlg.impl_step_tau_cases hstep
    rcases hcase with ⟨x, f, k, hact, h'⟩ | ⟨k, hact, -⟩
    · obtain ⟨hframe, -⟩ := tau_facts ids π hid hm ((inv_at hid hm e hwf t).1 q) hact
      rw [h']
      simp only [Function.update_self, Function.update_apply]
      split_ifs with hy
      · subst hy; exact hframe p (Ne.symm hqp)
      · rfl
    · exact absurd hact (act_ne_snap _ _)

include hid hm hwf in
lemma own_frame' {t : ℕ} {p : P} (h : e.lbl t ≠ .tau p) :
    own ids (e.cfg (t + 1)) p = own ids (e.cfg t) p :=
  own_congr ids (own_frame hid hm e hwf h)

/-- Effect of an internal step of `p`. -/
lemma tau_step {t : ℕ} {p : P} (h : e.lbl t = .tau p) :
    (e.cfg t).pend p ≠ none ∧ ∃ x f k, (alg2 Id m).act ((e.cfg t).loc p) = .rmw x f k ∧
      (e.cfg (t + 1)).loc p = k ((e.cfg t).mem () (π p x)) ∧
      (e.cfg (t + 1)).mem () = Function.update ((e.cfg t).mem ()) (π p x)
        (f ((e.cfg t).mem () (π p x))) ∧
      (e.cfg (t + 1)).pend = (e.cfg t).pend ∧
      ∀ q, q ≠ p → (e.cfg (t + 1)).loc q = (e.cfg t).loc q := by
  have hstep := e.step_eq t
  rw [h] at hstep
  obtain ⟨hp, hcase⟩ := SymAlg.impl_step_tau_cases hstep
  rcases hcase with ⟨x, f, k, hact, h'⟩ | ⟨k, hact, -⟩
  · refine ⟨hp, x, f, k, hact, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h']; simp
    · rw [h']; simp
    · rw [h']
    · rw [h']; simp [Function.update_of_ne hq]
  · exact absurd hact (act_ne_snap _ _)

section AfterT0

variable (t₀ : ℕ) (hnoret : ∀ t ≥ t₀, ∀ p r, e.lbl t ≠ .ret p r)

include hnoret in
/-- After `t₀` a pending operation stays pending. -/
lemma pend_persist {t : ℕ} (ht : t₀ ≤ t) {p : P} (hp : (e.cfg t).pend p ≠ none) :
    ∀ t' ≥ t, (e.cfg t').pend p = (e.cfg t).pend p := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => rfl
  | succ t' ht' ih =>
    rw [← ih]
    have hstep := e.step_eq t'
    cases hl : e.lbl t' with
    | inv q o =>
      by_cases hq : q = p
      · subst hq
        rw [hl] at hstep
        have := (SymAlg.impl_step_inv_cases hstep).1
        rw [ih] at this; exact absurd this hp
      · exact (loc_other e (by rw [hl]; exact hq)).2
    | ret q r => exact absurd hl (hnoret t' (by omega) q r)
    | tau q =>
      rw [hl] at hstep
      exact (Impl.step_tau hstep).2.1 ▸ rfl

include hnoret in
/-- A process with a pending operation after `t₀` keeps taking internal steps. -/
lemma exists_tau (hfair : e.Fair) {t : ℕ} (ht : t₀ ≤ t) {p : P} (hp : (e.cfg t).pend p ≠ none)
    (t₁ : ℕ) (ht₁ : t ≤ t₁) : ∃ t₂ ≥ t₁, e.lbl t₂ = .tau p := by
  have hp1 : (e.cfg t₁).pend p ≠ none := by
    rw [pend_persist e t₀ hnoret ht hp t₁ ht₁]; exact hp
  obtain ⟨t₂, ht₂, hproc, hst⟩ := hfair p t₁ hp1
  refine ⟨t₂, ht₂, ?_⟩
  cases hl : e.lbl t₂ with
  | inv q o => rw [hl] at hst; exact absurd hst id
  | ret q r => exact absurd hl (hnoret t₂ (by omega) q r)
  | tau q => rw [hl] at hproc; simp only [Label.proc] at hproc; rw [hproc]

omit hnoret in
lemma region_succ (t : ℕ) (p : P) : regionOf (e.pre (t + 1)) p =
    if (e.lbl t).proc = p then (regionOf (e.pre t) p).bind (fun r => r.next (e.lbl t))
    else regionOf (e.pre t) p := by
  rw [Impl.InfExec.pre_succ, regionOf_append_singleton]

include hnoret hwf in
/-- After `t₀`, a process in `lock()` (resp. `unlock()`) stays there. -/
lemma region_persist {t : ℕ} (ht : t₀ ≤ t) {p : P} {r : Region}
    (hr : regionOf (e.pre t) p = some r) (hr' : r = .trying ∨ r = .exiting) :
    ∀ t' ≥ t, regionOf (e.pre t') p = some r := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => exact hr
  | succ t' ht' ih =>
    have hw := hwf (t' + 1) p
    rw [region_succ] at hw ⊢
    split_ifs at hw ⊢ with hq
    · rw [ih] at hw ⊢
      cases hl : e.lbl t' with
      | ret q r0 => exact absurd hl (hnoret t' (by omega) q r0)
      | tau q => rcases hr' with rfl | rfl <;> rfl
      | inv q o => rw [hl] at hw; rcases hr' with rfl | rfl <;> cases o <;> simp [Region.next] at hw
    · exact ih

include hnoret hwf in
lemma not_cs_after (hnocs : ∀ q, ¬ InCS (e.pre t₀) q) :
    ∀ t ≥ t₀, ∀ p, regionOf (e.pre t) p ≠ some .cs := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hnocs
  | succ t ht ih =>
    intro p
    have hw := hwf t p
    rw [region_succ]
    split_ifs with hq
    · cases hr : regionOf (e.pre t) p with
      | none => exact absurd hr hw
      | some r =>
        have := ih p
        rw [hr] at this
        cases hl : e.lbl t with
        | ret q r0 => exact absurd hl (hnoret t ht q r0)
        | tau q => simpa [Region.next] using this
        | inv q o => cases r <;> cases o <;> simp_all [Region.next]
    · exact ih p

omit hnoret in
/-- A label that is not a step of `p` leaves `p`'s local state unchanged, provided `p` has a
pending operation (so that `p` cannot invoke). -/
lemma loc_of_not_step {t : ℕ} {p : P} (hp : (e.cfg t).pend p ≠ none)
    (h : ¬ ((e.lbl t).proc = p ∧ (e.lbl t).IsStep)) :
    (e.cfg (t + 1)).loc p = (e.cfg t).loc p := by
  by_cases hq : (e.lbl t).proc = p
  · have hstep := e.step_eq t
    cases hl : e.lbl t with
    | inv q o =>
      rw [hl] at hstep hq
      simp only [Label.proc] at hq; subst hq
      exact absurd (SymAlg.impl_step_inv_cases hstep).1 hp
    | ret q r => rw [hl] at h hq; exact absurd ⟨hq, trivial⟩ h
    | tau q => rw [hl] at h hq; exact absurd ⟨hq, trivial⟩ h
  · exact (loc_other e hq).1

include hid hm hwf hnoret in
lemma no_exiting (hfair : e.Fair) : ∀ t ≥ t₀, ∀ p, regionOf (e.pre t) p ≠ some .exiting := by
  intro t ht p hex
  have hall := region_persist e hwf t₀ hnoret ht hex (Or.inr rfl)
  have hR : ∀ t' ≥ t, (e.cfg t').pend p = some .unlock ∧ UnlockPC ((e.cfg t').loc p).pc :=
    fun t' ht' => ((inv_at hid hm e hwf t').2.1 p).2.2.2 (hall t' ht')
  obtain ⟨t', -, hf⟩ := e.exists_good p (fun _ => False)
    (fun t' => match ((e.cfg t').loc p).pc with | .un i => m + 1 - i | _ => 0) t
    (fun t' ht' _ => hfair p t' (by rw [(hR t' ht').1]; simp))
    (fun t' ht' _ hproc hst => by
      right
      have hl : e.lbl t' = .tau p := by
        cases hl : e.lbl t' with
        | inv q o => rw [hl] at hst; exact absurd hst id
        | ret q r => exact absurd hl (hnoret t' (by omega) q r)
        | tau q => rw [hl] at hproc; simp only [Label.proc] at hproc; rw [hproc]
      obtain ⟨-, x, f, k, hact, hloc, -⟩ := tau_step e hl
      have hL := ((inv_at hid hm e hwf t').1 p).2
      have hU := (hR t' ht').2
      cases hpc : ((e.cfg t').loc p).pc with
      | un i =>
        rw [hpc] at hL
        rw [act_un hpc hL.1] at hact
        simp only [SymAction.rmw.injEq] at hact
        obtain ⟨rfl, rfl, rfl⟩ := hact
        rw [hloc]
        dsimp only
        split_ifs <;> simp only [] <;> omega
      | retUnlock => rw [act_retUnlock hpc] at hact; cases hact
      | _ => rw [hpc] at hU; exact absurd hU id)
    (fun t' ht' _ hn => by
      right
      rw [loc_of_not_step e (by rw [(hR t' ht').1]; simp) hn])
  exact hf

include hid hm hwf in
omit hnoret in
lemma pend_of_lockPC {t : ℕ} {p : P} (h : LockPC ((e.cfg t).loc p).pc) :
    (e.cfg t).pend p = some .lock := by
  obtain ⟨h1, h2, h3, h4⟩ := (inv_at hid hm e hwf t).2.1 p
  cases hr : regionOf (e.pre t) p with
  | none => exact absurd hr (hwf t p)
  | some r =>
    cases r with
    | rem => rw [(h1 hr).1] at h; exact absurd h id
    | trying => exact (h2 hr).1
    | cs => rw [(h3 hr).1] at h; exact absurd h id
    | exiting =>
      have := (h4 hr).2
      cases hpc : ((e.cfg t).loc p).pc <;> simp_all [LockPC, UnlockPC]

include hid hm hwf hnoret in
lemma no_retLock (hfair : e.Fair) : ∀ t ≥ t₀, ∀ p, ((e.cfg t).loc p).pc ≠ .retLock := by
  intro t ht p hpc
  have hpend : (e.cfg t).pend p ≠ none := by
    rw [pend_of_lockPC hid hm e hwf (by rw [hpc]; trivial)]; simp
  have frozen : ∀ t' ≥ t, (e.cfg t').loc p = (e.cfg t).loc p := by
    intro t' ht'
    induction t', ht' using Nat.le_induction with
    | base => rfl
    | succ t' ht' ih =>
      by_cases hs : (e.lbl t').proc = p ∧ (e.lbl t').IsStep
      · exfalso
        cases hl : e.lbl t' with
        | inv q o => rw [hl] at hs; exact hs.2
        | ret q r => exact hnoret t' (by omega) q r hl
        | tau q =>
          rw [hl] at hs; simp only [Label.proc] at hs; rw [hs.1] at hl
          obtain ⟨-, x, f, k, hact, -⟩ := tau_step e hl
          rw [ih, act_retLock hpc] at hact; cases hact
      · rw [loc_of_not_step e (by rw [pend_persist e t₀ hnoret ht hpend t' ht']; exact hpend) hs, ih]
  obtain ⟨t₂, ht₂, hl⟩ := exists_tau e t₀ hnoret hfair ht hpend t le_rfl
  obtain ⟨-, x, f, k, hact, -⟩ := tau_step e hl
  rw [frozen t₂ ht₂, act_retLock hpc] at hact; cases hact

include hid hm hwf hnoret in
/-- After `t₀` every process is in the remainder section (owning nothing) or in `lock()` at one
of the program counters `cas`, `read`, `wr`, `wait`. -/
lemma phase_after (hfair : e.Fair) (hnocs : ∀ q, ¬ InCS (e.pre t₀) q) {t : ℕ} (ht : t₀ ≤ t)
    (p : P) :
    (((e.cfg t).loc p).pc = .rem ∧ (e.cfg t).pend p = none) ∨
    ((e.cfg t).pend p = some .lock ∧ Busy ((e.cfg t).loc p).pc) := by
  obtain ⟨h1, h2, h3, h4⟩ := (inv_at hid hm e hwf t).2.1 p
  cases hr : regionOf (e.pre t) p with
  | none => exact absurd hr (hwf t p)
  | some r =>
    cases r with
    | rem => exact Or.inl (h1 hr)
    | trying =>
      obtain ⟨hp, hl⟩ := h2 hr
      refine Or.inr ⟨hp, ?_⟩
      have := no_retLock hid hm e hwf t₀ hnoret hfair t ht p
      cases hpc : ((e.cfg t).loc p).pc <;> simp_all [LockPC, Busy]
    | cs => exact absurd hr (not_cs_after e hwf t₀ hnoret hnocs t ht p)
    | exiting => exact absurd hr (no_exiting hid hm e hwf t₀ hnoret hfair t ht p)

end AfterT0

end Exec

/-- The hypotheses refuted in the proof of Theorem 4: a fair client-well-formed infinite
execution in which, after `t₀`, no operation completes, and nobody is in the critical section at
`t₀`. -/
structure Hyp (e : ((alg2 Id m).impl ids π).InfExec) (t₀ : ℕ) : Prop where
  wf : ∀ t, ClientWF (e.pre t)
  fair : e.Fair
  noret : ∀ t ≥ t₀, ∀ p r, e.lbl t ≠ .ret p r
  nocs : ∀ q, ¬ InCS (e.pre t₀) q

namespace Hyp

variable (hid : Function.Injective ids) (hm : 0 < m) {e : ((alg2 Id m).impl ids π).InfExec}
  {t₀ : ℕ} (H : Hyp e t₀)
include hid hm H

lemma inv (t : ℕ) : Inv ids π (e.pre t) (e.cfg t) := inv_at hid hm e H.wf t

lemma locInv (t : ℕ) (p : P) : LocInv ids π (e.cfg t) p := (H.inv hid hm t).1 p

lemma valInv (t : ℕ) : ValInv ids (e.cfg t) := (H.inv hid hm t).2.2

lemma phase {t : ℕ} (ht : t₀ ≤ t) (p : P) :
    (((e.cfg t).loc p).pc = .rem ∧ (e.cfg t).pend p = none) ∨
    ((e.cfg t).pend p = some .lock ∧ Busy ((e.cfg t).loc p).pc) :=
  phase_after hid hm e H.wf t₀ H.noret H.fair H.nocs ht p

omit hid hm in
lemma tau {t : ℕ} (ht : t₀ ≤ t) {p : P} (hp : (e.cfg t).pend p ≠ none) (t₁ : ℕ) (ht₁ : t ≤ t₁) :
    ∃ t₂ ≥ t₁, e.lbl t₂ = .tau p :=
  exists_tau e t₀ H.noret H.fair ht hp t₁ ht₁

lemma own_frame {t : ℕ} {p : P} (h : e.lbl t ≠ .tau p) :
    own ids (e.cfg (t + 1)) p = own ids (e.cfg t) p := own_frame' hid hm e H.wf h

/-- After `t₀`, a process with a busy program counter is pending. -/
lemma pend_of_busy {t : ℕ} (ht : t₀ ≤ t) {p : P} (h : Busy ((e.cfg t).loc p).pc) :
    (e.cfg t).pend p ≠ none := by
  rcases H.phase hid hm ht p with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1] at h; exact absurd h id
  · rw [h1]; simp

/-- After `t₀`, a process that takes an internal step has a busy program counter. -/
lemma busy_of_tau {t : ℕ} (ht : t₀ ≤ t) {p : P} (hl : e.lbl t = .tau p) :
    Busy ((e.cfg t).loc p).pc := by
  rcases H.phase hid hm ht p with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact absurd h1 (tau_step e hl).1
  · exact h1

omit hid hm in
/-- **Local progress.** If `p` is pending at `t ≥ t₀`, and every internal step of `p` either
establishes `G` or decreases `φ` (both functions of `p`'s local state), then `G` eventually holds. -/
lemma eventually_loc {t : ℕ} (ht : t₀ ≤ t) {p : P} (hpend : (e.cfg t).pend p ≠ none)
    (G : St Id m → Prop) (φ : St Id m → ℕ)
    (hp : ∀ t' ≥ t, ¬ G ((e.cfg t').loc p) → e.lbl t' = .tau p →
      G ((e.cfg (t' + 1)).loc p) ∨ φ ((e.cfg (t' + 1)).loc p) < φ ((e.cfg t').loc p)) :
    ∃ t' ≥ t, G ((e.cfg t').loc p) := by
  have hpend' : ∀ t' ≥ t, (e.cfg t').pend p ≠ none := fun t' ht' => by
    rw [pend_persist e t₀ H.noret ht hpend t' ht']; exact hpend
  refine e.exists_good p (fun t' => G ((e.cfg t').loc p)) (fun t' => φ ((e.cfg t').loc p)) t
    (fun t' ht' _ => H.fair p t' (hpend' t' ht')) (fun t' ht' hg hproc hst => ?_)
    (fun t' ht' _ hn => Or.inr (by rw [loc_of_not_step e (hpend' t' ht') hn]))
  apply hp t' ht' hg
  cases hl : e.lbl t' with
  | inv q o => rw [hl] at hst; exact absurd hst id
  | ret q r => exact absurd hl (H.noret t' (by omega) q r)
  | tau q => rw [hl] at hproc; simp only [Label.proc] at hproc; rw [hproc]

end Hyp

end AnonymousMutex.Alg2
