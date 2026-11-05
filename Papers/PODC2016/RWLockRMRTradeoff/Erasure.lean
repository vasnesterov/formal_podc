import Papers.PODC2016.RWLockRMRTradeoff.Awareness

/-!
# Lemma 3: removing a process and everything that depends on it

Given an execution fragment `C ↪ E` and a process `p`, remove from `E` every step after which the
stepping process is aware of `p` (in particular all steps of `p`). The result `E'` is again an
execution fragment from `C` (`xrun_eraseFrom`); every process that is not aware of `p` at the end
of `E` takes exactly the same steps and ends in the same local state.

The paper says "steps executed by other processes *when they are aware of* `p`"; its proof
(a read `s_q` returning a value written by a removed step "should have been removed as well") shows
that the step through which a process *becomes* aware of `p` must be removed too, i.e. awareness is
taken *after* the step. Read literally (awareness before the step), the statement is false: if `p`
writes `1` to `v` and then `q` reads `v`, the read of `q` is kept but returns a different value.
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq ι] [DecidableEq V] [DecidableEq P] {v₀ : V}
variable {I : Impl A (Regs ι V v₀) P L} {cm : CacheModel P ι}

variable (p : P)

/-- The labels of `E` kept when removing `p` (Lemma 3): a label is kept iff after it the stepping
process is not aware of `p`. -/
noncomputable def eraseFrom : Ext I cm → List (Label P A) → List (Label P A)
  | _, [] => []
  | X, ℓ :: β =>
    match xstep X ℓ with
    | none => []
    | some Y => (if p ∈ Y.kn.aw ℓ.proc then [] else [ℓ]) ++ eraseFrom Y β

/-- The relation between a configuration of `E` and the corresponding configuration of `E'`. -/
structure ERel (X X' : Ext I cm) : Prop where
  mem : ∀ i, p ∉ X.kn.fam i → X'.cfg.mem i = X.cfg.mem i
  loc : ∀ q, p ∉ X.kn.aw q → X'.cfg.loc q = X.cfg.loc q
  pend : ∀ q, p ∉ X.kn.aw q → X'.cfg.pend q = X.cfg.pend q

variable {p}

/-- The familiarity set of the accessed variable after a step: either the step is trivial (value
and familiarity set unchanged) or the familiarity set is the stepping process's awareness set. -/
lemma tau_fam {X Y : Ext I cm} {q : P} {i : ι} {o : (Regs ι V v₀ i).Op} {k}
    (hact : I.act q (X.cfg.loc q) = .access i o k) (hs : xstep X (.tau q) = some Y) :
    (Y.cfg.mem i = X.cfg.mem i ∧ Y.kn.fam i = X.kn.fam i) ∨ Y.kn.fam i = Y.kn.aw q := by
  obtain ⟨h1, h2, -⟩ := xstep_eq_some.1 hs
  obtain ⟨-, -, i', o', k', hact', hm, -⟩ := Impl.step_tau h1
  rw [hact] at hact'; cases hact'
  rw [h2, hm]
  cases o with
  | read => left; rw [kstep_read I hact]; simp
  | write v =>
    rw [kstep_write I hact]
    by_cases hv : X.cfg.mem i = v
    · left; simp [hv]
    · right; simp [hv]
  | cas a b =>
    rw [kstep_cas I hact]
    by_cases hc : X.cfg.mem i = a ∧ b ≠ a
    · right; simp [hc]
    · left
      refine ⟨?_, by simp [hc]⟩
      simp only [Function.update_self]
      by_cases ha : X.cfg.mem i = a
      · have : b = a := by tauto
        simp [ha, this]
      · simp [ha]

lemma ERel.step {X X' Y : Ext I cm} {ℓ : Label P A} (hR : ERel p X X')
    (hs : xstep X ℓ = some Y) :
    (p ∈ Y.kn.aw ℓ.proc → ERel p Y X') ∧
      (p ∉ Y.kn.aw ℓ.proc → ∃ Y', xstep X' ℓ = some Y' ∧ ERel p Y Y') := by
  obtain ⟨h1, h2, -⟩ := xstep_eq_some.1 hs
  have haw := kstep_aw I X.cfg X.kn ℓ
  rw [← h2] at haw
  -- processes other than the stepping one
  have hoth := fun q (hq : ℓ.proc ≠ q) => Impl.step_other h1 hq
  cases ℓ with
  | inv q o =>
    obtain ⟨hp, hal, hpe, hlo, hm⟩ := Impl.step_inv h1
    have hK : Y.kn = X.kn := by rw [h2]; rfl
    refine ⟨fun hpq => ⟨fun i hi => ?_, fun r hr => ?_, fun r hr => ?_⟩, fun hpq => ?_⟩
    · rw [hm]; exact hR.mem i (by rwa [hK] at hi)
    · have hrq : q ≠ r := by rintro rfl; exact hr hpq
      rw [(hoth r hrq).1]; exact hR.loc r (by rwa [hK] at hr)
    · have hrq : q ≠ r := by rintro rfl; exact hr hpq
      rw [(hoth r hrq).2]; exact hR.pend r (by rwa [hK] at hr)
    · simp only [Label.proc] at hpq
      have hq' : p ∉ X.kn.aw q := by rwa [hK] at hpq
      have hp' : X'.cfg.pend q = none := (hR.pend q hq').trans hp
      have hs' := Impl.step_inv_eq_some (I := I) (o := o) hp' hal
      refine ⟨⟨_, kstep I X'.cfg X'.kn (.inv q o), cacheStep I cm X'.cfg X'.cache (.inv q o)⟩,
        xstep_eq_some.2 ⟨hs', rfl, rfl⟩, fun i hi => ?_, fun r hr => ?_, fun r hr => ?_⟩
      · simp only; rw [hm]; exact hR.mem i (by rwa [hK] at hi)
      · simp only [hlo]
        by_cases hrq : r = q
        · subst hrq; simp [hR.loc r hq']
        · simp [Function.update_of_ne hrq, hR.loc r (by rwa [hK] at hr)]
      · simp only [hpe]
        by_cases hrq : r = q
        · subst hrq; simp
        · simp [Function.update_of_ne hrq, hR.pend r (by rwa [hK] at hr)]
  | ret q r₀ =>
    obtain ⟨hp, hpe, hm, l, hact, hlo⟩ := Impl.step_ret h1
    have hK : Y.kn = X.kn := by rw [h2]; rfl
    refine ⟨fun hpq => ⟨fun i hi => ?_, fun r hr => ?_, fun r hr => ?_⟩, fun hpq => ?_⟩
    · rw [hm]; exact hR.mem i (by rwa [hK] at hi)
    · have hrq : q ≠ r := by rintro rfl; exact hr hpq
      rw [(hoth r hrq).1]; exact hR.loc r (by rwa [hK] at hr)
    · have hrq : q ≠ r := by rintro rfl; exact hr hpq
      rw [(hoth r hrq).2]; exact hR.pend r (by rwa [hK] at hr)
    · simp only [Label.proc] at hpq
      have hq' : p ∉ X.kn.aw q := by rwa [hK] at hpq
      have hp' : X'.cfg.pend q ≠ none := by rw [hR.pend q hq']; exact hp
      have hs' := Impl.step_ret_eq_some (I := I) hp' (by rw [hR.loc q hq']; exact hact)
      refine ⟨⟨_, kstep I X'.cfg X'.kn (.ret q r₀), cacheStep I cm X'.cfg X'.cache (.ret q r₀)⟩,
        xstep_eq_some.2 ⟨hs', rfl, rfl⟩, fun i hi => ?_, fun r hr => ?_, fun r hr => ?_⟩
      · simp only; rw [hm]; exact hR.mem i (by rwa [hK] at hi)
      · simp only [hlo]
        by_cases hrq : r = q
        · subst hrq; simp
        · simp [Function.update_of_ne hrq, hR.loc r (by rwa [hK] at hr)]
      · simp only [hpe]
        by_cases hrq : r = q
        · subst hrq; simp
        · simp [Function.update_of_ne hrq, hR.pend r (by rwa [hK] at hr)]
  | tau q =>
    obtain ⟨hp, hpe, i, o, k, hact, hm, hlo⟩ := Impl.step_tau h1
    have hfam := tau_fam hact hs
    have hfj : ∀ j, j ≠ i → Y.kn.fam j = X.kn.fam j := fun j hj => by
      rw [h2]; exact kstep_fam_of_ne I _ _ _ j (by
        rintro q' i' o' k' hq' hact'
        cases hq'; rw [hact] at hact'; cases hact'; exact Ne.symm hj)
    have hmj : ∀ j, j ≠ i → Y.cfg.mem j = X.cfg.mem j := fun j hj => by
      rw [hm, Function.update_of_ne hj]
    refine ⟨fun hpq => ⟨fun j hj => ?_, fun r hr => ?_, fun r hr => ?_⟩, fun hpq => ?_⟩
    · simp only [Label.proc] at hpq
      by_cases hji : j = i
      · subst hji
        rcases hfam with ⟨hmem, hf⟩ | hf
        · rw [hmem]; exact hR.mem j (by rwa [hf] at hj)
        · exact absurd (hf ▸ hpq) hj
      · rw [hmj j hji]; exact hR.mem j (by rwa [hfj j hji] at hj)
    · have hrq : q ≠ r := by rintro rfl; exact hr hpq
      rw [(hoth r hrq).1]; exact hR.loc r (by rwa [(haw r).2 hrq] at hr)
    · have hrq : q ≠ r := by rintro rfl; exact hr hpq
      rw [(hoth r hrq).2]; exact hR.pend r (by rwa [(haw r).2 hrq] at hr)
    · simp only [Label.proc] at hpq
      have hq' : p ∉ X.kn.aw q := fun h => hpq ((haw q).1 h)
      have hp' : X'.cfg.pend q ≠ none := by rw [hR.pend q hq']; exact hp
      have hact' : I.act q (X'.cfg.loc q) = .access i o k := by rw [hR.loc q hq']; exact hact
      have hs' := Impl.step_tau_eq_some (I := I) hp' hact'
      -- the step has the same effect in both runs
      have hδ : (Regs ι V v₀ i).δ (X'.cfg.mem i) o = (Regs ι V v₀ i).δ (X.cfg.mem i) o := by
        cases o with
        | write v => rfl
        | read =>
          have : X.kn.fam i ⊆ Y.kn.aw q := by rw [h2, kstep_read I hact]; simp
          rw [hR.mem i (fun h => hpq (this h))]
        | cas a b =>
          have : X.kn.fam i ⊆ Y.kn.aw q := by rw [h2, kstep_cas I hact]; simp
          rw [hR.mem i (fun h => hpq (this h))]
      refine ⟨⟨_, kstep I X'.cfg X'.kn (.tau q), cacheStep I cm X'.cfg X'.cache (.tau q)⟩,
        xstep_eq_some.2 ⟨hs', rfl, rfl⟩, fun j hj => ?_, fun r hr => ?_, fun r hr => ?_⟩
      · simp only [hm]
        by_cases hji : j = i
        · subst hji; simp only [Function.update_self]; exact congrArg (·.1) hδ
        · simp only [Function.update_of_ne hji]; exact hR.mem j (by rwa [hfj j hji] at hj)
      · simp only [hlo]
        by_cases hrq : r = q
        · subst hrq; simp only [Function.update_self]; exact congrArg (fun x => k x.2) hδ
        · simp [Function.update_of_ne hrq, hR.loc r (by rwa [(haw r).2 (Ne.symm hrq)] at hr)]
      · simp only [hpe]
        by_cases hrq : r = q
        · subst hrq; exact hR.pend r hq'
        · exact hR.pend r (by rwa [(haw r).2 (Ne.symm hrq)] at hr)

lemma ERel.run {X X' Y : Ext I cm} {β : List (Label P A)} (hR : ERel p X X')
    (h : xrun X β = some Y) : ∃ Y', xrun X' (eraseFrom p X β) = some Y' ∧ ERel p Y Y' := by
  induction β generalizing X X' with
  | nil => simp only [xrun_nil, Option.some.injEq] at h; subst h; exact ⟨X', rfl, hR⟩
  | cons ℓ β ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      simp only [eraseFrom, hs]
      obtain ⟨hk1, hk2⟩ := hR.step hs
      by_cases hd : p ∈ Z.kn.aw ℓ.proc
      · rw [if_pos hd, List.nil_append]; exact ih (hk1 hd) h
      · obtain ⟨Z', hs', hR'⟩ := hk2 hd
        obtain ⟨Y', h1, h2⟩ := ih hR' h
        refine ⟨Y', ?_, h2⟩
        rw [if_neg hd, List.singleton_append, xrun_cons, hs']
        exact h1

/-- **Lemma 3.** Removing from a fragment `C ↪ E` all steps after which the stepping process is
aware of `p` yields a fragment `C ↪ E'`; every process not aware of `p` at the end of `E` has the
same local state and pending operation at the end of `E'`. -/
theorem lemma3 {X Y : Ext I cm} {β : List (Label P A)} (hX : X.kn = Know.init)
    (h : xrun X β = some Y) :
    ∃ Y', xrun X (eraseFrom p X β) = some Y' ∧
      ∀ q, p ∉ Y.kn.aw q → Y'.cfg.loc q = Y.cfg.loc q ∧ Y'.cfg.pend q = Y.cfg.pend q := by
  have hR : ERel p X X := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨Y', h1, h2⟩ := hR.run h
  exact ⟨Y', h1, fun q hq => ⟨h2.loc q hq, h2.pend q hq⟩⟩

/-- No label of `p` is kept (every process is aware of itself). -/
lemma eraseFrom_proc_ne {X Y : Ext I cm} {β : List (Label P A)} (hK : KInv X.kn)
    (h : xrun X β = some Y) : ∀ ℓ ∈ eraseFrom p X β, ℓ.proc ≠ p := by
  induction β generalizing X with
  | nil => simp [eraseFrom]
  | cons ℓ β ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      have hKZ : KInv Z.kn := (xstep_eq_some.1 hs).2.1 ▸ hK.step X.cfg ℓ
      intro ℓ' hℓ'
      simp only [eraseFrom, hs] at hℓ'
      rcases List.mem_append.1 hℓ' with hm | hm
      · split_ifs at hm with hd
        · simp at hm
        · simp only [List.mem_singleton] at hm; subst hm
          rintro rfl; exact hd (hKZ.self_mem _)
      · exact ih hKZ h ℓ' hm

/-- All labels of a process that is not aware of `p` at the end are kept. -/
lemma eraseFrom_filter_of_not_mem {X Y : Ext I cm} {β : List (Label P A)}
    (h : xrun X β = some Y) (q : P) (hq : p ∉ Y.kn.aw q) :
    (eraseFrom p X β).filter (fun ℓ => decide (ℓ.proc = q)) =
      β.filter (fun ℓ => decide (ℓ.proc = q)) := by
  induction β generalizing X with
  | nil => simp [eraseFrom]
  | cons ℓ β ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      simp only [eraseFrom, hs]
      have ih' := ih h
      by_cases hpq : ℓ.proc = q
      · have hd : p ∉ Z.kn.aw ℓ.proc := by
          rw [hpq]; exact fun h' => hq (xrun_aw_mono h q h')
        rw [if_neg hd]
        simp [List.filter_cons, hpq, ih']
      · split_ifs <;> simp [List.filter_cons, hpq, ih']

/-- If `q` is already aware of `p`, no later label of `q` is kept. -/
lemma eraseFrom_filter_of_mem {X Y : Ext I cm} {β : List (Label P A)}
    (h : xrun X β = some Y) (q : P) (hq : p ∈ X.kn.aw q) :
    (eraseFrom p X β).filter (fun ℓ => decide (ℓ.proc = q)) = [] := by
  induction β generalizing X with
  | nil => simp [eraseFrom]
  | cons ℓ β ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      simp only [eraseFrom, hs]
      have hZ : p ∈ Z.kn.aw q := xrun_aw_mono (X := X) (α := [ℓ])
        (by simp [xrun_cons, hs]) q hq
      have ih' := ih h hZ
      by_cases hpq : ℓ.proc = q
      · rw [if_pos (hpq ▸ hZ)]; simpa using ih'
      · split_ifs <;> simp [List.filter_cons, hpq, ih']

/-- The kept labels of every process form a prefix of its labels. -/
lemma eraseFrom_filter_prefix {X Y : Ext I cm} {β : List (Label P A)}
    (h : xrun X β = some Y) (q : P) :
    (eraseFrom p X β).filter (fun ℓ => decide (ℓ.proc = q)) <+:
      β.filter (fun ℓ => decide (ℓ.proc = q)) := by
  induction β generalizing X with
  | nil => simp [eraseFrom]
  | cons ℓ β ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      simp only [eraseFrom, hs]
      have ih' := ih h
      by_cases hpq : ℓ.proc = q
      · by_cases hd : p ∈ Z.kn.aw ℓ.proc
        · rw [if_pos hd, List.nil_append, eraseFrom_filter_of_mem h q (hpq ▸ hd)]
          exact List.nil_prefix
        · rw [if_neg hd]
          simpa [List.filter_cons, hpq] using ih'
      · split_ifs <;> simpa [List.filter_cons, hpq] using ih'

lemma eraseFrom_sublist (X : Ext I cm) (β : List (Label P A)) : (eraseFrom p X β).Sublist β := by
  induction β generalizing X with
  | nil => simp [eraseFrom]
  | cons ℓ β ih =>
    simp only [eraseFrom]
    split
    · exact List.nil_sublist _
    · rename_i Y _
      split_ifs
      · exact (ih Y).cons ℓ
      · exact (ih Y).cons₂ ℓ

end Podc.RWLockRMRTradeoff
