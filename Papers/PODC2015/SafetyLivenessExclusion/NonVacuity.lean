import Papers.PODC2015.SafetyLivenessExclusion.CounterexampleWF

/-!
# Non-vacuity of the hypotheses of `theorem_4_9_reactive`

The trivial safety property `U` (all well-formed histories) satisfies the paper's standing
assumptions for the class of reactive valid implementations: the "free" implementation `Iall`
(each invocation may be answered with any response, at any time) is reactive and valid, and every
well-formed history, finite or infinite, is one of its histories. Together with
`waitFree_assumptions` this shows that the hypotheses of `theorem_4_9_reactive` can be met.
-/

namespace Podc.SafetyLivenessExclusion.Counterexample

open Hist Impl

/-- The free implementation: a process is idle (`false`) or pending (`true`); invocations and
responses are always accepted; the base objects stutter. -/
abbrev Iall : Impl 2 Unit Unit where
  Q := Bool
  B := Unit
  initQ _ q := q = false
  initB _ := True
  invT _ q _ q' := q = false ∧ q' = true
  resT _ q _ q' := q = true ∧ q' = false
  stepT _ _ _ _ _ := False
  baseT _ _ := True

/-- Local states of `Iall` encoding the statuses. -/
def enc : PStat → Option Bool
  | .idle => some false
  | .pend => some true
  | .dead => none

/-- The state of `Iall` with statuses `σ`. -/
def cfgOf (σ : Fin 2 → PStat) : Iall.Cfg := ⟨fun i => enc (σ i), ()⟩

theorem cfgOf_update (σ : Fin 2 → PStat) (i : Fin 2) (s : PStat) :
    cfgOf (Function.update σ i s) = ⟨Function.update (cfgOf σ).loc i (enc s), ()⟩ := by
  simp only [cfgOf, Impl.Cfg.mk.injEq, and_true]
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem Iall_trans {σ σ' : Fin 2 → PStat} {e : E} (h : stepStat σ e = some σ') :
    Iall.Trans (cfgOf σ) (.ext e) (cfgOf σ') := by
  cases e with
  | inv i x =>
    obtain ⟨hi, rfl⟩ := stepStat_inv.1 h
    rw [cfgOf_update]
    exact Trans.inv (I := Iall) (q := false) (q' := true) (by simp [cfgOf, hi, enc]) ⟨rfl, rfl⟩
  | res i r =>
    obtain ⟨hi, rfl⟩ := stepStat_res.1 h
    rw [cfgOf_update]
    exact Trans.res (I := Iall) (q := true) (q' := false) (by simp [cfgOf, hi, enc]) ⟨rfl, rfl⟩
  | crash i =>
    obtain ⟨hi, rfl⟩ := stepStat_crash.1 h
    obtain ⟨q, hq⟩ : ∃ q, (cfgOf σ).loc i = some q := by
      simp only [cfgOf]
      cases h' : σ i
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
      · exact absurd h' hi
    rw [cfgOf_update]
    exact Trans.crash (I := Iall) hq

theorem Iall_init : Iall.IsInit (cfgOf fun _ => .idle) :=
  ⟨fun _ => ⟨false, rfl, rfl⟩, trivial⟩

theorem Iall_reach {c : Iall.Cfg} {l : List E} (hc : Iall.Reach c l) :
    ∃ σ, runStat l = some σ ∧ c = cfgOf σ := by
  refine Reach.induct (P := fun (c : Iall.Cfg) (l : List E) =>
    ∃ σ, runStat l = some σ ∧ c = cfgOf σ) ?_ ?_ hc
  · intro c hc
    refine ⟨_, rfl, ?_⟩
    obtain ⟨loc, mem⟩ := c
    cases mem
    simp only [cfgOf, Impl.Cfg.mk.injEq, and_true]
    refine funext fun i => ?_
    obtain ⟨q, hq, hq'⟩ := hc.1 i
    simp only at hq hq'
    rw [hq, hq']; rfl
  · rintro c l a c' - ⟨σ, hσ, rfl⟩ ht
    cases ht with
    | @inv i x q q' hq ht =>
      obtain ⟨rfl, rfl⟩ := ht
      have hi : σ i = .idle := by
        simp only [cfgOf] at hq
        cases h : σ i <;> simp_all [enc]
      refine ⟨Function.update σ i .pend, by simp [runStat_append, hσ, stepStat, hi], ?_⟩
      simp only [cfgOf, Impl.Cfg.mk.injEq, and_true]
      funext j
      by_cases hj : j = i
      · subst hj; simp [enc]
      · simp [Function.update_of_ne hj]
    | @res i r q q' hq ht =>
      obtain ⟨rfl, rfl⟩ := ht
      have hi : σ i = .pend := by
        simp only [cfgOf] at hq
        cases h : σ i <;> simp_all [enc]
      refine ⟨Function.update σ i .idle, by simp [runStat_append, hσ, stepStat, hi], ?_⟩
      simp only [cfgOf, Impl.Cfg.mk.injEq, and_true]
      funext j
      by_cases hj : j = i
      · subst hj; simp [enc]
      · simp [Function.update_of_ne hj]
    | @crash i q hq =>
      have hi : σ i ≠ .dead := by
        simp only [cfgOf] at hq
        intro h; simp [h, enc] at hq
      refine ⟨Function.update σ i .dead, by simp [runStat_append, hσ, stepStat, hi], ?_⟩
      simp only [cfgOf, Impl.Cfg.mk.injEq, and_true]
      funext j
      by_cases hj : j = i
      · subst hj; simp [enc]
      · simp [Function.update_of_ne hj]
    | step _ ht => exact absurd ht id
    | base _ => exact ⟨σ, by simpa using hσ, rfl⟩

theorem Iall_valid : Iall.Valid := by
  refine ⟨⟨_, Iall_init⟩, ?_, ?_⟩
  · rintro l ⟨c, hc⟩
    obtain ⟨σ, hσ, -⟩ := Iall_reach hc
    simp [WF, hσ]
  · intro c l hc σ hσ i hi x
    obtain ⟨σ', hσ', rfl⟩ := Iall_reach hc
    rw [hσ] at hσ'; cases hσ'
    exact ⟨_, Iall_trans (σ' := Function.update σ i .pend) (e := .inv i x) (by simp [stepStat, hi])⟩

theorem Iall_reactive : Iall.Reactive := by
  rintro c l - σ - i - ⟨c', ht⟩
  cases ht with
  | step _ h => exact h

theorem Iall_ensuresU : Iall.EnsuresS U := by
  rintro l ⟨c, hc⟩
  obtain ⟨σ, hσ, -⟩ := Iall_reach hc
  exact fin_mem_U.2 (by simp [WF, hσ])

theorem Iall_isHistOf {h : Hist E} (hh : h ∈ U) : Iall.IsHistOf h := by
  cases h with
  | fin l =>
    left
    refine ⟨l, rfl, ?_⟩
    have hwf := fin_mem_U.1 hh
    suffices H : ∀ σ, runStat l = some σ → Iall.Reach (cfgOf σ) l by
      obtain ⟨σ, hσ⟩ := hwf.exists
      exact ⟨_, H σ hσ⟩
    induction l using List.reverseRecOn with
    | nil =>
      intro σ hσ
      simp only [runStat_nil, Option.some.injEq] at hσ
      subst hσ; exact Reach.init Iall_init
    | append_singleton l e ih =>
      intro σ hσ
      obtain ⟨σ₀, h₀, he⟩ := runStat_append_eq_some.1 hσ
      have := (ih (safe_prefixClosed _ _ hh _ (List.prefix_append _ _)) hwf.of_append σ₀ h₀).trans
        (Iall_trans he)
      simpa using this
  | inf f =>
    right
    refine exists_infExec_of_blocks (P := fun k c => ∃ σ, runStat (pfx f k) = some σ ∧
      c = cfgOf σ) Iall_init ⟨_, rfl, rfl⟩ ?_
    rintro k c ⟨σ, hσ, rfl⟩
    obtain ⟨σ', hσ'⟩ := (fin_mem_U.1 (safe_prefixClosed _ _ hh _ (finPrefix_pfx f (k + 1)))).exists
    rw [pfx_succ] at hσ'
    obtain ⟨σ₀, h₀, he⟩ := runStat_append_eq_some.1 hσ'
    rw [hσ] at h₀; cases h₀
    have hb : Iall.Trans (cfgOf σ) .base (cfgOf σ) := Trans.base (I := Iall) (b' := ()) trivial
    exact ⟨.base, .base, .ext (f k), cfgOf σ, cfgOf σ, cfgOf σ', hb, hb,
      Iall_trans he, rfl, σ', by rw [pfx_succ]; exact hσ', rfl⟩

/-- The hypotheses of `theorem_4_9_reactive` are satisfiable: `U` satisfies the paper's
assumptions on safety properties for the reactive valid implementations, and wait-freedom those
on `Lmax`. -/
theorem nonvacuous_4_9 :
    SafetyAssumptions {I : Impl 2 Unit Unit | I.Valid ∧ I.Reactive} U ∧
      LmaxAssumptions WaitFree :=
  ⟨{ isSafety := safe_isSafety (by simp [WF])
     subset_U := le_rfl
     seq := fun i x => ⟨(), fin_mem_U.2 (by
       cases x; show (runStat _).isSome = true; fin_cases i <;> decide)⟩
     impl := fun _ hh => ⟨Iall, ⟨Iall_valid, Iall_reactive⟩, Iall_ensuresU, Iall_isHistOf hh⟩ },
    waitFree_assumptions⟩

end Podc.SafetyLivenessExclusion.Counterexample
