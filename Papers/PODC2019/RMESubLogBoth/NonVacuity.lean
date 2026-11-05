import Papers.PODC2019.RMESubLogBoth.Liveness

/-!
# Non-vacuity: every schedule has a run; fair runs with finitely many crashes exist

Every process can always take a step (`step_total`): in particular a maximal path containing the
repairer's node exists at line 39 (the scanned graph is acyclic). Hence every schedule of events
yields a run (`exists_run`), and the round-robin schedule gives a fair crash-free run, so the
hypotheses of `starvation_freedom` are satisfiable.
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-- Every process can take a step in every reachable configuration. -/
theorem step_total {c : Cfg k} (hc : Reach c) (p : Fin k) : ∃ c', Step c p c' := by
  obtain ⟨own, hG, hL⟩ := inv_reach hc
  have hLp := hL p; unfold LI at hLp
  cases hpc : c.pc p with
  | rem =>
    cases hn : c.node p with
    | none => exact ⟨_, .l10_nil c p (.inl hpc) hn⟩
    | some x => exact ⟨_, .l10_some c p (.inl hpc) x hn⟩
  | l10 =>
    cases hn : c.node p with
    | none => exact ⟨_, .l10_nil c p (.inr hpc) hn⟩
    | some x => exact ⟨_, .l10_some c p (.inr hpc) x hn⟩
  | l11 => exact ⟨_, .l11 c p hpc⟩
  | l13 x => exact ⟨_, .l13 c p x hpc⟩
  | l14 x m => exact ⟨_, .l14 c p x m hpc⟩
  | l15 x m => exact ⟨_, .l15 c p x m hpc⟩
  | l18 x => exact ⟨_, .l18 c p x hpc⟩
  | l18w x => exact ⟨_, .l18w c p x hpc⟩
  | l19 x => exact ⟨_, .l19 c p x hpc⟩
  | l22a x => exact ⟨_, .l22a c p x hpc⟩
  | l22b => exact ⟨_, .l22b c p hpc⟩
  | l23 x v => exact ⟨_, .l23 c p x v hpc⟩
  | l24 x v =>
    cases hh : c.holder with
    | none => exact ⟨_, .l24_acq c p x v hpc (.inl hh)⟩
    | some q =>
      by_cases hq : q = p
      · subst hq; exact ⟨_, .l24_acq c q x v hpc (.inr hh)⟩
      · exact ⟨_, .l24_wait c p x v hpc q hh hq⟩
  | l30 x v => exact ⟨_, .l30 c p x v hpc⟩
  | l31 x => exact ⟨_, .l31 c p x hpc⟩
  | l33 x tl V E i =>
    by_cases hi : i < k
    · exact ⟨_, .l33 c p x tl V E i hpc hi⟩
    · exact ⟨_, .l33_end c p x tl V E i hpc (not_lt.mp hi)⟩
  | l35 x tl V E i a => exact ⟨_, .l35 c p x tl V E i a hpc⟩
  | l36 x tl V E i a => exact ⟨_, .l36 c p x tl V E i a hpc⟩
  | l39 x tl V E =>
    rw [hpc] at hLp
    obtain ⟨hn, -, -, EA, hS⟩ := hLp
    have hEV : ∀ u v, (u, v) ∈ E → u ∈ V ∧ v ∈ V := fun u v e => ⟨hS.Esrc u v e, hS.Etgt u v e⟩
    obtain ⟨σ, hσ, hxσ⟩ := exists_maxPath hEV hS.Eacyc (hS.x_mem hn)
    by_cases htl : tl ∈ V
    · obtain ⟨τ, hτ, htlτ⟩ := exists_maxPath hEV hS.Eacyc htl
      exact ⟨_, .l39 c p x tl V E hpc σ ⟨hσ, hxσ⟩ (some τ)
        ⟨fun _ => ⟨τ, rfl, hτ, htlτ⟩, fun h => absurd htl h⟩⟩
    · exact ⟨_, .l39 c p x tl V E hpc σ ⟨hσ, hxσ⟩ none
        ⟨fun h => absurd h htl, fun _ => rfl⟩⟩
  | l42 x tl V E mp tp hp dn =>
    by_cases h : ∃ σ, IsMaxPath V E σ ∧ σ ∉ dn
    · obtain ⟨σ, hσ, hd⟩ := h
      exact ⟨_, .l42_next c p x tl V E mp tp hp dn hpc σ hσ hd⟩
    · push_neg at h
      exact ⟨_, .l42_end c p x tl V E mp tp hp dn hpc h⟩
  | l43 x tl V E mp tp hp dn σ => exact ⟨_, .l43 c p x tl V E mp tp hp dn σ hpc⟩
  | l44 x tl V E mp tp hp dn σ => exact ⟨_, .l44 c p x tl V E mp tp hp dn σ hpc⟩
  | l46 x tl V E mp tp hp =>
    cases tp with
    | none => exact ⟨_, .l46_none c p x tl V E mp hp hpc⟩
    | some τ => exact ⟨_, .l46_some c p x tl V E mp τ hp hpc⟩
  | l47 x s => exact ⟨_, .l47 c p x s hpc⟩
  | l49 x m => exact ⟨_, .l49 c p x m hpc⟩
  | rx x v => exact ⟨_, .rx c p x v hpc⟩
  | l25 x v => exact ⟨_, .l25 c p x v hpc⟩
  | l26 x => exact ⟨_, .l26 c p x hpc⟩
  | cs x => exact ⟨_, .cs c p x hpc⟩
  | l28 x => exact ⟨_, .l28 c p x hpc⟩
  | l29 => exact ⟨_, .l29 c p hpc⟩

theorem next_total {c : Cfg k} (hc : Reach c) (e : Ev k) : ∃ c', Next c e c' := by
  cases e with
  | step p => exact step_total hc p
  | crash p => exact ⟨c.crash p, rfl⟩

/-- The configurations along a schedule. -/
noncomputable def runCfg (e : ℕ → Ev k) : ℕ → {c : Cfg k // Reach c}
  | 0 => ⟨Cfg.init, .init⟩
  | t + 1 =>
    let c := runCfg e t
    ⟨(next_total c.2 (e t)).choose, .next _ c.2 (next_total c.2 (e t)).choose_spec⟩

/-- Every schedule of events has a run. -/
theorem exists_run (e : ℕ → Ev k) : ∃ r : Run k, r.ev = e :=
  ⟨{ cfg := fun t => (runCfg e t).1, ev := e, init := rfl,
     next := fun t => (next_total (runCfg e t).2 (e t)).choose_spec }, rfl⟩

/-- The hypotheses of `starvation_freedom` are satisfiable: the round-robin schedule gives a fair
run without crashes. -/
theorem exists_fair_run (hk : 0 < k) : ∃ r : Run k, Fair r ∧ FinCrash r := by
  obtain ⟨r, hr⟩ := exists_run (fun t => Ev.step (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k))
  refine ⟨r, fun p t _ => ⟨k * t + p.val, ?_, .inl ?_⟩, ⟨0, fun t _ q => ?_⟩⟩
  · nlinarith [p.isLt]
  · rw [hr]; exact congrArg Ev.step (Fin.ext (by simp [Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]))
  · rw [hr]; simp

end Podc.RMESubLogBoth
