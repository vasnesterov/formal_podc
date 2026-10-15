import Papers.PODC2024.RecoverableConsensus.Config

/-!
# Lemmas 10 and 12 of Ovens (PODC'24)

`last = p_{n-1}`. Throughout, `RecConsensus A` (recoverable wait-free consensus, individual
crashes), `1 ≤ z`, `2 ≤ n`, and valency is w.r.t. Ovens' `E*_z`.
-/

namespace Cslib.SharedMemory.Recoverable.Ovens

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T} {z : ℕ}

/-- The process `p_{n-1}`. -/
def last (n : ℕ) (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/-! ## Crash budgets -/

lemma InEs.snoc_crash {L : List (Ev n)} {c : Fin n} (h : InEs z L)
    (hc : crashes c L + 1 ≤ z * n * stepsBelow c L) : InEs z (L ++ [.crash c]) := by
  intro m
  by_cases hm : m ≤ L.length
  · rw [List.take_append_of_le_length hm]; exact h m
  · rw [List.take_of_length_le (by simp; omega)]
    intro r
    rw [crashes_append, stepsBelow_append]
    by_cases hr : r = c
    · subst hr
      simp [crashes, Ev.isStepBelow, stepsBelow] at hc ⊢
      simpa [crashes, stepsBelow] using hc
    · have := h.inE r
      have h0 : crashes r [Ev.crash c] = 0 := by simp [crashes, Ne.symm hr]
      have h1 : stepsBelow r [Ev.crash c] = 0 := by simp [stepsBelow, Ev.isStepBelow]
      rw [h0, h1]; simpa using this

/-- The crash budget computation of Lemma 12 (and of the proof of Theorem 13): after `α ∈ E*_z`,
a block `s` containing a step of a process smaller than `c` and at most one crash of `c`, an
execution `α' ∈ E*_z` and crash-free events `Y`, one more crash of `c` is within budget. -/
lemma inEs_budget (hz : 1 ≤ z) (hn : 2 ≤ n) {α s α' Y : List (Ev n)} {c : Fin n}
    (hα : InEs z α) (hs : InEs z s) (hα' : InEs z α') (hY : CrashFree Y)
    (hs1 : 1 ≤ stepsBelow c s) (hsc : crashes c s ≤ 1) :
    InEs z (α ++ s ++ α' ++ Y ++ [.crash c]) := by
  refine InEs.snoc_crash (((hα.append hs).append hα').append_crashFree hY) ?_
  have h1 := hα.inE c
  have h2 := hα'.inE c
  have hK : 2 ≤ z * n := by nlinarith
  have h3 : z * n * 1 ≤ z * n * stepsBelow c s := Nat.mul_le_mul_left _ hs1
  simp only [crashes_append, stepsBelow_append, crashes_eq_zero_of_crashFree hY, mul_add]
  omega

/-! ## Lemma 10 -/

/-- **Lemma 10** of Ovens (PODC'24). Let `α` be an execution from `D` (valency w.r.t. `E*_z(D)`,
`z ≥ 1`) in which all processes are poised on `O`, and let `p_{n-1}` be on team `v̄`. If `p` is
on team `v`, `q` on team `v̄`, and the schedules `pσ`, `qτ` (of distinct processes) give `O` the
same value, then `q = p_{n-1}` and `τ` is empty. -/
theorem lemma10 (hA : RecConsensus A) (hz : 1 ≤ z) (hn : 2 ≤ n) {D : Cfg A}
    (hD : Reach A (fun _ => True) D) {α : List (Ev n)} {O : ι}
    (hpo : ∀ p, (run D α).Poised p O) {v : Bool}
    (hlast : Team z D α (last n (by omega)) (!v)) {p q : Fin n} {σ τ : List (Fin n)}
    (hp : Team z D α p v) (hq : Team z D α q (!v)) (hσ : (p :: σ).Nodup) (hτ : (q :: τ).Nodup)
    (heq : valAfter (run D α) O (p :: σ) = valAfter (run D α) O (q :: τ)) :
    q = last n (by omega) ∧ τ = [] := by
  have hAdm := admOK_true (n := n) z
  set L := last n (by omega) with hL
  by_contra hne
  have hpL : p ≠ L := by
    rintro rfl
    have := hp.unique hA hAdm hD hlast
    cases v <;> simp at this
  have hlt : ∀ r : Fin n, r ≠ L → r < L := by
    intro r hr
    rw [Fin.lt_def]
    have : r.val ≠ n - 1 := fun h => hr (Fin.ext h)
    have := r.isLt
    simp [hL, last]; omega
  have hpL' : p < L := hlt p hpL
  have hqτ : ∃ r ∈ q :: τ, r < L := by
    by_cases hqL : q = L
    · have hτne : τ ≠ [] := fun h => hne ⟨hqL, h⟩
      obtain ⟨r, τ', rfl⟩ := List.exists_cons_of_ne_nil hτne
      have hrq : r ≠ q := by
        intro h; subst h
        simp at hτ
      exact ⟨r, by simp, hlt r (hqL ▸ hrq)⟩
    · exact ⟨q, by simp, hlt q hqL⟩
  have hzn : 1 ≤ z * n := by nlinarith
  have hα : InEs z α := by
    have := hp.1; exact this.of_append_left
  have hβ : InEs z (α ++ [.step p] ++ (σ.map Ev.step ++ [.crash L])) := by
    have := hα.append (inEs_steps_crashes hzn (p :: σ) [L] (by simp)
      (fun c hc => by simp at hc; subst hc; exact ⟨p, by simp, hpL'⟩))
    simpa using this
  have hβ' : InEs z (α ++ [.step q] ++ (τ.map Ev.step ++ [.crash L])) := by
    have := hα.append (inEs_steps_crashes hzn (q :: τ) [L] (by simp)
      (fun c hc => by simp at hc; subst hc; exact hqτ))
    simpa using this
  refine team_contra hA hAdm hD hp hq (r := L) hβ hβ' ?_
  have e1 : run D (α ++ [.step p] ++ (σ.map Ev.step ++ [.crash L])) =
      (run (run D α) ((p :: σ).map Ev.step)).next (.crash L) := by
    simp [run_append]
  have e2 : run D (α ++ [.step q] ++ (τ.map Ev.step ++ [.crash L])) =
      (run (run D α) ((q :: τ).map Ev.step)).next (.crash L) := by
    simp [run_append]
  rw [e1, e2]
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [crash_mem]
    exact mem_eq_of_valAfter_eq hpo hσ hτ heq
  · simp at hr; subst hr
    simp

/-! ## Lemma 12 -/

/-- The common first part of Lemma 12 and of the inductive step of Theorem 13: after the team-`v`
schedule `p ρ` (containing a process `< k`) and the crashes `λ_k`, the configuration is
indistinguishable to `p_k,…,p_{n-1}` from `CαXλ_k`, and `{p_k,…,p_{n-1}}` is `v`-univalent
there. -/
lemma after_crashes (hA : RecConsensus A) (hz : 1 ≤ z) (hn : 2 ≤ n) {D : Cfg A}
    (hD : Reach A (fun _ => True) D) {α : List (Ev n)} (hc : Crit z D α) {v : Bool} {p : Fin n}
    (hp : Team z D α p v) {ρ : List (Fin n)} {X : List (Ev n)} {k : ℕ}
    (hℓ : ∃ q ∈ p :: ρ, q.val < k) (hX : ∀ e ∈ X, k ≤ e.proc.val)
    (hmem : (run (run D α) ((p :: ρ).map Ev.step)).mem = (run (run D α) X).mem) :
    InEs z ((p :: ρ).map Ev.step ++ lam n k) ∧
    Univ z D (α ++ ((p :: ρ).map Ev.step ++ lam n k)) v ∧
    AgreeOn {r | k ≤ r.val} (run D (α ++ ((p :: ρ).map Ev.step ++ lam n k)))
      (run (run D α) (X ++ lam n k)) ∧
    (∀ r : Fin n, ¬ k ≤ r.val → ∀ w, ¬ (run (run D α) (X ++ lam n k)).Out r w) ∧
    UnivQ z (run (run D α) (X ++ lam n k)) {r | k ≤ r.val} [] v := by
  have hAdm := admOK_true (n := n) z
  have hzn : 1 ≤ z * n := by nlinarith
  have hs : InEs z ((p :: ρ).map Ev.step ++ lam n k) := by
    unfold lam
    refine inEs_steps_crashes hzn _ _ (List.Nodup.filter _ (List.nodup_finRange n)) ?_
    intro c hc
    obtain ⟨q, hq, hqk⟩ := hℓ
    simp at hc
    exact ⟨q, hq, by rw [Fin.lt_def]; omega⟩
  have hW : InEs z (α ++ ((p :: ρ).map Ev.step ++ lam n k)) := hc.1.append hs
  have hU : Univ z D (α ++ ((p :: ρ).map Ev.step ++ lam n k)) v := by
    have := hp.append (β := ρ.map Ev.step ++ lam n k) (by simpa using hW)
    simpa using this
  have hag : AgreeOn {r | k ≤ r.val} (run D (α ++ ((p :: ρ).map Ev.step ++ lam n k)))
      (run (run D α) (X ++ lam n k)) := by
    simp only [run_append]
    refine ⟨by rw [run_lam_mem, run_lam_mem, hmem], fun r hr => ⟨?_, by simp⟩⟩
    simp only [Set.mem_ofPred_eq] at hr
    rw [run_lam_loc, run_lam_loc]
    simp [hr]
  have hout : ∀ r : Fin n, ¬ k ≤ r.val → ∀ w, ¬ (run (run D α) (X ++ lam n k)).Out r w := by
    intro r hr w hw
    apply hc.not_out hA hAdm hD r w
    have : (run (run D α) (X ++ lam n k)).loc r = (run D α).loc r := by
      apply run_loc_other
      intro e he hre
      rcases List.mem_append.1 he with he | he
      · exact hr (hre ▸ hX e he)
      · exact hr (hre ▸ lam_proc he)
    simpa [Cfg.Out, this] using hw
  exact ⟨hs, hU, hag, hout, UnivQ.transfer (hU.univQ _) hag (fun r hr w => hout r hr w)⟩

/-- **Lemma 12** of Ovens (PODC'24). Let `α` be critical w.r.t. `E*_z(D)` (`z ≥ 1`), `p` on team
`v` in `Cα`, and let `X` be an execution of processes `≥ k` (in the paper `X = ⟨⟩` or
`X = p_{n-1}`, with `k > ℓ`) such that the schedule `p ρ` (which contains a process `p_ℓ` with
`ℓ < k`) leaves the memory as `X` does. Then for any execution `α'` of processes `≥ k` that is
critical w.r.t. `E*_z(CαXλ_k)`, the configuration `CαXλ_kα'` is `n`-recording or `v`-hiding. -/
theorem lemma12 (hA : RecConsensus A) (hz : 1 ≤ z) (hn : 2 ≤ n) {D : Cfg A}
    (hD : Reach A (fun _ => True) D) {α : List (Ev n)} (hc : Crit z D α) {v : Bool} {p : Fin n}
    (hp : Team z D α p v) {ρ : List (Fin n)} {X : List (Ev n)} {k : ℕ} (hk : k ≤ n - 1)
    (hℓ : ∃ q ∈ p :: ρ, q.val < k) (hX : ∀ e ∈ X, k ≤ e.proc.val)
    (hmem : (run (run D α) ((p :: ρ).map Ev.step)).mem = (run (run D α) X).mem)
    {α' : List (Ev n)} (hα' : ∀ e ∈ α', k ≤ e.proc.val)
    (hc' : Crit z (run (run D α) (X ++ lam n k)) α') {O' : ι}
    (hpo' : ∀ r, (run (run (run D α) (X ++ lam n k)) α').Poised r O') :
    Recording z (run (run D α) (X ++ lam n k)) α' O' ∨
      Hiding z (run (run D α) (X ++ lam n k)) α' O' v := by
  have hAdm := admOK_true (n := n) z
  have hzn : 1 ≤ z * n := by nlinarith
  obtain ⟨hs_step, hU, hag, hout, hD'U⟩ := after_crashes hA hz hn hD hc hp hℓ hX hmem
  set W := α ++ ((p :: ρ).map Ev.step ++ lam n k) with hWdef
  set D' := run (run D α) (X ++ lam n k) with hD'
  set E' := run D' α' with hE'
  set L := last n (by omega) with hL
  have hD'r : Reach A (fun _ => True) D' := reach_run (reach_run hD _) _
  have hLk : k ≤ L.val := by simp [hL, last]; omega
  have hlt : ∀ r : Fin n, r ≠ L → r < L := by
    intro r hr
    rw [Fin.lt_def]
    have : r.val ≠ n - 1 := fun h => hr (Fin.ext h)
    have := r.isLt
    simp [hL, last]; omega
  -- `{p_k,…,p_{n-1}}` is `v`-univalent in `α'`; in particular `p_{n-1}` is on team `v`
  have hU' : UnivQ z D' {r | k ≤ r.val} α' v := by
    have := hD'U.append (β := α') (fun e he => hα' e he) (by simpa using hc'.1)
    simpa using this
  have hLv : Team z D' α' L v := hc'.team_of_univQ hA hAdm hD'r hU' hLk
  -- the indistinguishable execution `γ = α'` after `Cα p ρ λ_k`
  set G := run (run D W) α' with hG
  have hagG : AgreeOn {r | k ≤ r.val} G E' := run_agreeOn hag α' (fun e he => hα' e he)
  have hagGL : AgreeOn {L} G E' := hagG.mono (by simpa using hLk)
  -- `p_{n-1}` decides `v` after `αpρλ_kγ` followed by `c_{n-1}` or `p_{n-1} c_{n-1}`
  have hsL1 : 1 ≤ stepsBelow L ((p :: ρ).map Ev.step ++ lam n k) := by
    obtain ⟨q, hq, hqk⟩ := hℓ
    rw [stepsBelow_append]
    have := stepsBelow_steps_pos hq (show q < L by rw [Fin.lt_def]; omega)
    omega
  have hsLc : crashes L ((p :: ρ).map Ev.step ++ lam n k) ≤ 1 := by
    rw [crashes_append, crashes_steps, crashes_lam]; split_ifs; all_goals omega
  have hdecv : ∀ Y : List (Ev n), CrashFree Y →
      SoloOut (run G (Y ++ [.crash L])) L v := by
    intro Y hY
    have hb := inEs_budget (s := (p :: ρ).map Ev.step ++ lam n k) hz hn hc.1 hs_step hc'.1 hY
      hsL1 hsLc
    have hU2 := hU.append (β := α' ++ Y ++ [.crash L]) (by simpa [hWdef] using hb)
    have := UnivQ.soloOut hA hAdm hD hU2 (Set.mem_univ L)
    simpa [hG, run_append, hWdef] using this
  -- `p_{n-1}`'s state after a crash
  have hcrashL : ∀ (F F' : Cfg A), F.mem = F'.mem → F.inp = F'.inp →
      AgreeOn {L} (F.next (.crash L)) (F'.next (.crash L)) := by
    intro F F' hm hi
    refine ⟨by simpa using hm, fun r hr => ?_⟩
    simp at hr; subst hr
    simp [hi]
  have hinpG : G.inp = E'.inp := by
    show (run (run D W) α').inp = (run D' α').inp
    simp [hD']
  rcases obs11 (z := z) D' α' O' with hrec | ⟨w, hw⟩ | ⟨j₀, σ₀, m₀, τ₀, hj₀, hm₀, hσ₀, hτ₀, he₀⟩
  · exact Or.inl hrec
  · by_cases hwv : w = v
    · subst hwv; exact Or.inr hw
    exfalso
    have hw' : w = !v := by cases w <;> cases v <;> simp_all
    subst hw'
    -- Case 1: `v̄`-hiding
    obtain ⟨m, σm, hm, hσm, hval⟩ := hw.2
    have hmL : m ≠ L := by
      rintro rfl
      have := hm.unique hA hAdm hD'r hLv
      cases v <;> simp at this
    have hb : InEs z (α' ++ [.step m] ++ (σm.map Ev.step ++ [.crash L])) := by
      have := hc'.1.append (inEs_steps_crashes hzn (m :: σm) [L] (by simp)
        (fun c hc => by simp at hc; subst hc; exact ⟨m, by simp, hlt m hmL⟩))
      simpa using this
    have h1 := UnivQ.soloOut hA hAdm hD'r (Univ.append hm hb) (Set.mem_univ L)
    have e1 : run D' (α' ++ [.step m] ++ (σm.map Ev.step ++ [.crash L])) =
        (run E' ((m :: σm).map Ev.step)).next (.crash L) := by simp [hE', run_append]
    rw [e1] at h1
    have hag1 : AgreeOn {L} ((run E' ((m :: σm).map Ev.step)).next (.crash L))
        (G.next (.crash L)) := by
      refine hcrashL _ _ ?_ (by simp [hinpG])
      rw [mem_eq_of_valAfter_eq_self hpo' hσm hval.symm, hagG.1]
    have h2 := h1.of_agreeOn hag1
    have h3 := hdecv [] (fun _ h => by simp at h)
    simp only [List.nil_append] at h3
    have := h2.unique h3
    cases v <;> simp at this
  · exfalso
    -- Case 2: two schedules starting on different teams give the same value
    obtain ⟨j, σj, m, σm, hj, hm, hσj, hσm, he⟩ : ∃ j σj m σm, Team z D' α' j v ∧
        Team z D' α' m (!v) ∧ (j :: σj).Nodup ∧ (m :: σm).Nodup ∧
        valAfter E' O' (m :: σm) = valAfter E' O' (j :: σj) := by
      cases v
      · exact ⟨j₀, σ₀, m₀, τ₀, hj₀, hm₀, hσ₀, hτ₀, he₀.symm⟩
      · exact ⟨m₀, τ₀, j₀, σ₀, hm₀, hj₀, hτ₀, hσ₀, he₀⟩
    have hLv' : Team z D' α' L (!!v) := by simpa using hLv
    have hj' : Team z D' α' j (!!v) := by simpa using hj
    obtain ⟨rfl, rfl⟩ := lemma10 hA hz hn hD'r hpo' hLv' hm hj' hσm hσj he
    have hmL : m ≠ L := by
      rintro rfl
      have := hm.unique hA hAdm hD'r hLv
      cases v <;> simp at this
    have hb : InEs z (α' ++ [.step m] ++ (σm.map Ev.step ++ [.crash L])) := by
      have := hc'.1.append (inEs_steps_crashes hzn (m :: σm) [L] (by simp)
        (fun c hc => by simp at hc; subst hc; exact ⟨m, by simp, hlt m hmL⟩))
      simpa using this
    have h1 := UnivQ.soloOut hA hAdm hD'r (Univ.append hm hb) (Set.mem_univ L)
    have e1 : run D' (α' ++ [.step m] ++ (σm.map Ev.step ++ [.crash L])) =
        (run E' ((m :: σm).map Ev.step)).next (.crash L) := by simp [hE', run_append]
    rw [e1] at h1
    have hag1 : AgreeOn {L} ((run E' ((m :: σm).map Ev.step)).next (.crash L))
        ((run E' [Ev.step L]).next (.crash L)) := by
      refine hcrashL _ _ ?_ (by simp)
      exact mem_eq_of_valAfter_eq hpo' hσm (List.nodup_singleton L) he
    have hag2 : AgreeOn {L} ((run E' [Ev.step L]).next (.crash L))
        ((run G [Ev.step L]).next (.crash L)) := by
      have := run_agreeOn hagGL.symm [Ev.step L, Ev.crash L] (by simp)
      simpa [run_append] using this
    have h2 := (h1.of_agreeOn hag1).of_agreeOn hag2
    have h3 := hdecv [Ev.step L] (crashFree_steps [L])
    simp only [List.singleton_append, run_cons, run_nil] at h3
    simp only [run_cons, run_nil] at h2
    have := h2.unique h3
    cases v <;> simp at this

end Cslib.SharedMemory.Recoverable.Ovens
