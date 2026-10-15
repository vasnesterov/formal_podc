import Papers.PODC2024.RecoverableConsensus.Lemma12

/-!
# Theorem 13 of Ovens (PODC'24): `n`-recording is necessary

If there is a recoverable wait-free consensus algorithm for `n ≥ 2` processes (individual
crashes) using objects of deterministic types `T i`, then some `T i` is `n`-recording.

The proof follows the paper: an initial bivalent configuration `C`, Lemma 6(b) (with `z = 1`,
`z' = 2`) gives `D₀ = Cβ` from which no nonempty `E_2`-extension leads to a configuration bivalent
w.r.t. its own `E*_1`; then a chain of critical configurations `D_i' = D_i α_i` is built in which
the processes `p_{n-i},…,p_{n-1}` are on team `v` and `D_i'` is `v`-hiding, until an
`n`-recording configuration is reached (`Stage` is the invariant (a)–(f) of the paper).
-/

namespace Cslib.SharedMemory.Recoverable.Ovens

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

/-! ## Crash accounting -/

lemma crashes_eq_zero_of_not_proc {δ : List (Ev n)} {r : Fin n} (h : ∀ e ∈ δ, e.proc ≠ r) :
    crashes r δ = 0 :=
  List.count_eq_zero.2 (fun hm => h _ hm rfl)

lemma stepsBelow_pos_of_mem {α : List (Ev n)} {q r : Fin n} (hq : Ev.step q ∈ α) (hqr : q < r) :
    1 ≤ stepsBelow r α := by
  unfold stepsBelow
  rw [Nat.one_le_iff_ne_zero, Ne, List.countP_eq_zero]
  push Not
  exact ⟨_, hq, by simp [Ev.isStepBelow, hqr]⟩

/-- The `E_2` computation in the proof of Theorem 13 ("`α_i` contains no steps by
`p_0,…,p_{n-i-1}`"). -/
lemma inE2_of_budget {δ αi : List (Ev n)} {k j : ℕ} (hj : j + 1 < n)
    (hδ : ∀ r : Fin n, k ≤ r.val → crashes r δ ≤ n * stepsBelow r δ + j)
    (hδ' : ∀ r : Fin n, r.val < k → crashes r δ = 0)
    (hαi : InEs 1 αi) (hstep : ∃ q : Fin n, q.val < k ∧ Ev.step q ∈ αi) :
    InE 2 (δ ++ lam n k ++ αi) := by
  intro r
  have h2 := hαi.inE r
  simp only [crashes_append, stepsBelow_append, crashes_lam, stepsBelow_lam] at h2 ⊢
  by_cases hr : k ≤ r.val
  · have h1 := hδ r hr
    obtain ⟨q, hqk, hq⟩ := hstep
    have h3 := stepsBelow_pos_of_mem hq (show q < r by rw [Fin.lt_def]; omega)
    have h4 : n * 1 ≤ n * stepsBelow r αi := Nat.mul_le_mul_left _ h3
    simp only [hr, ite_true]
    nlinarith
  · have h1 := hδ' r (by omega)
    simp only [hr, ite_false]
    nlinarith

/-- The bookkeeping of property (f) of Theorem 13. -/
lemma fb_step {δ αi : List (Ev n)} {k j : ℕ}
    (hδ : ∀ r : Fin n, k ≤ r.val → crashes r δ ≤ n * stepsBelow r δ + j) (hαi : InEs 1 αi) :
    ∀ r : Fin n, k ≤ r.val → crashes r (δ ++ lam n k ++ αi) ≤
      n * stepsBelow r (δ ++ lam n k ++ αi) + (j + 1) := by
  intro r hr
  have h1 := hδ r hr
  have h2 := hαi.inE r
  simp only [crashes_append, stepsBelow_append, crashes_lam, stepsBelow_lam, hr, ite_true] at h2 ⊢
  nlinarith

/-- If `α_i ∈ E*_1` has no steps of processes `< k`, it has no events of processes `< k`. -/
lemma events_ge_of_no_steps {αi : List (Ev n)} {k : ℕ} (hαi : InEs 1 αi)
    (h : ∀ q : Fin n, q.val < k → Ev.step q ∉ αi) : ∀ e ∈ αi, k ≤ e.proc.val := by
  intro e he
  by_contra hlt
  push Not at hlt
  cases e with
  | step q => exact h q hlt he
  | crash q =>
    have h0 : stepsBelow q αi = 0 := by
      unfold stepsBelow
      rw [List.countP_eq_zero]
      intro a ha
      cases a with
      | step q' =>
        simp only [Ev.isStepBelow, decide_eq_true_eq]
        intro hq'
        exact h q' (by simp at hlt; rw [Fin.lt_def] at hq'; omega) ha
      | crash _ => simp [Ev.isStepBelow]
    have := hαi.inE.crashes_eq_zero h0
    exact absurd this (Nat.pos_iff_ne_zero.1 (List.count_pos_iff.2 he))

/-! ## The stage invariant -/

/-- The final conclusion: the type of some object is `n`-recording. -/
def Final (T : ι → ObjSpec) (n : ℕ) : Prop := ∃ O, IsRecording n (T O)

/-- Invariant of the construction of Theorem 13 at stage `j` (properties (a)–(f) of the paper for
`D_j'`, which is `v`-hiding but not `n`-recording). -/
def Stage (D₀ : Cfg A) (v : Bool) (j : ℕ) : Prop :=
  ∃ (D : Cfg A) (α δ : List (Ev n)) (O : ι), Reach A (fun _ => True) D ∧ run D₀ δ = run D α ∧
    Crit 1 D α ∧ (∀ r, (run D α).Poised r O) ∧ (∀ e ∈ δ, n - j ≤ e.proc.val) ∧
    (∀ r : Fin n, n - j ≤ r.val → crashes r δ ≤ n * stepsBelow r δ + j) ∧
    (∀ r : Fin n, n - j ≤ r.val → Team 1 D α r v) ∧
    Hiding 1 D α O v ∧ ¬ Recording 1 D α O

/-- `D₀` is "stuck" (Lemma 6(b)): no nonempty `E_2`-extension leads to a configuration that is
bivalent w.r.t. its own `E*_1`. -/
def Stuck (D₀ : Cfg A) : Prop := ∀ γ, γ ≠ [] → InE 2 γ → ¬ Biv 1 (run D₀ γ) []

section Main

variable (hA : RecConsensus A) (hn : 2 ≤ n)
include hA hn

/-- After a critical `α_i` from `D_i = D_{i-1}' λ_k`: if `D₀` is stuck, `α_i` has no events of
processes `< k`. -/
lemma no_small_events {D₀ : Cfg A} (hst : Stuck D₀) {δ : List (Ev n)} {Di : Cfg A}
    (hDi : Reach A (fun _ => True) Di) (hrun : run D₀ (δ ++ lam n k) = Di)
    {j : ℕ} (hj : j + 1 < n) (hk : k ≤ n - 1)
    (hδ : ∀ r : Fin n, k ≤ r.val → crashes r δ ≤ n * stepsBelow r δ + j)
    (hδ' : ∀ r : Fin n, r.val < k → crashes r δ = 0)
    {αi : List (Ev n)} (hc : Crit 1 Di αi) : ∀ e ∈ αi, k ≤ e.proc.val := by
  refine events_ge_of_no_steps hc.1 (fun q hq hmem => ?_)
  have hE := inE2_of_budget hj hδ hδ' hc.1 ⟨q, hq, hmem⟩
  refine hst _ ?_ hE ?_
  · intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_nil] at this
    have := List.length_pos_iff.2 (lam_ne_nil (n := n) (k := k) (by omega))
    omega
  · rw [run_append, hrun]
    exact hc.biv hA (admOK_true 1) hDi (by omega)

/-- **The inductive step** of the proof of Theorem 13 ("Defining `D_i` and `D_i'`"). -/
theorem stage_step {D₀ : Cfg A} (hst : Stuck D₀) {v : Bool} {j : ℕ} (hS : Stage D₀ v j) :
    Final T n ∨ (Stage D₀ v (j + 1) ∧ j + 1 < n) := by
  have hAdm := admOK_true (n := n) 1
  obtain ⟨D, α, δ, O, hD, hrun, hc, hpo, hδev, hδfb, hteam, hhid, hnrec⟩ := hS
  set E := run D α with hE
  -- two distinct processes on team `v̄`
  obtain ⟨r₁, hr₁⟩ : ∃ r, Team 1 D α r (!v) := by
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc.teams hA hAdm hD (by omega)
    cases v
    · exact ⟨q, hq⟩
    · exact ⟨p, hp⟩
  have hnu := hhid.not_unique hnrec
  obtain ⟨r₂, hr₂, hne⟩ : ∃ r, Team 1 D α r (!v) ∧ r ≠ r₁ := by
    by_contra h
    push Not at h
    exact hnu ⟨r₁, hr₁, fun r hr => h r hr⟩
  have hsmall : ∀ r, Team 1 D α r (!v) → r.val < n - j := by
    intro r hr
    by_contra hge
    have := (hteam r (by omega)).unique hA hAdm hD hr
    cases v <;> simp at this
  -- one of them is `p_j` with `j < n - i`
  obtain ⟨q₁, hq₁, hq₁k⟩ : ∃ q, Team 1 D α q (!v) ∧ q.val < n - (j + 1) := by
    have h1 := hsmall r₁ hr₁
    have h2 := hsmall r₂ hr₂
    by_cases h : r₁.val < n - (j + 1)
    · exact ⟨r₁, hr₁, h⟩
    · refine ⟨r₂, hr₂, ?_⟩
      have : r₂.val ≠ r₁.val := fun h' => hne (Fin.ext h')
      omega
  set k := n - (j + 1) with hk
  have hjn : j + 1 < n := by omega
  -- hiding: a team-`v` schedule `p_k R_k` that does not change `O`
  obtain ⟨k₁, σ, hk₁, hσ, hval⟩ := hhid.2
  have hmem0 : (run E ((k₁ :: σ).map Ev.step)).mem = E.mem :=
    mem_eq_of_valAfter_eq_self hpo hσ hval.symm
  -- `p_j ∈ R_k`
  have hq₁mem : q₁ ∈ k₁ :: σ := by
    by_contra hnot
    have hs1 : InEs 1 (α ++ [.step k₁] ++ (σ.map Ev.step ++ [.step q₁])) := by
      have := hc.1.append_crashFree (crashFree_steps (k₁ :: σ ++ [q₁]))
      simpa using this
    have hs2 : InEs 1 (α ++ [.step q₁] ++ []) := by
      simpa using hc.1.append_crashFree (crashFree_steps [q₁])
    refine team_contra hA hAdm hD hk₁ hq₁ (r := q₁) hs1 hs2 ?_
    have e1 : run D (α ++ [.step k₁] ++ (σ.map Ev.step ++ [.step q₁])) =
        (run E ((k₁ :: σ).map Ev.step)).next (.step q₁) := by simp [hE, run_append]
    have e2 : run D (α ++ [.step q₁] ++ []) = E.next (.step q₁) := by simp [hE, run_append]
    rw [e1, e2]
    refine next_agreeOn ⟨hmem0, fun r hr => ?_⟩ _ (by simp)
    simp only [Set.mem_singleton_iff] at hr
    subst hr
    refine ⟨run_loc_other _ _ (fun e he h => hnot ?_), by simp⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
    simp only [Ev.proc_step] at h
    rwa [← h]
  have hℓ : ∃ q ∈ k₁ :: σ, q.val < k := ⟨q₁, hq₁mem, hq₁k⟩
  -- `D_i = D_{i-1}' λ_{n-i}`; `{p_{n-i},…,p_{n-1}}` is `v`-univalent there
  obtain ⟨hs, hU, hag, hout, hDiU⟩ := after_crashes (X := []) hA (le_refl 1) hn hD hc hk₁ hℓ
    (by simp) (by simpa using hmem0)
  set Di := run (run D α) ([] ++ lam n k) with hDi
  have hDir : Reach A (fun _ => True) Di := reach_run (reach_run hD _) _
  have hLk : k ≤ (last n (by omega)).val := by simp [last]; omega
  -- `D_i` is bivalent
  have hbiv : Biv 1 Di [] := by
    intro w
    have : ∃ r, SoloOut Di r w := by
      by_cases hw : w = v
      · subst hw; exact ⟨_, UnivQ.soloOut hA hAdm hDir hDiU hLk⟩
      · have hw' : w = !v := by cases w <;> cases v <;> simp_all
        subst hw'
        refine ⟨q₁, (hq₁.soloOut hA hAdm hD).of_agreeOn ?_⟩
        refine ⟨by simp [hDi, run_lam_mem], fun r hr => ?_⟩
        simp only [Set.mem_singleton_iff] at hr
        subst hr
        simp [hDi, run_lam_loc, show ¬ k ≤ r.val by omega]
    obtain ⟨r, m, hm⟩ := this
    exact ⟨solo r m, by simpa using InEs.of_crashFree (crashFree_replicate m r) 1,
      by simpa using Dec.of_out hm⟩
  -- `α_i` critical
  obtain ⟨αi, hci⟩ := exists_crit hA hAdm hDir hbiv
  have hrunDi : run D₀ (δ ++ lam n k) = Di := by rw [run_append, hrun]; rfl
  have hδ1 : ∀ r : Fin n, k ≤ r.val → crashes r δ ≤ n * stepsBelow r δ + j := by
    intro r hr
    by_cases hr' : n - j ≤ r.val
    · exact hδfb r hr'
    · rw [crashes_eq_zero_of_not_proc (fun e he h => hr' (by rw [← h]; exact hδev e he))]; omega
  have hδ2 : ∀ r : Fin n, r.val < k → crashes r δ = 0 := fun r hr =>
    crashes_eq_zero_of_not_proc (fun e he h => by have := hδev e he; rw [h] at this; omega)
  -- `α_i` has no events by `p_0,…,p_{n-i-1}`
  have hαev := no_small_events hA hn hst hDir hrunDi hjn (by omega) hδ1 hδ2 hci
  obtain ⟨O', hpo'⟩ := hci.poised hA hAdm hDir (by omega)
  -- Lemma 12
  have h12 := lemma12 (X := []) hA (le_refl 1) hn hD hc hk₁ (by omega) hℓ (by simp)
    (by simpa using hmem0) hαev hci hpo'
  by_cases hrec : Recording 1 Di αi O'
  · exact Or.inl ⟨O', hrec.isRecording hA hDir (by omega) hci hpo'⟩
  have hhid' := h12.resolve_left hrec
  refine Or.inr ⟨⟨Di, αi, δ ++ lam n k ++ αi, O', hDir, by rw [run_append, hrunDi], hci, hpo',
    ?_, ?_, ?_, hhid', hrec⟩, hjn⟩
  · intro e he
    rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · have := hδev e he; omega
      · exact lam_proc he
    · exact hαev e he
  · exact fb_step hδ1 hci.1
  · intro r hr
    have hU' : UnivQ 1 Di {r | k ≤ r.val} αi v := by
      have := hDiU.append (β := αi) (fun e he => hαev e he) (by simpa using hci.1)
      simpa using this
    exact hci.team_of_univQ hA hAdm hDir hU' hr

/-- The construction of `D₁, D₁'` when `D₀'` is neither `n`-recording nor `v`-hiding. -/
theorem base_special {D₀ : Cfg A} (hD₀ : Reach A (fun _ => True) D₀) (hst : Stuck D₀)
    (hc₀ : Crit 1 D₀ []) {O : ι} (hpo : ∀ r, (run D₀ []).Poised r O) {v : Bool}
    (hLv : Team 1 D₀ [] (last n (by omega)) (!v)) {pi pj : Fin n} {σi σj : List (Fin n)}
    (hpi : Team 1 D₀ [] pi v) (hpj : Team 1 D₀ [] pj (!v)) (hσi : (pi :: σi).Nodup)
    (hσj : (pj :: σj).Nodup)
    (heq : valAfter (run D₀ []) O (pi :: σi) = valAfter (run D₀ []) O (pj :: σj)) :
    Final T n ∨ Stage D₀ v 1 := by
  have hAdm := admOK_true (n := n) 1
  set L := last n (by omega) with hL
  obtain ⟨rfl, rfl⟩ := lemma10 hA (le_refl 1) hn hD₀ hpo hLv hpi hpj hσi hσj heq
  have hpiL : pi ≠ L := by
    rintro rfl
    have := hpi.unique hA hAdm hD₀ hLv
    cases v <;> simp at this
  have hpik : pi.val < n - 1 := by
    have : pi.val ≠ n - 1 := fun h => hpiL (Fin.ext h)
    have := pi.isLt
    omega
  have hmem : (run (run D₀ []) ((pi :: σi).map Ev.step)).mem = (run (run D₀ []) [Ev.step L]).mem :=
    mem_eq_of_valAfter_eq hpo hσi (List.nodup_singleton L) heq
  have hX : ∀ e ∈ [Ev.step L], n - 1 ≤ e.proc.val := by simp [hL, last]; omega
  obtain ⟨hs, hU, hag, hout, hD1U⟩ := after_crashes (X := [.step L]) (k := n - 1) hA (le_refl 1)
    hn hD₀ hc₀ hpi ⟨pi, by simp, hpik⟩ hX hmem
  set D₁ := run (run D₀ []) ([Ev.step L] ++ lam n (n - 1)) with hD₁
  have hD₁r : Reach A (fun _ => True) D₁ := reach_run (reach_run hD₀ _) _
  have hLk : n - 1 ≤ L.val := by simp [hL, last]
  -- `D₁ = D₀' p_{n-1} c_{n-1}` is bivalent
  have hbiv : Biv 1 D₁ [] := by
    intro w
    have : ∃ r, SoloOut D₁ r w := by
      by_cases hw : w = v
      · subst hw; exact ⟨L, UnivQ.soloOut hA hAdm hD₁r hD1U hLk⟩
      · have hw' : w = !v := by cases w <;> cases v <;> simp_all
        subst hw'
        let p₀ : Fin n := ⟨0, by omega⟩
        have h1 := UnivQ.soloOut hA hAdm hD₀ hLv (Set.mem_univ p₀)
        refine ⟨p₀, h1.of_agreeOn ?_⟩
        refine ⟨by simp [hD₁, run_lam_mem], fun r hr => ?_⟩
        simp only [Set.mem_singleton_iff] at hr
        subst hr
        have : ¬ n - 1 ≤ (0 : ℕ) := by omega
        simp [hD₁, run_lam_loc, p₀, this]
    obtain ⟨r, m, hm⟩ := this
    exact ⟨solo r m, by simpa using InEs.of_crashFree (crashFree_replicate m r) 1,
      by simpa using Dec.of_out hm⟩
  obtain ⟨α₁, hc₁⟩ := exists_crit hA hAdm hD₁r hbiv
  have hrunD₁ : run D₀ ([Ev.step L] ++ lam n (n - 1)) = D₁ := by simp [hD₁]
  have hδ1 : ∀ r : Fin n, n - 1 ≤ r.val →
      crashes r [Ev.step L] ≤ n * stepsBelow r [Ev.step L] + 0 := by
    intro r _; simp [crashes]
  have hδ2 : ∀ r : Fin n, r.val < n - 1 → crashes r [Ev.step L] = 0 := by
    intro r _; simp [crashes]
  -- `α₁` contains only events of `p_{n-1}`
  have hαev := no_small_events hA hn hst hD₁r hrunD₁ (j := 0) (by omega) (le_refl _) hδ1 hδ2 hc₁
  obtain ⟨O', hpo'⟩ := hc₁.poised hA hAdm hD₁r (by omega)
  have h12 := lemma12 (X := [.step L]) hA (le_refl 1) hn hD₀ hc₀ hpi (le_refl _)
    ⟨pi, by simp, hpik⟩ hX hmem hαev hc₁ hpo'
  by_cases hrec : Recording 1 D₁ α₁ O'
  · exact Or.inl ⟨O', hrec.isRecording hA hD₁r (by omega) hc₁ hpo'⟩
  have hhid := h12.resolve_left hrec
  refine Or.inr ⟨D₁, α₁, [Ev.step L] ++ lam n (n - 1) ++ α₁, O', hD₁r,
    by rw [run_append, hrunD₁], hc₁, hpo', ?_, ?_, ?_, hhid, hrec⟩
  · intro e he
    rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · simp at he; subst he; simp [hL, last]
      · exact lam_proc he
    · exact hαev e he
  · simpa using fb_step hδ1 hc₁.1
  · intro r hr
    have hU' : UnivQ 1 D₁ {r | n - 1 ≤ r.val} α₁ v := by
      have := hD1U.append (β := α₁) (fun e he => hαev e he) (by simpa using hc₁.1)
      simpa using this
    exact hc₁.team_of_univQ hA hAdm hD₁r hU' hr

/-- The construction of `D₀, D₀'` (and of `D₁, D₁'` in the special case). -/
theorem base_case {D₀ : Cfg A} (hD₀ : Reach A (fun _ => True) D₀) (hst : Stuck D₀)
    (hb : Biv 1 D₀ []) : Final T n ∨ ∃ v j, Stage D₀ v j := by
  have hAdm := admOK_true (n := n) 1
  obtain ⟨α₀, hc₀⟩ := exists_crit hA hAdm hD₀ hb
  -- `α₀` is empty by Lemma 6(b)
  have hα₀ : α₀ = [] := by
    by_contra hne
    exact hst α₀ hne (hc₀.1.inE.mono (by norm_num)) (hc₀.biv hA hAdm hD₀ (by omega))
  subst hα₀
  obtain ⟨O, hpo⟩ := hc₀.poised hA hAdm hD₀ (by omega)
  by_cases hrec : Recording 1 D₀ [] O
  · exact Or.inl ⟨O, hrec.isRecording hA hD₀ (by omega) hc₀ hpo⟩
  rcases obs11 (z := 1) D₀ [] O with hrec' | ⟨v, hv⟩ | ⟨p₁, σ₁, q₁, τ₁, hp₁, hq₁, hσ₁, hτ₁, he⟩
  · exact absurd hrec' hrec
  · refine Or.inr ⟨v, 0, D₀, [], [], O, hD₀, rfl, hc₀, hpo, by simp, by simp [crashes], ?_, hv, hrec⟩
    intro r hr
    exact absurd r.isLt (by omega)
  · obtain ⟨wL, hwL⟩ := hc₀.team (last n (by omega))
    cases wL
    · rcases base_special hA hn hD₀ hst hc₀ hpo (v := true) (by simpa using hwL) hq₁ hp₁ hτ₁ hσ₁
        he.symm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨true, 1, h⟩
    · rcases base_special hA hn hD₀ hst hc₀ hpo (v := false) (by simpa using hwL) hp₁ hq₁ hσ₁ hτ₁
        he with h | h
      · exact Or.inl h
      · exact Or.inr ⟨false, 1, h⟩

/-- The chain of stages terminates (the paper's induction on `i ≤ n - 1`). -/
theorem final_of_stage {D₀ : Cfg A} (hst : Stuck D₀) {v : Bool} :
    ∀ m j, n - j = m → Stage D₀ v j → Final T n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j hj hS
    rcases stage_step hA hn hst hS with hf | ⟨hS', hlt⟩
    · exact hf
    · exact ih (n - (j + 1)) (by omega) (j + 1) rfl hS'

end Main

/-- **Theorem 13** of Ovens (PODC'24). If there is a recoverable wait-free consensus algorithm
(individual crashes) for `n ≥ 2` processes using objects of deterministic types `T i`, then at
least one of the types `T i` is `n`-recording. -/
theorem theorem13 (hn : 2 ≤ n) (hA : RecConsensus A) : ∃ i, IsRecording n (T i) := by
  have hAdm1 := admOK_true (n := n) 1
  let x : Fin n → Bool := fun r => decide (r.val = 1)
  have hb := biv_initial (z := 1) hA hAdm1 x ⟨⟨0, by omega⟩, by simp [x]⟩
    ⟨⟨1, by omega⟩, by simp [x]⟩
  obtain ⟨β, hβ, hbD₀, hst⟩ := exists_stuck (le_of_lt one_lt_two) hA (admOK_true 2)
    (Reach.initial (admOK_true 2) x) hb
  have hstuck : Stuck (run (initCfg A x) β) := by
    intro γ hγ hE
    rw [← run_append]
    exact hst γ hγ (hβ.append hE)
  have hD₀ : Reach A (fun _ => True) (run (initCfg A x) β) := reach_run ⟨x, [], trivial, rfl⟩ β
  rcases base_case hA hn hD₀ hstuck hbD₀ with hf | ⟨v, j, hS⟩
  · exact hf
  · exact final_of_stage hA hn hstuck _ j rfl hS

/-- **Theorem 14** of Ovens (PODC'24): the recoverable consensus hierarchy is robust for
deterministic readable types — *assuming* Theorem 8 of Delporte-Gallet, Fatourou, Fauconnier and
Ruppert (PODC'22) (`dffr`: an `n`-recording deterministic readable type, together with registers,
solves recoverable consensus among `n` processes), which is cited by the paper and not
formalized here. If objects of readable types `T i` solve recoverable consensus among `n ≥ 2`
processes, then one type `T i` (with read/write objects) already does. -/
theorem theorem14
    (dffr : ∀ (S : ObjSpec) (m : ℕ), Readable S → IsRecording m S → RecSolvable S m)
    (hread : ∀ i, Readable (T i)) (hn : 2 ≤ n) (hA : RecConsensus A) :
    ∃ i, RecSolvable (T i) n := by
  obtain ⟨i, hi⟩ := theorem13 hn hA
  exact ⟨i, dffr _ _ (hread i) hi⟩

end Cslib.SharedMemory.Recoverable.Ovens
