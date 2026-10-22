import Papers.PODC2022.RecoverableHarder.Recording
import Papers.PODC2024.RecoverableConsensus.Corollaries

/-!
# Theorem 14: recoverable consensus among `n ≥ 3` processes needs an `(n-1)`-recording type

The paper's proof (Section 3.2): a critical execution `γ` (valency w.r.t. executions in which only
one process `c` crashes, and not more often than the others step), all processes poised on one
object `O` (operations `op_p`, value `q₀`), process valencies `v_p`, **Lemma 15** (two schedules of
distinct processes that both contain a process other than `c` and lead `O` to the same value start
with processes of the same valency — `c` crashes afterwards and cannot tell them apart), the team
construction (Cases 1/2, properties P1, P2) and the verification of the three conditions
(Cases a/b/c of condition 3).

We work in the crash-recovery model of CSLib with Ovens' valency sets `E*_z` (`z = 1`) and take
for `c` the process with the largest identifier: then one crash of `c` after any step of another
process is admissible, which is all the proof uses of the paper's set `E_A`.

* `lemma15`, `theorem14_alg` (any object family), `theorem14` (`S` with read/write objects).
* `theorem14_of_ovens`: the stronger statement (`n`-recording, `n ≥ 2`) from Ovens' Theorem 13
  (PODC'24), formalized in `Papers/PODC2024/RecoverableConsensus`.
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

section Thm14

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

/-- **Lemma 15.** At a critical execution `α` (w.r.t. `E*_1`) where every process `p` is poised to
apply `o p` to `O`: if two schedules `p :: σ`, `q :: τ` of distinct processes, each containing a
process other than the last process `c`, lead `O` to the same value, then `p` and `q` have the
same valency. -/
theorem lemma15 (hA : RecConsensus A) (hn : 2 ≤ n) {x : Fin n → Bool} {α : List (Ev n)}
    (hc : Crit 1 (initCfg A x) α) {O : ι} (o : Fin n → (T O).Op)
    (κ : (p : Fin n) → (T O).Resp → A.L)
    (hok : ∀ p, A.act ((run (initCfg A x) α).loc p) = .access O (o p) (κ p))
    {p q : Fin n} {σ τ : List (Fin n)} (hσ : (p :: σ).Nodup) (hτ : (q :: τ).Nodup)
    (hσc : ∃ r ∈ p :: σ, r ≠ last n (by omega)) (hτc : ∃ r ∈ q :: τ, r ≠ last n (by omega))
    (heq : apply (T O) ((run (initCfg A x) α).mem O) o (p :: σ) =
      apply (T O) ((run (initCfg A x) α).mem O) o (q :: τ))
    {v w : Bool} (hp : Team 1 (initCfg A x) α p v) (hq : Team 1 (initCfg A x) α q w) : v = w := by
  have hAdm := admOK_true (n := n) 1
  have hC : Reach A (fun _ => True) (initCfg A x) := Reach.initial hAdm x
  set c := last n (by omega)
  set E := run (initCfg A x) α
  by_contra hvw
  have hw : w = !v := by cases v <;> cases w <;> simp_all
  subst hw
  -- the two extensions: the schedule, then a crash of `c`
  have hbudget : ∀ (l : List (Fin n)), (∃ r ∈ l, r ≠ c) →
      InEs 1 (α ++ l.map Ev.step ++ [.crash c]) := by
    intro l ⟨r, hr, hrc⟩
    have hrc' : r < c := by
      rcases lt_or_gt_of_ne hrc with h | h
      · exact h
      · exfalso; have := r.isLt; simp [c, last, Fin.lt_def] at h; omega
    refine InEs.snoc_crash (hc.1.append_crashFree (crashFree_steps l)) ?_
    have h1 := hc.1.inE c
    have h2 := stepsBelow_steps_pos hr hrc'
    rw [crashes_append, stepsBelow_append, crashes_eq_zero_of_crashFree (crashFree_steps l)]
    have hn1 : 1 ≤ n := by omega
    simp only [one_mul] at h1 ⊢
    nlinarith
  have hmem : ∀ (l : List (Fin n)), l.Nodup →
      (run E (l.map Ev.step ++ [.crash c])).mem = Function.update E.mem O (apply (T O) (E.mem O) o l) := by
    intro l hl
    rw [run_append]
    simp only [run_cons, run_nil, crash_mem]
    exact run_steps_poised o κ l hl E (fun p _ => hok p)
  have hag : AgreeOn {c} (run (initCfg A x) (α ++ [.step p] ++ (σ.map Ev.step ++ [.crash c])))
      (run (initCfg A x) (α ++ [.step q] ++ (τ.map Ev.step ++ [.crash c]))) := by
    have e1 : α ++ [.step p] ++ (σ.map Ev.step ++ [.crash c]) =
        α ++ ((p :: σ).map Ev.step ++ [.crash c]) := by simp
    have e2 : α ++ [.step q] ++ (τ.map Ev.step ++ [.crash c]) =
        α ++ ((q :: τ).map Ev.step ++ [.crash c]) := by simp
    rw [e1, e2, run_append _ α, run_append _ α]
    refine ⟨by rw [hmem _ hσ, hmem _ hτ, heq], fun r hr => ?_⟩
    simp only [Set.mem_singleton_iff] at hr; subst hr
    simp only [run_append, run_cons, run_nil, crash_loc_self, Cfg.next, run_inp]
    simp
  exact team_contra hA (admOK_true 1) hC hp hq (r := c)
    (by simpa using hbudget (p :: σ) hσc) (by simpa using hbudget (q :: τ) hτc) hag

/-- **Theorem 14** (for any object family). If an algorithm for `n ≥ 3` processes solves
recoverable consensus (individual crashes), one of its object types is `(n-1)`-recording. -/
theorem theorem14_alg (hn : 3 ≤ n) (hA : RecConsensus A) : ∃ i, IsRecording (n - 1) (T i) := by
  classical
  have hAdm := admOK_true (n := n) 1
  let x : Fin n → Bool := fun r => decide (r.val = 1)
  have hC : Reach A (fun _ => True) (initCfg A x) := Reach.initial hAdm x
  have hb := biv_initial (z := 1) hA hAdm x ⟨⟨0, by omega⟩, by simp [x]⟩ ⟨⟨1, by omega⟩, by simp [x]⟩
  obtain ⟨α, hc⟩ := exists_crit hA hAdm hC hb
  obtain ⟨O, hpo⟩ := hc.poised hA hAdm hC (by omega)
  choose o κ hok using hpo
  set E := run (initCfg A x) α
  set c := last n (by omega)
  -- valencies
  choose val hval using fun p => hc.team p
  have huniq : ∀ p v, Team 1 (initCfg A x) α p v → v = val p :=
    fun p v h => Team.unique hA hAdm hC h (hval p)
  have L15 : ∀ p σ q τ, (p :: σ).Nodup → (q :: τ).Nodup → (∃ r ∈ p :: σ, r ≠ c) →
      (∃ r ∈ q :: τ, r ≠ c) → apply (T O) (E.mem O) o (p :: σ) = apply (T O) (E.mem O) o (q :: τ) →
      val p = val q :=
    fun p σ q τ h1 h2 h3 h4 h5 => lemma15 hA (by omega) hc o κ hok h1 h2 h3 h4 h5 (hval p) (hval q)
  -- not all valencies are equal
  obtain ⟨⟨p0, hp0⟩, ⟨q0, hq0⟩⟩ := hc.teams hA hAdm hC (by omega)
  have hv0 : val p0 = false := (huniq p0 false hp0).symm
  have hv1 : val q0 = true := (huniq q0 true hq0).symm
  -- a cycle followed by one more process
  have cyc_snoc : ∀ (l : List (Fin n)) k, l.Nodup → k ∉ l →
      apply (T O) (E.mem O) o l = E.mem O →
      apply (T O) (E.mem O) o (l ++ [k]) = apply (T O) (E.mem O) o [k] := by
    intro l k _ _ h; rw [apply_append, h]
  have nd_snoc : ∀ (l : List (Fin n)) k, l.Nodup → k ∉ l → (l ++ [k]).Nodup := by
    intro l k hl hk
    rw [List.nodup_append]
    exact ⟨hl, by simp, fun a ha b hb => by simp at hb; subst hb; rintro rfl; exact hk ha⟩
  -- three distinct processes
  have third : ∀ a b : Fin n, ∃ r, r ≠ a ∧ r ≠ b := by
    intro a b
    by_contra hno
    push Not at hno
    have : (Finset.univ : Finset (Fin n)) ⊆ {a, b} := fun r _ => by
      by_cases h : r = a
      · simp [h]
      · simp [hno r h]
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_insert_le a {b}
    simp at h1 h2; omega
  -- the choice of `ℓ` and of the reserve process `r` (the paper's `p_n`)
  obtain ⟨ℓ, r, hrc, hrℓ, hcase⟩ : ∃ ℓ r : Fin n, r ≠ c ∧ val r ≠ val ℓ ∧
      ((∀ j, j ≠ ℓ → val j ≠ val ℓ) ∨
        ((∀ i, ∃ j, j ≠ i ∧ val j = val i) ∧
          ((∃ l : List (Fin n), l.Nodup ∧ l ≠ [] ∧ apply (T O) (E.mem O) o l = E.mem O) →
            ∃ lam : List (Fin n), (ℓ :: lam).Nodup ∧
              apply (T O) (E.mem O) o (ℓ :: lam) = E.mem O))) := by
    by_cases h1 : ∃ i, ∀ j, j ≠ i → val j ≠ val i
    · -- Case 1
      obtain ⟨i, hi⟩ := h1
      obtain ⟨r, hri, hrc⟩ := third i c
      exact ⟨i, r, hrc, hi r hri, Or.inl hi⟩
    · -- Case 2
      push Not at h1
      have h1' : ∀ i, ∃ j, j ≠ i ∧ val j = val i := by
        intro i; obtain ⟨j, hj, hv⟩ := h1 i; exact ⟨j, hj, hv⟩
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin n, (∃ l : List (Fin n), l.Nodup ∧ l ≠ [] ∧
          apply (T O) (E.mem O) o l = E.mem O) → ∃ lam : List (Fin n), (ℓ :: lam).Nodup ∧
            apply (T O) (E.mem O) o (ℓ :: lam) = E.mem O := by
        by_cases hcy : ∃ l : List (Fin n), l.Nodup ∧ l ≠ [] ∧ apply (T O) (E.mem O) o l = E.mem O
        · obtain ⟨l, hl, hne, he⟩ := hcy
          obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hne
          exact ⟨h, fun _ => ⟨t, hl, he⟩⟩
        · exact ⟨c, fun h => absurd h hcy⟩
      -- a process `ℓ'` with a different valency, chosen different from `c`
      obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ', val ℓ' ≠ val ℓ := by
        cases h : val ℓ
        · exact ⟨q0, by rw [hv1]; simp⟩
        · exact ⟨p0, by rw [hv0]; simp⟩
      by_cases hℓc : ℓ' = c
      · obtain ⟨j, hj, hjv⟩ := h1' ℓ'
        exact ⟨ℓ, j, by rw [← hℓc]; exact hj, by rw [hjv]; exact hℓ', Or.inr ⟨h1', hℓ⟩⟩
      · exact ⟨ℓ, ℓ', hℓc, hℓ', Or.inr ⟨h1', hℓ⟩⟩
  -- the teams: `A` = valency of `ℓ`, `B` = the other valency, among the processes other than `r`
  let team : Fin n → Bool := fun p => decide (val p ≠ val ℓ)
  let R : Finset (Fin n) := Finset.univ.erase r
  have hrR : r ∉ R := by simp [R]
  have hmemR : ∀ p, p ∈ R ↔ p ≠ r := by simp [R]
  have hrec : RecOn (T O) R (E.mem O) team o := by
    refine ⟨⟨ℓ, (hmemR ℓ).2 (fun h => hrℓ (by rw [h])), by simp [team]⟩, ?_, ?_, ?_⟩
    · -- team `B` meets `R`
      rcases hcase with hi | ⟨h1', -⟩
      · obtain ⟨j, hjℓ, hjr⟩ := third ℓ r
        exact ⟨j, (hmemR j).2 hjr, by simp [team, hi j hjℓ]⟩
      · obtain ⟨j, hjr, hjv⟩ := h1' r
        exact ⟨j, (hmemR j).2 hjr, by simp [team, hjv, hrℓ]⟩
    · -- condition 1 (P1 and Figure 3(c))
      intro p σ q τ hp hq hpn hqn tp tq heq
      have hpr : r ∉ p :: σ := fun h => hrR (hp r h)
      have hqr : r ∉ q :: τ := fun h => hrR (hq r h)
      have := L15 p (σ ++ [r]) q (τ ++ [r]) (nd_snoc _ r hpn hpr) (nd_snoc _ r hqn hqr)
        ⟨r, by simp, hrc⟩ ⟨r, by simp, hrc⟩ (by
          rw [show p :: (σ ++ [r]) = (p :: σ) ++ [r] by simp,
            show q :: (τ ++ [r]) = (q :: τ) ++ [r] by simp, apply_append, apply_append, heq])
      simp [team] at tp tq
      exact tq (this ▸ tp)
    · -- conditions 2 and 3
      intro p σ hp hpn hcyc
      have hpr : r ∉ p :: σ := fun h => hrR (hp r h)
      cases tp : team p
      · -- condition 2 (P2 and Figure 3(d)): no cycle starts on team `A`
        exfalso
        have := L15 p (σ ++ [r]) r [] (nd_snoc _ r hpn hpr) (by simp) ⟨r, by simp, hrc⟩
          ⟨r, by simp, hrc⟩ (by
            rw [show p :: (σ ++ [r]) = (p :: σ) ++ [r] by simp, apply_append, hcyc])
        simp [team] at tp
        exact hrℓ (this.symm.trans tp)
      · rcases hcase with hi | ⟨h1', hℓ⟩
        · -- Case 1: team `A` is `{ℓ}`
          refine ⟨ℓ, ⟨(hmemR ℓ).2 (fun h => hrℓ (by rw [h])), by simp [team]⟩,
            fun j ⟨_, hj⟩ => ?_⟩
          by_contra hjℓ
          simp [team, hi j hjℓ] at hj
        · -- Case 2: cases a, b, c of the paper — no cycle starts on team `B`
          exfalso
          obtain ⟨lam, hlam, hlamc⟩ := hℓ ⟨p :: σ, hpn, by simp, hcyc⟩
          simp [team] at tp
          apply tp
          by_cases ha : ∃ k, k ≠ c ∧ val k = val p ∧ k ∉ ℓ :: lam
          · -- Case a (Figure 3(e))
            obtain ⟨k, hkc, hkv, hkl⟩ := ha
            have := L15 ℓ (lam ++ [k]) k [] (nd_snoc _ k hlam hkl) (by simp) ⟨k, by simp, hkc⟩
              ⟨k, by simp, hkc⟩ (by
                rw [show ℓ :: (lam ++ [k]) = (ℓ :: lam) ++ [k] by simp, apply_append, hlamc])
            rw [this, hkv]
          by_cases hb' : ∃ k, k ≠ c ∧ val k = val ℓ ∧ k ∉ p :: σ
          · -- Case b
            obtain ⟨k, hkc, hkv, hkl⟩ := hb'
            have := L15 p (σ ++ [k]) k [] (nd_snoc _ k hpn hkl) (by simp) ⟨k, by simp, hkc⟩
              ⟨k, by simp, hkc⟩ (by
                rw [show p :: (σ ++ [k]) = (p :: σ) ++ [k] by simp, apply_append, hcyc])
            exact this.trans hkv
          · -- Case c (Figure 3(f))
            push Not at ha hb'
            have hk1 : ∃ k, k ≠ c ∧ val k = val ℓ := by
              by_cases hℓc : ℓ = c
              · obtain ⟨j, hj, hjv⟩ := h1' ℓ; exact ⟨j, hℓc ▸ hj, hjv⟩
              · exact ⟨ℓ, hℓc, rfl⟩
            have hk2 : ∃ k, k ≠ c ∧ val k = val p := by
              by_cases hpc : p = c
              · obtain ⟨j, hj, hjv⟩ := h1' p; exact ⟨j, hpc ▸ hj, hjv⟩
              · exact ⟨p, hpc, rfl⟩
            obtain ⟨k1, hk1c, hk1v⟩ := hk1
            obtain ⟨k2, hk2c, hk2v⟩ := hk2
            exact (L15 ℓ lam p σ hlam hpn ⟨k2, ha k2 hk2c hk2v, hk2c⟩
              ⟨k1, hb' k1 hk1c hk1v, hk1c⟩ (by rw [hlamc, hcyc])).symm
  refine ⟨O, ?_⟩
  have := hrec.isRecording
  rwa [show R.card = n - 1 by simp [R]] at this

/-- **Theorem 14.** For `n ≥ 3`, if a deterministic type `S` (with read/write objects) solves
recoverable consensus among `n` processes, then `S` is `(n-1)`-recording. -/
theorem theorem14 {S : ObjSpec} (hn : 3 ≤ n) (h : RecSolvable S n) : IsRecording (n - 1) S := by
  obtain ⟨ιR, ιS, _, _, R, hR, A, hA⟩ := h
  obtain ⟨i, hi⟩ := theorem14_alg hn hA
  rcases i with j | j
  · exact absurd hi (not_recording_of_rwLike (hR j) _)
  · exact hi

/-- The stronger statement obtained from Ovens' Theorem 13 (PODC'24): recoverable consensus among
`n ≥ 2` processes needs an `n`-recording type (so Theorem 14's bound `n - 1` is not tight). -/
theorem theorem14_of_ovens {S : ObjSpec} (hn : 2 ≤ n) (h : RecSolvable S n) : IsRecording n S := by
  obtain ⟨ιR, ιS, _, _, R, hR, A, hA⟩ := h
  obtain ⟨i, hi⟩ := theorem13 hn hA
  rcases i with j | j
  · exact absurd hi (not_recording_of_rwLike (hR j) _)
  · exact hi

end Thm14

end Podc.RecoverableHarder
