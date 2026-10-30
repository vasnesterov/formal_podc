import Papers.PODC2020.RecoverableMutexRMR.LivenessCalls

/-!
# Liveness, part 5: the last call of `Move_Token()` (Lemma 2.5 of the paper)

After the last call of `Move_Token()` and the last crash (time `s`), no process is in a `Pre`
state (from there every crash-free run makes a call before it can wait at line 31 or return to
the remainder section, `no_pre`). Hence `C`, `D`, `Token` are constant, `A` changes only from
`0` to `−1`, and `W` only from `(ℓ+1, false)` to `(ℓ+1, true)`. The last caller `r` reads
`Token = L`, `D = d`, `C = c`, and then

* `A[L+1] = q`: `r` sets `W[q] = (L+1, true)` and `q` eventually enters the critical
  section, which is a `Pre` state;
* `A[L+1] ∈ {0, −1}` and `c ≤ d`: `r` skips ticket `L+1` and moves `Token` — a new call;
* `A[L+1] ∈ {0, −1}` and `c > d`: by `Φ ≥ 0` some process is in `I`, hence in a `Pre` state.

`last_call_false` derives the contradiction.
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

namespace Live

/-- From time `s` on, crashes happen only in the remainder section (they have no effect). -/
def NoEff (e : ℕ → Ev P) (s : ℕ) : Prop :=
  ∀ t, s ≤ t → ∀ p, e t = .crash p → (exec e t).pc p = .rem

lemma NoEff.cases {e : ℕ → Ev P} {s t : ℕ} (h : NoEff e s) (ht : s ≤ t) :
    (∃ r, e t = .step r) ∨ (exec e (t + 1) = exec e t ∧ ghost e (t + 1) = ghost e t) := by
  cases he : e t with
  | step r => exact Or.inl ⟨r, rfl⟩
  | crash p =>
    right
    have := h t ht p he
    simp [he, Cfg.next, Cfg.crash, this, Ghost.next]

lemma follow' {e : ℕ → Ev P} (hF : Fair e) {s τ : ℕ} {q : P} (hNE : NoEff e s) (hτ : s ≤ τ)
    (hq : (exec e τ).pc q ≠ .rem) :
    ∃ τ', τ ≤ τ' ∧ e τ' = .step q ∧ (exec e τ').pc q = (exec e τ).pc q := by
  classical
  have hex := hF q τ hq
  have hτ' : τ ≤ Nat.find hex ∧ e (Nat.find hex) = .step q := Nat.find_spec hex
  refine ⟨Nat.find hex, hτ'.1, hτ'.2, ?_⟩
  have : ∀ t, τ ≤ t → t ≤ Nat.find hex → (exec e t).pc q = (exec e τ).pc q := by
    intro t h1 h2
    induction t, h1 using Nat.le_induction with
    | base => rfl
    | succ t ht ih =>
      rw [← ih (by omega)]
      rcases hNE.cases (show s ≤ t by omega) with ⟨r, hr⟩ | ⟨h, -⟩
      · have hrq : r ≠ q := fun h => Nat.find_min hex (show t < Nat.find hex by omega)
          ⟨ht, h ▸ hr⟩
        exact pc_frame hr hrq
      · rw [h]
  exact this _ hτ'.1 le_rfl

lemma PendPC_Pre {k : PC P} (h : PendPC k) : Pre k := by
  cases k <;> simp_all [PendPC, Pre]

lemma Pre_ne_rem {k : PC P} (h : Pre k) : k ≠ .rem := by
  rintro rfl; simp [Pre] at h

lemma Pre_ne_w31 {k : PC P} (h : Pre k) (w : ℕ) : k ≠ .w31 w := by
  rintro rfl; simp [Pre] at h

section Final

variable {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t)) (hF : Fair e)
  {s T₂ : ℕ} (hNE : NoEff e s) (hNC : NoCrash e T₂)
  (hsk : ∀ t, T₂ ≤ t → ∀ x, (exec e (t + 1)).A x = .skipped → (exec e t).A x = .skipped)
  (hcall : ∀ t, s ≤ t → ¬ IsCall e t)
include hinv hF hNE hNC hsk hcall

/-- After the last call and the last crash, nobody is in a `Pre` state. -/
lemma no_pre : ∀ τ, s ≤ τ → ∀ q, ¬ Pre ((exec e τ).pc q) := by
  intro τ hτ q hP
  have hP' : ∀ t, τ ≤ t → Pre ((exec e t).pc q) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hP
    | succ t ht ih =>
      rcases hNE.cases (show s ≤ t by omega) with ⟨r, hr⟩ | ⟨h, -⟩
      · by_cases hrq : r = q
        · subst hrq
          rcases pre_step _ r (Or.inr ih) with h | h
          · rwa [exec_step hr]
          · exact absurd ⟨r, hr, by rw [exec_step hr]; exact h⟩ (hcall t (by omega))
        · rw [pc_frame hr hrq]; exact ih
      · rw [h]; exact ih
  obtain ⟨T, hT, w, hw⟩ := stuck hinv hF (s₀ := max τ T₂) (q := q) (hNC.mono (by omega))
    (fun t ht => hsk t (by omega))
    (fun t ht => Pre_ne_rem (hP' t (by omega)))
    (fun t ht _ w => Pre_ne_w31 (hP' t (by omega)) w)
  exact Pre_ne_w31 (hP' T (by omega)) w (hw T le_rfl)

omit hF in
/-- The effect of an event after the last call and the last crash, given that nobody is in a
`Pre` state. -/
lemma quiet {t : ℕ} (ht : s ≤ t) (hpre : ∀ q, ¬ Pre ((exec e t).pc q)) :
    (exec e (t + 1)).C = (exec e t).C ∧ (exec e (t + 1)).D = (exec e t).D ∧
      (exec e (t + 1)).T = (exec e t).T ∧
      (∀ x, (exec e (t + 1)).A x = (exec e t).A x ∨
        ((exec e t).A x = .empty ∧ (exec e (t + 1)).A x = .skipped)) ∧
      (∀ q, (exec e (t + 1)).W q = (exec e t).W q ∨
        ∃ ℓ, (exec e t).W q = (ℓ + 1, false) ∧ (exec e (t + 1)).W q = (ℓ + 1, true)) := by
  rcases hNE.cases ht with ⟨r, hr⟩ | ⟨h, -⟩
  · rw [exec_step hr]
    have hr' := hpre r
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases step_C (exec e t) r with h | ⟨h, -⟩
      · exact h
      · rw [h] at hr'; simp [Pre] at hr'
    · rcases step_D (exec e t) r with h | ⟨h | ⟨w, h⟩, -⟩
      · exact h
      · rw [h] at hr'; simp [Pre] at hr'
      · rw [h] at hr'; simp [Pre] at hr'
    · rcases step_T (exec e t) r with h | ⟨-, ρ, h⟩
      · exact h
      · exact absurd ⟨r, hr, by rw [exec_step hr, h]; exact ⟨ρ, rfl⟩⟩ (hcall t ht)
    · intro x
      rcases step_A (exec e t) r x with h | ⟨h0, ⟨h, -⟩ | ⟨-, h⟩⟩
      · exact Or.inl h
      · rw [h] at hr'; simp [Pre] at hr'
      · exact Or.inr ⟨h0, h⟩
    · intro q
      rcases step_W (exec e t) r q with h | ⟨rfl, ⟨c, h⟩ | h | h⟩ | ⟨ρ, ℓ, -, h1, h2⟩
      · exact Or.inl h
      · rw [h] at hr'; simp [Pre] at hr'
      · rw [h] at hr'; simp [Pre] at hr'
      · rw [h] at hr'; simp [Pre] at hr'
      · exact Or.inr ⟨ℓ, h1, h2⟩
  · rw [h]; exact ⟨rfl, rfl, rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩

/-- The analysis of the last call: contradiction with a process `p` waiting at line 31
forever. -/
theorem last_call_false {T₄ w : ℕ} {p r : P} {ρ : Ret}
    (hp : ∀ t, T₄ ≤ t → (exec e t).pc p = .w31 w) (hr : (exec e s).pc r = .m34 ρ) : False := by
  have hpre := no_pre hinv hF hNE hNC hsk hcall
  have hq := fun t (ht : s ≤ t) => quiet hinv hNE hNC hsk hcall ht (hpre t ht)
  -- `C`, `D`, `Token` are constant from `s` on
  have hconst : ∀ t, s ≤ t → (exec e t).C = (exec e s).C ∧ (exec e t).D = (exec e s).D ∧
      (exec e t).T = (exec e s).T := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨rfl, rfl, rfl⟩
    | succ t ht ih =>
      obtain ⟨h1, h2, h3, -⟩ := hq t ht
      exact ⟨h1.trans ih.1, h2.trans ih.2.1, h3.trans ih.2.2⟩
  set L := (exec e s).T with hL
  set c := (exec e s).C with hc
  set d := (exec e s).D with hd
  have hLc : L < c := by
    have := w31_bound hinv (hp (max s T₄) (by omega))
    rw [(hconst _ (by omega)).1, (hconst _ (by omega)).2.2] at this
    omega
  -- the run of the last caller `r`
  have hrun : ∀ τ k, s ≤ τ → (exec e τ).pc r = k → k ≠ .rem →
      ∃ τ', τ ≤ τ' ∧ e τ' = .step r ∧ (exec e τ').pc r = k := by
    intro τ k hτ hk hk'
    obtain ⟨τ', h1, h2, h3⟩ := follow' hF hNE hτ (by rw [hk]; exact hk')
    exact ⟨τ', h1, h2, h3.trans hk⟩
  obtain ⟨τ₁, h1, he1, hk1⟩ := hrun s _ le_rfl hr (by simp)
  have hs1 := exec_step he1
  have hk1' : (exec e (τ₁ + 1)).pc r = .m35 ρ L := by
    rw [hs1]; simp [Cfg.step, hk1, Cfg.setPc, (hconst τ₁ h1).2.2]
  obtain ⟨τ₂, h2, he2, hk2⟩ := hrun _ _ (by omega) hk1' (by simp)
  have hs2 := exec_step he2
  have hk2' : (exec e (τ₂ + 1)).pc r = .m36 ρ L d := by
    rw [hs2]; simp [Cfg.step, hk2, Cfg.setPc, (hconst τ₂ (by omega)).2.1]
  obtain ⟨τ₃, h3, he3, hk3⟩ := hrun _ _ (by omega) hk2' (by simp)
  have hs3 := exec_step he3
  have hk3' : (exec e (τ₃ + 1)).pc r = .m38 ρ L c d := by
    rw [hs3]; simp [Cfg.step, hk3, Cfg.setPc, (hconst τ₃ (by omega)).1, hLc]
  obtain ⟨τ₄, h4, he4, hk4⟩ := hrun _ _ (by omega) hk3' (by simp)
  have hs4 := exec_step he4
  -- `A[L+1]` does not become claimed after `s`
  have hnoclaim : ∀ t, s ≤ t → (∀ q, (exec e t).A (L + 1) ≠ .claimed q) →
      ∀ t', t ≤ t' → ∀ q, (exec e t').A (L + 1) ≠ .claimed q := by
    intro t ht h0 t' ht'
    induction t', ht' using Nat.le_induction with
    | base => exact h0
    | succ t' ht' ih =>
      intro q hq'
      rcases (hq t' (by omega)).2.2.2.1 (L + 1) with h | ⟨_, h⟩
      · exact ih q (h ▸ hq')
      · rw [h] at hq'; simp at hq'
  -- case `A[L+1] ∈ {0, −1}`
  have hfree : (∀ q, (exec e τ₄).A (L + 1) ≠ .claimed q) →
      (exec e (τ₄ + 1)).pc r = (if c ≤ d then .m46 ρ L else ρ.pc) → False := by
    intro hnc hk4'
    by_cases hcd : c ≤ d
    · simp only [hcd, ↓reduceIte] at hk4'
      obtain ⟨τ₅, h5, he5, hk5⟩ := hrun _ _ (by omega) hk4' (by simp)
      have hs5 := exec_step he5
      have hA5 : (exec e (τ₅ + 1)).A (L + 1) = .skipped := by
        have := hnoclaim τ₄ (by omega) hnc τ₅ (by omega)
        rw [hs5]; simp only [Cfg.step, hk5]
        split_ifs with h
        · simp
        · revert this h; cases (exec e τ₅).A (L + 1) <;> simp
      have hk5' : (exec e (τ₅ + 1)).pc r = .m47 ρ L := by
        rw [hs5]; simp [Cfg.step, hk5]
      obtain ⟨τ₆, h6, he6, hk6⟩ := hrun _ _ (by omega) hk5' (by simp)
      have hs6 := exec_step he6
      have hA6 : (exec e τ₆).A (L + 1) = .skipped := by
        rw [A_perm e h6 (by rw [hA5]; simp), hA5]
      have hk6' : (exec e (τ₆ + 1)).pc r = .m48 ρ L := by
        rw [hs6]; simp [Cfg.step, hk6, hA6, Cfg.setPc]
      obtain ⟨τ₇, h7, he7, hk7⟩ := hrun _ _ (by omega) hk6' (by simp)
      have hs7 := exec_step he7
      have hk7' : (exec e (τ₇ + 1)).pc r = .m34 ρ := by
        rw [hs7]; simp [Cfg.step, hk7, (hconst τ₇ (by omega)).2.2]
      exact hcall τ₇ (by omega) ⟨r, he7, by rw [hk7']; exact ⟨ρ, rfl⟩⟩
    · -- `c > d`: by `Φ ≥ 0`, some process is in `I`, hence in a `Pre` state
      have hphi := (hinv s).phi_nonneg
      unfold Phi at hphi
      rw [← hc, ← hd] at hphi
      have hpos : 0 < Isize (exec e s) (ghost e s) := by omega
      obtain ⟨o, ho⟩ := Finset.card_pos.1 hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
      rcases (hinv s).pend_pc o ho.2.2 with h | h
      · exact hpre s le_rfl o (PendPC_Pre h)
      · exact ho.2.1 h
  cases hA : (exec e τ₄).A (L + 1) with
  | empty =>
    exact hfree (by simp [hA]) (by rw [hs4]; simp [Cfg.step, hk4, Cfg.setPc, hA])
  | skipped =>
    exact hfree (by simp [hA]) (by rw [hs4]; simp [Cfg.step, hk4, Cfg.setPc, hA])
  | claimed q =>
    have hk4' : (exec e (τ₄ + 1)).pc r = .m40 ρ L q := by
      rw [hs4]; simp [Cfg.step, hk4, Cfg.setPc, hA]
    obtain ⟨τ₅, h5, he5, hk5⟩ := hrun _ _ (by omega) hk4' (by simp)
    have hs5 := exec_step he5
    -- `r` lets `q` enter: `W[q] ≠ (L+1, false)` from now on
    have hW5 : (exec e (τ₅ + 1)).W q ≠ (L + 1, false) := by
      rw [hs5]; simp only [Cfg.step, hk5]
      split_ifs with h
      · simp
      · exact h
    have hW : ∀ t, τ₅ + 1 ≤ t → (exec e t).W q ≠ (L + 1, false) := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact hW5
      | succ t ht ih =>
        rcases (hq t (by omega)).2.2.2.2 q with h | ⟨ℓ, -, h⟩
        · rw [h]; exact ih
        · rw [h]; simp
    have hAq : ∀ t, τ₄ ≤ t → (exec e t).A (L + 1) = .claimed q := fun t ht => by
      rw [A_perm e ht (by rw [hA]; simp), hA]
    -- hence `W[q] = (L+1, true)` (otherwise `q` would move `Token`, `progress`)
    have hW1 : ∀ t, max (τ₅ + 1) T₂ ≤ t → (exec e t).W q = (L + 1, true) := by
      intro t ht
      by_contra hne
      have hfst : ((exec e t).W q).1 ≠ L + 1 := by
        intro h1
        apply hne
        have := hW t (by omega)
        rcases hb : ((exec e t).W q).2 with _ | _
        · exact absurd (Prod.ext h1 hb) this
        · exact Prod.ext h1 hb
      exact progress hinv hF (s₀ := t) (hNC.mono (by omega))
        (fun t' ht' => (hconst t' (by omega)).2.2) (hAq t (by omega))
        (Or.inr (Or.inr (Or.inr hfst)))
    -- `q` is eventually stuck at line 31, although it may enter the critical section
    obtain ⟨T', hT', w', hw'⟩ := stuck hinv hF (s₀ := max (τ₅ + 1) T₂) (q := q)
      (hNC.mono (by omega)) (fun t ht => hsk t (by omega))
      (fun t ht hrem => by
        have hl := (hinv t).loc q
        rw [LI, hrem, hW1 t ht] at hl
        simp at hl)
      (fun t ht hcs' _ _ => hpre (t + 1) (by omega) q (by rw [hcs']; simp [Pre]))
    obtain ⟨t, ht, he⟩ := hF q T' (by rw [hw' T' le_rfl]; simp)
    have hl := (hinv t).loc q
    rw [LI, hw' t ht] at hl
    have hWt := hW1 t (by omega)
    have h1 := hw' (t + 1) (by omega)
    rw [exec_step he] at h1
    simp only [RetInv, hWt] at hl
    simp [Cfg.step, hw' t ht, Cfg.setPc, hWt, ← hl.2.1] at h1

end Final

/-- **Starvation freedom** (Lemma 2.13 of the paper), assuming the invariant along the
execution: in a fair execution with finitely many crashes, every process is infinitely often in
the remainder or the critical section. -/
theorem eventually_rem_or_cs_of_inv {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t))
    (hF : Fair e) (hC : FinCrashes e) (p : P) (t : ℕ) :
    ∃ t', t ≤ t' ∧ ((exec e t').pc p = .rem ∨ (exec e t').pc p = .cs) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T₀, hT₀⟩ := hC
  have hNC : NoCrash e T₀ := fun t ht p => hT₀ t ht p
  obtain ⟨T₂, hT₂, hsk⟩ := exists_no_new_skip hinv hNC
  -- `p` is eventually stuck at line 31
  obtain ⟨T₄, hT₄, w, hw⟩ := stuck hinv hF (s₀ := max t T₂) (q := p) (hNC.mono (by omega))
    (fun t' ht' => hsk t' (by omega)) (fun t' ht' => (hcon t' (by omega)).1)
    (fun t' ht' hcs => absurd hcs (hcon (t' + 1) (by omega)).2)
  -- `Token` is eventually constant
  obtain ⟨T₃, hT₃, hc₃⟩ := Nat.eventually_const_of_le_succ (f := fun t => (exec e t).T)
    (N := T₄) (B := w) (fun t ht => (w31_bound hinv (hw t ht)).1.le)
    (fun t _ => T_mono e (Nat.le_succ t))
  have hcs := no_cs hinv hF (s := T₃) (L := (exec e T₃).T) (hNC.mono (by omega)) hc₃
  -- calls of `Move_Token()` eventually stop, and there is at least one
  obtain ⟨T₅, hT₅, hstop⟩ := calls_stop hinv (hNC.mono (by omega)) hc₃ hcs
  obtain ⟨τp, hτp, hcallp⟩ := exists_call hinv (hw T₄ le_rfl)
  -- the last call or effective crash
  let Act : ℕ → Prop := fun k => IsCall e k ∨ ∃ c, e k = .crash c ∧ (exec e k).pc c ≠ .rem
  obtain ⟨m, -, hmB, hm, hlast⟩ := Nat.exists_last_of_le (p := Act) (a := τp) (b := max T₀ T₅)
    (by omega) (Or.inl hcallp)
  have hlast' : ∀ k, m < k → ¬ Act k := by
    intro k hk hAct
    by_cases hkB : k ≤ max T₀ T₅
    · exact hlast k hk hkB hAct
    · rcases hAct with h | ⟨c, h, -⟩
      · exact hstop k (by omega) h
      · exact hT₀ k (by omega) c h
  have hNE : NoEff e (m + 1) := fun k hk c hc => by
    by_contra h; exact hlast' k (by omega) (Or.inr ⟨c, hc, h⟩)
  have hcall : ∀ k, m + 1 ≤ k → ¬ IsCall e k := fun k hk h => hlast' k (by omega) (Or.inl h)
  have hNC₂ : NoCrash e T₂ := hNC.mono hT₂
  rcases hm with ⟨r, hr, ρ, hρ⟩ | ⟨c, hc, hcr⟩
  · exact last_call_false hinv hF hNE hNC₂ hsk hcall (fun t ht => hw t ht) hρ
  · apply no_pre hinv hF hNE hNC₂ hsk hcall (m + 1) le_rfl c
    rw [exec_succ, hc]
    simp [Cfg.next, Cfg.crash, hcr, Cfg.setPc, Pre]

/-! ### Per-section versions -/

lemma succ_enter {k k' : PC P} (h : Succ k k') (hk : k.IsEnter) : k'.IsEnter ∨ k' = .cs := by
  cases h <;> (try cases ‹Ret›) <;>
    simp_all [PC.IsEnter, PC.IsRecover, PC.IsExit, Ret.pc]

lemma succ_exit {k k' : PC P} (h : Succ k k') (hk : k.IsExit) : k'.IsExit ∨ k' = .rem := by
  cases h <;> (try cases ‹Ret›) <;> simp_all [PC.IsExit, Ret.pc]

/-- If `p` does not crash, its program counter either stays or follows the control flow. -/
lemma pc_evolve {e : ℕ → Ev P} {t : ℕ} {p : P} (hp : e t ≠ .crash p) :
    (exec e (t + 1)).pc p = (exec e t).pc p ∨ Succ ((exec e t).pc p) ((exec e (t + 1)).pc p) := by
  rw [exec_succ]
  cases he : e t with
  | step r =>
    by_cases hrp : r = p
    · subst hrp; exact Or.inr (succ_step _ r)
    · exact Or.inl (step_pc_ne _ (Ne.symm hrp))
  | crash c =>
    rcases crash_pc (exec e t) c p with h | ⟨rfl, -⟩
    · exact Or.inl h
    · exact absurd he hp

/-- The first time `≥ t` at which `p` is in the remainder or the critical section. -/
lemma first_rem_or_cs {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t)) (hF : Fair e)
    (hC : FinCrashes e) (p : P) (t : ℕ) :
    ∃ t', t ≤ t' ∧ ((exec e t').pc p = .rem ∨ (exec e t').pc p = .cs) ∧
      ∀ k, t ≤ k → k < t' → (exec e k).pc p ≠ .rem ∧ (exec e k).pc p ≠ .cs := by
  classical
  have hex := eventually_rem_or_cs_of_inv hinv hF hC p t
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk hk' => ?_⟩
  have := Nat.find_min hex hk'
  push Not at this
  exact this hk

/-- A process executing `Enter()` that does not crash any more enters the critical section. -/
theorem enter_reaches_cs_of_inv {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t))
    (hF : Fair e) (hC : FinCrashes e) {p : P} {t : ℕ} (hE : ((exec e t).pc p).IsEnter)
    (hp : ∀ t', t ≤ t' → e t' ≠ .crash p) : ∃ t', t ≤ t' ∧ (exec e t').pc p = .cs := by
  obtain ⟨t', ht', h1, h2⟩ := first_rem_or_cs hinv hF hC p t
  have hE' : ∀ k, t ≤ k → k ≤ t' → ((exec e k).pc p).IsEnter ∨ (exec e k).pc p = .cs := by
    intro k hk hk'
    induction k, hk using Nat.le_induction with
    | base => exact Or.inl hE
    | succ k hk ih =>
      have ih := (ih (by omega)).resolve_right (h2 k hk (by omega)).2
      rcases pc_evolve (hp k hk) with h | h
      · rw [h]; exact Or.inl ih
      · exact succ_enter h ih
  refine ⟨t', ht', h1.resolve_left fun h => ?_⟩
  rcases hE' t' ht' le_rfl with h' | h' <;> rw [h] at h'
  · exact h'.1 rfl
  · simp at h'

/-- A process executing `Exit()` that does not crash any more returns to the remainder
section. -/
theorem exit_reaches_rem_of_inv {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t))
    (hF : Fair e) (hC : FinCrashes e) {p : P} {t : ℕ} (hE : ((exec e t).pc p).IsExit)
    (hp : ∀ t', t ≤ t' → e t' ≠ .crash p) : ∃ t', t ≤ t' ∧ (exec e t').pc p = .rem := by
  obtain ⟨t', ht', h1, h2⟩ := first_rem_or_cs hinv hF hC p t
  have hE' : ∀ k, t ≤ k → k ≤ t' → ((exec e k).pc p).IsExit ∨ (exec e k).pc p = .rem := by
    intro k hk hk'
    induction k, hk using Nat.le_induction with
    | base => exact Or.inl hE
    | succ k hk ih =>
      have ih := (ih (by omega)).resolve_right (h2 k hk (by omega)).1
      rcases pc_evolve (hp k hk) with h | h
      · rw [h]; exact Or.inl ih
      · exact succ_exit h ih
  refine ⟨t', ht', h1.resolve_right fun h => ?_⟩
  rcases hE' t' ht' le_rfl with h' | h' <;> rw [h] at h'
  · exact h'
  · simp at h'

/-- A process executing `Recover()` eventually leaves it (to the critical section, or via
`Enter()`/`Exit()`). -/
theorem recover_terminates_of_inv {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t))
    (hF : Fair e) (hC : FinCrashes e) (p : P) (t : ℕ) :
    ∃ t', t ≤ t' ∧ ¬ ((exec e t').pc p).IsRecover := by
  obtain ⟨t', ht', h⟩ := eventually_rem_or_cs_of_inv hinv hF hC p t
  refine ⟨t', ht', ?_⟩
  rcases h with h | h <;> rw [h] <;> simp [PC.IsRecover]

end Live

end Podc.RecoverableMutexRMR
