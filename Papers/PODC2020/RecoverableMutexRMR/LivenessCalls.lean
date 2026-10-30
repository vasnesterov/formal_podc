import Papers.PODC2020.RecoverableMutexRMR.LivenessTrace

/-!
# Liveness, part 4: Token stabilizes, calls of `Move_Token()` stop

Under the hypothesis that some process `p` waits at line 31 forever:

* `w31_bound`: `Token < w ≤ C` (with `w` the ticket of `p`), so `Token` eventually is constant;
* `no_cs`: if `Token` is constant, nobody is in the critical section (the owner of the next
  ticket would move `Token` when leaving, `progress`);
* `calls_stop`: then only finitely many calls of `Move_Token()` happen (call potential `cp`);
* `exists_call`: `p` called `Move_Token()` before waiting at line 31.
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

namespace Live

/-- A call of `Move_Token()` (a step into line 34) happens at time `t`. -/
def IsCall (e : ℕ → Ev P) (t : ℕ) : Prop := ∃ r, e t = .step r ∧ IsM34 ((exec e (t + 1)).pc r)

lemma crash_pc (s : Cfg P) (c p : P) :
    (s.crash c).pc p = s.pc p ∨ (c = p ∧ (s.crash c).pc p = .r15) := by
  unfold Cfg.crash
  split_ifs
  · exact Or.inl rfl
  · by_cases h : c = p
    · subst h; right; simp [Cfg.setPc]
    · left; simp [Cfg.setPc, Function.update_of_ne (Ne.symm h)]

variable {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t))
include hinv

/-- A process waiting at line 31 holds a ticket beyond `Token`. -/
lemma w31_bound {t w : ℕ} {p : P} (h : (exec e t).pc p = .w31 w) :
    (exec e t).T < w ∧ w ≤ (exec e t).C := by
  have hl := (hinv t).loc p
  rw [LI, h] at hl
  obtain ⟨-, hW, -, hA⟩ := hl
  refine ⟨?_, (( hinv t).A_ne w (by simp [hA])).2⟩
  by_contra hle
  exact (hinv t).done w p (by omega) hA hW

/-- If `Token` is constant from `s` on, nobody is in the critical section from `s` on. -/
lemma no_cs (hF : Fair e) {s L : ℕ} (hNC : NoCrash e s) (hT : ∀ t, s ≤ t → (exec e t).T = L) :
    ∀ t, s ≤ t → ∀ q, (exec e t).pc q ≠ .cs := by
  intro t ht q hq
  have hl := (hinv t).loc q
  rw [LI, hq] at hl
  have hg := (hinv t).grant q hl.2
  rw [hT t ht] at hg
  exact progress hinv hF (hNC.mono ht) (fun t' ht' => hT t' (by omega)) hg.2 (Or.inl hq)

/-- If `Token` is constant and nobody is in the critical section, calls of `Move_Token()`
eventually stop. -/
lemma calls_stop {s L : ℕ} (hNC : NoCrash e s) (hT : ∀ t, s ≤ t → (exec e t).T = L)
    (hcs : ∀ t, s ≤ t → ∀ q, (exec e t).pc q ≠ .cs) :
    ∃ T₅, s ≤ T₅ ∧ ∀ t, T₅ ≤ t → ¬ IsCall e t := by
  have hq : ∀ q, ∃ T, s ≤ T ∧ ∀ t, T ≤ t →
      ¬ (e t = .step q ∧ IsM34 ((exec e (t + 1)).pc q)) := by
    intro q
    have key : ∀ t, s ≤ t → cp ((exec e (t + 1)).pc q) ≤ cp ((exec e t).pc q) ∧
        (e t = .step q ∧ IsM34 ((exec e (t + 1)).pc q) →
          cp ((exec e (t + 1)).pc q) < cp ((exec e t).pc q)) := by
      intro t ht
      obtain ⟨r, hr⟩ := hNC.step ht
      by_cases hrq : r = q
      · subst hrq
        have hcs' := hcs (t + 1) (by omega) r
        rw [exec_step hr] at hcs' ⊢
        have := cp_succ (succ_step _ r) hcs' (fun hb => by
          have h1 := step_T_of_back _ r hb
          have h2 := hT t ht; have h3 := hT (t + 1) (by omega)
          rw [exec_step hr] at h3; omega)
        exact ⟨this.1, fun h => this.2 h.2⟩
      · rw [pc_frame hr hrq]
        exact ⟨le_rfl, fun h => absurd (h.1 ▸ hr).symm (by simp [hrq])⟩
    exact Nat.eventually_not_of_succ_le (f := fun t => cp ((exec e t).pc q)) (N := s)
      (fun t ht => (key t ht).1) (fun t ht => (key t ht).2)
  choose T hTs hTq using hq
  refine ⟨s + ∑ q, T q, by omega, fun t ht ⟨r, hr, hm⟩ => hTq r t ?_ ⟨hr, hm⟩⟩
  have := Finset.single_le_sum (f := T) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  omega

/-- A process waiting at line 31 has called `Move_Token()` before. -/
lemma exists_call {T₄ w : ℕ} {p : P} (h : (exec e T₄).pc p = .w31 w) :
    ∃ τ, τ < T₄ ∧ IsCall e τ := by
  obtain ⟨m, hm, h1, h2⟩ := Nat.exists_lt_and_not_succ_of_not
    (p := fun t => ¬ MW ((exec e t).pc p)) (K := T₄) (by simp [Cfg.init, MW])
    (by simp only [not_not, h]; simp [MW])
  simp only [not_not] at h2
  refine ⟨m, hm, ?_⟩
  rw [exec_succ] at h2
  cases he : e m with
  | crash c =>
    rw [he] at h2
    rcases crash_pc (exec e m) c p with h' | ⟨_, h'⟩ <;> simp only [Cfg.next] at h2 <;>
      rw [h'] at h2
    · exact absurd h2 h1
    · simp [MW] at h2
  | step r =>
    rw [he] at h2
    simp only [Cfg.next] at h2
    by_cases hrp : r = p
    · subst hrp
      exact ⟨r, he, by rw [exec_step he]; exact mw_entry _ r h1 h2⟩
    · rw [step_pc_ne _ (Ne.symm hrp)] at h2
      exact absurd h2 h1

end Live

end Podc.RecoverableMutexRMR
