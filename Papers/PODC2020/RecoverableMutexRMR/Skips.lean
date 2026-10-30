import Papers.PODC2020.RecoverableMutexRMR.Spec
import Papers.PODC2020.RecoverableMutexRMR.Invariant

/-!
# Skipped tickets are at most twice the number of crashes (Section 3.1, Lemma 2.10)

Section 3.1 of the paper: "the total number of skipped tickets is at most twice the number of
process crashes". Lemma 2.10: with finitely many crashes, only finitely many entries of `A` ever
contain `−1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

/-- Number of crashes among the first `t` events. Only crashes outside the remainder section
count: a crash in the remainder section has no effect (it does not start `Recover()`). -/
def numCrashes (e : ℕ → Ev P) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun u => ∃ p, e u = .crash p ∧ (exec e u).pc p ≠ .rem)).card

lemma ghost_ncr_le (e : ℕ → Ev P) (t : ℕ) : (ghost e t).ncr ≤ numCrashes e t := by
  induction t with
  | zero => simp [Ghost.init]
  | succ t ih =>
    have hsplit : numCrashes e (t + 1) =
        numCrashes e t + (if ∃ p, e t = .crash p ∧ (exec e t).pc p ≠ .rem then 1 else 0) := by
      unfold numCrashes
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    rw [hsplit, ghost_succ]
    cases he : e t with
    | crash p =>
      by_cases hp : (exec e t).pc p = .rem
      · have : ¬ (∃ q, Ev.crash p = Ev.crash q ∧ (exec e t).pc q ≠ .rem) := by
          rintro ⟨q, h, hq⟩; cases h; exact hq hp
        simp only [this, if_false, add_zero, Ghost.next, hp, if_true]; exact ih
      · have : (∃ q, Ev.crash p = Ev.crash q ∧ (exec e t).pc q ≠ .rem) := ⟨p, rfl, hp⟩
        simp only [this, if_true, Ghost.next, hp, if_false]; omega
    | step p =>
      have : ¬ (∃ q, Ev.step p = (Ev.crash q : Ev P) ∧ (exec e t).pc q ≠ .rem) := by
        rintro ⟨q, h, -⟩; cases h
      simp only [this, if_false, add_zero]
      have : ((ghost e t).next (exec e t) (.step p)).ncr = (ghost e t).ncr := by
        simp only [Ghost.next]; split <;> rfl
      omega

/-- **Skipped tickets vs crashes** (Section 3.1): at any time, the number of entries of `A`
containing `−1` is at most twice the number of crashes so far. -/
theorem skipped_le_two_mul_crashes (e : ℕ → Ev P) (t : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, (exec e t).A x = .skipped) : S.card ≤ 2 * numCrashes e t := by
  have hI := inv_exec e t
  have h1 : S.card ≤ nSkipped (exec e t) := by
    apply Finset.card_le_card
    intro x hx
    have hx' := hS x hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hI.A_ne x (by rw [hx']; simp)).2, hx'⟩
  have h2 := hI.psi_bound
  have h3 : 0 ≤ Psi (exec e t) (ghost e t) := by
    have := hI.phi_nonneg; unfold Psi; positivity
  have h4 := ghost_ncr_le e t
  have : (nSkipped (exec e t) : ℤ) ≤ 2 * (numCrashes e t : ℤ) := by
    have : ((ghost e t).ncr : ℤ) ≤ numCrashes e t := by exact_mod_cast h4
    have : (0 : ℤ) ≤ nR15 (exec e t) := by positivity
    linarith
  have : nSkipped (exec e t) ≤ 2 * numCrashes e t := by exact_mod_cast this
  omega

/-- Nonempty entries of `A` never change. -/
lemma next_A_of_ne_empty (s : Cfg P) (ev : Ev P) (x : ℕ) (h : s.A x ≠ .empty) :
    (s.next ev).A x = s.A x := by
  cases ev with
  | crash p => simp only [Cfg.next, Cfg.crash]; split_ifs <;> rfl
  | step p =>
    simp only [Cfg.next, Cfg.step]
    split <;> (try split_ifs) <;> simp [Cfg.setPc]
    all_goals (rw [Function.update_apply]; split_ifs <;> simp_all)

lemma exec_A_mono (e : ℕ → Ev P) (x : ℕ) {t t' : ℕ} (htt : t ≤ t')
    (h : (exec e t).A x ≠ .empty) : (exec e t').A x = (exec e t).A x := by
  induction t', htt using Nat.le_induction with
  | base => rfl
  | succ t' _ ih =>
    rw [exec_succ, next_A_of_ne_empty _ _ _ (by rw [ih]; exact h), ih]

lemma numCrashes_le_of_finCrashes (e : ℕ → Ev P) (T₀ : ℕ) (hT : ∀ t, T₀ ≤ t → ∀ p, e t ≠ .crash p)
    (t : ℕ) : numCrashes e t ≤ numCrashes e T₀ := by
  unfold numCrashes
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
  refine ⟨?_, hu.2⟩
  by_contra hlt
  obtain ⟨p, hp, -⟩ := hu.2
  exact hT u (by omega) p hp

/-- **Lemma 2.10.** With finitely many crashes, only finitely many entries of `A` ever contain
`−1`. -/
theorem lemma2_10 (e : ℕ → Ev P) (hC : FinCrashes e) :
    {x | ∃ t, (exec e t).A x = .skipped}.Finite := by
  obtain ⟨T₀, hT⟩ := hC
  by_contra hinf
  obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * numCrashes e T₀ + 1)
  choose! tx htx using fun x (hx : x ∈ S) => hSsub hx
  set t := S.sup tx
  have hall : ∀ x ∈ S, (exec e t).A x = .skipped := by
    intro x hx
    rw [exec_A_mono e x (Finset.le_sup hx) (by rw [htx x hx]; simp), htx x hx]
  have := skipped_le_two_mul_crashes e t S hall
  have := numCrashes_le_of_finCrashes e T₀ hT t
  omega

/-- `C`, `D` and `Token` never decrease in one event. -/
lemma next_mono (s : Cfg P) (ev : Ev P) :
    s.C ≤ (s.next ev).C ∧ s.D ≤ (s.next ev).D ∧ s.T ≤ (s.next ev).T := by
  cases ev with
  | crash p => simp only [Cfg.next, Cfg.crash]; split_ifs <;> simp [Cfg.setPc]
  | step p =>
    simp only [Cfg.next, Cfg.step]
    split <;> (try split_ifs) <;> simp [Cfg.setPc] <;> omega

/-- **Lemma 2.1 (3).** `C`, `D` and `Token` are monotonically non-decreasing. -/
theorem lemma2_1_3 (e : ℕ → Ev P) {t t' : ℕ} (h : t ≤ t') :
    (exec e t).C ≤ (exec e t').C ∧ (exec e t).D ≤ (exec e t').D ∧
      (exec e t).T ≤ (exec e t').T := by
  induction t', h using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl, le_rfl⟩
  | succ t' _ ih =>
    have := next_mono (exec e t') (e t')
    rw [exec_succ]; omega

/-- **Lemma 2.1 (10).** An entry of `A` cannot be modified after it is set to a non-zero value. -/
theorem lemma2_1_10 (e : ℕ → Ev P) (x : ℕ) {t t' : ℕ} (h : t ≤ t')
    (hx : (exec e t).A x ≠ .empty) : (exec e t').A x = (exec e t).A x :=
  exec_A_mono e x h hx

end Podc.RecoverableMutexRMR
