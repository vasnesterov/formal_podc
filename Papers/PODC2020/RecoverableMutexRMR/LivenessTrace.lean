import Papers.PODC2020.RecoverableMutexRMR.LivenessMeasure
import Cslib.Foundations.Data.Nat.Descent

/-!
# Liveness, part 3: facts along executions

All statements take the invariant along the execution as a hypothesis
`hinv : ∀ t, Inv (exec e t) (ghost e t)` (it is discharged by `inv_exec` in `Liveness.lean`).

* `exists_no_new_skip`: after the last crash, eventually no ticket is skipped any more (the
  number of skipped tickets is non-decreasing and at most twice the number of crashes, by the
  potential `Ψ` of the invariant).
* `stuck`: a process that stays outside the remainder section, does not crash, and does not
  enter the critical section from line 31, while no ticket is skipped, is eventually stuck at
  line 31 forever (lexicographic measure of `LivenessMeasure.lean`).
* `progress`: if `Token = L` forever, then the owner `q` of a claimed ticket `L + 1` that has
  left the waiting room (or is about to) moves `Token` — a contradiction.
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

namespace Live

/-- No crash event from time `s` on. -/
def NoCrash (e : ℕ → Ev P) (s : ℕ) : Prop := ∀ t, s ≤ t → ∀ p, e t ≠ .crash p

lemma NoCrash.mono {e : ℕ → Ev P} {s s' : ℕ} (h : NoCrash e s) (hs : s ≤ s') : NoCrash e s' :=
  fun t ht => h t (by omega)

lemma NoCrash.step {e : ℕ → Ev P} {s t : ℕ} (h : NoCrash e s) (ht : s ≤ t) :
    ∃ r, e t = .step r := by
  cases he : e t with
  | step r => exact ⟨r, rfl⟩
  | crash p => exact absurd he (h t ht p)

lemma exec_step {e : ℕ → Ev P} {t : ℕ} {r : P} (h : e t = .step r) :
    exec e (t + 1) = (exec e t).step r := by simp [h, Cfg.next]

lemma ghost_step {e : ℕ → Ev P} {t : ℕ} {r : P} (h : e t = .step r) :
    ghost e (t + 1) = (ghost e t).next (exec e t) (.step r) := by simp [h]

/-- The program counter of `q` changes only by steps of `q` (no crash). -/
lemma pc_frame {e : ℕ → Ev P} {t : ℕ} {r q : P} (h : e t = .step r) (hrq : r ≠ q) :
    (exec e (t + 1)).pc q = (exec e t).pc q := by
  rw [exec_step h]; exact step_pc_ne _ (Ne.symm hrq)

/-- Between two steps of `q`, its program counter is constant. -/
lemma pc_const_until {e : ℕ → Ev P} {s τ τ' : ℕ} {q : P} (hNC : NoCrash e s) (hτ : s ≤ τ)
    (hno : ∀ t, τ ≤ t → t < τ' → e t ≠ .step q) :
    ∀ t, τ ≤ t → t ≤ τ' → (exec e t).pc q = (exec e τ).pc q := by
  intro t h1 h2
  induction t, h1 using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    obtain ⟨r, hr⟩ := hNC.step (show s ≤ t by omega)
    have hrq : r ≠ q := fun h => hno t ht (by omega) (h ▸ hr)
    rw [pc_frame hr hrq, ih (by omega)]

/-- Fairness: a process outside the remainder section takes its next step, and its program
counter does not change until then. -/
lemma follow {e : ℕ → Ev P} (hF : Fair e) {s τ : ℕ} {q : P} (hNC : NoCrash e s) (hτ : s ≤ τ)
    (hq : (exec e τ).pc q ≠ .rem) :
    ∃ τ', τ ≤ τ' ∧ e τ' = .step q ∧ (exec e τ').pc q = (exec e τ).pc q ∧
      ∀ t, τ ≤ t → t ≤ τ' → (exec e t).pc q = (exec e τ).pc q := by
  classical
  have hex := hF q τ hq
  let τ' := Nat.find hex
  have hτ' : τ ≤ τ' ∧ e τ' = .step q := Nat.find_spec hex
  have hno : ∀ t, τ ≤ t → t < τ' → e t ≠ .step q := fun t h1 h2 h3 =>
    Nat.find_min hex h2 ⟨h1, h3⟩
  have hc := pc_const_until hNC hτ hno
  exact ⟨τ', hτ'.1, hτ'.2, hc τ' hτ'.1 le_rfl, hc⟩

/-- A rank that never increases and strictly decreases at every step of `q` contradicts
fairness, if `q` stays outside the remainder section. -/
lemma descent_false {e : ℕ → Ev P} (hF : Fair e) {s : ℕ} {q : P} (f : ℕ → ℕ)
    (hq : ∀ t, s ≤ t → (exec e t).pc q ≠ .rem) (hle : ∀ t, s ≤ t → f (t + 1) ≤ f t)
    (hlt : ∀ t, s ≤ t → e t = .step q → f (t + 1) < f t) : False := by
  obtain ⟨T, hT, hc⟩ := Nat.eventually_const_of_succ_le (f := f) (N := s) hle
  obtain ⟨t, ht, he⟩ := hF q T (hq T hT)
  have := hlt t (by omega) he
  rw [hc t ht, hc (t + 1) (by omega)] at this
  exact lt_irrefl _ this

/-! ### Monotone quantities -/

lemma next_T_le (s : Cfg P) (ev : Ev P) : s.T ≤ (s.next ev).T := by
  cases ev with
  | step r => exact T_le_step s r
  | crash p => simp only [Cfg.next, Cfg.crash]; split_ifs <;> simp [Cfg.setPc]

lemma next_C_le (s : Cfg P) (ev : Ev P) : s.C ≤ (s.next ev).C := by
  cases ev with
  | step r => exact C_le_step s r
  | crash p => simp only [Cfg.next, Cfg.crash]; split_ifs <;> simp [Cfg.setPc]

lemma next_A (s : Cfg P) (ev : Ev P) (x : ℕ) (h : s.A x ≠ .empty) : (s.next ev).A x = s.A x := by
  cases ev with
  | step r =>
    rcases step_A s r x with h' | h' <;> simp_all [Cfg.next]
  | crash p => simp only [Cfg.next, Cfg.crash]; split_ifs <;> simp [Cfg.setPc]

lemma T_mono (e : ℕ → Ev P) {t t' : ℕ} (h : t ≤ t') : (exec e t).T ≤ (exec e t').T := by
  induction t', h using Nat.le_induction with
  | base => rfl
  | succ t' _ ih => exact ih.trans (by rw [exec_succ]; exact next_T_le _ _)

lemma C_mono (e : ℕ → Ev P) {t t' : ℕ} (h : t ≤ t') : (exec e t).C ≤ (exec e t').C := by
  induction t', h using Nat.le_induction with
  | base => rfl
  | succ t' _ ih => exact ih.trans (by rw [exec_succ]; exact next_C_le _ _)

/-- Non-empty entries of `A` are permanent. -/
lemma A_perm (e : ℕ → Ev P) {t t' : ℕ} (h : t ≤ t') {x : ℕ} (hx : (exec e t).A x ≠ .empty) :
    (exec e t').A x = (exec e t).A x := by
  induction t', h using Nat.le_induction with
  | base => rfl
  | succ t' _ ih => rw [exec_succ, next_A _ _ _ (by rw [ih]; exact hx), ih]

/-! ### Skipped tickets -/

lemma nSkipped_step {s : Cfg P} {g : Ghost P} {r : P}
    (hI' : Inv (s.step r) (g.next s (.step r))) :
    nSkipped s ≤ nSkipped (s.step r) ∧
      ((∃ x, (s.step r).A x = .skipped ∧ s.A x ≠ .skipped) →
        nSkipped s < nSkipped (s.step r)) := by
  have hsub : (Finset.range (s.C + 1)).filter (fun x => s.A x = .skipped) ⊆
      (Finset.range ((s.step r).C + 1)).filter (fun x => (s.step r).A x = .skipped) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    have := C_le_step s r
    have hA : (s.step r).A x = s.A x := next_A s (.step r) x (by rw [hx.2]; simp)
    exact ⟨by omega, by rw [hA]; exact hx.2⟩
  refine ⟨Finset.card_le_card hsub, fun ⟨x, hx1, hx2⟩ => Finset.card_lt_card ⟨hsub, ?_⟩⟩
  intro h
  have hmem : x ∈ (Finset.range ((s.step r).C + 1)).filter
      (fun x => (s.step r).A x = .skipped) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := (hI'.A_ne x (by rw [hx1]; simp)).2; omega, hx1⟩
  have := h hmem
  simp only [Finset.mem_filter] at this
  exact hx2 this.2

lemma nSkipped_le_ncr {s : Cfg P} {g : Ghost P} (hI : Inv s g) : nSkipped s ≤ 2 * g.ncr := by
  have h1 := hI.psi_bound
  have h2 := hI.phi_nonneg
  unfold Psi at h1
  have : (0 : ℤ) ≤ crCount s g := by positivity
  have : (0 : ℤ) ≤ lostCount s g := by positivity
  have : (0 : ℤ) ≤ nR15 s := by positivity
  omega

lemma ncr_step (g : Ghost P) (s : Cfg P) (r : P) : (g.next s (.step r)).ncr = g.ncr := by
  simp only [Ghost.next]; split <;> rfl

variable {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t))
include hinv

/-- After the last crash, eventually no ticket gets skipped. -/
lemma exists_no_new_skip {T₀ : ℕ} (hNC : NoCrash e T₀) :
    ∃ T₂, T₀ ≤ T₂ ∧ ∀ t, T₂ ≤ t → ∀ x,
      (exec e (t + 1)).A x = .skipped → (exec e t).A x = .skipped := by
  have hncr : ∀ t, T₀ ≤ t → (ghost e t).ncr = (ghost e T₀).ncr := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih =>
      obtain ⟨r, hr⟩ := hNC.step ht
      rw [ghost_step hr, ncr_step, ih]
  have hmono : ∀ t, T₀ ≤ t → nSkipped (exec e t) ≤ nSkipped (exec e (t + 1)) := by
    intro t ht
    obtain ⟨r, hr⟩ := hNC.step ht
    have := hinv (t + 1); rw [exec_step hr, ghost_step hr] at this
    rw [exec_step hr]; exact (nSkipped_step this).1
  obtain ⟨T₂, hT₂, hc⟩ := Nat.eventually_const_of_le_succ (f := fun t => nSkipped (exec e t))
    (N := T₀) (B := 2 * (ghost e T₀).ncr)
    (fun t ht => by rw [← hncr t ht]; exact nSkipped_le_ncr (hinv t)) hmono
  refine ⟨T₂, hT₂, fun t ht x hx => ?_⟩
  by_contra hx'
  obtain ⟨r, hr⟩ := hNC.step (show T₀ ≤ t by omega)
  have hI' := hinv (t + 1); rw [exec_step hr, ghost_step hr] at hI'
  rw [exec_step hr] at hx
  have := (nSkipped_step hI').2 ⟨x, hx, hx'⟩
  have h1 := hc t ht; have h2 := hc (t + 1) (by omega)
  rw [exec_step hr] at h2
  omega

/-- A process that stays outside the remainder section and does not enter the critical section
from line 31, while no ticket gets skipped and nobody crashes, is eventually stuck at line 31. -/
lemma stuck (hF : Fair e) {s₀ : ℕ} {q : P} (hNC : NoCrash e s₀)
    (hsk : ∀ t, s₀ ≤ t → ∀ x, (exec e (t + 1)).A x = .skipped → (exec e t).A x = .skipped)
    (hq : ∀ t, s₀ ≤ t → (exec e t).pc q ≠ .rem)
    (hcs : ∀ t, s₀ ≤ t → (exec e (t + 1)).pc q = .cs → ∀ w, (exec e t).pc q ≠ .w31 w) :
    ∃ T, s₀ ≤ T ∧ ∃ w, ∀ t, T ≤ t → (exec e t).pc q = .w31 w := by
  have hsk' : ∀ t, s₀ ≤ t → ∀ r, e t = .step r →
      ∀ x, ((exec e t).step r).A x = .skipped → (exec e t).A x = .skipped :=
    fun t ht r hr => by rw [← exec_step hr]; exact hsk t ht
  have hcs' : ∀ t, s₀ ≤ t → ∀ r, e t = .step r →
      ((exec e t).step r).pc q = .cs → ∀ w, (exec e t).pc q ≠ .w31 w :=
    fun t ht r hr => by rw [← exec_step hr]; exact hcs t ht
  obtain ⟨T₁, hT₁, hc₁⟩ := Nat.eventually_const_of_succ_le
    (f := fun t => sNum (exec e t) (ghost e t) q) (N := s₀) (fun t ht => by
      obtain ⟨r, hr⟩ := hNC.step ht
      show sNum (exec e (t + 1)) (ghost e (t + 1)) q ≤ _
      rw [exec_step hr, ghost_step hr]
      exact sNum_step (hinv t) (hsk' t ht r hr))
  obtain ⟨T₂, hT₂, hc₂⟩ := Nat.eventually_const_of_succ_le
    (f := fun t => Kb (exec e t) q) (N := s₀) (fun t ht => by
      obtain ⟨r, hr⟩ := hNC.step ht
      show Kb (exec e (t + 1)) q ≤ _
      rw [exec_step hr]
      exact Kb_step (hinv t) (hsk' t ht r hr) (hcs' t ht r hr))
  have hR : ∀ t, max T₁ T₂ ≤ t → ∃ r, e t = .step r ∧
      rnk (exec e (t + 1)) (ghost e (t + 1)) q ≤ rnk (exec e t) (ghost e t) q ∧
      (r = q → (exec e (t + 1)).pc q ≠ (exec e t).pc q →
        rnk (exec e (t + 1)) (ghost e (t + 1)) q < rnk (exec e t) (ghost e t) q) := by
    intro t ht
    obtain ⟨r, hr⟩ := hNC.step (show s₀ ≤ t by omega)
    have hS := (hc₁ (t + 1) (by omega)).trans (hc₁ t (by omega)).symm
    have hK := (hc₂ (t + 1) (by omega)).trans (hc₂ t (by omega)).symm
    rw [exec_step hr, ghost_step hr] at hS ⊢
    rw [exec_step hr] at hK
    have hI' := hinv (t + 1); rw [exec_step hr, ghost_step hr] at hI'
    have hq' := hq (t + 1) (by omega); rw [exec_step hr] at hq'
    exact ⟨r, hr, rnk_step (hinv t) hI' (hsk' t (by omega) r hr) (hcs' t (by omega) r hr)
      (hq t (by omega)) hq' hS hK⟩
  obtain ⟨T₃, hT₃, hc₃⟩ := Nat.eventually_const_of_succ_le
    (f := fun t => rnk (exec e t) (ghost e t) q) (N := max T₁ T₂)
    (fun t ht => by obtain ⟨r, -, h, -⟩ := hR t ht; exact h)
  have hpc : ∀ t, T₃ ≤ t → (exec e (t + 1)).pc q = (exec e t).pc q := by
    intro t ht
    obtain ⟨r, hr, -, h⟩ := hR t (by omega)
    by_cases hrq : r = q
    · by_contra hne
      have := h hrq hne
      have h1 := hc₃ t ht; have h2 := hc₃ (t + 1) (by omega)
      omega
    · exact pc_frame hr hrq
  have hconst : ∀ t, T₃ ≤ t → (exec e t).pc q = (exec e T₃).pc q := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [hpc t ht, ih]
  obtain ⟨t, ht, he⟩ := hF q T₃ (hq T₃ (by omega))
  have h1 := hpc t ht
  rw [exec_step he] at h1
  obtain ⟨w, hw, -⟩ := spin _ q h1
  refine ⟨T₃, by omega, w, fun t' ht' => ?_⟩
  rw [hconst t' ht', ← hconst t ht, hw]

end Live

/-! ### Progress of the owner of ticket `Token + 1` -/

namespace Live

/-- `q` owns ticket `L + 1` and has left the waiting room for good (or is in the critical
section). -/
def Good (s : Cfg P) (L : ℕ) (q : P) : Prop :=
  s.pc q = .cs ∨ s.pc q = .x9 ∨ s.pc q = .x10 ∨ (s.W q).1 ≠ L + 1

lemma good_step {s : Cfg P} {g : Ghost P} {L : ℕ} {q : P} (r : P) (hI : Inv s g)
    (hA : s.A (L + 1) = .claimed q) (h : Good s L q) : Good (s.step r) L q := by
  unfold Good at h ⊢
  by_cases hrq : r = q
  · subst hrq
    rcases h with h | h | h | h
    · simp [Cfg.step, h, Cfg.setPc]
    · simp [Cfg.step, h]
    · simp [Cfg.step, h]
    · right; right; right
      rcases step_W s r r with hW | ⟨_, ⟨c, hc⟩ | hc | hc⟩ | ⟨ρ, ℓ, _, h1, h2⟩
      · rwa [hW]
      · have hl := hI.loc r; rw [LI, hc] at hl
        have hW : (s.step r).W r = (c, false) := by simp [Cfg.step, hc, hl.2.1]
        rw [hW]; simp only
        rintro rfl
        rcases hl.2.2.2.2 with h' | h' <;> simp_all
      · simp [Cfg.step, hc]
      · simp [Cfg.step, hc]
      · rw [h2]; rw [h1] at h; exact h
  · rw [step_pc_ne s (Ne.symm hrq), W_fst_step_ne hrq]; exact h

lemma good_OT {s : Cfg P} {g : Ghost P} {L : ℕ} {q : P} (hI : Inv s g)
    (hA : s.A (L + 1) = .claimed q) (hT : s.T = L) (h : Good s L q) : OTpc L q (s.pc q) := by
  rcases h with h | h | h | h
  · rw [h]; simp [OTpc]
  · rw [h]; simp [OTpc]
  · rw [h]; simp [OTpc]
  · rcases hI.future q (L + 1) hA (by omega) with h' | ⟨_, _, _, h'⟩
    · exact absurd h' h
    · have := (OT_iff s q).1 (Or.inr (Or.inr (Or.inr h'))); rwa [hT] at this

lemma OTpc_ne_rem {L : ℕ} {q : P} {k : PC P} (h : OTpc L q k) : k ≠ .rem := by
  rintro rfl; simp [OTpc] at h

end Live

namespace Live

variable {e : ℕ → Ev P} (hinv : ∀ t, Inv (exec e t) (ghost e t))
include hinv

/-- If `Token = L` from `s₀` on, the owner `q` of ticket `L + 1` cannot be in the critical
section or on its way out (it would move `Token`). -/
lemma progress (hF : Fair e) {s₀ L : ℕ} {q : P} (hNC : NoCrash e s₀)
    (hT : ∀ t, s₀ ≤ t → (exec e t).T = L) (hA : (exec e s₀).A (L + 1) = .claimed q)
    (hG : Good (exec e s₀) L q) : False := by
  have hA' : ∀ t, s₀ ≤ t → (exec e t).A (L + 1) = .claimed q := fun t ht => by
    rw [A_perm e ht (by rw [hA]; simp), hA]
  have hG' : ∀ t, s₀ ≤ t → Good (exec e t) L q := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hG
    | succ t ht ih =>
      obtain ⟨r, hr⟩ := hNC.step ht
      rw [exec_step hr]; exact good_step r (hinv t) (hA' t ht) ih
  have hOT : ∀ t, s₀ ≤ t → OTpc L q ((exec e t).pc q) := fun t ht =>
    good_OT (hinv t) (hA' t ht) (hT t ht) (hG' t ht)
  have key : ∀ t, s₀ ≤ t → rk0 ((exec e (t + 1)).pc q) ≤ rk0 ((exec e t).pc q) ∧
      (e t = .step q → rk0 ((exec e (t + 1)).pc q) < rk0 ((exec e t).pc q)) := by
    intro t ht
    obtain ⟨r, hr⟩ := hNC.step ht
    by_cases hrq : r = q
    · subst hrq
      have h2 := hOT (t + 1) (by omega)
      have hT2 := hT (t + 1) (by omega)
      rw [exec_step hr] at h2 hT2 ⊢
      have hlt := rk0_succ (succ_step _ r) (hOT t ht) h2 (fun hb => by
        have := step_T_of_back _ r hb; have := hT t ht; omega)
      exact ⟨hlt.le, fun _ => hlt⟩
    · rw [pc_frame hr hrq]
      exact ⟨le_rfl, fun h => absurd (h ▸ hr).symm (by simp [hrq])⟩
  exact descent_false hF (fun t => rk0 ((exec e t).pc q))
    (fun t ht => OTpc_ne_rem (hOT t ht)) (fun t ht => (key t ht).1) (fun t ht => (key t ht).2)

end Live

end Podc.RecoverableMutexRMR
