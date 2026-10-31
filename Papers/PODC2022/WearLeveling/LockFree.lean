import Papers.PODC2022.WearLeveling.Counter

/-!
# Theorem 4.2: the counter of Figure 1 is lock-free

Proof (following the paper's sketch): suppose that after some time there are no crashes and no
responses, but running threads keep taking steps.

1. After a successful CAS a thread is at line 6 or 7 until it responds; so after the last
   response every thread performs at most one successful CAS. With finitely many threads, there
   is a suffix without successful CAS, in which the cache is constant (`c`).
2. With a constant cache, the potential `Φ = Σ_p φ_c(p)` strictly decreases at every step of a
   running thread (`μ`): a thread either reaches `CAS(A[k-1], c[k-1], …)` with
   `iter = c[k-1]` read at line 1/12, which succeeds, or fails at most `k` times with a stale
   `iter` and then rereads `A[k-1]`. A contradiction.

The argument does not depend on persistent memory, so lock-freedom holds in every wear model.
The paper's proof needs finitely many threads (step 1), which we assume (`Finite P`).
-/

namespace Podc.WearLeveling

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.Persistent Alg

variable {k : ℕ} [NeZero k] {P : Type} [DecidableEq P]

/-- Steps-to-go measure of a local state when the cache is constantly `c`. -/
def μcas (c : Fin k → ℕ) (it : ℕ) (idx : Fin k) : ℕ :=
  (if it = c (last k) then 0 else 2 * k + 4) + 2 * (k - 1 - idx.val) + 2

/-- Steps-to-go measure of a local state when the cache is constantly `c`. -/
def μ (c : Fin k → ℕ) : CL k → ℕ
  | .rd => 2 * k + 2
  | .fl it => μcas c it 0 + 1
  | .cas it idx => μcas c it idx
  | .flF it idx => if h : idx.val + 1 < k then μcas c it ⟨idx.val + 1, h⟩ + 1 else 2 * k + 3
  | .flS _ _ => 2
  | .ret _ _ => 1

/-- Potential of a thread. -/
def φ (c : Fin k → ℕ) : TS Unit (CL k) → ℕ
  | .idle => 2 * k + 3
  | .run _ _ l => μ c l

lemma μ_rd_lt (c : Fin k → ℕ) : μ c (CL.rd) < 2 * k + 3 := by simp [μ]

/-- A step of a running thread that neither succeeds a CAS nor returns decreases `μ` and leaves
the cache unchanged. -/
lemma step_run_dec (W : Wear k ℕ) (C : Cfg (counter k) P) {p : P} {a : ℕ} {o : Unit}
    {l : CL k} (hp : C.ts p = .run a o l)
    (hcas : ∀ it idx, l = .cas it idx → C.cache idx ≠ it) (hret : ∀ it idx, l ≠ .ret it idx) :
    ∃ l' : CL k, (step1 W C (.step p)).1.ts = Function.update C.ts p (.run a o l') ∧
      μ C.cache l' < μ C.cache l ∧ (step1 W C (.step p)).1.cache = C.cache ∧
      (step1 W C (.step p)).2 = [] := by
  have hk := k_pos k
  cases l with
  | rd =>
    refine ⟨.fl (C.cache (last k)), by simp [step1, hp, counter], ?_, by simp [step1, hp, counter],
      by simp [step1, hp, counter]⟩
    simp only [μ, μcas, ite_eq_left rfl]
    simp; omega
  | fl it =>
    refine ⟨.cas it 0, by simp [step1, hp, counter], by simp [μ],
      by simp [step1, hp, counter]; exact writeBack_cache W C _, by simp [step1, hp, counter]⟩
  | cas it idx =>
    have hc := hcas it idx rfl
    refine ⟨.flF it idx, by simp [step1, hp, counter, hc], ?_, by simp [step1, hp, counter, hc],
      by simp [step1, hp, counter, hc]⟩
    simp only [μ]
    split_ifs with h1
    · simp only [μcas]; split_ifs <;> simp <;> omega
    · have hidx : idx = last k := Fin.ext (by simp; omega)
      subst hidx
      simp only [μcas]
      split_ifs with h2
      · exact absurd h2.symm hc
      · omega
  | flS it idx =>
    refine ⟨.ret it idx, by simp [step1, hp, counter], by simp [μ],
      by simp [step1, hp, counter]; exact writeBack_cache W C _, by simp [step1, hp, counter]⟩
  | ret it idx => exact absurd rfl (hret it idx)
  | flF it idx =>
    refine ⟨nextPC it idx, by simp [step1, hp, counter], ?_,
      by simp [step1, hp, counter]; exact writeBack_cache W C _, by simp [step1, hp, counter]⟩
    by_cases h1 : idx.val + 1 < k
    · rw [nextPC_of_lt k h1]; simp [μ, h1]
    · rw [nextPC_of_not_lt k h1]; simp [μ, h1]

/-- A thread that has performed its successful CAS (lines 6–7). -/
def Done : TS Unit (CL k) → Prop
  | .run _ _ (.flS _ _) => True
  | .run _ _ (.ret _ _) => True
  | _ => False

/-- Thread `p` is about to perform a successful CAS. -/
def SuccCAS (C : Cfg (counter k) P) (p : P) : Prop :=
  ∃ a o it idx, C.ts p = .run a o (CL.cas it idx) ∧ C.cache idx = it

lemma ret_output (W : Wear k ℕ) {C : Cfg (counter k) P} {p : P} {a : ℕ} {o : Unit} {it : ℕ}
    {idx : Fin k} (hp : C.ts p = .run a o (CL.ret it idx)) :
    (step1 W C (.step p)).2 = [.res a (idx.val + it * k)] := by
  simp [step1, hp, counter]

/-- Without crashes and responses, a successful CAS leads to `Done`, and `Done` persists. -/
lemma done_step (W : Wear k ℕ) (C : Cfg (counter k) P) (ev : Ev k P Unit)
    (hcr : ev ≠ .crash) (hno : ∀ a r, (step1 W C ev).2 ≠ [.res a r]) (q : P) :
    (ev = .step q → SuccCAS C q → Done ((step1 W C ev).1.ts q)) ∧
    (Done (C.ts q) → Done ((step1 W C ev).1.ts q)) := by
  constructor
  · rintro rfl ⟨a, o, it, idx, hp, hc⟩
    simp [step1, hp, counter, hc, Done]
  · intro hd
    cases ev with
    | crash => exact absurd rfl hcr
    | evict i => simpa [step1, writeBack_ts] using hd
    | inv p o =>
      cases hp : C.ts p with
      | run => simpa [step1, hp] using hd
      | idle =>
        have hpq : q ≠ p := by rintro rfl; rw [hp] at hd; exact hd
        simpa [step1, hp, Function.update_of_ne hpq] using hd
    | step p =>
      by_cases hpq : q = p
      · subst hpq
        cases hq : C.ts q with
        | idle => rw [hq] at hd; exact hd.elim
        | run a o l =>
          rw [hq] at hd
          cases l with
          | flS it idx => simp [step1, hq, counter, Done]
          | ret it idx => exact absurd (ret_output W hq) (hno _ _)
          | _ => exact hd.elim
      · cases hp : C.ts p with
        | idle => simpa [step1, hp] using hd
        | run a o l =>
          have key : (step1 W C (.step p)).1.ts q = C.ts q := by
            cases l with
            | cas it idx =>
              by_cases hc : C.cache idx = it
              · simp [step1, hp, counter, hc, Function.update_of_ne hpq]
              · simp [step1, hp, counter, hc, Function.update_of_ne hpq]
            | _ => simp [step1, hp, counter, Function.update_of_ne hpq]
          rw [key]; exact hd

/-- Without crashes, responses and successful CASes, the cache is unchanged and the potential of
every thread does not increase; it strictly decreases for a running thread that steps. -/
lemma phi_step (W : Wear k ℕ) (C : Cfg (counter k) P) (ev : Ev k P Unit)
    (hcr : ev ≠ .crash) (hno : ∀ a r, (step1 W C ev).2 ≠ [.res a r])
    (hns : ∀ p, ev = .step p → ¬ SuccCAS C p) :
    (step1 W C ev).1.cache = C.cache ∧
    (∀ q, φ C.cache ((step1 W C ev).1.ts q) ≤ φ C.cache (C.ts q)) ∧
    (∀ p, ev = .step p → C.ts p ≠ .idle →
      φ C.cache ((step1 W C ev).1.ts p) < φ C.cache (C.ts p)) := by
  cases ev with
  | crash => exact absurd rfl hcr
  | evict i =>
    refine ⟨by simp [step1, writeBack_cache], fun q => by simp [step1, writeBack_ts], ?_⟩
    intro p hp; cases hp
  | inv p o =>
    cases hp : C.ts p with
    | run => simp [step1, hp]
    | idle =>
      refine ⟨by simp [step1, hp], fun q => ?_, fun _ h => by cases h⟩
      by_cases hqp : q = p
      · subst hqp; simp [step1, hp, φ]; exact le_of_lt (μ_rd_lt _)
      · simp [step1, hp, Function.update_of_ne hqp]
  | step p =>
    cases hp : C.ts p with
    | idle =>
      refine ⟨by simp [step1, hp], fun q => by simp [step1, hp], ?_⟩
      intro p' hp' hne; cases hp'; exact absurd hp hne
    | run a o l =>
      have hcas : ∀ it idx, l = .cas it idx → C.cache idx ≠ it := by
        rintro it idx rfl hc; exact hns p rfl ⟨a, o, it, idx, hp, hc⟩
      have hret : ∀ it idx, l ≠ .ret it idx := by
        rintro it idx rfl; exact hno _ _ (ret_output W hp)
      obtain ⟨l', hts, hμ, hcache, -⟩ := step_run_dec W C hp hcas hret
      refine ⟨hcache, fun q => ?_, ?_⟩
      · rw [hts]
        by_cases hqp : q = p
        · subst hqp; simp [hp, φ]; exact le_of_lt hμ
        · simp [Function.update_of_ne hqp]
      · intro p' hp' _
        cases hp'
        rw [hts]; simp [hp, φ]; exact hμ

/-- **Theorem 4.2** of [Liu–Golab, PODC'22]: the counter of Figure 1 is lock-free (for finitely
many threads, in every wear model): in every infinite execution in which, from some point on,
there is no crash and running threads keep taking steps, responses keep occurring. -/
theorem theorem_4_2 [Finite P] (W : Wear k ℕ) : LockFree (counter k) P W := by
  classical
  have := Fintype.ofFinite P
  intro e _ ⟨t₀, hcr⟩ hsteps t
  by_contra hcon
  push Not at hcon
  set t₁ := max t t₀ with ht₁
  have hcr' : ∀ s ≥ t₁, e s ≠ .crash := fun s hs => hcr s (by omega)
  have hno : ∀ s ≥ t₁, ∀ a r, (step1 W (cfgAt (counter k) P W e s) (e s)).2 ≠ [.res a r] :=
    fun s hs a r h => hcon s (by omega) a r h
  -- Step 1: finitely many successful CASes after `t₁`.
  let S : Set ℕ := {s | t₁ ≤ s ∧ ∃ p, e s = .step p ∧ SuccCAS (cfgAt (counter k) P W e s) p}
  have hdone : ∀ s, t₁ ≤ s → ∀ p, Done ((cfgAt (counter k) P W e s).ts p) →
      ∀ u, s ≤ u → Done ((cfgAt (counter k) P W e u).ts p) := by
    intro s hs p hd u hu
    induction u, hu using Nat.le_induction with
    | base => exact hd
    | succ u hu ih =>
      rw [cfgAt_succ]
      exact (done_step W _ (e u) (hcr' u (by omega)) (hno u (by omega)) p).2 ih
  have hfin : S.Finite := by
    have hchoose : ∀ s : S, ∃ p, e s.1 = .step p ∧ SuccCAS (cfgAt (counter k) P W e s.1) p :=
      fun s => s.2.2
    choose f hf using hchoose
    have hinj : Function.Injective f := by
      intro s s' hss'
      by_contra hne
      have key : ∀ s s' : S, s.1 < s'.1 → f s = f s' → False := by
        intro s s' hlt hff
        have h1 := (done_step W _ (e s.1) (hcr' _ s.2.1) (hno _ s.2.1) (f s)).1 (hf s).1 (hf s).2
        rw [← cfgAt_succ] at h1
        have h2 := hdone (s.1 + 1) (by have := s.2.1; omega) (f s) h1 s'.1 hlt
        obtain ⟨a, o, it, idx, hts, -⟩ := (hf s').2
        rw [hff, hts] at h2
        exact h2
      rcases Nat.lt_trichotomy s.1 s'.1 with h | h | h
      · exact key s s' h hss'
      · exact hne (Subtype.ext h)
      · exact key s' s h hss'.symm
    exact Set.finite_coe_iff.1 (Finite.of_injective f hinj)
  obtain ⟨B, hB⟩ := hfin.bddAbove
  set t₂ := max t₁ (B + 1) with ht₂
  have hnS : ∀ s ≥ t₂, ∀ p, e s = .step p → ¬ SuccCAS (cfgAt (counter k) P W e s) p := by
    intro s hs p hp hsc
    have := hB ⟨by omega, p, hp, hsc⟩
    omega
  -- Step 2: the cache is constant after `t₂`.
  set c := (cfgAt (counter k) P W e t₂).cache
  have hc : ∀ s ≥ t₂, (cfgAt (counter k) P W e s).cache = c := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => rfl
    | succ u hu ih =>
      rw [cfgAt_succ, (phi_step W _ (e u) (hcr' u (by omega)) (hno u (by omega))
        (hnS u hu)).1, ih]
  -- Step 3: the potential decreases.
  let Φ : ℕ → ℕ := fun s => ∑ p, φ c ((cfgAt (counter k) P W e s).ts p)
  have hΦ : ∀ s ≥ t₂, Φ (s + 1) ≤ Φ s ∧
      (∀ p, e s = .step p → (cfgAt (counter k) P W e s).ts p ≠ .idle → Φ (s + 1) < Φ s) := by
    intro s hs
    have H := phi_step W _ (e s) (hcr' s (by omega)) (hno s (by omega)) (hnS s hs)
    rw [hc s hs] at H
    refine ⟨?_, fun p hp hrun => ?_⟩
    · show ∑ q, _ ≤ ∑ q, _
      rw [cfgAt_succ]
      exact Finset.sum_le_sum fun q _ => H.2.1 q
    · show ∑ q, _ < ∑ q, _
      rw [cfgAt_succ]
      exact Finset.sum_lt_sum (fun q _ => H.2.1 q) ⟨p, Finset.mem_univ _, H.2.2 p hp hrun⟩
  have hmono : ∀ s ≥ t₂, ∀ u ≥ s, Φ u ≤ Φ s := by
    intro s hs u hu
    induction u, hu using Nat.le_induction with
    | base => exact le_rfl
    | succ u hu ih => exact le_trans (hΦ u (by omega)).1 ih
  have hdec : ∀ n, ∃ s ≥ t₂, Φ s + n ≤ Φ t₂ := by
    intro n
    induction n with
    | zero => exact ⟨t₂, le_rfl, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs, hsn⟩ := ih
      obtain ⟨u, hu, p, hp, hrun⟩ := hsteps s
      have h1 := (hΦ u (by omega)).2 p hp hrun
      have h2 := hmono s hs u hu
      exact ⟨u + 1, by omega, by omega⟩
  obtain ⟨s, -, hs⟩ := hdec (Φ t₂ + 1)
  omega

end Podc.WearLeveling
