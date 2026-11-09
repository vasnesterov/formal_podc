import Papers.PODC2016.WeakCrashFailures.Fig1Ranks

/-!
# Fig. 1: termination (Theorem 3) and Theorem 1

Proof structure (refining the paper's proof of Theorem 3):
1. Once `decision ≠ ⊥`, every correct process decides (`eventually_done_of_dec`).
2. Otherwise `decision = ⊥` forever, so nobody ever decides. Then every correct process climbs
   all levels up to the loop of lines 21–24 (`reach_level`): scans end by themselves, and the
   wait of round `r` ends once all `≥ n − 1` correct processes have `state ≥ r`.
3. Lemma 2 (`lemma2`): if at some time all states are `≥ 2`, no process is faulty. Here Lemma 1 is
   used in the form: a weakly failing process `f` stops while some `q` has not started; if `f`'s
   state is `≥ 2`, all processes but `q` have `state ≥ 1` (invariant `g3`), so `q` is doomed in
   round 1 (`DoomedR 1 q`) and must decide in line 7 — but it is correct and climbs to level 2.
4. A correct process at line 21 sees all states `≥ 2`, hence nobody is faulty, hence all states
   eventually become `3` and the loop of lines 21–24 ends: it decides in line 25. Contradiction.
-/

namespace Podc.WeakCrashFailures.Fig1

open Finset Cslib.SWMR

variable {n : ℕ}

/-- Descent: a quantity that never increases while `F` holds and strictly decreases at every step
of `q` (which takes infinitely many steps) cannot keep `F` forever. -/
lemma progress {σ : ℕ → Fin n} {q : Fin n} (hq : InfOften σ q) (μ : ℕ → ℕ) (F : ℕ → Prop)
    (T0 : ℕ) (hdec : ∀ t, T0 ≤ t → F t → F (t + 1) → σ t = q → μ (t + 1) < μ t)
    (hle : ∀ t, T0 ≤ t → F t → F (t + 1) → σ t ≠ q → μ (t + 1) ≤ μ t) :
    ∃ t, T0 ≤ t ∧ ¬ F t := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hmono : ∀ a b, T0 ≤ a → a ≤ b → μ b ≤ μ a := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih =>
      have hb : T0 ≤ b := le_trans ha hab
      by_cases hs : σ b = q
      · exact le_trans (le_of_lt (hdec b hb (hall b hb) (hall (b + 1) (by omega)) hs)) ih
      · exact le_trans (hle b hb (hall b hb) (hall (b + 1) (by omega)) hs) ih
  have key : ∀ k, ∃ t, T0 ≤ t ∧ μ t + k ≤ μ T0 := by
    intro k
    induction k with
    | zero => exact ⟨T0, le_rfl, by simp⟩
    | succ k ih =>
      obtain ⟨t, ht, hk⟩ := ih
      obtain ⟨s, hs, hsq⟩ := hq t
      have h1 := hmono t s ht hs
      have h2 := hdec s (le_trans ht hs) (hall s (by omega)) (hall (s + 1) (by omega)) hsq
      exact ⟨s + 1, by omega, by omega⟩
  obtain ⟨t, -, ht⟩ := key (μ T0 + 1)
  omega

section Exec

variable {x inr₀ : Fin n → ℕ} {σ : ℕ → Fin n}

local notation "E" => exec x inr₀ σ

lemma st_mono_exec {t t' : ℕ} (h : t ≤ t') (k : Fin n) : (E t).st k ≤ (E t').st k := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ t' _ ih =>
    rw [exec_succ]; exact le_trans ih (st_step_mono (inv_exec _ _ _ _) _ _)

lemma lvl_mono_exec {t t' : ℕ} (h : t ≤ t') (k : Fin n) :
    lvl ((E t).pc k) ≤ lvl ((E t').pc k) := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ t' _ ih =>
    rw [exec_succ]
    by_cases hk : k = σ t'
    · subst hk; exact le_trans ih (lvl_step (inv_exec _ _ _ _) _)
    · rw [step_pc_ne hk]; exact ih

lemma dec_isSome_exec {t t' : ℕ} (h : t ≤ t') (hd : (E t).dec.isSome) : (E t').dec.isSome := by
  induction t', h using Nat.le_induction with
  | base => exact hd
  | succ t' _ ih => rw [exec_succ]; exact step_dec_isSome ih

lemma dec_isSome_of_done {t : ℕ} {k : Fin n} {v : ℕ} (h : (E t).pc k = .done v) :
    (E t).dec.isSome := by
  have := (inv_exec x inr₀ σ t).li k
  rw [h] at this
  exact this.1

lemma st_stopped {f : Fin n} {tf t : ℕ} (hs : StoppedFrom σ f tf) (h : tf ≤ t) :
    (E t).st f = (E tf).st f := by
  induction t, h using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [exec_succ, step_st_ne (fun he => hs t ht he.symm), ih]

/-- Levels and states. -/
lemma st_ge_of_lvl {x : Fin n → ℕ} {C : Cfg n} (hI : Inv x C) (k : Fin n) {r : ℕ} (hr : r ≤ 3)
    (h : 2 * r ≤ lvl (C.pc k)) (hnd : ∀ v, C.pc k ≠ .done v) : r ≤ C.st k := by
  have hli := hI.li k
  cases hc : C.pc k with
  | start => rw [hc] at h; simp [lvl] at h; omega
  | scan r' j cnt mx => rw [hc] at hli h; obtain ⟨-, -, -, h4, -⟩ := hli; simp [lvl] at h; omega
  | scanIn r' j cnt mx => rw [hc] at hli h; obtain ⟨-, -, -, h4, -⟩ := hli; simp [lvl] at h; omega
  | wait r' j cnt mx => rw [hc] at hli h; obtain ⟨-, -, -, h4, -⟩ := hli; simp [lvl] at h; omega
  | chk j cnt mx => rw [hc] at hli; obtain ⟨-, h4, -⟩ := hli; omega
  | chkIn j cnt mx => rw [hc] at hli; obtain ⟨h4, -⟩ := hli; omega
  | fin j mx => rw [hc] at hli; obtain ⟨-, h4, -⟩ := hli; omega
  | finDec j mx b => rw [hc] at hli; obtain ⟨h4, -⟩ := hli; omega
  | finIn j mx => rw [hc] at hli; obtain ⟨h4, -⟩ := hli; omega
  | done v => exact absurd hc (hnd v)

/-- At line 21 and later, all states are `≥ 2`. -/
lemma all_st2_of_lvl8 {x : Fin n → ℕ} {C : Cfg n} (hI : Inv x C) (k : Fin n)
    (h : 8 ≤ lvl (C.pc k)) (hnd : ∀ v, C.pc k ≠ .done v) (k' : Fin n) : 2 ≤ C.st k' := by
  have hli := hI.li k
  cases hc : C.pc k with
  | fin j mx => rw [hc] at hli; exact hli.2.2.1 k'
  | finDec j mx b => rw [hc] at hli; exact hli.2.1 k'
  | finIn j mx => rw [hc] at hli; exact hli.2.1 k'
  | done v => exact absurd hc (hnd v)
  | start => rw [hc] at h; simp [lvl] at h
  | scan r j cnt mx => rw [hc] at hli h; obtain ⟨-, h3, -⟩ := hli; simp [lvl] at h; omega
  | scanIn r j cnt mx => rw [hc] at hli h; obtain ⟨-, h3, -⟩ := hli; simp [lvl] at h; omega
  | wait r j cnt mx => rw [hc] at hli h; obtain ⟨-, h3, -⟩ := hli; simp [lvl] at h; omega
  | chk j cnt mx => rw [hc] at h; simp [lvl] at h
  | chkIn j cnt mx => rw [hc] at h; simp [lvl] at h

lemma lvl_le_eight {x : Fin n → ℕ} {C : Cfg n} (hI : Inv x C) (k : Fin n)
    (hnd : ∀ v, C.pc k ≠ .done v) : lvl (C.pc k) ≤ 8 := by
  have hli := hI.li k
  cases hc : C.pc k with
  | scan r j cnt mx => rw [hc] at hli; obtain ⟨-, h3, -⟩ := hli; simp [lvl]; omega
  | scanIn r j cnt mx => rw [hc] at hli; obtain ⟨-, h3, -⟩ := hli; simp [lvl]; omega
  | wait r j cnt mx => rw [hc] at hli; obtain ⟨-, h3, -⟩ := hli; simp [lvl]; omega
  | done v => exact absurd hc (hnd v)
  | _ => simp [lvl]

/-- A process doomed in round 1 is at level `≤ 1`. -/
lemma lvl_le_one_of_preR1 {x : Fin n → ℕ} {C : Cfg n} (hI : Inv x C) (k : Fin n)
    (h : PreRpc 1 k (C.pc k)) (hnd : ∀ v, C.pc k ≠ .done v) : lvl (C.pc k) ≤ 1 := by
  have hli := hI.li k
  cases hc : C.pc k with
  | start => simp [lvl]
  | scan r j cnt mx =>
    rw [hc] at hli h; obtain ⟨h1, -⟩ := hli; simp only [PreRpc] at h; simp [lvl]; omega
  | scanIn r j cnt mx =>
    rw [hc] at hli h; obtain ⟨h1, -⟩ := hli; simp only [PreRpc] at h; simp [lvl]; omega
  | wait r j cnt mx => rw [hc] at hli h; obtain ⟨h1, -⟩ := hli; simp only [PreRpc] at h; omega
  | done v => exact absurd hc (hnd v)
  | chk => rw [hc] at h; simp [PreRpc] at h
  | chkIn => rw [hc] at h; simp [PreRpc] at h
  | fin => rw [hc] at h; simp [PreRpc] at h
  | finDec => rw [hc] at h; simp [PreRpc] at h
  | finIn => rw [hc] at h; simp [PreRpc] at h

/-- Step 1: once `decision ≠ ⊥`, every correct process decides. -/
lemma eventually_done_of_dec {q : Fin n} (hq : InfOften σ q) {t0 : ℕ} (hd : (E t0).dec.isSome) :
    ∃ t v, (E t).pc q = .done v := by
  by_contra hcon
  simp only [not_exists] at hcon
  obtain ⟨t, -, hF⟩ := progress hq (fun t => drk n ((E t).pc q)) (fun _ => True) t0
    (fun t ht _ _ hs => by
      simp only [exec_succ, hs]
      exact drk_step (inv_exec _ _ _ _) q (dec_isSome_exec ht hd)
        (fun v hv => hcon (t + 1) v (by rw [exec_succ, hs]; exact hv)))
    (fun t _ _ _ hs => by
      simp only [exec_succ]
      rw [step_pc_ne (Ne.symm hs)])
  exact hF trivial

/-- One level up (under `decision = ⊥` forever). -/
lemma phase (hdn : ∀ t, (E t).dec = none) {q : Fin n} (hq : InfOften σ q) (L : ℕ) (hL : L ≤ 8)
    (T : ℕ) (hT : L ≤ lvl ((E T).pc q))
    (hW : ∀ r, 1 ≤ r → r ≤ 3 → 2 * r = L → ∃ T0, ∀ t, T0 ≤ t → n - 1 ≤ cntGE (E t) r)
    (hF8 : L = 8 → ∃ T0, ∀ k, (E T0).st k = 3) :
    ∃ t, T ≤ t ∧ L + 1 ≤ lvl ((E t).pc q) := by
  have hnd : ∀ t v, (E t).pc q ≠ .done v := fun t v h => by
    have := dec_isSome_of_done h; rw [hdn t] at this; simp at this
  -- the final argument, once `progress` gave a time where the level is no longer `L`
  have fin : ∀ T1, T ≤ T1 → (∃ t, T1 ≤ t ∧ ¬ lvl ((E t).pc q) = L) →
      ∃ t, T ≤ t ∧ L + 1 ≤ lvl ((E t).pc q) := by
    rintro T1 hT1 ⟨t, ht, hne⟩
    have := lvl_mono_exec (x := x) (inr₀ := inr₀) (σ := σ) (le_trans hT1 ht) q
    exact ⟨t, le_trans hT1 ht, by omega⟩
  have hother : ∀ (μ : PC → ℕ) t, σ t ≠ q → μ ((E (t + 1)).pc q) ≤ μ ((E t).pc q) := by
    intro μ t hs; rw [exec_succ, step_pc_ne (Ne.symm hs)]
  by_cases h0 : L = 0
  · subst h0
    refine fin T le_rfl (progress hq (fun _ => 0) (fun t => lvl ((E t).pc q) = 0) T
      (fun t _ hF hF' hs => ?_) (fun _ _ _ _ _ => le_rfl))
    exfalso
    have hI := inv_exec x inr₀ σ t
    have hli := hI.li q
    rw [exec_succ, hs] at hF'
    cases hc : (E t).pc q with
    | start => simp [step, hc, lvl] at hF'
    | scan r j cnt mx =>
      rw [hc] at hli hF; obtain ⟨h1, -⟩ := hli; simp [lvl] at hF; omega
    | scanIn r j cnt mx =>
      rw [hc] at hli hF; obtain ⟨h1, -⟩ := hli; simp [lvl] at hF; omega
    | wait r j cnt mx =>
      rw [hc] at hli hF; obtain ⟨h1, -⟩ := hli; simp [lvl] at hF; omega
    | done v => exact hnd t v hc
    | chk => rw [hc] at hF; simp [lvl] at hF
    | chkIn => rw [hc] at hF; simp [lvl] at hF
    | fin => rw [hc] at hF; simp [lvl] at hF
    | finDec => rw [hc] at hF; simp [lvl] at hF
    | finIn => rw [hc] at hF; simp [lvl] at hF
  by_cases hev : L = 2 ∨ L = 4 ∨ L = 6
  · -- a waiting loop of round `r = L / 2`
    obtain ⟨r, hr1, hr3, rfl⟩ : ∃ r, 1 ≤ r ∧ r ≤ 3 ∧ L = 2 * r :=
      ⟨L / 2, by omega, by omega, by omega⟩
    obtain ⟨T0, hT0⟩ := hW r hr1 hr3 rfl
    set T1 := max T T0
    set S0 : Finset (Fin n) := univ.filter fun k => r ≤ (E T1).st k
    have hS0c : n - 1 ≤ S0.card := hT0 T1 (le_max_right _ _)
    refine fin T1 (le_max_left _ _) (progress hq (fun t => wrk n S0 ((E t).pc q))
      (fun t => lvl ((E t).pc q) = 2 * r) T1 (fun t ht hF hF' hs => ?_)
      (fun t _ _ _ hs => hother _ t hs))
    have hI := inv_exec x inr₀ σ t
    have hli := hI.li q
    rw [exec_succ, hs] at hF' ⊢
    cases hc : (E t).pc q with
    | wait r' j cnt mx =>
      rw [hc] at hF
      simp only [lvl] at hF
      have hr' : r' = r := by omega
      subst hr'
      have := wrk_step hI q (hdn t) hc (S0 := S0)
        (fun k hk => le_trans (mem_filter.1 hk).2 (st_mono_exec (by omega) k)) hS0c
        (by rw [hF', hc]; simp [lvl])
      rw [hc] at this; exact this
    | start => rw [hc] at hF; simp [lvl] at hF; omega
    | scan r' j cnt mx => rw [hc] at hF; simp [lvl] at hF; omega
    | scanIn r' j cnt mx => rw [hc] at hF; simp [lvl] at hF; omega
    | chk => rw [hc] at hF; simp [lvl] at hF; omega
    | chkIn => rw [hc] at hF; simp [lvl] at hF; omega
    | fin => rw [hc] at hF; simp [lvl] at hF; omega
    | finDec => rw [hc] at hF; simp [lvl] at hF; omega
    | finIn => rw [hc] at hF; simp [lvl] at hF; omega
    | done v => exact absurd hc (hnd t v)
  · -- non-waiting code
    obtain ⟨T1, hT1, henv⟩ : ∃ T1, T ≤ T1 ∧ (L = 8 → ∀ t, T1 ≤ t → ∀ k, (E t).st k = 3) := by
      by_cases h8 : L = 8
      · obtain ⟨T0, hT0⟩ := hF8 h8
        refine ⟨max T T0, le_max_left _ _, fun _ t ht k => ?_⟩
        have h1 := st_mono_exec (x := x) (inr₀ := inr₀) (σ := σ)
          (le_trans (le_max_right T T0) ht) k
        have h2 := (inv_exec x inr₀ σ t).le3 k
        rw [hT0 k] at h1; omega
      · exact ⟨T, le_rfl, fun h => absurd h h8⟩
    refine fin T1 hT1 (progress hq (fun t => rk n ((E t).pc q))
      (fun t => lvl ((E t).pc q) = L) T1 (fun t ht hF hF' hs => ?_)
      (fun t _ _ _ hs => hother _ t hs))
    have hI := inv_exec x inr₀ σ t
    have hli := hI.li q
    rw [exec_succ, hs] at hF' ⊢
    refine rk_step hI q (hdn t) (fun v hv => hnd (t + 1) v (by rw [exec_succ, hs]; exact hv))
      (fun hc => by rw [hc] at hF; simp [lvl] at hF; omega)
      (fun r j cnt mx hc => by
        rw [hc] at hF hli; obtain ⟨h1, h3, -⟩ := hli; simp [lvl] at hF; omega)
      (fun h8 => henv (by omega) t ht) (by rw [hF', hF])

/-- The correct processes are at least `n − 1`. -/
lemma card_correct [DecidablePred fun q => InfOften σ q] (hF : (Faulty σ).ncard ≤ 1) :
    n - 1 ≤ (univ.filter fun q => InfOften σ q).card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun q => InfOften σ q)
  have h2 : ((univ.filter fun q => ¬ InfOften σ q : Finset (Fin n)) : Set (Fin n)) = Faulty σ := by
    ext q; simp [Faulty]
  have h3 : (univ.filter fun q => ¬ InfOften σ q : Finset (Fin n)).card ≤ 1 := by
    rw [← Set.ncard_coe_finset, h2]; exact hF
  rw [card_univ, Fintype.card_fin] at h1
  omega

/-- A common time after which a monotone property holds for all correct processes. -/
lemma common_time (P : Fin n → ℕ → Prop) (hmono : ∀ q t t', t ≤ t' → P q t → P q t')
    (h : ∀ q, InfOften σ q → ∃ T, P q T) : ∃ T0, ∀ q, InfOften σ q → ∀ t, T0 ≤ t → P q t := by
  classical
  choose! Tq hTq using h
  refine ⟨univ.sup Tq, fun q hq t ht => hmono q _ _ ?_ (hTq q hq)⟩
  exact le_trans (le_sup (mem_univ q)) ht

/-- Step 2: all correct processes reach every level up to `8` (line 21). -/
lemma reach_level (hdn : ∀ t, (E t).dec = none) (hF : (Faulty σ).ncard ≤ 1) :
    ∀ L, L ≤ 8 → ∀ q, InfOften σ q → ∃ T, L ≤ lvl ((E T).pc q) := by
  classical
  intro L
  induction L with
  | zero => intro _ q _; exact ⟨0, Nat.zero_le _⟩
  | succ L ih =>
    intro hL q hq
    obtain ⟨T, hT⟩ := ih (by omega) q hq
    have hnd : ∀ t k v, (E t).pc k ≠ .done v := fun t k v h => by
      have := dec_isSome_of_done h; rw [hdn t] at this; simp at this
    have hW : ∀ r, 1 ≤ r → r ≤ 3 → 2 * r = L →
        ∃ T0, ∀ t, T0 ≤ t → n - 1 ≤ cntGE (E t) r := by
      intro r _ hr3 hr
      obtain ⟨T0, hT0⟩ := common_time (σ := σ) (fun q t => L ≤ lvl ((E t).pc q))
        (fun q t t' h hp => le_trans hp (lvl_mono_exec h q)) (fun q hq => ih (by omega) q hq)
      refine ⟨T0, fun t ht => le_trans (card_correct hF) (card_le_card fun k hk => ?_)⟩
      simp only [mem_filter, mem_univ, true_and] at hk ⊢
      exact st_ge_of_lvl (inv_exec x inr₀ σ t) k (by omega) (by rw [hr]; exact hT0 k hk t ht)
        (hnd t k)
    obtain ⟨t, -, ht⟩ := phase hdn hq L (by omega) T hT hW (fun h => by omega)
    exact ⟨t, ht⟩

/-- **Lemma 2** of [Taubenfeld, Fig. 1] (with Lemma 1): if at some time all states are `≥ 2`,
then no process is faulty (here: under `decision = ⊥` forever, as used in Theorem 3). -/
lemma lemma2 (hdn : ∀ t, (E t).dec = none) (hF : WeakAdmissible (n - 1) 1 σ) {t0 : ℕ}
    (h : ∀ k, 2 ≤ (E t0).st k) : ∀ k, InfOften σ k := by
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨f, hf⟩ := hcon
  have hfF : f ∈ Faulty σ := hf
  obtain ⟨tf, hstop, hcont⟩ := hF.2 f hfF
  have hnd : ∀ t k v, (E t).pc k ≠ .done v := fun t k v h => by
    have := dec_isSome_of_done h; rw [hdn t] at this; simp at this
  -- some process `q` has not started at time `tf`
  have hlt : (started σ tf).card < (univ : Finset (Fin n)).card := by
    rw [card_univ, Fintype.card_fin]; unfold contention at hcont; have := f.isLt; omega
  obtain ⟨q, -, hq⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hqs : (E tf).pc q = .start := (pc_eq_start_iff x inr₀ σ tf q).2 hq
  have hI := inv_exec x inr₀ σ tf
  have hq0 : (E tf).st q = 0 := by have := hI.li q; rw [hqs] at this; exact this
  -- `tf < t0`
  have htf : tf < t0 := by
    by_contra hle
    have h1 := st_mono_exec (x := x) (inr₀ := inr₀) (σ := σ) (Nat.le_of_not_lt hle) q
    have := h q; omega
  have hf2 : 2 ≤ (E tf).st f := by rw [← st_stopped hstop htf.le]; exact h f
  have hfq : f ≠ q := by rintro rfl; omega
  -- all processes but `q` have state `≥ 1` at `tf`: `q` is doomed in round 1
  have hg3 := hI.g3 f hf2
  have hfil : (univ.filter fun k => 1 ≤ (E tf).st k) = univ.erase q := by
    apply eq_erase_of_card _ hg3
    simp [hq0]
  have hdoom : DoomedR (E tf) 1 q := by
    refine ⟨fun k hk => ?_, by omega, by rw [hqs]; trivial⟩
    have : k ∈ univ.filter fun k => 1 ≤ (E tf).st k := by rw [hfil]; simp [hk]
    exact (mem_filter.1 this).2
  have hdoomt : ∀ t, tf ≤ t → DoomedR (E t) 1 q := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hdoom
    | succ t _ ih => rw [exec_succ]; exact doomed_step (inv_exec _ _ _ _) le_rfl (by omega) ih _
  -- `q` is correct
  have hqc : InfOften σ q := by
    by_contra hqn
    have hsub : ({f, q} : Set (Fin n)) ⊆ Faulty σ := by
      intro k hk
      rcases hk with rfl | rfl
      · exact hfF
      · exact hqn
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hfq] at this
    have := hF.1
    omega
  obtain ⟨T2, hT2⟩ := reach_level hdn (le_trans (le_of_eq rfl) hF.1) 2 (by omega) q hqc
  have h1 := lvl_mono_exec (x := x) (inr₀ := inr₀) (σ := σ) (le_max_left T2 tf) q
  have h2 := lvl_le_one_of_preR1 (inv_exec x inr₀ σ (max T2 tf)) q
    (hdoomt _ (le_max_right _ _)).2.2 (hnd _ q)
  omega

end Exec

/-- **Theorem 3 (termination)** of [Taubenfeld, Fig. 1]: in every infinite execution with at most
one crash `(n−1)`-failure, every correct process eventually decides (any `n`). -/
theorem theorem3 (x inr₀ : Fin n → ℕ) (σ : ℕ → Fin n)
    (hF : WeakAdmissible (n - 1) 1 σ) (p : Fin n) (hp : InfOften σ p) :
    ∃ t v, (exec x inr₀ σ t).pc p = .done v := by
  by_contra hcon
  -- `decision` is never written
  have hdn : ∀ t, (exec x inr₀ σ t).dec = none := by
    intro t
    by_contra hd
    exact hcon (eventually_done_of_dec hp (t0 := t) (Option.ne_none_iff_isSome.1 hd))
  have hnd : ∀ t k v, (exec x inr₀ σ t).pc k ≠ .done v := fun t k v h => by
    have := dec_isSome_of_done h; rw [hdn t] at this; simp at this
  -- `p` reaches line 21; then nobody is faulty
  obtain ⟨T8, hT8⟩ := reach_level hdn hF.1 8 le_rfl p hp
  have hall := lemma2 hdn hF (all_st2_of_lvl8 (inv_exec x inr₀ σ T8) p hT8 (hnd T8 p))
  -- eventually all states are `3`
  obtain ⟨T6, hT6⟩ := common_time (σ := σ) (fun q t => 6 ≤ lvl ((exec x inr₀ σ t).pc q))
    (fun q t t' h hq => le_trans hq (lvl_mono_exec h q))
    (fun q hq => reach_level hdn hF.1 6 (by omega) q hq)
  obtain ⟨t, -, ht⟩ := phase hdn hp 8 le_rfl T8 hT8 (fun r _ hr3 hr => by omega)
    (fun _ => ⟨T6, fun k => by
      have := st_ge_of_lvl (inv_exec x inr₀ σ T6) k (r := 3) le_rfl
        (hT6 k (hall k) T6 le_rfl) (hnd T6 k)
      have := (inv_exec x inr₀ σ T6).le3 k
      omega⟩)
  have := lvl_le_eight (inv_exec x inr₀ σ t) p (hnd t p)
  omega

end Podc.WeakCrashFailures.Fig1
