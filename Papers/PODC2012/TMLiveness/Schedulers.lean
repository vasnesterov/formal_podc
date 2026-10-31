import Papers.PODC2012.TMLiveness.Liveness

/-!
# The two schedules: Lemma 1 in crash-free and in parasitic-free systems

* **Crash-free systems** (`lemma1_crashFree`): the processes are scheduled round-robin, so no
  process crashes. If `p₁` is parasitic, `p₂` is correct but makes no progress, so it does not run
  alone: another process is correct. Otherwise `p₁` is correct and never commits, so it does not
  run alone either. (The paper's sequential Strategy 2 is not admissible in a crash-free system
  with three or more processes, nor when an operation blocks until another process takes a step.)
* **Parasitic-free systems** (`lemma1_parasiticFree`): the paper's sequential Strategy 1: `p₁` is
  scheduled until `T₁` has read a value, then `p₂` until `p₁` is ready, then `p₁` again. A process
  whose operation does not return runs alone; so does `p₂` if `p₁` crashes, and `p₁` if `p₂`
  crashes. Otherwise both are correct, and only `p₂` may make progress.

In both cases we get an admissible execution with two correct processes in which only `p₂` can
make progress, against any TM ensuring serializability and solo progress.
-/

namespace Podc.TMLiveness

variable {P X V : Type*} [DecidableEq P] [DecidableEq X] [DecidableEq V]
variable {M : TM P X V} {S : Setup P X V} {init : X → V}

omit [DecidableEq P] in
theorem not_parasitic_of_crashes {α : ℕ → Step P X V} {k : P} (h : Crashes α k) :
    ¬ Parasitic α k := by
  rintro ⟨hinf, -, -⟩
  exact hinf (h.subset (fun t ⟨i, hi⟩ => by simp [hi, Step.proc, Ev.proc]))

omit [DecidableEq P] in
theorem not_progress_of_never {α : ℕ → Step P X V} {k : P}
    (h : ∀ t i, α t ≠ .ev (.res k i .commit)) : ¬ Progress α k := by
  intro hp
  obtain ⟨t, -, i, hi⟩ := infinite_iff.1 hp 0
  exact h t i hi

/-- In a run of the strategy only `p₂` can make progress. -/
theorem progress_eq_p₂ {sched : List (Step P X V) → P}
    (hM : EnsuresSafety M (Serializable init)) {k : P}
    (h : Progress (stratRun M S sched) k) : k = S.p₂ := by
  by_contra hk2
  by_cases hk1 : k = S.p₁
  · subst hk1; exact not_progress_of_never (fun t i => stratRun_ne_commit₁ hM t i) h
  · exact not_progress_of_never (fun t i => stratRun_ne_commit_other hM t hk1 hk2 i) h

/-- A process crashes iff from some point on it takes no step. -/
theorem crashes_iff_eventually {α : ℕ → Step P X V} {k : P} :
    Crashes α k ↔ ∃ T, ∀ t ≥ T, (α t).proc ≠ k := finite_iff

/-! ### Crash-free systems: round-robin scheduling -/

/-- Round-robin scheduling: at time `t` process number `t mod n`. -/
noncomputable def rrSched [Fintype P] (hP : 0 < Fintype.card P) (h : List (Step P X V)) : P :=
  (Fintype.equivFin P).symm ⟨h.length % Fintype.card P, Nat.mod_lt _ hP⟩

theorem length_stratPre {sched : List (Step P X V) → P} (t : ℕ) :
    (stratPre M S sched t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [stratPre, ih]

theorem not_crashes_rr [Fintype P] (hP : 0 < Fintype.card P) (k : P) :
    ¬ Crashes (stratRun M S (rrSched hP)) k := by
  rw [Crashes, ← Set.not_infinite, not_not, infinite_iff]
  intro T
  set n := Fintype.card P
  set j := ((Fintype.equivFin P) k).val
  refine ⟨j + n * T, by nlinarith, ?_⟩
  simp only [run_proc, rrSched, length_stratPre]
  have hj : j < n := ((Fintype.equivFin P) k).isLt
  have : (j + n * T) % n = j := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [Equiv.symm_apply_eq]
  ext; exact this

/-- **Lemma 1, crash-free systems.** -/
theorem lemma1_crashFree [Fintype P] (S : Setup P X V) (hM : EnsuresSafety M (Serializable init))
    (hsolo : ∀ α, IsExec M α → (∀ k, ¬ Crashes α k) → SoloProgress α) :
    ∃ α, IsExec M α ∧ (∀ k, ¬ Crashes α k) ∧
      (∃ k₁ k₂, k₁ ≠ k₂ ∧ Correct α k₁ ∧ Correct α k₂) ∧
      ∀ k₁ k₂, Progress α k₁ → Progress α k₂ → k₁ = k₂ := by
  have hP : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨S.p₁⟩
  set α := stratRun M S (rrSched hP)
  have hexec : IsExec M α := isExec_stratRun
  have hnc : ∀ k, ¬ Crashes α k := not_crashes_rr hP
  have hprog : ∀ k, Progress α k → k = S.p₂ := fun k h => progress_eq_p₂ hM h
  refine ⟨α, hexec, hnc, ?_, fun k₁ k₂ h₁ h₂ => (hprog k₁ h₁).trans (hprog k₂ h₂).symm⟩
  by_cases hpar : Parasitic α S.p₁
  · obtain ⟨T, c₁, a₀, hN⟩ := eventually_not_ready_of_parasitic hM hpar
    have hc2 : Correct α S.p₂ := ⟨hnc _, not_parasitic_p₂ hM hN⟩
    have hnp : ¬ Progress α S.p₂ := not_progress_p₂ hM hN
    by_contra hcon
    apply hnp
    refine hsolo α hexec hnc S.p₂ ⟨hc2, fun k hk hck => hcon ⟨k, S.p₂, hk, hck, hc2⟩⟩
  · have hc1 : Correct α S.p₁ := ⟨hnc _, hpar⟩
    by_contra hcon
    have := hsolo α hexec hnc S.p₁ ⟨hc1, fun k hk hck => hcon ⟨k, S.p₁, hk, hck, hc1⟩⟩
    exact S.hp (hprog _ this)

/-! ### Parasitic-free systems: the sequential schedule of Strategy 1 -/

open Classical in
/-- The sequential schedule: `p₁` until `T₁` has read a value, then `p₂` until `p₁` is ready, then
`p₁`. -/
noncomputable def seqSched (S : Setup P X V) (h : List (Step P X V)) : P :=
  if S.a (info (hist h)) = none ∨ S.Ready (info (hist h)) then S.p₁ else S.p₂

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
theorem IsEvOf.proc {s : Step P X V} {k : P} (h : IsEvOf s k) : s.proc = k := by
  obtain ⟨e, rfl, he⟩ := h; exact he

/-- A parasitic process has, from some point on, no pending `tryC`. -/
theorem eventually_no_pending_tryC {sched : List (Step P X V) → P} {k : P}
    (hpar : Parasitic (stratRun M S sched) k) :
    ∃ t₀, ∀ t ≥ t₀, (RI M S sched t).pend k ≠ some .tryC := by
  obtain ⟨hinf, htc, -⟩ := hpar
  obtain ⟨T₁, hT₁⟩ := finite_iff.1 htc
  obtain ⟨t₀, ht₀, i₀, hi₀⟩ := infinite_iff.1 hinf T₁
  refine ⟨t₀, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rw [(run_inv hi₀).1]; simp
  | succ t ht ih =>
    intro h
    exact hT₁ t (by omega) (run_inv_of_pend ih h)

open Classical in
theorem proc_seq (t : ℕ) : (stratRun M S (seqSched S) t).proc =
    if S.a (RI M S (seqSched S) t) = none ∨ S.Ready (RI M S (seqSched S) t) then S.p₁ else S.p₂ := by
  rw [run_proc]; rfl

/-- **Lemma 1, parasitic-free systems.** -/
theorem lemma1_parasiticFree (S : Setup P X V) (hM : EnsuresSafety M (Serializable init))
    (hsolo : ∀ α, IsExec M α → (∀ k, ¬ Parasitic α k) → SoloProgress α) :
    ∃ α, IsExec M α ∧ (∀ k, ¬ Parasitic α k) ∧
      (∃ k₁ k₂, k₁ ≠ k₂ ∧ Correct α k₁ ∧ Correct α k₂) ∧
      ∀ k₁ k₂, Progress α k₁ → Progress α k₂ → k₁ = k₂ := by
  set α := stratRun M S (seqSched S)
  have hexec : IsExec M α := isExec_stratRun
  have hprog : ∀ k, Progress α k → k = S.p₂ := fun k h => progress_eq_p₂ hM h
  have hp1 : ∀ t, (α t).proc = S.p₁ → S.a (RI M S (seqSched S) t) = none ∨
      S.Ready (RI M S (seqSched S) t) := by
    intro t h; rw [proc_seq] at h; split_ifs at h with hc
    · exact hc
    · exact absurd h.symm S.hp
  have hp2 : ∀ t, (α t).proc ≠ S.p₁ → S.a (RI M S (seqSched S) t) ≠ none ∧
      ¬ S.Ready (RI M S (seqSched S) t) := by
    intro t h; rw [proc_seq] at h; split_ifs at h with hc
    · exact absurd rfl h
    · push Not at hc; exact hc
  have hp2' : ∀ t, (α t).proc ≠ S.p₂ → (α t).proc = S.p₁ := by
    intro t h; rw [proc_seq] at h ⊢; split_ifs at h ⊢ <;> simp_all
  have hextra : ∀ k, k ≠ S.p₁ → k ≠ S.p₂ → Crashes α k := by
    intro k h1 h2
    refine Set.Finite.subset (Set.finite_empty) (fun t ht => ?_)
    simp only [Set.mem_setOf_eq] at ht
    rw [proc_seq] at ht; split_ifs at ht <;> simp_all
  have hpar_ok : ∀ k, k ≠ S.p₁ → k ≠ S.p₂ → ¬ Parasitic α k :=
    fun k h1 h2 => not_parasitic_of_crashes (hextra k h1 h2)
  -- if `p₁` is parasitic, from some point on only `p₂` is scheduled
  have hpar1 : Parasitic α S.p₁ → ∃ T, ∀ t ≥ T, (α t).proc = S.p₂ := by
    intro hpar
    obtain ⟨T, c₁, a₀, hN⟩ := eventually_not_ready_of_parasitic hM hpar
    refine ⟨T, fun t ht => ?_⟩
    rw [proc_seq, if_neg]
    rintro (h | h)
    · rw [(hN t ht).2.1] at h; simp at h
    · exact (hN t ht).2.2 h
  by_cases hc1 : Crashes α S.p₁
  · exfalso
    obtain ⟨T, hT⟩ := crashes_iff_eventually.1 hc1
    have hloc : ∀ t ≥ T, (RI M S (seqSched S) t).cnt S.p₁ = (RI M S (seqSched S) T).cnt S.p₁ ∧
        ∀ j, (RI M S (seqSched S) t).ops (S.p₁, j) = (RI M S (seqSched S) T).ops (S.p₁, j) := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact ⟨rfl, fun _ => rfl⟩
      | succ t ht ih =>
        have hloc := RI_succ_local (M := M) (S := S) (sched := seqSched S)
          (fun h => hT t ht h.proc)
        exact ⟨hloc.2.1.trans ih.1, fun j => (hloc.2.2.1 j).trans (ih.2 j)⟩
    obtain ⟨a₀, ha₀⟩ := Option.ne_none_iff_exists'.1 (hp2 T (hT T le_rfl)).1
    have hN : NeedsP₂ M S (seqSched S) T ((RI M S (seqSched S) T).cnt S.p₁) a₀ := by
      intro t ht
      refine ⟨(hloc t ht).1, ?_, (hp2 t (hT t ht)).2⟩
      rw [← ha₀]; simp only [Setup.a, Setup.T₁, (hloc t ht).1, (hloc t ht).2]
    have hnc2 : ¬ Crashes α S.p₂ := by
      rw [crashes_iff_eventually]; push Not
      intro T'
      refine ⟨max T T', le_max_right _ _, ?_⟩
      by_contra h; exact hT _ (le_max_left _ _) (hp2' _ h)
    have hc2 : Correct α S.p₂ := ⟨hnc2, not_parasitic_p₂ hM hN⟩
    have hadm : ∀ k, ¬ Parasitic α k := by
      intro k
      by_cases h1 : k = S.p₁
      · subst h1; exact not_parasitic_of_crashes hc1
      · by_cases h2 : k = S.p₂
        · subst h2; exact hc2.2
        · exact hpar_ok k h1 h2
    refine not_progress_p₂ hM hN (hsolo α hexec hadm S.p₂ ⟨hc2, fun k hk hck => ?_⟩)
    by_cases h1 : k = S.p₁
    · subst h1; exact hck.1 hc1
    · exact hck.1 (hextra k h1 hk)
  by_cases hc2 : Crashes α S.p₂
  · exfalso
    obtain ⟨T, hT⟩ := crashes_iff_eventually.1 hc2
    have hnp1 : ¬ Parasitic α S.p₁ := by
      intro hpar
      obtain ⟨T', hT'⟩ := hpar1 hpar
      exact hT (max T T') (le_max_left _ _) (hT' _ (le_max_right _ _))
    have hc1' : Correct α S.p₁ := ⟨hc1, hnp1⟩
    have hadm : ∀ k, ¬ Parasitic α k := by
      intro k
      by_cases h1 : k = S.p₁
      · subst h1; exact hnp1
      · by_cases h2 : k = S.p₂
        · subst h2; exact not_parasitic_of_crashes hc2
        · exact hpar_ok k h1 h2
    have := hsolo α hexec hadm S.p₁ ⟨hc1', fun k hk hck => ?_⟩
    · exact S.hp (hprog _ this)
    · by_cases h2 : k = S.p₂
      · subst h2; exact hck.1 hc2
      · exact hck.1 (hextra k hk h2)
  -- both `p₁` and `p₂` take infinitely many steps
  have hnp1 : ¬ Parasitic α S.p₁ := by
    intro hpar
    obtain ⟨T', hT'⟩ := hpar1 hpar
    exact hc1 (crashes_iff_eventually.2 ⟨T', fun t ht h => S.hp (h.symm.trans (hT' t ht))⟩)
  have hnp2 : ¬ Parasitic α S.p₂ := by
    intro hpar
    obtain ⟨t₀, ht₀⟩ := eventually_no_pending_tryC hpar
    obtain ⟨t₁, ht₁, hpt₁⟩ : ∃ t₁ ≥ t₀, (α t₁).proc = S.p₂ := by
      by_contra h; push Not at h
      exact hc2 (crashes_iff_eventually.2 ⟨t₀, h⟩)
    have hB : ∀ t ≥ t₁, S.a (RI M S (seqSched S) t) ≠ none ∧ ¬ S.Ready (RI M S (seqSched S) t) := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact hp2 t₁ (by rw [hpt₁]; exact Ne.symm S.hp)
      | succ t ht ih =>
        have hpt : (α t).proc = S.p₂ := by
          rw [proc_seq, if_neg]; rintro (h | h)
          · exact ih.1 h
          · exact ih.2 h
        obtain ⟨hwf, hg⟩ := good_RI (S := S) (sched := seqSched S) hM t
        rw [RI_succ]
        cases he : stratRun M S (seqSched S) t with
        | tau k => simpa [HInfo.apply] using ih
        | ev e =>
          have hep : e.proc = S.p₂ := by rw [← hpt]; simp [α, he, Step.proc]
          have hv : ValidEv (RI M S (seqSched S) t) e := by
            cases e with
            | inv k i => exact (run_inv he).1
            | res k i r => exact (run_res he).1
          have hJ : RI M S (seqSched S) (t + 1) = (RI M S (seqSched S) t).step e := by
            rw [RI_succ, he]; rfl
          have h' := S.ready_step_p₂ hwf hep hv (ht₀ t (by omega))
            (by rw [← hJ]; exact ht₀ (t + 1) (by omega))
            (fun i r hir => (run_res (hir ▸ he)).2)
          simp only [HInfo.apply, h'.1, h'.2]
          exact ih
    apply hc1
    refine crashes_iff_eventually.2 ⟨t₁, fun t ht h => ?_⟩
    have := hp1 t h
    rcases this with h' | h'
    · exact (hB t ht).1 h'
    · exact (hB t ht).2 h'
  refine ⟨α, hexec, ?_, ⟨S.p₁, S.p₂, S.hp, ⟨hc1, hnp1⟩, ⟨hc2, hnp2⟩⟩,
    fun k₁ k₂ h₁ h₂ => (hprog k₁ h₁).trans (hprog k₂ h₂).symm⟩
  intro k
  by_cases h1 : k = S.p₁
  · subst h1; exact hnp1
  · by_cases h2 : k = S.p₂
    · subst h2; exact hnp2
    · exact hpar_ok k h1 h2

end Podc.TMLiveness
