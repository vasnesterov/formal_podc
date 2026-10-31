import Papers.PODC2012.TMLiveness.Run

/-!
# Liveness facts about runs of the strategy (any scheduler)

Against a serializable TM:

* if `p₁` is parasitic, then from some point on `T₁` is fixed, has read some `a₀`, and `p₁` is
  never ready (`eventually_not_ready_of_parasitic`);
* whenever from some point on `T₁` is fixed, has read `a₀`, and `p₁` is never ready, the process
  `p₂` is not parasitic (`not_parasitic_p₂`) and makes no progress (`not_progress_p₂`): it keeps
  trying to commit a write of `bump a₀`, and any such commit would make `p₁` ready.
-/

namespace Podc.TMLiveness

variable {P X V : Type*} [DecidableEq P] [DecidableEq X] [DecidableEq V]
variable {M : TM P X V} {S : Setup P X V} {sched : List (Step P X V) → P} {init : X → V}

namespace Setup

theorem script_p₁_ready {I : HInfo P X V} {a : V} (ha : S.a I = some a) (hr : S.Ready I) :
    S.script I S.p₁ = if lastWrite S.x (I.ops (S.T₁ I)) = none then .write S.x (S.pick (S.cs I))
      else .tryC := by
  simp [script, ha, hr]

end Setup

theorem getLast?_filter_range_succ {p : ℕ → Bool} {c : ℕ} (hc : p c = true) :
    ((List.range (c + 1)).filter p).getLast? = some c := by
  rw [List.range_succ, List.filter_append]
  simp [hc]

/-- A step of the run after which a process `k` with pending invocation `i` has received the
response `r`: how the operations of its current transaction change. -/
theorem ops_after_res {t : ℕ} {k : P} {i : Inv X V} {r : Res V}
    (h : stratRun M S sched t = .ev (.res k i r)) :
    (RI M S sched (t + 1)).ops (k, (RI M S sched t).cnt k) =
      (RI M S sched t).ops (k, (RI M S sched t).cnt k) ++ (opOf i r).toList := by
  rw [RI_succ, h]; simp [HInfo.apply]

theorem infinite_inv {k : P} (h : {t | ∃ i, stratRun M S sched t = .ev (.inv k i)}.Infinite)
    (T : ℕ) : ∃ t ≥ T, ∃ i, stratRun M S sched t = .ev (.inv k i) :=
  infinite_iff.1 h T

/-- Between two invocations of `k` there is a response to the first one. -/
theorem exists_res_of_two_inv {t₁ t₂ : ℕ} {k : P} {i i' : Inv X V}
    (h1 : stratRun M S sched t₁ = .ev (.inv k i)) (h12 : t₁ < t₂)
    (h2 : stratRun M S sched t₂ = .ev (.inv k i')) :
    ∃ s, t₁ < s ∧ s < t₂ ∧ ∃ r, stratRun M S sched s = .ev (.res k i r) :=
  exists_res_between h1 h12 (run_inv h2).1

/-- **If `p₁` is parasitic**, then from some point on `T₁` is fixed, it has read some `a₀`, and
`p₁` is never ready. -/
theorem eventually_not_ready_of_parasitic (hM : EnsuresSafety M (Serializable init))
    (hpar : Parasitic (stratRun M S sched) S.p₁) :
    ∃ T c₁ a₀, ∀ t ≥ T, (RI M S sched t).cnt S.p₁ = c₁ ∧ S.a (RI M S sched t) = some a₀ ∧
      ¬ S.Ready (RI M S sched t) := by
  obtain ⟨hinf, htc, hab⟩ := hpar
  obtain ⟨T₁, hT₁⟩ := finite_iff.1 htc
  obtain ⟨T₂, hT₂⟩ := finite_iff.1 hab
  set T₀ := max T₁ T₂
  have hnotc : ∀ t ≥ T₀, stratRun M S sched t ≠ .ev (.inv S.p₁ .tryC) :=
    fun t ht => hT₁ t (by omega)
  have hnota : ∀ t ≥ T₀, ∀ i, stratRun M S sched t ≠ .ev (.res S.p₁ i .abort) :=
    fun t ht i h => hT₂ t (by omega) ⟨i, h⟩
  have hcnt1 : ∀ t ≥ T₀, (RI M S sched (t + 1)).cnt S.p₁ = (RI M S sched t).cnt S.p₁ := by
    intro t ht
    by_contra hne
    obtain ⟨i, r, he, hend⟩ := cnt_succ_ne hne
    cases r with
    | abort => exact hnota t ht i he
    | commit => exact stratRun_ne_commit₁ hM t i he
    | _ => simp [Res.isEnd] at hend
  have hcnt : ∀ t ≥ T₀, (RI M S sched t).cnt S.p₁ = (RI M S sched T₀).cnt S.p₁ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [hcnt1 t ht, ih]
  set c₁ := (RI M S sched T₀).cnt S.p₁
  set q : TxId P := (S.p₁, c₁)
  have hT : ∀ t ≥ T₀, S.T₁ (RI M S sched t) = q := fun t ht => by simp [Setup.T₁, hcnt t ht, q]
  let stage : ℕ → ℕ := fun t =>
    (if (RI M S sched t).ops q = [] then 0 else 1) +
      (if lastWrite S.x ((RI M S sched t).ops q) = none then 0 else 1)
  have hmono : ∀ t ≥ T₀, stage t ≤ stage (t + 1) := by
    intro t _
    obtain ⟨l, hl⟩ := ops_succ (M := M) (S := S) (sched := sched) t q
    simp only [stage, hl]
    have h1 : (RI M S sched t).ops q ≠ [] → (RI M S sched t).ops q ++ l ≠ [] := by simp_all
    have h2 : lastWrite S.x ((RI M S sched t).ops q) ≠ none →
        lastWrite S.x ((RI M S sched t).ops q ++ l) ≠ none := by
      intro h; rw [lastWrite_append]; cases lastWrite S.x l <;> simp_all
    split_ifs <;> simp_all
  obtain ⟨T', hT'0, hconst⟩ := Nat.eventually_const_of_le_succ (f := stage) (N := T₀) (B := 2)
    (fun t _ => by simp only [stage]; split_ifs <;> omega) hmono
  -- the response to an invocation of `p₁` after `T'`
  have hresp : ∀ t₁ ≥ T', ∀ i, stratRun M S sched t₁ = .ev (.inv S.p₁ i) →
      ∃ s, t₁ < s ∧ ∃ r, r ≠ .abort ∧ r ≠ .commit ∧ stratRun M S sched s = .ev (.res S.p₁ i r) := by
    intro t₁ ht₁ i hi
    obtain ⟨t₂, ht₂, i', hi'⟩ := infinite_inv hinf (t₁ + 1)
    obtain ⟨s, hs1, -, r, hr⟩ := exists_res_of_two_inv hi (by omega) hi'
    refine ⟨s, hs1, r, fun h => hnota s (by omega) i (h ▸ hr), fun h => ?_, hr⟩
    exact stratRun_ne_commit₁ hM s i (h ▸ hr)
  -- `T₁` has an operation after `T'`
  have hne : ∀ t ≥ T', (RI M S sched t).ops q ≠ [] := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀, h0⟩ := hcon
    have hst0 : stage T' = 0 := by
      rw [← hconst t₀ ht₀]; simp [stage, h0, lastWrite]
    obtain ⟨t₁, ht₁, i, hi⟩ := infinite_inv hinf T'
    have hs1 : stage t₁ = 0 := (hconst t₁ ht₁).trans hst0
    have hops1 : (RI M S sched t₁).ops q = [] := by
      simp only [stage] at hs1; split_ifs at hs1 with h <;> simp_all
    have hiread : i = .read S.x := by
      have := (run_inv hi).2
      rw [this, S.script_p₁_none (by simp [Setup.a, hT t₁ (by omega), hops1, firstRead])]
    subst hiread
    obtain ⟨s, hs, r, hra, hrc, hr⟩ := hresp t₁ ht₁ _ hi
    obtain ⟨v, rfl⟩ : ∃ v, r = .val v := by
      have := (run_res hr).2; simp [Res.Fits] at this; tauto
    have hops2 := ops_after_res hr
    rw [show (RI M S sched s).cnt S.p₁ = c₁ from hcnt s (by omega)] at hops2
    have : stage (s + 1) ≥ 1 := by
      simp only [stage]; rw [show (S.p₁, c₁) = q from rfl] at hops2; rw [hops2]; simp [opOf]
    have := hconst (s + 1) (by omega)
    omega
  -- the first read of `T₁`
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, firstRead ((RI M S sched T').ops q) = some a₀ := by
    have hg := (good_RI (S := S) (sched := sched) hM T').2
    rcases hg.ops_shape q with h | ⟨c, r, h⟩
    · exact absurd h (hne T' le_rfl)
    · exact ⟨c, by simp [h, firstRead]⟩
  have ha : ∀ t ≥ T', S.a (RI M S sched t) = some a₀ := by
    intro t ht
    obtain ⟨l, hl⟩ := ops_mono (M := M) (S := S) (sched := sched) ht q
    simp only [Setup.a, hT t (by omega), hl, firstRead_append (hne T' le_rfl), ha₀]
  refine ⟨T', c₁, a₀, fun t ht => ⟨hcnt t (by omega), ha t ht, fun hr₃ => ?_⟩⟩
  -- if `p₁` were ready, it would stay ready, then write and invoke `tryC`
  have hready : ∀ t' ≥ t, S.Ready (RI M S sched t') := by
    intro t' ht'
    induction t', ht' using Nat.le_induction with
    | base => exact hr₃
    | succ t' ht' ih =>
      obtain ⟨hwf, hg⟩ := good_RI (S := S) (sched := sched) hM t'
      rw [RI_succ]
      cases he : stratRun M S sched t' with
      | tau k => simpa [HInfo.apply] using ih
      | ev e =>
        refine S.ready_step hwf hg (stratEv_run he) ?_ ih
        rintro i r rfl
        cases r with
        | abort => exact absurd he (hnota t' (by omega) i)
        | commit => exact absurd he (stratRun_ne_commit₁ hM t' i)
        | _ => rfl
  obtain ⟨t₁, ht₁, i, hi⟩ := infinite_inv hinf t
  have hscript := (run_inv hi).2
  rw [S.script_p₁_ready (ha t₁ (by omega)) (hready t₁ ht₁)] at hscript
  split_ifs at hscript with hlw
  · subst hscript
    obtain ⟨s, hs, r, hra, hrc, hr⟩ := hresp t₁ (by omega) _ hi
    have hrok : r = .ok := by
      have := (run_res hr).2; simp [Res.Fits] at this; tauto
    subst hrok
    have hops2 := ops_after_res hr
    rw [show (RI M S sched s).cnt S.p₁ = c₁ from hcnt s (by omega)] at hops2
    have hst1 : stage t₁ ≤ 1 := by
      simp only [stage]; rw [hT t₁ (by omega)] at hlw; simp [hlw]; split_ifs <;> omega
    have hst2 : stage (s + 1) = 2 := by
      simp only [stage]
      rw [show (S.p₁, c₁) = q from rfl] at hops2
      rw [hops2]; simp [opOf]
    have := hconst t₁ (by omega); have := hconst (s + 1) (by omega)
    omega
  · exact hnotc t₁ (by omega) (hscript ▸ hi)

/-- Hypothesis shared by the two lemmas on `p₂`: from `T` on, `T₁` is the fixed transaction
`(p₁, c₁)`, it has read `a₀`, and `p₁` is not ready. -/
def NeedsP₂ (M : TM P X V) (S : Setup P X V) (sched : List (Step P X V) → P) (T c₁ : ℕ) (a₀ : V) :
    Prop :=
  ∀ t ≥ T, (RI M S sched t).cnt S.p₁ = c₁ ∧ S.a (RI M S sched t) = some a₀ ∧
    ¬ S.Ready (RI M S sched t)

/-- **`p₂` is not parasitic** while it is needed: it keeps writing `bump a₀` and invoking
`tryC`. -/
theorem not_parasitic_p₂ (hM : EnsuresSafety M (Serializable init)) {T c₁ : ℕ} {a₀ : V}
    (hN : NeedsP₂ M S sched T c₁ a₀) : ¬ Parasitic (stratRun M S sched) S.p₂ := by
  rintro ⟨hinf, htc, hab⟩
  obtain ⟨T₁, hT₁⟩ := finite_iff.1 htc
  obtain ⟨T₂, hT₂⟩ := finite_iff.1 hab
  obtain ⟨t₀, ht₀, i₀, hi₀⟩ := infinite_inv hinf (max T (max T₁ T₂))
  have hnotc : ∀ t ≥ t₀, stratRun M S sched t ≠ .ev (.inv S.p₂ .tryC) :=
    fun t ht => hT₁ t (by omega)
  have hnota : ∀ t ≥ t₀, ∀ i, stratRun M S sched t ≠ .ev (.res S.p₂ i .abort) :=
    fun t ht i h => hT₂ t (by omega) ⟨i, h⟩
  -- no pending `tryC` from `t₀` on
  have hptc : ∀ t ≥ t₀, (RI M S sched t).pend S.p₂ ≠ some .tryC := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rw [(run_inv hi₀).1]; simp
    | succ t ht ih =>
      intro h
      exact hnotc t ht (run_inv_of_pend ih h)
  have hcnt1 : ∀ t ≥ t₀, (RI M S sched (t + 1)).cnt S.p₂ = (RI M S sched t).cnt S.p₂ := by
    intro t ht
    by_contra hne
    obtain ⟨i, r, he, hend⟩ := cnt_succ_ne hne
    cases r with
    | abort => exact hnota t ht i he
    | commit => exact hptc t ht ((run_res he).1.trans (by rw [run_commit_tryC he]))
    | _ => simp [Res.isEnd] at hend
  have hcnt : ∀ t ≥ t₀, (RI M S sched t).cnt S.p₂ = (RI M S sched t₀).cnt S.p₂ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [hcnt1 t ht, ih]
  set q : TxId P := (S.p₂, (RI M S sched t₀).cnt S.p₂)
  -- pending writes of `p₂` write `bump a₀`
  have hpw : ∀ t ≥ t₀, ∀ y v, (RI M S sched t).pend S.p₂ = some (.write y v) → v = S.bump a₀ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro y v h; rw [(run_inv hi₀).1] at h; simp at h
    | succ t ht ih =>
      intro y v h
      by_cases h' : (RI M S sched t).pend S.p₂ = some (.write y v)
      · exact ih y v h'
      · have he := run_inv_of_pend h' h
        obtain ⟨-, hs⟩ := run_inv he
        obtain ⟨-, h1 | ⟨-, -, -, a, ha, hv⟩⟩ := S.script_write hs.symm
        · exact absurd h1.1.symm S.hp
        · rw [(hN t (by omega)).2.1] at ha
          simp only [Option.some.injEq] at ha
          rw [hv, ha]
  let stage : ℕ → ℕ := fun t =>
    (if (RI M S sched t).began q then 1 else 0) +
      (if lastWrite S.x ((RI M S sched t).ops q) = some (S.bump a₀) then 1 else 0)
  have hmono : ∀ t ≥ t₀, stage t ≤ stage (t + 1) := by
    intro t ht
    have hb : (RI M S sched t).began q = true → (RI M S sched (t + 1)).began q = true :=
      began_succ
    have hl : lastWrite S.x ((RI M S sched t).ops q) = some (S.bump a₀) →
        lastWrite S.x ((RI M S sched (t + 1)).ops q) = some (S.bump a₀) := by
      intro hlw
      rw [RI_succ]
      cases he : stratRun M S sched t with
      | tau k => simpa [HInfo.apply] using hlw
      | ev e =>
        cases e with
        | inv k i => simpa [HInfo.apply] using hlw
        | res k i r =>
          simp only [HInfo.apply, step_res_ops]
          split_ifs with hq
          · rw [lastWrite_append]
            cases ho : opOf i r with
            | none => simpa [lastWrite] using hlw
            | some o =>
              cases o with
              | read y v => simpa [lastWrite] using hlw
              | write y v =>
                have hi := Setup.opOf_eq_write ho
                subst hi
                have hk : k = S.p₂ := (congrArg Prod.fst hq).symm
                subst hk
                have hpk := (run_res he).1
                have hv := hpw t ht y v hpk
                have hy : y = S.x := by
                  have hg := (good_RI (S := S) (sched := sched) hM t).2
                  rcases hg.pend_x _ _ hpk with h | ⟨v', h⟩ | h <;> simp_all
                subst hy hv
                simp [lastWrite]
          · exact hlw
    simp only [stage]
    split_ifs <;> simp_all
  obtain ⟨T', hT'0, hconst⟩ := Nat.eventually_const_of_le_succ (f := stage) (N := t₀) (B := 2)
    (fun t _ => by simp only [stage]; split_ifs <;> omega) hmono
  obtain ⟨t₁, ht₁, i, hi⟩ := infinite_inv hinf T'
  obtain ⟨hp1, hs⟩ := run_inv hi
  have hc1 : (RI M S sched t₁).cnt S.p₂ = (RI M S sched t₀).cnt S.p₂ := hcnt t₁ (by omega)
  by_cases hb : (RI M S sched t₁).began q = true
  · obtain ⟨-, ha, hr⟩ := hN t₁ (by omega)
    have hbq : (RI M S sched t₁).began (S.p₂, (RI M S sched t₁).cnt S.p₂) = true := by
      rw [hc1]; exact hb
    rw [S.script_p₂_eq hbq ha hr] at hs
    split_ifs at hs with hlw
    · exact hnotc t₁ (by omega) (hs ▸ hi)
    · subst hs
      obtain ⟨t₂, ht₂, i', hi'⟩ := infinite_inv hinf (t₁ + 1)
      obtain ⟨s, hs1, hs2, r, hr⟩ := exists_res_of_two_inv hi (by omega) hi'
      have hrok : r = .ok := by
        have := (run_res hr).2
        simp only [Res.Fits] at this
        rcases this with h | h
        · exact absurd (h ▸ hr) (hnota s (by omega) _)
        · exact h
      subst hrok
      have hops2 := ops_after_res hr
      rw [show (RI M S sched s).cnt S.p₂ = (RI M S sched t₀).cnt S.p₂ from hcnt s (by omega)]
        at hops2
      have hst1 : stage t₁ = 1 := by
        simp only [stage, hb]; rw [hc1] at hlw; simp [hlw, q]
      have hst2 : stage (s + 1) = 2 := by
        have hb2 : (RI M S sched (s + 1)).began q = true := by
          obtain ⟨l, -⟩ := ops_mono (M := M) (S := S) (sched := sched) (show t₁ ≤ s + 1 by omega) q
          clear l
          induction s + 1, (show t₁ ≤ s + 1 by omega) using Nat.le_induction with
          | base => exact hb
          | succ u _ ih => exact began_succ ih
        simp only [stage, hb2]
        rw [show (S.p₂, (RI M S sched t₀).cnt S.p₂) = q from rfl] at hops2
        rw [hops2]; simp [opOf, lastWrite]
      have := hconst t₁ (by omega); have := hconst (s + 1) (by omega)
      omega
  · have hb2 : (RI M S sched (t₁ + 1)).began q = true := by
      rw [RI_succ, hi]
      simp [HInfo.apply, q, ← hc1]
    have hlw : lastWrite S.x ((RI M S sched t₁).ops q) = some (S.bump a₀) →
        lastWrite S.x ((RI M S sched (t₁ + 1)).ops q) = some (S.bump a₀) := by
      intro h; rw [RI_succ, hi]; simpa [HInfo.apply] using h
    have hb' : (RI M S sched t₁).began q = false := by simpa using hb
    have hlt : stage t₁ < stage (t₁ + 1) := by
      simp only [stage, hb', hb2, Bool.false_eq_true, ite_false, ite_true]
      by_cases h : lastWrite S.x ((RI M S sched t₁).ops q) = some (S.bump a₀)
      · rw [if_pos h, if_pos (hlw h)]; omega
      · rw [if_neg h]; split_ifs <;> omega
    have := hconst t₁ (by omega); have := hconst (t₁ + 1) (by omega)
    omega

/-- **`p₂` makes no progress** while it is needed: a commit of `p₂` whose `tryC` was invoked
while it was needed makes `p₁` ready. -/
theorem not_progress_p₂ (hM : EnsuresSafety M (Serializable init)) {T c₁ : ℕ} {a₀ : V}
    (hN : NeedsP₂ M S sched T c₁ a₀) : ¬ Progress (stratRun M S sched) S.p₂ := by
  intro hprog
  obtain ⟨s₁, hs₁, i₁, he₁⟩ := infinite_iff.1 hprog T
  obtain ⟨s₂, hs₂, i₂, he₂⟩ := infinite_iff.1 hprog (s₁ + 1)
  have hi₂ := run_commit_tryC he₂
  subst hi₂
  have hp₂ := (run_res he₂).1
  have hp₁ : (RI M S sched (s₁ + 1)).pend S.p₂ = none := by
    rw [RI_succ, he₁]; simp [HInfo.apply]
  obtain ⟨m, hm1, hm2, hpm, hlast⟩ :=
    Nat.exists_last_of_le (p := fun m => (RI M S sched m).pend S.p₂ ≠ some .tryC)
      (show s₁ + 1 ≤ s₂ by omega) (by simp [hp₁])
  have hms : m < s₂ := lt_of_le_of_ne hm2 (by rintro rfl; exact hpm hp₂)
  have hpend : ∀ u, m < u → u ≤ s₂ → (RI M S sched u).pend S.p₂ = some .tryC := by
    intro u h1 h2; simpa using hlast u h1 h2
  have hinv := run_inv_of_pend hpm (hpend (m + 1) (by omega) (by omega))
  obtain ⟨-, hscr⟩ := run_inv hinv
  obtain ⟨a, ha, -, hlw⟩ := S.script_p₂_tryC hscr.symm
  rw [(hN m (by omega)).2.1] at ha
  simp only [Option.some.injEq] at ha
  subst ha
  -- the state of `p₂` is frozen from `m` to `s₂`
  have hfrozen : ∀ u, m ≤ u → u ≤ s₂ → (RI M S sched u).cnt S.p₂ = (RI M S sched m).cnt S.p₂ ∧
      ∀ j, (RI M S sched u).ops (S.p₂, j) = (RI M S sched m).ops (S.p₂, j) := by
    intro u hu1 hu2
    induction u, hu1 using Nat.le_induction with
    | base => exact ⟨rfl, fun _ => rfl⟩
    | succ u hmu ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [RI_succ]
      cases he : stratRun M S sched u with
      | tau k => simpa [HInfo.apply] using ⟨ih1, ih2⟩
      | ev e =>
        cases e with
        | inv k i => simpa [HInfo.apply] using ⟨ih1, ih2⟩
        | res k i r =>
          by_cases hk : k = S.p₂
          · subst hk
            have : (RI M S sched (u + 1)).pend S.p₂ = none := by
              rw [RI_succ, he]; simp [HInfo.apply]
            rw [hpend (u + 1) (by omega) hu2] at this
            simp at this
          · refine ⟨by simp only [HInfo.apply]; rw [Setup.step_res_cnt_ne (Ne.symm hk), ih1],
              fun j => ?_⟩
            simp only [HInfo.apply, step_res_ops, Prod.mk.injEq, Ne.symm hk, false_and,
              if_false]
            exact ih2 j
  obtain ⟨hc, hops⟩ := hfrozen s₂ hm2 le_rfl
  set c := (RI M S sched s₂).cnt S.p₂ with hcdef
  have hI' : RI M S sched (s₂ + 1) = (RI M S sched s₂).step (.res S.p₂ .tryC .commit) := by
    rw [RI_succ, he₂]; rfl
  obtain ⟨hc₁, ha₁, hnr⟩ := hN (s₂ + 1) (by omega)
  apply hnr
  obtain ⟨hwf, -⟩ := good_RI (S := S) (sched := sched) hM s₂
  obtain ⟨hc₁', ha₁', -⟩ := hN s₂ (by omega)
  have hbeg : (RI M S sched s₂).began (S.p₁, c₁) = true := by
    have := S.began_of_a hwf (by rw [ha₁']; simp)
    simpa [Setup.T₁, hc₁'] using this
  have hT1 : S.T₁ (RI M S sched (s₂ + 1)) = (S.p₁, c₁) := by simp [Setup.T₁, hc₁]
  have hj0 : S.j₀ (RI M S sched (s₂ + 1)) ≤ c := by
    simp only [Setup.j₀, hT1]
    rw [hI', step_res_snap]
    exact hwf.snap_le _ _ hbeg
  have hchain : (S.chain (RI M S sched (s₂ + 1))).getLast? = some c := by
    unfold Setup.chain
    have hcnt' : (RI M S sched (s₂ + 1)).cnt S.p₂ = c + 1 := by
      rw [hI', Setup.step_res_cnt_self]; simp [Res.isEnd, hcdef]
    rw [hcnt']
    apply getLast?_filter_range_succ
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hj0, ?_⟩
    rw [hI', step_res_committed]
    simp [Res.isCommit, hcdef]
  have hdlast : S.dlast (RI M S sched (s₂ + 1)) = some (S.bump a₀) := by
    simp only [Setup.dlast, hchain, Option.bind_some]
    rw [hI', step_res_ops, if_pos rfl]
    simp only [opOf, Option.toList_none, List.append_nil]
    rw [hops c, hc]
    exact hlw
  exact ⟨a₀, S.bump a₀, ha₁, hdlast, S.bump_ne a₀, by rw [hI']; simp⟩

end Podc.TMLiveness
