import Papers.PODC2020.BezoutElection.Alg2ALive2

/-!
# Algorithm 2: liveness of a competition, the leader commits

Once the leader `ℓ` of the competition is determined (and is eligible), it eventually reaches
the committing phase (Algorithm 1's argument, `Alg1Term.lean`, `phase2`, step 1): eventually all
pending `⊥`-writes are the committing value of line 8, then `REG` holds committing values only,
and `ℓ` reads one.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

namespace LCtx

variable {R : ARun n U ids} (X : LCtx R)
include X

/-- The leader stays the leader. -/
lemma lead_forever {T₀ : ℕ} {ℓ : P} (E : Lead n ids (R.A T₀) ℓ) :
    ∀ t ≥ T₀, Lead n ids (R.A t) ℓ := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact E
  | succ t _ ih => exact R.lead_next X.hid X.hn ih (by rw [X.lev, X.lev])

/-- In a competition with a leader, the identifier in the register is the leader's. -/
lemma reg_id_lead {t : ℕ} {ℓ : P} (E : Lead n ids (R.A t) ℓ) {a : Id}
    (h : (R.A t).reg.id = some a) : a = ids ℓ := by
  obtain ⟨c, rfl, -, hc⟩ := (R.inv t).1.regId a h
  by_contra hne
  have hcl : c ≠ ℓ := fun h' => hne (by rw [h'])
  have := (E.others c hcl).2; rw [hc] at this; cases this

/-- **The leader commits.** -/
theorem phase2a {T₀ : ℕ} (hT₀ : X.T ≤ T₀) {ℓ : P} (E₀ : Lead n ids (R.A T₀) ℓ)
    (hℓok : X.okc ℓ = true) : ∃ t ≥ T₀, ((R.A t).loc ℓ).ph = .committing := by
  by_contra hcon
  push Not at hcon
  have hE : ∀ t ≥ T₀, ((R.A t).loc ℓ).ph = .electing := fun t ht => by
    cases h : ((R.A t).loc ℓ).ph
    · rfl
    · exact absurd h (hcon t ht)
  have hL := X.lead_forever E₀
  have hEl : ∀ t ≥ T₀, ElPart n ids (R.A t) ℓ := fun t ht => (hL t ht).el (hE t ht)
  have hact : ∀ t ≥ T₀, ∀ q, ((R.A t).loc q).lv = X.L := by
    intro t ht q
    by_cases hq : q = ℓ
    · subst hq; rw [← X.lev t]; exact (hL t ht).act.1
    · rw [← X.lev t]; exact ((hL t ht).others q hq).1
  have hok : ∀ t ≥ T₀, ∀ q ok fin, (R.tr t = .proc ok fin ∨ R.tr t = .readProc ok fin) →
      R.who t = q → ok = X.okc q := by
    intro t ht q ok fin h hw; rw [← hw]; exact (X.stab t (by omega) ok fin h).1
  -- good values: an identifier is the leader's, with `n - 1` discarded identifiers
  set GoodA : Reg Id → Prop := fun v => v.id ≠ none →
    v.id = some (ids ℓ) ∧ v.disc.card = n - 1 ∧ v.phase = .electing with hGoodA
  have hRA : ∀ t ≥ T₀, GoodA (R.A t).reg := by
    intro t ht hid
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hid
    have := X.reg_id_lead (hL t ht) ha
    subst this
    obtain ⟨h1, h2⟩ := (hEl t ht).regL ha
    exact ⟨ha, h2, h1⟩
  -- processing a good value
  have hproc : ∀ t ≥ T₀, ∀ q v ok fin,
      (((R.A t).loc q).st = .copy v ∨ (((R.A t).loc q).st = .fresh ∧ v = (R.A t).reg)) →
      GoodA v → (q = ℓ → ok = true) →
      ((procX n U (ids q) ((R.A t).loc q) v ok fin).2 = none ∧
          (q = ℓ → (procX n U (ids q) ((R.A t).loc q) v ok fin).1.ph = .committing)) ∨
      (∃ w, (procX n U (ids q) ((R.A t).loc q) v ok fin).2 = some w ∧ w.id = none ∧
        w.phase = .committing) ∨
      (q = ℓ ∧ v.phase = .electing ∧ v.id = none ∧
        ∃ w, (procX n U (ids q) ((R.A t).loc q) v ok fin).2 = some w ∧ w.id = some (ids ℓ)) := by
    intro t ht q v ok fin hv hG hqok
    obtain ⟨hV, hvL⟩ := X.val_of_proc (hact t ht q) hv
    have h1 : v.level = ((R.A t).loc q).lv := by rw [hvL, hact t ht q]
    have h2 : v.level < U := by rw [hvL]; exact X.hLU
    by_cases hvC : v.phase = .committing
    · -- a committing value is the value of line 8
      obtain ⟨hid, hdisc⟩ := (hEl t ht).coVals v hV hvC
      by_cases hqE : ((R.A t).loc q).ph = .electing
      · left
        rw [procX_commit h1 h2 hvC hqE]
        exact ⟨rfl, fun _ => rfl⟩
      · left
        have h3 : ¬(v.phase = .committing ∧ ((R.A t).loc q).ph = .electing) :=
          fun h => hqE h.2
        refine ⟨?_, fun hq => ?_⟩
        · by_cases hlo : ((R.A t).loc q).lo = true ∨ ok = false
          · rw [procX_bot_noop h1 h2 h3 hid hlo]
          · exfalso
            push Not at hlo
            have hq : q = ℓ := by
              by_contra hne
              have := ((hL t ht).others q hne).2
              simp only [Bool.not_eq_true] at hlo; rw [hlo.1] at this; cases this
            subst hq; exact hqE (hE t ht)
        · subst hq; exact absurd (hE t ht) hqE
    · have hvE : v.phase = .electing := by cases h : v.phase <;> simp_all
      have h3 : ¬(v.phase = .committing ∧ ((R.A t).loc q).ph = .electing) := by
        rw [hvE]; simp
      cases hid : v.id with
      | none =>
        by_cases hq : q = ℓ
        · subst hq
          right; right
          rw [procX_bot h1 h2 h3 hid (hL t ht).act.2 (hqok rfl)]
          exact ⟨rfl, hvE, rfl, _, rfl, rfl⟩
        · left
          have hlo := ((hL t ht).others q hq).2
          rw [procX_bot_noop h1 h2 h3 hid (Or.inl hlo)]
          exact ⟨rfl, fun h => absurd h hq⟩
      | some a =>
        obtain ⟨ha, hc, -⟩ := hG (by simp [hid])
        right; left
        rw [procX_line8 h1 h2 hc (by simp [hid]) hvE]
        exact ⟨_, rfl, rfl, rfl⟩
  -- the leader commits as soon as it processes a committing value
  have hcommit : ∀ t ≥ T₀, ∀ v ok fin, (((R.A t).loc ℓ).st = .copy v ∨
      (((R.A t).loc ℓ).st = .fresh ∧ v = (R.A t).reg)) → v.phase = .committing →
      (procX n U (ids ℓ) ((R.A t).loc ℓ) v ok fin).1.ph = .committing := by
    intro t ht v ok fin hv hvC
    obtain ⟨-, hvL⟩ := X.val_of_proc (hact t ht ℓ) hv
    rw [procX_commit (by rw [hvL, hact t ht ℓ]) (by rw [hvL]; exact X.hLU) hvC (hE t ht)]
  have hℓres : ∀ t₂ ≥ T₀, ∀ l v ok fin,
      (R.A (t₂ + 1)).loc ℓ = procL n U (ids ℓ) l v ok fin →
      (procX n U (ids ℓ) l v ok fin).1.ph = .committing → False := by
    intro t₂ ht₂ l v ok fin h1 h2
    have := hE (t₂ + 1) (by omega)
    rw [h1] at this; simp only [procL, h2] at this; cases this
  have hpw : ∀ t q w, ((R.A t).loc q).st = .pend w → ∃ t' ≥ t, R.tr t' = .write := by
    intro t q w hw
    obtain ⟨t', ht', -, -, h, -⟩ := X.next_write hw
    exact ⟨t', ht', h⟩
  -- infinitely many writes
  have hIW : ∀ t, ∃ t' ≥ t, R.tr t' = .write := by
    intro t
    by_contra hc
    push Not at hc
    obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ max t T₀) ℓ
    have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
        (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
    rcases hproc t'' (by omega) ℓ _ _ _ (Or.inr ⟨hfr, rfl⟩) (hRA t'' (by omega))
      (fun _ => hℓok) with ⟨-, h4⟩ | ⟨w, h4, -⟩ | ⟨-, -, -, w, h4, -⟩
    · exact hℓres t' (by omega) _ _ _ _ hl3 (h4 rfl)
    · obtain ⟨t₃, ht₃, h5⟩ := hpw (t' + 1) ℓ w (by rw [hl3]; simp [procL, h4, stOf])
      exact hc t₃ (by omega) h5
    · obtain ⟨t₃, ht₃, h5⟩ := hpw (t' + 1) ℓ w (by rw [hl3]; simp [procL, h4, stOf])
      exact hc t₃ (by omega) h5
  -- level A: pending `⊥`-writes are committing, copies are good
  have hQA : ∀ q, ∃ T, ∀ t ≥ T,
      (∀ w, ((R.A t).loc q).st = .pend w → w.id = none → w.phase = .committing) ∧
      (∀ v, ((R.A t).loc q).st = .copy v → GoodA v) := by
    intro q
    have hres : ∀ t ≥ T₀, ∀ v ok fin,
        (((R.A t).loc q).st = .copy v ∨ (((R.A t).loc q).st = .fresh ∧ v = (R.A t).reg)) →
        GoodA v → (q = ℓ → ok = true) →
        ∀ w, (procL n U (ids q) ((R.A t).loc q) v ok fin).st = .pend w → w.id = none →
          w.phase = .committing := by
      intro t ht v ok fin hv hG hqok w hw hwid
      simp only [procL] at hw
      rcases hproc t ht q v ok fin hv hG hqok with ⟨h4, -⟩ | ⟨w', h4, -, h5⟩ | ⟨-, -, -, w', h4, h5⟩
      · rw [h4] at hw; cases hw
      · rw [h4] at hw; simp only [stOf, AStatus.pend.injEq] at hw; subst hw; exact h5
      · rw [h4] at hw; simp only [stOf, AStatus.pend.injEq] at hw; subst hw
        rw [h5] at hwid; cases hwid
    obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc hT₀ q
    refine ⟨t' + 1, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base =>
      have hl3 : (R.A (t' + 1)).loc q = procL n U (ids q) ((R.A t'').loc q) (R.A t'').reg
          (X.okc q) (X.fc q) := by rw [h3]; simp
      refine ⟨fun w hw hwid => ?_, fun v hv => ?_⟩
      · rw [hl3] at hw
        exact hres t'' h1 _ _ _ (Or.inr ⟨hfr, rfl⟩) (hRA t'' h1)
          (fun h => by rw [h]; exact hℓok) w hw hwid
      · rw [hl3] at hv; simp only [procL] at hv
        cases ho : (procX n U (ids q) ((R.A t'').loc q) (R.A t'').reg (X.okc q) (X.fc q)).2 <;>
          simp [ho, stOf] at hv
    | succ t ht ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rcases X.loc_cases t q with h | ⟨-, -, h⟩ | ⟨hw, v, ok, fin, hv, h, htr⟩ | ⟨-, w, -, h⟩
      · rw [h]; exact ⟨ih1, ih2⟩
      · rw [h]; simp only
        refine ⟨fun w hw => (by cases hw), fun v hv => ?_⟩
        simp only [AStatus.copy.injEq] at hv; subst hv
        exact hRA t (by omega)
      · rw [h]
        have hG : GoodA v := by
          rcases hv with hv | ⟨-, rfl⟩
          · exact ih2 v hv
          · exact hRA t (by omega)
        refine ⟨hres t (by omega) v ok fin hv hG (fun hq => by
          rw [hok t (by omega) q ok fin htr hw, hq]; exact hℓok), fun v' hv' => ?_⟩
        simp only [procL] at hv'
        cases ho : (procX n U (ids q) ((R.A t).loc q) v ok fin).2 <;> simp [ho, stOf] at hv'
      · rw [h]; simp only
        exact ⟨fun w hw => (by cases hw), fun v hv => (by cases hv)⟩
  obtain ⟨TA, hTA, hQA'⟩ := ev_forall_fin _ hQA T₀
  -- level B: `⊥`-values in the register are committing
  obtain ⟨TB, hTB, hRB⟩ := X.ev_write
    (fun t => (R.A t).reg.id = none → (R.A t).reg.phase = .committing) TA
    (fun t ht hR ha => by
      rcases R.reg_step t with h1 | ⟨-, w, hw, h1⟩
      · rw [h1] at ha ⊢; exact hR ha
      · rw [h1] at ha ⊢; exact (hQA' t ht _).1 w hw ha)
    (fun t ht hwt ha => by
      obtain ⟨w, hw, h1⟩ := R.reg_write hwt
      rw [h1] at ha ⊢; exact (hQA' t ht _).1 w hw ha) hIW
  -- level C: the leader eventually writes only `⊥`-values
  have hQC : ∃ TC ≥ TB, ∀ t ≥ TC, (∀ w, ((R.A t).loc ℓ).st = .pend w → w.id = none) ∧
      (∀ v, ((R.A t).loc ℓ).st = .copy v → v.id = none → v.phase = .committing) := by
    have hres : ∀ t ≥ TB, ∀ t₂ ≥ t, ∀ v ok fin,
        (((R.A t).loc ℓ).st = .copy v ∨ (((R.A t).loc ℓ).st = .fresh ∧ v = (R.A t).reg)) →
        GoodA v → (v.id = none → v.phase = .committing) → ok = true →
        (R.A (t₂ + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t).loc ℓ) v ok fin →
        ∀ w, (procL n U (ids ℓ) ((R.A t).loc ℓ) v ok fin).st = .pend w → w.id = none := by
      intro t ht t₂ ht₂ v ok fin hv hG hC hok' hres' w hw
      by_cases hid : v.id = none
      · exact (hℓres t₂ (by omega) _ _ _ _ hres' (hcommit t (by omega) v ok fin hv (hC hid))).elim
      · simp only [procL] at hw
        rcases hproc t (by omega) ℓ v ok fin hv hG (fun _ => hok') with
          ⟨h4, -⟩ | ⟨w', h4, h5, -⟩ | ⟨-, -, h6, -⟩
        · rw [h4] at hw; cases hw
        · rw [h4] at hw; simp only [stOf, AStatus.pend.injEq] at hw; subst hw; exact h5
        · exact absurd h6 hid
    obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ TB) ℓ
    have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
        (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
    refine ⟨t' + 1, by omega, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base =>
      refine ⟨fun w hw => ?_, fun v hv => ?_⟩
      · rw [hl3] at hw
        exact hres t'' h1 t' h2 _ _ _ (Or.inr ⟨hfr, rfl⟩) (hRA t'' (by omega)) (hRB t'' h1)
          hℓok hl3 w hw
      · rw [hl3] at hv; simp only [procL] at hv
        cases ho : (procX n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg (X.okc ℓ) (X.fc ℓ)).2 <;>
          simp [ho, stOf] at hv
    | succ t ht ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rcases X.loc_cases t ℓ with h | ⟨-, -, h⟩ | ⟨hw, v, ok, fin, hv, h, htr⟩ | ⟨-, w, -, h⟩
      · rw [h]; exact ⟨ih1, ih2⟩
      · rw [h]; simp only
        refine ⟨fun w hw => (by cases hw), fun v hv => ?_⟩
        simp only [AStatus.copy.injEq] at hv; subst hv
        exact hRB t (by omega)
      · have hG : GoodA v ∧ (v.id = none → v.phase = .committing) := by
          rcases hv with hv | ⟨-, rfl⟩
          · exact ⟨(hQA' t (by omega) ℓ).2 v hv, ih2 v hv⟩
          · exact ⟨hRA t (by omega), hRB t (by omega)⟩
        have hok' : ok = true := by rw [hok t (by omega) ℓ ok fin htr hw]; exact hℓok
        rw [h]
        refine ⟨hres t (by omega) t le_rfl v ok fin hv hG.1 hG.2 hok' h, fun v' hv' => ?_⟩
        simp only [procL] at hv'
        cases ho : (procX n U (ids ℓ) ((R.A t).loc ℓ) v ok fin).2 <;> simp [ho, stOf] at hv'
      · rw [h]; simp only
        exact ⟨fun w hw => (by cases hw), fun v hv => (by cases hv)⟩
  obtain ⟨TC, hTC, hQC'⟩ := hQC
  -- level D: all writes are committing, so eventually the register is committing forever
  have hcw : ∀ t ≥ TC, ∀ q w, ((R.A t).loc q).st = .pend w → w.phase = .committing := by
    intro t ht q w hw
    have hwid : w.id = none := by
      by_cases hq : q = ℓ
      · subst hq; exact (hQC' t ht).1 w hw
      · by_contra hne
        have := ((R.inv t).1.pendId q w hw (by rw [X.nowin t q w hw, X.lev t]) hne).2.2.2.1
        rw [((hL t (by omega)).others q hq).2] at this; cases this
    exact (hQA' t (by omega) q).1 w hw hwid
  obtain ⟨TD, hTD, hRD⟩ := X.ev_write (fun t => (R.A t).reg.phase = .committing) TC
    (fun t ht hR => by
      rcases R.reg_step t with h1 | ⟨-, w, hw, h1⟩
      · rw [h1]; exact hR
      · rw [h1]; exact hcw t ht _ w hw)
    (fun t ht hwt => by
      obtain ⟨w, hw, h1⟩ := R.reg_write hwt
      rw [h1]; exact hcw t ht _ w hw) hIW
  obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ TD) ℓ
  have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
      (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
  exact hℓres t' (by omega) _ _ _ _ hl3
    (hcommit t'' (by omega) _ _ _ (Or.inr ⟨hfr, rfl⟩) (hRD t'' h1))

end LCtx

end BezoutElection.Alg2
