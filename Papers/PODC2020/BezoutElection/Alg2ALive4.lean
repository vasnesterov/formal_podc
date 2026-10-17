import Papers.PODC2020.BezoutElection.Alg2ALive3

/-!
# Algorithm 2: liveness of a competition, the committing phase

Once the leader `ℓ` is committing, the competition is eventually won by `ℓ` (Algorithm 1's
argument, `Alg1Term.lean`, `phase2`, steps 2–3): `ℓ`'s `discarded` set stabilizes; if it contains
all other processes, they are all quiet and `ℓ` eventually reads its own final value and wins;
otherwise some process outside it keeps acknowledging, `ℓ` cannot read `⊥` any more, stops
writing, and eventually reads `⊥` — a contradiction. Since no competition is won (`nowin`),
this is impossible.
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

/-- **The committing phase ends** (with a win, which is excluded): contradiction. -/
theorem phase2b {T₁ : ℕ} (hT₁ : X.T ≤ T₁) {ℓ : P} (E₁ : Lead n ids (R.A T₁) ℓ)
    (hC₁ : ((R.A T₁).loc ℓ).ph = .committing) (hℓok : X.okc ℓ = true) : False := by
  have hL := X.lead_forever E₁
  have hact : ∀ t ≥ T₁, ∀ q, ((R.A t).loc q).lv = X.L := by
    intro t ht q
    by_cases hq : q = ℓ
    · subst hq; rw [← X.lev t]; exact (hL t ht).act.1
    · rw [← X.lev t]; exact ((hL t ht).others q hq).1
  have hC : ∀ t ≥ T₁, ((R.A t).loc ℓ).ph = .committing := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hC₁
    | succ t ht ih => exact X.ph_mono hact t ht ℓ ih
  have hCo : ∀ t ≥ T₁, CoPart n ids (R.A t) ℓ := fun t ht => (hL t ht).co (hC t ht)
  have hok : ∀ t ≥ T₁, ∀ q ok fin, (R.tr t = .proc ok fin ∨ R.tr t = .readProc ok fin) →
      R.who t = q → ok = X.okc q := by
    intro t ht q ok fin h hw; rw [← hw]; exact (X.stab t (by omega) ok fin h).1
  have hlo : ∀ t ≥ T₁, ((R.A t).loc ℓ).lo = false := fun t ht => (hL t ht).act.2
  -- the leader's processing in the committing phase
  have hprocL : ∀ t ≥ T₁, ∀ v ok fin,
      (((R.A t).loc ℓ).st = .copy v ∨ (((R.A t).loc ℓ).st = .fresh ∧ v = (R.A t).reg)) →
      ok = true →
      (v.id = none ∧ (procX n U (ids ℓ) ((R.A t).loc ℓ) v ok fin).1.D =
          (if v.phase = .committing then ((R.A t).loc ℓ).D ∪ v.disc else ((R.A t).loc ℓ).D) ∧
        ∃ w, (procX n U (ids ℓ) ((R.A t).loc ℓ) v ok fin).2 = some w ∧ w.id = some (ids ℓ)) ∨
      (v.id = some (ids ℓ) ∧ v.phase = .committing ∧ v.disc ⊆ ((R.A t).loc ℓ).D ∧
        v.disc.card ≠ n - 1 ∧ procX n U (ids ℓ) ((R.A t).loc ℓ) v ok fin = ((R.A t).loc ℓ, none)) ∨
      (∃ w, (procX n U (ids ℓ) ((R.A t).loc ℓ) v ok fin).2 = some w ∧ w.level = v.level + 1) := by
    intro t ht v ok fin hv hok'
    obtain ⟨hV, hvL⟩ := X.val_of_proc (hact t ht ℓ) hv
    have h1 : v.level = ((R.A t).loc ℓ).lv := by rw [hvL, hact t ht ℓ]
    have h2 : v.level < U := by rw [hvL]; exact X.hLU
    have h3 : ¬(v.phase = .committing ∧ ((R.A t).loc ℓ).ph = .electing) := by
      rw [hC t ht]; simp
    cases hid : v.id with
    | none =>
      left
      rw [procX_bot h1 h2 h3 hid (hlo t ht) hok', hC t ht]
      exact ⟨rfl, rfl, _, rfl, rfl⟩
    | some a =>
      -- the identifier is the leader's, and the value is committing
      have ha : a = ids ℓ ∧ v.phase = .committing ∧ v.disc ⊆ ((R.A t).loc ℓ).D := by
        rcases hv with hv | ⟨-, rfl⟩
        · by_cases ha : a = ids ℓ
          · subst ha
            obtain ⟨c1, c2⟩ := (hCo t ht).copyL ℓ v hv (by rw [hvL, X.lev t])
              (by rw [hact t ht ℓ, X.lev t]) hid
            exact ⟨rfl, c1 rfl, c2 (c1 rfl)⟩
          · exact absurd rfl ((hL t ht).copyOther ℓ v hv (by rw [hvL, X.lev t])
              (by rw [hact t ht ℓ, X.lev t]) (by simp [hid]) (by simp [hid, ha])).1
        · have := X.reg_id_lead (hL t ht) hid
          subst this
          exact ⟨rfl, ((hCo t ht).regL hid).1, ((hCo t ht).regL hid).2⟩
      obtain ⟨rfl, hvC, hsub⟩ := ha
      by_cases hc : v.disc.card = n - 1
      · right; right
        refine ⟨_, procX_win h1 h2 h3 hc (by simp [hid]) hvC ?_, rfl⟩
        exact X.not_mem_of_nonloser hV (hlo t ht)
      · right; left
        exact ⟨rfl, hvC, hsub, hc, procX_noop_mem h1 h2 h3 (fun h => hc h.1) (by simp [hid])
          (Or.inr hid)⟩
  -- no competition is won
  have hnowin : ∀ t₂ l v ok fin, (R.A (t₂ + 1)).loc ℓ = procL n U (ids ℓ) l v ok fin →
      v.level = X.L → ∀ w, (procX n U (ids ℓ) l v ok fin).2 = some w → w.level = v.level + 1 →
      False := by
    intro t₂ l v ok fin h1 hvL w h2 h3
    have := X.nowin (t₂ + 1) ℓ w (by rw [h1]; simp [procL, h2, stOf])
    omega
  have hvlev : ∀ t ≥ T₁, ∀ v, (((R.A t).loc ℓ).st = .copy v ∨
      (((R.A t).loc ℓ).st = .fresh ∧ v = (R.A t).reg)) → v.level = X.L :=
    fun t ht v hv => (X.val_of_proc (hact t ht ℓ) hv).2
  -- the leader's discarded set grows and stabilizes
  have hDmono : ∀ t ≥ T₁, ((R.A t).loc ℓ).D ⊆ ((R.A (t + 1)).loc ℓ).D := by
    intro t ht
    rcases X.loc_cases t ℓ with h | ⟨-, -, h⟩ | ⟨hw, v, ok, fin, hv, h, htr⟩ | ⟨-, w, -, h⟩
    · rw [h]
    · rw [h]
    · have hok' : ok = true := by rw [hok t ht ℓ ok fin htr hw]; exact hℓok
      rcases hprocL t ht v ok fin hv hok' with ⟨-, e, -⟩ | ⟨-, -, -, -, e⟩ | ⟨w, e, hwl⟩
      · rw [h]; simp only [procL, e]
        split_ifs
        · exact Finset.subset_union_left
        · exact Finset.Subset.refl _
      · rw [h]; simp only [procL, e]; exact Finset.Subset.refl _
      · exact (hnowin t _ _ _ _ h (hvlev t ht v hv) w e hwl).elim
    · rw [h]
  obtain ⟨T₂, hT₂, hDst⟩ := stab_finset_from (fun t => ((R.A t).loc ℓ).D) T₁ n hDmono
    (fun t ht => card_le_n X.hn _ (fun a ha => by
      obtain ⟨i, hi, -⟩ := (R.inv t).1.discLoc ℓ (by rw [X.lev t]; exact hact t ht ℓ) a ha
      exact ⟨i, hi⟩))
  set D := ((R.A T₂).loc ℓ).D with hD
  have hDc : ∀ t ≥ T₂, ((R.A t).loc ℓ).D = D := fun t ht => hDst t ht
  have hDne : ∀ a ∈ D, ∃ j, ids j = a ∧ j ≠ ℓ := by
    intro a ha
    obtain ⟨i, hi, -, hl⟩ := (R.inv T₂).1.discLoc ℓ (by rw [X.lev T₂]; exact hact T₂ (by omega) ℓ)
      a ha
    exact ⟨i, hi, by rintro rfl; rw [hlo T₂ (by omega)] at hl; cases hl⟩
  have hDle : D.card ≤ n - 1 := card_le_of_ne X.hn D ℓ hDne
  -- eventually the leader's pending writes carry its identifier
  have hQL : ∃ Tf ≥ T₂, ∀ t ≥ Tf, ∀ w, ((R.A t).loc ℓ).st = .pend w → w.id = some (ids ℓ) := by
    have hres : ∀ t ≥ T₁, ∀ t₂ ≥ t, ∀ v ok fin,
        (((R.A t).loc ℓ).st = .copy v ∨ (((R.A t).loc ℓ).st = .fresh ∧ v = (R.A t).reg)) →
        ok = true → (R.A (t₂ + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t).loc ℓ) v ok fin →
        ∀ w, (procL n U (ids ℓ) ((R.A t).loc ℓ) v ok fin).st = .pend w → w.id = some (ids ℓ) := by
      intro t ht t₂ ht₂ v ok fin hv hok' hres' w hw
      simp only [procL] at hw
      rcases hprocL t ht v ok fin hv hok' with ⟨-, -, w', e, hw'⟩ | ⟨-, -, -, -, e⟩ | ⟨w', e, hwl⟩
      · rw [e] at hw; simp only [stOf, AStatus.pend.injEq] at hw; subst hw; exact hw'
      · rw [e] at hw; cases hw
      · exact (hnowin t₂ _ _ _ _ hres' (hvlev t ht v hv) w' e hwl).elim
    obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ T₂) ℓ
    have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
        (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
    refine ⟨t' + 1, by omega, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base =>
      intro w hw; rw [hl3] at hw
      exact hres t'' (by omega) t' h2 _ _ _ (Or.inr ⟨hfr, rfl⟩) hℓok hl3 w hw
    | succ t ht ih =>
      rcases X.loc_cases t ℓ with h | ⟨-, -, h⟩ | ⟨hw, v, ok, fin, hv, h, htr⟩ | ⟨-, w, -, h⟩
      · rw [h]; exact ih
      · rw [h]; intro w hw; cases hw
      · rw [h]
        exact hres t (by omega) t le_rfl v ok fin hv
          (by rw [hok t (by omega) ℓ ok fin htr hw]; exact hℓok) h
      · rw [h]; intro w hw; cases hw
  obtain ⟨Tf, hTf, hQL'⟩ := hQL
  by_cases hfull : D.card = n - 1
  · ------------------------------------------------------------------
    -- all other processes are quiet: the leader eventually wins
    have hquiet : ∀ t ≥ T₂, ∀ j, j ≠ ℓ → (R.A t).Quiet ids ℓ j := by
      intro t ht j hj
      apply (hCo t (by omega)).quiet j
      rw [hDc t ht]
      exact mem_of_card_eq_of_ne X.hid X.hn D ℓ hDne hfull j hj
    have hwℓ : ∀ t ≥ Tf, R.tr t = .write → ∀ w, ((R.A t).loc (R.who t)).st = .pend w →
        w.id = some (ids ℓ) := by
      intro t ht _ w hw
      by_cases hq : R.who t = ℓ
      · rw [hq] at hw; exact hQL' t ht w hw
      · exact absurd hw ((hquiet t (by omega) _ hq).2.1 w)
    have hwin : ∀ t'' ≥ Tf, ∀ t' ≥ t'', ((R.A t'').loc ℓ).st = .fresh →
        R.A (t' + 1) = (R.A t').upd ℓ (procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
          (X.okc ℓ) (X.fc ℓ)) →
        (R.A t'').reg.id = some (ids ℓ) → False := by
      intro t'' ht'' t' ht' hfr h3 hid
      have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
          (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
      rcases hprocL t'' (by omega) (R.A t'').reg (X.okc ℓ) (X.fc ℓ) (Or.inr ⟨hfr, rfl⟩) hℓok with
        ⟨hn, -⟩ | ⟨-, -, hsub, hc, -⟩ | ⟨w, e, hwl⟩
      · rw [hid] at hn; cases hn
      · apply hc
        have hge := card_ge_of_all X.hid X.hn _ ℓ
          (fun j hj => (hquiet t'' (by omega) j hj).2.2.2 hid)
        have hle := Finset.card_le_card hsub
        rw [hDc t'' (by omega)] at hle
        omega
      · exact hnowin t' _ _ _ _ hl3 (X.lev t'') w e hwl
    obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ Tf) ℓ
    cases hid : (R.A t'').reg.id with
    | some a =>
      have := X.reg_id_lead (hL t'' (by omega)) hid; subst this
      exact hwin t'' h1 t' h2 hfr h3 hid
    | none =>
      have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
          (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
      rcases hprocL t'' (by omega) (R.A t'').reg (X.okc ℓ) (X.fc ℓ) (Or.inr ⟨hfr, rfl⟩) hℓok with
        ⟨-, -, w, e, hw'⟩ | ⟨hn, -⟩ | ⟨w, e, hwl⟩
      · have hpend : ((R.A (t' + 1)).loc ℓ).st = .pend w := by rw [hl3]; simp [procL, e, stOf]
        obtain ⟨t₃, ht₃, hl₃, -, -, h4⟩ := X.next_write hpend
        have hR : ∀ t ≥ t₃ + 1, (R.A t).reg.id = some (ids ℓ) := by
          intro t ht
          induction t, ht using Nat.le_induction with
          | base => rw [h4]; simp only [AState.wr_reg]; exact hw'
          | succ t ht ih =>
            rcases R.reg_step t with h5 | ⟨h6, w', hw'', h5⟩
            · rw [h5]; exact ih
            · rw [h5]; exact hwℓ t (by omega) h6 w' hw''
        obtain ⟨t₄, t₅, h5, h6, hfr', h7⟩ := X.read_proc (by omega : X.T ≤ t₃ + 1) ℓ
        exact hwin t₄ (by omega) t₅ h6 hfr' h7 (hR t₄ h5)
      · rw [hid] at hn; cases hn
      · exact hnowin t' _ _ _ _ hl3 (X.lev t'') w e hwl
  · ------------------------------------------------------------------
    -- some process is outside the leader's discarded set
    have hlt : D.card < n - 1 := by omega
    obtain ⟨j₀, hj₀ℓ, hj₀D⟩ : ∃ j, j ≠ ℓ ∧ ids j ∉ D := by
      by_contra hcon
      push Not at hcon
      have := card_ge_of_all X.hid X.hn D ℓ hcon
      omega
    set Fresh : Reg Id → Prop := fun w => w.phase = .committing ∧
      ∃ i, ids i ∈ w.disc ∧ ids i ∉ D with hFresh
    set GoodB : Reg Id → Prop := fun v => v.id ≠ none →
      v.id = some (ids ℓ) ∧ v.phase = .committing ∧ v.disc ⊆ D with hGoodB
    have hRB : ∀ t ≥ T₂, GoodB (R.A t).reg := by
      intro t ht hid
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hid
      have := X.reg_id_lead (hL t (by omega)) ha; subst this
      obtain ⟨h1, h2⟩ := (hCo t (by omega)).regL ha
      exact ⟨ha, h1, by rw [← hDc t ht]; exact h2⟩
    -- processing by another process
    have hprocO : ∀ t ≥ T₂, ∀ j, j ≠ ℓ → ∀ v ok fin,
        (((R.A t).loc j).st = .copy v ∨ (((R.A t).loc j).st = .fresh ∧ v = (R.A t).reg)) →
        GoodB v →
        (procX n U (ids j) ((R.A t).loc j) v ok fin).2 = none ∨
        (∃ w, (procX n U (ids j) ((R.A t).loc j) v ok fin).2 = some w ∧ w.id = none ∧
          Fresh w) := by
      intro t ht j hj v ok fin hv hG
      obtain ⟨hV, hvL⟩ := X.val_of_proc (hact t (by omega) j) hv
      have h1 : v.level = ((R.A t).loc j).lv := by rw [hvL, hact t (by omega) j]
      have h2 : v.level < U := by rw [hvL]; exact X.hLU
      have hloj := ((hL t (by omega)).others j hj).2
      by_cases h3 : v.phase = .committing ∧ ((R.A t).loc j).ph = .electing
      · left; rw [procX_commit h1 h2 h3.1 h3.2]
      cases hid : v.id with
      | none => left; rw [procX_bot_noop h1 h2 h3 hid (Or.inl hloj)]
      | some a =>
        obtain ⟨ha, hvC, hsub⟩ := hG (by simp [hid])
        rw [hid] at ha; cases ha
        have hc : v.disc.card ≠ n - 1 := by
          have := Finset.card_le_card hsub; omega
        have h4 : ¬(v.disc.card = n - 1 ∧ v.id ≠ none) := fun h => hc h.1
        by_cases hm : ids j ∈ v.disc ∨ ids ℓ = ids j
        · left
          rw [procX_noop_mem h1 h2 h3 h4 (by simp [hid]) (by
            rcases hm with hm | hm
            · exact Or.inl hm
            · exact Or.inr (by rw [hid, hm]))]
        · push Not at hm
          right
          rw [procX_lose h1 h2 h3 h4 hid hm.2 hm.1]
          refine ⟨_, rfl, rfl, ?_, j, Finset.mem_insert_self _ _, fun hjD => ?_⟩
          · show ((R.A t).loc j).ph = .committing
            cases h : ((R.A t).loc j).ph
            · exact absurd ⟨hvC, h⟩ h3
            · rfl
          · have hq := (hCo t (by omega)).quiet j (by rw [hDc t ht]; exact hjD)
            rcases hv with hv | ⟨-, rfl⟩
            · rcases hq.2.2.1 v hv (by rw [hvL, X.lev t]) with h5 | ⟨-, h5⟩
              · rw [hid] at h5; cases h5
              · exact hm.1 h5
            · exact hm.1 (hq.2.2.2 hid)
    -- eventually the pending `⊥`-writes of the other processes are fresh
    have hQO : ∀ j, ∃ T, ∀ t ≥ T, j ≠ ℓ →
        (∀ w, ((R.A t).loc j).st = .pend w → w.id = none → Fresh w) ∧
        (∀ v, ((R.A t).loc j).st = .copy v → GoodB v) := by
      intro j
      by_cases hj : j = ℓ
      · exact ⟨0, fun t _ h => absurd hj h⟩
      have hres : ∀ t ≥ T₂, ∀ v ok fin,
          (((R.A t).loc j).st = .copy v ∨ (((R.A t).loc j).st = .fresh ∧ v = (R.A t).reg)) →
          GoodB v → ∀ w, (procL n U (ids j) ((R.A t).loc j) v ok fin).st = .pend w →
          w.id = none → Fresh w := by
        intro t ht v ok fin hv hG w hw _
        simp only [procL] at hw
        rcases hprocO t ht j hj v ok fin hv hG with h4 | ⟨w', h4, -, h5⟩
        · rw [h4] at hw; cases hw
        · rw [h4] at hw; simp only [stOf, AStatus.pend.injEq] at hw; subst hw; exact h5
      obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ T₂) j
      have hl3 : (R.A (t' + 1)).loc j = procL n U (ids j) ((R.A t'').loc j) (R.A t'').reg
          (X.okc j) (X.fc j) := by rw [h3]; simp
      refine ⟨t' + 1, fun t ht _ => ?_⟩
      induction t, ht using Nat.le_induction with
      | base =>
        refine ⟨fun w hw hwid => ?_, fun v hv => ?_⟩
        · rw [hl3] at hw
          exact hres t'' h1 _ _ _ (Or.inr ⟨hfr, rfl⟩) (hRB t'' h1) w hw hwid
        · rw [hl3] at hv; simp only [procL] at hv
          cases ho : (procX n U (ids j) ((R.A t'').loc j) (R.A t'').reg (X.okc j) (X.fc j)).2 <;>
            simp [ho, stOf] at hv
      | succ t ht ih =>
        obtain ⟨ih1, ih2⟩ := ih
        rcases X.loc_cases t j with h | ⟨-, -, h⟩ | ⟨hw, v, ok, fin, hv, h, htr⟩ | ⟨-, w, -, h⟩
        · rw [h]; exact ⟨ih1, ih2⟩
        · rw [h]; simp only
          refine ⟨fun w hw => (by cases hw), fun v hv => ?_⟩
          simp only [AStatus.copy.injEq] at hv; subst hv
          exact hRB t (by omega)
        · rw [h]
          have hG : GoodB v := by
            rcases hv with hv | ⟨-, rfl⟩
            · exact ih2 v hv
            · exact hRB t (by omega)
          refine ⟨hres t (by omega) v ok fin hv hG, fun v' hv' => ?_⟩
          simp only [procL] at hv'
          cases ho : (procX n U (ids j) ((R.A t).loc j) v ok fin).2 <;> simp [ho, stOf] at hv'
        · rw [h]; simp only
          exact ⟨fun w hw => (by cases hw), fun v hv => (by cases hv)⟩
    obtain ⟨T₃, hT₃, hQO'⟩ := ev_forall_fin _ hQO (max Tf T₂)
    have hcw : ∀ t ≥ T₃, ∀ q w, ((R.A t).loc q).st = .pend w → w.id = none → Fresh w := by
      intro t ht q w hw hwid
      by_cases hq : q = ℓ
      · subst hq; rw [hQL' t (by omega) w hw] at hwid; cases hwid
      · exact (hQO' t ht q hq).1 w hw hwid
    have hpw : ∀ t q w, ((R.A t).loc q).st = .pend w → ∃ t' ≥ t, R.tr t' = .write := by
      intro t q w hw
      obtain ⟨t', ht', -, -, h, -⟩ := X.next_write hw
      exact ⟨t', ht', h⟩
    -- infinitely many writes
    have hIW : ∀ t, ∃ t' ≥ t, R.tr t' = .write := by
      intro t
      by_contra hc
      push Not at hc
      set t₁ := max t T₃ with ht₁
      have hnw : ∀ t' ≥ t₁, R.tr t' ≠ .write := fun t' ht' => hc t' (by omega)
      have hnp : ∀ t' ≥ t₁, ∀ q w, ((R.A t').loc q).st = .pend w → False := by
        intro t' ht' q w hw
        obtain ⟨t'', ht'', h⟩ := hpw t' q w hw
        exact hnw t'' (by omega) h
      have hreg := X.reg_const hnw
      -- the leader reads an identifier (otherwise it would write)
      obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ t₁) ℓ
      have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
          (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
      have hvid : (R.A t₁).reg.id = some (ids ℓ) := by
        rcases hprocL t'' (by omega) (R.A t'').reg (X.okc ℓ) (X.fc ℓ) (Or.inr ⟨hfr, rfl⟩) hℓok with
          ⟨-, -, w, e, -⟩ | ⟨hn, -⟩ | ⟨w, e, hwl⟩
        · exact (hnp (t' + 1) (by omega) ℓ w (by rw [hl3]; simp [procL, e, stOf])).elim
        · rw [← hreg t'' h1]; exact hn
        · exact (hnowin t' _ _ _ _ hl3 (X.lev t'') w e hwl).elim
      obtain ⟨-, -, hsub⟩ := hRB t₁ (by omega) (by rw [hvid]; simp)
      have hj₀v : ids j₀ ∉ (R.A t₁).reg.disc := fun h => hj₀D (hsub h)
      -- `j₀` acknowledges (after possibly moving to the committing phase)
      have hack : ∀ t₂ ≥ t₁, ∀ t₃ ≥ t₂, ((R.A t₂).loc j₀).st = .fresh →
          ((R.A t₂).loc j₀).ph = .committing →
          R.A (t₃ + 1) = (R.A t₃).upd j₀ (procL n U (ids j₀) ((R.A t₂).loc j₀) (R.A t₂).reg
            (X.okc j₀) (X.fc j₀)) → False := by
        intro t₂ ht₂ t₃ ht₃ hfr' hph h4
        have hr2 : (R.A t₂).reg = (R.A t₁).reg := hreg t₂ ht₂
        obtain ⟨hV, hvL⟩ := X.val_of_proc (hact t₂ (by omega) j₀) (Or.inr ⟨hfr', rfl⟩)
        have c1 : (R.A t₂).reg.level = ((R.A t₂).loc j₀).lv := by rw [hvL, hact t₂ (by omega) j₀]
        have c2 : (R.A t₂).reg.level < U := by rw [hvL]; exact X.hLU
        have c3 : ¬((R.A t₂).reg.phase = .committing ∧ ((R.A t₂).loc j₀).ph = .electing) := by
          rw [hph]; simp
        have hc : (R.A t₂).reg.disc.card ≠ n - 1 := by
          rw [hr2]; have := Finset.card_le_card hsub; omega
        have e := procX_lose (n := n) (U := U) (me := ids j₀) (l := (R.A t₂).loc j₀)
          (ok := X.okc j₀) (fin := X.fc j₀) c1 c2 c3 (fun h => hc h.1) (by rw [hr2]; exact hvid)
          (fun h => hj₀ℓ (X.hid h).symm) (by rw [hr2]; exact hj₀v)
        exact hnp (t₃ + 1) (by omega) j₀ _ (by rw [h4]; simp only [AState.upd_loc_self, procL, e, stOf]; rfl)
      obtain ⟨t₄, t₅, h4, h5, hfr4, h6⟩ := X.read_proc (by omega : X.T ≤ t₁) j₀
      by_cases hph : ((R.A t₄).loc j₀).ph = .committing
      · exact hack t₄ h4 t₅ h5 hfr4 hph h6
      · -- `j₀` first moves to the committing phase
        have hphE : ((R.A t₄).loc j₀).ph = .electing := by
          cases h : ((R.A t₄).loc j₀).ph
          · rfl
          · exact absurd h hph
        have hr4 : (R.A t₄).reg = (R.A t₁).reg := hreg t₄ h4
        have hvC : (R.A t₄).reg.phase = .committing := by
          rw [hr4]; exact ((hCo t₁ (by omega)).regL hvid).1
        obtain ⟨-, hvL⟩ := X.val_of_proc (hact t₄ (by omega) j₀) (Or.inr ⟨hfr4, rfl⟩)
        have e := procX_commit (n := n) (U := U) (me := ids j₀) (l := (R.A t₄).loc j₀)
          (ok := X.okc j₀) (fin := X.fc j₀) (by rw [hvL, hact t₄ (by omega) j₀])
          (by rw [hvL]; exact X.hLU) hvC hphE
        have hph5 : ((R.A (t₅ + 1)).loc j₀).ph = .committing := by
          rw [h6]; simp [procL, e]
        have hphm : ∀ t ≥ t₅ + 1, ((R.A t).loc j₀).ph = .committing := by
          intro t ht
          induction t, ht using Nat.le_induction with
          | base => exact hph5
          | succ t ht ih => exact X.ph_mono hact t (by omega) j₀ ih
        obtain ⟨t₆, t₇, h7, h8, hfr6, h9⟩ := X.read_proc (by omega : X.T ≤ t₅ + 1) j₀
        exact hack t₆ (by omega) t₇ h8 hfr6 (hphm t₆ h7) h9
    -- eventually the `⊥`-values in the register are fresh
    obtain ⟨T₅, hT₅, hR5⟩ := X.ev_write
      (fun t => (R.A t).reg.id = none → Fresh (R.A t).reg) T₃
      (fun t ht hR ha => by
        rcases R.reg_step t with h1 | ⟨-, w, hw, h1⟩
        · rw [h1] at ha ⊢; exact hR ha
        · rw [h1] at ha ⊢; exact hcw t ht _ w hw ha)
      (fun t ht hwt ha => by
        obtain ⟨w, hw, h1⟩ := R.reg_write hwt
        rw [h1] at ha ⊢; exact hcw t ht _ w hw ha) hIW
    -- the leader eventually stops writing
    have hgrow : ∀ t ≥ T₂, ∀ t₂ ≥ t, ∀ v ok fin,
        (((R.A t).loc ℓ).st = .copy v ∨ (((R.A t).loc ℓ).st = .fresh ∧ v = (R.A t).reg)) →
        v.id = none → Fresh v → ok = true →
        (R.A (t₂ + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t).loc ℓ) v ok fin → False := by
      intro t ht t₂ ht₂ v ok fin hv hid hF hok' hres
      rcases hprocL t (by omega) v ok fin hv hok' with ⟨-, e, -⟩ | ⟨hn, -⟩ | ⟨w, e, hwl⟩
      · obtain ⟨hvC, i, hi1, hi2⟩ := hF
        have h1 := hDc (t₂ + 1) (by omega)
        rw [hres] at h1
        simp only [procL, e, if_pos hvC] at h1
        apply hi2
        rw [← h1]
        exact Finset.mem_union_right _ hi1
      · rw [hid] at hn; cases hn
      · exact hnowin t₂ _ _ _ _ hres (hvlev t (by omega) v hv) w e hwl
    have hQN : ∃ T₆ ≥ T₅, ∀ t ≥ T₆, (∀ w, ((R.A t).loc ℓ).st ≠ .pend w) ∧
        (∀ v, ((R.A t).loc ℓ).st = .copy v → v.id = none → Fresh v) := by
      have hres : ∀ t ≥ T₅, ∀ t₂ ≥ t, ∀ v ok fin,
          (((R.A t).loc ℓ).st = .copy v ∨ (((R.A t).loc ℓ).st = .fresh ∧ v = (R.A t).reg)) →
          (v.id = none → Fresh v) → ok = true →
          (R.A (t₂ + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t).loc ℓ) v ok fin →
          (procX n U (ids ℓ) ((R.A t).loc ℓ) v ok fin).2 = none := by
        intro t ht t₂ ht₂ v ok fin hv hF hok' hres'
        rcases hprocL t (by omega) v ok fin hv hok' with ⟨hid, -⟩ | ⟨-, -, -, -, e⟩ | ⟨w, e, hwl⟩
        · exact (hgrow t (by omega) t₂ ht₂ v ok fin hv hid (hF hid) hok' hres').elim
        · rw [e]
        · exact (hnowin t₂ _ _ _ _ hres' (hvlev t (by omega) v hv) w e hwl).elim
      obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ T₅) ℓ
      have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
          (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
      refine ⟨t' + 1, by omega, fun t ht => ?_⟩
      induction t, ht using Nat.le_induction with
      | base =>
        have e := hres t'' h1 t' h2 _ _ _ (Or.inr ⟨hfr, rfl⟩) (hR5 t'' h1) hℓok hl3
        rw [hl3]; simp only [procL, e, stOf]
        exact ⟨fun w hw => (by cases hw), fun v hv => (by cases hv)⟩
      | succ t ht ih =>
        obtain ⟨ih1, ih2⟩ := ih
        rcases X.loc_cases t ℓ with h | ⟨-, -, h⟩ | ⟨hw, v, ok, fin, hv, h, htr⟩ | ⟨-, w, hw, -⟩
        · rw [h]; exact ⟨ih1, ih2⟩
        · rw [h]; simp only
          refine ⟨fun w hw => (by cases hw), fun v hv => ?_⟩
          simp only [AStatus.copy.injEq] at hv; subst hv
          exact hR5 t (by omega)
        · have hF : v.id = none → Fresh v := by
            rcases hv with hv | ⟨-, rfl⟩
            · exact ih2 v hv
            · exact hR5 t (by omega)
          have e := hres t (by omega) t le_rfl v ok fin hv hF
            (by rw [hok t (by omega) ℓ ok fin htr hw]; exact hℓok) h
          rw [h]; simp only [procL, e, stOf]
          exact ⟨fun w hw => (by cases hw), fun v hv => (by cases hv)⟩
        · exact absurd hw (ih1 w)
    obtain ⟨T₆, hT₆, hQN'⟩ := hQN
    -- a write of another process hides the leader's identifier forever
    have hwbot : ∀ t ≥ T₆, R.tr t = .write → ∀ w, ((R.A t).loc (R.who t)).st = .pend w →
        w.id = none := by
      intro t ht _ w hw
      have hq : R.who t ≠ ℓ := by intro h; rw [h] at hw; exact (hQN' t ht).1 w hw
      by_contra hne
      have := ((R.inv t).1.pendId _ w hw (by rw [X.nowin t _ w hw, X.lev t]) hne).2.2.2.1
      rw [((hL t (by omega)).others _ hq).2] at this; cases this
    obtain ⟨t₇, ht₇, hw₇⟩ := hIW T₆
    have hnone : ∀ t ≥ t₇ + 1, (R.A t).reg.id = none := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base =>
        obtain ⟨w, hw, h1⟩ := R.reg_write hw₇
        rw [h1]; exact hwbot t₇ ht₇ hw₇ w hw
      | succ t ht ih =>
        rcases R.reg_step t with h1 | ⟨h2, w, hw, h1⟩
        · rw [h1]; exact ih
        · rw [h1]; exact hwbot t (by omega) h2 w hw
    obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ t₇ + 1) ℓ
    have hl3 : (R.A (t' + 1)).loc ℓ = procL n U (ids ℓ) ((R.A t'').loc ℓ) (R.A t'').reg
        (X.okc ℓ) (X.fc ℓ) := by rw [h3]; simp
    exact hgrow t'' (by omega) t' h2 _ _ _ (Or.inr ⟨hfr, rfl⟩) (hnone t'' h1)
      (hR5 t'' (by omega) (hnone t'' h1)) hℓok hl3

end LCtx

end BezoutElection.Alg2

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

namespace LCtx

variable {R : ARun n U ids} (X : LCtx R)
include X

/-- **The competition ends**: if some eligible process is eventually a non-loser forever, the
competition is won — which contradicts the hypotheses of `LCtx` (its level never changes). -/
theorem contra {c : P} (hcok : X.okc c = true) {T' : ℕ}
    (hc : ∀ t ≥ T', ((R.A t).loc c).lo = false) : False := by
  obtain ⟨T₁, hact⟩ := X.active
  obtain ⟨T₂, hT₂, hlos⟩ := X.losers hact
  set T₀ := max (max T₂ T') X.T with hT₀
  have hlos' : ∀ t ≥ T₀, ∀ q, ((R.A t).loc q).lo = ((R.A T₀).loc q).lo := by
    intro t ht q; rw [hlos t (by omega) q, hlos T₀ (by omega) q]
  by_cases hL : ∃ t ≥ T₀, ∃ ℓ, Lead n ids (R.A t) ℓ
  · obtain ⟨t₀, ht₀, ℓ, E⟩ := hL
    have hcℓ : c = ℓ := by
      by_contra hne
      have := (E.others c hne).2
      rw [hc t₀ (by omega)] at this; cases this
    subst hcℓ
    obtain ⟨t₁, ht₁, hC⟩ := X.phase2a (by omega : X.T ≤ t₀) E hcok
    exact X.phase2b (by omega : X.T ≤ t₁) (X.lead_forever E t₁ ht₁) hC hcok
  · push Not at hL
    refine X.phase1 (by omega : X.T ≤ T₀) (fun t ht => hact t (by omega)) hlos' (fun t ht => ?_)
      (hc T₀ (by omega)) hcok
    rcases (R.inv t).2 with N | ⟨ℓ, E⟩
    · exact N
    · exact absurd E (hL t ht ℓ)

end LCtx

end BezoutElection.Alg2
