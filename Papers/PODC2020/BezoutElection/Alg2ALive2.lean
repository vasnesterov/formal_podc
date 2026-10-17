import Papers.PODC2020.BezoutElection.Alg2ALive1
import Mathlib.Data.Finset.Max
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Algorithm 2: liveness of a competition, the electing phase

If no leader is ever determined (`NoLead` forever), but some eligible process (the global part
`okc` of its candidacy predicate holds) stays a non-loser, we get a contradiction. This is the
argument of Algorithm 1 (`Alg1Term.lean`, `phase1`) for a competition of Algorithm 2: the
losers and the `discarded` sets of the non-losers stabilize; an eligible non-loser `c₀` with
a minimal discarded set eventually cannot read `⊥` any more, stops writing, and is hidden by the
next write of another process.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-- All processes but `c` are in `D` ⇒ `n - 1 ≤ |D|`. -/
lemma card_ge_of_all (hid : Function.Injective ids) (hn : Fintype.card P = n) (D : Finset Id)
    (c : P) (h : ∀ j, j ≠ c → ids j ∈ D) : n - 1 ≤ D.card := by
  simpa [hn] using Finset.card_sub_card_le_of_injective_of_forall_notMem (F := {c}) hid
    fun j hj => h j (by simpa using hj)

lemma card_le_n (hn : Fintype.card P = n) (D : Finset Id) (h : ∀ a ∈ D, ∃ i, ids i = a) :
    D.card ≤ n := by
  have hsub : D ⊆ Finset.univ.image ids := by
    intro a ha; obtain ⟨i, rfl⟩ := h a ha; exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  calc D.card ≤ (Finset.univ.image ids).card := Finset.card_le_card hsub
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = n := by rw [Finset.card_univ, hn]

namespace LCtx

variable {R : ARun n U ids} (X : LCtx R)
include X

/-- A copy being processed by an active process is a value of the competition. -/
lemma val_of_proc {t : ℕ} {q : P} {v : Reg Id} (hact : ((R.A t).loc q).lv = X.L)
    (h : ((R.A t).loc q).st = .copy v ∨ (((R.A t).loc q).st = .fresh ∧ v = (R.A t).reg)) :
    (R.A t).Val v ∧ v.level = X.L := by
  have hl := X.copy_level h
  have hvL : v.level = X.L := by omega
  refine ⟨?_, hvL⟩
  rcases h with h | ⟨-, rfl⟩
  · exact Or.inr (Or.inr ⟨q, h, by rw [X.lev t]; exact hvL, by rw [X.lev t]; exact hact⟩)
  · exact Or.inl rfl

lemma not_mem_of_nonloser {t : ℕ} {q : P} {u : Reg Id} (hu : (R.A t).Val u)
    (hlo : ((R.A t).loc q).lo = false) : ids q ∉ u.disc := by
  intro h
  obtain ⟨i, hi, -, hl⟩ := (R.inv t).1.disc u hu _ h
  rw [X.hid hi, hlo] at hl; cases hl

/-- The outcomes of processing a value in the electing phase. -/
lemma proc_nolead {t : ℕ} {q : P} {v : Reg Id} (hN : NoLead n (R.A t))
    (hact : ((R.A t).loc q).lv = X.L)
    (h : ((R.A t).loc q).st = .copy v ∨ (((R.A t).loc q).st = .fresh ∧ v = (R.A t).reg))
    (ok fin : Bool) :
    (v.id = none ∧ ((R.A t).loc q).lo = false ∧ ok = true ∧
      procX n U (ids q) ((R.A t).loc q) v ok fin =
        ({ (R.A t).loc q with ca := true, D := ((R.A t).loc q).D ∪ v.disc },
         some ⟨some (ids q), ((R.A t).loc q).D ∪ v.disc, ((R.A t).loc q).ph, v.level, v.leaders⟩)) ∨
    procX n U (ids q) ((R.A t).loc q) v ok fin = ((R.A t).loc q, none) ∨
    (∃ a, v.id = some a ∧ a ≠ ids q ∧ ids q ∉ v.disc ∧
      procX n U (ids q) ((R.A t).loc q) v ok fin =
        ({ (R.A t).loc q with ca := false, lo := true, D := insert (ids q) v.disc },
         some ⟨none, insert (ids q) v.disc, ((R.A t).loc q).ph, v.level, v.leaders⟩)) := by
  obtain ⟨hV, hvL⟩ := X.val_of_proc hact h
  obtain ⟨hvE, hvc⟩ := hN.valsEl v hV
  have hph := hN.phEl q (by rw [X.lev t]; exact hact)
  have h1 : v.level = ((R.A t).loc q).lv := by rw [hvL, hact]
  have h2 : v.level < U := by rw [hvL]; exact X.hLU
  have h3 : ¬(v.phase = .committing ∧ ((R.A t).loc q).ph = .electing) := by rw [hvE]; simp
  have h4 : ¬(v.disc.card = n - 1 ∧ v.id ≠ none) := fun ⟨h5, h6⟩ => hvc h6 h5
  cases hid : v.id with
  | none =>
    by_cases hc : ((R.A t).loc q).lo = false ∧ ok = true
    · left
      refine ⟨rfl, hc.1, hc.2, ?_⟩
      rw [procX_bot h1 h2 h3 hid hc.1 hc.2, if_pos (by rw [hvE, hph])]
    · right; left
      refine procX_bot_noop h1 h2 h3 hid ?_
      cases h5 : ((R.A t).loc q).lo
      · cases h6 : ok
        · exact Or.inr rfl
        · exact absurd ⟨h5, h6⟩ hc
      · exact Or.inl rfl
  | some a =>
    by_cases hm : ids q ∈ v.disc ∨ a = ids q
    · right; left
      exact procX_noop_mem h1 h2 h3 h4 (by simp [hid]) (by
        rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr (by rw [hid, hm]))
    · push Not at hm
      right; right
      exact ⟨a, rfl, hm.2, hm.1, procX_lose h1 h2 h3 h4 hid hm.2 hm.1⟩

/-- The conditions of the `if`s of `procX` for a value of the electing phase. -/
lemma val_conds {t : ℕ} {q : P} {v : Reg Id} (hN : NoLead n (R.A t))
    (hact : ((R.A t).loc q).lv = X.L) (hV : (R.A t).Val v) (hvL : v.level = X.L) :
    v.level = ((R.A t).loc q).lv ∧ v.level < U ∧
      ¬(v.phase = .committing ∧ ((R.A t).loc q).ph = .electing) ∧
      ¬(v.disc.card = n - 1 ∧ v.id ≠ none) ∧ v.phase = ((R.A t).loc q).ph := by
  obtain ⟨hvE, hvc⟩ := hN.valsEl v hV
  have hph := hN.phEl q (by rw [X.lev t]; exact hact)
  exact ⟨by rw [hvL, hact], by rw [hvL]; exact X.hLU, by rw [hvE]; simp,
    fun ⟨h5, h6⟩ => hvc h6 h5, by rw [hvE, hph]⟩

/-- **The electing phase ends**: if no leader is ever determined from `T₀` on, and the
eligible process `c` stays a non-loser, we get a contradiction. -/
theorem phase1 {T₀ : ℕ} (hT₀ : X.T ≤ T₀) (hact : ∀ t ≥ T₀, ∀ q, ((R.A t).loc q).lv = X.L)
    (hlos : ∀ t ≥ T₀, ∀ q, ((R.A t).loc q).lo = ((R.A T₀).loc q).lo)
    (hN : ∀ t ≥ T₀, NoLead n (R.A t)) {c : P} (hc : ((R.A T₀).loc c).lo = false)
    (hcok : X.okc c = true) : False := by
  have hok : ∀ t ≥ T₀, ∀ q ok fin, (R.tr t = .proc ok fin ∨ R.tr t = .readProc ok fin) →
      R.who t = q → ok = X.okc q := by
    intro t ht q ok fin h hw; rw [← hw]; exact (X.stab t (by omega) ok fin h).1
  -- the discarded sets of the non-losers grow
  have hDmono : ∀ t ≥ T₀, ∀ q, ((R.A T₀).loc q).lo = false →
      ((R.A t).loc q).D ⊆ ((R.A (t + 1)).loc q).D := by
    intro t ht q hq
    rcases X.loc_cases t q with h | ⟨-, -, h⟩ | ⟨-, v, ok, fin, hv, h, -⟩ | ⟨-, w, -, h⟩
    · rw [h]
    · rw [h]
    · rcases X.proc_nolead (hN t ht) (hact t ht q) hv ok fin with ⟨-, -, -, e⟩ | e | ⟨a, -, -, -, e⟩
      · rw [h]; simp only [procL, e]; exact Finset.subset_union_left
      · rw [h]; simp only [procL, e]; exact Finset.Subset.refl _
      · exfalso
        have h1 := hlos (t + 1) (by omega) q
        rw [h, hq] at h1; simp only [procL, e] at h1; cases h1
    · rw [h]
  have hD : ∀ q, ∃ T, ∀ t ≥ T, ((R.A T₀).loc q).lo = false →
      ((R.A (t + 1)).loc q).D = ((R.A t).loc q).D := by
    intro q
    by_cases hq : ((R.A T₀).loc q).lo = false
    · obtain ⟨T, -, hTc⟩ := Finset.eventually_const_of_subset_succ
        (f := fun t => ((R.A t).loc q).D) (N := T₀) (h := fun t ht => hDmono t ht q hq)
        (hB := fun t ht => card_le_n X.hn _ (fun a ha => by
          obtain ⟨i, hi, -⟩ := (R.inv t).1.discLoc q (by rw [X.lev t]; exact hact t ht q) a ha
          exact ⟨i, hi⟩))
      exact ⟨T, fun t ht _ => by rw [hTc t ht, hTc (t + 1) (by omega)]⟩
    · exact ⟨0, fun t _ h => absurd h hq⟩
  obtain ⟨T₂, hT₂, hT₂'⟩ := Nat.eventually_forall_of_finite hD T₀
  have hDc : ∀ t ≥ T₂, ∀ q, ((R.A T₀).loc q).lo = false →
      ((R.A t).loc q).D = ((R.A T₂).loc q).D := by
    intro t ht q hq
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [hT₂' t ht q hq, ih]
  -- an eligible non-loser with a minimal discarded set
  set S := Finset.univ.filter (fun q => ((R.A T₀).loc q).lo = false ∧ X.okc q = true) with hS
  have hSne : S.Nonempty := ⟨c, by simp [hS, hc, hcok]⟩
  obtain ⟨c₀, hc₀S, hc₀min⟩ := S.exists_min_image (fun q => ((R.A T₂).loc q).D.card) hSne
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hc₀S
  obtain ⟨hc₀l, hc₀ok⟩ := hc₀S
  set μ := ((R.A T₂).loc c₀).D.card with hμ
  have hmin : ∀ q, ((R.A T₀).loc q).lo = false → X.okc q = true →
      μ ≤ ((R.A T₂).loc q).D.card := fun q h1 h2 => hc₀min q (by simp [hS, h1, h2])
  have hnl : ∀ t ≥ T₀, ∀ q, ((R.A T₀).loc q).lo = false → ((R.A t).loc q).lo = false :=
    fun t ht q hq => by rw [hlos t ht q]; exact hq
  -- pending writes with an identifier have `≥ μ` discarded identifiers
  have F3 : ∀ t ≥ T₂, ∀ q w, ((R.A t).loc q).st = .pend w → w.id ≠ none →
      μ ≤ w.disc.card := by
    intro t ht q w hw hwid
    obtain ⟨-, h2, -, h4, h5⟩ := (R.inv t).1.pendId q w hw
      (by rw [X.nowin t q w hw, X.lev t]) hwid
    have hql : ((R.A T₀).loc q).lo = false := by rw [← hlos t (by omega) q]; exact h4
    rw [h2, hDc t ht q hql]
    exact hmin q hql (X.caok t (by omega) q h5)
  -- a pending write is eventually written
  have hwrite : ∀ t q w, ((R.A t).loc q).st = .pend w → ∃ t' ≥ t, R.tr t' = .write := by
    intro t q w hw
    obtain ⟨t', ht', -, -, h, -⟩ := X.next_write hw
    exact ⟨t', ht', h⟩
  -- infinitely many writes
  have hIW : ∀ t, ∃ t' ≥ t, R.tr t' = .write := by
    intro t
    by_contra hcon
    push Not at hcon
    set t₁ := max t T₂ with ht₁
    have hnw : ∀ t' ≥ t₁, R.tr t' ≠ .write := fun t' ht' => hcon t' (by omega)
    have hnp : ∀ t' ≥ t₁, ∀ q w, ((R.A t').loc q).st = .pend w → False := by
      intro t' ht' q w hw
      obtain ⟨t'', ht'', h⟩ := hwrite t' q w hw
      exact hnw t'' (by omega) h
    have hreg := X.reg_const hnw
    -- the process `q` processes the constant value of the register
    have hpr : ∀ q, ∃ t'' t', t₁ ≤ t'' ∧ t'' ≤ t' ∧ (R.A t'').reg = (R.A t₁).reg ∧
        ((R.A t'').loc q).st = .fresh ∧
        R.A (t' + 1) = (R.A t').upd q
          (procL n U (ids q) ((R.A t'').loc q) (R.A t'').reg (X.okc q) (X.fc q)) := by
      intro q
      obtain ⟨t'', t', h1, h2, h3, h4⟩ := X.read_proc (by omega : X.T ≤ t₁) q
      exact ⟨t'', t', h1, h2, hreg t'' h1, h3, h4⟩
    cases hid : (R.A t₁).reg.id with
    | none =>
      obtain ⟨t'', t', h1, h2, hr, hfr, h3⟩ := hpr c₀
      obtain ⟨c1, c2, c3, -, c5⟩ := X.val_conds (hN t'' (by omega)) (hact t'' (by omega) c₀)
        (Or.inl rfl) (X.lev t'')
      have e := procX_bot (n := n) (me := ids c₀) (ok := X.okc c₀) (fin := X.fc c₀) c1 c2 c3
        (by rw [hr, hid]) (hnl t'' (by omega) c₀ hc₀l) hc₀ok
      exact hnp (t' + 1) (by omega) c₀ _ (by rw [h3]; simp only [AState.upd_loc_self, procL, e, stOf]; rfl)
    | some a =>
      obtain ⟨ca, hca1, hca2, hca3⟩ := (R.inv t₁).1.regId a hid
      have hall : ∀ q, q ≠ ca → ids q ∈ (R.A t₁).reg.disc := by
        intro q hq
        by_contra hm
        obtain ⟨t'', t', h1, h2, hr, hfr, h3⟩ := hpr q
        obtain ⟨c1, c2, c3, c4, -⟩ := X.val_conds (hN t'' (by omega)) (hact t'' (by omega) q)
          (Or.inl rfl) (X.lev t'')
        have e := procX_lose (n := n) (me := ids q) (ok := X.okc q) (fin := X.fc q) c1 c2 c3 c4
          (by rw [hr, hid]) (by rw [← hca1]; exact fun h => hq (X.hid h).symm)
          (by rw [hr]; exact hm)
        exact hnp (t' + 1) (by omega) q _ (by rw [h3]; simp only [AState.upd_loc_self, procL, e, stOf]; rfl)
      have hge := card_ge_of_all X.hid X.hn _ ca hall
      have hle : (R.A t₁).reg.disc.card ≤ n - 1 := card_le_of_ne X.hn _ ca (fun x hx => by
        obtain ⟨j, hj, -, hl⟩ := (R.inv t₁).1.disc _ (Or.inl rfl) x hx
        exact ⟨j, hj, by rintro rfl; rw [hca3] at hl; cases hl⟩)
      exact ((hN t₁ (by omega)).valsEl _ (Or.inl rfl)).2 (by rw [hid]; simp) (by omega)
  -- level 1: values with an identifier in the register
  obtain ⟨T₃, hT₃, hR1⟩ := X.ev_write
    (fun t => (R.A t).reg.id ≠ none → μ ≤ (R.A t).reg.disc.card) T₂
    (fun t ht hR ha => by
      rcases R.reg_step t with h1 | ⟨-, w, hw, h1⟩
      · rw [h1] at ha ⊢; exact hR ha
      · rw [h1] at ha ⊢; exact F3 t ht _ w hw ha)
    (fun t ht hwt ha => by
      obtain ⟨w, hw, h1⟩ := R.reg_write hwt
      rw [h1] at ha ⊢; exact F3 t ht _ w hw ha) hIW
  -- level 2: pending `⊥`-writes and copies with an identifier
  have hQ2 : ∀ q, ∃ T, ∀ t ≥ T,
      (∀ w, ((R.A t).loc q).st = .pend w → w.id = none → μ < w.disc.card) ∧
      (∀ v, ((R.A t).loc q).st = .copy v → v.id ≠ none → μ ≤ v.disc.card) := by
    intro q
    -- processing a value with the right property
    have hres : ∀ t ≥ T₃, ∀ v ok fin,
        (((R.A t).loc q).st = .copy v ∨ (((R.A t).loc q).st = .fresh ∧ v = (R.A t).reg)) →
        (v.id ≠ none → μ ≤ v.disc.card) →
        ∀ w, (procL n U (ids q) ((R.A t).loc q) v ok fin).st = .pend w → w.id = none →
          μ < w.disc.card := by
      intro t ht v ok fin hv hgood w hw hwid
      rcases X.proc_nolead (hN t (by omega)) (hact t (by omega) q) hv ok fin with
        ⟨-, -, -, e⟩ | e | ⟨a, ha, -, hni, e⟩
      · simp only [procL, e, stOf, AStatus.pend.injEq] at hw; rw [← hw] at hwid; cases hwid
      · simp [procL, e, stOf] at hw
      · simp only [procL, e, stOf, AStatus.pend.injEq] at hw
        rw [← hw]; simp only
        rw [Finset.card_insert_of_notMem hni]
        have := hgood (by rw [ha]; simp)
        omega
    obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ T₃) q
    refine ⟨t' + 1, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base =>
      refine ⟨fun w hw hwid => ?_, fun v hv => ?_⟩
      · rw [h3] at hw; simp only [AState.upd_loc_self] at hw
        rw [← procL_st _ _ (.fresh) _ _ _] at hw
        have hl : ((R.A t'').loc q) = { (R.A t'').loc q with st := .fresh } := by
          rw [← hfr]
        rw [← hl] at hw
        exact hres t'' h1 _ _ _ (Or.inr ⟨hfr, rfl⟩) (hR1 t'' h1) w hw hwid
      · rw [h3] at hv; simp only [AState.upd_loc_self, procL] at hv
        cases ho : (procX n U (ids q) ((R.A t'').loc q) (R.A t'').reg (X.okc q) (X.fc q)).2 <;>
          simp [ho, stOf] at hv
    | succ t ht ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rcases X.loc_cases t q with h | ⟨-, -, h⟩ | ⟨-, v, ok, fin, hv, h, -⟩ | ⟨-, w, -, h⟩
      · rw [h]; exact ⟨ih1, ih2⟩
      · rw [h]; simp only
        refine ⟨fun w hw => (by cases hw), fun v hv hid => ?_⟩
        simp only [AStatus.copy.injEq] at hv; subst hv
        exact hR1 t (by omega) hid
      · rw [h]
        have hgood : v.id ≠ none → μ ≤ v.disc.card := by
          rcases hv with hv | ⟨-, rfl⟩
          · exact ih2 v hv
          · exact hR1 t (by omega)
        refine ⟨hres t (by omega) v ok fin hv hgood, fun v' hv' => ?_⟩
        simp only [procL] at hv'
        cases ho : (procX n U (ids q) ((R.A t).loc q) v ok fin).2 <;> simp [ho, stOf] at hv'
      · rw [h]; simp only
        exact ⟨fun w hw => (by cases hw), fun v hv => (by cases hv)⟩
  obtain ⟨T₄, hT₄, hQ2'⟩ := Nat.eventually_forall_of_finite hQ2 T₃
  -- level 2: `⊥`-values in the register
  obtain ⟨T₅, hT₅, hR2⟩ := X.ev_write
    (fun t => (R.A t).reg.id = none → μ < (R.A t).reg.disc.card) T₄
    (fun t ht hR ha => by
      rcases R.reg_step t with h1 | ⟨-, w, hw, h1⟩
      · rw [h1] at ha ⊢; exact hR ha
      · rw [h1] at ha ⊢; exact (hQ2' t ht _).1 w hw ha)
    (fun t ht hwt ha => by
      obtain ⟨w, hw, h1⟩ := R.reg_write hwt
      rw [h1] at ha ⊢; exact (hQ2' t ht _).1 w hw ha) hIW
  -- `c₀` only reads its own identifier
  set Good : Reg Id → Prop := fun v => (v.id ≠ none → μ ≤ v.disc.card) ∧
    (v.id = none → μ < v.disc.card) with hGood
  have hRG : ∀ t ≥ T₅, Good (R.A t).reg := fun t ht =>
    ⟨hR1 t (by omega), hR2 t ht⟩
  have hc₀l' : ∀ t ≥ T₀, ((R.A t).loc c₀).lo = false := fun t ht => hnl t ht c₀ hc₀l
  have hc₀proc : ∀ t ≥ T₅, ∀ t₂ ≥ t, ∀ v ok fin,
      (((R.A t).loc c₀).st = .copy v ∨ (((R.A t).loc c₀).st = .fresh ∧ v = (R.A t).reg)) →
      Good v → (R.A (t₂ + 1)).loc c₀ = procL n U (ids c₀) ((R.A t).loc c₀) v ok fin →
      ok = X.okc c₀ →
      v.id = some (ids c₀) ∧ procX n U (ids c₀) ((R.A t).loc c₀) v ok fin = ((R.A t).loc c₀, none) := by
    intro t ht t₂ ht₂ v ok fin hv hG hres hok'
    obtain ⟨hV, hvL⟩ := X.val_of_proc (hact t (by omega) c₀) hv
    obtain ⟨c1, c2, c3, c4, c5⟩ := X.val_conds (hN t (by omega)) (hact t (by omega) c₀) hV hvL
    cases hid : v.id with
    | none =>
      exfalso
      have e := procX_bot (n := n) (me := ids c₀) (ok := ok) (fin := fin) c1 c2 c3 hid
        (hc₀l' t (by omega)) (by rw [hok']; exact hc₀ok)
      have hD1 := hDc (t₂ + 1) (by omega) c₀ hc₀l
      have hD2 := hDc t (by omega) c₀ hc₀l
      rw [hres] at hD1
      simp only [procL, e, if_pos c5] at hD1
      have hsub : v.disc ⊆ ((R.A T₂).loc c₀).D := by
        rw [← hD1]; exact Finset.subset_union_right
      have h5 := Finset.card_le_card hsub
      have h6 := hG.2 hid
      omega
    | some a =>
      by_cases ha : a = ids c₀
      · subst ha
        exact ⟨rfl, procX_noop_mem c1 c2 c3 c4 (by simp [hid]) (Or.inr hid)⟩
      · exfalso
        have e := procX_lose (n := n) (me := ids c₀) (ok := ok) (fin := fin) c1 c2 c3 c4 hid ha
          (X.not_mem_of_nonloser hV (hc₀l' t (by omega)))
        have h1 := hc₀l' (t₂ + 1) (by omega)
        rw [hres] at h1; simp only [procL, e] at h1; cases h1
  -- eventually `c₀` never writes
  have hQc : ∃ T₆ ≥ T₅, ∀ t ≥ T₆, (∀ w, ((R.A t).loc c₀).st ≠ .pend w) ∧
      (∀ v, ((R.A t).loc c₀).st = .copy v → Good v) := by
    obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ T₅) c₀
    refine ⟨t' + 1, by omega, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base =>
      have hl3 : (R.A (t' + 1)).loc c₀ = procL n U (ids c₀) ((R.A t'').loc c₀) (R.A t'').reg
          (X.okc c₀) (X.fc c₀) := by rw [h3]; simp
      obtain ⟨-, e⟩ := hc₀proc t'' h1 t' h2 _ _ _ (Or.inr ⟨hfr, rfl⟩) (hRG t'' h1) hl3 rfl
      rw [hl3]; simp only [procL, e, stOf]
      exact ⟨fun w hw => (by cases hw), fun v hv => (by cases hv)⟩
    | succ t ht ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rcases X.loc_cases t c₀ with h | ⟨-, -, h⟩ | ⟨hw, v, ok, fin, hv, h, htr⟩ | ⟨-, w, hw, -⟩
      · rw [h]; exact ⟨ih1, ih2⟩
      · rw [h]; simp only
        refine ⟨fun w hw => (by cases hw), fun v hv => ?_⟩
        simp only [AStatus.copy.injEq] at hv; subst hv
        exact hRG t (by omega)
      · have hG : Good v := by
          rcases hv with hv | ⟨-, rfl⟩
          · exact ih2 v hv
          · exact hRG t (by omega)
        obtain ⟨-, e⟩ := hc₀proc t (by omega) t le_rfl v ok fin hv hG h
          (hok t (by omega) c₀ ok fin htr hw)
        rw [h]; simp only [procL, e, stOf]
        exact ⟨fun w hw => (by cases hw), fun v hv => (by cases hv)⟩
      · exact absurd hw (ih1 w)
  obtain ⟨T₆, hT₆, hQc'⟩ := hQc
  -- a write of another process hides `c₀` forever
  obtain ⟨t₇, ht₇, hw₇⟩ := hIW T₆
  have hwother : ∀ t ≥ T₆, R.tr t = .write → ∀ w, ((R.A t).loc (R.who t)).st = .pend w →
      w.id ≠ some (ids c₀) := by
    intro t ht _ w hw hid'
    have hwc : R.who t ≠ c₀ := by rintro h; rw [h] at hw; exact (hQc' t ht).1 w hw
    obtain ⟨h1, -⟩ := (R.inv t).1.pendId _ w hw (by rw [X.nowin t _ w hw, X.lev t])
      (by rw [hid']; simp)
    rw [hid'] at h1
    exact hwc (X.hid (Option.some.inj h1)).symm
  have hR3 : ∀ t ≥ t₇ + 1, (R.A t).reg.id ≠ some (ids c₀) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      obtain ⟨w, hw, h1⟩ := R.reg_write hw₇
      rw [h1]; exact hwother t₇ ht₇ hw₇ w hw
    | succ t ht ih =>
      rcases R.reg_step t with h1 | ⟨h2, w, hw, h1⟩
      · rw [h1]; exact ih
      · rw [h1]; exact hwother t (by omega) h2 w hw
  obtain ⟨t'', t', h1, h2, hfr, h3⟩ := X.read_proc (by omega : X.T ≤ t₇ + 1) c₀
  have hl3 : (R.A (t' + 1)).loc c₀ = procL n U (ids c₀) ((R.A t'').loc c₀) (R.A t'').reg
      (X.okc c₀) (X.fc c₀) := by rw [h3]; simp
  obtain ⟨hid', -⟩ := hc₀proc t'' (by omega) t' h2 _ _ _ (Or.inr ⟨hfr, rfl⟩) (hRG t'' (by omega))
    hl3 rfl
  exact hR3 t'' h1 hid'

end LCtx

end BezoutElection.Alg2
