import Papers.PODC2020.BezoutElection.Alg2ARun

/-!
# Algorithm 2: liveness of a competition (basic facts)

Outcomes of `procX` in the situations met by the liveness proof, and basic facts on an abstract
run of a register whose level does not change: eventually all processes are at the current
level, the losers stabilize, and some eventuality patterns.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-! ### Outcomes of `procX` -/

section ProcX

variable {me : Id} {l : ALoc Id} {r : Reg Id} {ok fin : Bool}

lemma procX_bot (h1 : r.level = l.lv) (h2 : r.level < U)
    (h3 : ¬(r.phase = .committing ∧ l.ph = .electing)) (hid : r.id = none) (hlo : l.lo = false)
    (hok : ok = true) :
    procX n U me l r ok fin =
      ({ l with ca := true, D := if r.phase = l.ph then l.D ∪ r.disc else l.D },
       some ⟨some me, if r.phase = l.ph then l.D ∪ r.disc else l.D, l.ph, r.level, r.leaders⟩) := by
  unfold procX
  rw [if_pos ⟨h1, h2⟩, if_neg h3, if_neg (by simp [hid]), if_pos ⟨hid, hlo, hok⟩]

lemma procX_bot_noop (h1 : r.level = l.lv) (h2 : r.level < U)
    (h3 : ¬(r.phase = .committing ∧ l.ph = .electing)) (hid : r.id = none)
    (hno : l.lo = true ∨ ok = false) : procX n U me l r ok fin = (l, none) := by
  unfold procX
  rw [if_pos ⟨h1, h2⟩, if_neg h3, if_neg (by simp [hid]), if_neg (by
    rintro ⟨-, h4, h5⟩; rcases hno with h | h <;> simp_all), if_neg (by simp [hid])]

lemma procX_lose (h1 : r.level = l.lv) (h2 : r.level < U)
    (h3 : ¬(r.phase = .committing ∧ l.ph = .electing))
    (h4 : ¬(r.disc.card = n - 1 ∧ r.id ≠ none)) {a : Id} (hid : r.id = some a) (ha : a ≠ me)
    (hme : me ∉ r.disc) :
    procX n U me l r ok fin = ({ l with ca := false, lo := true, D := insert me r.disc },
      some ⟨none, insert me r.disc, l.ph, r.level, r.leaders⟩) := by
  unfold procX
  rw [if_pos ⟨h1, h2⟩, if_neg h3, if_neg h4, if_neg (by simp [hid]),
    if_pos ⟨by simp [hid], by simp [hid, ha], hme⟩]

lemma procX_noop_mem (h1 : r.level = l.lv) (h2 : r.level < U)
    (h3 : ¬(r.phase = .committing ∧ l.ph = .electing))
    (h4 : ¬(r.disc.card = n - 1 ∧ r.id ≠ none)) (hid : r.id ≠ none)
    (hme : me ∈ r.disc ∨ r.id = some me) : procX n U me l r ok fin = (l, none) := by
  unfold procX
  rw [if_pos ⟨h1, h2⟩, if_neg h3, if_neg h4, if_neg (by simp [hid]), if_neg (by
    rintro ⟨-, h5, h6⟩; rcases hme with h | h
    · exact h6 h
    · exact h5 h)]

lemma procX_commit (h1 : r.level = l.lv) (h2 : r.level < U) (h3 : r.phase = .committing)
    (h4 : l.ph = .electing) :
    procX n U me l r ok fin = ({ l with ph := .committing, D := ∅ }, none) := by
  unfold procX
  rw [if_pos ⟨h1, h2⟩, if_pos ⟨h3, h4⟩]

lemma procX_line8 (h1 : r.level = l.lv) (h2 : r.level < U)
    (h4 : r.disc.card = n - 1) (hid : r.id ≠ none) (h5 : r.phase = .electing) :
    procX n U me l r ok fin = (l, some ⟨none, ∅, .committing, r.level, r.leaders⟩) := by
  unfold procX
  rw [if_pos ⟨h1, h2⟩, if_neg (by rw [h5]; simp), if_pos ⟨h4, hid⟩, if_neg (by rw [h5]; simp)]

lemma procX_win (h1 : r.level = l.lv) (h2 : r.level < U)
    (h3 : ¬(r.phase = .committing ∧ l.ph = .electing))
    (h4 : r.disc.card = n - 1) (hid : r.id ≠ none) (h5 : r.phase = .committing) (hme : me ∉ r.disc) :
    (procX n U me l r ok fin).2 = some ⟨none, ∅, .electing, r.level + 1,
      if fin then insert me r.leaders else r.leaders⟩ := by
  unfold procX
  rw [if_pos ⟨h1, h2⟩, if_neg h3, if_pos ⟨h4, hid⟩, if_pos h5, if_pos hme]

/-- The local level grows by at most one. -/
lemma procX_lv : (procX n U me l r ok fin).1.lv = l.lv ∨
    ((procX n U me l r ok fin).1.lv = l.lv + 1 ∧ l.lv < r.level) := by
  rcases procX_cases n U me l r ok fin with
    ⟨-, h2, e⟩ | e | ⟨-, -, -, -, e⟩ | ⟨-, -, -, -, -, -, e⟩ |
    ⟨-, -, -, -, -, e⟩ | ⟨-, -, -, -, -, e⟩ | ⟨-, -, -, -, -, -, -, e⟩ <;> rw [e]
  · exact Or.inr ⟨rfl, h2⟩
  all_goals exact Or.inl rfl

/-- A process at the level of its copy stays a loser. -/
lemma procX_lo (h : r.level ≤ l.lv) (hlo : l.lo = true) : (procX n U me l r ok fin).1.lo = true := by
  rcases procX_cases n U me l r ok fin with
    ⟨-, h2, e⟩ | e | ⟨-, -, -, -, e⟩ | ⟨-, -, -, -, -, -, e⟩ |
    ⟨-, -, -, -, -, e⟩ | ⟨-, -, -, -, -, e⟩ | ⟨-, -, -, -, -, -, -, e⟩ <;> rw [e]
  · omega
  all_goals simpa using hlo

/-- A committing process at the level of its copy stays committing. -/
lemma procX_ph (h : r.level ≤ l.lv) (hph : l.ph = .committing) :
    (procX n U me l r ok fin).1.ph = .committing := by
  rcases procX_cases n U me l r ok fin with
    ⟨-, h2, e⟩ | e | ⟨-, -, -, -, e⟩ | ⟨-, -, -, -, -, -, e⟩ |
    ⟨-, -, -, -, -, e⟩ | ⟨-, -, -, -, -, e⟩ | ⟨-, -, -, -, -, -, -, e⟩ <;> rw [e]
  · omega
  all_goals simpa using hph

/-- A lagging process processing a copy of a higher level moves up. -/
lemma procX_up (h : l.lv < r.level) : (procX n U me l r ok fin).1.lv = l.lv + 1 := by
  rw [procX_lvup (by omega) h]

end ProcX

/-! ### Basic facts on runs of a competition -/

namespace LCtx0

variable {R : ARun n U ids} (X : LCtx0 R)
include X

/-- A local state evolves only by the transitions of its process. -/
lemma loc_step (t : ℕ) (q : P) : (R.A (t + 1)).loc q = (R.A t).loc q ∨
    (R.who t = q ∧ ((∃ s, (R.A (t + 1)).loc q = { (R.A t).loc q with st := s }) ∨
      ∃ v ok fin, (R.A (t + 1)).loc q = procL n U (ids q) ((R.A t).loc q) v ok fin ∧
        (((R.A t).loc q).st = .copy v ∨ (((R.A t).loc q).st = .fresh ∧ v = (R.A t).reg)))) := by
  by_cases hq : q = R.who t
  · right
    refine ⟨hq.symm, ?_⟩
    have hs := R.step t
    rw [← hq] at hs
    generalize R.tr t = tr at hs
    cases tr with
    | none => left; exact ⟨((R.A t).loc q).st, by rw [hs]⟩
    | read => left; exact ⟨.copy (R.A t).reg, by rw [hs.2]; simp [setSt]⟩
    | proc ok fin =>
      obtain ⟨v, h1, hs⟩ := hs
      right; exact ⟨v, ok, fin, by rw [hs]; simp, Or.inl h1⟩
    | readProc ok fin =>
      right; exact ⟨_, ok, fin, by rw [hs.2]; simp, Or.inr ⟨hs.1, rfl⟩⟩
    | write => obtain ⟨w, -, hs⟩ := hs; left; exact ⟨.fresh, by rw [hs]; simp [wr, setSt]⟩
  · left; exact R.other hq

/-- The possible evolutions of a local state. -/
lemma loc_cases (t : ℕ) (q : P) : (R.A (t + 1)).loc q = (R.A t).loc q ∨
    (R.who t = q ∧ ((R.A t).loc q).st = .fresh ∧
      (R.A (t + 1)).loc q = { (R.A t).loc q with st := .copy (R.A t).reg }) ∨
    (R.who t = q ∧ ∃ v ok fin, (((R.A t).loc q).st = .copy v ∨
        (((R.A t).loc q).st = .fresh ∧ v = (R.A t).reg)) ∧
      (R.A (t + 1)).loc q = procL n U (ids q) ((R.A t).loc q) v ok fin ∧
      (R.tr t = .proc ok fin ∨ R.tr t = .readProc ok fin)) ∨
    (R.who t = q ∧ ∃ w, ((R.A t).loc q).st = .pend w ∧
      (R.A (t + 1)).loc q = { (R.A t).loc q with st := .fresh }) := by
  by_cases hq : q = R.who t
  · have hs := R.step t
    rw [← hq] at hs
    generalize hg : R.tr t = tr at hs
    cases tr with
    | none => left; rw [hs]
    | read => right; left; exact ⟨hq.symm, hs.1, by rw [hs.2]; simp [setSt]⟩
    | proc ok fin =>
      obtain ⟨v, h1, hs⟩ := hs
      right; right; left; exact ⟨hq.symm, v, ok, fin, Or.inl h1, by rw [hs]; simp, Or.inl rfl⟩
    | readProc ok fin =>
      right; right; left
      exact ⟨hq.symm, _, ok, fin, Or.inr ⟨hs.1, rfl⟩, by rw [hs.2]; simp, Or.inr rfl⟩
    | write =>
      obtain ⟨w, h1, hs⟩ := hs
      right; right; right; exact ⟨hq.symm, w, h1, by rw [hs]; simp [wr, setSt]⟩
  · left; exact R.other hq

/-- The copy processed by a process is of a level at least its own. -/
lemma copy_level {t : ℕ} {q : P} {v : Reg Id}
    (h : ((R.A t).loc q).st = .copy v ∨ (((R.A t).loc q).st = .fresh ∧ v = (R.A t).reg)) :
    ((R.A t).loc q).lv ≤ v.level ∧ v.level ≤ X.L := by
  have hB := (R.inv t).1
  have hL := X.lev t
  rcases h with h | ⟨-, rfl⟩
  · have := hB.copyLv q v h
    rw [hL] at this; exact this
  · have := hB.lvLe q; rw [hL] at this ⊢; exact ⟨this, le_rfl⟩

lemma lv_mono (t : ℕ) (q : P) : ((R.A t).loc q).lv ≤ ((R.A (t + 1)).loc q).lv := by
  rcases X.loc_step t q with h | ⟨-, ⟨s, h⟩ | ⟨v, ok, fin, h, -⟩⟩
  · rw [h]
  · rw [h]
  · rw [h]; simp only [procL]
    rcases procX_lv (n := n) (U := U) (me := ids q) (l := (R.A t).loc q) (r := v) (ok := ok)
      (fin := fin) with h1 | ⟨h1, -⟩ <;> omega

lemma lv_le (t : ℕ) (q : P) : ((R.A t).loc q).lv ≤ X.L := by
  have := (R.inv t).1.lvLe q; rw [X.lev t] at this; exact this

/-- Eventually all processes are at the current level. -/
lemma active : ∃ T₁, ∀ t ≥ T₁, ∀ q, ((R.A t).loc q).lv = X.L := by
  have h : ∀ q, ∃ T', ∀ t ≥ T', ((R.A t).loc q).lv = X.L := by
    intro q
    obtain ⟨T', hT', hc⟩ := Nat.eventually_const_of_le_succ (f := fun t => ((R.A t).loc q).lv)
      (N := 0) (fun t _ => X.lv_le t q) (fun t _ => X.lv_mono t q)
    refine ⟨T', fun t ht => ?_⟩
    rw [hc t ht]
    by_contra hne
    have hlt : ((R.A T').loc q).lv < X.L := lt_of_le_of_ne (X.lv_le T' q) hne
    -- `q` reads the register and moves up
    obtain ⟨t', ht', hw, hr⟩ := X.fair q T'
    have hc' := hc t' ht'
    have hfr : ((R.A t').loc q).st = .fresh := by
      rcases hr with hr | ⟨ok, fin, hr⟩
      · have hs := R.step t'; rw [hr, hw] at hs; exact hs.1
      · have hs := R.step t'; rw [hr, hw] at hs; exact hs.1
    rcases R.act_fresh hfr hw (by rcases hr with hr | ⟨ok, fin, hr⟩ <;> rw [hr] <;> simp) with
      ⟨-, h2⟩ | ⟨ok, fin, -, h2⟩
    · -- the copy is processed later
      have hcp : ((R.A (t' + 1)).loc q).st = .copy (R.A t').reg := by rw [h2]; simp [setSt]
      obtain ⟨t'', ht'', hl, hw', ha⟩ := X.next_act q (t' + 1)
      obtain ⟨ok, fin, -, h3⟩ := R.act_copy (by rw [hl]; exact hcp) hw' ha
      have h4 := hc (t'' + 1) (by omega)
      rw [h3] at h4
      simp only [upd_loc_self, procL] at h4
      have h5 : ((R.A t'').loc q).lv = ((R.A T').loc q).lv := by
        rw [hl, h2]; simp [setSt, hc']
      rw [procX_up (by rw [h5, X.lev t']; exact hlt), h5] at h4
      omega
    · have h4 := hc (t' + 1) (by omega)
      rw [h2] at h4
      simp only [upd_loc_self, procL] at h4
      rw [procX_up (by rw [hc', X.lev t']; exact hlt), hc'] at h4
      omega
  obtain ⟨T₁, -, h1⟩ := Nat.eventually_forall_of_finite h 0
  exact ⟨T₁, fun t ht q => h1 t ht q⟩

/-- At the current level, losers stay losers. -/
lemma lo_mono {T₁ : ℕ} (hT₁ : ∀ t ≥ T₁, ∀ q, ((R.A t).loc q).lv = X.L) (t : ℕ) (ht : T₁ ≤ t)
    (q : P) (h : ((R.A t).loc q).lo = true) : ((R.A (t + 1)).loc q).lo = true := by
  rcases X.loc_step t q with h1 | ⟨-, ⟨s, h1⟩ | ⟨v, ok, fin, h1, hv⟩⟩
  · rw [h1]; exact h
  · rw [h1]; exact h
  · rw [h1]; simp only [procL]
    have := (X.copy_level hv).2
    exact procX_lo (by rw [hT₁ t ht q]; exact this) h

/-- At the current level, committing processes stay committing. -/
lemma ph_mono {T₁ : ℕ} (hT₁ : ∀ t ≥ T₁, ∀ q, ((R.A t).loc q).lv = X.L) (t : ℕ) (ht : T₁ ≤ t)
    (q : P) (h : ((R.A t).loc q).ph = .committing) : ((R.A (t + 1)).loc q).ph = .committing := by
  rcases X.loc_step t q with h1 | ⟨-, ⟨s, h1⟩ | ⟨v, ok, fin, h1, hv⟩⟩
  · rw [h1]; exact h
  · rw [h1]; exact h
  · rw [h1]; simp only [procL]
    have := (X.copy_level hv).2
    exact procX_ph (by rw [hT₁ t ht q]; exact this) h

/-- The losers eventually stabilize. -/
lemma losers {T₁ : ℕ} (hT₁ : ∀ t ≥ T₁, ∀ q, ((R.A t).loc q).lv = X.L) :
    ∃ T₂ ≥ T₁, ∀ t ≥ T₂, ∀ q, ((R.A t).loc q).lo = ((R.A T₂).loc q).lo := by
  obtain ⟨T₂, hT₂, hc⟩ := Finset.eventually_const_of_subset_succ_of_finite
    (f := fun t => Finset.univ.filter (fun q => ((R.A t).loc q).lo = true)) (N := T₁)
    (fun t ht q hq => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact X.lo_mono hT₁ t ht q hq)
  refine ⟨T₂, hT₂, fun t ht q => ?_⟩
  have := Finset.ext_iff.1 (hc t ht) q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact Bool.eq_iff_iff.2 this

/-- A property established by every write and preserved afterwards eventually holds forever,
provided there are infinitely many writes. -/
lemma ev_write (Q : ℕ → Prop) (t₀ : ℕ) (hpres : ∀ t ≥ t₀, Q t → Q (t + 1))
    (hw : ∀ t ≥ t₀, R.tr t = .write → Q (t + 1)) (hIW : ∀ t, ∃ t' ≥ t, R.tr t' = .write) :
    ∃ T ≥ t₀, ∀ t ≥ T, Q t := by
  obtain ⟨t, ht, hwt⟩ := hIW t₀
  exact Nat.eventually_of_imp_succ hpres ⟨t + 1, by omega, hw t ht hwt⟩

/-- If the register is not written from `t₁` on, it keeps its value. -/
lemma reg_const {t₁ : ℕ} (hnw : ∀ t ≥ t₁, R.tr t ≠ .write) (t : ℕ) (ht : t₁ ≤ t) :
    (R.A t).reg = (R.A t₁).reg := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rcases R.reg_step t with h | ⟨h, -⟩
    · rw [h, ih]
    · exact absurd h (hnw t ht)

end LCtx0

namespace LCtx

variable {R : ARun n U ids} (X : LCtx R)
include X

/-- Every process eventually reads the register and processes the value read. -/
lemma read_proc {t₁ : ℕ} (ht₁ : X.T ≤ t₁) (q : P) :
    ∃ t'' t', t₁ ≤ t'' ∧ t'' ≤ t' ∧ ((R.A t'').loc q).st = .fresh ∧
      R.A (t' + 1) = (R.A t').upd q
        (procL n U (ids q) ((R.A t'').loc q) (R.A t'').reg (X.okc q) (X.fc q)) := by
  obtain ⟨t'', ht'', hw, hr⟩ := X.fair q t₁
  have hfr : ((R.A t'').loc q).st = .fresh := by
    rcases hr with hr | ⟨ok, fin, hr⟩
    · have hs := R.step t''; rw [hr, hw] at hs; exact hs.1
    · have hs := R.step t''; rw [hr, hw] at hs; exact hs.1
  rcases R.act_fresh hfr hw (by rcases hr with hr | ⟨ok, fin, hr⟩ <;> rw [hr] <;> simp) with
    ⟨-, h2⟩ | ⟨ok, fin, h1, h2⟩
  · have hcp : ((R.A (t'' + 1)).loc q).st = .copy (R.A t'').reg := by rw [h2]; simp [setSt]
    obtain ⟨t', ht', hl, hw', h3⟩ := X.next_proc (by omega : X.T ≤ t'' + 1) hcp
    refine ⟨t'', t', ht'', by omega, hfr, ?_⟩
    rw [h3, h2]
    congr 1
    simp only [setSt, upd_loc_self]
    exact procL_st _ _ _ _ _ _
  · obtain ⟨rfl, rfl⟩ := X.stab t'' (by omega) ok fin (Or.inr h1)
    rw [hw] at h2
    exact ⟨t'', t'', ht'', le_rfl, hfr, h2⟩

end LCtx

end BezoutElection.Alg2
