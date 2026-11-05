import Papers.PODC2024.NoBroadcastKSA.Concat
import Papers.PODC2024.NoBroadcastKSA.Derive

/-!
# The copy of the final process decides, and decides its own proposal

`fin_copy`: in an admissible concatenation `catRun pars L fin` where only `fin.p` is correct, if
from local slot `w0` on the copy of `A` run by `fin.p` is never discarded and sees no foreign
message, then this copy decides (k-SA-Termination of `A`), and every decision it takes from
`w0` on is its own proposal (k-SA-Validity of `A`: it is the only participant of the derived
execution of `A`).
-/

namespace Podc.NoBroadcastKSA.Camp

set_option linter.unusedSectionVars false

open Classical

variable {P C V X O W : Type} [DecidableEq P] [DecidableEq C]
variable {A : Algo P C V} {B : BAlgo P (Msg C) X O W}

/-! ## Auxiliary lemmas -/

omit [DecidableEq P] in
lemma CStep.floc_eq_inv {M : Type} {s : CStep P M X O W} {m : M} :
    s.floc = .b (.inv m) ↔ ∃ p, s = .inv p m := by
  rcases s with _ | _ | _ | _ | _ <;> simp [CStep.floc, CStep.bloc]

omit [DecidableEq P] in
lemma CStep.floc_eq_ret {M : Type} {s : CStep P M X O W} {m : M} :
    s.floc = .b (.act (.ret m)) ↔ ∃ p, s = .act p (.ret m) := by
  rcases s with _ | _ | _ | _ | _ <;> simp [CStep.floc, CStep.bloc]

lemma mem_fhistA {M : Type} {α : CExec P M X O W} {p : P} {t : ℕ} {e : FLEv P M X O W} :
    e ∈ fhist α p t ↔ ∃ s < t, ∃ st, α s = some st ∧ st.proc = p ∧ st.floc = e := by
  induction t with
  | zero => simp [fhist]
  | succ t ih =>
    simp only [fhist, List.mem_append, ih, Option.mem_toList,
      Option.bind_eq_some_iff]
    constructor
    · rintro (⟨s, hs, st, h1, h2, h3⟩ | ⟨st, h1, h2⟩)
      · exact ⟨s, by omega, st, h1, h2, h3⟩
      · split_ifs at h2 with hp
        · cases h2; exact ⟨t, by omega, st, h1, hp, rfl⟩
    · rintro ⟨s, hs, st, h1, h2, h3⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact Or.inl ⟨s, hs, st, h1, h2, h3⟩
      · exact Or.inr ⟨st, h1, by simp [h2, h3]⟩

lemma isBroadcast_proj_empty {M : Type} {α : CExec P M X O W} {Cr : Set P}
    (h : (proj α Cr).IsBroadcast) : (proj α ∅).IsBroadcast :=
  ⟨h.validity, h.noDup, h.uniqueBc, ⟨h.wf.ret_bc, h.wf.ret_unique, h.wf.seq⟩, fun _ _ _ hp => absurd hp (Set.notMem_empty _),
    fun _ _ _ hp => absurd hp (Set.notMem_empty _)⟩

section Upper

variable (A) (par : RunPar P C V X O W)

lemma upperStep_of_not_bcast {h : List (FLEv P (Msg C) X O W)}
    (hh : ∀ c, A.act par.p par.v (simView A par.p par.v par.R par.F h) ≠ some (.bcast c)) :
    upperStep A par h = .up par.p := by
  unfold upperStep
  split
  · rename_i c hc; exact absurd hc (hh c)
  · rfl

lemma upperStep_eq_inv {h : List (FLEv P (Msg C) X O W)} {q : P} {m : Msg C}
    (hs : upperStep A par h = .inv q m) :
    q = par.p ∧ A.act par.p par.v (simView A par.p par.v par.R par.F h) = some (.bcast m.2) ∧
      noPend h := by
  unfold upperStep at hs
  split at hs
  · rename_i c hc
    split_ifs at hs with hn
    · cases hs; exact ⟨rfl, hc, hn⟩
  · cases hs

end Upper

/-- A step `inv` of a run comes from the upper layer, as its copy wants. -/
lemma prun_inv {par : RunPar P C V X O W} {off j : ℕ} {q : P} {m : Msg C}
    (h : prun A B par off j = some (.inv q m)) :
    j % 4 = 0 ∧ q = par.p ∧
      A.act par.p par.v (simView A par.p par.v par.R par.F (lst A B par j).h) =
        some (.bcast m.2) := by
  have hj : j % 4 = 0 := by
    by_contra hj
    have : j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    rcases this with h1 | h1 | h1
    · rw [prun_slot1 A B par off j h1] at h; cases h
    · rw [prun_slot2 A B par off j h1] at h
      split at h
      · (split_ifs at h; cases h)
      · cases h
      · cases h
    · -- slot 3 only receives messages
      unfold prun pstep at h
      simp only [show ¬ j % 4 = 0 by omega, show ¬ j % 4 = 1 by omega,
        show ¬ j % 4 = 2 by omega, ite_false] at h
      split at h
      · cases h
      · split_ifs at h
        all_goals (try split at h) <;> cases h
  refine ⟨hj, ?_⟩
  rw [prun_slot0 A B par off j hj] at h
  have := upperStep_eq_inv A par (Option.some.inj h)
  exact ⟨this.1, this.2.1⟩

/-! ## The copy of the final process -/

variable {S : Set (BExec P (Msg C))} {k : ℕ}

omit [DecidableEq P] in
lemma append_cons_eq {β : Type} {a b a' b' : List β} {x : β} (h : a ++ x :: b = a' ++ x :: b')
    (ha : x ∉ a) (hb : x ∉ b) : b = b' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simpa using h
    | cons y a'' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.2 ▸ by simp) hb
  | cons y a ih =>
    cases a' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) ha
    | cons y' a'' =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact ih h.2 (fun hx => ha (List.mem_cons_of_mem _ hx))

/-- An event of `p` at a time in `[u, t)` lies in the part of the history after time `u`. -/
lemma mem_after {α : CExec P (Msg C) X O W} {p : P} {t u rt : ℕ} {r : List (FLEv P (Msg C) X O W)}
    (hr : fhist α p t = fhist α p u ++ r) (hu : u ≤ rt) (ht : rt < t)
    {st : CStep P (Msg C) X O W} (hst : α rt = some st) (hp : st.proc = p) : st.floc ∈ r := by
  obtain ⟨r1, h1, -⟩ := fhist_split (α := α) (p := p) hu
  obtain ⟨r2, h2, -⟩ := fhist_split (α := α) (p := p) (show rt + 1 ≤ t by omega)
  have h3 : fhist α p (rt + 1) = fhist α p rt ++ [st.floc] := by simp [fhist, hst, hp]
  have e : fhist α p t = fhist α p u ++ (r1 ++ [st.floc] ++ r2) := by
    rw [h2, h3, h1]; simp [List.append_assoc]
  have : r = r1 ++ [st.floc] ++ r2 := List.append_cancel_left (hr.symm.trans e)
  rw [this]; simp

/-- **Fairness of the final process** in a derived execution: once the invocations of the
earlier copies have returned, every step of its upper layer is a step of `A`. -/
theorem fin_fair (hAwf : A.WellFormed) {m : ℕ} {pars : Fin m → RunPar P C V X O W}
    {L : Fin m → ℕ} {fin : RunPar P C V X O W} (hd : Distinct pars fin)
    (hbc : (proj (catRun A B pars L fin) {fin.p}).IsBroadcast)
    {cp : CopyPar P C V O} {Ms : Set (P × Msg C)} {act : Set P} {ws : P → ℕ} {Cr : Set P}
    (hDH : DeriveHyp A cp (catRun A B pars L fin) Ms act ws) (hfa : fin.p ∈ act) (w0 : ℕ)
    (hws : ws fin.p = segEnd L + w0)
    (hcv : ∀ t, copyView A cp (catRun A B pars L fin) fin.p t =
      simView A fin.p fin.v fin.R fin.F (fhist (catRun A B pars L fin) fin.p t))
    (hcpv : cp.v fin.p = fin.v)
    (hMs : ∀ t ≥ segEnd L + w0, ∀ m, catRun A B pars L fin t = some (.inv fin.p m) →
      (fin.p, m) ∈ Ms) :
    ∀ t, ∃ t' ≥ t, ∃ (s : Step P (Msg C) V) (o : Option (AAct (Msg C) V)),
      (derive A cp (catRun A B pars L fin) Ms act ws Cr).st t' = some s ∧
        s.aStep fin.p = some o := by
  set α := catRun A B pars L fin with hα
  set E := segEnd L with hE
  have hfh : ∀ j, fhist α fin.p (E + j) = (lst A B fin j).h := fun j =>
    fhist_catRun_fin A B pars L fin hd j
  have hinvU : ∀ t t' (q : P) (m : Msg C), α t = some (.inv q m) → α t' = some (.inv q m) →
      t = t' := fun t t' q m h h' =>
    hbc.uniqueBc t t' q m (proj_ev_eq_some.2 ⟨_, h, rfl⟩) (proj_ev_eq_some.2 ⟨_, h', rfl⟩)
  -- the invocations before the copy started return eventually
  have hdirty : ∀ N, ∃ J, ∀ s < N, ∀ m, α s = some (.inv fin.p m) →
      ∃ r, s < r ∧ r < J ∧ α r = some (.act fin.p (.ret m)) := by
    intro N
    induction N with
    | zero => exact ⟨0, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
    | succ N ih =>
      obtain ⟨J, hJ⟩ := ih
      by_cases hN : ∃ m, α N = some (.inv fin.p m)
      · obtain ⟨m0, hm0⟩ := hN
        obtain ⟨r, hr, hret⟩ := hbc.localTerm N fin.p m0 rfl (proj_ev_eq_some.2 ⟨_, hm0, rfl⟩)
        obtain ⟨s', hs', hb'⟩ := proj_ev_eq_some.1 hret
        rw [CStep.toB_eq_ret] at hb'
        subst hb'
        refine ⟨max J (r + 1), fun s hs m hm => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
        · obtain ⟨r', hr1, hr', h'⟩ := hJ s hs m hm
          exact ⟨r', hr1, by omega, h'⟩
        · rw [hm0] at hm
          cases hm
          exact ⟨r, hr, by omega, hs'⟩
      · push Not at hN
        exact ⟨J, fun s hs m hm => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
          · exact hJ s hs m hm
          · exact absurd hm (hN m)⟩
  obtain ⟨J, hJ⟩ := hdirty (E + w0)
  intro t
  set j := 4 * (t + J + w0 + 1) with hj
  have hj4 : j % 4 = 0 := by omega
  have hstep : α (E + j) = some (upperStep A fin (lst A B fin j).h) := by
    rw [hα, catRun_fin A B pars L fin (by omega), show E + j - E = j by omega]
    exact prun_slot0 A B fin _ j hj4
  have hws' : ws fin.p ≤ E + j := by rw [hws]; omega
  refine ⟨E + j, by omega, ?_⟩
  cases hact : A.act fin.p fin.v (simView A fin.p fin.v fin.R fin.F (lst A B fin j).h) with
  | none =>
    have hup : upperStep A fin (lst A B fin j).h = .up fin.p :=
      upperStep_of_not_bcast A fin (by intro c; rw [hact]; simp)
    refine ⟨.tick fin.p, none, ?_, by simp [Step.aStep]⟩
    simp only [derive, hstep, hup]
    rw [ite_eq_left ⟨hfa, hws'⟩, hcpv, hcv, hfh, hact]
  | some a =>
    rcases a with c | w
    · -- the copy wants to broadcast: no invocation is pending
      have hnp : noPend (lst A B fin j).h := by
        intro h₁ h₂ m hsplit
        by_contra hret
        rw [← hfh] at hsplit
        have hm : FLEv.b (.inv m) ∈ fhist α fin.p (E + j) := by rw [hsplit]; simp
        obtain ⟨s, hs, st, hst, hsp, hsf⟩ := mem_fhistA.1 hm
        obtain ⟨q, rfl⟩ := CStep.floc_eq_inv.1 hsf
        simp only [CStep.proc] at hsp
        subst hsp
        obtain ⟨r, hr, hrmem⟩ := fhist_split (α := α) (p := fin.p)
          (show s + 1 ≤ E + j by omega)
        have hs1 : fhist α fin.p (s + 1) = fhist α fin.p s ++ [FLEv.b (.inv m)] := by
          simp [fhist, hst, CStep.proc, CStep.floc, CStep.bloc]
        have hnotin1 : FLEv.b (.inv m) ∉ fhist α fin.p s := by
          intro h'
          obtain ⟨s', hs', st', hst', hsp', hsf'⟩ := mem_fhistA.1 h'
          obtain ⟨q', rfl⟩ := CStep.floc_eq_inv.1 hsf'
          simp only [CStep.proc] at hsp'
          subst hsp'
          have := hinvU s' s _ m hst' hst
          omega
        have hnotin2 : FLEv.b (.inv m) ∉ r := by
          intro h'
          obtain ⟨s', hs1', -, st', hst', hsp', hsf'⟩ := hrmem _ h'
          obtain ⟨q', rfl⟩ := CStep.floc_eq_inv.1 hsf'
          simp only [CStep.proc] at hsp'
          subst hsp'
          have := hinvU s' s _ m hst' hst
          omega
        have hr2 : fhist α fin.p (E + j) = fhist α fin.p s ++ FLEv.b (.inv m) :: r := by
          rw [hr, hs1]; simp
        have h2eq : r = h₂ := append_cons_eq (hr2.symm.trans hsplit) hnotin1 hnotin2
        subst h2eq
        have hretr : ∀ rt, s < rt → rt < E + j → α rt = some (.act fin.p (.ret m)) → False :=
          fun rt h1 h2 h3 => hret (by
            simpa [CStep.floc, CStep.bloc] using mem_after hr (by omega) h2 h3 rfl)
        by_cases hsw : s < E + w0
        · obtain ⟨rt, h1, h2, h3⟩ := hJ s hsw m hst
          exact hretr rt h1 (by omega) h3
        · have hMs' : (fin.p, m) ∈ Ms := hMs s (by omega) m hst
          have hbcD : LEv.bc m ∈ (derive A cp α Ms act ws Cr).hist fin.p (E + j) :=
            AExec.mem_hist.2 ⟨s, by omega, by
              rw [(derive_st_bc A cp).2 ⟨hst, hMs'⟩]; simp [Step.loc]⟩
          have hDh := derive_hist A cp (Cr := Cr) hDH (p := fin.p) hfa hws'
          rw [hDh, hcv, hfh] at hbcD
          have hretv := hAwf fin.p fin.v _ c hact m hbcD
          rw [← hfh, ← hcv, ← hDh] at hretv
          obtain ⟨rt, hrt, hr'⟩ := AExec.mem_hist.1 hretv
          obtain ⟨st', hst', hloc'⟩ : ∃ st', (derive A cp α Ms act ws Cr).st rt = some st' ∧
              st'.loc fin.p = some (.ret m) := by
            simpa [Option.bind_eq_some_iff] using hr'
          rcases AExec.loc_eq_some hloc' with ⟨_, he, _⟩ | ⟨_, he, hs'⟩ | ⟨_, _, he, _⟩ |
            ⟨_, he, _⟩ <;> cases he
          subst hs'
          obtain ⟨hαr, -⟩ := (derive_st_ret A cp).1 hst'
          obtain ⟨t'', ht'', h''⟩ := hbc.wf.ret_bc rt _ m (proj_ev_eq_some.2 ⟨_, hαr, rfl⟩)
          obtain ⟨s'', hs'', hb''⟩ := proj_ev_eq_some.1 h''
          rw [CStep.toB_eq_bc] at hb''
          subst hb''
          have := hinvU _ _ _ _ hs'' hst
          exact hretr rt (by omega) hrt hαr
      have hinv : upperStep A fin (lst A B fin j).h = .inv fin.p (nInv (lst A B fin j).h, c) := by
        unfold upperStep; rw [hact]; simp [hnp]
      refine ⟨.b (.bc fin.p (nInv (lst A B fin j).h, c)),
        some (.bcast (nInv (lst A B fin j).h, c)), ?_, by simp [Step.aStep]⟩
      rw [derive_st_bc, hstep, hinv]
      exact ⟨rfl, hMs (E + j) (by omega) _ (by rw [hstep, hinv])⟩
    · have hup : upperStep A fin (lst A B fin j).h = .up fin.p :=
        upperStep_of_not_bcast A fin (by intro c; rw [hact]; simp)
      refine ⟨.dec fin.p w, some (.decide w), ?_, by simp [Step.aStep]⟩
      simp only [derive, hstep, hup]
      rw [ite_eq_left ⟨hfa, hws'⟩, hcpv, hcv, hfh, hact]

/-- **The copy of the final process decides, and decides its own proposal.** -/
theorem fin_copy (hSb : IsBroadcastAbstraction S) (hS : Compositional S)
    (hA : SolvesKSA k A S) (hAwf : A.WellFormed) (hB : Implements B k S) {m : ℕ}
    {pars : Fin m → RunPar P C V X O W} {L : Fin m → ℕ} {fin : RunPar P C V X O W}
    (hd : Distinct pars fin) (hadm : Adm B k {fin.p} (catRun A B pars L fin)) (w0 : ℕ)
    (hw0 : simView A fin.p fin.v fin.R fin.F (lst A B fin w0).h = [])
    (hnr : ∀ t ≥ segEnd L + w0, ∀ o w,
      catRun A B pars L fin t = some (.act fin.p (.propose o w)) →
      ¬ (o ∈ fin.R ∧ (simView A fin.p fin.v fin.R fin.F
        (fhist (catRun A B pars L fin) fin.p t)).any isDecL = false))
    (hF : ∀ t q m, q ≠ fin.p →
      catRun A B pars L fin t = some (.act fin.p (.deliver q m)) → ¬ fin.F q m) :
    (∃ j, (simView A fin.p fin.v fin.R fin.F (lst A B fin j).h).any isDecL) ∧
      ∀ j ≥ w0, ∀ w, j % 4 = 0 →
        A.act fin.p fin.v (simView A fin.p fin.v fin.R fin.F (lst A B fin j).h) =
          some (.decide w) → w = fin.v := by
  set α := catRun A B pars L fin with hα
  set E := segEnd L with hE
  let cp : CopyPar P C V O := ⟨fun _ => fin.v, fun _ => fin.R, fun _ => fin.F⟩
  let Ms : Set (P × Msg C) := {x | x.1 = fin.p ∧ ∃ t ≥ E + w0, α t = some (.inv fin.p x.2)}
  let act : Set P := {fin.p}
  let ws : P → ℕ := fun _ => E + w0
  have hbc : (proj α {fin.p}).IsBroadcast := hSb _ (hB _ _ hadm)
  -- facts about the steps of the final process
  have hF1 : ∀ t (s : CStep P (Msg C) X O W), E ≤ t → α t = some s → s.proc = fin.p := by
    intro t s ht hs
    rw [hα, catRun_fin A B pars L fin ht] at hs
    exact prun_proc A B fin hs
  have hF2 : ∀ t (s : CStep P (Msg C) X O W), α t = some s → s.proc = fin.p → E ≤ t :=
    fun t s hs hp => catRun_proc_fin A B pars L fin hd hs hp
  have hinvU : ∀ t t' (q : P) (m : Msg C), α t = some (.inv q m) → α t' = some (.inv q m) →
      t = t' := fun t t' q m h h' =>
    hbc.uniqueBc t t' q m (proj_ev_eq_some.2 ⟨_, h, rfl⟩) (proj_ev_eq_some.2 ⟨_, h', rfl⟩)
  have hfh : ∀ j, fhist α fin.p (E + j) = (lst A B fin j).h := fun j =>
    fhist_catRun_fin A B pars L fin hd j
  have hcv : ∀ t, copyView A cp α fin.p t =
      simView A fin.p fin.v fin.R fin.F (fhist α fin.p t) := fun t => rfl
  have hDH : DeriveHyp A cp α Ms act ws := by
    refine ⟨isBroadcast_proj_empty hbc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp t m
      have hp' : p ≠ fin.p := hp
      refine ⟨fun hm => absurd hm.1 hp', fun hm => absurd hm.1 hp', ?_⟩
      rintro q ⟨rfl, t', ht', hinv⟩ hdl
      obtain ⟨t'', ht'', h''⟩ := hbc.validity t p _ m (proj_ev_eq_some.2 ⟨_, hdl, rfl⟩)
      obtain ⟨s'', hs'', hb''⟩ := proj_ev_eq_some.1 h''
      rw [CStep.toB_eq_bc] at hb''
      subst hb''
      have := hinvU _ _ _ _ hs'' hinv
      exact hp' (hF1 t _ (by omega) hdl)
    · intro p hp t ht m
      have hp' : p = fin.p := hp
      subst hp'
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨-, t', ht', hinv⟩ h
        have := hinvU _ _ _ _ h hinv
        simp only [ws] at ht; omega
      · rintro ⟨-, t', ht', hinv⟩ h
        obtain ⟨t'', ht'', h''⟩ := hbc.wf.ret_bc t _ m (proj_ev_eq_some.2 ⟨_, h, rfl⟩)
        obtain ⟨s'', hs'', hb''⟩ := proj_ev_eq_some.1 h''
        rw [CStep.toB_eq_bc] at hb''
        subst hb''
        have := hinvU _ _ _ _ hs'' hinv
        simp only [ws] at ht; omega
      · rintro q ⟨rfl, t', ht', hinv⟩ h
        obtain ⟨t'', ht'', h''⟩ := hbc.validity t _ _ m (proj_ev_eq_some.2 ⟨_, h, rfl⟩)
        obtain ⟨s'', hs'', hb''⟩ := proj_ev_eq_some.1 h''
        rw [CStep.toB_eq_bc] at hb''
        subst hb''
        have := hinvU _ _ _ _ hs'' hinv
        simp only [ws] at ht; omega
    · intro p hp
      have hp' : p = fin.p := hp
      subst hp'
      rw [hcv, hfh]; exact hw0
    · intro p hp t ht o w h
      have hp' : p = fin.p := hp
      subst hp'
      exact hnr t ht o w h
    · intro p hp m
      have hp' : p = fin.p := hp
      subst hp'
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨rfl, h⟩
    · intro p hp t _ q m hq h
      have hp' : p = fin.p := hp
      subst hp'
      constructor
      · rintro ⟨h1, -⟩; exact absurd h1 hq
      · intro h1; exact absurd h1 (hF t q m hq h)
    · intro p hp t ht m h
      have hp' : p = fin.p := hp
      subst hp'
      have hEt : E ≤ t := by simp only [ws] at ht; omega
      have h' := h
      rw [hα, catRun_fin A B pars L fin hEt] at h'
      obtain ⟨-, -, hact⟩ := prun_inv h'
      rw [hcv]
      obtain ⟨j, rfl⟩ : ∃ j, t = E + j := ⟨t - E, by omega⟩
      rw [hfh]
      simp only [show E + j - segEnd L = j by omega] at hact
      exact hact
  have hfair : ∀ p ∈ ({fin.p} : Set P), p ∈ act ∧ ∀ t, ∃ t' ≥ t, ∃ s o,
      (derive A cp α Ms act ws {fin.p}).st t' = some s ∧ s.aStep p = some o := by
    intro p hp
    have hp' : p = fin.p := hp
    subst hp'
    exact ⟨rfl, fin_fair hAwf hd hbc hDH rfl w0 rfl hcv rfl
      (fun t ht m h => ⟨rfl, t, ht, h⟩)⟩
  have hadmD := derive_admissible A cp hS hB hadm hDH hfair
  have hksa := hA _ hadmD
  constructor
  · obtain ⟨t, w, ht⟩ := hksa.termination fin.p rfl
    obtain ⟨hup, -, hwt, hw⟩ := derive_st_dec A cp ht
    have hEt : E ≤ t := hF2 t _ hup rfl
    obtain ⟨j, rfl⟩ : ∃ j, t = E + j := ⟨t - E, by omega⟩
    refine ⟨j + 1, ?_⟩
    have h1 := hup
    rw [hα, catRun_fin A B pars L fin hEt, show E + j - E = j by omega] at h1
    rw [lst_h_succ A B fin E j, h1]
    simp only [Option.map_some, Option.toList_some, CStep.floc]
    rw [simView_append]
    rw [hcv, hfh] at hw
    have hw' : A.act fin.p fin.v (simView A fin.p fin.v fin.R fin.F (lst A B fin j).h) =
        some (.decide w) := hw
    simp only [simStep]
    rw [hw']
    simp [isDecL]
  · intro j hj w hj4 hw
    have hup : upperStep A fin (lst A B fin j).h = .up fin.p :=
      upperStep_of_not_bcast A fin (by intro c; rw [hw]; simp)
    have hstep : α (E + j) = some (.up fin.p) := by
      rw [hα, catRun_fin A B pars L fin (by omega), show E + j - E = j by omega,
        prun_slot0 A B fin _ j hj4, hup]
    have hdec : (derive A cp α Ms act ws {fin.p}).st (E + j) = some (.dec fin.p w) := by
      simp only [derive, hstep]
      rw [ite_eq_left ⟨rfl, by simp only [ws]; omega⟩, hcv, hfh, hw]
    obtain ⟨q, hq, -⟩ := hksa.validity _ _ _ hdec
    exact hq.symm

end Podc.NoBroadcastKSA.Camp
