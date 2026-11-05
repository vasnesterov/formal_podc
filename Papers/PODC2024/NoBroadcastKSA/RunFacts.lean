import Papers.PODC2024.NoBroadcastKSA.Adversary

/-!
# Facts about the run of one process

The steps of a process run (`prun`): what each kind of step looks like, uniqueness of
proposals, decisions and invocations, monotonicity of the "the copy has decided" flag, the slot
at which the copy decides, independence of the starting time, and the fact that the pending
messages do not matter before the copy decides.
-/

namespace Podc.NoBroadcastKSA.Camp

set_option linter.unusedSectionVars false

open Classical

variable {P C V X O W : Type} [DecidableEq P] [DecidableEq C]
variable (A : Algo P C V) (B : BAlgo P (Msg C) X O W) (par : RunPar P C V X O W)

/-- The copy of the run has decided after `j` slots. -/
def Decd (j : ℕ) : Prop :=
  (simView A par.p par.v par.R par.F (lst A B par j).h).any isDecL = true

lemma mem_lst_h (off : ℕ) {j : ℕ} {e : FLEv P (Msg C) X O W} :
    e ∈ (lst A B par j).h ↔ ∃ j' < j, ∃ s, prun A B par off j' = some s ∧ s.floc = e := by
  induction j with
  | zero => simp [lst, LSt.init]
  | succ j ih =>
    rw [lst_h_succ A B par off j, List.mem_append, ih]
    constructor
    · rintro (⟨j', hj', s, h1, h2⟩ | h)
      · exact ⟨j', by omega, s, h1, h2⟩
      · cases hp : prun A B par off j with
        | none => rw [hp] at h; simp at h
        | some s => rw [hp] at h; simp at h; exact ⟨j, by omega, s, hp, h.symm⟩
    · rintro ⟨j', hj', s, h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
      · exact Or.inl ⟨j', hj', s, h1, h2⟩
      · right; rw [h1]; simp [h2]

lemma lst_h_prefix {j j' : ℕ} (h : j ≤ j') : (lst A B par j).h <+: (lst A B par j').h := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rw [lst_h_succ A B par 0]
    exact ih.trans (List.prefix_append _ _)

/-- The steps of `B` in a run. -/
lemma prun_actR {off j : ℕ} {q : P} {a : BAct P (Msg C) X O W}
    (h : prun A B par off j = some (.act q a)) :
    j % 4 = 1 ∧ q = par.p ∧ a = B.next par.p (bview (lst A B par j).h) := by
  have : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases this with hj | hj | hj | hj
  · rw [prun_slot0 A B par off j hj] at h
    unfold upperStep at h
    split at h
    · split_ifs at h <;> cases h
    · cases h
  · rw [prun_slot1 A B par off j hj] at h
    cases h; exact ⟨hj, rfl, rfl⟩
  · rw [prun_slot2 A B par off j hj] at h
    split at h
    · (split_ifs at h; cases h)
    · cases h
    · cases h
  · exfalso
    unfold prun pstep at h
    simp only [show ¬ j % 4 = 0 by omega, show ¬ j % 4 = 1 by omega,
      show ¬ j % 4 = 2 by omega, ite_false] at h
    split at h
    · cases h
    · split_ifs at h
      all_goals (try split at h) <;> cases h

/-- The k-SA answers in a run. -/
lemma prun_dec {off j : ℕ} {q : P} {o : O} {w : W}
    (h : prun A B par off j = some (.dec q o w)) :
    j % 4 = 2 ∧ q = par.p ∧ ∃ w0, prun A B par off (j - 1) = some (.act par.p (.propose o w0)) ∧
      w = par.resp o w0 := by
  have : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases this with hj | hj | hj | hj
  · rw [prun_slot0 A B par off j hj] at h
    unfold upperStep at h
    split at h
    · split_ifs at h <;> cases h
    · cases h
  · rw [prun_slot1 A B par off j hj] at h; cases h
  · have h' := h
    rw [prun_slot2 A B par off j hj] at h
    split at h
    · (split_ifs at h; cases h)
    · rename_i o' w' hb
      cases h
      refine ⟨hj, rfl, w', ?_, rfl⟩
      rw [prun_slot1 A B par off (j - 1) (by omega), hb]
    · cases h
  · exfalso
    unfold prun pstep at h
    simp only [show ¬ j % 4 = 0 by omega, show ¬ j % 4 = 1 by omega,
      show ¬ j % 4 = 2 by omega, ite_false] at h
    split at h
    · cases h
    · split_ifs at h
      all_goals (try split at h) <;> cases h

/-- The steps `up` of a run come from the upper layer. -/
lemma prun_up {off j : ℕ} {q : P} (h : prun A B par off j = some (.up q)) :
    j % 4 = 0 ∧ upperStep A par (lst A B par j).h = .up q := by
  have : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases this with hj | hj | hj | hj
  · rw [prun_slot0 A B par off j hj] at h; exact ⟨hj, Option.some.inj h⟩
  · rw [prun_slot1 A B par off j hj] at h; cases h
  · rw [prun_slot2 A B par off j hj] at h
    split at h
    · (split_ifs at h; cases h)
    · cases h
    · cases h
  · exfalso
    unfold prun pstep at h
    simp only [show ¬ j % 4 = 0 by omega, show ¬ j % 4 = 1 by omega,
      show ¬ j % 4 = 2 by omega, ite_false] at h
    split at h
    · cases h
    · split_ifs at h
      all_goals (try split at h) <;> cases h

/-- A process proposes at most once to each object in a run. -/
lemma propose_once (hB : B.OneShot) {off j j' : ℕ} {o : O} {w w' : W}
    (h : prun A B par off j = some (.act par.p (.propose o w)))
    (h' : prun A B par off j' = some (.act par.p (.propose o w'))) : j = j' := by
  by_contra hne
  wlog hlt : j < j' generalizing j j' w w'
  · exact this h' h (Ne.symm hne) (by omega)
  obtain ⟨-, -, ha⟩ := prun_actR A B par h'
  have hmem : FLEv.b (.act (.propose o w)) ∈ (lst A B par j').h :=
    (mem_lst_h A B par off).2 ⟨j, hlt, _, h, rfl⟩
  have hmem' : CLEv.act (.propose o w) ∈ bview (lst A B par j').h := by
    simp only [bview, List.mem_filterMap]
    exact ⟨_, hmem, rfl⟩
  exact hB _ _ _ _ ha.symm w hmem'

/-- A process gets at most one answer from each object in a run. -/
lemma dec_once (hB : B.OneShot) {off j j' : ℕ} {q q' : P} {o : O} {w w' : W}
    (h : prun A B par off j = some (.dec q o w)) (h' : prun A B par off j' = some (.dec q' o w')) :
    j = j' := by
  obtain ⟨hj, -, w0, h0, -⟩ := prun_dec A B par h
  obtain ⟨hj', -, w0', h0', -⟩ := prun_dec A B par h'
  have := propose_once A B par hB h0 h0'
  omega

lemma nInv_appendR {M : Type} (h : List (FLEv P M X O W)) (e : FLEv P M X O W) :
    nInv (h ++ [e]) = nInv h + (match e with | .b (.inv _) => 1 | _ => 0) := by
  simp only [nInv, List.countP_append]
  rcases e with ((_ | _ | _ | _) | _ | _ | _) | _ <;> simp

lemma nInv_mono {j j' : ℕ} (h : j ≤ j') : nInv (lst A B par j).h ≤ nInv (lst A B par j').h := by
  obtain ⟨l, hl⟩ := lst_h_prefix A B par h
  rw [← hl]; simp only [nInv, List.countP_append]; omega

/-- A message is invoked at most once in a run. -/
lemma inv_once {off j j' : ℕ} {q q' : P} {m : Msg C}
    (h : prun A B par off j = some (.inv q m)) (h' : prun A B par off j' = some (.inv q' m)) :
    j = j' := by
  have key : ∀ {j : ℕ} {q : P} {m : Msg C}, prun A B par off j = some (.inv q m) →
      m.1 = nInv (lst A B par j).h ∧ nInv (lst A B par (j + 1)).h = m.1 + 1 := by
    intro j q m hh
    obtain ⟨hj, -, -⟩ := prun_inv hh
    have hh' := hh
    rw [prun_slot0 A B par off j hj] at hh
    unfold upperStep at hh
    split at hh
    · split_ifs at hh with hnp
      swap
      · cases hh
      cases hh
      refine ⟨rfl, ?_⟩
      rw [lst_h_succ A B par off j, hh']
      simp only [Option.map_some, Option.toList_some, nInv_appendR, CStep.floc, CStep.bloc]
    · cases hh
  by_contra hne
  wlog hlt : j < j' generalizing j j' q q'
  · exact this h' h (Ne.symm hne) (by omega)
  obtain ⟨h1, h2⟩ := key h
  obtain ⟨h1', -⟩ := key h'
  have := nInv_mono A B par (show j + 1 ≤ j' by omega)
  omega

/-! ## The decision flag of the copy -/

lemma simStep_any_mono {p : P} {v : V} {R : Set O} {F : P → Msg C → Prop}
    {view : List (LEv P (Msg C) V)} (e : FLEv P (Msg C) X O W) (h : view.any isDecL = true) :
    (simStep A p v R F view e).any isDecL = true := by
  rcases e with ((_ | ⟨o, w⟩ | m | ⟨q, m⟩ | _) | m | _ | _) | _ <;> simp only [simStep]
  all_goals first
    | exact h
    | (split_ifs <;> simp_all [List.any_append])
    | (split <;> simp_all [List.any_append])
    | simp [List.any_append, h]

lemma decd_mono {j j' : ℕ} (hjj : j ≤ j') (h : Decd A B par j) : Decd A B par j' := by
  induction hjj with
  | refl => exact h
  | step _ ih =>
    unfold Decd at *
    rw [lst_h_succ A B par 0]
    cases prun A B par 0 _ with
    | none => simpa using ih
    | some s =>
      simp only [Option.map_some, Option.toList_some]
      rw [simView_append]
      exact simStep_any_mono A _ ih

lemma simStep_any_of_not_up {p : P} {v : V} {R : Set O} {F : P → Msg C → Prop}
    {view : List (LEv P (Msg C) V)} {e : FLEv P (Msg C) X O W} (he : e ≠ .up)
    (h : view.any isDecL = false) : (simStep A p v R F view e).any isDecL = false := by
  rcases e with ((_ | ⟨o, w⟩ | m | ⟨q, m⟩ | _) | m | _ | _) | _ <;> simp only [simStep]
  all_goals first
    | exact h
    | exact absurd rfl he
    | (split_ifs <;> simp_all [List.any_append, isDecL])
    | simp [List.any_append, h, isDecL]

omit [DecidableEq P] in
lemma CStep.floc_eq_up {M : Type} {s : CStep P M X O W} : s.floc = .up ↔ ∃ q, s = .up q := by
  rcases s with _ | _ | _ | _ | _ <;> simp [CStep.floc, CStep.bloc]

/-- The copy decides at an `up` step of the upper layer, on the decision of `A`. -/
lemma decd_step {j : ℕ} (h0 : ¬ Decd A B par j) (h1 : Decd A B par (j + 1)) :
    j % 4 = 0 ∧ ∃ w, A.act par.p par.v (simView A par.p par.v par.R par.F (lst A B par j).h) =
      some (.decide w) := by
  unfold Decd at h0 h1
  have h0' : (simView A par.p par.v par.R par.F (lst A B par j).h).any isDecL = false := by
    simpa using h0
  rw [lst_h_succ A B par 0] at h1
  cases hp : prun A B par 0 j with
  | none => rw [hp] at h1; simp only [Option.map_none, Option.toList_none, List.append_nil] at h1
            exact absurd h1 h0
  | some s =>
    rw [hp] at h1
    simp only [Option.map_some, Option.toList_some] at h1
    rw [simView_append] at h1
    by_cases hu : s.floc = .up
    · obtain ⟨q, rfl⟩ := CStep.floc_eq_up.1 hu
      obtain ⟨hj, -⟩ := prun_up A B par hp
      refine ⟨hj, ?_⟩
      simp only [CStep.floc, simStep] at h1
      split at h1
      · rename_i w hw; exact ⟨w, hw⟩
      · exact absurd h1 h0
    · rw [simStep_any_of_not_up A hu h0'] at h1
      exact absurd h1 (by simp)

/-! ## Independence of the starting time -/

lemma prun_off {off off' j : ℕ} {s : CStep P (Msg C) X O W}
    (h : prun A B par off j = some s) (hs : ∀ p q x t, s ≠ .recv p q x t) :
    prun A B par off' j = some s := by
  have : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases this with hj | hj | hj | hj
  · rw [prun_slot0 A B par off j hj] at h; rw [prun_slot0 A B par off' j hj, h]
  · rw [prun_slot1 A B par off j hj] at h; rw [prun_slot1 A B par off' j hj, h]
  · rw [prun_slot2 A B par off j hj] at h; rw [prun_slot2 A B par off' j hj]
    split at h
    · split_ifs at h with hq
      · cases h; exact absurd rfl (hs _ _ _ _)
    · exact h
    · cases h
  · have e : prun A B par off j = prun A B par off' j := by
      unfold prun pstep
      simp only [show ¬ j % 4 = 0 by omega, show ¬ j % 4 = 1 by omega,
        show ¬ j % 4 = 2 by omega, ite_false]
    rw [← e, h]

/-! ## k-SA agreement from a bound on the deciders -/

omit [DecidableEq C] in
/-- If every value decided on `o` is decided by a member of a set of at most `k` processes, each
of which decides at most one value on `o`, then at most `k` values are decided on `o`. -/
lemma agree_of_bound {α : CExec P (Msg C) X O W} {k : ℕ} (o : O)
    (huniq : ∀ q t t' w w', α t = some (.dec q o w) → α t' = some (.dec q o w') → w = w')
    (Ps : Finset P) (hPs : Ps.card ≤ k)
    (hcov : ∀ t p w, α t = some (.dec p o w) → ∃ q ∈ Ps, ∃ t', α t' = some (.dec q o w))
    (f : Fin (k + 1) → W) (hf : Function.Injective f) :
    ¬ ∀ i, ∃ t p, α t = some (.dec p o (f i)) := by
  intro hall
  have hq : ∀ i, ∃ q ∈ Ps, ∃ t', α t' = some (.dec q o (f i)) := by
    intro i
    obtain ⟨t, p, ht⟩ := hall i
    exact hcov t p _ ht
  choose q hqP t' ht' using hq
  have hinj : Set.InjOn q (Finset.univ : Finset (Fin (k + 1))) := by
    intro i _ i' _ hii
    apply hf
    have h2 := ht' i'
    rw [← hii] at h2
    exact huniq _ _ _ _ _ (ht' i) h2
  have := Finset.card_le_card_of_injOn q (fun i _ => hqP i) hinj
  simp at this
  omega

/-! ## Decisions in a concatenation -/

section CatDec

variable {m : ℕ} (pars : Fin m → RunPar P C V X O W) (L : Fin m → ℕ) (fin : RunPar P C V X O W)

/-- A step of a concatenation is a step of the run of a segment, or of the final run. -/
lemma catRun_step (_hd : Distinct pars fin) {t : ℕ} {s : CStep P (Msg C) X O W}
    (h : catRun A B pars L fin t = some s) :
    (∃ i, s.proc = (pars i).p ∧ segOff L i ≤ t ∧ t < segOff L i + L i ∧
      prun A B (pars i) (segOff L i) (t - segOff L i) = some s) ∨
    (s.proc = fin.p ∧ segEnd L ≤ t ∧ prun A B fin (segEnd L) (t - segEnd L) = some s) := by
  by_cases ht : t < segEnd L
  · obtain ⟨i, h1, h2⟩ := exists_seg_of_lt_end L ht
    rw [catRun_seg A B pars L fin h1 h2] at h
    exact Or.inl ⟨i, prun_proc A B _ h, h1, h2, h⟩
  · rw [catRun_fin A B pars L fin (by omega)] at h
    exact Or.inr ⟨prun_proc A B _ h, by omega, h⟩

/-- A process gets at most one answer from each k-SA object in a concatenation. -/
lemma catRun_dec_uniq (hB : B.OneShot) (hd : Distinct pars fin) {q : P} {t t' : ℕ} {o : O}
    {w w' : W} (h : catRun A B pars L fin t = some (.dec q o w))
    (h' : catRun A B pars L fin t' = some (.dec q o w')) : w = w' := by
  rcases catRun_step A B pars L fin hd h with ⟨i, hp, h1, h2, h3⟩ | ⟨hp, h1, h3⟩ <;>
  rcases catRun_step A B pars L fin hd h' with ⟨i', hp', h1', h2', h3'⟩ | ⟨hp', h1', h3'⟩ <;>
    simp only [CStep.proc] at hp hp'
  · have hii : i = i' := hd.1 (by simp only; rw [← hp, ← hp'])
    subst hii
    have := dec_once A B _ hB h3 h3'
    have htt : t = t' := by omega
    subst htt; rw [h] at h'; cases h'; rfl
  · exact absurd (hp.symm.trans hp') (hd.2 i)
  · exact absurd (hp'.symm.trans hp) (hd.2 i')
  · have := dec_once A B _ hB h3 h3'
    have htt : t = t' := by omega
    subst htt; rw [h] at h'; cases h'; rfl

end CatDec

/-- A process run alone (every other process crashes initially). -/
noncomputable def solo (par : RunPar P C V X O W) : CExec P (Msg C) X O W :=
  catRun A B (m := 0) Fin.elim0 Fin.elim0 par

lemma solo_eq (par : RunPar P C V X O W) (t : ℕ) : solo A B par t = prun A B par 0 t := by
  unfold solo
  rw [catRun_fin A B _ _ par (by simp [segEnd])]
  simp [segEnd]

lemma distinct_solo (par : RunPar P C V X O W) :
    Distinct (Fin.elim0 : Fin 0 → RunPar P C V X O W) par :=
  ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- **A process run alone is admissible**, if the k-SA objects answer its own proposals and
it has no pending messages. -/
lemma solo_adm {k : ℕ} (hk : 1 ≤ k) (hB : B.OneShot) (par : RunPar P C V X O W)
    (hresp : ∀ o w, par.resp o w = w) (hnow : par.pendNow = []) (hlater : par.pendLater = []) :
    Adm B k {par.p} (solo A B par) := by
  unfold solo
  refine catRun_adm A B _ _ par hk hB (distinct_solo par) (fun i => i.elim0)
    (fun i => i.elim0) (fun o w => Or.inl (hresp o w)) ?_ ?_ ?_ ?_
  · intro q x s
    simp [hnow, hlater, segEnd]
  · simp [hnow, hlater]
  · intro h; exact absurd hlater h
  · intro o f hf
    refine agree_of_bound o (fun q t t' w w' h h' =>
      catRun_dec_uniq A B _ _ par hB (distinct_solo par) h h') {par.p} (by simp; omega)
      ?_ f hf
    intro t p w h
    refine ⟨par.p, by simp, t, ?_⟩
    rcases catRun_step A B _ _ par (distinct_solo par) h with ⟨i, -⟩ | ⟨hp, -⟩
    · exact i.elim0
    · simp only [CStep.proc] at hp; rw [← hp]; exact h

/-! ## Pending messages do not matter before the copy decides -/

/-- Two runs with the same parameters except for the sending times of the messages of
`pendNow` and for `pendLater` coincide until the copy decides. -/
lemma lst_agree (par par' : RunPar P C V X O W) (hp : par.p = par'.p) (hv : par.v = par'.v)
    (hR : par.R = par'.R) (hF : par.F = par'.F) (hresp : par.resp = par'.resp)
    (hnow : par.pendNow.map (fun e => (e.1, e.2.1)) = par'.pendNow.map (fun e => (e.1, e.2.1)))
    {J : ℕ} (hJ : ∀ j < J, ¬ Decd A B par' j) : ∀ j ≤ J, lst A B par j = lst A B par' j := by
  obtain ⟨p, v, R, F, resp, pn, pl⟩ := par
  obtain ⟨p', v', R', F', resp', pn', pl'⟩ := par'
  simp only at hp hv hR hF hresp hnow
  subst hp hv hR hF hresp
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have ih := ih (by omega)
    have hund := hJ j (by omega)
    rw [lst, lst, ih]
    unfold Decd at hund
    generalize lst A B ⟨p, v, R, F, resp, pn', pl'⟩ j = st at hund ⊢
    unfold pstep
    split_ifs with h0 h1 h2
    · rfl
    · rfl
    · rfl
    · simp only at hund ⊢
      have hlen : pn.length = pn'.length := by
        have := congrArg List.length hnow; simpa using this
      have hget : (pn[st.iNow]?).map (fun e => (e.1, e.2.1)) =
          (pn'[st.iNow]?).map (fun e => (e.1, e.2.1)) := by
        rw [← List.getElem?_map, ← List.getElem?_map, hnow]
      rcases h3 : pn[st.iNow]? with _ | ⟨q, x, s⟩ <;>
        rcases h4 : pn'[st.iNow]? with _ | ⟨q', x', s'⟩ <;> rw [h3, h4] at hget <;>
        simp at hget
      all_goals (obtain ⟨rfl, rfl⟩ := hget; simp)

end Podc.NoBroadcastKSA.Camp
