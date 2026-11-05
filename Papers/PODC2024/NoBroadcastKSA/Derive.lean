import Papers.PODC2024.NoBroadcastKSA.Sim

/-!
# Executions of `A` on top of `S` derived from executions of `B`

Let `α` be an admissible execution of the implementation `B` in `CAMP_n[k-SA]` whose upper layer
runs copies of the k-SA algorithm `A` (`Sim.lean`). Keep only

* the broadcast events of the messages of a set `Ms` (the messages of selected copies), and
* the internal steps of the upper layer of the *active* processes from time `ws p` on (the start
  of the selected copy of `p`), turned into the decisions and idle steps of `A`.

The result (`derive`) is an execution of `A` on top of the broadcast abstraction. Its
broadcast events are the restriction of those of `α` to `Ms`, so if `B` implements `S` and `S`
is compositional, it is admitted by `S`; under the hypotheses of `derive_admissible` (the
selected copy of each active process sees exactly the selected messages) it is an admissible
execution of `A`, and the local history of an active process is the view of its copy
(`derive_hist`).
-/

namespace Podc.NoBroadcastKSA.Camp

open Classical

variable {P C V X O W : Type} [DecidableEq P] [DecidableEq C]

/-- The parameters of the copy of `A` run by the upper layer of each process. -/
structure CopyPar (P C V O : Type) where
  /-- the proposal -/
  v : P → V
  /-- the reset objects -/
  R : P → Set O
  /-- the foreign filter -/
  F : P → P → Msg C → Prop

variable (A : Algo P C V) (cp : CopyPar P C V O)

/-- The view of the copy of `p` at time `t` of `α`. -/
noncomputable def copyView (α : CExec P (Msg C) X O W) (p : P) (t : ℕ) :
    List (LEv P (Msg C) V) :=
  simView A p (cp.v p) (cp.R p) (cp.F p) (fhist α p t)

/-- The execution of `A` derived from `α`. -/
noncomputable def derive (α : CExec P (Msg C) X O W) (Ms : Set (P × Msg C)) (act : Set P)
    (ws : P → ℕ) (Cr : Set P) : AExec P (Msg C) V where
  st t := match α t with
    | some (.inv p m) => if (p, m) ∈ Ms then some (.b (.bc p m)) else none
    | some (.act p (.ret m)) => if (p, m) ∈ Ms then some (.b (.ret p m)) else none
    | some (.act p (.deliver q m)) => if (q, m) ∈ Ms then some (.b (.dl p q m)) else none
    | some (.up p) =>
      if p ∈ act ∧ ws p ≤ t then
        match A.act p (cp.v p) (copyView A cp α p t) with
        | some (.decide w) => some (.dec p w)
        | none => some (.tick p)
        | some (.bcast _) => none
      else none
    | _ => none
  correct := Cr
  inp := cp.v

/-- The hypotheses under which the selected copies see exactly the selected messages. -/
structure DeriveHyp (α : CExec P (Msg C) X O W) (Ms : Set (P × Msg C)) (act : Set P)
    (ws : P → ℕ) : Prop where
  /-- the broadcast events of `α` satisfy the basic properties (e.g. `α` is admissible for an
  implementation of a broadcast abstraction) -/
  bc : (proj α ∅).IsBroadcast
  /-- inactive processes have no selected events -/
  inactive : ∀ p ∉ act, ∀ t (m : Msg C), ((p, m) ∈ Ms → α t ≠ some (.inv p m)) ∧
    ((p, m) ∈ Ms → α t ≠ some (.act p (.ret m))) ∧
    ∀ q, (q, m) ∈ Ms → α t ≠ some (.act p (.deliver q m))
  /-- before `ws p`, an active process has no selected events -/
  before : ∀ p ∈ act, ∀ t < ws p, ∀ (m : Msg C), ((p, m) ∈ Ms → α t ≠ some (.inv p m)) ∧
    ((p, m) ∈ Ms → α t ≠ some (.act p (.ret m))) ∧
    ∀ q, (q, m) ∈ Ms → α t ≠ some (.act p (.deliver q m))
  /-- the copy starts at `ws p` with an empty view -/
  start : ∀ p ∈ act, copyView A cp α p (ws p) = []
  /-- the copy is not discarded after `ws p` -/
  noReset : ∀ p ∈ act, ∀ t ≥ ws p, ∀ o w, α t = some (.act p (.propose o w)) →
    ¬ (o ∈ cp.R p ∧ (copyView A cp α p t).any isDecL = false)
  /-- the selected messages of an active process are the ones its upper layer invokes from
  `ws p` on -/
  own : ∀ p ∈ act, ∀ m, (p, m) ∈ Ms ↔ ∃ t ≥ ws p, α t = some (.inv p m)
  /-- the copy sees exactly the selected foreign messages -/
  foreign : ∀ p ∈ act, ∀ t ≥ ws p, ∀ q m, q ≠ p → α t = some (.act p (.deliver q m)) →
    ((q, m) ∈ Ms ↔ cp.F p q m)
  /-- the upper layer invokes `broadcast` as its copy wants -/
  invAct : ∀ p ∈ act, ∀ t ≥ ws p, ∀ m, α t = some (.inv p m) →
    A.act p (cp.v p) (copyView A cp α p t) = some (.bcast m.2)

section Aux

variable {M : Type}

omit [DecidableEq P] in
lemma CStep.toB_eq_bc {s : CStep P M X O W} {q : P} {m : M} :
    s.toB = some (.bc q m) ↔ s = .inv q m := by
  rcases s with ⟨_, (_ | _ | _ | _ | _)⟩ | _ | _ | _ | _ <;> simp [CStep.toB]

omit [DecidableEq P] in
lemma CStep.toB_eq_ret {s : CStep P M X O W} {q : P} {m : M} :
    s.toB = some (.ret q m) ↔ s = .act q (.ret m) := by
  rcases s with ⟨_, (_ | _ | _ | _ | _)⟩ | _ | _ | _ | _ <;> simp [CStep.toB]

omit [DecidableEq P] in
lemma CStep.toB_eq_dl {s : CStep P M X O W} {q r : P} {m : M} :
    s.toB = some (.dl q r m) ↔ s = .act q (.deliver r m) := by
  rcases s with ⟨_, (_ | _ | _ | _ | _)⟩ | _ | _ | _ | _ <;> simp [CStep.toB]

end Aux

omit [DecidableEq C] in
/-- The broadcast events of the derived execution are those of `α` restricted to `Ms`. -/
theorem derive_proj (α : CExec P (Msg C) X O W) (Ms : Set (P × Msg C)) (act : Set P)
    (ws : P → ℕ) (Cr : Set P) :
    (derive A cp α Ms act ws Cr).proj = (proj α Cr).restrict Ms := by
  simp only [AExec.proj, BExec.restrict, proj, derive]
  congr 1
  funext t
  rcases α t with _ | ⟨q, a⟩ | ⟨q, m⟩ | ⟨q, r, x, s⟩ | ⟨q, o, w⟩ | q
  · rfl
  · rcases a with ⟨r, x⟩ | ⟨o, w⟩ | m | ⟨r, m⟩ | _ <;>
      simp [CStep.toB, BEv.msg, Step.toB] <;> split_ifs <;> simp_all [Step.toB]
  · simp [CStep.toB, BEv.msg, Step.toB]; split_ifs <;> simp_all [Step.toB]
  · rfl
  · rfl
  · simp only [CStep.toB]
    split_ifs
    · split <;> rfl
    · rfl

omit [DecidableEq C] in
lemma derive_st_b {α : CExec P (Msg C) X O W} {Ms : Set (P × Msg C)} {act : Set P}
    {ws : P → ℕ} {Cr : Set P} {t : ℕ} {e : BEv P (Msg C)} :
    (derive A cp α Ms act ws Cr).st t = some (.b e) ↔
      (∃ s, α t = some s ∧ s.toB = some e) ∧ e.msg ∈ Ms := by
  rw [← AExec.proj_ev_eq_some, derive_proj, BExec.restrict_ev_eq_some, proj_ev_eq_some]

omit [DecidableEq C] in
lemma derive_st_bc {α : CExec P (Msg C) X O W} {Ms : Set (P × Msg C)} {act : Set P}
    {ws : P → ℕ} {Cr : Set P} {t : ℕ} {q : P} {m : Msg C} :
    (derive A cp α Ms act ws Cr).st t = some (.b (.bc q m)) ↔
      α t = some (.inv q m) ∧ (q, m) ∈ Ms := by
  rw [derive_st_b]; simp [CStep.toB_eq_bc, BEv.msg]

omit [DecidableEq C] in
lemma derive_st_ret {α : CExec P (Msg C) X O W} {Ms : Set (P × Msg C)} {act : Set P}
    {ws : P → ℕ} {Cr : Set P} {t : ℕ} {q : P} {m : Msg C} :
    (derive A cp α Ms act ws Cr).st t = some (.b (.ret q m)) ↔
      α t = some (.act q (.ret m)) ∧ (q, m) ∈ Ms := by
  rw [derive_st_b]; simp [CStep.toB_eq_ret, BEv.msg]

omit [DecidableEq C] in
lemma derive_st_dl {α : CExec P (Msg C) X O W} {Ms : Set (P × Msg C)} {act : Set P}
    {ws : P → ℕ} {Cr : Set P} {t : ℕ} {q r : P} {m : Msg C} :
    (derive A cp α Ms act ws Cr).st t = some (.b (.dl q r m)) ↔
      α t = some (.act q (.deliver r m)) ∧ (r, m) ∈ Ms := by
  rw [derive_st_b]; simp [CStep.toB_eq_dl, BEv.msg]

omit [DecidableEq C] in
lemma derive_st_dec {α : CExec P (Msg C) X O W} {Ms : Set (P × Msg C)} {act : Set P}
    {ws : P → ℕ} {Cr : Set P} {t : ℕ} {q : P} {w : V}
    (hs : (derive A cp α Ms act ws Cr).st t = some (.dec q w)) :
    α t = some (.up q) ∧ q ∈ act ∧ ws q ≤ t ∧
      A.act q (cp.v q) (copyView A cp α q t) = some (.decide w) := by
  simp only [derive] at hs
  split at hs
  · split_ifs at hs; simp at hs
  · split_ifs at hs; simp at hs
  · split_ifs at hs; simp at hs
  · rename_i r hα
    split_ifs at hs with hr
    split at hs
    · rename_i w' hw
      cases hs
      exact ⟨hα, hr.1, hr.2, hw⟩
    · cases hs
    · cases hs
  · cases hs

omit [DecidableEq C] in
lemma derive_st_tick {α : CExec P (Msg C) X O W} {Ms : Set (P × Msg C)} {act : Set P}
    {ws : P → ℕ} {Cr : Set P} {t : ℕ} {q : P}
    (hs : (derive A cp α Ms act ws Cr).st t = some (.tick q)) :
    α t = some (.up q) ∧ q ∈ act ∧ ws q ≤ t ∧
      A.act q (cp.v q) (copyView A cp α q t) = none := by
  simp only [derive] at hs
  split at hs
  · split_ifs at hs; simp at hs
  · split_ifs at hs; simp at hs
  · split_ifs at hs; simp at hs
  · rename_i r hα
    split_ifs at hs with hr
    split at hs
    · cases hs
    · rename_i hw
      cases hs
      exact ⟨hα, hr.1, hr.2, hw⟩
    · cases hs
  · cases hs

omit [DecidableEq C] in
lemma copyView_succ_none {α : CExec P (Msg C) X O W} {p : P} {t : ℕ} (hα : α t = none) :
    copyView A cp α p (t + 1) = copyView A cp α p t := by
  simp [copyView, fhist, hα]

omit [DecidableEq C] in
lemma copyView_succ_other {α : CExec P (Msg C) X O W} {p : P} {t : ℕ}
    {s : CStep P (Msg C) X O W} (hα : α t = some s) (hs : s.proc ≠ p) :
    copyView A cp α p (t + 1) = copyView A cp α p t := by
  simp [copyView, fhist, hα, hs]

omit [DecidableEq C] in
lemma copyView_succ_self {α : CExec P (Msg C) X O W} {p : P} {t : ℕ}
    {s : CStep P (Msg C) X O W} (hα : α t = some s) (hs : s.proc = p) :
    copyView A cp α p (t + 1) =
      simStep A p (cp.v p) (cp.R p) (cp.F p) (copyView A cp α p t) s.floc := by
  simp only [copyView, fhist, hα, Option.bind_some, hs, ↓reduceIte, Option.toList_some]
  exact simView_append ..

omit [DecidableEq C] in
/-- The local history of an active process in the derived execution is the view of its
copy. -/
theorem derive_hist {α : CExec P (Msg C) X O W} {Ms : Set (P × Msg C)} {act : Set P}
    {ws : P → ℕ} {Cr : Set P} (h : DeriveHyp A cp α Ms act ws) {p : P} (hp : p ∈ act)
    {t : ℕ} (ht : ws p ≤ t) :
    (derive A cp α Ms act ws Cr).hist p t = copyView A cp α p t := by
  have hmem : ∀ t m, LEv.bc m ∈ (derive A cp α Ms act ws Cr).hist p t ↔
      ∃ s < t, α s = some (.inv p m) ∧ (p, m) ∈ Ms := by
    intro t m
    rw [AExec.mem_hist]
    constructor
    · rintro ⟨s, hs, he⟩
      obtain ⟨st, hst, hl⟩ := Option.bind_eq_some_iff.1 he
      rcases AExec.loc_eq_some hl with ⟨m', he', rfl⟩ | ⟨m', he', rfl⟩ | ⟨q, m', he', rfl⟩ |
          ⟨v, he', rfl⟩ <;> cases he'
      exact ⟨s, hs, (derive_st_bc A cp).1 hst⟩
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, by rw [(derive_st_bc A cp).2 ⟨h1, h2⟩]; simp [Step.loc]⟩
  induction t, ht using Nat.le_induction with
  | base =>
    rw [h.start p hp]
    refine List.eq_nil_iff_forall_not_mem.2 fun e he => ?_
    obtain ⟨s, hs, he⟩ := AExec.mem_hist.1 he
    obtain ⟨st, hst, hl⟩ := Option.bind_eq_some_iff.1 he
    rcases AExec.loc_eq_some hl with ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩ | ⟨q, m, rfl, rfl⟩ |
        ⟨v, rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := (derive_st_bc A cp).1 hst
      exact (h.before p hp s hs m).1 h2 h1
    · obtain ⟨h1, h2⟩ := (derive_st_ret A cp).1 hst
      exact (h.before p hp s hs m).2.1 h2 h1
    · obtain ⟨h1, h2⟩ := (derive_st_dl A cp).1 hst
      exact (h.before p hp s hs m).2.2 q h2 h1
    · have := (derive_st_dec A cp hst).2.2.1
      omega
  | succ t ht ih =>
    have hown : ∀ m, (p, m) ∈ Ms → (∃ s < t, α s = some (.inv p m)) →
        LEv.bc m ∈ copyView A cp α p t := by
      rintro m hm ⟨s, hs, h1⟩
      exact ih ▸ (hmem t m).2 ⟨s, hs, h1, hm⟩
    have hown' : ∀ m, LEv.bc m ∈ copyView A cp α p t → (p, m) ∈ Ms := by
      intro m hm
      obtain ⟨-, -, -, h2⟩ := (hmem t m).1 (ih ▸ hm)
      exact h2
    rw [AExec.hist, ih]
    rcases hα : α t with _ | s
    · rw [copyView_succ_none A cp hα]; simp [derive, hα]
    by_cases hq : s.proc = p
    swap
    · rw [copyView_succ_other A cp hα hq]
      rcases s with ⟨q, a⟩ | ⟨q, m⟩ | ⟨q, r, x, s⟩ | ⟨q, o, w⟩ | q <;>
        simp only [CStep.proc] at hq
      · rcases a with ⟨r, x⟩ | ⟨o, w⟩ | m | ⟨r, m⟩ | _ <;> simp [derive, hα, Step.loc, hq]
      · simp only [derive, hα]; split_ifs <;> simp [Step.loc, hq]
      · simp [derive, hα]
      · simp [derive, hα]
      · simp only [derive, hα]; split_ifs <;> (try split) <;> simp [Step.loc, hq]
    rw [copyView_succ_self A cp hα hq]
    rcases s with ⟨q, a⟩ | ⟨q, m⟩ | ⟨q, r, x, s⟩ | ⟨q, o, w⟩ | q <;>
      simp only [CStep.proc] at hq <;> subst hq
    · have hinv : ∀ m, (∃ t' < t, (proj α ∅).ev t' = some (.bc q m)) →
          ∃ s < t, α s = some (.inv q m) := by
        rintro m ⟨t', ht', h1⟩
        obtain ⟨st, h2, h3⟩ := proj_ev_eq_some.1 h1
        exact ⟨t', ht', CStep.toB_eq_bc.1 h3 ▸ h2⟩
      rcases a with ⟨r, x⟩ | ⟨o, w⟩ | m | ⟨r, m⟩ | _
      · simp [derive, hα, CStep.floc, CStep.bloc, simStep]
      · have := h.noReset q hp t ht o w hα
        simp only [derive, hα, CStep.floc, CStep.bloc, simStep]
        split_ifs
        simp
      · simp only [derive, hα, CStep.floc, CStep.bloc, simStep]
        by_cases hm : (q, m) ∈ Ms
        · have hb : LEv.bc m ∈ copyView A cp α q t :=
            hown m hm (hinv m (h.bc.wf.ret_bc t q m (proj_ev_eq_some.2 ⟨_, hα, rfl⟩)))
          simp [hm, hb, Step.loc]
        · have hb : LEv.bc m ∉ copyView A cp α q t := fun hb => hm (hown' m hb)
          simp [hm, hb]
      · simp only [derive, hα, CStep.floc, CStep.bloc, simStep]
        by_cases hr : r = q
        · subst hr
          by_cases hm : (r, m) ∈ Ms
          · have hb : LEv.bc m ∈ copyView A cp α r t :=
              hown m hm (hinv m (h.bc.validity t r r m (proj_ev_eq_some.2 ⟨_, hα, rfl⟩)))
            simp [hm, hb, Step.loc]
          · have hb : LEv.bc m ∉ copyView A cp α r t := fun hb => hm (hown' m hb)
            simp [hm, hb]
        · have hF := h.foreign q hp t ht r m hr hα
          by_cases hm : (r, m) ∈ Ms
          · simp [hm, hF.1 hm, hr, Step.loc]
          · have : ¬ cp.F q r m := fun h' => hm (hF.2 h')
            simp [hm, this, hr]
      · simp [derive, hα, CStep.floc, CStep.bloc, simStep]
    · simp [derive, hα, CStep.floc, CStep.bloc, simStep, (h.own q hp m).2 ⟨t, ht, hα⟩,
        Step.loc]
    · simp [derive, hα, CStep.floc, CStep.bloc, simStep]
    · simp [derive, hα, CStep.floc, CStep.bloc, simStep]
    · simp only [derive, hα, hp, ht, and_self, ↓reduceIte, CStep.floc, simStep]
      rcases hA : A.act q (cp.v q) (copyView A cp α q t) with _ | (m | w) <;> simp [Step.loc]

omit [DecidableEq C] in
/-- A step of the derived execution at `p` comes from a step of `p` in `α`. -/
lemma derive_proc {α : CExec P (Msg C) X O W} {Ms : Set (P × Msg C)} {act : Set P}
    {ws : P → ℕ} {Cr : Set P} {t : ℕ} {s : Step P (Msg C) V} {p : P}
    (hs : (derive A cp α Ms act ws Cr).st t = some s) (hp : s.aStep p ≠ none ∨ s.loc p ≠ none) :
    ∃ st, α t = some st ∧ st.proc = p := by
  rcases s with (⟨q, m⟩ | ⟨q, m⟩ | ⟨q, r, m⟩) | ⟨q, w⟩ | q
  · exact ⟨_, ((derive_st_bc A cp).1 hs).1, by simpa [Step.aStep, Step.loc, CStep.proc] using hp⟩
  · exact ⟨_, ((derive_st_ret A cp).1 hs).1, by simpa [Step.aStep, Step.loc, CStep.proc] using hp⟩
  · exact ⟨_, ((derive_st_dl A cp).1 hs).1, by simpa [Step.aStep, Step.loc, CStep.proc] using hp⟩
  · exact ⟨_, (derive_st_dec A cp hs).1, by simpa [Step.aStep, Step.loc, CStep.proc] using hp⟩
  · exact ⟨_, (derive_st_tick A cp hs).1, by simpa [Step.aStep, Step.loc, CStep.proc] using hp⟩

omit [DecidableEq C] in
/-- **The derived execution is an admissible execution of `A`.** -/
theorem derive_admissible {k : ℕ} {B : BAlgo P (Msg C) X O W} {S : Set (BExec P (Msg C))}
    (hS : Compositional S) (hB : Implements B k S) {Cr : Set P} {α : CExec P (Msg C) X O W}
    (hα : Adm B k Cr α) {Ms : Set (P × Msg C)} {act : Set P} {ws : P → ℕ}
    (h : DeriveHyp A cp α Ms act ws)
    (hfair : ∀ p ∈ Cr, p ∈ act ∧ ∀ t, ∃ t' ≥ t, ∃ s o,
      (derive A cp α Ms act ws Cr).st t' = some s ∧ s.aStep p = some o) :
    Admissible A S (derive A cp α Ms act ws Cr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [derive_proj]
    exact hS _ (hB Cr α hα) Ms
  · intro t p s o hs ho
    change A.act p (cp.v p) _ = _
    rcases AExec.aStep_eq_some ho with ⟨m, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := (derive_st_bc A cp).1 hs
      have hp : p ∈ act := by
        by_contra hp
        exact (h.inactive p hp t m).1 h2 h1
      have ht : ws p ≤ t := by
        by_contra ht
        exact (h.before p hp t (by omega) m).1 h2 h1
      rw [derive_hist A cp h hp ht, h.invAct p hp t ht m h1]
      rfl
    · obtain ⟨-, hp, ht, hA⟩ := derive_st_dec A cp hs
      rw [derive_hist A cp h hp ht, hA]
      rfl
    · obtain ⟨-, hp, ht, hA⟩ := derive_st_tick A cp hs
      rw [derive_hist A cp h hp ht, hA]
      rfl
  · intro p hp t
    exact (hfair p hp).2 t
  · intro p hp
    obtain ⟨T, hT⟩ := hα.crash p hp
    refine ⟨T, fun t ht s hs => ?_⟩
    by_contra hc
    obtain ⟨st, h1, h2⟩ := derive_proc A cp hs (not_and_or.1 hc)
    exact hT t ht st h1 h2

end Podc.NoBroadcastKSA.Camp
