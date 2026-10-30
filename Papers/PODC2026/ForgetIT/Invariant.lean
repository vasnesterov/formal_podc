import Papers.PODC2026.ForgetIT.Frame

/-!
# Basic invariants of Forget-IT

`Inv prm F g` collects the bookkeeping invariants of the transition system of `Spec.lean`: the
local state of a correct process reflects every message it broadcast, received and accepted
messages from correct processes were really broadcast, every lock/decision is backed by a
quorum, the assessment variables `decision_alert`/`potential_decision` are backed by quorums of
`vote-2` messages, and the guard of the current view is set. They hold in every reachable state
(`reach_inv`) and only use `|F| ≤ f`.
-/

set_option linter.unusedSectionVars false

namespace Podc.ForgetIT

open Finset

variable {P Val : Type} [Fintype P] [DecidableEq P] [DecidableEq Val]
variable (prm : Params P) (F : Finset P)

/-- `2f + 1` processes, whose correct members broadcast `⟨vote-1, V, x⟩`. -/
def Q1 (g : GS P Val) (V : ℕ) (x : Val) : Prop :=
  ∃ S : Finset P, 2 * prm.f + 1 ≤ S.card ∧ ∀ r ∈ S, r ∉ F → (r, .vote1 V x) ∈ g.sent

/-- The basic invariant. -/
structure Inv (g : GS P Val) : Prop where
  refl : ∀ p ∉ F, ∀ m, (p, m) ∈ g.sent → Refl (g.loc p) m
  echoSent : ∀ p ∉ F, ∀ k V x, (g.loc p).echo k V = some x → (p, .echo k V x) ∈ g.sent
  rcv : ∀ p ∉ F, ∀ q m, (q, m) ∈ (g.loc p).rcv → q ∉ F → (q, m) ∈ g.sent
  acc : ∀ p ∉ F, ∀ V q l gd, (g.loc p).acc V q = some (l, gd) → q ∉ F →
    (q, .vote2 V l gd) ∈ g.sent
  accLock : ∀ p ∉ F, ∀ V q x, lockOf ((g.loc p).acc V q) = some x →
    ∃ r ∉ F, (r, .vote1 V x) ∈ g.sent
  lockQ : ∀ p ∉ F, ∀ V x, (g.loc p).lock V = some x → Q1 prm F g V x
  vote2Q : ∀ p ∉ F, ∀ V x gd, (g.loc p).vote2 V = some (some x, gd) → Q1 prm F g V x
  dec : ∀ e ∈ g.dec, e.1 ∉ F ∧ 1 ≤ e.2.1 ∧ ∃ S : Finset P, 2 * prm.f + 1 ≤ S.card ∧
    ∀ r ∈ S, r ∉ F → ∃ gd, (r, .vote2 e.2.1 (some e.2.2) gd) ∈ g.sent
  alertPot : ∀ p ∉ F, ∀ V, (g.loc p).alert V = some true → ∃ ℓ, (g.loc p).pot V = some ℓ
  potAlert : ∀ p ∉ F, ∀ V, (g.loc p).pot V ≠ none → (g.loc p).alert V ≠ none
  potW : ∀ p ∉ F, ∀ V ℓ, (g.loc p).pot V = some ℓ → ∃ S : Finset P, 2 * prm.f + 1 ≤ S.card ∧
    ∀ r ∈ S, r ∉ F → ∃ l gd, (r, .vote2 V l gd) ∈ g.sent ∧ (l = none ∨ l = some ℓ)
  falseW : ∀ p ∉ F, ∀ V, (g.loc p).alert V = some false → ∃ S : Finset P,
    2 * prm.f + 1 ≤ S.card ∧ ∀ r ∈ S, r ∉ F → ∃ l gd, (r, .vote2 V l gd) ∈ g.sent ∧
      (l = none ∨ ∃ ℓ, (g.loc p).pot V = some ℓ ∧ l ≠ some ℓ)
  guardV : ∀ p ∉ F, (g.loc p).guard (g.loc p).view ≠ none
  view1 : ∀ p ∉ F, 1 ≤ (g.loc p).view

/-! ### Counting helpers -/

variable {prm F}

/-- A set of more than `f ≥ |F|` senders has a correct member. -/
lemma exists_correct_of_snd (hF : F.card ≤ prm.f) {rcv : List (P × Msg Val)} {b : Msg Val → Bool}
    {th : ℕ} (hth : prm.f + 1 ≤ th) (h : th ≤ (snd rcv b).card) :
    ∃ r ∉ F, ∃ m, (r, m) ∈ rcv ∧ b m = true := by
  obtain ⟨r, hr, hrF⟩ :=
    Finset.exists_mem_notMem_of_card_le_of_lt (s := snd rcv b) hF (show prm.f < _ by omega)
  simp only [snd, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  obtain ⟨e, he, rfl, hb⟩ := hr
  exact ⟨e.1, hrF, e.2, he, hb⟩

lemma isVote1_eq {V : ℕ} {x : Val} {m : Msg Val} (h : isVote1 V x m = true) : m = .vote1 V x := by
  cases m <;> simp_all [isVote1]

lemma isVote2L_eq {V : ℕ} {x : Val} {m : Msg Val} (h : isVote2L V x m = true) :
    ∃ gd, m = .vote2 V (some x) gd := by
  cases m with
  | vote2 V' l g => cases l <;> simp_all [isVote2L]
  | _ => simp [isVote2L] at h

lemma isEcho_eq {k : Fin 3} {V : ℕ} {x : GV Val} {m : Msg Val} (h : isEcho k V x m = true) :
    ∃ y, m = .echo k V y ∧ (y = x ∨ y = .safe) := by
  cases m with
  | echo k' V' y => simp [isEcho] at h; obtain ⟨⟨rfl, rfl⟩, h⟩ := h; exact ⟨y, rfl, h⟩
  | _ => simp [isEcho] at h

/-- Members of `snd rcv b`. -/
lemma mem_snd {rcv : List (P × Msg Val)} {b : Msg Val → Bool} {r : P} (h : r ∈ snd rcv b) :
    ∃ m, (r, m) ∈ rcv ∧ b m = true := by
  simp only [snd, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨e, he, rfl, hb⟩ := h
  exact ⟨e.2, he, hb⟩

/-! ### Preservation -/

section act

variable {g : GS P Val} {p : P} {a : Act P Val}

lemma act_loc (q : P) :
    (g.act prm p a).loc q = if q = p then (exec prm p a (g.loc p)).1 else g.loc q := by
  simp [GS.act, Function.update_apply]

lemma act_loc_self : (g.act prm p a).loc p = (exec prm p a (g.loc p)).1 := by
  simp [act_loc]

lemma act_loc_ne {q : P} (h : q ≠ p) : (g.act prm p a).loc q = g.loc q := by
  simp [act_loc, h]

lemma act_sent {e : P × Msg Val} :
    e ∈ (g.act prm p a).sent ↔ e ∈ g.sent ∨ (e.1 = p ∧ e.2 ∈ (exec prm p a (g.loc p)).2) := by
  simp [GS.act]

lemma sent_sub_act {e : P × Msg Val} (h : e ∈ g.sent) : e ∈ (g.act prm p a).sent :=
  act_sent.2 (Or.inl h)

lemma Q1_mono {g g' : GS P Val} (hs : g.sent ⊆ g'.sent) {V : ℕ} {x : Val} (h : Q1 prm F g V x) :
    Q1 prm F g' V x := by
  obtain ⟨S, hS, hm⟩ := h
  exact ⟨S, hS, fun r hr hrF => hs (hm r hr hrF)⟩

end act

theorem inv_act (hF : F.card ≤ prm.f) {g : GS P Val} (hg : Inv prm F g) {p : P} (hp : p ∉ F)
    {a : Act P Val} (hen : En prm p a (g.loc p)) : Inv prm F (g.act prm p a) := by
  set s := g.loc p with hs
  have hsub : g.sent ⊆ (g.act prm p a).sent := fun e he => sent_sub_act he
  -- the quorum of senders of `vote-1` behind a lock
  have lockQ_new : ∀ v, En prm p (.lock v) s → Q1 prm F (g.act prm p a) s.view v := by
    intro v h
    refine ⟨snd s.rcv (isVote1 s.view v), h.1, fun r hr hrF => hsub ?_⟩
    obtain ⟨m, hm, hb⟩ := mem_snd hr
    rw [isVote1_eq hb] at hm
    exact hg.rcv p hp r _ hm hrF
  constructor
  · -- refl
    intro q hq m hm
    rcases act_sent.1 hm with hm1 | ⟨rfl, hm1⟩
    · by_cases hqp : q = p
      · subst hqp; rw [act_loc_self]; exact refl_exec prm q _ a hen (hg.refl q hq m hm1)
      · rw [act_loc_ne hqp]; exact hg.refl q hq m hm1
    · rw [act_loc_self]; exact mem_exec_refl prm _ _ a hm1
  · -- echoSent
    intro q hq k V x h
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h
      rcases exec_echo prm q s a k V with h' | ⟨h0, -⟩
      · rw [h'] at h; exact hsub (hg.echoSent q hq k V x h)
      · exact act_sent.2 (Or.inr ⟨rfl, exec_echo_msg prm q s a k V h0 h⟩)
    · rw [act_loc_ne hqp] at h; exact hsub (hg.echoSent q hq k V x h)
  · -- rcv
    intro q hq r m h hr
    by_cases hqp : q = p
    · subst hqp; rw [act_loc_self, exec_rcv] at h; exact hsub (hg.rcv q hq r m h hr)
    · rw [act_loc_ne hqp] at h; exact hsub (hg.rcv q hq r m h hr)
  · -- acc
    intro q hq V r l gd h hr
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h
      rcases exec_acc prm q s a V r with h' | ⟨l', g', rfl, h'⟩
      · rw [h'] at h; exact hsub (hg.acc q hq V r l gd h hr)
      · rw [h'] at h; cases h
        exact hsub (hg.rcv q hq r _ hen.1 hr)
    · rw [act_loc_ne hqp] at h; exact hsub (hg.acc q hq V r l gd h hr)
  · -- accLock
    intro q hq V r x h
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h
      rcases exec_acc prm q s a V r with h' | ⟨l', g', rfl, h'⟩
      · rw [h'] at h; obtain ⟨r', hr', h''⟩ := hg.accLock q hq V r x h; exact ⟨r', hr', hsub h''⟩
      · rw [h'] at h; simp only [lockOf, Option.bind_some] at h; subst h
        obtain ⟨r', hr', m, hm, hb⟩ := exists_correct_of_snd hF le_rfl (hen.2.2 x rfl)
        rw [isVote1_eq hb] at hm
        exact ⟨r', hr', hsub (hg.rcv q hq r' _ hm hr')⟩
    · rw [act_loc_ne hqp] at h; obtain ⟨r', hr', h''⟩ := hg.accLock q hq V r x h
      exact ⟨r', hr', hsub h''⟩
  · -- lockQ
    intro q hq V x h
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h
      rcases exec_lock prm q s a V with h' | ⟨v, rfl, rfl, h'⟩
      · rw [h'] at h; exact Q1_mono hsub (hg.lockQ q hq V x h)
      · rw [h'] at h; cases h; exact lockQ_new _ hen
    · rw [act_loc_ne hqp] at h; exact Q1_mono hsub (hg.lockQ q hq V x h)
  · -- vote2Q
    intro q hq V x gd h
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h
      rcases exec_vote2 prm q s a hen V with h' | ⟨-, l, g', h1, h2, -⟩
      · rw [h'] at h; exact Q1_mono hsub (hg.vote2Q q hq V x gd h)
      · rw [h1] at h; cases h
        rcases h2 x rfl with ⟨rfl, rfl⟩ | h3
        · exact lockQ_new _ hen
        · exact Q1_mono hsub (hg.lockQ q hq V x h3)
    · rw [act_loc_ne hqp] at h; exact Q1_mono hsub (hg.vote2Q q hq V x gd h)
  · -- dec
    intro e he
    simp only [GS.act, Set.mem_union] at he
    rcases he with he | he
    · obtain ⟨h1, h2, S, hS, hm⟩ := hg.dec e he
      exact ⟨h1, h2, S, hS, fun r hr hrF => (hm r hr hrF).imp fun _ h => hsub h⟩
    · cases a <;> simp [decEv] at he
      subst he
      refine ⟨hp, hg.view1 p hp, snd s.rcv (isVote2L s.view _), hen, fun r hr hrF => ?_⟩
      obtain ⟨m, hm, hb⟩ := mem_snd hr
      obtain ⟨gd, rfl⟩ := isVote2L_eq hb
      exact ⟨gd, hsub (hg.rcv p hp r _ hm hrF)⟩
  · -- alertPot
    intro q hq V h
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h ⊢
      rcases exec_alert prm q s a V with h' | ⟨ol, rfl, h'⟩ | ⟨-, h'⟩
      · rw [h'] at h; obtain ⟨ℓ, hℓ⟩ := hg.alertPot q hq V h
        rcases exec_pot prm q s (a) V with h'' | ⟨ℓ', -, h''⟩
        · exact ⟨ℓ, h'' ▸ hℓ⟩
        · exact ⟨ℓ', h''⟩
      · rw [h'] at h; cases ol with
        | none => simp at h
        | some ℓ =>
          rcases exec_pot prm q s (.alertSet V (some ℓ)) V with h'' | ⟨ℓ', -, h''⟩
          · simp [exec] at h''; exact ⟨ℓ, by simp [exec]⟩
          · exact ⟨ℓ', h''⟩
      · rw [h'] at h; simp at h
    · rw [act_loc_ne hqp] at h ⊢; exact hg.alertPot q hq V h
  · -- potAlert
    intro q hq V h
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h ⊢
      rcases exec_pot prm q s a V with h' | ⟨ℓ, rfl, h'⟩
      · rw [h'] at h
        rcases exec_alert prm q s a V with h'' | ⟨ol, -, h''⟩ | ⟨-, h''⟩ <;> rw [h''] <;> simp
        exact hg.potAlert q hq V h
      · simp [exec]
    · rw [act_loc_ne hqp] at h ⊢; exact hg.potAlert q hq V h
  · -- potW
    intro q hq V ℓ h
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h
      rcases exec_pot prm q s a V with h' | ⟨ℓ', rfl, h'⟩
      · rw [h'] at h; obtain ⟨S, hS, hm⟩ := hg.potW q hq V ℓ h
        exact ⟨S, hS, fun r hr hrF => (hm r hr hrF).imp fun l ⟨gd, h1, h2⟩ => ⟨gd, hsub h1, h2⟩⟩
      · rw [h'] at h; cases h
        obtain ⟨-, -, hc, -⟩ := hen
        refine ⟨lockSet s V (some ℓ), hc, fun r hr hrF => ?_⟩
        simp only [lockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        obtain ⟨h1, h2⟩ := hr
        obtain ⟨⟨l, gd⟩, he⟩ := Option.ne_none_iff_exists'.1 h1
        refine ⟨l, gd, hsub (hg.acc q hq V r l gd he hrF), ?_⟩
        simpa [lockOf, he] using h2
    · rw [act_loc_ne hqp] at h; obtain ⟨S, hS, hm⟩ := hg.potW q hq V ℓ h
      exact ⟨S, hS, fun r hr hrF => (hm r hr hrF).imp fun l ⟨gd, h1, h2⟩ => ⟨gd, hsub h1, h2⟩⟩
  · -- falseW
    intro q hq V h
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self] at h ⊢
      have hpot : (exec prm q a s).1.pot V = s.pot V ∨ s.alert V = none := by
        rcases exec_pot prm q s a V with h' | ⟨ℓ, rfl, -⟩
        · exact Or.inl h'
        · exact Or.inr hen.2.1
      -- a witness set in terms of accepted messages
      have mk : ∀ T : Finset P, 2 * prm.f + 1 ≤ T.card →
          (∀ r ∈ T, ∃ l gd, s.acc V r = some (l, gd) ∧
            (l = none ∨ ∃ ℓ, (exec prm q a s).1.pot V = some ℓ ∧ l ≠ some ℓ)) →
          ∃ S : Finset P, 2 * prm.f + 1 ≤ S.card ∧ ∀ r ∈ S, r ∉ F → ∃ l gd,
            (r, .vote2 V l gd) ∈ (g.act prm q a).sent ∧
            (l = none ∨ ∃ ℓ, (exec prm q a s).1.pot V = some ℓ ∧ l ≠ some ℓ) := by
        intro T hT hm
        refine ⟨T, hT, fun r hr hrF => ?_⟩
        obtain ⟨l, gd, he, h2⟩ := hm r hr
        exact ⟨l, gd, hsub (hg.acc q hq V r l gd he hrF), h2⟩
      have accOf : ∀ r, s.acc V r ≠ none → ∃ l gd, s.acc V r = some (l, gd) ∧ lockOf (s.acc V r) = l :=
        fun r h1 => by
          obtain ⟨⟨l, gd⟩, he⟩ := Option.ne_none_iff_exists'.1 h1
          exact ⟨l, gd, he, by simp [lockOf, he]⟩
      rcases exec_alert prm q s a V with h' | ⟨ol, rfl, h'⟩ | ⟨hcl, h'⟩
      · rw [h'] at h
        obtain ⟨S, hS, hm⟩ := hg.falseW q hq V h
        rcases hpot with hpot | hpot
        · refine ⟨S, hS, fun r hr hrF => ?_⟩
          obtain ⟨l, gd, h1, h2⟩ := hm r hr hrF
          exact ⟨l, gd, hsub h1, by rw [hpot]; exact h2⟩
        · simp_all
      · rw [h'] at h; cases ol with
        | some ℓ => simp at h
        | none =>
          obtain ⟨-, -, hc, -⟩ := hen
          refine mk _ hc fun r hr => ?_
          simp only [lockSet, Finset.mem_filter, Finset.mem_univ, true_and, or_self] at hr
          obtain ⟨l, gd, he, hl⟩ := accOf r hr.1
          exact ⟨l, gd, he, Or.inl (hl ▸ hr.2)⟩
      · rcases hcl with rfl | rfl
        · obtain ⟨-, -, hc⟩ := hen
          refine mk _ hc fun r hr => ?_
          simp only [lockSet, Finset.mem_filter, Finset.mem_univ, true_and, or_self] at hr
          obtain ⟨l, gd, he, hl⟩ := accOf r hr.1
          exact ⟨l, gd, he, Or.inl (hl ▸ hr.2)⟩
        · obtain ⟨-, ha, hc⟩ := hen
          obtain ⟨ℓ, hℓ⟩ := hg.alertPot q hq V ha
          have hp' : (exec prm q (.alertClear2 V) s).1.pot V = some ℓ := by simpa [exec, hs] using hℓ
          refine mk _ hc fun r hr => ?_
          simp only [notPotSet, Finset.mem_filter, Finset.mem_univ, true_and] at hr
          obtain ⟨l, gd, he, hl⟩ := accOf r hr.1
          refine ⟨l, gd, he, ?_⟩
          rcases hr.2 with h2 | h2
          · exact Or.inl (hl ▸ h2)
          · exact Or.inr ⟨ℓ, hp', by rw [← hl, ← hℓ]; exact h2⟩
    · rw [act_loc_ne hqp] at h ⊢
      obtain ⟨S, hS, hm⟩ := hg.falseW q hq V h
      exact ⟨S, hS, fun r hr hrF => (hm r hr hrF).imp fun l ⟨gd, h1, h2⟩ => ⟨gd, hsub h1, h2⟩⟩
  · -- guardV
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self]
      rcases exec_view prm q s a hen with hv | ⟨-, hv⟩
      · rw [hv]
        rcases exec_guard prm q s a hen s.view with h | ⟨x, -, -, h⟩ | ⟨h, h', -⟩
        · rw [h]; exact hg.guardV q hq
        · rw [h]; simp
        · omega
      · exact hv
    · rw [act_loc_ne hqp]; exact hg.guardV q hq
  · -- view1
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      rw [act_loc_self]
      rcases exec_view prm q s a hen with hv | ⟨hv, -⟩
      · rw [hv]; exact hg.view1 q hq
      · have := hg.view1 q hq; exact this.trans hv.le
    · rw [act_loc_ne hqp]; exact hg.view1 q hq

lemma setLoc_loc {g : GS P Val} {p q : P} {s : LS P Val} :
    (g.setLoc p s).loc q = if q = p then s else g.loc q := by
  simp [GS.setLoc, Function.update_apply]

/-- Changing only the volatile/bookkeeping fields of a process preserves `Inv`, provided the new
received and accepted messages are sound. -/
theorem inv_setLoc {g : GS P Val} (hg : Inv prm F g) {p : P} {s' : LS P Val}
    (h1 : s'.vote1 = (g.loc p).vote1) (h2 : s'.vote2 = (g.loc p).vote2)
    (h3 : s'.echo = (g.loc p).echo) (h4 : s'.echoS = (g.loc p).echoS)
    (h5 : s'.lock = (g.loc p).lock) (h6 : s'.pot = (g.loc p).pot)
    (h7 : s'.alert = (g.loc p).alert) (h8 : s'.guard = (g.loc p).guard)
    (h9 : s'.view = (g.loc p).view)
    (hr : p ∉ F → ∀ q m, (q, m) ∈ s'.rcv → q ∉ F → (q, m) ∈ g.sent)
    (ha : ∀ V q l gd, s'.acc V q = some (l, gd) → (g.loc p).acc V q = some (l, gd)) :
    Inv prm F (g.setLoc p s') := by
  have hl : ∀ q, (g.setLoc p s').loc q = if q = p then s' else g.loc q := fun q => setLoc_loc
  have hsent : (g.setLoc p s').sent = g.sent := rfl
  have hdec : (g.setLoc p s').dec = g.dec := rfl
  have hR : ∀ m, Refl s' m ↔ Refl (g.loc p) m := by
    intro m; cases m <;> simp [Refl, h1, h2, h3, h4]
  have ha' : ∀ V q x, lockOf (s'.acc V q) = some x → lockOf ((g.loc p).acc V q) = some x := by
    intro V q x h
    rcases hs : s'.acc V q with _ | ⟨l, gd⟩
    · simp [hs, lockOf] at h
    · rw [ha V q l gd hs]; rw [hs] at h; exact h
  have L : ∀ q, q ∉ F → (q = p → ∀ {Φ : LS P Val → Prop}, Φ (g.loc p) → Φ s' → Φ ((g.setLoc p s').loc q))
      ∧ (q ≠ p → (g.setLoc p s').loc q = g.loc q) := by
    intro q _
    refine ⟨fun hqp Φ _ h => by rw [hl, if_pos hqp]; exact h, fun hqp => by rw [hl, if_neg hqp]⟩
  constructor
  · intro q hq m hm
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl]; exact (hR m).2 (hg.refl q hq m hm)
    · rw [(L q hq).2 hqp]; exact hg.refl q hq m hm
  · intro q hq k V x h
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h3] at h; exact hg.echoSent q hq k V x h
    · rw [(L q hq).2 hqp] at h; exact hg.echoSent q hq k V x h
  · intro q hq r m h hr'
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl] at h; exact hr hq r m h hr'
    · rw [(L q hq).2 hqp] at h; exact hg.rcv q hq r m h hr'
  · intro q hq V r l gd h hr'
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl] at h; exact hg.acc q hq V r l gd (ha V r l gd h) hr'
    · rw [(L q hq).2 hqp] at h; exact hg.acc q hq V r l gd h hr'
  · intro q hq V r x h
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl] at h; exact hg.accLock q hq V r x (ha' V r x h)
    · rw [(L q hq).2 hqp] at h; exact hg.accLock q hq V r x h
  · intro q hq V x h
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h5] at h; exact hg.lockQ q hq V x h
    · rw [(L q hq).2 hqp] at h; exact hg.lockQ q hq V x h
  · intro q hq V x gd h
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h2] at h; exact hg.vote2Q q hq V x gd h
    · rw [(L q hq).2 hqp] at h; exact hg.vote2Q q hq V x gd h
  · exact hg.dec
  · intro q hq V h
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h7] at h; rw [hl, if_pos rfl, h6]; exact hg.alertPot q hq V h
    · rw [(L q hq).2 hqp] at h ⊢; exact hg.alertPot q hq V h
  · intro q hq V h
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h6] at h; rw [hl, if_pos rfl, h7]; exact hg.potAlert q hq V h
    · rw [(L q hq).2 hqp] at h ⊢; exact hg.potAlert q hq V h
  · intro q hq V ℓ h
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h6] at h; exact hg.potW q hq V ℓ h
    · rw [(L q hq).2 hqp] at h; exact hg.potW q hq V ℓ h
  · intro q hq V h
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h7] at h; rw [hl, if_pos rfl, h6]; exact hg.falseW q hq V h
    · rw [(L q hq).2 hqp] at h ⊢; exact hg.falseW q hq V h
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h8, h9]; exact hg.guardV q hq
    · rw [(L q hq).2 hqp]; exact hg.guardV q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [hl, if_pos rfl, h9]; exact hg.view1 q hq
    · rw [(L q hq).2 hqp]; exact hg.view1 q hq

theorem inv_step (hF : F.card ≤ prm.f) {g g' : GS P Val} (hg : Inv prm F g)
    (h : Step prm F g g') : Inv prm F g' := by
  cases h with
  | act p a hp hen => exact inv_act hF hg hp hen
  | vol p hp rcv acc hrcv hacc =>
    refine inv_setLoc hg rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_
    · intro _ q m hm hq
      rcases hrcv _ hm with h' | h' | h'
      · exact hg.rcv p hp q m h' hq
      · exact absurd h' hq
      · exact h'
    · intro V q l gd h
      rcases hacc V q with h' | h' <;> simp only [h'] at h
      · simp at h
      · exact h
  | aux p hp clk entered active out =>
    exact inv_setLoc hg rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun hp => hg.rcv p hp)
      (fun _ _ _ _ h => h)

theorem inv_init (inp : P → Val) : Inv prm F (initGS prm F inp) := by
  have hl : ∀ q, (initGS prm F inp).loc q =
      { (enterV prm q 1 (startLS (inp q))).1 with out := (enterV prm q 1 (startLS (inp q))).2 } :=
    fun _ => rfl
  constructor <;> (try simp only [hl])
  · intro q hq m hm
    have hm' : m ∈ (enterV prm q 1 (startLS (inp q))).2 := hm.2
    rcases mem_enterV _ _ _ _ hm' with ⟨W, rfl, -, -, h⟩ | ⟨w, rfl⟩
    · exact h
    · trivial
  · intro q _ k V x h; simp [startLS] at h
  · intro q _ r m h; simp [startLS] at h
  · intro q _ V r l gd h; simp [startLS] at h
  · intro q _ V r x h; simp [startLS, lockOf] at h
  · intro q _ V x h; simp [startLS] at h
  · intro q _ V x gd h
    rcases enterV_vote2 prm q 1 (startLS (inp q)) V with h' | ⟨-, -, h'⟩ <;> rw [h'] at h <;>
      simp [startLS] at h
  · intro e he; simp [initGS] at he
  · intro q _ V h; simp [startLS] at h
  · intro q _ V h; simp [startLS] at h
  · intro q _ V ℓ h; simp [startLS] at h
  · intro q _ V h; simp [startLS] at h
  · intro q _; simp [startLS]
  · intro q _; simp

/-- The basic invariant holds in every reachable state. -/
theorem reach_inv (hF : F.card ≤ prm.f) {inp : P → Val} {g : GS P Val} (h : Reach prm F inp g) :
    Inv prm F g := by
  induction h with
  | refl => exact inv_init inp
  | tail _ hs ih => exact inv_step hF ih hs

end Podc.ForgetIT
