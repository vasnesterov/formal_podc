/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Send
import Papers.PODC2019.ReconfigurableCommit.Consequences

/-!
# Preservation of the invariant: local-state updates

The delivery of `ACCEPT`, `DECISION` and `NEW_STATE`, and the `CONFIG_CHANGE` step.
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st st' : State T Pl S P}

section SetLoc

variable (st : State T Pl S P) (p : P) (ls : LState T Pl S P)

theorem State.setLoc_proj {α : Type} (f : LState T Pl S P → α) (h : f ls = f (st.loc p))
    (q : P) : f ((st.setLoc p ls).loc q) = f (st.loc q) := by
  by_cases hq : q = p
  · subst hq; simpa using h
  · rw [State.setLoc_loc_ne _ _ _ hq]

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
@[simp] theorem acked_setLoc : Acked (st.setLoc p ls) = Acked st := rfl
omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
@[simp] theorem replied_setLoc : Replied (st.setLoc p ls) = Replied st := rfl
omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
@[simp] theorem accL_setLoc : AccL (st.setLoc p ls) = AccL st := rfl
omit [DecidableEq T] [DecidableEq Pl] in
@[simp] theorem decided_setLoc (Pa : Params T Pl S P) :
    Decided Pa (st.setLoc p ls) = Decided Pa st := rfl
omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
@[simp] theorem fresh_setLoc : Fresh (st.setLoc p ls) = Fresh st := rfl
omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
@[simp] theorem plAt_setLoc (Pa : Params T Pl S P) : plAt Pa (st.setLoc p ls) = plAt Pa st := rfl
omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
@[simp] theorem decIn_setLoc : DecIn (st.setLoc p ls) = DecIn st := rfl

theorem dead_setLoc (h : ls.newEpoch = (st.loc p).newEpoch) : Dead (st.setLoc p ls) = Dead st := by
  have hN := State.setLoc_proj st p ls (·.newEpoch) h
  funext s e
  simp only [Dead, cfg_setLoc, acked_setLoc, hN]

theorem aliveK_setLoc (h : ls.newEpoch = (st.loc p).newEpoch) :
    AliveK (st.setLoc p ls) = AliveK st := by
  have hN := State.setLoc_proj st p ls (·.newEpoch) h
  funext s e k
  simp only [AliveK, cfg_setLoc, acked_setLoc, hN]

/-- `cand` only reads the local state of the leader of the configuration. -/
theorem cand_setLoc_of_ne {s : S} {E : ℕ} {c : Config P} (h : c.leader ≠ p) :
    cand (st.setLoc p ls) s E c = cand st s E c := by
  simp only [cand, State.setLoc_started, State.setLoc_elog, State.setLoc_base,
    State.setLoc_loc_ne _ _ _ h]

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem cand_setLoc_of_started {s : S} {E : ℕ} {c : Config P} (h : st.started s E = true) :
    cand (st.setLoc p ls) s E c = cand st s E c := by
  simp only [cand, State.setLoc_started, h, ite_true, State.setLoc_base]

theorem cand_setLoc (h1 : ls.arr.ent = (st.loc p).arr.ent) (h2 : ls.epoch = (st.loc p).epoch) :
    cand (st.setLoc p ls) = cand st := by
  have hE := State.setLoc_proj st p ls (·.arr.ent) h1
  have hP := State.setLoc_proj st p ls (·.epoch) h2
  funext s E c
  simp only [cand, State.setLoc_started, State.setLoc_elog, State.setLoc_base, hE, hP]

end SetLoc

namespace Inv

omit [DecidableEq T] in
/-- A process that is a member of configuration `e` and of an earlier configuration has replied to
the probing of `e`, so its `new_epoch` is at least `e`. -/
theorem newEpoch_of_mem (hI : Inv Pa st) {s : S} {e z : ℕ} {c cz : Config P} {q : P}
    (hc : cfg st s e = some c) (hq : q ∈ c.members) (hz : z < e) (hcz : cfg st s z = some cz)
    (hqz : q ∈ cz.members) : e ≤ (st.loc q).newEpoch := by
  obtain ⟨pe, -, -, -, -, hmem⟩ := hI.cfg_mem s e c (by omega) hc
  rcases hmem q hq with hf | ⟨⟨b, r, hr⟩, -⟩
  · exact absurd hqz (hf z hz cz hcz)
  · exact (hI.m_probeAck q r b e s hr).2.1

omit [DecidableEq T] in
/-- The leader of a configured epoch `E` that has not started, with `new_epoch = E`, is
reconfiguring (it is frozen until it receives `NEW_CONFIG(E)`). -/
theorem frozen_leader (hI : Inv Pa st) {s : S} {E : ℕ} {c : Config P} (hc : cfg st s E = some c)
    (hns : st.started s E = false) (hne : (st.loc c.leader).newEpoch = E) :
    (st.loc c.leader).status = .reconfiguring := by
  obtain ⟨hlm, hhome, -⟩ := hI.cfg_wf s E c hc
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · exfalso
    have hs := hhome _ hlm
    subst hs
    have hst := hI.loc_started c.leader
    have hpos : 0 < (st.loc c.leader).epoch (Pa.home c.leader) := by
      rcases Nat.eq_zero_or_pos ((st.loc c.leader).epoch (Pa.home c.leader)) with h0 | h0
      · rw [h0, hns] at hst; cases hst
      · exact h0
    rcases hI.loc_member0 c.leader with h0 | hm
    · omega
    · have := hI.newEpoch_of_mem (hI.loc_view c.leader _) hm hpos hc hlm
      omega
  · obtain ⟨-, -, -, hR, -⟩ := hI.cfg_mem s E c hE hc
    exact hI.m_frozen _ _ _ _ hR hne hns

end Inv

set_option hygiene false in
local macro "frD " h:term : tactic => `(tactic| simpa only [hS, hEp, hMb, hLd, hNx, hEnt, hIn, hNE,
  hPr, hPE, hPM, hRE, hRS, hAA, hPA, hD, hK, hC, cfg_setLoc, State.setLoc_cs, State.setLoc_hist,
  State.setLoc_sent, State.setLoc_net, State.setLoc_started, State.setLoc_elog, State.setLoc_base,
  State.setLoc_vinfo, acked_setLoc, replied_setLoc, accL_setLoc, decided_setLoc, fresh_setLoc,
  plAt_setLoc, decIn_setLoc] using $h)

/-- Storing a decision (lines 31–32) at a leader or follower `p`. -/
theorem Inv.setLoc_decision (hI : Inv Pa st) {p : P} {e k : ℕ} {d : Dec}
    (hst : (st.loc p).status = .leader ∨ (st.loc p).status = .follower)
    (he : e ≤ (st.loc p).epoch (Pa.home p))
    (hm : ∃ v, AccL st (Pa.home p) e k v ∧ Event.decide v.1.1 d ∈ st.hist)
    (ls : LState T Pl S P)
    (hls : ls = { st.loc p with arr := { (st.loc p).arr with
        dec := Function.update (st.loc p).arr.dec k (some d),
        phase := Function.update (st.loc p).arr.phase k .decided,
        len := max (st.loc p).arr.len k } }) :
    Inv Pa (st.setLoc p ls) := by
  have hS := State.setLoc_proj st p ls (·.status) (by rw [hls])
  have hEp := State.setLoc_proj st p ls (·.epoch) (by rw [hls])
  have hMb := State.setLoc_proj st p ls (·.members) (by rw [hls])
  have hLd := State.setLoc_proj st p ls (·.leader) (by rw [hls])
  have hNx := State.setLoc_proj st p ls (·.next) (by rw [hls])
  have hEnt := State.setLoc_proj st p ls (·.arr.ent) (by rw [hls])
  have hIn := State.setLoc_proj st p ls (·.initialized) (by rw [hls])
  have hNE := State.setLoc_proj st p ls (·.newEpoch) (by rw [hls])
  have hPr := State.setLoc_proj st p ls (·.probing) (by rw [hls])
  have hPE := State.setLoc_proj st p ls (·.probedEpoch) (by rw [hls])
  have hPM := State.setLoc_proj st p ls (·.probedMembers) (by rw [hls])
  have hRE := State.setLoc_proj st p ls (·.reconEpoch) (by rw [hls])
  have hRS := State.setLoc_proj st p ls (·.reconShard) (by rw [hls])
  have hAA := State.setLoc_proj st p ls (·.acceptAcks) (by rw [hls])
  have hPA := State.setLoc_proj st p ls (·.probeAcks) (by rw [hls])
  have hD := dead_setLoc st p ls (by rw [hls])
  have hK := aliveK_setLoc st p ls (by rw [hls])
  have hC := cand_setLoc st p ls (by rw [hls]) (by rw [hls])
  -- the decided slot holds an entry
  obtain ⟨v, hv, hvd⟩ := hm
  have hkEnt : ((st.loc p).arr.ent k).isSome = true := by
    have hEs := hI.loc_started p
    rcases hst with hl | hf
    · obtain ⟨hlp, -⟩ := hI.loc_leader p hl
      rw [hI.loc_leaderArr p hlp k, hI.accL_le hv he hEs]; rfl
    · obtain ⟨hlp, hin, hpm⟩ := hI.loc_follower p hf
      rcases he.lt_or_eq with hlt | heq
      · rw [hI.loc_base p hin k v (hI.accL_persist hv hlt hEs).1]; rfl
      · obtain ⟨-, c, hc, hacks⟩ := hv
        have hview := hI.loc_view p (Pa.home p)
        rw [← heq, hc] at hview
        cases hview
        obtain ⟨l, hl⟩ := hI.loc_acked p k _ _ (heq ▸ hacks p (by
          simp [Config.followers, hpm, Ne.symm hlp]))
        rw [hl]; rfl
  exact {
    cs_zero := by frD hI.cs_zero
    cfg_wf := by frD hI.cfg_wf
    cfg_mem := by frD hI.cfg_mem
    frz := by frD hI.frz
    leader_init := by frD hI.leader_init
    init_init := by frD hI.init_init
    started_cfg := by frD hI.started_cfg
    started_leader := by frD hI.started_leader
    elog_started := by frD hI.elog_started
    base_elog := by frD hI.base_elog
    elog_above := by frD hI.elog_above
    elog_origin := by frD hI.elog_origin
    elog_dist := by frD hI.elog_dist
    elog_txn := by frD hI.elog_txn
    vinfo_none := by frD hI.vinfo_none
    vinfo_ok := by frD hI.vinfo_ok
    inv2 := by frD hI.inv2
    loc_len := by
      intro q j hj
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls] at hj ⊢
        by_cases hjk : j = k
        · subst hjk; exact le_max_right _ _
        · rw [Function.update_of_ne hjk] at hj
          exact le_trans (hI.loc_len q j hj) (le_max_left _ _)
      · simp only [State.setLoc_loc_ne _ _ _ hq] at hj ⊢
        exact hI.loc_len q j hj
    loc_ent := by
      intro q j
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls]
        by_cases hjk : j = k
        · subst hjk; simp [hkEnt]
        · rw [Function.update_of_ne hjk]; exact hI.loc_ent q j
      · simp only [State.setLoc_loc_ne _ _ _ hq]
        exact hI.loc_ent q j
    loc_newEpoch := by frD hI.loc_newEpoch
    loc_view := by frD hI.loc_view
    loc_started := by frD hI.loc_started
    loc_member := by frD hI.loc_member
    loc_member0 := by frD hI.loc_member0
    loc_leaderArr := by frD hI.loc_leaderArr
    loc_leader := by
      intro q hql
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls] at hql ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hI.loc_leader q hql
        refine ⟨h1, h2, fun j hj => ?_, h4⟩
        by_cases hjk : j = k
        · subst hjk
          exact absurd (h3 j hj) ((hI.loc_ent q j).1 hkEnt)
        · rw [Function.update_of_ne hjk]; exact h3 j hj
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_base] at hql ⊢
        exact hI.loc_leader q hql
    loc_follower := by frD hI.loc_follower
    loc_elog := by frD hI.loc_elog
    loc_base := by frD hI.loc_base
    loc_acked := by frD hI.loc_acked
    loc_acked_epoch := by frD hI.loc_acked_epoch
    loc_dec := by
      intro q j hj
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, accL_setLoc, State.setLoc_hist] at hj ⊢
        by_cases hjk : j = k
        · subst hjk
          exact ⟨d, by simp, e, v, he, hv, hvd⟩
        · rw [Function.update_of_ne hjk] at hj ⊢
          exact hI.loc_dec q j hj
      · simp only [State.setLoc_loc_ne _ _ _ hq, accL_setLoc, State.setLoc_hist] at hj ⊢
        exact hI.loc_dec q j hj
    loc_acceptAcks := by frD hI.loc_acceptAcks
    loc_probeAcks := by frD hI.loc_probeAcks
    prb := by frD hI.prb
    probe_old := by frD hI.probe_old
    probe_sent := by frD hI.probe_sent
    m_probeAck := by frD hI.m_probeAck
    m_frozen := by frD hI.m_frozen
    m_prepare := by frD hI.m_prepare
    m_prepareAck := by frD hI.m_prepareAck
    m_accept := by frD hI.m_accept
    m_acceptAck := by frD hI.m_acceptAck
    m_decision := by frD hI.m_decision
    m_newConfig := by frD hI.m_newConfig
    m_newState := by frD hI.m_newState
    net_sub := by frD hI.net_sub
    nc_unique := by frD hI.nc_unique
    nc_count := by frD hI.nc_count
    nc_flight := by frD hI.nc_flight
    ns_unique := by frD hI.ns_unique
    ns_count := by frD hI.ns_count
    ns_flight := by frD hI.ns_flight
    hist_certify := by frD hI.hist_certify
    hist_certify_unique := by frD hI.hist_certify_unique
    hist_decide := by frD hI.hist_decide
    hist_decide_unique := by frD hI.hist_decide_unique
    hist_decide_idx := by frD hI.hist_decide_idx
    hist_certify_idx := by frD hI.hist_certify_idx
    hist_decide_after := by frD hI.hist_decide_after
    hist_order := by frD hI.hist_order
    vinfo_len := by frD hI.vinfo_len
  }

theorem Inv.deliver_decision (hI : Inv Pa st) {src dst : P} {e k : ℕ} {d : Dec}
    (hm : Msg.decision e k d ∈ st.sent src dst)
    (h : handle Pa st src dst (.decision e k d) = some st') : Inv Pa st' := by
  simp only [handle] at h
  split_ifs at h with hc
  cases h
  exact hI.setLoc_decision hc.1 hc.2 (hI.m_decision _ _ _ _ _ hm) _ rfl

set_option hygiene false in
local macro "frB " h:term : tactic => `(tactic| simpa only [hR, cfg_send,
  State.send_loc, State.send_cs, State.send_hist, State.send_started, State.send_elog,
  State.send_base, State.send_vinfo, fresh_send, cand_send, plAt_send, decIn_send] using $h)

/-- Sending `ACCEPT_ACK` (line 25) for an entry stored at a follower `p` preserves the
invariant. -/
theorem Inv.send_acceptAck (hI : Inv Pa st) {p : P} {k : ℕ} {t : T} {d : Dec}
    (hf : (st.loc p).status = .follower) (hent : ∃ l, (st.loc p).arr.ent k = some (t, l, d))
    (out : P → Option (Msg T Pl S P))
    (hout : ∀ b m, out b = some m →
      m = .acceptAck (Pa.home p) ((st.loc p).epoch (Pa.home p)) k t d) :
    Inv Pa (st.send p out) := by
  have hNP : NoProbeAck out := fun b b' E s h => by cases hout _ _ h
  have hR := replied_send st p out hNP
  have hM := fun {m : Msg T Pl S P} {a b : P} => State.mem_send_sent st p out (m := m) (a := a) (b := b)
  have hN := fun {m : Msg T Pl S P} {a b : P} => State.mem_send_net st p out (m := m) (a := a) (b := b)
  have old : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ (st.send p out).sent a b →
      (∀ s e k t d, m ≠ Msg.acceptAck s e k t d) → m ∈ st.sent a b := by
    intro m a b h hn
    rcases hM.1 h with h | ⟨-, h⟩
    · exact h
    · exact absurd (hout _ _ h) (hn _ _ _ _ _)
  have oldN : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ (st.send p out).net a b →
      (∀ s e k t d, m ≠ Msg.acceptAck s e k t d) → m ∈ st.net a b := by
    intro m a b h hn
    rcases hN.1 h with h | ⟨-, h⟩
    · exact h
    · exact absurd (hout _ _ h) (hn _ _ _ _ _)
  have new : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ st.sent a b → m ∈ (st.send p out).sent a b :=
    fun h => hM.2 (Or.inl h)
  have oldI : ∀ {m : Msg T Pl S P} {a b : P} {i : ℕ}, ((st.send p out).sent a b)[i]? = some m →
      (∀ s e k t d, m ≠ Msg.acceptAck s e k t d) → (st.sent a b)[i]? = some m := by
    intro m a b i h hn
    rw [State.send_sent] at h
    split_ifs at h
    · rcases getElem?_append_toList h with h | ⟨-, h⟩
      · exact h
      · exact absurd (hout _ _ h) (hn _ _ _ _ _)
    · exact h
  have hAck1 : ∀ {q s e k' t' d'}, Acked (st.send p out) q s e k' t' d' →
      Acked st q s e k' t' d' ∨ (q = p ∧ s = Pa.home p ∧ e = (st.loc p).epoch (Pa.home p) ∧
        k' = k ∧ t' = t ∧ d' = d) := by
    rintro q s e k' t' d' ⟨r, hr⟩
    rcases hM.1 hr with h | ⟨rfl, h⟩
    · exact Or.inl ⟨r, h⟩
    · have := hout _ _ h
      simp only [Msg.acceptAck.injEq] at this
      exact Or.inr ⟨rfl, this⟩
  have hNEp : (st.loc p).newEpoch ≤ (st.loc p).epoch (Pa.home p) :=
    hI.loc_newEpoch p (by rw [hf]; decide)
  have hDm : ∀ {s e}, Dead st s e → Dead (st.send p out) s e := by
    rintro s e ⟨c, hc, q, hq, hlt, hna⟩
    refine ⟨c, hc, q, hq, hlt, fun k' t' d' ha => ?_⟩
    rcases hAck1 ha with ha | ⟨rfl, rfl, rfl, -⟩
    · exact hna _ _ _ ha
    · omega
  have hKm : ∀ {s e k'}, AliveK (st.send p out) s e k' → AliveK st s e k' := by
    intro s e k' h c hc q hq
    rcases h c hc q hq with ⟨t', d', ha⟩ | hle
    · rcases hAck1 ha with ha | ⟨rfl, rfl, rfl, -⟩
      · exact Or.inl ⟨t', d', ha⟩
      · exact Or.inr hNEp
    · exact Or.inr hle
  have hLm : ∀ {s e k' v}, AccL st s e k' v → AccL (st.send p out) s e k' v := by
    rintro s e k' v ⟨h1, c, hc, h2⟩
    exact ⟨h1, c, hc, fun q hq => acked_mono_send st p out (h2 q hq)⟩
  obtain ⟨l₀, hl₀⟩ := hent
  obtain ⟨o₀, ho₀⟩ := hI.loc_elog p k _ hl₀
  have hview := hI.loc_view p (Pa.home p)
  have hfol : p ∈ Config.followers ⟨(st.loc p).members (Pa.home p), (st.loc p).leader (Pa.home p)⟩ := by
    obtain ⟨h1, -, h3⟩ := hI.loc_follower p hf
    simp [Config.followers, h3, Ne.symm h1]
  have hent : ∃ l, (st.loc p).arr.ent k = some (t, l, d) := ⟨l₀, hl₀⟩
  exact {
    cs_zero := by frB hI.cs_zero
    cfg_wf := by frB hI.cfg_wf
    cfg_mem := by
      intro s E c h1 hc
      obtain ⟨pe, hpe, hd, hr, hy, hm⟩ := hI.cfg_mem s E c h1 hc
      exact ⟨pe, hpe, fun e' a b => hDm (hd e' a b), by rw [hR]; exact hr, hy,
        by simpa only [hR, fresh_send, cfg_send] using hm⟩
    frz := by frB hI.frz
    leader_init := by frB hI.leader_init
    init_init := by frB hI.init_init
    started_cfg := by frB hI.started_cfg
    started_leader := by frB hI.started_leader
    elog_started := by frB hI.elog_started
    base_elog := by frB hI.base_elog
    elog_above := by frB hI.elog_above
    elog_origin := by frB hI.elog_origin
    elog_dist := by frB hI.elog_dist
    elog_txn := by frB hI.elog_txn
    vinfo_none := by frB hI.vinfo_none
    vinfo_ok := by frB hI.vinfo_ok
    inv2 := by
      intro s E c hc hst e' he' j v hv hal
      exact hI.inv2 s E c hc hst e' he' j v hv (hKm hal)
    loc_len := by frB hI.loc_len
    loc_ent := by frB hI.loc_ent
    loc_newEpoch := by frB hI.loc_newEpoch
    loc_view := by frB hI.loc_view
    loc_started := by frB hI.loc_started
    loc_member := by frB hI.loc_member
    loc_member0 := by frB hI.loc_member0
    loc_leaderArr := by frB hI.loc_leaderArr
    loc_leader := by frB hI.loc_leader
    loc_follower := by frB hI.loc_follower
    loc_elog := by frB hI.loc_elog
    loc_base := by frB hI.loc_base
    loc_acked := by
      intro q k' t' d' ha
      rcases hAck1 ha with ha | ⟨rfl, -, -, rfl, rfl, rfl⟩
      · exact hI.loc_acked q k' t' d' ha
      · exact hent
    loc_acked_epoch := by
      intro q s e k' t' d' ha
      rcases hAck1 ha with ha | ⟨rfl, rfl, rfl, -⟩
      · exact hI.loc_acked_epoch q s e k' t' d' ha
      · exact ⟨rfl, le_refl _, (hI.loc_follower q hf).2.1⟩
    loc_dec := by
      intro q j hj
      obtain ⟨dd, h1, e, v, h2, h3, h4⟩ := hI.loc_dec q j hj
      exact ⟨dd, h1, e, v, h2, hLm h3, h4⟩
    loc_acceptAcks := by
      intro q r s e k t d h
      exact new (hI.loc_acceptAcks q r s e k t d h)
    loc_probeAcks := by
      intro q r b E s h
      exact new (hI.loc_probeAcks q r b E s h)
    prb := by
      intro q hq
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.prb q hq
      exact ⟨h1, h2, h3, h4, fun e' a b => hDm (h5 e' a b),
        fun r hr hr' => h6 r (old hr (by intro _ _ _ _ _ h; cases h)) hr'⟩
    probe_old := by
      intro r q E h
      simpa using hI.probe_old r q E (old h (by intro _ _ _ _ _ h; cases h))
    probe_sent := by
      intro r q E h
      simpa using hI.probe_sent r q E (old h (by intro _ _ _ _ _ h; cases h))
    m_probeAck := by
      intro q r b E s h
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI.m_probeAck q r b E s (old h (by intro _ _ _ _ _ h; cases h))
      refine ⟨h1, h2, new h3, h4, fun hb => ?_⟩
      obtain ⟨h5a, h5b⟩ := h5 hb
      refine ⟨fun e he k' t' d' ha => ?_, h5b⟩
      rcases hAck1 ha with ha | ⟨rfl, -, rfl, -⟩
      · exact h5a e he _ _ _ ha
      · have := hNEp; omega
    m_frozen := by frB hI.m_frozen
    m_prepare := by
      intro c b t lo h
      exact hI.m_prepare c b t lo (old h (by intro _ _ _ _ _ h; cases h))
    m_prepareAck := by
      intro c r e s k t l d h
      exact hI.m_prepareAck c r e s k t l d (old h (by intro _ _ _ _ _ h; cases h))
    m_accept := by
      intro c q e k t l d h
      exact hI.m_accept c q e k t l d (old h (by intro _ _ _ _ _ h; cases h))
    m_acceptAck := by
      intro q r s e k' t' d' h
      rcases hM.1 h with h' | ⟨rfl, h'⟩
      · exact hI.m_acceptAck q r s e k' t' d' h'
      · have := hout _ _ h'
        simp only [Msg.acceptAck.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
        exact ⟨rfl, ⟨l₀, o₀, ho₀⟩, _, hview, hfol⟩
    m_decision := by
      intro c q e k d h
      obtain ⟨v, h1, h2⟩ := hI.m_decision c q e k d (old h (by intro _ _ _ _ _ h; cases h))
      exact ⟨v, hLm h1, h2⟩
    m_newConfig := by
      intro r q e M h
      simpa only [hR, cfg_send] using hI.m_newConfig r q e M (old h (by intro _ _ _ _ _ h; cases h))
    m_newState := by
      intro q r e M a h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        hI.m_newState q r e M a (old h (by intro _ _ _ _ _ h; cases h))
      refine ⟨h1, h2, h3, h4, h5, h6, h7, fun j hj => ?_⟩
      obtain ⟨dd, a1, e', v, a2, a3, a4⟩ := h8 j hj
      exact ⟨dd, a1, e', v, a2, hLm a3, a4⟩
    net_sub := by
      intro a b
      rw [State.send_net, State.send_sent]
      split_ifs
      · exact (hI.net_sub a b).append_right _
      · exact hI.net_sub a b
    nc_unique := by
      intro r q e M r' q' M' h h'
      exact hI.nc_unique r q e M r' q' M' (old h (by intro _ _ _ _ _ h; cases h))
        (old h' (by intro _ _ _ _ _ h; cases h))
    nc_count := by
      intro r q e M M' i j h h'
      exact hI.nc_count r q e M M' i j (oldI h (by intro _ _ _ _ _ h; cases h))
        (oldI h' (by intro _ _ _ _ _ h; cases h))
    nc_flight := by
      intro r q e M h
      simpa using hI.nc_flight r q e M (oldN h (by intro _ _ _ _ _ h; cases h))
    ns_unique := by
      intro q r e M a q' M' a' h h'
      exact hI.ns_unique q r e M a q' M' a' (old h (by intro _ _ _ _ _ h; cases h))
        (old h' (by intro _ _ _ _ _ h; cases h))
    ns_count := by
      intro q r e M a M' a' i j h h'
      exact hI.ns_count q r e M a M' a' i j (oldI h (by intro _ _ _ _ _ h; cases h))
        (oldI h' (by intro _ _ _ _ _ h; cases h))
    ns_flight := by
      intro q r e M a h
      simpa using hI.ns_flight q r e M a (oldN h (by intro _ _ _ _ _ h; cases h))
    hist_certify := by frB hI.hist_certify
    hist_certify_unique := by frB hI.hist_certify_unique
    hist_decide := by
      intro t d h
      obtain ⟨es, ks, vs, h1, h2⟩ := hI.hist_decide t d h
      exact ⟨es, ks, vs, fun s hs => ⟨hLm (h1 s hs).1, (h1 s hs).2⟩, h2⟩
    hist_decide_unique := by frB hI.hist_decide_unique
    hist_decide_idx := by frB hI.hist_decide_idx
    hist_certify_idx := by frB hI.hist_certify_idx
    hist_decide_after := by frB hI.hist_decide_after
    hist_order := by
      intro i t d h s hs
      obtain ⟨e, k, v, h1, h2, h3⟩ := hI.hist_order i t d h s hs
      exact ⟨e, k, v, hLm h1, h2, h3⟩
    vinfo_len := by frB hI.vinfo_len
  }

set_option hygiene false in
local macro "frA " h:term : tactic => `(tactic| simpa only [hS, hEp, hMb, hLd, hNx, hIn, hNE,
  hPr, hPE, hPM, hRE, hRS, hAA, hPA, hD, hK, cfg_setLoc, State.setLoc_cs, State.setLoc_hist,
  State.setLoc_sent, State.setLoc_net, State.setLoc_started, State.setLoc_elog, State.setLoc_base,
  State.setLoc_vinfo, acked_setLoc, replied_setLoc, accL_setLoc, decided_setLoc, fresh_setLoc,
  plAt_setLoc, decIn_setLoc] using $h)

/-- Storing an accepted entry in an empty slot (line 24) at a follower `p`. -/
theorem Inv.setLoc_accept (hI : Inv Pa st) {p : P} {k : ℕ} {t : T} {l : Pl} {d : Dec}
    (hf : (st.loc p).status = .follower) (hph : (st.loc p).arr.phase k = .start)
    (helog : ∃ o, st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) k = some ((t, l, d), o))
    (ls : LState T Pl S P)
    (hls : ls = { st.loc p with arr := { (st.loc p).arr with
        ent := Function.update (st.loc p).arr.ent k (some (t, l, d)),
        phase := Function.update (st.loc p).arr.phase k .prepared,
        len := max (st.loc p).arr.len k } }) :
    Inv Pa (st.setLoc p ls) := by
  have hS := State.setLoc_proj st p ls (·.status) (by rw [hls])
  have hEp := State.setLoc_proj st p ls (·.epoch) (by rw [hls])
  have hMb := State.setLoc_proj st p ls (·.members) (by rw [hls])
  have hLd := State.setLoc_proj st p ls (·.leader) (by rw [hls])
  have hNx := State.setLoc_proj st p ls (·.next) (by rw [hls])
  have hIn := State.setLoc_proj st p ls (·.initialized) (by rw [hls])
  have hNE := State.setLoc_proj st p ls (·.newEpoch) (by rw [hls])
  have hPr := State.setLoc_proj st p ls (·.probing) (by rw [hls])
  have hPE := State.setLoc_proj st p ls (·.probedEpoch) (by rw [hls])
  have hPM := State.setLoc_proj st p ls (·.probedMembers) (by rw [hls])
  have hRE := State.setLoc_proj st p ls (·.reconEpoch) (by rw [hls])
  have hRS := State.setLoc_proj st p ls (·.reconShard) (by rw [hls])
  have hAA := State.setLoc_proj st p ls (·.acceptAcks) (by rw [hls])
  have hPA := State.setLoc_proj st p ls (·.probeAcks) (by rw [hls])
  have hD := dead_setLoc st p ls (by rw [hls])
  have hK := aliveK_setLoc st p ls (by rw [hls])
  have hk0 : (st.loc p).arr.ent k = none := by
    have := hI.loc_ent p k
    rw [hph] at this
    simpa using this
  exact {
    cs_zero := by frA hI.cs_zero
    cfg_wf := by frA hI.cfg_wf
    cfg_mem := by frA hI.cfg_mem
    frz := by frA hI.frz
    leader_init := by frA hI.leader_init
    init_init := by frA hI.init_init
    started_cfg := by frA hI.started_cfg
    started_leader := by frA hI.started_leader
    elog_started := by frA hI.elog_started
    base_elog := by frA hI.base_elog
    elog_above := by frA hI.elog_above
    elog_origin := by frA hI.elog_origin
    elog_dist := by frA hI.elog_dist
    elog_txn := by frA hI.elog_txn
    vinfo_none := by frA hI.vinfo_none
    vinfo_ok := by frA hI.vinfo_ok
    inv2 := by
      intro s E c hc hst e' he' j v hv hal
      simp only [State.setLoc_started, hNE, cfg_setLoc] at hst hc
      have hC : cand (st.setLoc p ls) s E c = cand st s E c := by
        by_cases hsE : st.started s E = true
        · exact cand_setLoc_of_started _ _ _ hsE
        · by_cases hl : c.leader = p
          · exfalso
            have hfr := hI.frozen_leader hc (by simpa using hsE) (hst.resolve_left hsE)
            rw [hl, hf] at hfr; cases hfr
          · exact cand_setLoc_of_ne _ _ _ hl
      rw [hC]
      exact hI.inv2 s E c hc hst e' he' j v hv (by rwa [hK] at hal)
    loc_len := by
      intro q j hj
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls] at hj ⊢
        by_cases hjk : j = k
        · subst hjk; exact le_max_right _ _
        · rw [Function.update_of_ne hjk] at hj
          exact le_trans (hI.loc_len q j hj) (le_max_left _ _)
      · simp only [State.setLoc_loc_ne _ _ _ hq] at hj ⊢
        exact hI.loc_len q j hj
    loc_ent := by
      intro q j
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls]
        by_cases hjk : j = k
        · subst hjk; simp
        · rw [Function.update_of_ne hjk, Function.update_of_ne hjk]; exact hI.loc_ent q j
      · simp only [State.setLoc_loc_ne _ _ _ hq]
        exact hI.loc_ent q j
    loc_newEpoch := by frA hI.loc_newEpoch
    loc_view := by frA hI.loc_view
    loc_started := by frA hI.loc_started
    loc_member := by frA hI.loc_member
    loc_member0 := by frA hI.loc_member0
    loc_leaderArr := by
      intro q hql j
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls] at hql
        exact absurd hql (hI.loc_follower q hf).1
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_elog] at hql ⊢
        exact hI.loc_leaderArr q hql j
    loc_leader := by
      intro q hql
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, hf] at hql; cases hql
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_base] at hql ⊢
        exact hI.loc_leader q hql
    loc_follower := by frA hI.loc_follower
    loc_elog := by
      intro q j x hx
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, State.setLoc_elog] at hx ⊢
        by_cases hjk : j = k
        · subst hjk
          simp only [Function.update_self, Option.some.injEq] at hx
          subst hx; exact helog
        · rw [Function.update_of_ne hjk] at hx; exact hI.loc_elog q j x hx
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_elog] at hx ⊢
        exact hI.loc_elog q j x hx
    loc_base := by
      intro q hin j v hv
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, State.setLoc_base] at hin hv ⊢
        have := hI.loc_base q hin j v hv
        by_cases hjk : j = k
        · subst hjk; rw [hk0] at this; cases this
        · rw [Function.update_of_ne hjk]; exact this
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_base] at hin hv ⊢
        exact hI.loc_base q hin j v hv
    loc_acked := by
      intro q j t' d' ha
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, acked_setLoc] at ha ⊢
        obtain ⟨l', hl'⟩ := hI.loc_acked q j t' d' ha
        by_cases hjk : j = k
        · subst hjk; rw [hk0] at hl'; cases hl'
        · rw [Function.update_of_ne hjk]; exact ⟨l', hl'⟩
      · simp only [State.setLoc_loc_ne _ _ _ hq, acked_setLoc] at ha ⊢
        exact hI.loc_acked q j t' d' ha
    loc_acked_epoch := by frA hI.loc_acked_epoch
    loc_dec := by
      intro q j hj
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, accL_setLoc, State.setLoc_hist] at hj ⊢
        by_cases hjk : j = k
        · subst hjk; simp at hj
        · rw [Function.update_of_ne hjk] at hj
          exact hI.loc_dec q j hj
      · simp only [State.setLoc_loc_ne _ _ _ hq, accL_setLoc, State.setLoc_hist] at hj ⊢
        exact hI.loc_dec q j hj
    loc_acceptAcks := by frA hI.loc_acceptAcks
    loc_probeAcks := by frA hI.loc_probeAcks
    prb := by frA hI.prb
    probe_old := by frA hI.probe_old
    probe_sent := by frA hI.probe_sent
    m_probeAck := by frA hI.m_probeAck
    m_frozen := by frA hI.m_frozen
    m_prepare := by frA hI.m_prepare
    m_prepareAck := by frA hI.m_prepareAck
    m_accept := by frA hI.m_accept
    m_acceptAck := by frA hI.m_acceptAck
    m_decision := by frA hI.m_decision
    m_newConfig := by frA hI.m_newConfig
    m_newState := by frA hI.m_newState
    net_sub := by frA hI.net_sub
    nc_unique := by frA hI.nc_unique
    nc_count := by frA hI.nc_count
    nc_flight := by frA hI.nc_flight
    ns_unique := by frA hI.ns_unique
    ns_count := by frA hI.ns_count
    ns_flight := by frA hI.ns_flight
    hist_certify := by frA hI.hist_certify
    hist_certify_unique := by frA hI.hist_certify_unique
    hist_decide := by frA hI.hist_decide
    hist_decide_unique := by frA hI.hist_decide_unique
    hist_decide_idx := by frA hI.hist_decide_idx
    hist_certify_idx := by frA hI.hist_certify_idx
    hist_decide_after := by frA hI.hist_decide_after
    hist_order := by frA hI.hist_order
    vinfo_len := by frA hI.vinfo_len
  }

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem State.setLoc_self (st : State T Pl S P) (p : P) : st.setLoc p (st.loc p) = st := by
  unfold State.setLoc; simp

/-- Delivery of `ACCEPT(e, k, t, l, d)` (lines 21–25). -/
theorem Inv.deliver_accept (hI : Inv Pa st) {src dst : P} {e k : ℕ} {t : T} {l : Pl} {d : Dec}
    (hm : Msg.accept e k t l d ∈ st.sent src dst)
    (h : handle Pa st src dst (.accept e k t l d) = some st') : Inv Pa st' := by
  simp only [handle] at h
  split_ifs at h with hc hph <;> cases h
  · obtain ⟨hf, he⟩ := hc
    obtain ⟨o, ho⟩ := hI.m_accept _ _ _ _ _ _ _ hm
    have hI1 := hI.setLoc_accept hf hph ⟨o, by rw [he]; exact ho⟩ _ rfl
    refine hI1.send_acceptAck (k := k) (t := t) (d := d) (by simpa using hf) ⟨l, by simp⟩ _ fun b m hb => ?_
    split_ifs at hb
    cases hb
    simp [he]
  · obtain ⟨hf, he⟩ := hc
    obtain ⟨o, ho⟩ := hI.m_accept _ _ _ _ _ _ _ hm
    show Inv Pa ((st.setLoc dst (st.loc dst)).send1 dst src _)
    rw [State.setLoc_self]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((hI.loc_ent dst k).2 hph)
    obtain ⟨o', ho'⟩ := hI.loc_elog dst k x hx
    rw [he, ho] at ho'
    cases ho'
    refine hI.send_acceptAck hf ⟨l, hx⟩ _ fun b m hb => ?_
    split_ifs at hb
    cases hb
    simp [he]

set_option hygiene false in
local macro "frC " h:term : tactic => `(tactic| simpa only [hS, hEpH, hMbH, hLdH, hNx, hArr, hIn,
  hNE, hPr, hPE, hPM, hRE, hRS, hAA, hPA, hD, hK, cfg_setLoc, State.setLoc_cs, State.setLoc_hist,
  State.setLoc_sent, State.setLoc_net, State.setLoc_started, State.setLoc_elog, State.setLoc_base,
  State.setLoc_vinfo, acked_setLoc, replied_setLoc, accL_setLoc, decided_setLoc, fresh_setLoc,
  plAt_setLoc, decIn_setLoc] using $h)

/-- Adopting a configuration of another shard (lines 67–69). -/
theorem Inv.setLoc_configChange (hI : Inv Pa st) {p : P} {s : S} {e : ℕ} {c : Config P}
    (hcs : cfg st s e = some c) (hs : s ≠ Pa.home p) (ls : LState T Pl S P)
    (hls : ls = { st.loc p with
        epoch := Function.update (st.loc p).epoch s e
        members := Function.update (st.loc p).members s c.members
        leader := Function.update (st.loc p).leader s c.leader }) :
    Inv Pa (st.setLoc p ls) := by
  have hS := State.setLoc_proj st p ls (·.status) (by rw [hls])
  have hNx := State.setLoc_proj st p ls (·.next) (by rw [hls])
  have hArr := State.setLoc_proj st p ls (·.arr) (by rw [hls])
  have hIn := State.setLoc_proj st p ls (·.initialized) (by rw [hls])
  have hNE := State.setLoc_proj st p ls (·.newEpoch) (by rw [hls])
  have hPr := State.setLoc_proj st p ls (·.probing) (by rw [hls])
  have hPE := State.setLoc_proj st p ls (·.probedEpoch) (by rw [hls])
  have hPM := State.setLoc_proj st p ls (·.probedMembers) (by rw [hls])
  have hRE := State.setLoc_proj st p ls (·.reconEpoch) (by rw [hls])
  have hRS := State.setLoc_proj st p ls (·.reconShard) (by rw [hls])
  have hAA := State.setLoc_proj st p ls (·.acceptAcks) (by rw [hls])
  have hPA := State.setLoc_proj st p ls (·.probeAcks) (by rw [hls])
  have hEpH : ∀ q, ((st.setLoc p ls).loc q).epoch (Pa.home q) = (st.loc q).epoch (Pa.home q) := by
    intro q
    rcases eq_or_ne q p with rfl | hq
    · simp [hls, Function.update_of_ne (Ne.symm hs)]
    · rw [State.setLoc_loc_ne _ _ _ hq]
  have hMbH : ∀ q, ((st.setLoc p ls).loc q).members (Pa.home q) =
      (st.loc q).members (Pa.home q) := by
    intro q
    rcases eq_or_ne q p with rfl | hq
    · simp [hls, Function.update_of_ne (Ne.symm hs)]
    · rw [State.setLoc_loc_ne _ _ _ hq]
  have hLdH : ∀ q, ((st.setLoc p ls).loc q).leader (Pa.home q) =
      (st.loc q).leader (Pa.home q) := by
    intro q
    rcases eq_or_ne q p with rfl | hq
    · simp [hls, Function.update_of_ne (Ne.symm hs)]
    · rw [State.setLoc_loc_ne _ _ _ hq]
  have hD := dead_setLoc st p ls (by rw [hls])
  have hK := aliveK_setLoc st p ls (by rw [hls])
  exact {
    cs_zero := by frC hI.cs_zero
    cfg_wf := by frC hI.cfg_wf
    cfg_mem := by frC hI.cfg_mem
    frz := by frC hI.frz
    leader_init := by frC hI.leader_init
    init_init := by frC hI.init_init
    started_cfg := by frC hI.started_cfg
    started_leader := by
      intro s' e' c' hst hc
      simp only [State.setLoc_started, cfg_setLoc] at hst hc
      obtain ⟨hlm, hhome, -⟩ := hI.cfg_wf s' e' c' hc
      have hh := hhome _ hlm
      subst hh
      rw [hEpH]
      exact hI.started_leader _ e' c' hst hc
    elog_started := by frC hI.elog_started
    base_elog := by frC hI.base_elog
    elog_above := by frC hI.elog_above
    elog_origin := by frC hI.elog_origin
    elog_dist := by frC hI.elog_dist
    elog_txn := by frC hI.elog_txn
    vinfo_none := by frC hI.vinfo_none
    vinfo_ok := by frC hI.vinfo_ok
    inv2 := by
      intro s' E c' hc hst e' he' j v hv hal
      simp only [State.setLoc_started, hNE, cfg_setLoc] at hst hc
      have hC : cand (st.setLoc p ls) s' E c' = cand st s' E c' := by
        by_cases hl : c'.leader = p
        · obtain ⟨hlm, hhome, -⟩ := hI.cfg_wf s' E c' hc
          have hh := hhome _ hlm
          rw [hl] at hh
          subst hh
          simp only [cand, State.setLoc_started, State.setLoc_base, State.setLoc_elog, hl,
            State.setLoc_loc_self, hls, Function.update_of_ne (Ne.symm hs)]
        · exact cand_setLoc_of_ne _ _ _ hl
      rw [hC]
      exact hI.inv2 s' E c' hc hst e' he' j v hv (by rwa [hK] at hal)
    loc_len := by frC hI.loc_len
    loc_ent := by frC hI.loc_ent
    loc_newEpoch := by frC hI.loc_newEpoch
    loc_view := by
      intro q s'
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, cfg_setLoc]
        by_cases hss : s' = s
        · subst hss
          simp only [Function.update_self]
          exact hcs
        · simp only [Function.update_of_ne hss]
          exact hI.loc_view q s'
      · simp only [State.setLoc_loc_ne _ _ _ hq, cfg_setLoc]
        exact hI.loc_view q s'
    loc_started := by frC hI.loc_started
    loc_member := by frC hI.loc_member
    loc_member0 := by frC hI.loc_member0
    loc_leaderArr := by frC hI.loc_leaderArr
    loc_leader := by frC hI.loc_leader
    loc_follower := by frC hI.loc_follower
    loc_elog := by frC hI.loc_elog
    loc_base := by frC hI.loc_base
    loc_acked := by frC hI.loc_acked
    loc_acked_epoch := by frC hI.loc_acked_epoch
    loc_dec := by frC hI.loc_dec
    loc_acceptAcks := by frC hI.loc_acceptAcks
    loc_probeAcks := by frC hI.loc_probeAcks
    prb := by frC hI.prb
    probe_old := by frC hI.probe_old
    probe_sent := by frC hI.probe_sent
    m_probeAck := by frC hI.m_probeAck
    m_frozen := by frC hI.m_frozen
    m_prepare := by frC hI.m_prepare
    m_prepareAck := by frC hI.m_prepareAck
    m_accept := by frC hI.m_accept
    m_acceptAck := by frC hI.m_acceptAck
    m_decision := by frC hI.m_decision
    m_newConfig := by frC hI.m_newConfig
    m_newState := by frC hI.m_newState
    net_sub := by frC hI.net_sub
    nc_unique := by frC hI.nc_unique
    nc_count := by frC hI.nc_count
    nc_flight := by frC hI.nc_flight
    ns_unique := by frC hI.ns_unique
    ns_count := by frC hI.ns_count
    ns_flight := by frC hI.ns_flight
    hist_certify := by frC hI.hist_certify
    hist_certify_unique := by frC hI.hist_certify_unique
    hist_decide := by frC hI.hist_decide
    hist_decide_unique := by frC hI.hist_decide_unique
    hist_decide_idx := by frC hI.hist_decide_idx
    hist_certify_idx := by frC hI.hist_certify_idx
    hist_decide_after := by frC hI.hist_decide_after
    hist_order := by frC hI.hist_order
    vinfo_len := by frC hI.vinfo_len
  }

/-- The `CONFIG_CHANGE` step (lines 67–69). -/
theorem Inv.step_configChange (hI : Inv Pa st) {p : P} {s : S} {e : ℕ}
    (h : step Pa st (.configChange p s e) = some st') : Inv Pa st' := by
  simp only [step] at h
  split at h
  · rename_i c hc
    split_ifs at h with hcond
    cases h
    exact hI.setLoc_configChange hc hcond.1 _ rfl
  · cases h

set_option hygiene false in
local macro "frN " h:term : tactic => `(tactic| simpa only [hNx, hNE, hPr, hPE, hPM, hRE, hRS, hAA,
  hPA, hD, hK, cfg_setLoc, State.setLoc_cs, State.setLoc_hist,
  State.setLoc_sent, State.setLoc_net, State.setLoc_started, State.setLoc_elog, State.setLoc_base,
  State.setLoc_vinfo, acked_setLoc, replied_setLoc, accL_setLoc, decided_setLoc, fresh_setLoc,
  plAt_setLoc, decIn_setLoc] using $h)

/-- Adopting the state of a new leader (lines 62–66) at `p`. -/
theorem Inv.setLoc_newState (hI : Inv Pa st) {src p : P} {e : ℕ} {M : Finset P}
    {a : Arrays T Pl} (hm : Msg.newState e M a ∈ st.sent src p)
    (hne : (st.loc p).newEpoch ≤ e)
    (hfl : (st.loc p).epoch (Pa.home p) < e ∨ e < (st.loc p).newEpoch)
    (hgone : ∀ r M' a', Msg.newState e M' a' ∉ st.net r p) (ls : LState T Pl S P)
    (hls : ls = { st.loc p with
        initialized := true
        status := .follower
        epoch := Function.update (st.loc p).epoch (Pa.home p) e
        members := Function.update (st.loc p).members (Pa.home p) M
        leader := Function.update (st.loc p).leader (Pa.home p) src
        arr := a }) :
    Inv Pa (st.setLoc p ls) := by
  have hNx := State.setLoc_proj st p ls (·.next) (by rw [hls])
  have hNE := State.setLoc_proj st p ls (·.newEpoch) (by rw [hls])
  have hPr := State.setLoc_proj st p ls (·.probing) (by rw [hls])
  have hPE := State.setLoc_proj st p ls (·.probedEpoch) (by rw [hls])
  have hPM := State.setLoc_proj st p ls (·.probedMembers) (by rw [hls])
  have hRE := State.setLoc_proj st p ls (·.reconEpoch) (by rw [hls])
  have hRS := State.setLoc_proj st p ls (·.reconShard) (by rw [hls])
  have hAA := State.setLoc_proj st p ls (·.acceptAcks) (by rw [hls])
  have hPA := State.setLoc_proj st p ls (·.probeAcks) (by rw [hls])
  have hD := dead_setLoc st p ls (by rw [hls])
  have hK := aliveK_setLoc st p ls (by rw [hls])
  have hlt : (st.loc p).epoch (Pa.home p) < e := by omega
  obtain ⟨hcfg, hpM, hps, hstarted, hent, hlen, hentph, hdec⟩ := hI.m_newState _ _ _ _ _ hm
  have hmemNE : ∀ z < e, ∀ cz, cfg st (Pa.home p) z = some cz → p ∈ cz.members →
      e ≤ (st.loc p).newEpoch := fun z hz cz hcz hpz =>
    hI.newEpoch_of_mem hcfg hpM hz hcz hpz
  have hInM : ∀ q, (st.loc q).initialized = true → ((st.setLoc p ls).loc q).initialized = true := by
    intro q hq
    rcases eq_or_ne q p with rfl | hq'
    · simp [hls]
    · rw [State.setLoc_loc_ne _ _ _ hq']; exact hq
  have hEpGe : ∀ q s, (st.loc q).epoch s ≤ ((st.setLoc p ls).loc q).epoch s := by
    intro q s
    rcases eq_or_ne q p with rfl | hq'
    · simp only [State.setLoc_loc_self, hls]
      by_cases hs : s = Pa.home q
      · subst hs; simp only [Function.update_self]; omega
      · simp [Function.update_of_ne hs]
    · rw [State.setLoc_loc_ne _ _ _ hq']
  exact {
    cs_zero := by frN hI.cs_zero
    cfg_wf := by frN hI.cfg_wf
    cfg_mem := by frN hI.cfg_mem
    frz := by frN hI.frz
    leader_init := by
      intro s e' c hc
      exact hInM _ (hI.leader_init s e' c hc)
    init_init := by
      intro s q hq
      exact hInM _ (hI.init_init s q hq)
    started_cfg := by frN hI.started_cfg
    started_leader := by
      intro s e' c hst hc
      exact le_trans (hI.started_leader s e' c hst hc) (hEpGe _ _)
    elog_started := by frN hI.elog_started
    base_elog := by frN hI.base_elog
    elog_above := by frN hI.elog_above
    elog_origin := by frN hI.elog_origin
    elog_dist := by frN hI.elog_dist
    elog_txn := by frN hI.elog_txn
    vinfo_none := by frN hI.vinfo_none
    vinfo_ok := by frN hI.vinfo_ok
    inv2 := by
      intro s E c hc hst e' he' j v hv hal
      simp only [State.setLoc_started, hNE, cfg_setLoc] at hst hc
      have hC : cand (st.setLoc p ls) s E c = cand st s E c := by
        by_cases hsE : st.started s E = true
        · exact cand_setLoc_of_started _ _ _ hsE
        · by_cases hl : c.leader = p
          · exfalso
            have hE := hst.resolve_left hsE
            obtain ⟨hlm, hhome, -⟩ := hI.cfg_wf s E c hc
            have hh := hhome _ hlm
            rw [hl] at hh hlm hE
            subst hh
            have hEe : E < e := by
              rcases (hE ▸ hne : E ≤ e).lt_or_eq with h | h
              · exact h
              · subst h; exact absurd hstarted hsE
            have := hmemNE E hEe c hc hlm
            omega
          · exact cand_setLoc_of_ne _ _ _ hl
      rw [hC]
      exact hI.inv2 s E c hc hst e' he' j v hv (by rwa [hK] at hal)
    loc_len := by
      intro q j hj
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls] at hj ⊢
        exact hlen j hj
      · simp only [State.setLoc_loc_ne _ _ _ hq] at hj ⊢
        exact hI.loc_len q j hj
    loc_ent := by
      intro q j
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls]
        exact hentph j
      · simp only [State.setLoc_loc_ne _ _ _ hq]
        exact hI.loc_ent q j
    loc_newEpoch := by
      intro q hst
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self]
        exact hne
      · simp only [State.setLoc_loc_ne _ _ _ hq] at hst ⊢
        exact hI.loc_newEpoch q hst
    loc_view := by
      intro q s
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, cfg_setLoc]
        by_cases hss : s = Pa.home q
        · subst hss
          simp only [Function.update_self]
          exact hcfg
        · simp only [Function.update_of_ne hss]
          exact hI.loc_view q s
      · simp only [State.setLoc_loc_ne _ _ _ hq, cfg_setLoc]
        exact hI.loc_view q s
    loc_started := by
      intro q
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self, State.setLoc_started]
        exact hstarted
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_started]
        exact hI.loc_started q
    loc_member := by
      intro q hin
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self]
        exact hpM
      · simp only [State.setLoc_loc_ne _ _ _ hq] at hin ⊢
        exact hI.loc_member q hin
    loc_member0 := by
      intro q
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self]
        exact Or.inr hpM
      · simp only [State.setLoc_loc_ne _ _ _ hq]
        exact hI.loc_member0 q
    loc_leaderArr := by
      intro q hql j
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self] at hql
        exact absurd hql.symm hps
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_elog] at hql ⊢
        exact hI.loc_leaderArr q hql j
    loc_leader := by
      intro q hql
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls] at hql
        cases hql
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_base] at hql ⊢
        exact hI.loc_leader q hql
    loc_follower := by
      intro q hql
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self]
        exact ⟨Ne.symm hps, by simp, hpM⟩
      · simp only [State.setLoc_loc_ne _ _ _ hq] at hql ⊢
        exact hI.loc_follower q hql
    loc_elog := by
      intro q j x hx
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self, State.setLoc_elog] at hx ⊢
        rw [hent] at hx
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hx
        exact ⟨v.2, hI.base_elog _ _ _ _ hv⟩
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_elog] at hx ⊢
        exact hI.loc_elog q j x hx
    loc_base := by
      intro q hin j v hv
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self, State.setLoc_base] at hv ⊢
        rw [hent, hv]; rfl
      · simp only [State.setLoc_loc_ne _ _ _ hq, State.setLoc_base] at hin hv ⊢
        exact hI.loc_base q hin j v hv
    loc_acked := by
      intro q j t' d' ha
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self, acked_setLoc] at ha
        have := (hI.loc_acked_epoch q _ _ j t' d' ha).2.1
        omega
      · simp only [State.setLoc_loc_ne _ _ _ hq, acked_setLoc] at ha ⊢
        exact hI.loc_acked q j t' d' ha
    loc_acked_epoch := by
      intro q s e' j t' d' ha
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self, acked_setLoc] at ha ⊢
        obtain ⟨h1, h2, -⟩ := hI.loc_acked_epoch q s e' j t' d' ha
        exact ⟨h1, by omega, trivial⟩
      · simp only [State.setLoc_loc_ne _ _ _ hq, acked_setLoc] at ha ⊢
        exact hI.loc_acked_epoch q s e' j t' d' ha
    loc_dec := by
      intro q j hj
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self, accL_setLoc, State.setLoc_hist] at hj ⊢
        exact hdec j hj
      · simp only [State.setLoc_loc_ne _ _ _ hq, accL_setLoc, State.setLoc_hist] at hj ⊢
        exact hI.loc_dec q j hj
    loc_acceptAcks := by frN hI.loc_acceptAcks
    loc_probeAcks := by frN hI.loc_probeAcks
    prb := by frN hI.prb
    probe_old := by frN hI.probe_old
    probe_sent := by frN hI.probe_sent
    m_probeAck := by
      intro q r b E s h
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI.m_probeAck q r b E s h
      refine ⟨h1, by rw [hNE]; exact h2, h3, fun hb => hInM _ (h4 hb), h5⟩
    m_frozen := by
      intro q b E s hR hE hns
      simp only [replied_setLoc, hNE, State.setLoc_started] at hR hE hns
      rcases eq_or_ne q p with rfl | hq
      · exfalso
        obtain ⟨r, hr⟩ := hR
        obtain ⟨rfl, -, hpr, -⟩ := hI.m_probeAck q r b E s hr
        obtain ⟨-, z, hz, cz, hcz, hqz⟩ := hI.probe_sent r q E hpr
        have hEe : E < e := by
          rcases (hE ▸ hne : E ≤ e).lt_or_eq with h | h
          · exact h
          · subst h; rw [hstarted] at hns; cases hns
        have := hmemNE z (by omega) cz hcz hqz
        omega
      · rw [State.setLoc_loc_ne _ _ _ hq]
        exact hI.m_frozen q b E s hR hE hns
    m_prepare := by frN hI.m_prepare
    m_prepareAck := by frN hI.m_prepareAck
    m_accept := by frN hI.m_accept
    m_acceptAck := by frN hI.m_acceptAck
    m_decision := by frN hI.m_decision
    m_newConfig := by frN hI.m_newConfig
    m_newState := by frN hI.m_newState
    net_sub := by frN hI.net_sub
    nc_unique := by frN hI.nc_unique
    nc_count := by frN hI.nc_count
    nc_flight := by
      intro r q e' M' h
      simp only [State.setLoc_net, State.setLoc_started, hNE] at h ⊢
      obtain ⟨h1, h2⟩ := hI.nc_flight r q e' M' h
      refine ⟨h1, ?_⟩
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self]
        rcases lt_trichotomy e e' with h3 | rfl | h3
        · exact Or.inl h3
        · rw [hstarted] at h1; cases h1
        · right
          obtain ⟨-, hc', -⟩ := hI.m_newConfig r q e' M' ((hI.net_sub r q).subset h)
          have := hmemNE e' h3 _ hc' (hI.cfg_wf _ _ _ hc').1
          omega
      · rw [State.setLoc_loc_ne _ _ _ hq]; exact h2
    ns_unique := by frN hI.ns_unique
    ns_count := by frN hI.ns_count
    ns_flight := by
      intro r q e' M' a' h
      simp only [State.setLoc_net, hNE] at h ⊢
      rcases eq_or_ne q p with rfl | hq
      · simp only [State.setLoc_loc_self, hls, Function.update_self]
        rcases lt_trichotomy e e' with h3 | rfl | h3
        · exact Or.inl h3
        · exact absurd h (hgone r M' a')
        · right
          obtain ⟨hc', hqM', -⟩ := hI.m_newState r q e' M' a' ((hI.net_sub r q).subset h)
          have := hmemNE e' h3 _ hc' hqM'
          omega
      · rw [State.setLoc_loc_ne _ _ _ hq]; exact hI.ns_flight r q e' M' a' h
    hist_certify := by frN hI.hist_certify
    hist_certify_unique := by frN hI.hist_certify_unique
    hist_decide := by frN hI.hist_decide
    hist_decide_unique := by frN hI.hist_decide_unique
    hist_decide_idx := by frN hI.hist_decide_idx
    hist_certify_idx := by frN hI.hist_certify_idx
    hist_decide_after := by frN hI.hist_decide_after
    hist_order := by frN hI.hist_order
    vinfo_len := by frN hI.vinfo_len
  }

/-- Delivery of `NEW_STATE(e, M, a)` (lines 61–66). The hypotheses `hfl` and `hgone` hold for a
delivery step by `Inv.ns_flight` and `Inv.ns_gone`. -/
theorem Inv.deliver_newState (hI : Inv Pa st) {src dst : P} {e : ℕ} {M : Finset P}
    {a : Arrays T Pl} (hm : Msg.newState e M a ∈ st.sent src dst)
    (hfl : (st.loc dst).epoch (Pa.home dst) < e ∨ e < (st.loc dst).newEpoch)
    (hgone : ∀ p M' a', Msg.newState e M' a' ∉ st.net p dst)
    (h : handle Pa st src dst (.newState e M a) = some st') : Inv Pa st' := by
  simp only [handle] at h
  split_ifs at h with hc
  cases h
  exact hI.setLoc_newState hm hc hfl hgone _ rfl

end Podc.ReconfigurableCommit
