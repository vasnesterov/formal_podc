/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Frame

/-!
# Raising `new_epoch` and entering `RECONFIGURING` preserves the invariant (line 42–43)
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The state where `p` is `RECONFIGURING` with `new_epoch = e`. -/
def State.setRaise (st : State T Pl S P) (p : P) (e : ℕ) : State T Pl S P :=
  { st with loc := fun q => { st.loc q with
      status := if q = p then .reconfiguring else (st.loc q).status
      newEpoch := if q = p then e else (st.loc q).newEpoch } }

theorem State.setLoc_eq_setRaise (st : State T Pl S P) (p : P) (e : ℕ) :
    st.setLoc p { st.loc p with status := .reconfiguring, newEpoch := e } = st.setRaise p e := by
  unfold State.setLoc State.setRaise
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · simp [h]

section
variable (st : State T Pl S P) (p : P) (e : ℕ) (Pa : Params T Pl S P)
@[simp] theorem setRaise_cs : (st.setRaise p e).cs = st.cs := rfl
@[simp] theorem setRaise_hist : (st.setRaise p e).hist = st.hist := rfl
@[simp] theorem setRaise_sent : (st.setRaise p e).sent = st.sent := rfl
@[simp] theorem setRaise_net : (st.setRaise p e).net = st.net := rfl
@[simp] theorem setRaise_started : (st.setRaise p e).started = st.started := rfl
@[simp] theorem setRaise_elog : (st.setRaise p e).elog = st.elog := rfl
@[simp] theorem setRaise_base : (st.setRaise p e).base = st.base := rfl
@[simp] theorem setRaise_vinfo : (st.setRaise p e).vinfo = st.vinfo := rfl
@[simp] theorem setRaise_loc (q : P) : (st.setRaise p e).loc q = { st.loc q with
      status := if q = p then .reconfiguring else (st.loc q).status
      newEpoch := if q = p then e else (st.loc q).newEpoch } := rfl
@[simp] theorem cfg_setRaise : cfg (st.setRaise p e) = cfg st := rfl
@[simp] theorem acked_setRaise : Acked (st.setRaise p e) = Acked st := rfl
@[simp] theorem replied_setRaise : Replied (st.setRaise p e) = Replied st := rfl
@[simp] theorem accL_setRaise : AccL (st.setRaise p e) = AccL st := rfl
@[simp] theorem decided_setRaise : Decided Pa (st.setRaise p e) = Decided Pa st := rfl
@[simp] theorem cand_setRaise : cand (st.setRaise p e) = cand st := rfl
@[simp] theorem fresh_setRaise : Fresh (st.setRaise p e) = Fresh st := rfl
@[simp] theorem plAt_setRaise : plAt Pa (st.setRaise p e) = plAt Pa st := rfl
@[simp] theorem decIn_setRaise : DecIn (st.setRaise p e) = DecIn st := rfl
end

variable {st : State T Pl S P} {p : P} {e : ℕ}

theorem ne_raise (hle : (st.loc p).newEpoch ≤ e) (q : P) :
    (st.loc q).newEpoch ≤ ((st.setRaise p e).loc q).newEpoch := by
  simp only [setRaise_loc]
  split_ifs with h
  · subst h; exact hle
  · exact le_rfl

theorem dead_raise (hle : (st.loc p).newEpoch ≤ e) {s : S} {e' : ℕ} (h : Dead st s e') :
    Dead (st.setRaise p e) s e' := by
  obtain ⟨c, hc, q, hq, h1, h2⟩ := h
  exact ⟨c, hc, q, hq, lt_of_lt_of_le h1 (ne_raise hle q), h2⟩

theorem aliveK_raise (hle : (st.loc p).newEpoch ≤ e) {s : S} {e' k : ℕ}
    (h : AliveK (st.setRaise p e) s e' k) : AliveK st s e' k := by
  intro c hc q hq
  rcases h c hc q hq with h | h
  · exact Or.inl h
  · exact Or.inr ((ne_raise hle q).trans h)

set_option hygiene false in
local macro "rframe " h:term : tactic => `(tactic| simpa only [setRaise_cs, setRaise_hist,
  setRaise_sent, setRaise_net, setRaise_started, setRaise_elog, setRaise_base, setRaise_vinfo,
  setRaise_loc, cfg_setRaise, acked_setRaise, replied_setRaise, accL_setRaise,
  decided_setRaise, cand_setRaise, fresh_setRaise, plAt_setRaise, decIn_setRaise] using $h)

/-- Raising `new_epoch` of `p` and setting its status to `RECONFIGURING` preserves `Inv`. -/
theorem Inv.setRaise {Pa : Params T Pl S P} (hI : Inv Pa st) (hle : (st.loc p).newEpoch ≤ e) :
    Inv Pa (st.setRaise p e) where
  cs_zero := by rframe hI.cs_zero
  cfg_wf := by rframe hI.cfg_wf
  cfg_mem := by
    intro s E c hE hc
    obtain ⟨pe, hpe, h1, h2, h3, h4⟩ := hI.cfg_mem s E c hE hc
    exact ⟨pe, hpe, fun e' a b => dead_raise hle (h1 e' a b), h2, h3, h4⟩
  frz := by
    intro s e' h
    obtain ⟨c, hc, q, hq, h'⟩ := hI.frz s e' h
    exact ⟨c, hc, q, hq, lt_of_lt_of_le h' (ne_raise hle q)⟩
  leader_init := by rframe hI.leader_init
  init_init := by rframe hI.init_init
  started_cfg := by rframe hI.started_cfg
  started_leader := by rframe hI.started_leader
  elog_started := by rframe hI.elog_started
  base_elog := by rframe hI.base_elog
  elog_above := by rframe hI.elog_above
  elog_origin := by rframe hI.elog_origin
  elog_dist := by rframe hI.elog_dist
  elog_txn := by rframe hI.elog_txn
  vinfo_none := by rframe hI.vinfo_none
  vinfo_ok := by rframe hI.vinfo_ok
  inv2 := by
    intro s E c hc hpre e' he' k v hv hal
    refine hI.inv2 s E c hc ?_ e' he' k v hv (aliveK_raise hle hal)
    rcases hpre with h | h
    · exact Or.inl h
    · right
      simp only [setRaise_loc] at h
      split_ifs at h with hq
      · -- the leader of `E` already had `newEpoch ≥ E`
        have hle' : E ≤ (st.loc c.leader).newEpoch := by
          rcases Nat.eq_zero_or_pos E with hE | hE
          · omega
          · obtain ⟨-, -, -, hr, -⟩ := hI.cfg_mem s E c hE hc
            obtain ⟨r, hr⟩ := hr
            exact (hI.m_probeAck _ _ _ _ _ hr).2.1
        rw [← hq] at hle
        omega
      · exact h
  loc_len := by rframe hI.loc_len
  loc_ent := by rframe hI.loc_ent
  loc_newEpoch := by
    intro q hq
    simp only [setRaise_loc] at hq ⊢
    split_ifs at hq ⊢ with h
    · exact absurd rfl hq
    · exact hI.loc_newEpoch q hq
  loc_view := by rframe hI.loc_view
  loc_started := by rframe hI.loc_started
  loc_member := by rframe hI.loc_member
  loc_member0 := by rframe hI.loc_member0
  loc_leaderArr := by rframe hI.loc_leaderArr
  loc_leader := by
    intro q hq
    simp only [setRaise_loc, setRaise_base] at hq ⊢
    split_ifs at hq with h
    exact hI.loc_leader q hq
  loc_follower := by
    intro q hq
    simp only [setRaise_loc] at hq ⊢
    split_ifs at hq with h
    exact hI.loc_follower q hq
  loc_elog := by rframe hI.loc_elog
  loc_base := by rframe hI.loc_base
  loc_acked := by rframe hI.loc_acked
  loc_acked_epoch := by rframe hI.loc_acked_epoch
  loc_dec := by rframe hI.loc_dec
  loc_acceptAcks := by rframe hI.loc_acceptAcks
  loc_probeAcks := by rframe hI.loc_probeAcks
  prb := by
    intro q hq
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.prb q (by simpa using hq)
    exact ⟨h1, h2, h3, h4, fun e' a b => dead_raise hle (h5 e' a b), h6⟩
  probe_old := by rframe hI.probe_old
  probe_sent := by rframe hI.probe_sent
  m_probeAck := by
    intro q r b E s h
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI.m_probeAck q r b E s h
    exact ⟨h1, h2.trans (ne_raise hle q), h3, by simpa using h4, by simpa using h5⟩
  m_frozen := by
    intro q b E s hr hq hst
    simp only [setRaise_loc] at hq ⊢
    split_ifs at hq ⊢ with h
    · rfl
    · exact hI.m_frozen q b E s hr hq hst
  m_prepare := by rframe hI.m_prepare
  m_prepareAck := by rframe hI.m_prepareAck
  m_accept := by rframe hI.m_accept
  m_acceptAck := by rframe hI.m_acceptAck
  m_decision := by rframe hI.m_decision
  m_newConfig := by rframe hI.m_newConfig
  m_newState := by rframe hI.m_newState
  net_sub := by rframe hI.net_sub
  nc_unique := by rframe hI.nc_unique
  nc_count := by rframe hI.nc_count
  nc_flight := by
    intro r q e' M h
    obtain ⟨h1, h2⟩ := hI.nc_flight r q e' M h
    refine ⟨h1, ?_⟩
    have := ne_raise hle q
    simp only [setRaise_loc] at this ⊢
    omega
  ns_unique := by rframe hI.ns_unique
  ns_count := by rframe hI.ns_count
  ns_flight := by
    intro p' q e' M a h
    have h2 := hI.ns_flight p' q e' M a h
    have := ne_raise hle q
    simp only [setRaise_loc] at this ⊢
    omega
  hist_certify := by rframe hI.hist_certify
  hist_certify_unique := by rframe hI.hist_certify_unique
  hist_decide := by rframe hI.hist_decide
  hist_decide_unique := by rframe hI.hist_decide_unique
  hist_decide_idx := by rframe hI.hist_decide_idx
  hist_certify_idx := by rframe hI.hist_certify_idx
  hist_decide_after := by rframe hI.hist_decide_after
  hist_order := by rframe hI.hist_order
  vinfo_len := by rframe hI.vinfo_len

end Podc.ReconfigurableCommit
