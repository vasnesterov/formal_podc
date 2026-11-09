/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Frame

/-!
# Updating the probing variables of a process preserves the invariant
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The state where `p`'s probing variables are replaced. -/
def State.setProb (st : State T Pl S P) (p : P) (b : Bool) (pe : ℕ) (pm : Finset P) (E : ℕ)
    (s : S) : State T Pl S P :=
  { st with loc := fun q => { st.loc q with
      probing := if q = p then b else (st.loc q).probing
      probedEpoch := if q = p then pe else (st.loc q).probedEpoch
      probedMembers := if q = p then pm else (st.loc q).probedMembers
      reconEpoch := if q = p then E else (st.loc q).reconEpoch
      reconShard := if q = p then s else (st.loc q).reconShard } }

theorem State.setLoc_eq_setProb (st : State T Pl S P) (p : P) (b : Bool) (pe : ℕ) (pm : Finset P)
    (E : ℕ) (s : S) :
    st.setLoc p { st.loc p with
      probing := b
      probedEpoch := pe
      probedMembers := pm
      reconEpoch := E
      reconShard := s } = st.setProb p b pe pm E s := by
  unfold State.setLoc State.setProb
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · simp [h]

section
variable (st : State T Pl S P) (p : P) (b : Bool) (pe : ℕ) (pm : Finset P) (E : ℕ) (s : S)
  (Pa : Params T Pl S P)
@[simp] theorem setProb_cs : (st.setProb p b pe pm E s).cs = st.cs := rfl
@[simp] theorem setProb_hist : (st.setProb p b pe pm E s).hist = st.hist := rfl
@[simp] theorem setProb_sent : (st.setProb p b pe pm E s).sent = st.sent := rfl
@[simp] theorem setProb_net : (st.setProb p b pe pm E s).net = st.net := rfl
@[simp] theorem setProb_started : (st.setProb p b pe pm E s).started = st.started := rfl
@[simp] theorem setProb_elog : (st.setProb p b pe pm E s).elog = st.elog := rfl
@[simp] theorem setProb_base : (st.setProb p b pe pm E s).base = st.base := rfl
@[simp] theorem setProb_vinfo : (st.setProb p b pe pm E s).vinfo = st.vinfo := rfl
@[simp] theorem setProb_loc (q : P) : (st.setProb p b pe pm E s).loc q = { st.loc q with
      probing := if q = p then b else (st.loc q).probing
      probedEpoch := if q = p then pe else (st.loc q).probedEpoch
      probedMembers := if q = p then pm else (st.loc q).probedMembers
      reconEpoch := if q = p then E else (st.loc q).reconEpoch
      reconShard := if q = p then s else (st.loc q).reconShard } := rfl
@[simp] theorem cfg_setProb : cfg (st.setProb p b pe pm E s) = cfg st := rfl
@[simp] theorem acked_setProb : Acked (st.setProb p b pe pm E s) = Acked st := rfl
@[simp] theorem replied_setProb : Replied (st.setProb p b pe pm E s) = Replied st := rfl
@[simp] theorem dead_setProb : Dead (st.setProb p b pe pm E s) = Dead st := rfl
@[simp] theorem aliveK_setProb : AliveK (st.setProb p b pe pm E s) = AliveK st := rfl
@[simp] theorem accL_setProb : AccL (st.setProb p b pe pm E s) = AccL st := rfl
@[simp] theorem decided_setProb : Decided Pa (st.setProb p b pe pm E s) = Decided Pa st := rfl
@[simp] theorem cand_setProb : cand (st.setProb p b pe pm E s) = cand st := rfl
@[simp] theorem fresh_setProb : Fresh (st.setProb p b pe pm E s) = Fresh st := rfl
@[simp] theorem plAt_setProb : plAt Pa (st.setProb p b pe pm E s) = plAt Pa st := rfl
@[simp] theorem decIn_setProb : DecIn (st.setProb p b pe pm E s) = DecIn st := rfl
end

set_option hygiene false in
local macro "pframe " h:term : tactic => `(tactic| simpa only [setProb_cs, setProb_hist,
  setProb_sent, setProb_net, setProb_started, setProb_elog, setProb_base, setProb_vinfo,
  setProb_loc, cfg_setProb, acked_setProb, replied_setProb, dead_setProb, aliveK_setProb,
  accL_setProb, decided_setProb, cand_setProb, fresh_setProb, plAt_setProb, decIn_setProb]
  using $h)

/-- Updating the probing variables of `p` preserves `Inv`, provided the probing invariants of
`p` hold for the new values. -/
theorem Inv.setProb {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st) (p : P)
    (b : Bool) (pe : ℕ) (pm : Finset P) (E : ℕ) (s : S)
    (hprb : b = true →
      1 ≤ E ∧ pe < E ∧ E ≤ (st.cs s).length ∧ (∃ c, cfg st s pe = some c ∧ c.members = pm) ∧
      (∀ e', pe < e' → e' < E → Dead st s e') ∧
      ∀ q, Msg.probe E ∈ st.sent p q → Pa.home q = s →
        ∃ z, pe ≤ z ∧ z < E ∧ ∃ c, cfg st s z = some c ∧ q ∈ c.members)
    (hold : ∀ q E', Msg.probe E' ∈ st.sent p q →
      E' < (st.cs (Pa.home q)).length ∨ (b = true ∧ E = E' ∧ s = Pa.home q)) :
    Inv Pa (st.setProb p b pe pm E s) where
  cs_zero := by pframe hI.cs_zero
  cfg_wf := by pframe hI.cfg_wf
  cfg_mem := by pframe hI.cfg_mem
  frz := by pframe hI.frz
  leader_init := by pframe hI.leader_init
  init_init := by pframe hI.init_init
  started_cfg := by pframe hI.started_cfg
  started_leader := by pframe hI.started_leader
  elog_started := by pframe hI.elog_started
  base_elog := by pframe hI.base_elog
  elog_above := by pframe hI.elog_above
  elog_origin := by pframe hI.elog_origin
  elog_dist := by pframe hI.elog_dist
  elog_txn := by pframe hI.elog_txn
  vinfo_none := by pframe hI.vinfo_none
  vinfo_ok := by pframe hI.vinfo_ok
  inv2 := by pframe hI.inv2
  loc_len := by pframe hI.loc_len
  loc_ent := by pframe hI.loc_ent
  loc_newEpoch := by pframe hI.loc_newEpoch
  loc_view := by pframe hI.loc_view
  loc_started := by pframe hI.loc_started
  loc_member := by pframe hI.loc_member
  loc_member0 := by pframe hI.loc_member0
  loc_leaderArr := by pframe hI.loc_leaderArr
  loc_leader := by pframe hI.loc_leader
  loc_follower := by pframe hI.loc_follower
  loc_elog := by pframe hI.loc_elog
  loc_base := by pframe hI.loc_base
  loc_acked := by pframe hI.loc_acked
  loc_acked_epoch := by pframe hI.loc_acked_epoch
  loc_dec := by pframe hI.loc_dec
  loc_acceptAcks := by pframe hI.loc_acceptAcks
  loc_probeAcks := by pframe hI.loc_probeAcks
  prb := by
    intro q hq
    by_cases h : q = p
    · subst h
      simp only [setProb_loc, if_true] at hq ⊢
      exact hprb hq
    · simp only [setProb_loc, if_neg h] at hq ⊢
      exact hI.prb q hq
  probe_old := by
    intro r q E h
    by_cases hr : r = p
    · subst hr
      simp only [setProb_loc, if_true]
      exact hold q E h
    · simp only [setProb_loc, if_neg hr]
      exact hI.probe_old r q E h
  probe_sent := by pframe hI.probe_sent
  m_probeAck := by pframe hI.m_probeAck
  m_frozen := by pframe hI.m_frozen
  m_prepare := by pframe hI.m_prepare
  m_prepareAck := by pframe hI.m_prepareAck
  m_accept := by pframe hI.m_accept
  m_acceptAck := by pframe hI.m_acceptAck
  m_decision := by pframe hI.m_decision
  m_newConfig := by pframe hI.m_newConfig
  m_newState := by pframe hI.m_newState
  net_sub := by pframe hI.net_sub
  nc_unique := by pframe hI.nc_unique
  nc_count := by pframe hI.nc_count
  nc_flight := by pframe hI.nc_flight
  ns_unique := by pframe hI.ns_unique
  ns_count := by pframe hI.ns_count
  ns_flight := by pframe hI.ns_flight
  hist_certify := by pframe hI.hist_certify
  hist_certify_unique := by pframe hI.hist_certify_unique
  hist_decide := by pframe hI.hist_decide
  hist_decide_unique := by pframe hI.hist_decide_unique
  hist_decide_idx := by pframe hI.hist_decide_idx
  hist_certify_idx := by pframe hI.hist_certify_idx
  hist_decide_after := by pframe hI.hist_decide_after
  hist_order := by pframe hI.hist_order
  vinfo_len := by pframe hI.vinfo_len

end Podc.ReconfigurableCommit
