/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Frame

/-!
# Updating the message buffers of a process preserves the invariant
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The state where `p`'s buffers are replaced by `A`, `B`. -/
def State.setBuf (st : State T Pl S P) (p : P) (A : List (P × S × ℕ × ℕ × T × Dec))
    (B : List (P × Bool × ℕ × S)) : State T Pl S P :=
  { st with loc := fun q => { st.loc q with
      acceptAcks := if q = p then A else (st.loc q).acceptAcks
      probeAcks := if q = p then B else (st.loc q).probeAcks } }

theorem State.setLoc_eq_setBuf (st : State T Pl S P) (p : P) (A : List (P × S × ℕ × ℕ × T × Dec))
    (B : List (P × Bool × ℕ × S)) :
    st.setLoc p { st.loc p with acceptAcks := A, probeAcks := B } = st.setBuf p A B := by
  unfold State.setLoc State.setBuf
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · simp [h]

section
variable (st : State T Pl S P) (p : P) (A : List (P × S × ℕ × ℕ × T × Dec))
  (B : List (P × Bool × ℕ × S)) (Pa : Params T Pl S P)
@[simp] theorem setBuf_cs : (st.setBuf p A B).cs = st.cs := rfl
@[simp] theorem setBuf_hist : (st.setBuf p A B).hist = st.hist := rfl
@[simp] theorem setBuf_sent : (st.setBuf p A B).sent = st.sent := rfl
@[simp] theorem setBuf_net : (st.setBuf p A B).net = st.net := rfl
@[simp] theorem setBuf_started : (st.setBuf p A B).started = st.started := rfl
@[simp] theorem setBuf_elog : (st.setBuf p A B).elog = st.elog := rfl
@[simp] theorem setBuf_base : (st.setBuf p A B).base = st.base := rfl
@[simp] theorem setBuf_vinfo : (st.setBuf p A B).vinfo = st.vinfo := rfl
@[simp] theorem setBuf_loc (q : P) : (st.setBuf p A B).loc q = { st.loc q with
      acceptAcks := if q = p then A else (st.loc q).acceptAcks
      probeAcks := if q = p then B else (st.loc q).probeAcks } := rfl
@[simp] theorem cfg_setBuf : cfg (st.setBuf p A B) = cfg st := rfl
@[simp] theorem acked_setBuf : Acked (st.setBuf p A B) = Acked st := rfl
@[simp] theorem replied_setBuf : Replied (st.setBuf p A B) = Replied st := rfl
@[simp] theorem dead_setBuf : Dead (st.setBuf p A B) = Dead st := rfl
@[simp] theorem aliveK_setBuf : AliveK (st.setBuf p A B) = AliveK st := rfl
@[simp] theorem accL_setBuf : AccL (st.setBuf p A B) = AccL st := rfl
@[simp] theorem decided_setBuf : Decided Pa (st.setBuf p A B) = Decided Pa st := rfl
@[simp] theorem cand_setBuf : cand (st.setBuf p A B) = cand st := rfl
@[simp] theorem fresh_setBuf : Fresh (st.setBuf p A B) = Fresh st := rfl
@[simp] theorem plAt_setBuf : plAt Pa (st.setBuf p A B) = plAt Pa st := rfl
@[simp] theorem decIn_setBuf : DecIn (st.setBuf p A B) = DecIn st := rfl
end

set_option hygiene false in
local macro "bframe " h:term : tactic => `(tactic| simpa only [setBuf_cs, setBuf_hist,
  setBuf_sent, setBuf_net, setBuf_started, setBuf_elog, setBuf_base, setBuf_vinfo, setBuf_loc,
  cfg_setBuf, acked_setBuf, replied_setBuf, dead_setBuf, aliveK_setBuf, accL_setBuf,
  decided_setBuf, cand_setBuf, fresh_setBuf, plAt_setBuf, decIn_setBuf] using $h)

theorem Inv.setBuf {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st) (p : P)
    (A : List (P × S × ℕ × ℕ × T × Dec)) (B : List (P × Bool × ℕ × S))
    (hA : ∀ q s e k t d, (q, s, e, k, t, d) ∈ A → Msg.acceptAck s e k t d ∈ st.sent q p)
    (hB : ∀ q b E s, (q, b, E, s) ∈ B → Msg.probeAck b E s ∈ st.sent q p) :
    Inv Pa (st.setBuf p A B) where
  cs_zero := by bframe hI.cs_zero
  cfg_wf := by bframe hI.cfg_wf
  cfg_mem := by bframe hI.cfg_mem
  frz := by bframe hI.frz
  leader_init := by bframe hI.leader_init
  init_init := by bframe hI.init_init
  started_cfg := by bframe hI.started_cfg
  started_leader := by bframe hI.started_leader
  elog_started := by bframe hI.elog_started
  base_elog := by bframe hI.base_elog
  elog_above := by bframe hI.elog_above
  elog_origin := by bframe hI.elog_origin
  elog_dist := by bframe hI.elog_dist
  elog_txn := by bframe hI.elog_txn
  vinfo_none := by bframe hI.vinfo_none
  vinfo_ok := by bframe hI.vinfo_ok
  inv2 := by bframe hI.inv2
  loc_len := by bframe hI.loc_len
  loc_ent := by bframe hI.loc_ent
  loc_newEpoch := by bframe hI.loc_newEpoch
  loc_view := by bframe hI.loc_view
  loc_started := by bframe hI.loc_started
  loc_member := by bframe hI.loc_member
  loc_member0 := by bframe hI.loc_member0
  loc_leaderArr := by bframe hI.loc_leaderArr
  loc_leader := by bframe hI.loc_leader
  loc_follower := by bframe hI.loc_follower
  loc_elog := by bframe hI.loc_elog
  loc_base := by bframe hI.loc_base
  loc_acked := by bframe hI.loc_acked
  loc_acked_epoch := by bframe hI.loc_acked_epoch
  loc_dec := by bframe hI.loc_dec
  loc_acceptAcks := by
    intro q r s e k t d h
    simp only [setBuf_loc, setBuf_sent] at h ⊢
    split_ifs at h with hq
    · subst hq; exact hA r s e k t d h
    · exact hI.loc_acceptAcks q r s e k t d h
  loc_probeAcks := by
    intro q r b E s h
    simp only [setBuf_loc, setBuf_sent] at h ⊢
    split_ifs at h with hq
    · subst hq; exact hB r b E s h
    · exact hI.loc_probeAcks q r b E s h
  prb := by bframe hI.prb
  probe_old := by bframe hI.probe_old
  probe_sent := by bframe hI.probe_sent
  m_probeAck := by bframe hI.m_probeAck
  m_frozen := by bframe hI.m_frozen
  m_prepare := by bframe hI.m_prepare
  m_prepareAck := by bframe hI.m_prepareAck
  m_accept := by bframe hI.m_accept
  m_acceptAck := by bframe hI.m_acceptAck
  m_decision := by bframe hI.m_decision
  m_newConfig := by bframe hI.m_newConfig
  m_newState := by bframe hI.m_newState
  net_sub := by bframe hI.net_sub
  nc_unique := by bframe hI.nc_unique
  nc_count := by bframe hI.nc_count
  nc_flight := by bframe hI.nc_flight
  ns_unique := by bframe hI.ns_unique
  ns_count := by bframe hI.ns_count
  ns_flight := by bframe hI.ns_flight
  hist_certify := by bframe hI.hist_certify
  hist_certify_unique := by bframe hI.hist_certify_unique
  hist_decide := by bframe hI.hist_decide
  hist_decide_unique := by bframe hI.hist_decide_unique
  hist_decide_idx := by bframe hI.hist_decide_idx
  hist_certify_idx := by bframe hI.hist_certify_idx
  hist_decide_after := by bframe hI.hist_decide_after
  hist_order := by bframe hI.hist_order
  vinfo_len := by bframe hI.vinfo_len

end Podc.ReconfigurableCommit
