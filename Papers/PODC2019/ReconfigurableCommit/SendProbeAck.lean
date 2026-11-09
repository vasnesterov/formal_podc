/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Send

/-!
# Sending `PROBE_ACK` preserves the invariant

`Inv.send_probeAck`: the reply to a `PROBE` (line 44) preserves `Inv`.
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The conditions for `src` to send `PROBE_ACK(b, E, s)` (line 44). -/
def PAOK (Pa : Params T Pl S P) (st : State T Pl S P) (src r : P) : Msg T Pl S P → Prop
  | .probeAck b E s => s = Pa.home src ∧ (st.loc src).newEpoch = E ∧
      (st.loc src).status = .reconfiguring ∧ Msg.probe E ∈ st.sent r src ∧
      b = (st.loc src).initialized
  | _ => False

set_option hygiene false in
/-- Rewrite the derived notions of a sent-to state back to the original state. -/
local macro "sframe " h:term : tactic => `(tactic| simpa only [hA, hD, hK, hL, hDe, cfg_send,
  State.send_loc, State.send_cs, State.send_hist, State.send_started, State.send_elog,
  State.send_base, State.send_vinfo, fresh_send, cand_send, plAt_send, decIn_send] using $h)

theorem Inv.send_probeAck {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st) (src : P)
    (out : P → Option (Msg T Pl S P)) (hout : ∀ b m, out b = some m → PAOK Pa st src b m) :
    Inv Pa (st.send src out) := by
  have hNA : NoAcceptAck out := fun b s e k t d h => by simpa [PAOK] using hout _ _ h
  have hA := acked_send st src out hNA
  have hD := dead_send st src out hNA
  have hK := aliveK_send st src out hNA
  have hL := accL_send st src out hNA
  have hDe := decided_send st src out Pa hNA
  have hM := fun {m : Msg T Pl S P} {a b : P} => State.mem_send_sent st src out (m := m) (a := a) (b := b)
  have hN := fun {m : Msg T Pl S P} {a b : P} => State.mem_send_net st src out (m := m) (a := a) (b := b)
  have old : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ (st.send src out).sent a b →
      (∀ b, ¬ PAOK Pa st src b m) → m ∈ st.sent a b := by
    intro m a b h hn
    rcases hM.1 h with h | ⟨-, h⟩
    · exact h
    · exact absurd (hout _ _ h) (hn _)
  have oldN : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ (st.send src out).net a b →
      (∀ b, ¬ PAOK Pa st src b m) → m ∈ st.net a b := by
    intro m a b h hn
    rcases hN.1 h with h | ⟨-, h⟩
    · exact h
    · exact absurd (hout _ _ h) (hn _)
  have new : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ st.sent a b → m ∈ (st.send src out).sent a b :=
    fun h => hM.2 (Or.inl h)
  have oldI : ∀ {m : Msg T Pl S P} {a b : P} {i : ℕ}, ((st.send src out).sent a b)[i]? = some m →
      (∀ b, ¬ PAOK Pa st src b m) → (st.sent a b)[i]? = some m := by
    intro m a b i h hn
    rw [State.send_sent] at h
    split_ifs at h
    · rcases getElem?_append_toList h with h | ⟨-, h⟩
      · exact h
      · exact absurd (hout _ _ h) (hn _)
    · exact h
  exact {
    cs_zero := by sframe hI.cs_zero
    cfg_wf := by sframe hI.cfg_wf
    cfg_mem := by
      intro s E c hE hc
      obtain ⟨pe, hpe, h1, h2, h3, h4⟩ := hI.cfg_mem s E c hE hc
      refine ⟨pe, hpe, by simpa only [hD] using h1, replied_mono_send _ _ _ h2, h3, fun q hq => ?_⟩
      rcases h4 q hq with h | ⟨⟨b, hb⟩, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨b, replied_mono_send _ _ _ hb⟩, h⟩
    frz := by sframe hI.frz
    leader_init := by sframe hI.leader_init
    init_init := by sframe hI.init_init
    started_cfg := by sframe hI.started_cfg
    started_leader := by sframe hI.started_leader
    elog_started := by sframe hI.elog_started
    base_elog := by sframe hI.base_elog
    elog_above := by sframe hI.elog_above
    elog_origin := by sframe hI.elog_origin
    elog_dist := by sframe hI.elog_dist
    elog_txn := by sframe hI.elog_txn
    vinfo_none := by sframe hI.vinfo_none
    vinfo_ok := by sframe hI.vinfo_ok
    inv2 := by sframe hI.inv2
    loc_len := by sframe hI.loc_len
    loc_ent := by sframe hI.loc_ent
    loc_newEpoch := by sframe hI.loc_newEpoch
    loc_view := by sframe hI.loc_view
    loc_started := by sframe hI.loc_started
    loc_member := by sframe hI.loc_member
    loc_member0 := by sframe hI.loc_member0
    loc_leaderArr := by sframe hI.loc_leaderArr
    loc_leader := by sframe hI.loc_leader
    loc_follower := by sframe hI.loc_follower
    loc_elog := by sframe hI.loc_elog
    loc_base := by sframe hI.loc_base
    loc_acked := by sframe hI.loc_acked
    loc_acked_epoch := by sframe hI.loc_acked_epoch
    loc_dec := by sframe hI.loc_dec
    loc_acceptAcks := by
      intro p q s e k t d h
      exact new (hI.loc_acceptAcks p q s e k t d h)
    loc_probeAcks := by
      intro p q b E s h
      exact new (hI.loc_probeAcks p q b E s h)
    prb := by
      intro p hp
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.prb p hp
      exact ⟨h1, h2, h3, h4, by simpa only [hD, State.send_loc] using h5,
        fun q hq hq' => h6 q (old hq (by simp [PAOK])) hq'⟩
    probe_old := by
      intro r q E h
      simpa using hI.probe_old r q E (old h (by simp [PAOK]))
    probe_sent := by
      intro r q E h
      simpa using hI.probe_sent r q E (old h (by simp [PAOK]))
    m_probeAck := by
      intro q r b E s h
      rcases hM.1 h with h | ⟨heq, h'⟩
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hI.m_probeAck q r b E s h
        exact ⟨h1, h2, new h3, h4, by simpa only [hA, cfg_send] using h5⟩
      · subst heq
        obtain ⟨h1, h2, h3, h4, h5⟩ := hout _ _ h'
        subst h5
        refine ⟨h1, h2.ge, new h4, id, fun hb => ⟨fun e _ k t d hk => ?_, fun e _ c hc hl => ?_⟩⟩
        · rw [hA] at hk
          have := (hI.loc_acked_epoch _ _ _ _ _ _ hk).2.2
          simp_all
        · have := hI.leader_init _ _ _ hc
          rw [hl] at this
          simp_all
    m_frozen := by
      intro q b E s ⟨r, hr⟩ hq hst
      rcases hM.1 hr with hr | ⟨heq, hr'⟩
      · exact hI.m_frozen q b E s ⟨r, hr⟩ hq hst
      · subst heq
        obtain ⟨-, -, h3, -⟩ := hout _ _ hr'
        simpa using h3
    m_prepare := by
      intro a1 a2 a3 a4 h
      exact hI.m_prepare a1 a2 a3 a4 (old h (by simp [PAOK]))
    m_prepareAck := by
      intro a1 a2 a3 a4 a5 a6 a7 a8 h
      exact hI.m_prepareAck a1 a2 a3 a4 a5 a6 a7 a8 (old h (by simp [PAOK]))
    m_accept := by
      intro a1 a2 a3 a4 a5 a6 a7 h
      exact hI.m_accept a1 a2 a3 a4 a5 a6 a7 (old h (by simp [PAOK]))
    m_acceptAck := by
      intro q r s e k t d h
      simpa using hI.m_acceptAck q r s e k t d (old h (by simp [PAOK]))
    m_decision := by
      intro a1 a2 a3 a4 a5 h
      rw [hL]
      exact hI.m_decision a1 a2 a3 a4 a5 (old h (by simp [PAOK]))
    m_newConfig := by
      intro r q e M h
      obtain ⟨h1, h2, h3⟩ := hI.m_newConfig r q e M (old h (by simp [PAOK]))
      exact ⟨h1, h2, replied_mono_send _ _ _ h3⟩
    m_newState := by
      intro p q e M a h
      simpa only [hL, cfg_send, State.send_started, State.send_base, State.send_hist] using
        hI.m_newState p q e M a (old h (by simp [PAOK]))
    net_sub := by
      intro a b
      rw [State.send_net, State.send_sent]
      split_ifs
      · exact (hI.net_sub a b).append_right _
      · exact hI.net_sub a b
    nc_unique := by
      intro r q e M r' q' M' h h'
      exact hI.nc_unique r q e M r' q' M' (old h (by simp [PAOK])) (old h' (by simp [PAOK]))
    nc_count := by
      intro r q e M M' i j h h'
      exact hI.nc_count r q e M M' i j (oldI h (by simp [PAOK])) (oldI h' (by simp [PAOK]))
    nc_flight := by
      intro r q e M h
      simpa using hI.nc_flight r q e M (oldN h (by simp [PAOK]))
    ns_unique := by
      intro p q e M a p' M' a' h h'
      exact hI.ns_unique p q e M a p' M' a' (old h (by simp [PAOK])) (old h' (by simp [PAOK]))
    ns_count := by
      intro p q e M a M' a' i j h h'
      exact hI.ns_count p q e M a M' a' i j (oldI h (by simp [PAOK])) (oldI h' (by simp [PAOK]))
    ns_flight := by
      intro p q e M a h
      simpa using hI.ns_flight p q e M a (oldN h (by simp [PAOK]))
    hist_certify := by sframe hI.hist_certify
    hist_certify_unique := by sframe hI.hist_certify_unique
    hist_decide := by sframe hI.hist_decide
    hist_decide_unique := by sframe hI.hist_decide_unique
    hist_decide_idx := by sframe hI.hist_decide_idx
    hist_certify_idx := by sframe hI.hist_certify_idx
    hist_decide_after := by sframe hI.hist_decide_after
    hist_order := by sframe hI.hist_order
    vinfo_len := by sframe hI.vinfo_len
  }

end Podc.ReconfigurableCommit
