/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Send

/-!
# Sending `PROBE` preserves the invariant

`Inv.send_probe`: probing (lines 39, 55) preserves `Inv`.
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The conditions for the prober `src` to send `PROBE(E)` to `b` (lines 39, 55). -/
def PrOK (Pa : Params T Pl S P) (st : State T Pl S P) (src b : P) : Msg T Pl S P → Prop
  | .probe E => (st.loc src).probing = true ∧ (st.loc src).reconEpoch = E ∧
      Pa.home b = (st.loc src).reconShard ∧ ∃ z, (st.loc src).probedEpoch ≤ z ∧ z < E ∧
        ∃ c, cfg st (Pa.home b) z = some c ∧ b ∈ c.members
  | _ => False

set_option hygiene false in
/-- Rewrite the derived notions of a sent-to state back to the original state. -/
local macro "sframe " h:term : tactic => `(tactic| simpa only [hA, hR, hD, hK, hL, hDe, cfg_send,
  State.send_loc, State.send_cs, State.send_hist, State.send_started, State.send_elog,
  State.send_base, State.send_vinfo, fresh_send, cand_send, plAt_send, decIn_send] using $h)

theorem Inv.send_probe {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st) (src : P)
    (out : P → Option (Msg T Pl S P)) (hout : ∀ b m, out b = some m → PrOK Pa st src b m) :
    Inv Pa (st.send src out) := by
  have hNA : NoAcceptAck out := fun b s e k t d h => by simpa [PrOK] using hout _ _ h
  have hNP : NoProbeAck out := fun b b' E s h => by simpa [PrOK] using hout _ _ h
  have hA := acked_send st src out hNA
  have hR := replied_send st src out hNP
  have hD := dead_send st src out hNA
  have hK := aliveK_send st src out hNA
  have hL := accL_send st src out hNA
  have hDe := decided_send st src out Pa hNA
  have hM := fun {m : Msg T Pl S P} {a b : P} => State.mem_send_sent st src out (m := m) (a := a) (b := b)
  have hN := fun {m : Msg T Pl S P} {a b : P} => State.mem_send_net st src out (m := m) (a := a) (b := b)
  have old : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ (st.send src out).sent a b →
      (∀ b, ¬ PrOK Pa st src b m) → m ∈ st.sent a b := by
    intro m a b h hn
    rcases hM.1 h with h | ⟨-, h⟩
    · exact h
    · exact absurd (hout _ _ h) (hn _)
  have oldN : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ (st.send src out).net a b →
      (∀ b, ¬ PrOK Pa st src b m) → m ∈ st.net a b := by
    intro m a b h hn
    rcases hN.1 h with h | ⟨-, h⟩
    · exact h
    · exact absurd (hout _ _ h) (hn _)
  have new : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ st.sent a b → m ∈ (st.send src out).sent a b :=
    fun h => hM.2 (Or.inl h)
  have oldI : ∀ {m : Msg T Pl S P} {a b : P} {i : ℕ}, ((st.send src out).sent a b)[i]? = some m →
      (∀ b, ¬ PrOK Pa st src b m) → (st.sent a b)[i]? = some m := by
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
    cfg_mem := by sframe hI.cfg_mem
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
      refine ⟨h1, h2, h3, h4, by simpa only [hD, State.send_loc] using h5, fun q hq hq' => ?_⟩
      rcases hM.1 hq with hq | ⟨heq, hq2⟩
      · exact h6 q hq hq'
      · subst heq
        obtain ⟨-, -, -, z, hz1, hz2, c, hc, hqc⟩ := hout _ _ hq2
        exact ⟨z, hz1, hz2, c, by simpa [hq'] using hc, hqc⟩
    probe_old := by
      intro r q E h
      rcases hM.1 h with h | ⟨heq, h'⟩
      · simpa using hI.probe_old r q E h
      · subst heq
        obtain ⟨h1, h2, h3, -⟩ := hout _ _ h'
        exact Or.inr ⟨h1, h2, h3.symm⟩
    probe_sent := by
      intro r q E h
      rcases hM.1 h with h | ⟨heq, h'⟩
      · simpa using hI.probe_sent r q E h
      · subst heq
        obtain ⟨h1, h2, -, z, -, hz2, c, hc, hqc⟩ := hout _ _ h'
        exact ⟨h2 ▸ (hI.prb r h1).1, z, hz2, c, hc, hqc⟩
    m_probeAck := by
      intro q r b E s h
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI.m_probeAck q r b E s (old h (by simp [PrOK]))
      exact ⟨h1, h2, new h3, h4, by simpa only [hA, cfg_send] using h5⟩
    m_frozen := by sframe hI.m_frozen
    m_prepare := by
      intro a1 a2 a3 a4 h
      exact hI.m_prepare a1 a2 a3 a4 (old h (by simp [PrOK]))
    m_prepareAck := by
      intro a1 a2 a3 a4 a5 a6 a7 a8 h
      exact hI.m_prepareAck a1 a2 a3 a4 a5 a6 a7 a8 (old h (by simp [PrOK]))
    m_accept := by
      intro a1 a2 a3 a4 a5 a6 a7 h
      exact hI.m_accept a1 a2 a3 a4 a5 a6 a7 (old h (by simp [PrOK]))
    m_acceptAck := by
      intro q r s e k t d h
      simpa using hI.m_acceptAck q r s e k t d (old h (by simp [PrOK]))
    m_decision := by
      intro a1 a2 a3 a4 a5 h
      rw [hL]
      exact hI.m_decision a1 a2 a3 a4 a5 (old h (by simp [PrOK]))
    m_newConfig := by
      intro r q e M h
      simpa only [hR, cfg_send] using hI.m_newConfig r q e M (old h (by simp [PrOK]))
    m_newState := by
      intro p q e M a h
      simpa only [hL, cfg_send, State.send_started, State.send_base, State.send_hist] using
        hI.m_newState p q e M a (old h (by simp [PrOK]))
    net_sub := by
      intro a b
      rw [State.send_net, State.send_sent]
      split_ifs
      · exact (hI.net_sub a b).append_right _
      · exact hI.net_sub a b
    nc_unique := by
      intro r q e M r' q' M' h h'
      exact hI.nc_unique r q e M r' q' M' (old h (by simp [PrOK])) (old h' (by simp [PrOK]))
    nc_count := by
      intro r q e M M' i j h h'
      exact hI.nc_count r q e M M' i j (oldI h (by simp [PrOK])) (oldI h' (by simp [PrOK]))
    nc_flight := by
      intro r q e M h
      simpa using hI.nc_flight r q e M (oldN h (by simp [PrOK]))
    ns_unique := by
      intro p q e M a p' M' a' h h'
      exact hI.ns_unique p q e M a p' M' a' (old h (by simp [PrOK])) (old h' (by simp [PrOK]))
    ns_count := by
      intro p q e M a M' a' i j h h'
      exact hI.ns_count p q e M a M' a' i j (oldI h (by simp [PrOK])) (oldI h' (by simp [PrOK]))
    ns_flight := by
      intro p q e M a h
      simpa using hI.ns_flight p q e M a (oldN h (by simp [PrOK]))
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
