/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Send

/-!
# Sending `NEW_STATE` preserves the invariant

`Inv.send_newState`: line 60 preserves `Inv`.
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The conditions for `src` to send `NEW_STATE(e, M, a)` to `b` (line 60). -/
def NSOK (Pa : Params T Pl S P) (st : State T Pl S P) (src b : P) : Msg T Pl S P → Prop
  | .newState e M a =>
    cfg st (Pa.home b) e = some ⟨M, src⟩ ∧ b ∈ M ∧ b ≠ src ∧ st.started (Pa.home b) e = true ∧
    (∀ k, a.ent k = (st.base (Pa.home b) e k).map Prod.fst) ∧
    (∀ k, a.phase k ≠ .start → k ≤ a.len) ∧
    (∀ k, (a.ent k).isSome = true ↔ a.phase k ≠ .start) ∧
    (∀ k, a.phase k = .decided → ∃ dd, a.dec k = some dd ∧
      ∃ e' v, e' ≤ e ∧ AccL st (Pa.home b) e' k v ∧ Event.decide v.1.1 dd ∈ st.hist) ∧
    (∀ p' M' a', Msg.newState e M' a' ∉ st.sent p' b) ∧
    ((st.loc b).epoch (Pa.home b) < e ∨ e < (st.loc b).newEpoch)
  | _ => False

set_option hygiene false in
/-- Rewrite the derived notions of a sent-to state back to the original state. -/
local macro "sframe " h:term : tactic => `(tactic| simpa only [hA, hR, hD, hK, hL, hDe, cfg_send,
  State.send_loc, State.send_cs, State.send_hist, State.send_started, State.send_elog,
  State.send_base, State.send_vinfo, fresh_send, cand_send, plAt_send, decIn_send] using $h)

theorem Inv.send_newState {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st) (src : P)
    (out : P → Option (Msg T Pl S P)) (hout : ∀ b m, out b = some m → NSOK Pa st src b m) :
    Inv Pa (st.send src out) := by
  have hNA : NoAcceptAck out := fun b s e k t d h => by simpa [NSOK] using hout _ _ h
  have hNP : NoProbeAck out := fun b b' E s h => by simpa [NSOK] using hout _ _ h
  have hA := acked_send st src out hNA
  have hR := replied_send st src out hNP
  have hD := dead_send st src out hNA
  have hK := aliveK_send st src out hNA
  have hL := accL_send st src out hNA
  have hDe := decided_send st src out Pa hNA
  have hM := fun {m : Msg T Pl S P} {a b : P} => State.mem_send_sent st src out (m := m) (a := a) (b := b)
  have hN := fun {m : Msg T Pl S P} {a b : P} => State.mem_send_net st src out (m := m) (a := a) (b := b)
  have old : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ (st.send src out).sent a b →
      (∀ b, ¬ NSOK Pa st src b m) → m ∈ st.sent a b := by
    intro m a b h hn
    rcases hM.1 h with h | ⟨-, h⟩
    · exact h
    · exact absurd (hout _ _ h) (hn _)
  have oldN : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ (st.send src out).net a b →
      (∀ b, ¬ NSOK Pa st src b m) → m ∈ st.net a b := by
    intro m a b h hn
    rcases hN.1 h with h | ⟨-, h⟩
    · exact h
    · exact absurd (hout _ _ h) (hn _)
  have new : ∀ {m : Msg T Pl S P} {a b : P}, m ∈ st.sent a b → m ∈ (st.send src out).sent a b :=
    fun h => hM.2 (Or.inl h)
  have oldI : ∀ {m : Msg T Pl S P} {a b : P} {i : ℕ}, ((st.send src out).sent a b)[i]? = some m →
      (∀ b, ¬ NSOK Pa st src b m) → (st.sent a b)[i]? = some m := by
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
      exact ⟨h1, h2, h3, h4, by simpa only [hD, State.send_loc] using h5,
        fun q hq hq' => h6 q (old hq (by simp [NSOK])) hq'⟩
    probe_old := by
      intro r q E h
      simpa using hI.probe_old r q E (old h (by simp [NSOK]))
    probe_sent := by
      intro r q E h
      simpa using hI.probe_sent r q E (old h (by simp [NSOK]))
    m_probeAck := by
      intro q r b E s h
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI.m_probeAck q r b E s (old h (by simp [NSOK]))
      exact ⟨h1, h2, new h3, h4, by simpa only [hA, cfg_send] using h5⟩
    m_frozen := by sframe hI.m_frozen
    m_prepare := by
      intro a1 a2 a3 a4 h
      exact hI.m_prepare a1 a2 a3 a4 (old h (by simp [NSOK]))
    m_prepareAck := by
      intro a1 a2 a3 a4 a5 a6 a7 a8 h
      exact hI.m_prepareAck a1 a2 a3 a4 a5 a6 a7 a8 (old h (by simp [NSOK]))
    m_accept := by
      intro a1 a2 a3 a4 a5 a6 a7 h
      exact hI.m_accept a1 a2 a3 a4 a5 a6 a7 (old h (by simp [NSOK]))
    m_acceptAck := by
      intro q r s e k t d h
      simpa using hI.m_acceptAck q r s e k t d (old h (by simp [NSOK]))
    m_decision := by
      intro a1 a2 a3 a4 a5 h
      rw [hL]
      exact hI.m_decision a1 a2 a3 a4 a5 (old h (by simp [NSOK]))
    m_newConfig := by
      intro r q e M h
      simpa only [hR, cfg_send] using hI.m_newConfig r q e M (old h (by simp [NSOK]))
    m_newState := by
      intro p q e M a h
      rw [hL]
      rcases hM.1 h with h | ⟨heq, h'⟩
      · simpa using hI.m_newState p q e M a h
      · subst heq
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ := hout _ _ h'
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    net_sub := by
      intro a b
      rw [State.send_net, State.send_sent]
      split_ifs
      · exact (hI.net_sub a b).append_right _
      · exact hI.net_sub a b
    nc_unique := by
      intro r q e M r' q' M' h h'
      exact hI.nc_unique r q e M r' q' M' (old h (by simp [NSOK])) (old h' (by simp [NSOK]))
    nc_count := by
      intro r q e M M' i j h h'
      exact hI.nc_count r q e M M' i j (oldI h (by simp [NSOK])) (oldI h' (by simp [NSOK]))
    nc_flight := by
      intro r q e M h
      simpa using hI.nc_flight r q e M (oldN h (by simp [NSOK]))
    ns_unique := by
      intro p q e M a p' M' a' h h'
      rcases hM.1 h with h | ⟨hr, h2⟩ <;> rcases hM.1 h' with h' | ⟨hr', h2'⟩
      · exact hI.ns_unique p q e M a p' M' a' h h'
      · exact absurd h ((hout _ _ h2').2.2.2.2.2.2.2.2.1 p M a)
      · exact absurd h' ((hout _ _ h2).2.2.2.2.2.2.2.2.1 p' M' a')
      · subst hr hr'
        rw [h2] at h2'
        cases h2'
        exact ⟨rfl, rfl, rfl⟩
    ns_count := by
      intro p q e M a M' a' i j h h'
      rw [State.send_sent] at h h'
      split_ifs at h h' with hr
      · rcases getElem?_append_toList h with h | ⟨hi, ho⟩ <;>
          rcases getElem?_append_toList h' with h' | ⟨hj, ho'⟩
        · exact hI.ns_count p q e M a M' a' i j h h'
        · exact absurd (List.mem_of_getElem? h) ((hout _ _ ho').2.2.2.2.2.2.2.2.1 p M a)
        · exact absurd (List.mem_of_getElem? h') ((hout _ _ ho).2.2.2.2.2.2.2.2.1 p M' a')
        · omega
      · exact hI.ns_count p q e M a M' a' i j h h'
    ns_flight := by
      intro p q e M a h
      rcases hN.1 h with h | ⟨heq, h'⟩
      · simpa using hI.ns_flight p q e M a h
      · subst heq
        simpa using (hout _ _ h').2.2.2.2.2.2.2.2.2
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
