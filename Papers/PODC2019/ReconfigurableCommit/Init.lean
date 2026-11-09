/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Inv

/-!
# The invariant holds initially
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem cfg_initState (Pa : Params T Pl S P) (s : S) (e : ℕ) :
    cfg (initState Pa) s e = if e = 0 then some (Pa.init s) else none := by
  unfold cfg initState
  rcases e with _ | e <;> simp

/-- The invariant holds in the initial state. -/
theorem inv_init (Pa : Params T Pl S P) (hinit : ValidInit Pa) : Inv Pa (initState Pa) where
  cs_zero := fun s => by simp [cfg_initState]
  cfg_wf := by
    intro s e c h
    rw [cfg_initState] at h
    split_ifs at h with he
    cases h
    exact hinit s
  cfg_mem := by
    intro s E c hE h
    rw [cfg_initState] at h
    split_ifs at h with he
    omega
  frz := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  leader_init := by
    intro s e c h
    rw [cfg_initState] at h
    split_ifs at h with he
    cases h
    have := (hinit s).1
    simp [initState, (hinit s).2.1 _ this, this]
  init_init := by
    intro s q hq
    simp [initState, (hinit s).2.1 _ hq, hq]
  started_cfg := by
    intro s e h
    simp [initState] at h
    simp [initState, h]
  started_leader := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  elog_started := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  base_elog := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  elog_above := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  elog_origin := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  elog_dist := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  elog_txn := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  vinfo_none := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  vinfo_ok := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  inv2 := by
    intro s E c h
    rw [cfg_initState] at h
    split_ifs at h with he
    intro _ e' he'
    omega
  loc_len := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_ent := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_newEpoch := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_view := by
    intro p s
    rw [show ((initState Pa).loc p).epoch s = 0 from rfl, cfg_initState]
    rfl
  loc_started := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_member := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_member0 := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_leaderArr := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_leader := by
    intro p h
    simp only [initState] at h ⊢
    refine ⟨?_, ?_, fun _ _ => rfl, fun j v hv => by simp at hv⟩
    · split_ifs at h with h1 h2 <;> simp_all
    · by_cases h1 : (Pa.init (Pa.home p)).leader = p
      · have := (hinit (Pa.home p)).1
        rw [h1] at this
        simpa using this
      · rw [if_neg h1] at h
        split_ifs at h
  loc_follower := by
    intro p h
    simp only [initState] at h ⊢
    by_cases h1 : (Pa.init (Pa.home p)).leader = p
    · rw [if_pos h1] at h; cases h
    · rw [if_neg h1] at h
      by_cases h2 : p ∈ (Pa.init (Pa.home p)).members
      · exact ⟨h1, by simpa using h2, h2⟩
      · rw [if_neg h2] at h; cases h
  loc_elog := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_base := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_acked := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_acked_epoch := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_dec := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_acceptAcks := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  loc_probeAcks := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  prb := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  probe_old := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  probe_sent := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_probeAck := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_frozen := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_prepare := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_prepareAck := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_accept := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_acceptAck := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_decision := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_newConfig := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  m_newState := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  net_sub := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  nc_unique := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  nc_count := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  nc_flight := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  ns_unique := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  ns_count := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  ns_flight := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  hist_certify := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  hist_certify_unique := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  hist_decide := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  hist_decide_unique := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  hist_decide_idx := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  hist_certify_idx := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  hist_decide_after := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  hist_order := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]
  vinfo_len := by intros; simp_all [initState, Arrays.empty, cfg_initState, Acked, Replied, AccL, cand]

end Podc.ReconfigurableCommit
