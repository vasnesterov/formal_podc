/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Frame

/-!
# Recording an action in the history preserves the invariant
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

theorem getElem?_append_singleton {α : Type} {l : List α} {x y : α} {i : ℕ}
    (h : (l ++ [x])[i]? = some y) : l[i]? = some y ∨ (i = l.length ∧ x = y) := by
  rcases lt_or_ge i l.length with hi | hi
  · left; rwa [List.getElem?_append_left hi] at h
  · right
    rw [List.getElem?_append_right hi] at h
    rcases Nat.eq_or_lt_of_le hi with h' | h'
    · subst h'; simpa using h
    · have : i - l.length ≠ 0 := by omega
      simp [List.getElem?_singleton, this] at h

/-- Appending a `certify` or `decide` action to the history preserves the invariant, provided the
action is new and (for `decide`) justified by accepted entries. -/
theorem Inv.addEvent {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st)
    (ev : Event T Pl)
    (hc : ∀ t l, ev = .certify t l → Pa.σ.ValidPayload t l ∧ ∀ l', Event.certify t l' ∉ st.hist)
    (hd : ∀ t d, ev = .decide t d → Decided Pa st t d ∧ (∀ d', Event.decide t d' ∉ st.hist) ∧
      (∃ l, Event.certify t l ∈ st.hist) ∧
      ∀ s ∈ Pa.σ.shards t, ∃ e k v, AccL st s e k v ∧ v.1.1 = t ∧
        ∀ J₁ J₂ hl, st.vinfo s v.2 k = some (J₁, J₂, hl) → hl ≤ st.hist.length) :
    Inv Pa { st with hist := st.hist ++ [ev] } where
  cs_zero := hI.cs_zero
  cfg_wf := hI.cfg_wf
  cfg_mem := hI.cfg_mem
  frz := hI.frz
  leader_init := hI.leader_init
  init_init := hI.init_init
  started_cfg := hI.started_cfg
  started_leader := hI.started_leader
  elog_started := hI.elog_started
  base_elog := hI.base_elog
  elog_above := hI.elog_above
  elog_origin := hI.elog_origin
  elog_dist := hI.elog_dist
  elog_txn := by
    intro s e k t l d o h
    obtain ⟨h1, l₀, h2, h3⟩ := hI.elog_txn s e k t l d o h
    exact ⟨h1, l₀, List.mem_append_left _ h2, h3⟩
  vinfo_none := hI.vinfo_none
  vinfo_ok := by
    intro s o k t l d J₁ J₂ hl h hv
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.vinfo_ok s o k t l d J₁ J₂ hl h hv
    have htake : (st.hist ++ [ev]).take hl = st.hist.take hl := List.take_append_of_le_length h1
    refine ⟨by simp; omega, h2, h3, ?_, h5, ?_⟩
    · intro j hj v hv'
      have := h4 j hj v hv'
      unfold DecIn at this ⊢
      simpa only [htake] using this
    · intro j hj v hv'
      have := h6 j hj v hv'
      unfold DecIn at this ⊢
      simpa only [htake] using this
  inv2 := hI.inv2
  loc_len := hI.loc_len
  loc_ent := hI.loc_ent
  loc_newEpoch := hI.loc_newEpoch
  loc_view := hI.loc_view
  loc_started := hI.loc_started
  loc_member := hI.loc_member
  loc_member0 := hI.loc_member0
  loc_leaderArr := hI.loc_leaderArr
  loc_leader := hI.loc_leader
  loc_follower := hI.loc_follower
  loc_elog := hI.loc_elog
  loc_base := hI.loc_base
  loc_acked := hI.loc_acked
  loc_acked_epoch := hI.loc_acked_epoch
  loc_dec := by
    intro p k h
    obtain ⟨dd, h1, e, v, h2, h3, h4⟩ := hI.loc_dec p k h
    exact ⟨dd, h1, e, v, h2, h3, List.mem_append_left _ h4⟩
  loc_acceptAcks := hI.loc_acceptAcks
  loc_probeAcks := hI.loc_probeAcks
  prb := hI.prb
  probe_old := hI.probe_old
  probe_sent := hI.probe_sent
  m_probeAck := hI.m_probeAck
  m_frozen := hI.m_frozen
  m_prepare := by
    intro c b t lo h
    obtain ⟨h1, l₀, h2, h3⟩ := hI.m_prepare c b t lo h
    exact ⟨h1, l₀, List.mem_append_left _ h2, h3⟩
  m_prepareAck := hI.m_prepareAck
  m_accept := hI.m_accept
  m_acceptAck := hI.m_acceptAck
  m_decision := by
    intro c q e k d h
    obtain ⟨v, h1, h2⟩ := hI.m_decision c q e k d h
    exact ⟨v, h1, List.mem_append_left _ h2⟩
  m_newConfig := hI.m_newConfig
  m_newState := by
    intro p q e M a h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.m_newState p q e M a h
    refine ⟨h1, h2, h3, h4, h5, h6, h7, fun k hk => ?_⟩
    obtain ⟨dd, h9, e', v, h10, h11, h12⟩ := h8 k hk
    exact ⟨dd, h9, e', v, h10, h11, List.mem_append_left _ h12⟩
  net_sub := hI.net_sub
  nc_unique := hI.nc_unique
  nc_count := hI.nc_count
  nc_flight := hI.nc_flight
  ns_unique := hI.ns_unique
  ns_count := hI.ns_count
  ns_flight := hI.ns_flight
  hist_certify := by
    intro t l h
    rcases List.mem_append.1 h with h | h
    · exact hI.hist_certify t l h
    · exact (hc t l (List.mem_singleton.1 h).symm).1
  hist_certify_unique := by
    intro t l l' h h'
    rcases List.mem_append.1 h with h | h <;> rcases List.mem_append.1 h' with h' | h'
    · exact hI.hist_certify_unique t l l' h h'
    · exact absurd h ((hc t l' (List.mem_singleton.1 h').symm).2 l)
    · exact absurd h' ((hc t l (List.mem_singleton.1 h).symm).2 l')
    · have := (List.mem_singleton.1 h).trans (List.mem_singleton.1 h').symm
      cases this
      rfl
  hist_decide := by
    intro t d h
    rcases List.mem_append.1 h with h | h
    · exact hI.hist_decide t d h
    · exact (hd t d (List.mem_singleton.1 h).symm).1
  hist_decide_unique := by
    intro t d d' h h'
    rcases List.mem_append.1 h with h | h <;> rcases List.mem_append.1 h' with h' | h'
    · exact hI.hist_decide_unique t d d' h h'
    · exact absurd h ((hd t d' (List.mem_singleton.1 h').symm).2.1 d)
    · exact absurd h' ((hd t d (List.mem_singleton.1 h).symm).2.1 d')
    · have := (List.mem_singleton.1 h).trans (List.mem_singleton.1 h').symm
      cases this
      rfl
  hist_decide_idx := by
    intro i j t d d' h h'
    simp only at h h'
    rcases getElem?_append_singleton h with h | ⟨hi, rfl⟩ <;>
      rcases getElem?_append_singleton h' with h' | ⟨hj, h'e⟩
    · exact hI.hist_decide_idx i j t d d' h h'
    · exact absurd (List.mem_of_getElem? h) ((hd t d' h'e).2.1 d)
    · exact absurd (List.mem_of_getElem? h') ((hd t d rfl).2.1 d')
    · omega
  hist_certify_idx := by
    intro i j t l l' h h'
    simp only at h h'
    rcases getElem?_append_singleton h with h | ⟨hi, rfl⟩ <;>
      rcases getElem?_append_singleton h' with h' | ⟨hj, h'e⟩
    · exact hI.hist_certify_idx i j t l l' h h'
    · exact absurd (List.mem_of_getElem? h) ((hc t l' h'e).2 l)
    · exact absurd (List.mem_of_getElem? h') ((hc t l rfl).2 l')
    · omega
  hist_decide_after := by
    intro i t d h
    simp only at h
    rcases getElem?_append_singleton h with h | ⟨hi, rfl⟩
    · obtain ⟨j, hj, l, h'⟩ := hI.hist_decide_after i t d h
      exact ⟨j, hj, l, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h').1]; exact h'⟩
    · obtain ⟨l, hl⟩ := (hd t d rfl).2.2.1
      obtain ⟨j, hj, h'⟩ := List.getElem_of_mem hl
      exact ⟨j, by omega, l, by rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, h']⟩
  hist_order := by
    intro i t d h
    simp only at h
    rcases getElem?_append_singleton h with h | ⟨hi, rfl⟩
    · exact hI.hist_order i t d h
    · intro s hs
      obtain ⟨e, k, v, h1, h2, h3⟩ := (hd t d rfl).2.2.2 s hs
      exact ⟨e, k, v, h1, h2, fun J₁ J₂ hl hv => (h3 J₁ J₂ hl hv).trans hi.ge⟩
  vinfo_len := by
    intro s o k J₁ J₂ hl h
    have := hI.vinfo_len s o k J₁ J₂ hl h
    simp; omega

end Podc.ReconfigurableCommit
