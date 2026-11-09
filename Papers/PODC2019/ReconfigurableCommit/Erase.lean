/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Frame

/-!
# Removing a message from a channel preserves the invariant
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The state with the `i`-th message of channel `src → dst` removed. -/
def State.erase (st : State T Pl S P) (src dst : P) (i : ℕ) : State T Pl S P :=
  let net' := Function.update st.net src
    (Function.update (st.net src) dst ((st.net src dst).eraseIdx i))
  { st with net := net' }

theorem mem_erase_net {st : State T Pl S P} {src dst : P} {i : ℕ} {m : Msg T Pl S P} {a b : P}
    (h : m ∈ (st.erase src dst i).net a b) : m ∈ st.net a b := by
  unfold State.erase at h
  by_cases h1 : a = src
  · subst h1
    by_cases h2 : b = dst
    · subst h2; simp at h; exact (List.eraseIdx_sublist _ _).subset h
    · simpa [h2] using h
  · simpa [h1] using h

theorem Inv.erase {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st) (src dst : P)
    (i : ℕ) : Inv Pa (st.erase src dst i) where
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
  elog_txn := hI.elog_txn
  vinfo_none := hI.vinfo_none
  vinfo_ok := hI.vinfo_ok
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
  loc_dec := hI.loc_dec
  loc_acceptAcks := hI.loc_acceptAcks
  loc_probeAcks := hI.loc_probeAcks
  prb := hI.prb
  probe_old := hI.probe_old
  probe_sent := hI.probe_sent
  m_probeAck := hI.m_probeAck
  m_frozen := hI.m_frozen
  m_prepare := hI.m_prepare
  m_prepareAck := hI.m_prepareAck
  m_accept := hI.m_accept
  m_acceptAck := hI.m_acceptAck
  m_decision := hI.m_decision
  m_newConfig := hI.m_newConfig
  m_newState := hI.m_newState
  net_sub := by
    intro a b
    unfold State.erase
    by_cases h1 : a = src
    · subst h1
      by_cases h2 : b = dst
      · subst h2; simpa using (List.eraseIdx_sublist _ _).trans (hI.net_sub _ _)
      · simpa [h2] using hI.net_sub a b
    · simpa [h1] using hI.net_sub a b
  nc_unique := hI.nc_unique
  nc_count := hI.nc_count
  nc_flight := by
    intro r q e M h
    exact hI.nc_flight r q e M (mem_erase_net h)
  ns_unique := hI.ns_unique
  ns_count := hI.ns_count
  ns_flight := by
    intro p q e M a h
    exact hI.ns_flight p q e M a (mem_erase_net h)
  hist_certify := hI.hist_certify
  hist_certify_unique := hI.hist_certify_unique
  hist_decide := hI.hist_decide
  hist_decide_unique := hI.hist_decide_unique
  hist_decide_idx := hI.hist_decide_idx
  hist_certify_idx := hI.hist_certify_idx
  hist_decide_after := hI.hist_decide_after
  hist_order := hI.hist_order
  vinfo_len := hI.vinfo_len

section ListAux

variable {α : Type}

theorem countP_le_one_of_unique {l : List α} {Q : α → Prop} [DecidablePred Q]
    (h : ∀ (i j : ℕ) x y, l[i]? = some x → l[j]? = some y → Q x → Q y → i = j) :
    l.countP Q ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have ih' := ih fun i j x y hx hy hqx hqy =>
      Nat.succ.inj (h (i + 1) (j + 1) x y (by simpa using hx) (by simpa using hy) hqx hqy)
    by_cases ha : Q a
    · have : l.countP Q = 0 := by
        rw [List.countP_eq_zero]
        intro y hy hqy
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
        have := h 0 (j + 1) a l[j] rfl (by simp) ha (by simpa using hqy)
        omega
      simp [ha, this]
    · simp [ha]; exact ih'

theorem not_mem_eraseIdx_of_countP {l : List α} {Q : α → Prop} [DecidablePred Q]
    (h1 : l.countP Q ≤ 1) {i : ℕ} {x : α} (hx : l[i]? = some x) (hq : Q x) :
    ∀ y ∈ l.eraseIdx i, ¬ Q y := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 hx).1
  have hl : l = l.take i ++ x :: l.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i l]
    congr 1
    rw [List.drop_eq_getElem_cons hi]
    congr
    exact (List.getElem?_eq_some_iff.1 hx).2
  rw [List.eraseIdx_eq_take_drop_succ]
  rw [hl, List.countP_append, List.countP_cons] at h1
  simp only [hq, decide_true, if_true] at h1
  intro y hy hqy
  rcases List.mem_append.1 hy with hy | hy
  · have := (List.countP_pos_iff (p := fun z => decide (Q z))).2 ⟨y, hy, decide_eq_true hqy⟩
    omega
  · have := (List.countP_pos_iff (p := fun z => decide (Q z))).2 ⟨y, hy, decide_eq_true hqy⟩
    omega

end ListAux

open Classical in
/-- After delivering a `NEW_CONFIG(e)`, no `NEW_CONFIG(e)` for that shard is left in transit. -/
theorem Inv.nc_gone {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st) {src dst : P}
    {i : ℕ} {e : ℕ} {M : Finset P} (hm : (st.net src dst)[i]? = some (Msg.newConfig e M))
    (r q : P) (M' : Finset P) (hq : Pa.home q = Pa.home dst) :
    Msg.newConfig e M' ∉ (st.erase src dst i).net r q := by
  intro h
  have hmS : Msg.newConfig e M ∈ st.sent src dst :=
    (hI.net_sub src dst).subset (List.mem_of_getElem? hm)
  by_cases hc : r = src ∧ q = dst
  · obtain ⟨rfl, rfl⟩ := hc
    have hcnt : (st.sent r q).countP (fun m => ∃ M', m = Msg.newConfig e M') ≤ 1 :=
      countP_le_one_of_unique fun i j x y hx hy ⟨M₁, h1⟩ ⟨M₂, h2⟩ => by
        subst h1 h2; exact hI.nc_count r q e M₁ M₂ i j hx hy
    have hcnt' := ((hI.net_sub r q).countP_le (p := fun m => decide (∃ M', m = Msg.newConfig e M'))).trans
      (by simpa using hcnt)
    unfold State.erase at h
    simp at h
    exact not_mem_eraseIdx_of_countP (Q := fun m => ∃ M', m = Msg.newConfig e M')
      (by simpa using hcnt') hm ⟨M, rfl⟩ _ h ⟨M', rfl⟩
  · have h' := (hI.net_sub r q).subset (mem_erase_net h)
    obtain ⟨h1, h2, -⟩ := hI.nc_unique r q e M' src dst M h' hmS hq
    exact hc ⟨h1, h2⟩

open Classical in
/-- After delivering a `NEW_STATE(e)` to `dst`, no `NEW_STATE(e)` to `dst` is left in transit. -/
theorem Inv.ns_gone {Pa : Params T Pl S P} {st : State T Pl S P} (hI : Inv Pa st) {src dst : P}
    {i : ℕ} {e : ℕ} {M : Finset P} {a : Arrays T Pl}
    (hm : (st.net src dst)[i]? = some (Msg.newState e M a)) (p : P) (M' : Finset P)
    (a' : Arrays T Pl) : Msg.newState e M' a' ∉ (st.erase src dst i).net p dst := by
  intro h
  have hmS : Msg.newState e M a ∈ st.sent src dst :=
    (hI.net_sub src dst).subset (List.mem_of_getElem? hm)
  by_cases hc : p = src
  · subst hc
    have hcnt : (st.sent p dst).countP (fun m => ∃ M' a', m = Msg.newState e M' a') ≤ 1 :=
      countP_le_one_of_unique fun i j x y hx hy ⟨M₁, a₁, h1⟩ ⟨M₂, a₂, h2⟩ => by
        subst h1 h2; exact hI.ns_count p dst e M₁ a₁ M₂ a₂ i j hx hy
    have hcnt' := ((hI.net_sub p dst).countP_le
      (p := fun m => decide (∃ M' a', m = Msg.newState e M' a'))).trans (by simpa using hcnt)
    unfold State.erase at h
    simp at h
    exact not_mem_eraseIdx_of_countP (Q := fun m => ∃ M' a', m = Msg.newState e M' a')
      (by simpa using hcnt') hm ⟨M, a, rfl⟩ _ h ⟨M', a', rfl⟩
  · have h' := (hI.net_sub p dst).subset (mem_erase_net h)
    exact hc (hI.ns_unique p dst e M' a' src M a h' hmS).1

end Podc.ReconfigurableCommit
