/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Safe

/-!
# Storing a new configuration at the CS preserves the invariant (line 49)
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The state after `compare_and_swap` stored configuration `c` for shard `s`. -/
def State.addCfg (st : State T Pl S P) (s : S) (c : Config P) : State T Pl S P :=
  { st with cs := Function.update st.cs s (st.cs s ++ [c]) }

section
variable {st : State T Pl S P} {s : S} {c : Config P}

@[simp] theorem addCfg_loc : (st.addCfg s c).loc = st.loc := rfl
@[simp] theorem addCfg_sent : (st.addCfg s c).sent = st.sent := rfl
@[simp] theorem addCfg_net : (st.addCfg s c).net = st.net := rfl
@[simp] theorem addCfg_hist : (st.addCfg s c).hist = st.hist := rfl
@[simp] theorem addCfg_started : (st.addCfg s c).started = st.started := rfl
@[simp] theorem addCfg_elog : (st.addCfg s c).elog = st.elog := rfl
@[simp] theorem addCfg_base : (st.addCfg s c).base = st.base := rfl
@[simp] theorem addCfg_vinfo : (st.addCfg s c).vinfo = st.vinfo := rfl
@[simp] theorem acked_addCfg : Acked (st.addCfg s c) = Acked st := rfl
@[simp] theorem replied_addCfg : Replied (st.addCfg s c) = Replied st := rfl
@[simp] theorem cand_addCfg : cand (st.addCfg s c) = cand st := rfl
@[simp] theorem plAt_addCfg (Pa : Params T Pl S P) : plAt Pa (st.addCfg s c) = plAt Pa st := rfl
@[simp] theorem decIn_addCfg : DecIn (st.addCfg s c) = DecIn st := rfl
theorem addCfg_cs_self : (st.addCfg s c).cs s = st.cs s ++ [c] := by simp [State.addCfg]
theorem addCfg_cs_ne {s' : S} (h : s' ≠ s) : (st.addCfg s c).cs s' = st.cs s' := by
  simp [State.addCfg, h]
theorem addCfg_len_le (s' : S) : (st.cs s').length ≤ ((st.addCfg s c).cs s').length := by
  by_cases h : s' = s
  · subst h; simp [addCfg_cs_self]
  · rw [addCfg_cs_ne h]

theorem cfg_addCfg (s' : S) (e : ℕ) : cfg (st.addCfg s c) s' e =
    if s' = s ∧ e = (st.cs s).length then some c else cfg st s' e := by
  unfold cfg
  by_cases h : s' = s
  · subst h
    rw [addCfg_cs_self]
    rcases lt_trichotomy e (st.cs s').length with h' | h' | h'
    · rw [List.getElem?_append_left h', if_neg (by omega)]
    · subst h'; simp
    · rw [List.getElem?_append_right (by omega), if_neg (by omega)]
      simp [List.getElem?_eq_none (show (st.cs s').length ≤ e by omega)]
      omega
  · rw [addCfg_cs_ne h, if_neg (by tauto)]

theorem cfg_addCfg_of {s' : S} {e : ℕ} {x : Config P} (h : cfg st s' e = some x) :
    cfg (st.addCfg s c) s' e = some x := by
  rw [cfg_addCfg, if_neg]
  · exact h
  · rintro ⟨rfl, rfl⟩
    unfold cfg at h
    simp at h

theorem cfg_lt {s' : S} {e : ℕ} {x : Config P} (h : cfg st s' e = some x) :
    e < (st.cs s').length := by
  unfold cfg at h
  exact (List.getElem?_eq_some_iff.1 h).1

theorem cfg_addCfg_cases {s' : S} {e : ℕ} {x : Config P} (h : cfg (st.addCfg s c) s' e = some x) :
    cfg st s' e = some x ∨ (s' = s ∧ e = (st.cs s).length ∧ x = c) := by
  rw [cfg_addCfg] at h
  split_ifs at h with h'
  · cases h; exact Or.inr ⟨h'.1, h'.2, rfl⟩
  · exact Or.inl h

theorem cfg_addCfg_eq {s' : S} {e : ℕ} (h : e < (st.cs s').length) :
    cfg (st.addCfg s c) s' e = cfg st s' e := by
  rw [cfg_addCfg, if_neg]
  rintro ⟨rfl, rfl⟩
  omega

theorem dead_addCfg {s' : S} {e : ℕ} (h : Dead st s' e) : Dead (st.addCfg s c) s' e := by
  obtain ⟨c', hc', q, hq, h1, h2⟩ := h
  exact ⟨c', cfg_addCfg_of hc', q, hq, h1, h2⟩

theorem fresh_addCfg {q : P} {s' : S} {E : ℕ} (hE : E ≤ (st.cs s').length)
    (h : Fresh st q s' E) : Fresh (st.addCfg s c) q s' E := by
  intro e he c' hc'
  rw [cfg_addCfg_eq (by omega)] at hc'
  exact h e he c' hc'

theorem aliveK_addCfg {s' : S} {e k : ℕ} (he : e < (st.cs s').length)
    (h : AliveK (st.addCfg s c) s' e k) : AliveK st s' e k := by
  intro c' hc'
  exact h c' (by rw [cfg_addCfg_eq he]; exact hc')

end

variable {Pa : Params T Pl S P} {st : State T Pl S P}

theorem Inv.cfg_lt' (hI : Inv Pa st) {s : S} {e : ℕ} (h : st.started s e = true) :
    e < (st.cs s).length := hI.started_cfg s e h

theorem Inv.accL_addCfg (hI : Inv Pa st) (s : S) (c : Config P) :
    AccL (st.addCfg s c) = AccL st := by
  funext s' e k v
  apply propext
  unfold AccL
  constructor
  · rintro ⟨h1, c', hc', h2⟩
    have := cfg_addCfg_eq (s := s) (c := c) (hI.started_cfg _ _ (hI.elog_started _ _ _ _ h1))
    rw [this] at hc'
    exact ⟨h1, c', hc', h2⟩
  · rintro ⟨h1, c', hc', h2⟩
    exact ⟨h1, c', cfg_addCfg_of hc', h2⟩

theorem Inv.decided_addCfg (hI : Inv Pa st) (s : S) (c : Config P) :
    Decided Pa (st.addCfg s c) = Decided Pa st := by
  unfold Decided; rw [hI.accL_addCfg]

set_option hygiene false in
local macro "aframe " h:term : tactic => `(tactic| simpa only [addCfg_loc, addCfg_sent,
  addCfg_net, addCfg_hist, addCfg_started, addCfg_elog, addCfg_base, addCfg_vinfo, hacc, hdec,
  acked_addCfg, replied_addCfg, cand_addCfg, plAt_addCfg, decIn_addCfg]
  using $h)

/-- Storing a new configuration `⟨M, q⟩` at epoch `E = |cs s|` preserves `Inv`, given its
probing record (`hmem`), the frozen epoch `E - 1` (`hfrz`) and the safety of the new leader's
state (`hsafe`, see `Inv.safe`). -/
theorem Inv.addCfg (hI : Inv Pa st) (s : S) (M : Finset P) (q : P)
    (hwf : q ∈ M ∧ (∀ r ∈ M, Pa.home r = s) ∧ 2 ≤ M.card)
    (hmem : ∃ pe < (st.cs s).length,
      (∀ e', pe < e' → e' < (st.cs s).length → Dead st s e') ∧
      Replied st q true (st.cs s).length s ∧
      (∃ y, pe ≤ y ∧ y < (st.cs s).length ∧ ∃ cy, cfg st s y = some cy ∧ q ∈ cy.members) ∧
      ∀ r ∈ M, Fresh st r s (st.cs s).length ∨
        ((∃ b, Replied st r b (st.cs s).length s) ∧ ∃ z, pe ≤ z ∧ z < (st.cs s).length ∧
          ∃ cz, cfg st s z = some cz ∧ r ∈ cz.members))
    (hfrz : ∃ c', cfg st s ((st.cs s).length - 1) = some c' ∧
      ∃ r ∈ c'.members, (st.cs s).length - 1 < (st.loc r).newEpoch)
    (hinit : (st.loc q).initialized = true)
    (hsafe : (st.loc q).newEpoch = (st.cs s).length → ∀ e' < (st.cs s).length, ∀ k v,
      st.elog s e' k = some v → AliveK st s e' k →
        candOf st s q k = some v ∧ ∀ j < k, ∀ w, candOf st s q j = some w → st.elog s e' j = some w) :
    Inv Pa (st.addCfg s ⟨M, q⟩) := by
  have hacc := hI.accL_addCfg s ⟨M, q⟩
  have hdec := hI.decided_addCfg s ⟨M, q⟩
  exact {
    cs_zero := by
      intro s'
      rw [cfg_addCfg, if_neg (by omega)]
      exact hI.cs_zero s'
    cfg_wf := by
      intro s' e c' h
      rcases cfg_addCfg_cases h with h | ⟨rfl, rfl, rfl⟩
      · exact hI.cfg_wf s' e c' h
      · exact hwf
    cfg_mem := by
      intro s' E' c' hE' h
      rcases cfg_addCfg_cases h with h | ⟨rfl, rfl, rfl⟩
      · have hlt := cfg_lt h
        obtain ⟨pe, hpe, h1, h2, h3, h4⟩ := hI.cfg_mem s' E' c' hE' h
        refine ⟨pe, hpe, fun e' a b => dead_addCfg (h1 e' a b), h2, ?_, fun q' hq' => ?_⟩
        · obtain ⟨y, hy1, hy2, cy, hcy, hqy⟩ := h3
          exact ⟨y, hy1, hy2, cy, cfg_addCfg_of hcy, hqy⟩
        · rcases h4 q' hq' with h | ⟨h5, z, hz1, hz2, cz, hcz, hqz⟩
          · exact Or.inl (fresh_addCfg hlt.le h)
          · exact Or.inr ⟨h5, z, hz1, hz2, cz, cfg_addCfg_of hcz, hqz⟩
      · obtain ⟨pe, hpe, h1, h2, h3, h4⟩ := hmem
        refine ⟨pe, hpe, fun e' a b => dead_addCfg (h1 e' a b), h2, ?_, fun q' hq' => ?_⟩
        · obtain ⟨y, hy1, hy2, cy, hcy, hqy⟩ := h3
          exact ⟨y, hy1, hy2, cy, cfg_addCfg_of hcy, hqy⟩
        · rcases h4 q' hq' with h | ⟨h5, z, hz1, hz2, cz, hcz, hqz⟩
          · exact Or.inl (fresh_addCfg le_rfl h)
          · exact Or.inr ⟨h5, z, hz1, hz2, cz, cfg_addCfg_of hcz, hqz⟩
    frz := by
      intro s' e h
      by_cases hs : s' = s
      · subst hs
        rw [addCfg_cs_self] at h
        simp only [List.length_append, List.length_singleton] at h
        rcases Nat.lt_or_ge (e + 1) (st.cs s').length with h' | h'
        · obtain ⟨c', hc', q', hq', h''⟩ := hI.frz s' e h'
          exact ⟨c', cfg_addCfg_of hc', q', hq', h''⟩
        · have : e = (st.cs s').length - 1 := by omega
          subst this
          obtain ⟨c', hc', q', hq', h''⟩ := hfrz
          exact ⟨c', cfg_addCfg_of hc', q', hq', h''⟩
      · rw [addCfg_cs_ne hs] at h
        obtain ⟨c', hc', q', hq', h''⟩ := hI.frz s' e h
        exact ⟨c', cfg_addCfg_of hc', q', hq', h''⟩
    leader_init := by
      intro s' e c' h
      rcases cfg_addCfg_cases h with h | ⟨rfl, rfl, rfl⟩
      · exact hI.leader_init s' e c' h
      · exact hinit
    init_init := by aframe hI.init_init
    started_cfg := by
      intro s' e h
      have := hI.started_cfg s' e h
      by_cases hs : s' = s
      · subst hs; rw [addCfg_cs_self]; simp; omega
      · rw [addCfg_cs_ne hs]; exact this
    started_leader := by
      intro s' e c' hs h
      rcases cfg_addCfg_cases h with h | ⟨rfl, rfl, rfl⟩
      · exact hI.started_leader s' e c' hs h
      · have := hI.started_cfg _ _ hs; omega
    elog_started := by aframe hI.elog_started
    base_elog := by aframe hI.base_elog
    elog_above := by aframe hI.elog_above
    elog_origin := by aframe hI.elog_origin
    elog_dist := by aframe hI.elog_dist
    elog_txn := by aframe hI.elog_txn
    vinfo_none := by aframe hI.vinfo_none
    vinfo_ok := by aframe hI.vinfo_ok
    inv2 := by
      intro s' E' c' h hpre e' he' k v hv hal
      have hal' : AliveK st s' e' k := aliveK_addCfg (hI.cfg_lt' (hI.elog_started _ _ _ _ hv)) hal
      rcases cfg_addCfg_cases h with h | ⟨rfl, rfl, rfl⟩
      · exact hI.inv2 s' E' c' h hpre e' he' k v hv hal'
      · have hns : st.started s' (st.cs s').length = false := by
          cases h' : st.started s' (st.cs s').length
          · rfl
          · have := hI.started_cfg _ _ h'; omega
        rcases hpre with hpre | hpre
        · rw [addCfg_started, hns] at hpre; cases hpre
        · have := hsafe hpre e' he' k v hv hal'
          simp only [cand, addCfg_started, hns]
          exact this
    loc_len := by aframe hI.loc_len
    loc_ent := by aframe hI.loc_ent
    loc_newEpoch := by aframe hI.loc_newEpoch
    loc_view := by
      intro p s'
      exact cfg_addCfg_of (hI.loc_view p s')
    loc_started := by aframe hI.loc_started
    loc_member := by aframe hI.loc_member
    loc_member0 := by aframe hI.loc_member0
    loc_leaderArr := by aframe hI.loc_leaderArr
    loc_leader := by aframe hI.loc_leader
    loc_follower := by aframe hI.loc_follower
    loc_elog := by aframe hI.loc_elog
    loc_base := by aframe hI.loc_base
    loc_acked := by aframe hI.loc_acked
    loc_acked_epoch := by aframe hI.loc_acked_epoch
    loc_dec := by
      rw [hacc]; exact hI.loc_dec
    loc_acceptAcks := by aframe hI.loc_acceptAcks
    loc_probeAcks := by aframe hI.loc_probeAcks
    prb := by
      intro p hp
      obtain ⟨h1, h2, h3, ⟨c', hc', hm'⟩, h5, h6⟩ := hI.prb p hp
      refine ⟨h1, h2, h3.trans (addCfg_len_le _), ⟨c', cfg_addCfg_of hc', hm'⟩,
        fun e' a b => dead_addCfg (h5 e' a b), fun q hq hq' => ?_⟩
      obtain ⟨z, hz1, hz2, cz, hcz, hqz⟩ := h6 q hq hq'
      exact ⟨z, hz1, hz2, cz, cfg_addCfg_of hcz, hqz⟩
    probe_old := by
      intro r q E' h
      rcases hI.probe_old r q E' h with h | h
      · exact Or.inl (lt_of_lt_of_le h (addCfg_len_le _))
      · exact Or.inr h
    probe_sent := by
      intro r q E' h
      obtain ⟨h1, z, hz, cz, hcz, hqz⟩ := hI.probe_sent r q E' h
      exact ⟨h1, z, hz, cz, cfg_addCfg_of hcz, hqz⟩
    m_probeAck := by
      intro q r b E' s' h
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI.m_probeAck q r b E' s' h
      refine ⟨h1, h2, h3, h4, fun hb => ⟨(h5 hb).1, fun e he c' hc' => ?_⟩⟩
      rcases cfg_addCfg_cases hc' with hc' | ⟨rfl, rfl, rfl⟩
      · exact (h5 hb).2 e he c' hc'
      · -- `q` replied `false` to `PROBE(E')` with `E' > |cs|`: impossible
        exfalso
        have hle : E' ≤ (st.cs (Pa.home q)).length := by
          rcases hI.probe_old _ _ _ h3 with hl | ⟨hpr, hre, hrs⟩
          · exact hl.le
          · have := (hI.prb r hpr).2.2.1
            rw [hre, hrs] at this
            exact this
        subst h1
        omega
    m_frozen := by aframe hI.m_frozen
    m_prepare := by aframe hI.m_prepare
    m_prepareAck := by aframe hI.m_prepareAck
    m_accept := by aframe hI.m_accept
    m_acceptAck := by
      intro q r s' e k t d h
      obtain ⟨h1, h2, c', hc', hq⟩ := hI.m_acceptAck q r s' e k t d h
      exact ⟨h1, h2, c', cfg_addCfg_of hc', hq⟩
    m_decision := by
      rw [hacc]; exact hI.m_decision
    m_newConfig := by
      intro r q e M' h
      obtain ⟨h1, h2, h3⟩ := hI.m_newConfig r q e M' h
      exact ⟨h1, cfg_addCfg_of h2, h3⟩
    m_newState := by
      rw [hacc]
      intro p q e M' a h
      obtain ⟨h1, h2⟩ := hI.m_newState p q e M' a h
      exact ⟨cfg_addCfg_of h1, h2⟩
    net_sub := by aframe hI.net_sub
    nc_unique := by aframe hI.nc_unique
    nc_count := by aframe hI.nc_count
    nc_flight := by aframe hI.nc_flight
    ns_unique := by aframe hI.ns_unique
    ns_count := by aframe hI.ns_count
    ns_flight := by aframe hI.ns_flight
    hist_certify := by aframe hI.hist_certify
    hist_certify_unique := by aframe hI.hist_certify_unique
    hist_decide := by
      rw [hdec]; exact hI.hist_decide
    hist_decide_unique := by aframe hI.hist_decide_unique
    hist_decide_idx := by aframe hI.hist_decide_idx
    hist_certify_idx := by aframe hI.hist_certify_idx
    hist_decide_after := by aframe hI.hist_decide_after
    hist_order := by
      rw [hacc]; exact hI.hist_order
    vinfo_len := by aframe hI.vinfo_len
  }

end Podc.ReconfigurableCommit
