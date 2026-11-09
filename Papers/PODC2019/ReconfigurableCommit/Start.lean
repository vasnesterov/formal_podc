/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Steps2
import Papers.PODC2019.ReconfigurableCommit.AddCfg

/-!
# Starting an epoch preserves the invariant (lines 56–59, with the check `e ≥ new_epoch`)
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The state after `p` started epoch `e` of `s₀` with members `M`; `lg` is the new ghost log. -/
def State.startEpoch (st : State T Pl S P) (p : P) (s₀ : S) (e : ℕ) (M : Finset P)
    (lg : ℕ → Option (Entry T Pl × ℕ)) : State T Pl S P :=
  { st with
    loc := fun q => { st.loc q with
      status := if q = p then .leader else (st.loc q).status
      epoch := if q = p then Function.update (st.loc p).epoch s₀ e else (st.loc q).epoch
      members := if q = p then Function.update (st.loc p).members s₀ M else (st.loc q).members
      leader := if q = p then Function.update (st.loc p).leader s₀ p else (st.loc q).leader
      next := if q = p then (st.loc p).arr.maxSlot else (st.loc q).next }
    started := upd2 st.started s₀ e true
    elog := fun s' e' => if s' = s₀ ∧ e' = e then lg else st.elog s' e'
    base := fun s' e' => if s' = s₀ ∧ e' = e then lg else st.base s' e' }

section
variable (st : State T Pl S P) (p : P) (s₀ : S) (e : ℕ) (M : Finset P)
  (lg : ℕ → Option (Entry T Pl × ℕ)) (Pa : Params T Pl S P)
@[simp] theorem startEpoch_cs : (st.startEpoch p s₀ e M lg).cs = st.cs := rfl
@[simp] theorem startEpoch_hist : (st.startEpoch p s₀ e M lg).hist = st.hist := rfl
@[simp] theorem startEpoch_sent : (st.startEpoch p s₀ e M lg).sent = st.sent := rfl
@[simp] theorem startEpoch_net : (st.startEpoch p s₀ e M lg).net = st.net := rfl
@[simp] theorem startEpoch_vinfo : (st.startEpoch p s₀ e M lg).vinfo = st.vinfo := rfl
@[simp] theorem startEpoch_started : (st.startEpoch p s₀ e M lg).started =
    upd2 st.started s₀ e true := rfl
@[simp] theorem startEpoch_elog : (st.startEpoch p s₀ e M lg).elog =
    fun s' e' => if s' = s₀ ∧ e' = e then lg else st.elog s' e' := rfl
@[simp] theorem startEpoch_base : (st.startEpoch p s₀ e M lg).base =
    fun s' e' => if s' = s₀ ∧ e' = e then lg else st.base s' e' := rfl
@[simp] theorem startEpoch_loc (q : P) : (st.startEpoch p s₀ e M lg).loc q = { st.loc q with
      status := if q = p then .leader else (st.loc q).status
      epoch := if q = p then Function.update (st.loc p).epoch s₀ e else (st.loc q).epoch
      members := if q = p then Function.update (st.loc p).members s₀ M else (st.loc q).members
      leader := if q = p then Function.update (st.loc p).leader s₀ p else (st.loc q).leader
      next := if q = p then (st.loc p).arr.maxSlot else (st.loc q).next } := rfl
@[simp] theorem cfg_startEpoch : cfg (st.startEpoch p s₀ e M lg) = cfg st := rfl
@[simp] theorem acked_startEpoch : Acked (st.startEpoch p s₀ e M lg) = Acked st := rfl
@[simp] theorem replied_startEpoch : Replied (st.startEpoch p s₀ e M lg) = Replied st := rfl
@[simp] theorem dead_startEpoch : Dead (st.startEpoch p s₀ e M lg) = Dead st := rfl
@[simp] theorem aliveK_startEpoch : AliveK (st.startEpoch p s₀ e M lg) = AliveK st := rfl
@[simp] theorem fresh_startEpoch : Fresh (st.startEpoch p s₀ e M lg) = Fresh st := rfl
@[simp] theorem decIn_startEpoch : DecIn (st.startEpoch p s₀ e M lg) = DecIn st := rfl
end

variable {Pa : Params T Pl S P} {st : State T Pl S P}

set_option hygiene false in
local macro "eframe " h:term : tactic => `(tactic| simpa only [startEpoch_cs, startEpoch_hist,
  startEpoch_sent, startEpoch_net, startEpoch_vinfo, startEpoch_loc, cfg_startEpoch,
  acked_startEpoch, replied_startEpoch, dead_startEpoch, aliveK_startEpoch, fresh_startEpoch,
  decIn_startEpoch, hacc, hdec] using $h)

/-- The leader `p` of a configured, not yet started epoch `e` with `new_epoch = e` starts it
(lines 57–59) with its frozen state as the new base. -/
theorem Inv.startEpoch (hI : Inv Pa st) {p : P} {e : ℕ} {M : Finset P}
    (hcfg : cfg st (Pa.home p) e = some ⟨M, p⟩) (hns : st.started (Pa.home p) e = false)
    (hne : (st.loc p).newEpoch = e) (hrep : Replied st p true e (Pa.home p))
    (hgone : ∀ r q M', Pa.home q = Pa.home p → Msg.newConfig e M' ∉ st.net r q) :
    Inv Pa (st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p)) := by
  have hinit : (st.loc p).initialized = true := by
    obtain ⟨r, hr⟩ := hrep
    exact (hI.m_probeAck _ _ _ _ _ hr).2.2.2.1 rfl
  have hpM : p ∈ M := (hI.cfg_wf _ _ _ hcfg).1
  have he0 : (st.loc p).epoch (Pa.home p) < e := by
    have h1 := cfg_lt (hI.loc_view p (Pa.home p))
    have h2 := hI.loc_started p
    rcases Nat.lt_trichotomy ((st.loc p).epoch (Pa.home p)) e with h | h | h
    · exact h
    · rw [h, hns] at h2; cases h2
    · exfalso
      have hm := hI.loc_member p hinit
      have := hI.newEpoch_of_mem (hI.loc_view p (Pa.home p)) hm h hcfg hpM
      omega
  have hnone : ∀ k, st.elog (Pa.home p) e k = none := by
    intro k
    cases h : st.elog (Pa.home p) e k
    · rfl
    · have := hI.elog_started _ _ _ _ h; rw [hns] at this; cases this
  have old_ne : ∀ {s e' k v}, st.elog s e' k = some v → ¬ (s = Pa.home p ∧ e' = e) := by
    rintro s e' k v h ⟨rfl, rfl⟩; rw [hnone] at h; cases h
  have hlg : ∀ {k v}, candOf st (Pa.home p) p k = some v →
      st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) k = some v ∧
        ((st.loc p).arr.ent k).isSome = true := by
    intro k v h
    unfold candOf at h
    split_ifs at h with hk
    exact ⟨h, hk⟩
  have hq_ne : ∀ q, ¬ (Pa.home q = Pa.home p ∧ (st.loc q).epoch (Pa.home q) = e) := by
    rintro q ⟨h1, h2⟩
    have := hI.loc_started q
    rw [h1] at this
    rw [← h1, h2, h1, hns] at this
    cases this
  have hacc : AccL (st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p)) = AccL st := by
    funext s e' k v
    apply propext
    unfold AccL
    simp only [startEpoch_elog, cfg_startEpoch, acked_startEpoch]
    constructor
    · rintro ⟨h1, c, hc, h2⟩
      refine ⟨?_, c, hc, h2⟩
      split_ifs at h1 with hn
      · exfalso
        obtain ⟨rfl, rfl⟩ := hn
        obtain ⟨-, -, hcard⟩ := hI.cfg_wf _ _ _ hc
        obtain ⟨w, hw, hwl⟩ := Finset.exists_mem_ne hcard c.leader
        obtain ⟨r, hr⟩ := h2 w (by simp [Config.followers, hw, hwl])
        obtain ⟨-, ⟨l₀, o, ho⟩, -⟩ := hI.m_acceptAck _ _ _ _ _ _ _ hr
        rw [hnone] at ho; cases ho
      · exact h1
    · rintro ⟨h1, c, hc, h2⟩
      exact ⟨by rw [if_neg (old_ne h1)]; exact h1, c, hc, h2⟩
  have hdec : Decided Pa (st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p)) =
      Decided Pa st := by
    unfold Decided; rw [hacc]
  exact {
    cs_zero := by eframe hI.cs_zero
    cfg_wf := by eframe hI.cfg_wf
    cfg_mem := by eframe hI.cfg_mem
    frz := by eframe hI.frz
    leader_init := by eframe hI.leader_init
    init_init := by eframe hI.init_init
    started_cfg := by
      intro s e' h
      simp only [startEpoch_started, upd2, startEpoch_cs] at h ⊢
      split_ifs at h with hn
      · obtain ⟨rfl, rfl⟩ := hn; exact cfg_lt hcfg
      · exact hI.started_cfg _ _ h
    started_leader := by
      intro s e' c h hc
      simp only [startEpoch_started, upd2, startEpoch_loc] at h ⊢
      rw [cfg_startEpoch] at hc
      split_ifs at h with hn
      · obtain ⟨rfl, rfl⟩ := hn
        rw [hcfg] at hc; cases hc
        simp
      · have h1 := hI.started_leader _ _ _ h hc
        by_cases hl : c.leader = p
        · have hs : Pa.home c.leader = s := (hI.cfg_wf _ _ _ hc).2.1 _ (hI.cfg_wf _ _ _ hc).1
          rw [hl] at hs h1
          subst hs
          simp only [hl, if_true, Function.update_self]
          omega
        · simp only [hl, if_false]
          exact h1
    elog_started := by
      intro s e' k v h
      simp only [startEpoch_elog, startEpoch_started, upd2] at h ⊢
      split_ifs at h ⊢ with hn
      · rfl
      · exact hI.elog_started _ _ _ _ h
    base_elog := by
      intro s e' k v h
      simp only [startEpoch_elog, startEpoch_base] at h ⊢
      split_ifs at h ⊢ with hn
      · exact h
      · exact hI.base_elog _ _ _ _ h
    elog_above := by
      intro s e' k v h hb j hj
      simp only [startEpoch_elog, startEpoch_base] at h hb ⊢
      split_ifs at h hb ⊢ with hn
      · rw [h] at hb; cases hb
      · exact hI.elog_above _ _ _ _ h hb j hj
    elog_origin := by
      intro s e' k x o h
      simp only [startEpoch_elog] at h ⊢
      split_ifs at h with hn
      · obtain ⟨rfl, rfl⟩ := hn
        obtain ⟨h0, -⟩ := hlg h
        obtain ⟨h1, h2, h3⟩ := hI.elog_origin _ _ _ _ _ h0
        refine ⟨by omega, by rw [if_neg (by tauto)]; exact h2, fun j hj y hy => ?_⟩
        rw [if_pos ⟨rfl, rfl⟩] at hy
        rw [if_neg (by tauto)]
        exact h3 j hj y (hlg hy).1
      · obtain ⟨h1, h2, h3⟩ := hI.elog_origin _ _ _ _ _ h
        refine ⟨h1, by rw [if_neg]; exact h2; exact old_ne h2, fun j hj y hy => ?_⟩
        rw [if_neg hn] at hy
        have := h3 j hj y hy
        rw [if_neg (old_ne this)]
        exact this
    elog_dist := by
      intro s e' i j v w hv hw hvw
      simp only [startEpoch_elog] at hv hw
      split_ifs at hv hw with hn
      · exact hI.elog_dist _ _ _ _ _ _ (hlg hv).1 (hlg hw).1 hvw
      · exact hI.elog_dist _ _ _ _ _ _ hv hw hvw
    elog_txn := by
      intro s e' k t l d o h
      simp only [startEpoch_elog, startEpoch_hist] at h ⊢
      split_ifs at h with hn
      · obtain ⟨rfl, rfl⟩ := hn
        exact hI.elog_txn _ _ _ _ _ _ _ (hlg h).1
      · exact hI.elog_txn _ _ _ _ _ _ _ h
    vinfo_none := by
      intro s o k t l d h hv
      simp only [startEpoch_elog, startEpoch_vinfo] at h hv
      split_ifs at h with hn
      · obtain ⟨rfl, rfl⟩ := hn
        have := (hI.elog_origin _ _ _ _ _ (hlg h).1).1
        omega
      · exact hI.vinfo_none _ _ _ _ _ _ h hv
    vinfo_ok := by
      intro s o k t l d J₁ J₂ hl h hv
      have hn : ¬ (s = Pa.home p ∧ o = e) := by
        rintro ⟨rfl, rfl⟩
        simp only [startEpoch_elog, if_pos (And.intro rfl rfl)] at h
        have := (hI.elog_origin _ _ _ _ _ (hlg h).1).1
        omega
      have hel : (st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p)).elog s o = st.elog s o := by
        simp only [startEpoch_elog, if_neg hn]
      have hpl : plAt Pa (st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p)) s o =
          plAt Pa st s o := by
        funext j; unfold plAt; rw [hel]
      rw [hel] at h
      simp only [startEpoch_vinfo, startEpoch_hist, hel, hpl, decIn_startEpoch] at hv ⊢
      exact hI.vinfo_ok _ _ _ _ _ _ _ _ _ h hv
    inv2 := by
      intro s E c hc hpre e' he' k v hv hal
      rw [cfg_startEpoch] at hc
      simp only [aliveK_startEpoch] at hal
      have hlen : e' + 1 < (st.cs s).length := lt_of_le_of_lt (by omega) (cfg_lt hc)
      -- new entries of epoch `e` below a configured `E > e` cannot be accepted
      have hnew : ∀ k v, s = Pa.home p → e' = e → candOf st (Pa.home p) p k = some v →
          AliveK st s e' k → False := by
        rintro k v rfl rfl hv hal
        obtain ⟨c', hc', w, hw, hwn⟩ := hI.frz _ _ hlen
        rw [hcfg] at hc'; cases hc'
        have hwp : w ≠ p := by rintro rfl; omega
        rcases hal _ hcfg w (by simp [Config.followers, hw, hwp]) with ⟨t', d'', hack⟩ | hle
        · obtain ⟨-, ⟨l₀, o, ho⟩, -⟩ := hI.m_acceptAck _ _ _ _ _ _ _ hack.choose_spec
          rw [hnone] at ho; cases ho
        · omega
      by_cases hsE : s = Pa.home p ∧ E = e
      · -- the epoch that starts now
        obtain ⟨rfl, rfl⟩ := hsE
        rw [hcfg] at hc; cases hc
        rw [startEpoch_elog] at hv
        simp only [true_and] at hv
        rw [if_neg (by omega)] at hv
        obtain ⟨h1, h2⟩ := hI.inv2 _ _ _ hcfg (Or.inr hne) e' he' k v hv hal
        have hcd : cand (st.startEpoch p (Pa.home p) E M (candOf st (Pa.home p) p)) (Pa.home p) E
            ⟨M, p⟩ = cand st (Pa.home p) E ⟨M, p⟩ := by
          funext j
          simp [cand, upd2, hns, candOf]
        rw [hcd]
        refine ⟨h1, fun j hj y hy => ?_⟩
        have := h2 j hj y hy
        simp only [startEpoch_elog]
        rw [if_neg (by omega)]
        exact this
      · -- other epochs: the candidate state is unchanged
        have hcd : cand (st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p)) s E c =
            cand st s E c := by
          funext j
          have h1 : (st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p)).started s E =
              st.started s E := by simp [upd2, hsE]
          have h2 : (st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p)).base s E =
              st.base s E := by simp [hsE]
          unfold cand
          simp only [h1, h2]
          by_cases hst' : st.started s E = true
          · simp only [hst', if_true]
          · have hcl : c.leader ≠ p := by
              intro hcl
              rcases hpre with h | h
              · simp [upd2, hsE, hst'] at h
              · simp only [startEpoch_loc, hcl, if_true] at h
                have hs : Pa.home c.leader = s := (hI.cfg_wf _ _ _ hc).2.1 _ (hI.cfg_wf _ _ _ hc).1
                rw [hcl] at hs
                exact hsE ⟨hs.symm, by omega⟩
            have hs : Pa.home c.leader = s := (hI.cfg_wf _ _ _ hc).2.1 _ (hI.cfg_wf _ _ _ hc).1
            have hne' : ¬ (s = Pa.home p ∧ (st.loc c.leader).epoch s = e) := by
              rintro ⟨rfl, h2⟩
              have := hI.loc_started c.leader
              rw [hs, h2, hns] at this
              cases this
            simp only [hst', Bool.false_eq_true, if_false, startEpoch_loc, hcl, startEpoch_elog,
              if_neg hne']
        have hpre' : st.started s E = true ∨ (st.loc c.leader).newEpoch = E := by
          rcases hpre with h | h
          · left; simpa [upd2, hsE] using h
          · right; simpa using h
        rw [hcd]
        simp only [startEpoch_elog] at hv
        split_ifs at hv with hn
        · exact (hnew k v hn.1 hn.2 hv hal).elim
        · obtain ⟨h1, h2⟩ := hI.inv2 _ _ _ hc hpre' e' he' k v hv hal
          refine ⟨h1, fun j hj y hy => ?_⟩
          have := h2 j hj y hy
          simp only [startEpoch_elog]
          rw [if_neg hn]
          exact this
    loc_len := by eframe hI.loc_len
    loc_ent := by eframe hI.loc_ent
    loc_newEpoch := by
      intro q hq
      simp only [startEpoch_loc] at hq ⊢
      split_ifs at hq ⊢ with hqp
      · subst hqp; simp [hne]
      · exact hI.loc_newEpoch q hq
    loc_view := by
      intro q s
      simp only [startEpoch_loc, cfg_startEpoch]
      split_ifs with hqp
      · subst hqp
        by_cases hs : s = Pa.home q
        · subst hs; simp [hcfg]
        · simp [Function.update_apply, hs, hI.loc_view q s]
      · exact hI.loc_view q s
    loc_started := by
      intro q
      simp only [startEpoch_loc, startEpoch_started, upd2]
      split_ifs with h1 h2
      · rfl
      · subst h1; simp at h2
      · rfl
      · exact hI.loc_started q
    loc_member := by
      intro q hq
      simp only [startEpoch_loc] at hq ⊢
      split_ifs with hqp
      · subst hqp; simp [hpM]
      · exact hI.loc_member q hq
    loc_member0 := by
      intro q
      simp only [startEpoch_loc]
      split_ifs with hqp
      · subst hqp; right; simp [hpM]
      · exact hI.loc_member0 q
    loc_leaderArr := by
      intro q hq k
      by_cases hqp : q = p
      · subst hqp
        simp only [startEpoch_loc, if_true, Function.update_self, startEpoch_elog, and_self] at hq ⊢
        unfold candOf
        split_ifs with hk
        · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
          obtain ⟨o, ho⟩ := hI.loc_elog q k x hx
          rw [ho, hx]; rfl
        · simpa using hk
      · simp only [startEpoch_loc, hqp, if_false, startEpoch_elog] at hq ⊢
        rw [if_neg (hq_ne q)]
        exact hI.loc_leaderArr q hq k
    loc_leader := by
      intro q hq
      by_cases hqp : q = p
      · subst hqp
        simp only [startEpoch_loc, if_true, Function.update_self, startEpoch_base, and_self] at hq ⊢
        refine ⟨trivial, hinit, fun k hk => ?_, fun j v hj => ?_⟩
        · by_contra hph
          have := Nat.le_findGreatest (P := fun k => (st.loc q).arr.phase k ≠ .start)
            (hI.loc_len q k hph) hph
          unfold Arrays.maxSlot at hk
          omega
        · unfold candOf at hj
          split_ifs at hj with hk
          have hph := (hI.loc_ent q j).1 hk
          exact Nat.le_findGreatest (P := fun k => (st.loc q).arr.phase k ≠ .start)
            (hI.loc_len q j hph) hph
      · simp only [startEpoch_loc, hqp, if_false, startEpoch_base] at hq ⊢
        rw [if_neg (hq_ne q)]
        exact hI.loc_leader q hq
    loc_follower := by
      intro q hq
      simp only [startEpoch_loc] at hq ⊢
      split_ifs at hq ⊢ with hqp
      · exact hI.loc_follower q hq
    loc_elog := by
      intro q k x hx
      by_cases hqp : q = p
      · subst hqp
        simp only [startEpoch_loc, if_true, Function.update_self, startEpoch_elog, and_self] at hx ⊢
        obtain ⟨o, ho⟩ := hI.loc_elog q k x hx
        exact ⟨o, by simp [candOf, hx, ho]⟩
      · simp only [startEpoch_loc, hqp, if_false, startEpoch_elog] at hx ⊢
        rw [if_neg (hq_ne q)]
        exact hI.loc_elog q k x hx
    loc_base := by
      intro q hq k v hk
      by_cases hqp : q = p
      · subst hqp
        simp only [startEpoch_loc, if_true, Function.update_self, startEpoch_base, and_self] at hq hk ⊢
        unfold candOf at hk
        split_ifs at hk with hks
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hks
        obtain ⟨o, ho⟩ := hI.loc_elog q k x hx
        rw [ho] at hk; cases hk
        exact hx
      · simp only [startEpoch_loc, hqp, if_false, startEpoch_base] at hq hk ⊢
        rw [if_neg (hq_ne q)] at hk
        exact hI.loc_base q hq k v hk
    loc_acked := by
      intro q k t d hk
      simp only [startEpoch_loc, acked_startEpoch] at hk ⊢
      split_ifs at hk ⊢ with hqp
      · subst hqp
        simp only [Function.update_self] at hk
        have := (hI.loc_acked_epoch _ _ _ _ _ _ hk).2.1
        omega
      · exact hI.loc_acked q k t d hk
    loc_acked_epoch := by
      intro q s e' k t d hk
      simp only [startEpoch_loc, acked_startEpoch] at hk ⊢
      obtain ⟨h1, h2, h3⟩ := hI.loc_acked_epoch q s e' k t d hk
      split_ifs with hqp
      · subst hqp; refine ⟨h1, ?_, h3⟩; simp; omega
      · exact ⟨h1, h2, h3⟩
    loc_dec := by
      intro q k hk
      simp only [startEpoch_loc] at hk ⊢
      rw [hacc]
      obtain ⟨dd, h1, e', v, h2, h3, h4⟩ := hI.loc_dec q k hk
      refine ⟨dd, h1, e', v, ?_, h3, h4⟩
      split_ifs with hqp
      · subst hqp; simp; omega
      · exact h2
    loc_acceptAcks := by eframe hI.loc_acceptAcks
    loc_probeAcks := by eframe hI.loc_probeAcks
    prb := by eframe hI.prb
    probe_old := by eframe hI.probe_old
    probe_sent := by eframe hI.probe_sent
    m_probeAck := by eframe hI.m_probeAck
    m_frozen := by
      intro q b E s hr hq hst
      by_cases hqp : q = p
      · exfalso
        subst hqp
        obtain ⟨r, hr⟩ := hr
        have hs := (hI.m_probeAck _ _ _ _ _ hr).1
        subst hs
        simp only [startEpoch_loc, if_true] at hq
        have hE : E = e := hq.symm.trans hne
        subst hE
        simp [upd2] at hst
      · simp only [startEpoch_loc, hqp, if_false] at hq ⊢
        have : st.started s E = false := by
          simp only [startEpoch_started, upd2] at hst
          split_ifs at hst with h
          exact hst
        exact hI.m_frozen q b E s hr hq this
    m_prepare := by eframe hI.m_prepare
    m_prepareAck := by
      intro c r e' s k t l d h
      obtain ⟨o, ho⟩ := hI.m_prepareAck c r e' s k t l d h
      exact ⟨o, by simp only [startEpoch_elog]; rw [if_neg (old_ne ho)]; exact ho⟩
    m_accept := by
      intro c q e' k t l d h
      obtain ⟨o, ho⟩ := hI.m_accept c q e' k t l d h
      exact ⟨o, by simp only [startEpoch_elog]; rw [if_neg (old_ne ho)]; exact ho⟩
    m_acceptAck := by
      intro q r s e' k t d h
      obtain ⟨h1, ⟨l, o, ho⟩, h3⟩ := hI.m_acceptAck q r s e' k t d h
      exact ⟨h1, ⟨l, o, by simp only [startEpoch_elog]; rw [if_neg (old_ne ho)]; exact ho⟩, h3⟩
    m_decision := by rw [hacc]; exact hI.m_decision
    m_newConfig := by eframe hI.m_newConfig
    m_newState := by
      rw [hacc]
      intro p' q e' M' a h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.m_newState p' q e' M' a h
      have hn : ¬ (Pa.home q = Pa.home p ∧ e' = e) := by
        rintro ⟨h7, rfl⟩; rw [h7, hns] at h4; cases h4
      refine ⟨h1, h2, h3, ?_, ?_, h6⟩
      · simp only [startEpoch_started, upd2]; split_ifs <;> first | rfl | exact h4
      · intro k; simp only [startEpoch_base, if_neg hn]; exact h5 k
    net_sub := by eframe hI.net_sub
    nc_unique := by eframe hI.nc_unique
    nc_count := by eframe hI.nc_count
    nc_flight := by
      intro r q e' M' h
      simp only [startEpoch_started, upd2, startEpoch_loc, startEpoch_net] at h ⊢
      have hn : ¬ (Pa.home q = Pa.home p ∧ e' = e) := by
        rintro ⟨h7, rfl⟩; exact hgone r q M' h7 h
      obtain ⟨h1, h2⟩ := hI.nc_flight r q e' M' h
      refine ⟨by rw [if_neg hn]; exact h1, ?_⟩
      split_ifs with hqp
      · subst hqp
        simp only [Function.update_self]
        rcases Nat.lt_trichotomy e' e with h3 | h3 | h3
        · right; omega
        · exact absurd ⟨rfl, h3⟩ hn
        · exfalso
          have := (hI.m_newConfig _ _ _ _ ((hI.net_sub _ _).subset h)).2.2
          obtain ⟨r', hr'⟩ := this
          have := (hI.m_probeAck _ _ _ _ _ hr').2.1
          omega
      · exact h2
    ns_unique := by eframe hI.ns_unique
    ns_count := by eframe hI.ns_count
    ns_flight := by
      intro p' q e' M' a h
      simp only [startEpoch_loc, startEpoch_net] at h ⊢
      have h2 := hI.ns_flight p' q e' M' a h
      split_ifs with hqp
      · subst hqp
        simp only [Function.update_self]
        obtain ⟨h1, h3, -, h4, -⟩ := hI.m_newState _ _ _ _ _ ((hI.net_sub _ _).subset h)
        rcases Nat.lt_trichotomy e' e with h5 | h5 | h5
        · right; omega
        · subst h5; rw [hns] at h4; cases h4
        · exfalso
          have := hI.newEpoch_of_mem h1 h3 h5 hcfg hpM
          omega
      · exact h2
    hist_certify := by eframe hI.hist_certify
    hist_certify_unique := by eframe hI.hist_certify_unique
    hist_decide := by rw [hdec]; exact hI.hist_decide
    hist_decide_unique := by eframe hI.hist_decide_unique
    hist_decide_idx := by eframe hI.hist_decide_idx
    hist_certify_idx := by eframe hI.hist_certify_idx
    hist_decide_after := by eframe hI.hist_decide_after
    hist_order := by rw [hacc]; exact hI.hist_order
    vinfo_len := by eframe hI.vinfo_len
  }

end Podc.ReconfigurableCommit
