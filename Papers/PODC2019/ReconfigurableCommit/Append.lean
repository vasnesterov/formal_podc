/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Steps2
import Papers.PODC2019.ReconfigurableCommit.AddCfg

/-!
# Preparing a new transaction preserves the invariant (lines 8–16)

The leader appends the transaction at slot `next + 1`, with its vote, and the ghost log of its
epoch and the vote context (Proposition A.2) are recorded.
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

/-- The state after the leader `p` appended entry `x` at slot `n` of epoch `e` of `s₀`. -/
def State.appendSlot (st : State T Pl S P) (p : P) (n : ℕ) (a' : Arrays T Pl) (s₀ : S) (e : ℕ)
    (x : Entry T Pl) (vi : Option (Finset ℕ × Finset ℕ × ℕ)) : State T Pl S P :=
  { st with
    loc := fun q => { st.loc q with
      next := if q = p then n else (st.loc q).next
      arr := if q = p then a' else (st.loc q).arr }
    elog := upd3 st.elog s₀ e n (some (x, e))
    vinfo := upd3 st.vinfo s₀ e n vi }

section
variable (st : State T Pl S P) (p : P) (n : ℕ) (a' : Arrays T Pl) (s₀ : S) (e : ℕ)
  (x : Entry T Pl) (vi : Option (Finset ℕ × Finset ℕ × ℕ)) (Pa : Params T Pl S P)
@[simp] theorem appendSlot_cs : (st.appendSlot p n a' s₀ e x vi).cs = st.cs := rfl
@[simp] theorem appendSlot_hist : (st.appendSlot p n a' s₀ e x vi).hist = st.hist := rfl
@[simp] theorem appendSlot_sent : (st.appendSlot p n a' s₀ e x vi).sent = st.sent := rfl
@[simp] theorem appendSlot_net : (st.appendSlot p n a' s₀ e x vi).net = st.net := rfl
@[simp] theorem appendSlot_started : (st.appendSlot p n a' s₀ e x vi).started = st.started := rfl
@[simp] theorem appendSlot_base : (st.appendSlot p n a' s₀ e x vi).base = st.base := rfl
@[simp] theorem appendSlot_elog : (st.appendSlot p n a' s₀ e x vi).elog =
    upd3 st.elog s₀ e n (some (x, e)) := rfl
@[simp] theorem appendSlot_vinfo : (st.appendSlot p n a' s₀ e x vi).vinfo =
    upd3 st.vinfo s₀ e n vi := rfl
@[simp] theorem appendSlot_loc (q : P) : (st.appendSlot p n a' s₀ e x vi).loc q = { st.loc q with
      next := if q = p then n else (st.loc q).next
      arr := if q = p then a' else (st.loc q).arr } := rfl
@[simp] theorem cfg_appendSlot : cfg (st.appendSlot p n a' s₀ e x vi) = cfg st := rfl
@[simp] theorem acked_appendSlot : Acked (st.appendSlot p n a' s₀ e x vi) = Acked st := rfl
@[simp] theorem replied_appendSlot : Replied (st.appendSlot p n a' s₀ e x vi) = Replied st := rfl
@[simp] theorem dead_appendSlot : Dead (st.appendSlot p n a' s₀ e x vi) = Dead st := rfl
@[simp] theorem aliveK_appendSlot : AliveK (st.appendSlot p n a' s₀ e x vi) = AliveK st := rfl
@[simp] theorem fresh_appendSlot : Fresh (st.appendSlot p n a' s₀ e x vi) = Fresh st := rfl
@[simp] theorem decIn_appendSlot : DecIn (st.appendSlot p n a' s₀ e x vi) = DecIn st := rfl
end

theorem upd3_apply {α : Type} (g : S → ℕ → ℕ → α) (s : S) (e k : ℕ) (v : α) (s' : S)
    (e' k' : ℕ) : upd3 g s e k v s' e' k' = if s' = s ∧ e' = e ∧ k' = k then v else g s' e' k' :=
  rfl

theorem upd3_same {α : Type} (g : S → ℕ → ℕ → α) (s : S) (e k : ℕ) (v : α) :
    upd3 g s e k v s e k = v := by simp [upd3]

theorem upd3_ne {α : Type} (g : S → ℕ → ℕ → α) (s : S) (e k : ℕ) (v : α) {s' : S} {e' k' : ℕ}
    (h : ¬ (s' = s ∧ e' = e ∧ k' = k)) : upd3 g s e k v s' e' k' = g s' e' k' := by
  simp [upd3, h]

variable {Pa : Params T Pl S P} {st : State T Pl S P}

set_option hygiene false in
local macro "xframe " h:term : tactic => `(tactic| simpa only [appendSlot_cs, appendSlot_hist,
  appendSlot_sent, appendSlot_net, appendSlot_started, appendSlot_base, appendSlot_loc,
  cfg_appendSlot, acked_appendSlot, replied_appendSlot, dead_appendSlot, aliveK_appendSlot,
  fresh_appendSlot, decIn_appendSlot, hacc, hdec] using $h)

/-- Appending a fresh slot at the leader preserves `Inv`. -/
theorem Inv.appendSlot (hI : Inv Pa st) {p : P} {t : T} {l' : Pl} {d' : Dec}
    {vi : Option (Finset ℕ × Finset ℕ × ℕ)} {a' : Arrays T Pl}
    (hlead : (st.loc p).status = .leader)
    (hfind : ∀ k, ((st.loc p).arr.ent k).map (·.1) ≠ some t)
    (htxn : Pa.home p ∈ Pa.σ.shards t ∧ ∃ l₀, Event.certify t l₀ ∈ st.hist ∧
      (l' = Pa.σ.proj l₀ (Pa.home p) ∨ (l' = Pa.σ.eps ∧ d' = .abort)))
    (hvn : vi = none → d' = .abort)
    (hvs : ∀ J₁ J₂ hl, vi = some (J₁, J₂, hl) →
      J₁ = slotsWhere (st.loc p).arr ((st.loc p).next + 1) (condL1 (st.loc p).arr) ∧
      J₂ = slotsWhere (st.loc p).arr ((st.loc p).next + 1) (condL2 (st.loc p).arr) ∧
      hl = st.hist.length ∧
      d' = (Pa.fs (Pa.home p) (payloadsWhere (st.loc p).arr ((st.loc p).next + 1)
          (condL1 (st.loc p).arr)) l').meet
        (Pa.gs (Pa.home p) (payloadsWhere (st.loc p).arr ((st.loc p).next + 1)
          (condL2 (st.loc p).arr)) l'))
    (ha' : a' = { (st.loc p).arr with
        ent := Function.update (st.loc p).arr.ent ((st.loc p).next + 1) (some (t, l', d'))
        phase := Function.update (st.loc p).arr.phase ((st.loc p).next + 1) .prepared
        len := max (st.loc p).arr.len ((st.loc p).next + 1) }) :
    Inv Pa (st.appendSlot p ((st.loc p).next + 1) a'
      (Pa.home p) ((st.loc p).epoch (Pa.home p)) (t, l', d') vi) := by
  have hL := hI.loc_leader p hlead
  have hArr := hI.loc_leaderArr p hL.1
  have hst := hI.loc_started p
  have hAbove : ∀ k, (st.loc p).next + 1 ≤ k →
      st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) k = none := by
    intro k hk
    have hph := hL.2.2.1 k (by omega)
    have hent := (hI.loc_ent p k).not.2 (by simp [hph])
    rw [hArr k] at hent
    cases h : st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) k
    · rfl
    · simp [h] at hent
  have hF1 := hAbove _ le_rfl
  have hF3 : ∀ j v, st.base (Pa.home p) ((st.loc p).epoch (Pa.home p)) j = some v →
      j < (st.loc p).next + 1 := fun j v h => Nat.lt_succ_of_le (hL.2.2.2 j v h)
  -- old entries are untouched
  have elog_old : ∀ {s e' k v}, st.elog s e' k = some v →
      upd3 st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) ((st.loc p).next + 1)
        (some ((t, l', d'), (st.loc p).epoch (Pa.home p))) s e' k = some v := by
    intro s e' k v h
    rw [upd3_ne]
    · exact h
    · rintro ⟨rfl, rfl, rfl⟩; rw [hF1] at h; cases h
  have hacc : AccL (st.appendSlot p ((st.loc p).next + 1) a' (Pa.home p)
      ((st.loc p).epoch (Pa.home p)) (t, l', d') vi) = AccL st := by
    funext s e' k v
    apply propext
    unfold AccL
    simp only [appendSlot_elog, cfg_appendSlot, acked_appendSlot]
    constructor
    · rintro ⟨h1, c, hc, h2⟩
      refine ⟨?_, c, hc, h2⟩
      rw [upd3_apply] at h1
      split_ifs at h1 with hn
      · exfalso
        obtain ⟨rfl, rfl, rfl⟩ := hn
        obtain ⟨-, -, hcard⟩ := hI.cfg_wf _ _ _ hc
        obtain ⟨w, hw, hwl⟩ := Finset.exists_mem_ne hcard c.leader
        obtain ⟨r, hr⟩ := h2 w (by simp [Config.followers, hw, hwl])
        obtain ⟨-, ⟨l₀, o, ho⟩, -⟩ := hI.m_acceptAck _ _ _ _ _ _ _ hr
        rw [hF1] at ho; cases ho
      · exact h1
    · rintro ⟨h1, c, hc, h2⟩
      exact ⟨elog_old h1, c, hc, h2⟩
  have hdec : Decided Pa (st.appendSlot p ((st.loc p).next + 1) a' (Pa.home p)
      ((st.loc p).epoch (Pa.home p)) (t, l', d') vi) = Decided Pa st := by
    unfold Decided; rw [hacc]
  exact {
    cs_zero := by xframe hI.cs_zero
    cfg_wf := by xframe hI.cfg_wf
    cfg_mem := by xframe hI.cfg_mem
    frz := by xframe hI.frz
    leader_init := by xframe hI.leader_init
    init_init := by xframe hI.init_init
    started_cfg := by xframe hI.started_cfg
    started_leader := by xframe hI.started_leader
    elog_started := by
      intro s e' k v h
      simp only [appendSlot_elog, appendSlot_started, upd3_apply] at h ⊢
      split_ifs at h with hn
      · obtain ⟨rfl, rfl, -⟩ := hn; exact hst
      · exact hI.elog_started _ _ _ _ h
    base_elog := by
      intro s e' k v h
      simp only [appendSlot_elog, appendSlot_base, upd3_apply] at h ⊢
      split_ifs with hn
      · obtain ⟨rfl, rfl, rfl⟩ := hn; exact absurd (hF3 _ _ h) (lt_irrefl _)
      · exact hI.base_elog _ _ _ _ h
    elog_above := by
      intro s e' k v h hb j hj
      simp only [appendSlot_elog, appendSlot_base, upd3_apply] at h hb ⊢
      split_ifs at h with hn
      · obtain ⟨rfl, rfl, rfl⟩ := hn
        rcases hbj : st.base (Pa.home p) ((st.loc p).epoch (Pa.home p)) j with _ | w
        · rfl
        · have := hF3 _ _ hbj; omega
      · exact hI.elog_above _ _ _ _ h hb j hj
    elog_origin := by
      intro s e' k x' o h
      simp only [appendSlot_elog, upd3_apply] at h ⊢
      split_ifs at h with hn
      · obtain ⟨rfl, rfl, rfl⟩ := hn
        cases h
        refine ⟨le_rfl, by simp, fun j hj y hy => ?_⟩
        simpa using hy
      · obtain ⟨h1, h2, h3⟩ := hI.elog_origin _ _ _ _ _ h
        refine ⟨h1, ?_, fun j hj y hy => ?_⟩
        · rw [if_neg]; exact h2
          rintro ⟨rfl, rfl, rfl⟩; rw [hF1] at h2; cases h2
        · split_ifs at hy with hn'
          · obtain ⟨rfl, rfl, rfl⟩ := hn'
            exact absurd h (by rw [hAbove k (by omega)]; simp)
          · have := h3 j hj y hy
            rw [if_neg]; exact this
            rintro ⟨rfl, rfl, rfl⟩; rw [hF1] at this; cases this
    elog_dist := by
      intro s e' i j v w hv hw hvw
      simp only [appendSlot_elog, upd3_apply] at hv hw
      split_ifs at hv hw with hi hj hj
      · omega
      · obtain ⟨rfl, rfl, rfl⟩ := hi
        cases hv
        exfalso; apply hfind j; rw [hArr j, hw]; simp [← hvw]
      · obtain ⟨rfl, rfl, rfl⟩ := hj
        cases hw
        exfalso; apply hfind i; rw [hArr i, hv]; simp [hvw]
      · exact hI.elog_dist _ _ _ _ _ _ hv hw hvw
    elog_txn := by
      intro s e' k t' l'' d'' o h
      simp only [appendSlot_elog, upd3_apply, appendSlot_hist] at h ⊢
      split_ifs at h with hn
      · obtain ⟨rfl, rfl, rfl⟩ := hn
        cases h
        exact htxn
      · exact hI.elog_txn _ _ _ _ _ _ _ h
    vinfo_none := by
      intro s o k t' l'' d'' h hv
      simp only [appendSlot_elog, appendSlot_vinfo, upd3_apply] at h hv
      split_ifs at h hv with hn
      · obtain ⟨rfl, rfl, rfl⟩ := hn
        cases h
        exact hvn hv
      · exact hI.vinfo_none _ _ _ _ _ _ h hv
    vinfo_ok := by
      intro s o k t' l'' d'' J₁ J₂ hl h hvi
      simp only [appendSlot_elog, appendSlot_vinfo, appendSlot_hist, upd3_apply] at h hvi ⊢
      split_ifs at h hvi with hn
      · -- the new vote (Proposition A.2)
        obtain ⟨rfl, rfl, rfl⟩ := hn
        cases h
        obtain ⟨rfl, rfl, rfl, hd⟩ := hvs _ _ _ hvi
        have hslot : ∀ cond j, j ∈ slotsWhere (st.loc p).arr ((st.loc p).next + 1) cond →
            j < (st.loc p).next + 1 ∧ cond j = true ∧ ((st.loc p).arr.ent j).isSome = true := by
          intro cond j hj
          simpa [slotsWhere] using hj
        have hent : ∀ j y, (st.loc p).arr.ent j = some y →
            ∃ o, st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) j = some (y, o) := by
          intro j y hy
          rw [hArr j] at hy
          cases h : st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) j with
          | none => simp [h] at hy
          | some w => simp [h] at hy; exact ⟨w.2, by rw [← hy]⟩
        have hpl : ∀ j y, (st.loc p).arr.ent j = some y → j < (st.loc p).next + 1 →
            plAt Pa (st.appendSlot p ((st.loc p).next + 1) a' (Pa.home p)
              ((st.loc p).epoch (Pa.home p)) (t, l', d') vi) (Pa.home p)
              ((st.loc p).epoch (Pa.home p)) j = y.2.1 := by
          intro j y hy hj
          obtain ⟨o, ho⟩ := hent j y hy
          unfold plAt
          rw [appendSlot_elog, upd3_ne _ _ _ _ _ (by omega), ho]
          rfl
        have hpw : ∀ cond, payloadsWhere (st.loc p).arr ((st.loc p).next + 1) cond =
            (slotsWhere (st.loc p).arr ((st.loc p).next + 1) cond).image
              (plAt Pa (st.appendSlot p ((st.loc p).next + 1) a' (Pa.home p)
                ((st.loc p).epoch (Pa.home p)) (t, l', d') vi) (Pa.home p)
                ((st.loc p).epoch (Pa.home p))) := by
          intro cond
          ext y
          simp only [payloadsWhere, List.mem_toFinset, List.mem_filterMap, List.mem_range,
            Finset.mem_image]
          constructor
          · rintro ⟨j, hj, hy⟩
            split_ifs at hy with hc
            obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hy
            exact ⟨j, by simp [slotsWhere, hj, hc, hz], hpl j z hz hj⟩
          · rintro ⟨j, hj, rfl⟩
            obtain ⟨hj1, hj2, hj3⟩ := hslot cond j hj
            obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hj3
            exact ⟨j, hj1, by simp [hj2, hz, hpl j z hz hj1]⟩
        -- the vote of a decided slot below is the accepted one
        have hdecv : ∀ j v, j < (st.loc p).next + 1 →
            st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) j = some v →
            (st.loc p).arr.phase j = .decided → ∃ dd, (st.loc p).arr.dec j = some dd ∧
              Event.decide v.1.1 dd ∈ st.hist := by
          intro j v hj hv hph
          obtain ⟨dd, hdd, e₁, v₁, he₁, hacc₁, hdec₁⟩ := hI.loc_dec p j hph
          have := hI.accL_le hacc₁ he₁ hst
          rw [hv] at this
          cases this
          exact ⟨dd, hdd, hdec₁⟩
        have htake : st.hist.take st.hist.length = st.hist := List.take_length
        refine ⟨le_rfl, fun j hj => ?_, ?_, fun j hj v hv => ?_, fun j hj v hv => ?_,
          fun j hj v hv => ?_⟩
        · have hj' : ∃ cond, j ∈ slotsWhere (st.loc p).arr ((st.loc p).next + 1) cond := by
            rcases Finset.mem_union.1 hj with h | h
            · exact ⟨_, h⟩
            · exact ⟨_, h⟩
          obtain ⟨cond, hc⟩ := hj'
          obtain ⟨hj1, -, hj3⟩ := hslot cond j hc
          refine ⟨hj1, ?_⟩
          rw [if_neg (by omega)]
          obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hj3
          obtain ⟨o, ho⟩ := hent j z hz
          simp [ho]
        · rw [hpw, hpw] at hd; exact hd
        · rw [if_neg (by have := (hslot _ j hj).1; omega)] at hv
          obtain ⟨hj1, hc, -⟩ := hslot _ j hj
          simp only [condL1, decide_eq_true_eq] at hc
          obtain ⟨dd, hdd, hdm⟩ := hdecv j v hj1 hv hc.1
          rw [hc.2] at hdd; cases hdd
          unfold DecIn; rw [appendSlot_hist, htake]; exact hdm
        · rw [if_neg (by have := (hslot _ j hj).1; omega)] at hv
          obtain ⟨-, hc, -⟩ := hslot _ j hj
          simp only [condL2, decide_eq_true_eq, hArr j, hv] at hc
          simpa using hc.2
        · rw [if_neg (by omega)] at hv
          have hentj : (st.loc p).arr.ent j = some v.1 := by rw [hArr j, hv]; rfl
          have hph : (st.loc p).arr.phase j ≠ .start := (hI.loc_ent p j).1 (by simp [hentj])
          unfold DecIn; rw [appendSlot_hist, htake]
          cases hphj : (st.loc p).arr.phase j with
          | start => exact absurd hphj hph
          | prepared =>
            rcases hvd : v.1.2.2 with _ | _
            · right; left
              exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, by simp [condL2, hphj, hentj, hvd]⟩
            · right; right; left; rfl
          | decided =>
            obtain ⟨dd, hdd, hdm⟩ := hdecv j v hj hv hphj
            rcases dd with _ | _
            · left; simp [slotsWhere, condL1, hj, hphj, hdd, hentj]
            · right; right; right; exact hdm
      · -- an old vote: its context only mentions old slots
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.vinfo_ok s o k t' l'' d'' J₁ J₂ hl h hvi
        have hne : ∀ j, (st.elog s o j).isSome = true →
            ¬ (s = Pa.home p ∧ o = (st.loc p).epoch (Pa.home p) ∧ j = (st.loc p).next + 1) := by
          rintro j hj ⟨rfl, rfl, rfl⟩
          rw [hF1] at hj; cases hj
        have hpl : ∀ j, (st.elog s o j).isSome = true →
            plAt Pa (st.appendSlot p ((st.loc p).next + 1) a' (Pa.home p)
              ((st.loc p).epoch (Pa.home p)) (t, l', d') vi) s o j = plAt Pa st s o j := by
          intro j hj
          unfold plAt
          rw [appendSlot_elog, upd3_ne _ _ _ _ _ (hne j hj)]
        refine ⟨by omega, fun j hj => ?_, ?_, fun j hj v hv => ?_, fun j hj v hv => ?_,
          fun j hj v hv => ?_⟩
        · obtain ⟨hj1, hj2⟩ := h2 j hj
          exact ⟨hj1, by rw [if_neg (hne j hj2)]; exact hj2⟩
        · rw [h3]
          congr 2
          · exact Finset.image_congr fun j hj => (hpl j (h2 j (Finset.mem_union_left _ hj)).2).symm
          · exact Finset.image_congr fun j hj => (hpl j (h2 j (Finset.mem_union_right _ hj)).2).symm
        · rw [if_neg (hne j (h2 j (Finset.mem_union_left _ hj)).2)] at hv
          simpa using h4 j hj v hv
        · rw [if_neg (hne j (h2 j (Finset.mem_union_right _ hj)).2)] at hv
          exact h5 j hj v hv
        · split_ifs at hv with hn'
          · exfalso
            obtain ⟨rfl, rfl, rfl⟩ := hn'
            rw [hAbove k (by omega)] at h
            cases h
          · simpa using h6 j hj v hv
    inv2 := by
      intro s E c hc hpre e' he' k v hv hal
      simp only [aliveK_appendSlot] at hal
      -- the candidate state is unchanged
      have hcand : ∀ j, cand (st.appendSlot p ((st.loc p).next + 1) a' (Pa.home p)
        ((st.loc p).epoch (Pa.home p)) (t, l', d') vi) s E c j = cand st s E c j := by
        intro j
        have hcd : cand (st.appendSlot p ((st.loc p).next + 1) a' (Pa.home p)
            ((st.loc p).epoch (Pa.home p)) (t, l', d') vi) s E c =
            if st.started s E then st.base s E else fun k =>
              if ((if c.leader = p then a' else (st.loc c.leader).arr).ent k).isSome then
                upd3 st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) ((st.loc p).next + 1)
                  (some ((t, l', d'), (st.loc p).epoch (Pa.home p))) s
                  ((st.loc c.leader).epoch s) k
              else none := rfl
        rw [hcd]
        unfold cand
        by_cases hst' : st.started s E = true
        · simp only [hst', if_true]
        · simp only [hst', if_false, Bool.false_eq_true]
          have hcl : c.leader ≠ p := by
            intro hcl
            rcases hpre with hpre | hpre
            · simp [hst'] at hpre
            · have := hI.frozen_leader hc (by simpa using hst') (by simpa [hcl] using hpre)
              rw [hcl, hlead] at this; cases this
          simp only [hcl, if_false]
          by_cases hc2 : ((st.loc c.leader).arr.ent j).isSome = true
          · rw [if_pos hc2, if_pos hc2]
            obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hc2
            obtain ⟨o, ho⟩ := hI.loc_elog _ _ _ hy
            have := hI.cfg_wf _ _ _ hc
            have hhome : Pa.home c.leader = s := this.2.1 _ this.1
            rw [hhome] at ho
            rw [elog_old ho, ho]
          · rw [if_neg hc2, if_neg hc2]
      have hpre' : st.started s E = true ∨ (st.loc c.leader).newEpoch = E := by
        rcases hpre with h | h
        · exact Or.inl h
        · right; simpa using h
      simp only [appendSlot_elog, upd3_apply] at hv
      split_ifs at hv with hn
      · -- the new slot cannot be accepted: the frozen follower of epoch `e` blocks it
        obtain ⟨rfl, rfl, rfl⟩ := hn
        exfalso
        have hlen : (st.loc p).epoch (Pa.home p) + 1 < (st.cs (Pa.home p)).length :=
          lt_of_le_of_lt (by omega) (cfg_lt hc)
        obtain ⟨c', hc', w, hw, hwn⟩ := hI.frz _ _ hlen
        have hview := hI.loc_view p (Pa.home p)
        rw [hc'] at hview
        cases hview
        have hwp : w ≠ p := by
          rintro rfl
          have := hI.loc_newEpoch w (by rw [hlead]; simp)
          omega
        have hwF : w ∈ (Config.mk ((st.loc p).members (Pa.home p))
            ((st.loc p).leader (Pa.home p))).followers := by
          simp [Config.followers, hw, hL.1, hwp]
        rcases hal _ hc' w hwF with ⟨t', d'', hack⟩ | hle
        · obtain ⟨-, ⟨l₀, o, ho⟩, -⟩ := hI.m_acceptAck _ _ _ _ _ _ _ hack.choose_spec
          rw [hF1] at ho; cases ho
        · omega
      · obtain ⟨h1, h2⟩ := hI.inv2 s E c hc hpre' e' he' k v hv hal
        refine ⟨by rw [hcand]; exact h1, fun j hj y hy => ?_⟩
        rw [hcand] at hy
        have := h2 j hj y hy
        simp only [appendSlot_elog]
        exact elog_old this
    loc_len := by
      intro q k hk
      simp only [appendSlot_loc] at hk ⊢
      split_ifs at hk ⊢ with hq
      · subst hq ha'
        simp only [Function.update_apply] at hk ⊢
        split_ifs at hk with hkn
        · omega
        · exact (hI.loc_len q k hk).trans (le_max_left _ _)
      · exact hI.loc_len q k hk
    loc_ent := by
      intro q k
      simp only [appendSlot_loc]
      split_ifs with hq
      · subst hq ha'
        simp only [Function.update_apply]
        split_ifs with hkn
        · simp
        · exact hI.loc_ent q k
      · exact hI.loc_ent q k
    loc_newEpoch := by xframe hI.loc_newEpoch
    loc_view := by xframe hI.loc_view
    loc_started := by xframe hI.loc_started
    loc_member := by xframe hI.loc_member
    loc_member0 := by xframe hI.loc_member0
    loc_leaderArr := by
      intro q hq k
      simp only [appendSlot_loc, appendSlot_elog] at hq ⊢
      split_ifs with hqp
      · subst hqp ha'
        simp only [Function.update_apply, upd3_apply, true_and]
        split_ifs with hkn
        · simp
        · exact hArr k
      · rw [upd3_ne]
        · exact hI.loc_leaderArr q hq k
        · rintro ⟨hs, he, rfl⟩
          apply hqp
          have h1 := hI.loc_view q (Pa.home q)
          have h2 := hI.loc_view p (Pa.home p)
          rw [he, hs] at h1
          rw [hs] at hq
          rw [h1] at h2
          simp only [Option.some.injEq, Config.mk.injEq] at h2
          rw [← hq, h2.2, hL.1]
    loc_leader := by
      intro q hq
      simp only [appendSlot_loc, appendSlot_base] at hq ⊢
      split_ifs with hqp
      · subst hqp ha'
        refine ⟨hL.1, hL.2.1, fun k hk => ?_, fun j v hj => (hF3 j v hj).le⟩
        simp only [Function.update_apply]
        rw [if_neg (by omega)]
        exact hL.2.2.1 k (by omega)
      · exact hI.loc_leader q hq
    loc_follower := by xframe hI.loc_follower
    loc_elog := by
      intro q k x' hx
      simp only [appendSlot_loc, appendSlot_elog] at hx ⊢
      split_ifs at hx with hqp
      · subst hqp ha'
        simp only [Function.update_apply] at hx
        split_ifs at hx with hkn
        · cases hx; exact ⟨(st.loc q).epoch (Pa.home q), by simp [upd3_apply, hkn]⟩
        · obtain ⟨o, ho⟩ := hI.loc_elog q k x' hx
          exact ⟨o, elog_old ho⟩
      · obtain ⟨o, ho⟩ := hI.loc_elog q k x' hx
        exact ⟨o, elog_old ho⟩
    loc_base := by
      intro q hq k v hk
      simp only [appendSlot_loc, appendSlot_base] at hq hk ⊢
      split_ifs with hqp
      · subst hqp ha'
        simp only [Function.update_apply]
        rw [if_neg (by have := hF3 k v hk; omega)]
        exact hI.loc_base q hq k v hk
      · exact hI.loc_base q hq k v hk
    loc_acked := by
      intro q k t' d'' hk
      simp only [appendSlot_loc, acked_appendSlot] at hk ⊢
      split_ifs with hqp
      · subst hqp ha'
        simp only [Function.update_apply]
        have := (hI.m_acceptAck _ _ _ _ _ _ _ hk.choose_spec).2.1
        obtain ⟨l₀, o, ho⟩ := this
        rw [if_neg]
        · exact hI.loc_acked q k t' d'' hk
        · rintro rfl; rw [hF1] at ho; cases ho
      · exact hI.loc_acked q k t' d'' hk
    loc_acked_epoch := by xframe hI.loc_acked_epoch
    loc_dec := by
      intro q k hk
      simp only [appendSlot_loc] at hk ⊢
      rw [hacc]
      split_ifs at hk ⊢ with hqp
      · subst hqp ha'
        simp only [Function.update_apply] at hk ⊢
        split_ifs at hk with hkn
        exact hI.loc_dec q k hk
      · exact hI.loc_dec q k hk
    loc_acceptAcks := by xframe hI.loc_acceptAcks
    loc_probeAcks := by xframe hI.loc_probeAcks
    prb := by xframe hI.prb
    probe_old := by xframe hI.probe_old
    probe_sent := by xframe hI.probe_sent
    m_probeAck := by xframe hI.m_probeAck
    m_frozen := by xframe hI.m_frozen
    m_prepare := by xframe hI.m_prepare
    m_prepareAck := by
      intro c r e' s k t' l'' d'' h
      obtain ⟨o, ho⟩ := hI.m_prepareAck c r e' s k t' l'' d'' h
      exact ⟨o, elog_old ho⟩
    m_accept := by
      intro c q e' k t' l'' d'' h
      obtain ⟨o, ho⟩ := hI.m_accept c q e' k t' l'' d'' h
      exact ⟨o, elog_old ho⟩
    m_acceptAck := by
      intro q r s e' k t' d'' h
      obtain ⟨h1, ⟨l₀, o, ho⟩, h3⟩ := hI.m_acceptAck q r s e' k t' d'' h
      exact ⟨h1, ⟨l₀, o, elog_old ho⟩, h3⟩
    m_decision := by xframe hI.m_decision
    m_newConfig := by xframe hI.m_newConfig
    m_newState := by xframe hI.m_newState
    net_sub := by xframe hI.net_sub
    nc_unique := by xframe hI.nc_unique
    nc_count := by xframe hI.nc_count
    nc_flight := by xframe hI.nc_flight
    ns_unique := by xframe hI.ns_unique
    ns_count := by xframe hI.ns_count
    ns_flight := by xframe hI.ns_flight
    hist_certify := by xframe hI.hist_certify
    hist_certify_unique := by xframe hI.hist_certify_unique
    hist_decide := by xframe hI.hist_decide
    hist_decide_unique := by xframe hI.hist_decide_unique
    hist_decide_idx := by xframe hI.hist_decide_idx
    hist_certify_idx := by xframe hI.hist_certify_idx
    hist_decide_after := by xframe hI.hist_decide_after
    hist_order := by
      intro i t' d'' h s hs
      obtain ⟨e', k, v, hv, h2, h3⟩ := hI.hist_order i t' d'' h s hs
      refine ⟨e', k, v, hacc ▸ hv, h2, fun J₁ J₂ hl hvi => h3 J₁ J₂ hl ?_⟩
      simp only [appendSlot_vinfo] at hvi
      rw [upd3_ne] at hvi
      · exact hvi
      · rintro ⟨rfl, he, rfl⟩
        have := (hI.elog_origin _ _ _ _ _ hv.1).2.1
        rw [he, hF1] at this; cases this
    vinfo_len := by
      intro s o k J₁ J₂ hl h
      simp only [appendSlot_vinfo, upd3_apply, appendSlot_hist] at h ⊢
      split_ifs at h with hn
      · exact ((hvs _ _ _ h).2.2.1).le
      · exact hI.vinfo_len _ _ _ _ _ _ h
  }

end Podc.ReconfigurableCommit
