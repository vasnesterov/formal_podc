/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Start
import Papers.PODC2019.ReconfigurableCommit.SendNewState
import Papers.PODC2019.ReconfigurableCommit.Erase

/-!
# Preservation of the invariant: delivering `NEW_CONFIG` (lines 56–60), corrected protocol
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st st' : State T Pl S P}

/-- The local update of line 57–59 together with the ghost update is `startEpoch`. -/
theorem startEpoch_eq (st : State T Pl S P) (Pa : Params T Pl S P) (p : P) (e : ℕ)
    (M : Finset P) :
    ({ st.setLoc p { st.loc p with
        status := .leader
        epoch := Function.update (st.loc p).epoch (Pa.home p) e
        members := Function.update (st.loc p).members (Pa.home p) M
        leader := Function.update (st.loc p).leader (Pa.home p) p
        next := (st.loc p).arr.maxSlot } with
      started := upd2 st.started (Pa.home p) e true
      elog := fun s' e' => if s' = Pa.home p ∧ e' = e then (fun k =>
        if ((st.loc p).arr.ent k).isSome then st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) k
        else none) else st.elog s' e'
      base := fun s' e' => if s' = Pa.home p ∧ e' = e then (fun k =>
        if ((st.loc p).arr.ent k).isSome then st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) k
        else none) else st.base s' e' } : State T Pl S P) =
      st.startEpoch p (Pa.home p) e M (candOf st (Pa.home p) p) := by
  unfold State.setLoc State.startEpoch candOf
  simp only [State.mk.injEq, and_true, true_and]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [hq]

/-- Delivering `NEW_CONFIG(e, M)` (the `i`-th message of channel `src → dst`) in the corrected
protocol. The handler runs on the state with the message removed. -/
theorem Inv.deliver_newConfig (hfix : Pa.fixNewConfig = true) (hI : Inv Pa st) {src dst : P}
    {i e : ℕ} {M : Finset P} (hm : (st.net src dst)[i]? = some (Msg.newConfig e M))
    (h : handle Pa (st.erase src dst i) src dst (.newConfig e M) = some st') : Inv Pa st' := by
  have hmS : Msg.newConfig e M ∈ st.sent src dst :=
    (hI.net_sub src dst).subset (List.mem_of_getElem? hm)
  obtain ⟨he1, hcfg, hrep⟩ := hI.m_newConfig _ _ _ _ hmS
  obtain ⟨hns, hfl⟩ := hI.nc_flight _ _ _ _ (List.mem_of_getElem? hm)
  have hI₁ := hI.erase src dst i
  have hgone := hI.nc_gone hm
  -- everything but the network is the same after removing the message
  have hcfg₁ : cfg (st.erase src dst i) (Pa.home dst) e = some ⟨M, dst⟩ := hcfg
  have hns₁ : (st.erase src dst i).started (Pa.home dst) e = false := hns
  have hrep₁ : Replied (st.erase src dst i) dst true e (Pa.home dst) := hrep
  obtain ⟨r, hr⟩ := hrep
  have hge : e ≤ ((st.erase src dst i).loc dst).newEpoch := (hI.m_probeAck _ _ _ _ _ hr).2.1
  simp only [handle, hfix] at h
  split at h
  swap
  · cases h
  rename_i hle
  cases h
  have hle' : ((st.erase src dst i).loc dst).newEpoch ≤ e := by simpa using hle
  have hne : ((st.erase src dst i).loc dst).newEpoch = e := by omega
  rw [startEpoch_eq]
  have hI₂ := hI₁.startEpoch (p := dst) hcfg₁ hns₁ hne hrep₁
    (fun r' q M' hq => hgone r' q M' hq)
  refine hI₂.send_newState dst _ fun b m hb => ?_
  split_ifs at hb with hbM
  cases hb
  obtain ⟨hbM', hbd⟩ := Finset.mem_sdiff.1 hbM
  have hbd' : b ≠ dst := by simpa using hbd
  have hhome : Pa.home b = Pa.home dst := by
    have := (hI.cfg_wf _ _ _ hcfg).2.1
    rw [this b hbM', this dst (hI.cfg_wf _ _ _ hcfg).1]
  have hacc : ∀ {s e' k v}, AccL (st.erase src dst i) s e' k v → AccL ((st.erase src dst i).startEpoch
      dst (Pa.home dst) e M (candOf (st.erase src dst i) (Pa.home dst) dst)) s e' k v := by
    rintro s e' k v ⟨h1, c, hc, h2⟩
    refine ⟨?_, c, hc, h2⟩
    simp only [startEpoch_elog]
    rw [if_neg]
    · exact h1
    · rintro ⟨rfl, rfl⟩
      have := hI₁.elog_started _ _ _ _ h1
      rw [hns₁] at this; cases this
  refine ⟨?_, hbM', hbd', ?_, fun k => ?_, hI₁.loc_len dst, hI₁.loc_ent dst, fun k hk => ?_, ?_, ?_⟩
  · rw [cfg_startEpoch, hhome]; exact hcfg₁
  · simp [hhome, upd2]
  · simp only [startEpoch_base, hhome, and_self, if_true]
    unfold candOf
    split_ifs with hk
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
      obtain ⟨o, ho⟩ := hI₁.loc_elog dst k x hx
      rw [ho, hx]; rfl
    · simpa using hk
  · obtain ⟨dd, h1, e', v, h2, h3, h4⟩ := hI₁.loc_dec dst k hk
    have he0 : ((st.erase src dst i).loc dst).epoch (Pa.home dst) < e := by
      rcases hfl with h | h
      · exact h
      · exfalso; change e < ((st.erase src dst i).loc dst).newEpoch at h; omega
    exact ⟨dd, h1, e', v, by omega, hhome ▸ hacc h3, h4⟩
  · intro p' M' a' hs
    obtain ⟨-, -, -, h4, -⟩ := hI₁.m_newState _ _ _ _ _ hs
    rw [hhome, hns₁] at h4
    cases h4
  · simp only [startEpoch_loc, hbd', if_false]
    have hst := hI₁.loc_started b
    rcases Nat.lt_trichotomy (((st.erase src dst i).loc b).epoch (Pa.home b)) e with h | h | h
    · exact Or.inl h
    · rw [h, hhome, hns₁] at hst; cases hst
    · right
      rcases hI₁.loc_member0 b with h0 | hm0
      · omega
      · have := hI₁.newEpoch_of_mem (hI₁.loc_view b (Pa.home b)) hm0 h (hhome ▸ hcfg₁) hbM'
        omega

end Podc.ReconfigurableCommit
