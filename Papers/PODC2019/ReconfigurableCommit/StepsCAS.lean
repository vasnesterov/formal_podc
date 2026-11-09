/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.AddCfg
import Papers.PODC2019.ReconfigurableCommit.Prob
import Papers.PODC2019.ReconfigurableCommit.SendNewConfig

/-!
# Preservation of the invariant: end of probing and `compare_and_swap` (lines 45–50)
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st st' : State T Pl S P}

theorem responded_spec {ls : LState T Pl S P} {r : P} (h : responded ls r = true) :
    ∃ b, (r, b, ls.reconEpoch, ls.reconShard) ∈ ls.probeAcks := by
  unfold responded at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨r', b, E, s⟩, hx, hp⟩ := h
  simp only [decide_eq_true_eq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  exact ⟨b, hx⟩

theorem Inv.step_probeDone (hI : Inv Pa st) {p q : P} {M : Finset P}
    (h : step Pa st (.probeDone p q M) = some st') : Inv Pa st' := by
  simp only [step] at h
  split at h
  swap
  · cases h
  rename_i hpre
  obtain ⟨hpr, hack, hqM, hcard, hM⟩ := hpre
  set E := (st.loc p).reconEpoch with hEdef
  set s := (st.loc p).reconShard with hsdef
  obtain ⟨h1, h2, h3, ⟨cpe, hcpe, hcpem⟩, h5, h6⟩ := hI.prb p hpr
  have key := State.setLoc_eq_setProb st p false (st.loc p).probedEpoch (st.loc p).probedMembers
    E s
  split_ifs at h with hlen
  · -- the compare-and-swap succeeds
    cases h
    -- the new leader `q`
    have hackS := hI.loc_probeAcks p q true E s hack
    obtain ⟨hqs, hqE, hpq, hqinit, -⟩ := hI.m_probeAck q p true E s hackS
    obtain ⟨y, hy1, hy2, cy, hcy, hqy⟩ := h6 q hpq hqs.symm
    have hview := hI.loc_view q s
    have hqep : (st.loc q).epoch s < E := hlen ▸ cfg_lt hview
    have hI₁ := hI.addCfg s M q ⟨hqM, fun r hr => (hM r hr).1, hcard⟩
      ⟨(st.loc p).probedEpoch, by omega, fun e' a b => h5 e' a (by omega), ⟨p, hlen ▸ hackS⟩,
        ⟨y, hy1, by omega, cy, hcy, hqy⟩, fun r hr => by
          rcases (hM r hr).2 with hres | hfr
          · obtain ⟨b, hb⟩ := responded_spec hres
            have hbS := hI.loc_probeAcks p r b E s hb
            obtain ⟨hrs, -, hpr', -⟩ := hI.m_probeAck r p b E s hbS
            obtain ⟨z, hz1, hz2, cz, hcz, hrz⟩ := h6 r hpr' hrs.symm
            exact Or.inr ⟨⟨b, p, hlen ▸ hbS⟩, z, hz1, by omega, cz, hcz, hrz⟩
          · left
            intro e he c hc
            exact hfr c (List.mem_of_getElem? hc)⟩
      (by
        rcases Nat.lt_or_ge (st.loc p).probedEpoch ((st.cs s).length - 1) with hlt | hge
        · obtain ⟨c, hc, w, hw, hw1, -⟩ := h5 _ hlt (by omega)
          exact ⟨c, hc, w, (Finset.mem_sdiff.1 hw).1, hw1⟩
        · have : y = (st.cs s).length - 1 := by omega
          subst this
          exact ⟨cy, hcy, q, hqy, by omega⟩)
      (hqinit rfl)
      (fun _ => hI.safe hqs.symm (hqinit rfl) (hlen ▸ hqE) (hlen ▸ hqep) (fun e' a b => h5 e' a (by omega))
        hy1 (by omega) hcy hqy)
    have hst : (st.addCfg s ⟨M, q⟩).setLoc p { st.loc p with probing := false } =
        { st.setLoc p { st.loc p with probing := false } with
          cs := Function.update st.cs s (st.cs s ++ [Config.mk M q]) } := rfl
    rw [← hst]
    have key' := State.setLoc_eq_setProb (st.addCfg s ⟨M, q⟩) p false (st.loc p).probedEpoch
      (st.loc p).probedMembers E s
    rw [show ({ st.loc p with probing := false } : LState T Pl S P) = { (st.addCfg s ⟨M, q⟩).loc p with
        probing := false
        probedEpoch := (st.loc p).probedEpoch
        probedMembers := (st.loc p).probedMembers
        reconEpoch := E
        reconShard := s } from rfl, key']
    have hI₂ := hI₁.setProb p false (st.loc p).probedEpoch (st.loc p).probedMembers E s
      (fun h => by cases h)
      (fun q' E' hq' => by
        left
        rcases hI.probe_old _ _ _ hq' with hl | ⟨-, hre, hrs⟩
        · exact lt_of_lt_of_le hl (addCfg_len_le _)
        · rw [← hrs, addCfg_cs_self]; simp; omega)
    refine hI₂.send_newConfig p _ (fun b m hb => ?_) (fun b b' m m' hb hb' => ?_)
    · split_ifs at hb with hbq
      cases hb
      subst hbq
      have hsq : Pa.home b = s := hqs.symm
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [cfg_setProb]
        rw [hsq, cfg_addCfg, if_pos ⟨rfl, hlen.symm⟩]
      · exact ⟨p, by simpa [hsq, hEdef] using hackS⟩
      · intro r q' M' hq' hm
        simp only [setProb_sent, addCfg_sent] at hm
        obtain ⟨-, hc, -⟩ := hI.m_newConfig r q' _ M' hm
        have := cfg_lt hc
        rw [hq', hsq] at this
        omega
      · simp only [setProb_started, addCfg_started, hsq]
        cases h' : st.started s E
        · rfl
        · have := hI.started_cfg _ _ h'; omega
      · simpa [hsq] using hqep
    · split_ifs at hb hb' with h1 h2
      exact h1.trans h2.symm
  · -- the compare-and-swap fails
    cases h
    rw [show ({ st.loc p with probing := false } : LState T Pl S P) = { st.loc p with
        probing := false
        probedEpoch := (st.loc p).probedEpoch
        probedMembers := (st.loc p).probedMembers
        reconEpoch := E
        reconShard := s } from rfl, key]
    exact hI.setProb p false _ _ E s (fun h => by cases h) (fun q' E' hq' => by
      left
      rcases hI.probe_old _ _ _ hq' with hl | ⟨-, hre, hrs⟩
      · exact hl
      · have h3' : E ≤ (st.cs s).length := h3
        have hlen' : ¬ (st.cs s).length = E := hlen
        have hre' : E = E' := hre
        have hrs' : s = Pa.home q' := hrs
        rw [← hrs', ← hre']
        omega)

end Podc.ReconfigurableCommit
