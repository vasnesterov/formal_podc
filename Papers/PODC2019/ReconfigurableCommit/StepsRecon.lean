/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.SendProbe
import Papers.PODC2019.ReconfigurableCommit.Prob

/-!
# Preservation of the invariant: `reconfigure` (lines 33–39) and skipping an epoch (lines 51–55)
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st st' : State T Pl S P}

theorem Inv.step_reconfigure (hI : Inv Pa st) {p : P} {s : S}
    (h : step Pa st (.reconfigure p s) = some st') : Inv Pa st' := by
  simp only [step] at h
  split at h
  swap
  · cases h
  rename_i c hpr hc
  cases h
  rw [State.setLoc_eq_setProb]
  have hlen : 1 ≤ (st.cs s).length := by
    have := hI.cs_zero s
    unfold cfg at this
    exact List.length_pos_iff.2 (fun h => by simp [h] at this)
  have hcfg : cfg st s ((st.cs s).length - 1) = some c := by
    unfold cfg
    rw [List.getLast?_eq_getElem?] at hc
    exact hc
  have hI₁ := hI.setProb p true ((st.cs s).length - 1) c.members ((st.cs s).length - 1 + 1) s
    (fun _ => ⟨by omega, by omega, by omega, ⟨c, hcfg, rfl⟩, fun e' h1 h2 => by omega,
      fun q hq hqs => by
        rcases hI.probe_old p q _ hq with h | h
        · rw [hqs] at h; omega
        · rw [hpr] at h; simp at h⟩)
    (fun q E' hq => by
      rcases hI.probe_old p q E' hq with h | h
      · exact Or.inl h
      · rw [hpr] at h; simp at h)
  refine hI₁.send_probe p _ fun b m hb => ?_
  split_ifs at hb with hbm
  cases hb
  have hhome := (hI.cfg_wf _ _ _ hcfg).2.1 b hbm
  unfold PrOK
  refine ⟨by simp, by simp, by simp [hhome], (st.cs s).length - 1, by simp, by omega, c,
    by rw [hhome]; exact hcfg, hbm⟩

theorem Inv.step_probeSkip (hI : Inv Pa st) {p q : P}
    (h : step Pa st (.probeSkip p q) = some st') : Inv Pa st' := by
  simp only [step] at h
  split_ifs at h with hpre
  split at h
  swap
  · cases h
  rename_i c hc
  cases h
  obtain ⟨hpr, hack, hqm, -⟩ := hpre
  have key := State.setLoc_eq_setProb st p (st.loc p).probing ((st.loc p).probedEpoch - 1)
    c.members (st.loc p).reconEpoch (st.loc p).reconShard
  rw [show ({ st.loc p with
        probedEpoch := (st.loc p).probedEpoch - 1
        probedMembers := c.members } : LState T Pl S P) = { st.loc p with
        probing := (st.loc p).probing
        probedEpoch := (st.loc p).probedEpoch - 1
        probedMembers := c.members
        reconEpoch := (st.loc p).reconEpoch
        reconShard := (st.loc p).reconShard } from rfl, key]
  set E := (st.loc p).reconEpoch
  set s := (st.loc p).reconShard
  set pe := (st.loc p).probedEpoch
  obtain ⟨h1, h2, h3, ⟨cpe, hcpe, hcpem⟩, h5, h6⟩ := hI.prb p hpr
  have hcfg : cfg st s (pe - 1) = some c := hc
  -- the epoch `pe` is dead: `q` replied `PROBE_ACK(false)` and is a follower of `pe`
  have hdead : Dead st s pe := by
    obtain ⟨hs, hE, -, -, hfalse⟩ := hI.m_probeAck q p false E s (hI.loc_probeAcks p q _ _ _ hack)
    obtain ⟨hnoack, hnl⟩ := hfalse rfl
    refine ⟨cpe, hcpe, q, ?_, lt_of_lt_of_le h2 hE, fun k t d => hnoack pe h2 k t d⟩
    simp only [Config.followers, Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hcpem ▸ hqm, fun h => hnl pe h2 cpe hcpe h.symm⟩
  have hI₁ := hI.setProb p (st.loc p).probing (pe - 1) c.members E s
    (fun _ => ⟨h1, by omega, h3, ⟨c, hcfg, rfl⟩, fun e' a b => by
        rcases Nat.lt_or_ge pe e' with h | h
        · exact h5 e' h b
        · have : e' = pe := by omega
          subst this; exact hdead,
      fun q' hq' hq's => by
        obtain ⟨z, hz1, hz2, hz⟩ := h6 q' hq' hq's
        exact ⟨z, by omega, hz2, hz⟩⟩)
    (fun q' E' hq' => by
      rcases hI.probe_old p q' E' hq' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩)
  refine hI₁.send_probe p _ fun b m hb => ?_
  split_ifs at hb with hbm
  cases hb
  have hhome := (hI.cfg_wf _ _ _ hcfg).2.1 b hbm
  unfold PrOK
  refine ⟨by simpa using hpr, by simp, by simp [hhome], pe - 1, by simp, by simp only [setProb_loc, if_true] at *; omega, c,
    by rw [hhome]; exact hcfg, hbm⟩

end Podc.ReconfigurableCommit
