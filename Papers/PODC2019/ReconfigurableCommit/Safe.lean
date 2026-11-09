/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Consequences

/-!
# Invariant 5 and the safety of probing

* `Inv.inv5` (Invariant 5 of the paper, in the form "a process that leaves the membership and
  comes back skipped a dead epoch");
* `Inv.safe`: when a reconfiguration chooses the new leader `q` (a `PROBE_ACK(true)`), every slot of
  an earlier epoch that may still be accepted is in `q`'s state, with the same prefix (the core of
  the proof sketch of Invariant 2, §4).
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st : State T Pl S P}

theorem Dead.not_aliveK {s : S} {e k : ℕ} (hd : Dead st s e) : ¬ AliveK st s e k := by
  intro ha
  obtain ⟨c, hc, q, hq, h1, h2⟩ := hd
  rcases ha c hc q hq with ⟨t, d, h⟩ | h
  · exact h2 k t d h
  · omega

/-- Invariant 5 of [Bravo–Gotsman 2019]: if `q` is a member of epochs `e₀ < e' < y` of shard `s`
but not of `e'`, then `e'` is dead. -/
theorem Inv.inv5 (hI : Inv Pa st) {s : S} {q : P} {e₀ e' : ℕ} {c₀ c' : Config P}
    (h₀ : cfg st s e₀ = some c₀) (hq₀ : q ∈ c₀.members) (he₀ : e₀ < e')
    (h' : cfg st s e' = some c') (hq' : q ∉ c'.members) :
    ∀ y, e' < y → ∀ cy, cfg st s y = some cy → q ∈ cy.members → Dead st s e' := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy cy hcy hqy
    obtain ⟨pe, hpe, hdead, -, -, hmem⟩ := hI.cfg_mem s y cy (by omega) hcy
    rcases hmem q hqy with hfr | ⟨-, z, hz1, hz2, cz, hcz, hqz⟩
    · exact absurd hq₀ (hfr e₀ (by omega) c₀ h₀)
    · rcases lt_trichotomy z e' with h | h | h
      · exact hdead e' (by omega) hy
      · subst h; rw [h'] at hcz; cases hcz; exact absurd hqz hq'
      · exact ih z hz2 h cz hcz hqz

/-- The candidate state of a not yet started epoch whose leader is `q`. -/
def candOf (st : State T Pl S P) (s : S) (q : P) : ℕ → Option (Entry T Pl × ℕ) := fun k =>
  if ((st.loc q).arr.ent k).isSome then st.elog s ((st.loc q).epoch s) k else none

/-- The heart of Invariant 2: a process `q` chosen as leader of epoch `E` of shard `s` (it is
initialized, frozen with `new_epoch = E`, and a member of an epoch `y ≥ pe` probed by the
reconfiguration, all epochs in `(pe, E)` being dead) holds every slot of an earlier epoch that may
still be accepted, with the same prefix. -/
theorem Inv.safe (hI : Inv Pa st) {s : S} {q : P} {E pe y : ℕ} {cy : Config P}
    (hs : Pa.home q = s) (hinit : (st.loc q).initialized = true) (hnE : E ≤ (st.loc q).newEpoch)
    (hE : (st.loc q).epoch s < E) (hdead : ∀ e', pe < e' → e' < E → Dead st s e')
    (hy1 : pe ≤ y) (hy2 : y < E) (hcy : cfg st s y = some cy) (hqy : q ∈ cy.members) :
    ∀ e' < E, ∀ k v, st.elog s e' k = some v → AliveK st s e' k →
      candOf st s q k = some v ∧ ∀ j < k, ∀ w, candOf st s q j = some w → st.elog s e' j = some w := by
  intro e' he' k v hv hal
  subst hs
  set e₀ := (st.loc q).epoch (Pa.home q) with he₀
  have hview := hI.loc_view q (Pa.home q)
  have hq₀ : q ∈ (st.loc q).members (Pa.home q) := hI.loc_member q hinit
  -- the prefix part is easy whenever `candOf` agrees with the log of `e₀` below `k`
  rcases lt_trichotomy e₀ e' with hlt | heq | hgt
  · -- `e' > e₀`: nothing can be accepted at `e'`
    exfalso
    obtain ⟨c', hc'⟩ : ∃ c', cfg st (Pa.home q) e' = some c' :=
      hI.cfg_of_started (hI.elog_started _ _ _ _ hv)
    rcases Nat.lt_or_ge pe e' with hpe | hpe
    · exact (hdead e' hpe he').not_aliveK hal
    · by_cases hqm : q ∈ c'.members
      · by_cases hql : c'.leader = q
        · have := hI.started_leader _ _ _ (hI.elog_started _ _ _ _ hv) hc'
          rw [hql] at this
          omega
        · have hF : q ∈ c'.followers := by
            simp [Config.followers, hqm, Ne.symm hql]
          rcases hal c' hc' q hF with ⟨t, d, hack⟩ | hle
          · have := (hI.loc_acked_epoch _ _ _ _ _ _ hack).2.1
            omega
          · omega
      · have hy : e' < y := by
          rcases Nat.lt_or_ge e' y with h | h
          · exact h
          · have : y = e' := by omega
            subst this; rw [hcy] at hc'; cases hc'; exact absurd hqy hqm
        exact (hI.inv5 hview hq₀ hlt hc' hqm y hy cy hcy hqy).not_aliveK hal
  · -- `e' = e₀`
    subst heq
    by_cases hql : (st.loc q).leader (Pa.home q) = q
    · have harr := hI.loc_leaderArr q hql
      have hc : ∀ k', candOf st (Pa.home q) q k' = st.elog (Pa.home q) e₀ k' := by
        intro k'
        unfold candOf
        rw [harr k']
        cases h : st.elog (Pa.home q) e₀ k' <;> simp [h, he₀]
      refine ⟨by rw [hc]; exact hv, fun j _ w hw => by rw [hc] at hw; exact hw⟩
    · have hF : q ∈ (Config.mk ((st.loc q).members (Pa.home q))
          ((st.loc q).leader (Pa.home q))).followers := by
        simp [Config.followers, hq₀, Ne.symm hql]
      rcases hal _ hview q hF with ⟨t, d, hack⟩ | hle
      · obtain ⟨l, hl⟩ := hI.loc_acked q k t d hack
        refine ⟨?_, fun j _ w hw => ?_⟩
        · unfold candOf; simp [hl, ← he₀, hv]
        · unfold candOf at hw
          split_ifs at hw
          exact hw
      · omega
  · -- `e' < e₀`: by Invariant 2 for the started epoch `e₀`
    have hst : st.started (Pa.home q) e₀ = true := hI.loc_started q
    have h2 := hI.inv2 (Pa.home q) e₀ _ hview (Or.inl hst) e' hgt k v hv hal
    simp only [cand, hst, if_true] at h2
    obtain ⟨hb, hpre⟩ := h2
    have hent := hI.loc_base q hinit k v hb
    refine ⟨?_, fun j hj w hw => ?_⟩
    · unfold candOf; simp [hent, ← he₀, hI.base_elog _ _ _ _ hb]
    · unfold candOf at hw
      split_ifs at hw with hsome
      rw [← he₀] at hw
      rcases hbj : st.base (Pa.home q) e₀ j with _ | w'
      · have := hI.elog_above _ _ _ _ hw hbj k hj.le
        rw [hb] at this; cases this
      · have := hI.base_elog _ _ _ _ hbj
        rw [hw] at this
        cases this
        exact hpre j hj w hbj

end Podc.ReconfigurableCommit
