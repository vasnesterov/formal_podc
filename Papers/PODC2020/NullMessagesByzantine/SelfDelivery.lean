import Papers.PODC2020.NullMessagesByzantine.Compose

/-!
# The self-delivery convention is necessary

In SmallCouncil a process that broadcasts `err` must treat itself as having received an `err`
(and similarly for `help!`). If processes do not receive their own broadcasts
(`smallCouncilGen false`), the composed protocol violates agreement for **every** base protocol
`B` that solves binary Byzantine agreement:

`n = 7`, `t = 2`, Council `{0, 1, 2}`, process `1` Byzantine and completely silent, process `6`
has input `0`, all others input `1`. The correct council members `0` and `2` recommend
`MAJ = 1`; the null message of `1` tells `6` "recommendation `0`", so `6` has no unanimous
recommendation, sets `est = 0` and broadcasts `err`. Nobody else sends `err`, so `6` (which does
not count its own `err`) decides `0` at time 3. The others got `6`'s `err`, run `B` with input
`1`; declaring `6` Byzantine as well (same run, 2 faults) shows that `B`'s validity forces them to
decide `1`.
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep

variable {M₂ : Type*} (B : Protocol (Fin 7) Bool M₂ Bool)

/-- The run: process `1` is Byzantine and silent, process `6` has input `false`. -/
def bad : Scenario (Fin 7) Bool (Msg M₂) where
  byz := {1}
  input p := decide (p ≠ 6)
  adv _ _ _ := none


lemma bad_reliable : (bad (M₂ := M₂)).Reliable := fun _ _ _ h => h

lemma bad_lmsg_byz {k r : ℕ} (hk : k < r) (p : Fin 7) (hp : p ≠ 1) :
    lmsg (H false 2 B (bad (M₂ := M₂)) r p) k 1 = none := by
  rw [lmsg_hist false 2 B (bad (M₂ := M₂)) hk, deliver_byz _ _ _ (by simp [bad])
    (by simpa using (Ne.symm hp))]
  rfl

lemma bad_recOf {j : Fin 7} (hj : council 2 j) :
    recOf j ((bad (M₂ := M₂)).input j) (H false 2 B (bad (M₂ := M₂)) 1 j) = true := by
  unfold recOf
  apply maj_eq_of_forall_notMem _ {1, 6} true (by rw [Set.ncard_pair (by decide)]; norm_num)
  intro i hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
  rw [values_honest false 2 B (bad (M₂ := M₂)) bad_reliable (by norm_num) hj (by simp [bad, hi.1])]
  simp [bad, hi.2]

lemma bad_recFrom_honest {p j : Fin 7} (hp : p ≠ 1) (hj : council 2 j) (hj1 : j ≠ 1) :
    recFrom p ((bad (M₂ := M₂)).input p) (H false 2 B (bad (M₂ := M₂)) 2 p) j = true := by
  rw [recFrom_honest false 2 B (bad (M₂ := M₂)) bad_reliable (by norm_num) (by simp [bad, hp]) hj
    (by simp [bad, hj1]), bad_recOf B hj]

lemma bad_recFrom_one {p : Fin 7} (hp : p ≠ 1) :
    recFrom p ((bad (M₂ := M₂)).input p) (H false 2 B (bad (M₂ := M₂)) 2 p) 1 =
      (bad (M₂ := M₂)).input p := by
  unfold recFrom
  rw [ite_eq_right (Ne.symm hp), bad_lmsg_byz B (by norm_num) p hp]
  rfl

lemma bad_unanimous {p : Fin 7} (hp : p ≠ 1) (hp6 : p ≠ 6) :
    Unanimous 2 p ((bad (M₂ := M₂)).input p) (H false 2 B (bad (M₂ := M₂)) 2 p) true := by
  intro j hj
  by_cases hj1 : j = 1
  · subst hj1; rw [bad_recFrom_one B hp]; simp [bad, hp6]
  · exact bad_recFrom_honest B hp hj hj1

lemma bad_not_err {p : Fin 7} (hp : p ≠ 1) (hp6 : p ≠ 6) :
    ¬ Err 2 p ((bad (M₂ := M₂)).input p) (H false 2 B (bad (M₂ := M₂)) 2 p) :=
  fun he => he.1 (bad_unanimous B hp hp6)

lemma bad_err_six : Err 2 6 ((bad (M₂ := M₂)).input 6) (H false 2 B (bad (M₂ := M₂)) 2 6) := by
  constructor
  · intro h
    have := h 1 (by decide)
    rw [bad_recFrom_one B (by decide)] at this
    simp [bad] at this
  · intro h
    have := h 0 (by decide)
    rw [bad_recFrom_honest B (by decide) (by decide) (by decide)] at this
    simp at this

lemma bad_est (p : Fin 7) (hp : p ≠ 1) (hp6 : p ≠ 6) :
    est 2 p ((bad (M₂ := M₂)).input p) (H false 2 B (bad (M₂ := M₂)) 2 p) = true :=
  est_of_unanimous 2 (bad_unanimous B hp hp6)

/-- Process `6` gets no `err` from anybody else. -/
lemma bad_not_gotErr_six :
    ¬ GotErr false 2 6 ((bad (M₂ := M₂)).input 6) (H false 2 B (bad (M₂ := M₂)) 3 6) := by
  rintro (⟨h, -⟩ | ⟨q, hq⟩)
  · simp at h
  · by_cases hq1 : q = 1
    · subst hq1; rw [bad_lmsg_byz B (by norm_num) 6 (by decide)] at hq; simp at hq
    · by_cases hq6 : q = 6
      · subst hq6
        rw [lmsg_hist false 2 B (bad (M₂ := M₂)) (by norm_num)] at hq; simp [deliver] at hq
      · rw [lmsg2_honest false 2 B (bad (M₂ := M₂)) bad_reliable (by norm_num)
          (by simp [bad, hq1]) hq6, ite_eq_right (bad_not_err B hq1 hq6)] at hq
        simp at hq

lemma bad_gotErr {q : Fin 7} (hq6 : q ≠ 6) :
    GotErr false 2 q ((bad (M₂ := M₂)).input q) (H false 2 B (bad (M₂ := M₂)) 3 q) := by
  right
  refine ⟨6, ?_⟩
  rw [lmsg2_honest false 2 B (bad (M₂ := M₂)) bad_reliable (by norm_num) (by simp [bad])
    (Ne.symm hq6), ite_eq_left (bad_err_six B)]
  rfl

lemma bad_participates (q : Fin 7) :
    Participates false 2 q ((bad (M₂ := M₂)).input q) (H false 2 B (bad (M₂ := M₂)) 4 q) := by
  right
  obtain ⟨q', hq'1, hq'6, hq'q⟩ : ∃ q' : Fin 7, q' ≠ 1 ∧ q' ≠ 6 ∧ q' ≠ q := by
    by_cases h0 : q = 0
    · exact ⟨2, by decide, by decide, by rw [h0]; decide⟩
    · exact ⟨0, by decide, by decide, Ne.symm h0⟩
  refine ⟨q', ?_⟩
  rw [lmsg3_honest false 2 B (bad (M₂ := M₂)) bad_reliable (by norm_num) (by simp [bad, hq'1])
    hq'q, ite_eq_left (bad_gotErr B hq'6)]
  rfl

/-- **The literal no-self-delivery reading of Figure 1 is wrong.** For every base protocol `B`
solving binary Byzantine agreement against `2` faults among `7 > 3·2` processes, SmallCouncil
in which a process does not receive its own `err`/`help!` messages violates agreement. -/
theorem not_solves_without_selfDelivery (hB : Solves ⊤ B (atMost 2) BA) :
    ¬ Solves ⊤ (smallCouncilGen false 2 B) (atMost 2) BA := by
  intro hS
  -- the run `(bad (M₂ := M₂))`: `6` decides `false` at time 3
  have h6 : Decides ⊤ (smallCouncilGen false 2 B) (bad (M₂ := M₂)) 6 false := by
    have := decides_of_not_gotErr false 2 B (bad (M₂ := M₂)) (bad_not_gotErr_six B)
    rwa [est_of_err 2 (bad_err_six B)] at this
  -- the padded run: `1` and `6` Byzantine, same run
  let s' := padScenario ⊤ (smallCouncilGen false 2 B) (bad (M₂ := M₂)) {6}
  have hpad : ∀ r, H false 2 B s' r = H false 2 B (bad (M₂ := M₂)) r :=
    hist_padScenario ⊤ (smallCouncilGen false 2 B) (bad (M₂ := M₂)) {6}
  have hbyz' : ∀ q, q ∉ s'.byz ↔ q ≠ 1 ∧ q ≠ 6 := by
    intro q; simp [s', padScenario, bad]; tauto
  have hrel' : s'.Reliable :=
    reliable_padScenario ⊤ (smallCouncilGen false 2 B) (fun _ _ _ h => False.elim h)
  have hall : ∀ q, q ∉ s'.byz → Participates false 2 q (s'.input q) (H false 2 B s' 4 q) := by
    intro q _
    rw [hpad]
    exact bad_participates B q
  have hs' : s'.byz ∈ (atMost 2 : AdvStructure (Fin 7)) := by
    show (s'.byz).ncard ≤ 2
    have : s'.byz = {1, 6} := by
      ext q; simp [s', padScenario, bad]; tauto
    rw [this, Set.ncard_pair (by decide)]
  obtain ⟨-, hval, -⟩ := hB (baseScenario false 2 B s') hs' (baseScenario_reliable false 2 B s')
  have h0B : Decides ⊤ B (baseScenario false 2 B s') 0 true := by
    refine hval true (fun q hq => ?_) 0 (by simp [Scenario.honest, hbyz'])
    have hq' := (hbyz' q).1 hq
    show est 2 q (s'.input q) (H false 2 B s' 2 q) = true
    rw [hpad]
    exact bad_est B q hq'.1 hq'.2
  have h0 : Decides ⊤ (smallCouncilGen false 2 B) (bad (M₂ := M₂)) 0 true := by
    rw [← decides_padScenario ⊤ (smallCouncilGen false 2 B) (bad (M₂ := M₂)) {6}]
    refine (decides_iff_base false 2 B s' hrel' hall ((hbyz' 0).2 ⟨by decide, by decide⟩) ?_
      true).2 h0B
    rw [hpad]; exact bad_gotErr B (by decide)
  obtain ⟨-, -, hagr⟩ := hS (bad (M₂ := M₂)) (by
    show ({1} : Set (Fin 7)).ncard ≤ 2
    simp) bad_reliable
  have := hagr 0 (by simp [Scenario.honest, bad]) 6
    (by simp [Scenario.honest, bad]) true false h0 h6
  simp at this

end Podc.NullMessagesByzantine
