import Papers.PODC2020.NullMessagesByzantine.Layer

/-!
# Decisions of the composed protocol

* `decides_of_not_gotErr`: a process that got no `err` decides its estimate (at time 3);
* `histR_hist_base`: if all correct processes take part in the base protocol (they got a
  `help!`), then from round 4 on the base-protocol components of their histories form a run of
  `B` in the scenario `baseScenario` (inputs = estimates, Byzantine messages = the `M₂` parts of
  the Byzantine messages from round 4 on);
* `decides_iff_base`: then a process that got an `err` decides what it decides in that run of `B`.
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep

variable {n : ℕ} {M₂ : Type*} (sr : Bool) (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool)
  (s : Scenario (Fin n) Bool (Msg M₂))

/-- The run of the base protocol started at time 4 (lines 13–15): inputs are the estimates. -/
noncomputable def baseScenario : Scenario (Fin n) Bool M₂ where
  byz := s.byz
  input p := est t p (s.input p) (H sr t B s 2 p)
  adv r b q := (s.adv (4 + r) b q).bind Sum.getRight?

@[simp] lemma baseScenario_byz : (baseScenario sr t B s).byz = s.byz := rfl
@[simp] lemma baseScenario_honest : (baseScenario sr t B s).honest = s.honest := rfl
lemma baseScenario_reliable : (baseScenario sr t B s).Reliable := fun _ _ _ h => h

open Classical in
/-- The status of `p` after `r ≥ 3` rounds. -/
lemma status_eq {r : ℕ} (hr : 3 ≤ r) (p : Fin n) :
    status ⊤ (smallCouncilGen sr t B) s r p =
      if ¬ GotErr sr t p (s.input p) (H sr t B s 3 p) then
        some (est t p (s.input p) (H sr t B s 2 p))
      else if r < 4 then none
      else if Participates sr t p (s.input p) (H sr t B s 4 p) then
        B.decide p (est t p (s.input p) (H sr t B s 2 p)) (histR ((H sr t B s r p).drop 4))
      else none := by
  have hl : (hist ⊤ (smallCouncilGen sr t B) s r p).length = r := length_hist _ _ _ _ _
  unfold status
  rw [decide_eq, hl, ite_eq_right (by omega : ¬ r < 3)]
  rw [gotErr_congr sr (lEq_hist sr t B s (k := 2) (r := r) (r' := 3) (by omega) (by omega) p),
    est_congr (lEq_hist sr t B s (k := 1) (r := r) (r' := 2) (by omega) (by omega) p)]
  by_cases h4 : r < 4
  · simp [h4]
  · rw [participates_congr sr
      (lEq_hist sr t B s (k := 3) (r := r) (r' := 4) (by omega) (by omega) p)]

lemma status_lt {r : ℕ} (hr : r < 3) (p : Fin n) :
    status ⊤ (smallCouncilGen sr t B) s r p = none := by
  have hl : (hist ⊤ (smallCouncilGen sr t B) s r p).length = r := length_hist _ _ _ _ _
  unfold status
  rw [decide_eq, hl, ite_eq_left hr]

/-- Line 11: a process that got no `err` decides its estimate at time 3. -/
lemma decides_of_not_gotErr {p : Fin n} (hp : ¬ GotErr sr t p (s.input p) (H sr t B s 3 p)) :
    Decides ⊤ (smallCouncilGen sr t B) s p (est t p (s.input p) (H sr t B s 2 p)) := by
  refine ⟨3, ?_, fun r hr => status_lt sr t B s hr p⟩
  rw [status_eq sr t B s le_rfl, ite_eq_left hp]

/-- Decisions happen at time 3 exactly when no `err` was received. -/
lemma status_three {p : Fin n} (hp : ¬ GotErr sr t p (s.input p) (H sr t B s 3 p)) :
    status ⊤ (smallCouncilGen sr t B) s 3 p = some (est t p (s.input p) (H sr t B s 2 p)) := by
  rw [status_eq sr t B s le_rfl, ite_eq_left hp]

/-- **Projection onto the base protocol.** If every correct process takes part in the base
protocol, the `M₂` components of their histories from round 4 on are their histories in the run
of `B` in `baseScenario`. -/
lemma histR_hist_base (hrel : s.Reliable)
    (hall : ∀ q, q ∉ s.byz → Participates sr t q (s.input q) (H sr t B s 4 q)) :
    ∀ r p, p ∉ s.byz →
      histR ((H sr t B s (4 + r) p).drop 4) = hist ⊤ B (baseScenario sr t B s) r p := by
  intro r
  induction r with
  | zero => intro p _; simp [histR]
  | succ r ih =>
    intro p hp
    show histR ((hist ⊤ (smallCouncilGen sr t B) s (4 + r + 1) p).drop 4) = _
    rw [hist_succ, hist_succ,
      List.drop_append_of_le_length (by simp), histR_append, ih p hp]
    congr 1
    simp only [histR, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext q
    simp only [inboxR]
    by_cases hqp : q = p
    · subst hqp; simp [deliver]
    · have hadj : (⊤ : SimpleGraph (Fin n)).Adj q p := by simpa using hqp
      by_cases hq : q ∈ s.byz
      · rw [deliver_byz _ _ _ hq hadj, deliver_byz _ _ _ (by simpa using hq) hadj]
        rfl
      · rw [deliver_honest _ _ _ hrel hq hadj,
          deliver_honest _ _ _ (baseScenario_reliable sr t B s) (by simpa using hq) hadj]
        have hl : 4 ≤ (H sr t B s (4 + r) q).length := by simp
        rw [send_round4 _ _ _ hl,
          ite_eq_left ((participates_congr sr
            (lEq_hist sr t B s (k := 3) (r := 4 + r) (r' := 4) (by omega) (by omega) q)
            _ _).2 (hall q hq)),
          est_congr (lEq_hist sr t B s (k := 1) (r := 4 + r) (r' := 2) (by omega) (by omega) q),
          ih q hq]
        simp only [baseScenario]
        generalize B.send _ _ _ _ = o
        cases o <;> rfl

/-- The status of a process that got an `err`, from round 4 on, is its status in the base run. -/
lemma status_base (hrel : s.Reliable)
    (hall : ∀ q, q ∉ s.byz → Participates sr t q (s.input q) (H sr t B s 4 q)) {p : Fin n}
    (hp : p ∉ s.byz) (he : GotErr sr t p (s.input p) (H sr t B s 3 p)) (r : ℕ) :
    status ⊤ (smallCouncilGen sr t B) s (4 + r) p =
      status ⊤ B (baseScenario sr t B s) r p := by
  rw [status_eq sr t B s (by omega), ite_eq_right (not_not.2 he), ite_eq_right (by omega),
    ite_eq_left (hall p hp), histR_hist_base sr t B s hrel hall r p hp]
  rfl

/-- **Decision correspondence**: a correct process that got an `err` decides what it decides in
the base run (when all correct processes take part in it). -/
lemma decides_iff_base (hrel : s.Reliable)
    (hall : ∀ q, q ∉ s.byz → Participates sr t q (s.input q) (H sr t B s 4 q)) {p : Fin n}
    (hp : p ∉ s.byz) (he : GotErr sr t p (s.input p) (H sr t B s 3 p)) (o : Bool) :
    Decides ⊤ (smallCouncilGen sr t B) s p o ↔ Decides ⊤ B (baseScenario sr t B s) p o := by
  have hlt : ∀ r < 4, status ⊤ (smallCouncilGen sr t B) s r p = none := by
    intro r hr
    by_cases h3 : r < 3
    · exact status_lt sr t B s h3 p
    · rw [status_eq sr t B s (by omega), ite_eq_right (not_not.2 he), ite_eq_left hr]
  constructor
  · rintro ⟨r, hr, hmin⟩
    have h4 : 4 ≤ r := by
      by_contra h
      rw [hlt r (by omega)] at hr
      exact absurd hr (by simp)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h4
    refine ⟨k, by rwa [← status_base sr t B s hrel hall hp he], fun r' hr' => ?_⟩
    rw [← status_base sr t B s hrel hall hp he]
    exact hmin _ (by omega)
  · rintro ⟨k, hk, hmin⟩
    refine ⟨4 + k, by rwa [status_base sr t B s hrel hall hp he], fun r' hr' => ?_⟩
    by_cases h : r' < 4
    · exact hlt r' h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
      rw [status_base sr t B s hrel hall hp he]
      exact hmin j (by omega)

end Podc.NullMessagesByzantine
