import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/LockStep/Basic.lean (append to the
-- existing file; `decides_iff_of_hist` needs `take_hist`, which then moves from `Parallel.lean`)

/-!
# Lock-step runs: congruence of honest histories, padding, decisions from finite histories

Additions to `Cslib/Computability/Distributed/Byzantine/LockStep/Basic.lean`.

* `hist_honest_congr`: the histories of the honest parties only depend on the honest inputs, the
  omissions between honest parties and the messages of Byzantine parties to honest neighbours.
* `padScenario G alg s Y`: declare the parties of `Y` Byzantine, but let them send exactly what they
  send in `s`. The run is unchanged (`hist_padScenario`, `status_padScenario`,
  `decides_padScenario`) and omissions of the padded parties disappear (`reliable_padScenario`).
  Used to reach an exact number of faults, or to turn omission faults into Byzantine ones.
* `decides_iff_of_hist`: a party that has decided within `k` rounds of `s₁` and has the same input
  and the same history after `k` rounds in `s₂` makes the same (first) decision in `s₂`.
-/

namespace Cslib.Byzantine.LockStep

variable {P I M O : Type*} (G : SimpleGraph P) (alg : Protocol P I M O)

/-! ### Congruence of honest histories -/

/-- **Congruence of honest histories.** Two scenarios with the same Byzantine parties, the same
honest inputs, the same omissions between honest parties and the same messages from Byzantine
parties to honest neighbours give every honest party the same history. -/
theorem hist_honest_congr {s s' : Scenario P I M} (hbyz : s.byz = s'.byz)
    (hin : ∀ p ∉ s.byz, s.input p = s'.input p)
    (hdrop : ∀ r p q, p ∉ s.byz → q ∉ s.byz → G.Adj p q → (s.drop r p q ↔ s'.drop r p q))
    (hadv : ∀ r b q, b ∈ s.byz → q ∉ s.byz → G.Adj b q → s.adv r b q = s'.adv r b q) :
    ∀ r, ∀ p ∉ s.byz, hist G alg s r p = hist G alg s' r p := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro q hq
    rw [hist_succ, hist_succ, ih q hq]
    congr 1
    refine congrArg (fun f => [f]) (funext fun p => ?_)
    unfold deliver
    by_cases hadj : G.Adj p q
    · by_cases hp : p ∈ s.byz
      · simp [hadj, hp, ← hbyz, hadv r p q hp hq hadj]
      · have hd := hdrop r p q hp hq hadj
        by_cases h : s.drop r p q
        · simp [hadj, hp, ← hbyz, h, hd.1 h]
        · simp [hadj, hp, ← hbyz, h, mt hd.2 h, hin p hp, ih p hp]
    · simp [hadj]

/-! ### Padding: Byzantine parties that behave as in a given run -/

section Pad

open Classical in
/-- Declare the parties of `Y` Byzantine, but let them send exactly the messages they send as
(honest or Byzantine) parties in `s`. The run is unchanged (`hist_padScenario`). -/
noncomputable def padScenario (s : Scenario P I M) (Y : Set P) : Scenario P I M where
  byz := s.byz ∪ Y
  input := s.input
  adv r p q := if p ∈ s.byz then s.adv r p q
    else if s.drop r p q then none else alg.send p (s.input p) (hist G alg s r p) q
  drop r p q := s.drop r p q ∧ p ∉ Y

/-- Padding does not change the run. -/
theorem hist_padScenario (s : Scenario P I M) (Y : Set P) :
    ∀ r, hist G alg (padScenario G alg s Y) r = hist G alg s r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    funext q
    rw [hist_succ, hist_succ, ih]
    congr 2
    funext p
    unfold deliver
    by_cases hp : p ∈ s.byz <;> by_cases hY : p ∈ Y <;> simp [padScenario, hp, hY]
    all_goals split_ifs <;> simp_all

/-- Omissions by the padded parties disappear: they are now Byzantine sends of nothing. -/
theorem reliable_padScenario {s : Scenario P I M} {Y : Set P}
    (h : ∀ r p q, s.drop r p q → p ∈ Y) : (padScenario G alg s Y).Reliable :=
  fun r p q hd => hd.2 (h r p q hd.1)

/-- Padding does not change the decision status. -/
theorem status_padScenario (s : Scenario P I M) (Y : Set P) (r : ℕ) (p : P) :
    status G alg (padScenario G alg s Y) r p = status G alg s r p := by
  simp only [status, hist_padScenario]
  rfl

/-- Padding does not change decisions. -/
theorem decides_padScenario (s : Scenario P I M) (Y : Set P) (p : P) (o : O) :
    Decides G alg (padScenario G alg s Y) p o ↔ Decides G alg s p o := by
  simp only [Decides, status_padScenario]

end Pad

/-! ### Decisions determined by a finite history -/

/-- A party that has decided within `k` rounds of `s₁` and has the same input and the same
history after `k` rounds in `s₂` makes the same (first) decision in `s₂`. -/
theorem decides_iff_of_hist {s₁ s₂ : Scenario P I M} {p : P} {k : ℕ}
    (hx : s₁.input p = s₂.input p) (hh : hist G alg s₁ k p = hist G alg s₂ k p)
    (hdec : ∃ r ≤ k, status G alg s₁ r p ≠ none) (o : O) :
    Decides G alg s₁ p o ↔ Decides G alg s₂ p o := by
  have hst : ∀ r ≤ k, status G alg s₁ r p = status G alg s₂ r p := by
    intro r hr
    simp only [status, hx, ← take_hist G alg s₁ hr p, ← take_hist G alg s₂ hr p, hh]
  obtain ⟨r₀, hr₀, hne⟩ := hdec
  constructor
  · rintro ⟨r, hr, hlt⟩
    have hrr : r ≤ r₀ := by
      by_contra h
      exact hne (hlt r₀ (by omega))
    exact ⟨r, (hst r (by omega)).symm ▸ hr, fun r' hr' => (hst r' (by omega)) ▸ hlt r' hr'⟩
  · rintro ⟨r, hr, hlt⟩
    have hrr : r ≤ r₀ := by
      by_contra h
      exact hne ((hst r₀ hr₀).trans (hlt r₀ (by omega)))
    exact ⟨r, (hst r (by omega)) ▸ hr, fun r' hr' => (hst r' (by omega)).trans (hlt r' hr')⟩

end Cslib.Byzantine.LockStep
