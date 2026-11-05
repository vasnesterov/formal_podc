import Papers.PODC2012.LeaderElectionSpaceLB.Basic

-- CSLib candidate: nondeterministic read/write shared memory + covering toolkit

/-!
# Erasing the steps of processes that nobody in `Q` has seen; Claim 5.2

If no process of `Q` sees a process outside `Q` during an execution `E`, then deleting all steps
of processes outside `Q` from `E` yields an execution in which every process of `Q` goes through
exactly the same local states (`erase`). This is the indistinguishability argument behind
Claim 5.2 of the paper. Note that the paper's wording "configurations `C(E)` and `C(D)` are
indistinguishable to all processes in `Q`" is too strong under its own definition of
indistinguishability (which includes the register values: registers last written outside `Q`
differ); what is true and what is used is that the processes of `Q` have the same states and
agree on all registers last written by `Q` (or never written).
-/

namespace Podc.LeaderElectionSpaceLB

set_option linter.unusedSectionVars false

open Classical

variable {P Reg V L : Type*} [DecidableEq P] [DecidableEq Reg]

namespace Alg

variable (A : Alg P Reg V L)

/-- `D` agrees with `C` for the processes of `Q`: same local states of `Q`, and the same value
and last writer of every register that in `C` is unwritten or last written by `Q`. -/
def AgreeOn (Q : Set P) (C D : Config P Reg V L) : Prop :=
  (∀ p ∈ Q, D.loc p = C.loc p) ∧
    ∀ r, (∀ p, C.wr r = some p → p ∈ Q) → D.val r = C.val r ∧ D.wr r = C.wr r

lemma agreeOn_refl (Q : Set P) (C : Config P Reg V L) : AgreeOn Q C C :=
  ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- The steps of processes outside `Q`, removed from `es`. -/
noncomputable def restrict (Q : Set P) (es : List (P × L)) : List (P × L) :=
  es.filter (fun e => decide (e.1 ∈ Q))

lemma restrict_append (Q : Set P) (es fs : List (P × L)) :
    restrict Q (es ++ fs) = restrict Q es ++ restrict Q fs := by simp [restrict]

lemma mem_restrict {Q : Set P} {es : List (P × L)} {e : P × L} (h : e ∈ restrict Q es) :
    e ∈ es ∧ e.1 ∈ Q := by
  unfold restrict at h; simpa using h

/-- **Erasure lemma.** If during `es` from `C` no process of `Q` sees a process outside `Q`,
and `D` agrees with `C` on `Q`, then the `Q`-steps of `es` form an execution from `D` after
which the agreement persists. -/
theorem erase (Q : Set P) :
    ∀ (es : List (P × L)) (C D : Config P Reg V L), A.Valid C es → AgreeOn Q C D →
      (∀ p q, A.SeesIn C es p q → p ∈ Q → q ∈ Q) →
      A.Valid D (restrict Q es) ∧ AgreeOn Q (A.run C es) (A.run D (restrict Q es)) := by
  intro es
  induction es with
  | nil => intro C D _ h _; exact ⟨trivial, h⟩
  | cons e es ih =>
    intro C D hv hag hs
    obtain ⟨he, hv⟩ := hv
    have hs' : ∀ p q, A.SeesIn (A.apply C e) es p q → p ∈ Q → q ∈ Q :=
      fun p q h hp => hs p q (Or.inr h) hp
    by_cases hq : e.1 ∈ Q
    · have hres : restrict Q (e :: es) = e :: restrict Q es := by
        simp [restrict, hq]
      rw [hres]
      have hloc : D.loc e.1 = C.loc e.1 := hag.1 _ hq
      -- the step is enabled in `D`
      have hen : A.Enabled D e := by
        unfold Enabled at he ⊢
        rw [hloc]
        rcases hact : A.act (C.loc e.1) with r | ⟨r, v⟩ | b <;> rw [hact] at he
        · have hr : ∀ p, C.wr r = some p → p ∈ Q := fun p hp =>
            hs e.1 p (Or.inl ⟨rfl, r, hact, hp⟩) hq
          dsimp only at he ⊢
          rw [(hag.2 r hr).1]; exact he
        · exact he
        · exact he
      -- agreement after the step
      have hag' : AgreeOn Q (A.apply C e) (A.apply D e) := by
        refine ⟨fun p hp => ?_, fun r hr => ?_⟩
        · rw [A.apply_loc, A.apply_loc]
          by_cases hpe : p = e.1
          · subst hpe; simp
          · simp [Function.update_of_ne hpe, hag.1 p hp]
        · rcases hact : A.act (C.loc e.1) with r' | ⟨r', v⟩ | b
          · have hD : ∀ r v, A.act (D.loc e.1) ≠ .write r v := by rw [hloc, hact]; simp
            have hC : ∀ r v, A.act (C.loc e.1) ≠ .write r v := by rw [hact]; simp
            obtain ⟨c1, c2⟩ := A.apply_mem_of_not_write C e hC
            obtain ⟨d1, d2⟩ := A.apply_mem_of_not_write D e hD
            rw [c1, c2, d1, d2]
            rw [c2] at hr
            exact hag.2 r hr
          · obtain ⟨c1, c2⟩ := A.apply_mem_of_write C e hact
            obtain ⟨d1, d2⟩ := A.apply_mem_of_write D e (by rw [hloc]; exact hact)
            rw [c1, c2, d1, d2]
            by_cases hrr : r = r'
            · subst hrr; simp
            · simp only [Function.update_of_ne hrr]
              rw [c2, Function.update_of_ne hrr] at hr
              exact hag.2 r hr
          · have hD : ∀ r v, A.act (D.loc e.1) ≠ .write r v := by rw [hloc, hact]; simp
            have hC : ∀ r v, A.act (C.loc e.1) ≠ .write r v := by rw [hact]; simp
            obtain ⟨c1, c2⟩ := A.apply_mem_of_not_write C e hC
            obtain ⟨d1, d2⟩ := A.apply_mem_of_not_write D e hD
            rw [c1, c2, d1, d2]
            rw [c2] at hr
            exact hag.2 r hr
      obtain ⟨h1, h2⟩ := ih _ _ hv hag' hs'
      exact ⟨⟨hen, h1⟩, h2⟩
    · have hres : restrict Q (e :: es) = restrict Q es := by
        simp [restrict, hq]
      rw [hres]
      have hag' : AgreeOn Q (A.apply C e) D := by
        refine ⟨fun p hp => ?_, fun r hr => ?_⟩
        · rw [A.apply_loc_of_ne C e (fun h => hq (h ▸ hp))]; exact hag.1 p hp
        · by_cases hw : ∃ v, A.act (C.loc e.1) = .write r v
          · obtain ⟨v, hv⟩ := hw
            have := (A.apply_mem_of_write C e hv).2
            exact absurd (hr e.1 (by rw [this]; simp)) hq
          · push Not at hw
            obtain ⟨a1, a2⟩ := A.apply_mem_other C e r hw
            rw [a1, a2]
            rw [a2] at hr
            exact hag.2 r hr
      exact ih _ _ hv hag' hs'

/-- Erasure from an initial configuration: if no process of `Q` sees a process outside `Q`
during `es`, then `restrict Q es` is an execution from the same initial configuration that
leaves every process of `Q` in the same local state. -/
theorem erase_init {C₀ : Config P Reg V L} {es : List (P × L)} (hv : A.Valid C₀ es)
    (Q : Set P) (hs : ∀ p q, A.SeesIn C₀ es p q → p ∈ Q → q ∈ Q) :
    A.Valid C₀ (restrict Q es) ∧
      ∀ p ∈ Q, (A.run C₀ (restrict Q es)).loc p = (A.run C₀ es).loc p := by
  obtain ⟨h1, h2⟩ := A.erase Q es C₀ C₀ hv (agreeOn_refl Q C₀) hs
  exact ⟨h1, h2.1⟩

/-- **Claim 5.2** (general form). Let `E` be an execution from an initial configuration and
`Q` a nonempty set of processes, all of which have returned at the end of `E`, such that no
process of `Q` sees a process outside `Q` during `E` (e.g. `Q` is closed w.r.t. `≡_E`). Then
exactly one process of `Q` has won. -/
theorem claim_5_2 (hLE : A.IsLeaderElection) {C₀ : Config P Reg V L} (h0 : A.IsInit C₀)
    {es : List (P × L)} (hv : A.Valid C₀ es) (Q : Set P) (hQ : Q.Nonempty)
    (hs : ∀ p q, A.SeesIn C₀ es p q → p ∈ Q → q ∈ Q)
    (hfin : ∀ p ∈ Q, A.Finished (A.run C₀ es) p) :
    (∃ p ∈ Q, A.Won (A.run C₀ es) p) ∧
      ∀ p ∈ Q, ∀ q ∈ Q, A.Won (A.run C₀ es) p → A.Won (A.run C₀ es) q → p = q := by
  obtain ⟨hv', hloc⟩ := A.erase_init hv Q hs
  have hS : ∀ e ∈ restrict Q es, e.1 ∈ Q := fun e he => (mem_restrict he).2
  obtain ⟨-, hex⟩ := hLE C₀ _ h0 hv' Q hS
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, hw⟩ := hex hQ (fun p hp => by
      unfold Finished; rw [hloc p hp]; exact hfin p hp)
    exact ⟨p, hp, by unfold Won at hw ⊢; rwa [hloc p hp] at hw⟩
  · intro p hp q hq hwp hwq
    exact (hLE C₀ es h0 hv Set.univ (fun _ _ => trivial)).1 p trivial q trivial hwp hwq

/-- **Claim 5.2** as stated in the paper: if the set `Q` of processes that have returned at the
end of `E` is nonempty and closed w.r.t. `≡_E`, then exactly one process of `Q` wins. -/
theorem claim_5_2_paper (hLE : A.IsLeaderElection) {C₀ : Config P Reg V L} (h0 : A.IsInit C₀)
    {es : List (P × L)} (hv : A.Valid C₀ es) (hQ : {p | A.Finished (A.run C₀ es) p}.Nonempty)
    (hcl : A.Closed C₀ es {p | A.Finished (A.run C₀ es) p}) :
    ∃! p, A.Finished (A.run C₀ es) p ∧ A.Won (A.run C₀ es) p := by
  have hcl' := (A.closed_iff _ _ _).1 hcl
  obtain ⟨⟨p, hp, hw⟩, huniq⟩ := A.claim_5_2 hLE h0 hv _ hQ
    (fun p q h hp => (hcl' p q h).1 hp) (fun p hp => hp)
  exact ⟨p, ⟨hp, hw⟩, fun q hq => huniq q hq.1 p hp hq.2 hw⟩

end Alg

end Podc.LeaderElectionSpaceLB
