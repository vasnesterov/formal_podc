import Papers.PODC2012.IteratedSnapshotFD.Termination

/-!
# Non-vacuity of the consensus model

* `Upd.exists`: lines 7–18 of Figure 5 can always be executed.
* `Exec.ofSchedule`: every IIS schedule, every input vector and every sequence of leader outputs
  give an execution of Figure 5.
* `full`, `omegaStar_full`, `theorem5_full`: in the failure-free synchronous schedule with a
  constant leader, `Ω*` holds and Theorem 5 applies, so every process decides.
-/

set_option linter.unusedSectionVars false

namespace Podc.IteratedSnapshotFD

variable {P V : Type} [DecidableEq P]

open Classical in
/-- Lines 7–18 of Figure 5 can always be executed. -/
theorem Upd.exists (w : P → Loc P V) (vw : Finset P) (i : P) : ∃ t, Upd w vw i t := by
  by_cases h0 : (w i).dec = true
  · exact ⟨_, .done h0⟩
  simp only [Bool.not_eq_true] at h0
  by_cases hd : ∃ j ∈ vw, (w j).dec = true
  · obtain ⟨j, hj, hd⟩ := hd; exact ⟨_, .seeDec h0 j hj hd⟩
  push Not at hd
  have hnd : ∀ j ∈ vw, (w j).dec = false := fun j hj => by simpa using hd j hj
  by_cases hu : ∃ v, Unanim w vw v
  · obtain ⟨v, hv⟩ := hu; exact ⟨_, .unanim h0 hnd v hv⟩
  push Not at hu
  by_cases hl : ∃ l : Option P, ∀ j ∈ vw, (w j).rl = l
  · obtain ⟨l, hl⟩ := hl
    by_cases hc : ∃ v, Cand w vw l v
    · obtain ⟨v, hv⟩ := hc; exact ⟨_, .adopt h0 hnd hu l hl v hv⟩
    · push Not at hc; exact ⟨_, .keep h0 hnd hu l hl hc⟩
  push Not at hl
  have hnl : ∀ l : Option P, ¬ ∀ j ∈ vw, (w j).rl = l := fun l h => by
    obtain ⟨j, hj, hne⟩ := hl l; exact hne (h j hj)
  by_cases hv : ∃ j ∈ vw, (w j).vls = true
  · obtain ⟨j, hj, hv⟩ := hv; exact ⟨_, .mixAdopt h0 hnd hu hnl j hj hv⟩
  · push Not at hv
    exact ⟨_, .mixKeep h0 hnd hu hnl fun j hj => by simpa using hv j hj⟩

/-- States of an execution built by resolving every choice arbitrarily. -/
noncomputable def stOf (σ : Schedule P) (input : P → V) (ld : ℕ → P → P) : ℕ → P → Loc P V
  | 0 => fun i => Loc.init (input i)
  | r + 1 => fun i =>
    open Classical in
    if i ∈ (σ.rd r).part then
      (Upd.exists (fun j => wr (stOf σ input ld r j) (ld r j)) ((σ.rd r).view i) i).choose
    else stOf σ input ld r i

/-- Every schedule, input vector and sequence of leader outputs gives an execution. -/
noncomputable def Exec.ofSchedule (σ : Schedule P) (input : P → V) (ld : ℕ → P → P) :
    Exec σ input where
  ld := ld
  st := stOf σ input ld
  init _ := rfl
  step r i hi := by
    simp only [stOf, hi, ite_true]
    exact (Upd.exists _ _ _).choose_spec
  frozen r i hi := by simp [stOf, hi]

/-- The failure-free synchronous schedule: everybody sees everybody in every round. -/
def full (P : Type) [Fintype P] : Schedule P where
  rd _ :=
    { part := Finset.univ
      view := fun _ => Finset.univ
      view_sub := fun _ _ => le_rfl
      self_mem := fun _ _ => Finset.mem_univ _
      contain := fun _ _ _ _ => Or.inl le_rfl
      immed := fun _ _ _ _ _ => le_rfl }
  mono _ := le_rfl

theorem full_SC [Fintype P] (l : P) : l ∈ (full P).SC :=
  ⟨0, (full P).mem_SCk_zero.2 fun R =>
    ⟨R, le_rfl, Finset.mem_univ _, fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩⟩

/-- A constant leader satisfies `Ω*` in the failure-free synchronous schedule. -/
theorem omegaStar_full [Fintype P] (l : P) : OmegaStar (full P) (fun _ _ => l) :=
  ⟨l, full_SC l, 0, fun _ _ _ _ => rfl⟩

/-- Theorem 5 is not vacuous: in the failure-free synchronous schedule with a constant leader,
any execution of Figure 5 satisfies validity, agreement, and every process decides. -/
theorem theorem5_full [Fintype P] (input : P → V) (l : P) :
    let E := Exec.ofSchedule (full P) input (fun _ _ => l)
    (∀ i v, E.Decides i v → ∃ j, v = input j) ∧
    (∀ i j v v', E.Decides i v → E.Decides j v' → v = v') ∧
    (∀ i, ∃ v, E.Decides i v) := by
  intro E
  obtain ⟨h1, h2, h3⟩ := theorem5 E (omegaStar_full l)
  exact ⟨h1, h2, fun i => h3 i fun _ => Finset.mem_univ _⟩

end Podc.IteratedSnapshotFD
