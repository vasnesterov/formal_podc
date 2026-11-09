import Papers.PODC2020.SelfStabHighDynamics.Model
import Papers.PODC2021.StabilizingLEDynamic.Classes

/-!
# The classes `TC_B(Δ) ⊆ TC_Q(Δ) ⊆ TC_R` and sequential composition (Property 1)
-/

namespace Podc.SelfStabHighDynamics

open Cslib.HeardOf
open Cslib.DynNet (Journey tdist tdist_le_iff)
open StabilizingLEDynamic (DG IsDG J JssB JssQ Jss Conn Timeliness Kind)

variable {ι : Type*}

theorem JssB_subset_JssQ (Δ : ℕ) (V : Finset ι) : JssB Δ V ⊆ JssQ Δ V :=
  fun _ ⟨hdg, h⟩ => ⟨hdg, fun p hp q hq => (h p hp q hq).mono (by decide)⟩

theorem JssQ_subset_Jss (Δ : ℕ) (V : Finset ι) : JssQ Δ V ⊆ Jss V :=
  fun _ ⟨hdg, h⟩ => ⟨hdg, fun p hp q hq =>
    (StabilizingLEDynamic.Conn.mono (τ' := .recur) (h p hp q hq) (by decide) : Conn _ Δ _ p q)⟩

theorem JssB_subset_Jss (Δ : ℕ) (V : Finset ι) : JssB Δ V ⊆ Jss V :=
  (JssB_subset_JssQ Δ V).trans (JssQ_subset_Jss Δ V)

/-- The complete digraph on `X`. -/
def K (X : Finset ι) : Graph ι := fun p q => p ∈ X ∧ q ∈ X ∧ p ≠ q

/-- The graph without edges. -/
def E0 : Graph ι := fun _ _ => False

/-- A dynamic graph on `V` whose snapshot is complete on `V` at least once in every window of
`Δ` consecutive rounds is in `TC_B(Δ)`. -/
theorem mem_JssB_of_complete {V : Finset ι} {G : DG ι} {Δ : ℕ} (hG : IsDG V G)
    (hK : ∀ i, ∃ j, i ≤ j ∧ j < i + Δ ∧ ∀ p ∈ V, ∀ q ∈ V, p ≠ q → G j p q) : G ∈ JssB Δ V := by
  refine ⟨hG, fun p hp q hq i => tdist_le_iff.mpr ?_⟩
  obtain ⟨j, hij, hjΔ, hj⟩ := hK i
  by_cases hpq : p = q
  · subst hpq; exact Journey.self (by omega)
  · exact ((Journey.single (hj p hp q hq hpq)).mono_left hij).mono_right (by omega)

theorem isDG_K (V : Finset ι) : IsDG V (fun _ => K V) := fun _ _ _ h => h

/-- The static complete graph is in `TC_B(Δ)` for `Δ ≥ 1`. -/
theorem K_mem_JssB {V : Finset ι} {Δ : ℕ} (hΔ : 1 ≤ Δ) : (fun _ => K V) ∈ JssB Δ V :=
  mem_JssB_of_complete (isDG_K V) fun i => ⟨i, le_rfl, by omega, fun _ hp _ hq h => ⟨hp, hq, h⟩⟩

theorem tdist_splice_le {P G : DG ι} {T j Δ : ℕ} {p q : ι} (h : tdist G j p q ≤ Δ) :
    tdist (splice P T G) (T + j) p q ≤ Δ := by
  have hG : (fun k => splice P T G (T + k)) = G := by funext k; simp [splice]
  rw [tdist_le_iff] at h ⊢
  rw [Nat.add_assoc]
  exact Cslib.DynNet.journey_shift_iff.mp (by rw [hG]; exact h)

-- CSLib candidate
/-- **Property 1** (sequential composition): a finite prefix of graphs on `V` followed by a graph
of `TC_Q(Δ)` gives a graph of `TC_Q(Δ)`. -/
theorem splice_mem_JssQ {V : Finset ι} {Δ : ℕ} {P G : DG ι} (hP : IsDG V P) (T : ℕ)
    (hG : G ∈ JssQ Δ V) : splice P T G ∈ JssQ Δ V := by
  obtain ⟨hdg, h⟩ := hG
  refine ⟨fun t a b hab => ?_, fun p hp q hq i => ?_⟩
  · simp only [splice] at hab; split_ifs at hab
    · exact hP _ _ _ hab
    · exact hdg _ _ _ hab
  · obtain ⟨j, hji, hj⟩ := h p hp q hq i
    exact ⟨T + j, by omega, tdist_splice_le hj⟩

end Podc.SelfStabHighDynamics
