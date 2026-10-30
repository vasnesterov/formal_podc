import Papers.PODC2026.DistinctGathering.Impossibility

/-!
# Conjectures 2 and 3, and three-point configurations

[Frei–Wada, *Distinct Gathering and the Virtue of Self-Consistency*, PODC 2026], §3–§4.

* `conjecture_2_three`: Conjecture 2 (Défago et al.) holds for `n = 3` (this is Theorem 4).
* `conjecture_3_as_stated`: Conjecture 3 *as printed* ("every algorithm that solves Gathering under
  Round-Robin is rapid-gathering") is vacuously true for every `n ≥ 3`, by Theorem 1, so it cannot
  be disproved. The intended conjecture is about *Distinct* Gathering (`Conjecture3Distinct`),
  which holds vacuously for `n = 3` by Theorem 4 (`conjecture_3_distinct_three`).
* `exists_three_point`: an execution from a distinct configuration of `n ≥ 3` robots that
  gathers passes through a configuration with exactly three occupied points (§4.1, before
  Theorem 5), under any centralized scheduler and movement model.
-/

noncomputable section

namespace Podc.DistinctGathering

open Cslib.MobileRobots

variable {n : ℕ}

/-- Definition 5 of [Frei–Wada] (Défago et al., Def. 1): from some distinct configuration, with
some Round-Robin order, the algorithm gathers all robots within `n - 1` activations (here: for some
legal adversary — the weakest reading). -/
def IsRapidGathering (n : ℕ) (A : Algorithm) (frameOK : Frame → Prop) (M : Movement) : Prop :=
  ∃ P₀ : Config n, Function.Injective P₀ ∧ ∃ act, IsRoundRobin act ∧ ∃ adv : Adversary n,
    Legal A act adv P₀ frameOK M ∧ ∃ t ≤ n - 1, Gathered (run A act adv P₀ t)

/-- Conjecture 3 of [Frei–Wada] as printed: every algorithm solving Gathering under Round-Robin is
rapid-gathering. -/
def Conjecture3 (n : ℕ) (frameOK : Frame → Prop) (M : Movement) : Prop :=
  ∀ A, Solves n A IsRoundRobin frameOK M (fun _ => True) → IsRapidGathering n A frameOK M

/-- Conjecture 3 with "Distinct Gathering" (the intended reading). -/
def Conjecture3Distinct (n : ℕ) (frameOK : Frame → Prop) (M : Movement) : Prop :=
  ∀ A, Solves n A IsRoundRobin frameOK M Function.Injective → IsRapidGathering n A frameOK M

/-- Conjecture 3 as printed holds (vacuously) for every `n ≥ 3`, in the default model or with a
consistent unit length, so it cannot be disproved. -/
theorem conjecture_3_as_stated (hn : 3 ≤ n) {frameOK : Frame → Prop}
    (hframe : ∀ a (ha : a ≠ 0), ‖a‖ = 1 → frameOK (Frame.ofCoef a ha)) (M : Movement) :
    Conjecture3 n frameOK M :=
  fun A h => absurd h (theorem_1_general hn A hframe M)

/-- Conjecture 2 of [Frei–Wada] (Défago et al., Conj. 2) for `n = 3`: no algorithm solves
Distinct Gathering under Round-Robin. -/
theorem conjecture_2_three (M : Movement) :
    ∀ A, ¬ Solves 3 A IsRoundRobin (fun _ => True) M Function.Injective :=
  fun A => theorem_4 A M

/-- The intended Conjecture 3 holds (vacuously) for `n = 3`. -/
theorem conjecture_3_distinct_three (M : Movement) :
    Conjecture3Distinct 3 (fun _ => True) M :=
  fun A h => absurd h (theorem_4 A M)

/-! ### Passing through three-point configurations -/

/-- Number of occupied points. -/
def numPoints (P : Config n) : ℕ := (Finset.univ.image P).card

lemma numPoints_step_le (A : Algorithm) (P : Config n) (r : Fin n) (f : Frame) (s : ℝ) :
    numPoints P ≤ numPoints (step A P r f s) + 1 := by
  unfold numPoints
  refine (Finset.card_le_card ?_).trans (Finset.card_insert_le (P r) _)
  intro z hz
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
  by_cases hj : j = r
  · subst hj; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨j, Finset.mem_univ _, step_apply_ne A P f s hj⟩)

lemma numPoints_le_one_of_gathered {P : Config n} (h : Gathered P) : numPoints P ≤ 1 := by
  unfold numPoints
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
  exact h i j

/-- Any execution from a distinct configuration of `n ≥ 3` robots that eventually gathers passes
through a configuration with exactly three occupied points. -/
theorem exists_three_point (hn : 3 ≤ n) (A : Algorithm) (act : ℕ → Fin n) (adv : Adversary n)
    (P₀ : Config n) (hP₀ : Function.Injective P₀) (T : ℕ)
    (hT : Gathered (run A act adv P₀ T)) :
    ∃ t ≤ T, numPoints (run A act adv P₀ t) = 3 := by
  set f : ℕ → ℕ := fun t => numPoints (run A act adv P₀ t)
  have hf : ∀ t, f t ≤ f (t + 1) + 1 := fun t => numPoints_step_le A _ _ _ _
  have h0 : 3 ≤ f 0 := by
    show 3 ≤ (Finset.univ.image P₀).card
    rw [Finset.card_image_of_injective _ hP₀, Finset.card_univ, Fintype.card_fin]; exact hn
  have hex : ∃ t, f t ≤ 3 := ⟨T, (numPoints_le_one_of_gathered hT).trans (by omega)⟩
  set t := Nat.find hex
  have ht : f t ≤ 3 := Nat.find_spec hex
  have htT : t ≤ T := Nat.find_min' hex ((numPoints_le_one_of_gathered hT).trans (by omega))
  refine ⟨t, htT, ?_⟩
  rcases Nat.eq_zero_or_pos t with h | h
  · show f t = 3; rw [h] at ht ⊢; omega
  · obtain ⟨t', ht'⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hlt : ¬ f t' ≤ 3 := Nat.find_min hex (by omega)
    have := hf t'
    show f t = 3
    rw [ht'] at ht ⊢
    omega

end Podc.DistinctGathering

end
