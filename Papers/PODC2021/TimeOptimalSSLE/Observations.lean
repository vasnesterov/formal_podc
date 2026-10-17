import Papers.PODC2021.TimeOptimalSSLE.SilentSSR
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Observations 2.5 and 2.6

* **Observation 2.5**: a silent SSLE protocol for `n = 3` whose states cannot be assigned ranks
  so that it solves SSR. States `l, f₀, …, f₄` (`Option (Fin 5)`, `none = l`); a pair of equal
  states, or two followers `fᵢ, fⱼ` that are not adjacent modulo `5`, moves to an arbitrary pair
  of states (`δ = univ`, the support of the uniform distribution); all other pairs are null.
  `obs25_solvesSSLE`, `obs25_silent` and `obs25_not_solvesSSR`.
* **Observation 2.6** (deterministic core): in a silent configuration `C` with a unique leader
  `ℓ`, copying the leader state to another agent `u` gives a configuration with two leaders in
  which *every* interaction except the one between `ℓ` and `u` is null
  (`obs26_null_of_ne`). The quantitative form "for any `α > 0`, probability `≥ ½ n^{-3α}` to need
  `≥ α n ln n` time" fails for `n = 2`: `Silent-n-state-SSR` with two agents is correct after one
  interaction from every configuration under every schedule (`obs26_n2_counterexample`), i.e.
  within parallel time `1/2 < α · n ln n` for `α = 1`.
-/

open Cslib.PopulationProtocol Finset

namespace TimeOptimalSSLE

/-! ### Observation 2.5 -/

namespace Obs25

/-- Two followers `fᵢ, fⱼ` are adjacent modulo `5`. -/
def adj (i j : Fin 5) : Prop := j = i + 1 ∨ i = j + 1

instance (i j : Fin 5) : Decidable (adj i j) := by unfold adj; infer_instance

/-- The pair of states is *active* (has a non-null, uniformly random transition). -/
def active : Option (Fin 5) → Option (Fin 5) → Prop
  | none, none => True
  | some i, some j => ¬ adj i j
  | _, _ => False

instance (x y : Option (Fin 5)) : Decidable (active x y) := by
  cases x <;> cases y <;> unfold active <;> infer_instance

open Classical in
/-- The protocol of Observation 2.5 (support of the transition distributions). -/
noncomputable def P : NProtocol (Option (Fin 5)) where
  δ x y := if active x y then Set.univ else {(x, y)}

/-- The leader state `l`. -/
def leader (x : Option (Fin 5)) : Bool := x.isNone

lemma silent_iff (C : Config (Fin 3) (Option (Fin 5))) :
    P.Silent C ↔ ∀ a b, a ≠ b → ¬ active (C a) (C b) := by
  constructor
  · intro h a b hab hact
    have := h a b hab (if C a = none then (some 0, some 0) else (none, none)) (by
      simp [P, hact])
    split_ifs at this with hC <;> simp_all
  · intro h a b hab o ho
    simp only [P, h a b hab, ite_false, Set.mem_singleton_iff] at ho
    exact ho

/-- Silent configurations of three agents have exactly one leader. -/
lemma silent_one_leader : ∀ C : Fin 3 → Option (Fin 5),
    (∀ a b, a ≠ b → ¬ active (C a) (C b)) →
      (univ.filter fun a => leader (C a) = true).card = 1 := by
  decide +kernel

/-- From every configuration one interaction reaches a silent configuration. -/
lemma exists_silent_step : ∀ C : Fin 3 → Option (Fin 5), (∃ a b, a ≠ b ∧ active (C a) (C b)) →
    ∃ a b, a ≠ b ∧ active (C a) (C b) ∧ ∃ o : Option (Fin 5) × Option (Fin 5),
      ∀ x y, x ≠ y → ¬ active (NProtocol.upd C a b o x) (NProtocol.upd C a b o y) := by
  decide +kernel

/-- **Observation 2.5 (silence).** From every configuration of three agents a silent
configuration is reachable (in at most one interaction). -/
theorem obs25_silent (C : Config (Fin 3) (Option (Fin 5))) :
    ∃ D, P.Reachable C D ∧ P.Silent D := by
  by_cases h : ∃ a b, a ≠ b ∧ active (C a) (C b)
  · obtain ⟨a, b, hab, hact, o, ho⟩ := exists_silent_step C h
    refine ⟨NProtocol.upd C a b o, Relation.ReflTransGen.single
      ⟨a, b, hab, o, by simp [P, hact], rfl⟩, ?_⟩
    exact (silent_iff _).mpr ho
  · push Not at h
    exact ⟨C, Relation.ReflTransGen.refl, (silent_iff C).mpr fun a b hab => h a b hab⟩

/-- **Observation 2.5 (SSLE).** The protocol solves self-stabilizing leader election for
`n = 3`. -/
theorem obs25_solvesSSLE : P.SolvesSSLE (A := Fin 3) leader := by
  intro C
  obtain ⟨D, hD, hs⟩ := obs25_silent C
  exact ⟨D, hD, hs.stablyIn (silent_one_leader D ((silent_iff D).mp hs))⟩

/-- No proper colouring of the 5-cycle with the two ranks different from the leader's rank. -/
lemma no_two_coloring : ∀ (v : Fin 3) (x : Fin 5 → Fin 3),
    ∃ i : Fin 5, ¬ (x i ≠ v ∧ x (i + 1) ≠ v ∧ x i ≠ x (i + 1)) := by
  decide +kernel

lemma silent_cycle : ∀ (i : Fin 5) (a b : Fin 3), a ≠ b →
    ¬ active ((![none, some i, some (i + 1)] : Fin 3 → Option (Fin 5)) a)
      ((![none, some i, some (i + 1)] : Fin 3 → Option (Fin 5)) b) := by
  decide

/-- **Observation 2.5 (no ranking).** For no assignment of ranks to the states does the protocol
solve self-stabilizing ranking: the silent configurations `{l, fᵢ, fᵢ₊₁}` would all have to be
correctly ranked, i.e. the five followers would be properly 2-coloured around a 5-cycle. -/
theorem obs25_not_solvesSSR (r : Option (Fin 5) → Fin 3) : ¬ P.SolvesSSR (A := Fin 3) r := by
  intro hP
  obtain ⟨i, hi⟩ := no_two_coloring (r none) (fun i => r (some i))
  let C : Config (Fin 3) (Option (Fin 5)) := ![none, some i, some (i + 1)]
  have hs : P.Silent C := (silent_iff C).mpr (silent_cycle i)
  obtain ⟨D, hD, hDs⟩ := hP C
  have hDC := hs.reach_eq hD
  subst hDC
  have hb : Function.Injective fun a => r (C a) := (hDs C Relation.ReflTransGen.refl).1
  apply hi
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (hb (a₁ := 1) (a₂ := 0) (by simpa [C] using h)) (by decide)
  · exact absurd (hb (a₁ := 2) (a₂ := 0) (by simpa [C] using h)) (by decide)
  · exact absurd (hb (a₁ := 1) (a₂ := 2) (by simpa [C] using h)) (by decide)

end Obs25

/-! ### Observation 2.6 -/

section Obs26

variable {Q A : Type*} [DecidableEq A] (P : NProtocol Q)

/-- **Observation 2.6 (deterministic core).** Let `C` be silent, `ℓ ≠ u`, and let `C'` be `C`
with the state of `ℓ` copied to `u`. Then every interaction of `C'` other than the one between
`ℓ` and `u` (in either order) is null. -/
theorem obs26_null_of_ne {C : Config A Q} (hC : P.Silent C) {ℓ u : A} (hℓu : ℓ ≠ u)
    {a b : A} (hab : a ≠ b) (hne : ¬ ((a = ℓ ∧ b = u) ∨ (a = u ∧ b = ℓ)))
    {o : Q × Q} (ho : o ∈ P.δ (Function.update C u (C ℓ) a) (Function.update C u (C ℓ) b)) :
    o = (Function.update C u (C ℓ) a, Function.update C u (C ℓ) b) := by
  by_cases hau : a = u
  · subst hau
    have hbℓ : b ≠ ℓ := fun h => hne (Or.inr ⟨rfl, h⟩)
    rw [Function.update_self, Function.update_of_ne (Ne.symm hab)] at ho ⊢
    exact hC ℓ b (Ne.symm hbℓ) o ho
  · by_cases hbu : b = u
    · subst hbu
      have haℓ : a ≠ ℓ := fun h => hne (Or.inl ⟨h, rfl⟩)
      rw [Function.update_self, Function.update_of_ne hab] at ho ⊢
      exact hC a ℓ haℓ o ho
    · rw [Function.update_of_ne hau, Function.update_of_ne hbu] at ho ⊢
      exact hC a b hab o ho

/-- The configuration `C'` of Observation 2.6 has two leaders. -/
theorem obs26_two_leaders [Fintype A] {leader : Q → Bool} {C : Config A Q} {ℓ u : A}
    (hℓu : ℓ ≠ u) (hC : NProtocol.numLeaders leader C = 1) (hℓ : leader (C ℓ) = true) :
    NProtocol.numLeaders leader (Function.update C u (C ℓ)) = 2 := by
  unfold NProtocol.numLeaders at hC ⊢
  obtain ⟨x, hx⟩ := card_eq_one.mp hC
  have hxℓ : ℓ = x := by
    have : ℓ ∈ univ.filter fun a => leader (C a) = true := by simpa using hℓ
    rw [hx] at this; simpa using this
  subst hxℓ
  have hu : leader (C u) = false := by
    by_contra h
    have : u ∈ univ.filter fun a => leader (C a) = true := by simpa using h
    rw [hx] at this; exact hℓu (by simp at this; exact this.symm)
  rw [card_eq_two]
  refine ⟨ℓ, u, hℓu, ?_⟩
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  by_cases hyu : y = u
  · subst hyu; simp [hℓ]
  · rw [Function.update_of_ne hyu]
    constructor
    · intro h
      have : y ∈ univ.filter fun a => leader (C a) = true := by simpa using h
      rw [hx] at this; exact Or.inl (by simpa using this)
    · rintro (rfl | rfl)
      · exact hℓ
      · exact absurd rfl hyu

end Obs26

lemma n2_inj : ∀ (a b : Fin 2), a ≠ b → ∀ C : Fin 2 → Fin 2,
    Function.Injective (if C a = C b then Function.update C b (C b + 1) else C) := by
  decide

/-- **Observation 2.6 fails for `n = 2` (quantitative part).** For two agents,
`Silent-n-state-SSR` (a silent SSLE protocol) is correctly ranked — hence has a unique leader —
after the first interaction, from every configuration and under every schedule. So its
convergence time is at most `1/2` (parallel time), while Observation 2.6 claims probability
`≥ ½ n^{-3α} > 0` of needing time `≥ α n ln n`; for `α = 1` this is `2 ln 2 > 1/2`. -/
theorem obs26_n2_counterexample (E : (SilentSSR.silentSSR 2).Execution (Fin 2)) (t : ℕ)
    (ht : 1 ≤ t) : Function.Bijective (E.config t) ∧ (1 / 2 : ℝ) < 1 * 2 * Real.log 2 := by
  refine ⟨?_, ?_⟩
  · -- after the first interaction the two ranks differ, and then nothing changes
    have h1 : ∀ s, Function.Injective (E.config (s + 1)) := by
      intro s
      have hstep := E.step s
      have hne := E.sched_ne s
      generalize E.sched s = q at hstep hne
      obtain ⟨a, b⟩ := q
      generalize E.config s = C at hstep
      rw [hstep, SilentSSR.interact_eq C a b hne]
      exact n2_inj a b hne C
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨h1 s, rfl⟩
  · have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    linarith

end TimeOptimalSSLE
