import Papers.PODC2022.AdaptiveBAFewerWords.BBComplexity

/-!
# Non-vacuity of the BB results of [CKS22]

A run with `n = 3`, `t = 1`, correct sender `p₀` with input `true` and a silent Byzantine `p₂`:
the adversary is valid, every correct process enters the weak BA with `⟨true⟩_{p₀}`, a weak BA
deciding `⟨true⟩_{p₀}` satisfies the black-box specification, and `theorem13` yields that all
correct processes decide `true`.
-/

namespace Podc.AdaptiveBAFewerWords.BB.Example

open Podc.AdaptiveBAFewerWords.BB

/-- Correct sender `p₀` (input `true`), Byzantine `p₂` sends nothing. -/
def scG : Scenario 3 Bool where
  F := {2}
  sender := 0
  inp := true
  adv := fun _ _ _ => []

theorem scG_valid : AdvValid 1 .fixed scG := by
  intro r b w m _ _ hm
  simp [scG] at hm

theorem scG_end : ∀ u : Fin 3, vEnd 1 .fixed scG u = some (.signed 0 true) := by
  decide +kernel

/-- Phase 1 (leader `p₁`) is silent: every correct process got the sender's value in round 1. -/
theorem scG_words : words 1 .fixed scG = 3 := by
  decide +kernel

/-- The weak BA in which every process decides `⟨true⟩_{p₀}`. -/
def decG : Fin 3 → Option (Option (Item 3 Bool)) := fun _ => some (some (.signed 0 true))

theorem decG_spec : WeakBASpec (fun x => bbValid scG.sender x = true) (Ex 1 .fixed scG)
    {u | u ∉ scG.F} (vEnd 1 .fixed scG) decG := by
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p _ q _ a b ha hb; simp only [decG, Option.some.injEq] at ha hb; rw [← ha, ← hb]
  · intro p _; exact ⟨_, rfl⟩
  · intro p _ d hd
    simp only [decG, Option.some.injEq] at hd
    subst hd
    decide
  · intro p _ x hx
    simp only [decG, Option.some.injEq] at hx
    subst hx
    exact Or.inl ⟨0, by decide, scG_end 0⟩

/-- `theorem13` applies: every correct process decides the sender's input `true`. -/
theorem scG_decides : ∀ u ∉ scG.F, bbDec scG decG u = some (some true) :=
  (theorem13 1 scG (by decide) (by decide) scG_valid decG decG_spec).2.2 (by decide)

end Podc.AdaptiveBAFewerWords.BB.Example
