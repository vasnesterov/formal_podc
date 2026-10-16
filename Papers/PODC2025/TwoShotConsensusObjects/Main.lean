import Papers.PODC2025.TwoShotConsensusObjects.Necessity
import Papers.PODC2025.TwoShotConsensusObjects.AlgC1
import Papers.PODC2025.TwoShotConsensusObjects.AlgC15
import Papers.PODC2025.TwoShotConsensusObjects.AlgC2
import Papers.PODC2025.TwoShotConsensusObjects.Examples

/-!
# The exact characterization (main theorem)

Nguyen–Sutra, PODC 2025: a deterministic two-shot object type `(O, m)` solves wait-free
two-process consensus (together with registers) **iff** it belongs to one of the classes
`C₁`, `C₁.₅`, `C₂`.

* `→`: Theorem 3 (`necessity`; Propositions 1, 2 and Lemma 5);
* `←`: Section 5 (`solvable_of_C1`, `solvable_of_C15Cond` — Algorithms 1, 2 / Theorem 1 —,
  `solvable_of_C2Cond` — Algorithm 3 / Theorem 2).
-/

namespace TwoShotCons

open Cslib.SharedMemory

/-- **Main theorem.** Objects of type `(O, m)` solve two-shot two-process consensus iff `(O, m)`
belongs to `C₁`, `C₁.₅` or `C₂`. -/
theorem characterization (O : ObjSpec) (m : Fin 2 → Set O.Op) :
    Solvable O m ↔ C1 O m ∨ C15 O m ∨ C2 O m := by
  refine ⟨necessity, fun h => ?_⟩
  rw [classes_iff] at h
  rcases h with h | h | h | h
  · exact solvable_of_C1 h
  · exact solvable_of_C15Cond (by decide) h
  · exact solvable_of_C15Cond (by decide) h
  · exact solvable_of_C2Cond h

/-! ## Sanity checks -/

/-- The readable, asymmetric and weak queues of Section 4.2.5 all solve two-shot two-process
consensus. -/
theorem queues_solvable : Solvable queue RQ ∧ Solvable queue AQ ∧ Solvable queue WQ :=
  ⟨(characterization _ _).2 (Or.inl rq_C1), (characterization _ _).2 (Or.inr (Or.inr aq_C2)),
    (characterization _ _).2 (Or.inr (Or.inr wq_C2))⟩

/-- A type whose operations never return information (a single response) cannot solve
two-process consensus, even with two shots (the characterization is not vacuous on the
negative side). -/
theorem not_solvable_of_trivial_resp (O : ObjSpec) (m : Fin 2 → Set O.Op)
    (h : ∀ r r' : O.Resp, r = r') : ¬ Solvable O m := by
  rw [characterization, classes_iff]
  have hD : ∀ s p σ τ, Dist O s p σ τ → (∀ q, (σ.filter (·.1 = q)).length =
      (τ.filter (·.1 = q)).length) → False := by
    intro s p σ τ hd hq
    apply hd
    apply List.ext_get
    · have key : ∀ s (σ : List (Fin 2 × O.Op)), (view O s σ p).length =
          (σ.filter (·.1 = p)).length := by
        intro s σ
        induction σ generalizing s with
        | nil => rfl
        | cons x σ ih =>
          obtain ⟨q, c⟩ := x
          by_cases hqp : q = p
          · subst hqp; rw [view_cons_self]; simp [ih]
          · rw [view_cons_other O _ hqp]; simp [ih, hqp]
      rw [key, key, hq p]
    · intro n _ _; exact h _ _
  rintro (⟨s, f, g, -, -, h0, -⟩ | ⟨s, f, f', g, g', -, -, -, -, h1, -⟩ |
    ⟨s, f, f', g, g', -, -, -, -, h1, -⟩ | ⟨s, f, g, n, c, hn, -, -, -, -, -, h2, -⟩)
  · exact hD _ _ _ _ h0 (fun q => by fin_cases q <;> simp)
  · exact hD _ _ _ _ h1 (fun q => by fin_cases q <;> simp)
  · exact hD _ _ _ _ h1 (fun q => by fin_cases q <;> simp)
  · exact hD _ _ _ _ (h2 0 (by obtain ⟨r, hr⟩ := hn; omega)).1.1
      (fun q => by fin_cases q <;> simp [own])

end TwoShotCons
