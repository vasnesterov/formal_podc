import Papers.PODC2011.UniformLocalAlgorithms.Theorem1
import Papers.PODC2011.UniformLocalAlgorithms.Observation41

/-!
# Non-vacuity of the hypotheses of Theorem 1

A toy instance in which all hypotheses of `theorem_1` hold simultaneously: the problem "every node
outputs its input", the family of all normalized instances, the pruning algorithm "prune the nodes
whose tentative output equals their input", the parameter `p = 0`, and the non-uniform algorithm
that waits `g` rounds (its guess) before outputting its input, with running-time bound `f(g) = g`
(additive, so `s_f = 1` by Observation 4.1). The MIS / ruling-set pruning algorithms of
`Pruning.lean` give non-toy pruning algorithms.
-/

open Cslib.Local Filter

namespace Podc.UniformLocalAlgorithms.NonVacuity

open scoped Classical

variable {V α : Type*} [Inhabited α]

/-- The trivial parameter. -/
def zeroParam : Param V α := fun _ _ => 0

/-- Every node outputs its input. -/
def echo : Problem V α α where
  sol _ x y := ∀ v a, x v = some a → y v = a
  congr {_ x y y'} h hy v a hv := by
    rw [← h v (by simp [hv])]; exact hy v a hv
  empty := ⟨fun _ => Classical.arbitrary _, fun _ _ h => by simp at h⟩

/-- All normalized instances. -/
def allInst : Family V α where
  mem G x := res G x = G
  res_eq h := h

/-- Prune the nodes whose tentative output is their input. -/
noncomputable def echoPruning : Pruning (echo (V := V) (α := α)) allInst where
  prune _ x ŷ v := if x v = some (ŷ v) then none else x v
  rad := 0
  isLocal := fun _ _ _ _ v h => by
    have := h.2 v (by simp)
    simp only at this ⊢
    rw [this]
  sub _ x ŷ v h := by
    by_cases hv : x v = some (ŷ v)
    · simp [hv]
    · simpa [hv] using h
  mem G x ŷ _ := by
    show res (res G _) _ = res G _
    exact res_res (fun v h => h)
  detect _ x ŷ _ hsol v := by
    rcases hx : x v with _ | a
    · simp
    · simp [hsol v a hx]
  glue G x ŷ y' _ hy' v a hv := by
    by_cases h : x v = some (ŷ v)
    · simp only [h, ite_true, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [hv] at h; exact (Option.some.inj h).symm
    · have hne : ¬ a = ŷ v := fun e => h (by rw [hv, e])
      have hsome : (if x v = some (ŷ v) then none else x v).isSome := by simp [hv, hne]
      simp only [hsome, ite_true]
      exact hy' v a (by simp [hv, hne])

/-- Wait `g 0` rounds, then output the input. -/
def waitAlg (g : Fin 1 → ℕ) : Alg V α α where
  out t _ x v := if g 0 ≤ t then x v else none
  isLocal t := fun _ _ _ _ v h => by simp only [h.2 v (by simp)]
  stable {t _ x v b} h := by
    split_ifs at h with h1
    · simp only [show g 0 ≤ t + 1 by omega, ite_true]; exact h

/-- The hypotheses of Theorem 1 are satisfiable (with the trivial parameter `p = 0`). -/
theorem theorem_1_hypotheses :
    (∀ g, 0 ≤ ((fun g : Fin 1 → ℕ => (g 0 : ℝ)) g)) ∧
    DependsWithTime (echo (V := V) (α := α)) allInst (fun _ => zeroParam) waitAlg (fun g => (g 0 : ℝ)) ∧
    IsSeqNumber (fun g : Fin 1 → ℕ => (g 0 : ℝ)) (fun _ => 1) ∧
    ∀ _k : Fin 1, (echoPruning (V := V) (α := α)).Monotone zeroParam := by
  refine ⟨fun g => by positivity, ?_, ?_, fun _ _ _ _ _ => le_rfl⟩
  · intro G x _ g _ T hT
    refine ⟨fun v => (x v).getD default, fun v a hv => by simp [hv], fun v hv => ?_⟩
    have hT' : g 0 ≤ T := by simp only at hT; exact_mod_cast hT
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hv
    simp [waitAlg, hT', ha]
  · have := observation_4_1_additive (ℓ := 1) (fun _ y => (y : ℝ)) (fun _ _ => by positivity)
      (fun _ => tendsto_natCast_atTop_atTop)
    simpa using this

/-- Theorem 1 applied to the toy instance. -/
example : ∃ U : Alg V α α, ∃ C : ℝ, ∀ G x, allInst.mem G x → ∃ T : ℕ,
    (T : ℝ) ≤ C * (((correct (fun (_ : Fin 1) => (zeroParam : Param V α)) G x 0 : ℕ) : ℝ) * 1 + 1)
      ∧ U.SolvesWithin echo G x T := by
  obtain ⟨h0, hA, hs, hP⟩ := theorem_1_hypotheses (V := V) (α := α)
  simpa using theorem_1 echo allInst (fun _ => zeroParam) waitAlg _ h0 hA _ hs echoPruning hP

end Podc.UniformLocalAlgorithms.NonVacuity
