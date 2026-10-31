import Papers.PODC2016.CollaborativeListSpec.RGA
import Papers.PODC2016.CollaborativeListSpec.Theorem9

/-!
# Non-vacuity of the lower bound: RGA is push-based

RGA (Theorem 1) is push-based for the strong, hence the weak, list specification, so Theorems 8
and 9 apply to it: with three replicas and integer elements, RGA has executions with `D`
deletions where a replica whose visible list has one element stores `⌊(D-2)/2⌋` bits.
-/

namespace Podc.CollaborativeListSpec

/-- RGA satisfies the hypotheses of Theorem 9 (paper form). -/
theorem rga_pushBased_weak (U : Type) [DecidableEq U] (n : ℕ) :
    PushBased (RGA.protocol U n) Weak
      (fun α => CausalBroadcast α ∧ UserOK (RGA.protocol U n) α) :=
  RGA.pushBased.weak

/-- Theorem 9 instantiated with RGA on three replicas. -/
theorem rga_lowerBound :
    ∃ u : ℕ, ∀ D, 4 ≤ D → ∀ r₁ : Fin 3, ∀ enc : RGA.St ℕ → List Bool, Function.Injective enc →
      ∃ α : List (Act (Fin 3) (LOp ℕ)), (RGA.protocol ℕ 3).WF α ∧ CausalAtomic α ∧
        UserOK (RGA.protocol ℕ 3) α ∧ numDel α = D ∧
        ∃ n ≤ α.length, (∀ q < n, ∀ s, α[q]? ≠ some (.recv r₁ s)) ∧
          (((RGA.protocol ℕ 3).exec (α.take n)).st r₁).2 = none ∧
          (RGA.protocol ℕ 3).resp r₁ (((RGA.protocol ℕ 3).exec (α.take n)).st r₁) .read = [u] ∧
          (D - 2) / 2 ≤ (enc (((RGA.protocol ℕ 3).exec (α.take n)).st r₁).1).length :=
  theorem9_causal (by simp) (rga_pushBased_weak ℕ 3)

end Podc.CollaborativeListSpec
