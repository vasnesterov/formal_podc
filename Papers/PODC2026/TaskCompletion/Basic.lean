import Mathlib

/-!
# Load balancing covering families (Definition 1) and Lemma A.2

Fischer, Gelles, *The Task Completion Problem and its Application to Crash-Resilient
Computation* (PODC 2026, arXiv:2605.17961).

* `IsLBCF n m k B ε A` — the family `A : Fin m → Finset (Fin n)` is a `(k, B, ε)`-load balancing
  covering family (Definition 1).
* `load A I j` — the number of sets `A ℓ`, `ℓ ∈ I`, that contain `j` (equation (2)).
* `floor_mul_ceil_le_ceil_mul` — Lemma A.2: `⌊x⌈y⌉⌋ ≤ ⌈xy⌉` for `x ∈ [0,1)`, `y ≥ 0`.

Definition 1 speaks of "any `k` sets `A_{i_1}, …, A_{i_k}` of this family"; we read this as any
`k` *distinct* indices, i.e. a `k`-element index set `I : Finset (Fin m)` (this is the only way
the definition is used in the paper, with `I'` a set of `k_i` tasks).
-/

open Finset

namespace Podc.TaskCompletion

/-- The load of the element `j` in the index set `I` (equation (2) of the paper):
`load(j, I) = |{ℓ ∈ I | j ∈ A_ℓ}|`. -/
def load {n m : ℕ} (A : Fin m → Finset (Fin n)) (I : Finset (Fin m)) (j : Fin n) : ℕ :=
  #(I.filter fun ℓ => j ∈ A ℓ)

/-- **Definition 1.** `A₁, …, A_m ⊆ [n]` is a `(k, B, ε)`-load balancing covering family if
1. `nB/(2k) ≤ |A_i| ≤ 2nB/k` for all `i`, and
2. for any `k` sets `A_{i_1}, …, A_{i_k}` of the family there is `J ⊆ [n]` with
   `|J| ≥ (1 - ε) n` such that every `j ∈ J` lies in between `(1 - ε)B` and `(1 + ε)B` of them. -/
structure IsLBCF (n m k B : ℕ) (ε : ℝ) (A : Fin m → Finset (Fin n)) : Prop where
  card_ge : ∀ i, (n * B : ℝ) / (2 * k) ≤ #(A i)
  card_le : ∀ i, (#(A i) : ℝ) ≤ 2 * n * B / k
  balanced : ∀ I : Finset (Fin m), #I = k →
    ∃ J : Finset (Fin n), (1 - ε) * n ≤ #J ∧
      ∀ j ∈ J, (1 - ε) * B ≤ load A I j ∧ (load A I j : ℝ) ≤ (1 + ε) * B

/-- **Lemma A.2.** For `x ∈ [0, 1)` and `y ≥ 0`, `⌊x ⌈y⌉⌋ ≤ ⌈x y⌉`. -/
theorem floor_mul_ceil_le_ceil_mul {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (_hy : 0 ≤ y) :
    ⌊x * ⌈y⌉⌋ ≤ ⌈x * y⌉ := by
  have h1 : (⌈y⌉ : ℝ) < y + 1 := Int.ceil_lt_add_one y
  have h2 : x * ⌈y⌉ < x * y + 1 := by nlinarith
  have h3 : (⌊x * ⌈y⌉⌋ : ℝ) ≤ x * ⌈y⌉ := Int.floor_le _
  have h4 : x * y ≤ ⌈x * y⌉ := Int.le_ceil _
  have : (⌊x * ⌈y⌉⌋ : ℝ) < ⌈x * y⌉ + 1 := by linarith
  exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)

end Podc.TaskCompletion
