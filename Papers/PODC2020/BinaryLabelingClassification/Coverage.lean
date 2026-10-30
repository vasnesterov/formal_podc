import Papers.PODC2020.BinaryLabelingClassification.Families

/-!
# Lemma 10.4: every problem not of type I–IV relaxes to a forbidden-degree or a bipartite
sinkless orientation problem

Bit-vector patterns of Table 2 (bit `i` of `W` is `1` iff `i ∈ W`):

* type II: `W = 0⁺` or `B = 0⁺` (empty constraint);
* type III: `B = 1⁺` and `W` non-empty, or `W = 1⁺` and `B` non-empty;
* type IV: `w₀ = b₀ = 1`, or `w_d = b_δ = 1`;
* forbidden degree (Definition 10.2): `W = 1⁺01⁺`, `B = 01⁺0`;
* bipartite sinkless orientation (Definition 10.3): `W = 1⁺0`, `B = 01⁺`.

Lemma 10.4 only needs that the problem is not of type II, III or IV (type I is not used).
"Equivalent" (Observation 3.2) is realised by the colour swap or the complement.
-/

namespace Podc.BinaryLabeling

namespace Problem

/-- Type II (unsolvable): an empty constraint. -/
def IsTypeII (P : Problem) : Prop := P.W = ∅ ∨ P.B = ∅

/-- Type III (trivial): one side is unconstrained and the other non-empty. -/
def IsTypeIII (P : Problem) : Prop :=
  (P.W.Nonempty ∧ ∀ i ≤ P.δ, i ∈ P.B) ∨ ((∀ i ≤ P.d, i ∈ P.W) ∧ P.B.Nonempty)

/-- Type IV (trivial): all-0 or all-1 labels are feasible on both sides. -/
def IsTypeIV (P : Problem) : Prop := (0 ∈ P.W ∧ 0 ∈ P.B) ∨ (P.d ∈ P.W ∧ P.δ ∈ P.B)

/-- Forbidden degree problems `(1⁺01⁺, 01⁺0)` (Definition 10.2). -/
def IsFD (P : Problem) : Prop :=
  ∃ i, 0 < i ∧ i < P.d ∧ (∀ x, x ∈ P.W ↔ x ≤ P.d ∧ x ≠ i) ∧
    (∀ x, x ∈ P.B ↔ 1 ≤ x ∧ x + 1 ≤ P.δ)

/-- Bipartite sinkless orientation problems `(1⁺0, 01⁺)` (Definition 10.3). -/
def IsBSO (P : Problem) : Prop :=
  (∀ x, x ∈ P.W ↔ x + 1 ≤ P.d) ∧ (∀ x, x ∈ P.B ↔ 1 ≤ x ∧ x ≤ P.δ)

end Problem

open Problem

/-- A problem from its data. -/
def mkProblem (d δ : ℕ) (W B : Set ℕ) (hd : 2 ≤ d) (hδ : 2 ≤ δ) (hW : ∀ x ∈ W, x ≤ d)
    (hB : ∀ x ∈ B, x ≤ δ) : Problem := ⟨d, δ, W, B, hd, hδ, hW, hB⟩

/-- **Lemma 10.4.** If `Π` is not of type II, III or IV, then it has a relaxation `Π' ⊇ Π` that
is a forbidden degree problem or a bipartite sinkless orientation problem, or is equivalent to
one (Observation 3.2: its complement is a bipartite sinkless orientation problem, or its colour
swap is a forbidden degree problem). -/
theorem lemma_10_4 (P : Problem) (h2 : ¬ P.IsTypeII) (h3 : ¬ P.IsTypeIII) (h4 : ¬ P.IsTypeIV) :
    ∃ P' : Problem, P.IsRestriction P' ∧ (P'.IsFD ∨ P'.IsBSO ∨ P'.compl.IsBSO ∨ P'.swap.IsFD) := by
  have hd := P.two_le_d
  have hδ := P.two_le_δ
  have hW := P.W_le
  have hB := P.B_le
  simp only [IsTypeII, IsTypeIII, IsTypeIV, not_or, not_and] at h2 h3 h4
  by_cases hW0 : 0 ∈ P.W
  · -- `w₀ = 1`, hence `b₀ = 0`
    have hB0 : 0 ∉ P.B := h4.1 hW0
    by_cases hWd : P.d ∈ P.W
    · -- case `1010`
      have hBδ : P.δ ∉ P.B := h4.2 hWd
      -- `W` is not all ones (else type II.b or III.b)
      have : ∃ i ≤ P.d, i ∉ P.W := by
        by_contra hc
        push Not at hc
        exact h3.2 hc (Set.nonempty_iff_ne_empty.2 h2.2)
      obtain ⟨i, hi, hiW⟩ := this
      have hi0 : i ≠ 0 := fun h => hiW (h ▸ hW0)
      have hid : i ≠ P.d := fun h => hiW (h ▸ hWd)
      refine ⟨mkProblem P.d P.δ {x | x ≤ P.d ∧ x ≠ i} {x | 1 ≤ x ∧ x + 1 ≤ P.δ} hd hδ
        (fun x hx => hx.1) (fun x hx => by have := hx.2; omega), ⟨rfl, rfl, ?_, ?_⟩,
        Or.inl ⟨i, by omega, show i < P.d by omega, fun x => Iff.rfl, fun x => Iff.rfl⟩⟩
      · intro x hx
        exact ⟨hW x hx, fun h => hiW (h ▸ hx)⟩
      · intro x hx
        have := hB x hx
        refine ⟨?_, ?_⟩
        · by_contra hc; exact hB0 (by convert hx; omega)
        · by_contra hc; exact hBδ (by convert hx; omega)
    · -- `w_d = 0` and `b₀ = 0`: bipartite sinkless orientation
      refine ⟨mkProblem P.d P.δ {x | x + 1 ≤ P.d} {x | 1 ≤ x ∧ x ≤ P.δ} hd hδ
        (fun x hx => by have : x + 1 ≤ P.d := hx; omega) (fun x hx => hx.2), ⟨rfl, rfl, ?_, ?_⟩,
        Or.inr (Or.inl ⟨fun x => Iff.rfl, fun x => Iff.rfl⟩)⟩
      · intro x hx
        have := hW x hx
        show x + 1 ≤ P.d
        by_contra hc; exact hWd (by convert hx; omega)
      · intro x hx
        refine ⟨?_, hB x hx⟩
        by_contra hc; exact hB0 (by convert hx; omega)
  · -- `w₀ = 0`
    by_cases hBδ : P.δ ∈ P.B
    · have hWd : P.d ∉ P.W := fun h => h4.2 h hBδ
      by_cases hB0 : 0 ∈ P.B
      · -- case `0101`: the colour swap is of type `1010`
        have : ∃ i ≤ P.δ, i ∉ P.B := by
          by_contra hc
          push Not at hc
          exact h3.1 (Set.nonempty_iff_ne_empty.2 h2.1) hc
        obtain ⟨i, hi, hiB⟩ := this
        have hi0 : i ≠ 0 := fun h => hiB (h ▸ hB0)
        have hid : i ≠ P.δ := fun h => hiB (h ▸ hBδ)
        refine ⟨mkProblem P.d P.δ {x | 1 ≤ x ∧ x + 1 ≤ P.d} {x | x ≤ P.δ ∧ x ≠ i} hd hδ
          (fun x hx => by have := hx.2; omega) (fun x hx => hx.1), ⟨rfl, rfl, ?_, ?_⟩,
          Or.inr (Or.inr (Or.inr ⟨i, by omega, show i < P.δ by omega,
            fun x => Iff.rfl, fun x => Iff.rfl⟩))⟩
        · intro x hx
          have := hW x hx
          refine ⟨?_, ?_⟩
          · by_contra hc; exact hW0 (by convert hx; omega)
          · by_contra hc; exact hWd (by convert hx; omega)
        · intro x hx
          exact ⟨hB x hx, fun h => hiB (h ▸ hx)⟩
      · -- `b₀ = 0` and `w_d = 0`: bipartite sinkless orientation
        refine ⟨mkProblem P.d P.δ {x | x + 1 ≤ P.d} {x | 1 ≤ x ∧ x ≤ P.δ} hd hδ
          (fun x hx => by have : x + 1 ≤ P.d := hx; omega) (fun x hx => hx.2),
          ⟨rfl, rfl, ?_, ?_⟩, Or.inr (Or.inl ⟨fun x => Iff.rfl, fun x => Iff.rfl⟩)⟩
        · intro x hx
          have := hW x hx
          show x + 1 ≤ P.d
          by_contra hc; exact hWd (by convert hx; omega)
        · intro x hx
          refine ⟨?_, hB x hx⟩
          by_contra hc; exact hB0 (by convert hx; omega)
    · -- `w₀ = 0` and `b_δ = 0`: the complement is a bipartite sinkless orientation problem
      refine ⟨mkProblem P.d P.δ {x | 1 ≤ x ∧ x ≤ P.d} {x | x + 1 ≤ P.δ} hd hδ
        (fun x hx => hx.2) (fun x hx => by have : x + 1 ≤ P.δ := hx; omega),
        ⟨rfl, rfl, ?_, ?_⟩, Or.inr (Or.inr (Or.inl ⟨fun x => ?_, fun x => ?_⟩))⟩
      · intro x hx
        refine ⟨?_, hW x hx⟩
        by_contra hc; exact hW0 (by convert hx; omega)
      · intro x hx
        have := hB x hx
        show x + 1 ≤ P.δ
        by_contra hc; exact hBδ (by convert hx; omega)
      · simp only [compl_W, compl_d, mkProblem]
        constructor
        · rintro ⟨y, hy, rfl⟩; have := hy.1; dsimp only; omega
        · intro hx; exact ⟨P.d - x, ⟨by omega, by omega⟩, by dsimp only; omega⟩
      · simp only [compl_B, compl_δ, mkProblem]
        constructor
        · rintro ⟨y, hy, rfl⟩; have : y + 1 ≤ P.δ := hy; dsimp only; omega
        · intro hx; exact ⟨P.δ - x, show P.δ - x + 1 ≤ P.δ by omega, by dsimp only; omega⟩

end Podc.BinaryLabeling
