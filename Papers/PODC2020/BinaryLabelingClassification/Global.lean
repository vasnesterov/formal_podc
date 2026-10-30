import Papers.PODC2020.BinaryLabelingClassification.LowerBound
import Papers.PODC2020.BinaryLabelingClassification.Existence

/-!
# Theorems 8.1–8.3: the global problem families V and VI

For a node set `V` with `n = |V|` nodes (identifiers), `WhiteSolvable Π V T` says that some
`T`-round deterministic LOCAL white algorithm solves `Π` on every tree on `V` with every proper
2-colouring.

* Theorem 8.1: for V.a and V.b, `T = n` rounds suffice, and every `T`-round algorithm needs
  `n < (3T + 6) d` (V.a), resp. `n < (3T + 9) δ` (V.b) (`theorem_8_1`).
* Theorem 8.2: for VI.a and VI.b, every `T`-round algorithm needs `n < (6T + 10)(d + δ − 2)`.
* Theorem 8.3: for VI.a and VI.b, `T = n` rounds suffice.

So all these problems have deterministic complexity `Θ(n)` (for fixed degrees).
-/

namespace Podc.BinaryLabeling

open SimpleGraph Caterpillar

variable {V : Type*}

/-- Observation 3.4 for complexities: an algorithm for a restriction solves the relaxation. -/
theorem WhiteSolvable.of_restriction {P P' : Problem} (h : P'.IsRestriction P) {T : ℕ}
    (hs : WhiteSolvable P' V T) : WhiteSolvable P V T := by
  obtain ⟨A, hA, hs⟩ := hs
  exact ⟨A, hA, fun G f hGf => (hs G f hGf).of_restriction h⟩

lemma card_node (M a b r : ℕ) :
    Fintype.card (Node M a b r) = (M + 1) * (a + 1) + ((M + 1) * (b + 1) + r) := by
  simp [Node]

/-- Lower bound of Theorem 8.1 for V.a, for every node set. -/
theorem va_lower_card [Fintype V] {P : Problem} (hP : P.IsVa) {T : ℕ}
    (h : WhiteSolvable P V T) : Fintype.card V < (3 * T + 6) * P.d := by
  by_contra hn
  push Not at hn
  have hd := P.two_le_d
  have hcard : Fintype.card (Node (3 * T + 5) (P.d - 2) 0
      (Fintype.card V - (3 * T + 5 + 1) * P.d)) = Fintype.card V := by
    rw [card_node]
    have : (3 * T + 5 + 1) * (P.d - 2 + 1) + (3 * T + 5 + 1) * (0 + 1) =
        (3 * T + 5 + 1) * P.d := by
      rw [← mul_add]; congr 1; omega
    have h6 : (3 * T + 5 + 1) * P.d = (3 * T + 6) * P.d := by ring_nf
    omega
  exact va_lower hP (by omega) rfl le_rfl ((h.of_equiv (Fintype.equivOfCardEq hcard)))

/-- **Theorem 8.1.** Problems of families V.a and V.b have complexity `Θ(n)`: they are solvable
in `n` rounds, and a `T`-round algorithm exists only if `n < (3T + 6)·d` (V.a), resp.
`n < (3T + 9)·δ` (V.b; a `T`-round algorithm for V.b gives a `(T + 1)`-round algorithm for
V.a, Observation 3.2). -/
theorem theorem_8_1 [Fintype V] {P : Problem} (hP : P.IsVa ∨ P.IsVb) :
    WhiteSolvable P V (Fintype.card V) ∧
    ∀ T, WhiteSolvable P V T →
      (P.IsVa → Fintype.card V < (3 * T + 6) * P.d) ∧
      (P.IsVb → Fintype.card V < (3 * T + 9) * P.δ) := by
  refine ⟨theorem_8_1_upper hP, fun T h => ⟨fun ha => va_lower_card ha h, fun hb => ?_⟩⟩
  have := va_lower_card hb (observation_3_2_swap h)
  simpa [Problem.swap, show 3 * (T + 1) + 6 = 3 * T + 9 by ring] using this

/-- Lower bound for the easiest problem of VI.b, for every node set. -/
theorem viEasy_lower_card [Fintype V] {d δ : ℕ} {hd : 2 ≤ d} {hδ : 2 ≤ δ} {T : ℕ}
    (h : WhiteSolvable (viEasy d δ hd hδ) V T) :
    Fintype.card V < (6 * T + 10) * (d + δ - 2) := by
  by_contra hn
  push Not at hn
  have hcard : Fintype.card (Node (6 * T + 9) (d - 2) (δ - 2)
      (Fintype.card V - (6 * T + 9 + 1) * (d + δ - 2))) = Fintype.card V := by
    rw [card_node]
    have : (6 * T + 9 + 1) * (d - 2 + 1) + (6 * T + 9 + 1) * (δ - 2 + 1) =
        (6 * T + 9 + 1) * (d + δ - 2) := by
      rw [← mul_add]; congr 1; omega
    have h6 : (6 * T + 9 + 1) * (d + δ - 2) = (6 * T + 10) * (d + δ - 2) := by ring_nf
    omega
  exact viEasy_lower (by omega) (by omega) le_rfl (h.of_equiv (Fintype.equivOfCardEq hcard))

/-- **Theorem 8.2.** Every problem of family VI.a or VI.b has complexity `Ω(n)`: a `T`-round
algorithm exists only if `n < (6T + 10)(d + δ − 2)`. -/
theorem theorem_8_2 [Fintype V] {P : Problem} (hP : P.IsVIa ∨ P.IsVIb) {T : ℕ}
    (h : WhiteSolvable P V T) : Fintype.card V < (6 * T + 10) * (P.d + P.δ - 2) := by
  rcases hP with ha | hb
  · have hc := ha.compl
    have := viEasy_lower_card (h := (observation_3_2_compl h).of_restriction hc.le_viEasy)
    simpa using this
  · exact viEasy_lower_card (h := h.of_restriction hb.le_viEasy)

/-- **Theorems 8.2 and 8.3 together.** Problems of families VI.a and VI.b have complexity
`Θ(n)`. -/
theorem theorem_8_2_8_3 [Fintype V] {P : Problem} (hP : P.IsVIa ∨ P.IsVIb) :
    WhiteSolvable P V (Fintype.card V) ∧
    ∀ T, WhiteSolvable P V T → Fintype.card V < (6 * T + 10) * (P.d + P.δ - 2) :=
  ⟨theorem_8_3 hP, fun _ h => theorem_8_2 hP h⟩

/-! ### Non-vacuity: the families are non-empty -/

/-- V.a with `d = 3`: `W = 1001`, `B = 010` (2-colouring of 3-regular trees). -/
def vaExample : Problem where
  d := 3
  δ := 2
  W := {0, 3}
  B := {1}
  two_le_d := by norm_num
  two_le_δ := le_rfl
  W_le := by rintro x (rfl | rfl) <;> norm_num
  B_le := by rintro x rfl; norm_num

example : vaExample.IsVa := ⟨rfl, rfl, rfl⟩

example : (viEasy 3 3 (by norm_num) (by norm_num)).IsVIb := by
  rw [Problem.IsVIb.iff]
  refine ⟨⟨by simp [viEasy], fun i hi h => ?_⟩, ⟨by simp [viEasy], fun i hi h => ?_⟩⟩
  · simp [viEasy] at h; omega
  · simp [viEasy] at h hi; omega

end Podc.BinaryLabeling
