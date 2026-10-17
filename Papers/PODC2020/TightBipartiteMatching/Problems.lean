import Papers.PODC2020.TightBipartiteMatching.RoundElim
import Podc.Foundations.Data.Nat.CeilDiv

/-!
# The problems of §4

Throughout `Δ = d + 1`. All constraints are written exactly as in the paper, as lists of condensed
configurations (`[S]^n` is the block `(S, n)`, `[MZPOX]` is `Set.univ`).

* `Phi d x y` is `Φ^W_Δ(x, y)`, the locally checkable encoding of bipartite `x`-maximal
  `y`-matching (white constraint `[MOX]^{y-1}[M][OX]^{Δ-y}`, `[PX]^x[P]^{Δ-x}`; black constraint
  `[MPOX]^{y-1}[M][POX]^{Δ-y}`, `[OX]^x[O]^{Δ-x}`).
* `Phi' d x y` is the intermediate problem `Φ'(x, y)` of Lemma 4.2.
* `Psi d a b c` is `Ψ^W_Δ(a, b, c)`; `Ψ^B_Δ(a, b, c)` is `(Psi d a b c).swap`.

We also prove the label-count consequences of membership that the lower bound needs.
-/

namespace TightBipartiteMatching

open Lab

variable (d : ℕ)

/-- `Φ^W_Δ(x, y)` (§4): bipartite `x`-maximal `y`-matching, encoded with labels `M, P, O, X`. -/
def Phi (x y : ℕ) : Problem Lab where
  W := Cond.Gens [[({M, O, X}, y - 1), ({M}, 1), ({O, X}, d + 1 - y)],
    [({P, X}, x), ({P}, d + 1 - x)]]
  B := Cond.Gens [[({M, P, O, X}, y - 1), ({M}, 1), ({P, O, X}, d + 1 - y)],
    [({O, X}, x), ({O}, d + 1 - x)]]

/-- `Φ'(x, y)` (Lemma 4.2). -/
def Phi' (x y : ℕ) : Problem Lab where
  W := Cond.Gens [[({M, P, O, X}, y - 1), ({M, X}, 1), ({P, O, X}, d + 1 - y)],
    [({P, O, X}, x), ({O, X}, d + 1 - x)]]
  B := Cond.Gens [[({X}, y - 1), ({M}, 1), ({O}, d + 1 - y)], [({X}, y), ({P}, d + 1 - y)]]

/-- `Ψ^W_Δ(a, b, c)` (§4). -/
def Psi (a b c : ℕ) : Problem Lab where
  W := Cond.Gens [[({X}, a - 1), ({M}, 1), ({O}, d + 1 - a)],
    [({X}, a), ({O}, b), ({P}, d + 1 - a - b)],
    [({X}, a), ({Z}, 1), ({O}, d + 1 - a - 1)]]
  B := Cond.Gens [[(Set.univ, a - 1), ({M, X}, 1), ({P, O, X}, d + 1 - a)],
    [(Set.univ, a), ({P, O, X}, c), ({O, X}, d + 1 - a - c)],
    [(Set.univ, a), ({X}, 1), ({P, O, X}, d + 1 - a - 1)]]

variable {d}

/-! ### Label counts -/

/-- Every black configuration of `Ψ^W(a, b, c)` has at most `a` labels from `{M, Z}`, and either an
`M` or an `X`, or at most `a + c` labels from `{M, Z, P}`. -/
theorem psi_B_counts {a b c : ℕ} (ha : 1 ≤ a) {m : Multiset Lab} (h : m ∈ (Psi d a b c).B) :
    m.count M + m.count Z ≤ a ∧
      (1 ≤ m.count M + m.count X ∨ m.count M + m.count Z + m.count P ≤ a + c) := by
  simp only [Psi, Cond.mem_gens, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨c', hc', hm⟩ := h
  rcases hc' with rfl | rfl | rfl
  all_goals
    obtain ⟨m₁, m₂, m₃, rfl, h1, h2, h3⟩ := gen3_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2 h3
    simp only [Multiset.count_add]
    omega

/-- Every white configuration of `Ψ^W(a, b, c)` contains an `M`, a `Z`, or `Δ - a - b` labels `P`. -/
theorem psi_W_counts {a b c : ℕ} {m : Multiset Lab} (h : m ∈ (Psi d a b c).W) :
    1 ≤ m.count M ∨ 1 ≤ m.count Z ∨ d + 1 - a - b ≤ m.count P := by
  simp only [Psi, Cond.mem_gens, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨c', hc', hm⟩ := h
  rcases hc' with rfl | rfl | rfl
  all_goals
    obtain ⟨m₁, m₂, m₃, rfl, h1, h2, h3⟩ := gen3_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2 h3
    simp only [Multiset.count_add]
    omega

/-- Black configurations of `Φ^W(x, y)`: no `Z`, at most `y` labels `M`, and a `P` only next to an
`M`. -/
theorem phi_B_counts {x y : ℕ} (hy : 1 ≤ y) {m : Multiset Lab} (h : m ∈ (Phi d x y).B) :
    m.count Z = 0 ∧ m.count M ≤ y ∧ (1 ≤ m.count M ∨ m.count P = 0) := by
  simp only [Phi, Cond.mem_gens, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨c', hc', hm⟩ := h
  rcases hc' with rfl | rfl
  · obtain ⟨m₁, m₂, m₃, rfl, h1, h2, h3⟩ := gen3_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2 h3
    simp only [Multiset.count_add]
    omega
  · obtain ⟨m₁, m₂, rfl, h1, h2⟩ := gen2_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2
    simp only [Multiset.count_add]
    omega

/-- White configurations of `Φ^W(x, y)` contain an `M` or `Δ - x` labels `P`. -/
theorem phi_W_counts {x y : ℕ} {m : Multiset Lab} (h : m ∈ (Phi d x y).W) :
    1 ≤ m.count M ∨ d + 1 - x ≤ m.count P := by
  simp only [Phi, Cond.mem_gens, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨c', hc', hm⟩ := h
  rcases hc' with rfl | rfl
  · obtain ⟨m₁, m₂, m₃, rfl, h1, h2, h3⟩ := gen3_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2 h3
    simp only [Multiset.count_add]
    omega
  · obtain ⟨m₁, m₂, rfl, h1, h2⟩ := gen2_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2
    simp only [Multiset.count_add]
    omega

/-- White configurations of `Φ'(x, y)`: no `Z`, at most `y` labels `M`, and an `M` or an `X`, or at
most `x` labels `P`. -/
theorem phi'_W_counts {x y : ℕ} (hy : 1 ≤ y) {m : Multiset Lab} (h : m ∈ (Phi' d x y).W) :
    m.count Z = 0 ∧ m.count M ≤ y ∧ (1 ≤ m.count M + m.count X ∨ m.count P ≤ x) := by
  simp only [Phi', Cond.mem_gens, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨c', hc', hm⟩ := h
  rcases hc' with rfl | rfl
  · obtain ⟨m₁, m₂, m₃, rfl, h1, h2, h3⟩ := gen3_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2 h3
    simp only [Multiset.count_add]
    omega
  · obtain ⟨m₁, m₂, rfl, h1, h2⟩ := gen2_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2
    simp only [Multiset.count_add]
    omega

/-- Black configurations of `Φ'(x, y)` contain an `M` or `Δ - y` labels `P`. -/
theorem phi'_B_counts {x y : ℕ} {m : Multiset Lab} (h : m ∈ (Phi' d x y).B) :
    1 ≤ m.count M ∨ d + 1 - y ≤ m.count P := by
  simp only [Phi', Cond.mem_gens, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨c', hc', hm⟩ := h
  rcases hc' with rfl | rfl
  · obtain ⟨m₁, m₂, m₃, rfl, h1, h2, h3⟩ := gen3_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2 h3
    simp only [Multiset.count_add]
    omega
  · obtain ⟨m₁, m₂, rfl, h1, h2⟩ := gen2_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2
    simp only [Multiset.count_add]
    omega

/-! ### The bound `T_Δ(x, y)` -/

/-- `T_Δ(x, y)` (§1): `2⌈(Δ-x)/y⌉` if `⌈Δ/y⌉ > ⌈(Δ-x)/y⌉`, and `2⌈(Δ-x)/y⌉ - 1` otherwise
(`a ⌈/⌉ b` is Mathlib's ceiling division on `ℕ`). -/
def Tval (Δ x y : ℕ) : ℕ :=
  if (Δ - x) ⌈/⌉ y < Δ ⌈/⌉ y then 2 * ((Δ - x) ⌈/⌉ y) else 2 * ((Δ - x) ⌈/⌉ y) - 1

/-- Counts of a constant configuration. -/
theorem count_mset_const (ℓ ℓ' : Lab) :
    (mset fun _ : Fin (d + 1) => ℓ).count ℓ' = if ℓ = ℓ' then d + 1 else 0 := by
  rw [count_mset]
  split_ifs with h
  · subst h; simp
  · simp [h]

end TightBipartiteMatching
