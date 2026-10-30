import Papers.PODC2018.SpannerApproximation.LowerBound

/-!
# Theorems 2.8 and 1.1: CONGEST lower bounds for approximating minimum directed `k`-spanners

The algorithm runs on an arbitrary vertex set `V` with `n = |V|` and must be correct on every
loopless digraph on `V` whose underlying network is connected. The lower-bound graph `G(ℓ, β)` is
padded with pendant vertices to have exactly `n` vertices, so `ℓ` and `β` are chosen from `n` and
`α` (the paper instead runs the algorithm on a graph with `n ≤ n'` vertices and uses monotonicity
of `α(n)` and `T(n)`).
-/

namespace Podc.SpannerApproximation

open Finset Cslib.Congest

/-- **Theorem 2.8** (deterministic), concrete form. Let `k ≥ 5`, `α ≥ 0`, and let `β` be a natural
number with `156 α < β²` and `β (2β + 5) ≤ n` (so `α ≤ n / c'`). If a deterministic CONGEST
algorithm with `B`-bit messages outputs, within `T` rounds, an `α`-approximate minimum directed
`k`-spanner of every loopless `n`-vertex digraph with connected underlying network, then
`⌊n / (2β + 5)⌋ ≤ 18 · B · T + 1`. With `β = Θ(√α)` and `B = O(log n)` this is
`T = Ω(n / (√α · log n))`. -/
theorem theorem_2_8 {V σ : Type*} [Fintype V] [DecidableEq V] {B T k : ℕ} (hk : 5 ≤ k)
    {α : ℝ} (hα : 0 ≤ α) {β : ℕ} (hβ : 156 * α < β ^ 2)
    (hn : β * (2 * β + 5) ≤ Fintype.card V)
    (A : Algorithm V (DInput V) σ B) (pick : V → σ → V → V → Bool)
    (hA : ∀ E : Finset (V × V), (∀ v, (v, v) ∉ E) → (net E).Connected →
      IsApproxDiSpanner α E (outArcs A pick E T) k) :
    Fintype.card V / (2 * β + 5) ≤ 18 * T * B + 1 := by
  set n := Fintype.card V
  set ℓ := n / (2 * β + 5)
  set p := n % (2 * β + 5)
  have hβpos : 0 < β := by
    rcases Nat.eq_zero_or_pos β with h | h
    · subst h; simp at hβ; linarith
    · exact h
  have hβℓ : β ≤ ℓ := (Nat.le_div_iff_mul_le (by omega)).2 hn
  have hℓ : 0 < ℓ := lt_of_lt_of_le hβpos hβℓ
  have hp : p < 2 * β + 5 := Nat.mod_lt _ (by omega)
  have hcard : Fintype.card (Vtx ℓ β p) = n := by
    rw [Vtx.card]
    calc 2 * ℓ * β + 5 * ℓ + p = (2 * β + 5) * ℓ + p := by ring
      _ = n := Nat.div_add_mod n _
  let e : V ≃ Vtx ℓ β p := Fintype.equivOfCardEq hcard.symm
  have hbound : nonDBound ℓ β p ≤ 13 * ℓ ^ 2 := by
    simp only [nonDBound]
    have h1 : ℓ * β ≤ ℓ * ℓ := Nat.mul_le_mul_left _ hβℓ
    have h2 : ℓ ≤ ℓ * ℓ := Nat.le_mul_of_pos_left ℓ hℓ
    nlinarith
  have hgap : 12 * (α * nonDBound ℓ β p) < (β : ℝ) ^ 2 * ℓ ^ 2 := by
    have hb : (nonDBound ℓ β p : ℝ) ≤ 13 * (ℓ : ℝ) ^ 2 := by exact_mod_cast hbound
    have hℓ2 : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by positivity
    calc 12 * (α * nonDBound ℓ β p) ≤ 12 * (α * (13 * (ℓ : ℝ) ^ 2)) := by gcongr
      _ = (156 * α) * ℓ ^ 2 := by ring
      _ < (β : ℝ) ^ 2 * ℓ ^ 2 := by gcongr
  have h := lemma_2_7 e hα hk (by exact_mod_cast hgap) A pick T
    (fun a b => hA _ (Ev_loopless e a b) (Ev_connected e a b hℓ hβpos))
  change ℓ ≤ 18 * T * B + 1
  by_contra hc
  push Not at hc
  have : ℓ * (18 * T * B + 2) ≤ ℓ * ℓ := Nat.mul_le_mul_left _ hc
  nlinarith

/-- The choice `β = ⌊√⌈156 α⌉⌋ + 1` satisfies `156 α < β²`. -/
lemma lt_sq_sqrt_ceil (α : ℝ) : 156 * α < ((Nat.sqrt ⌈156 * α⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by
  have h1 : 156 * α ≤ ⌈156 * α⌉₊ := Nat.le_ceil _
  have h2 : ⌈156 * α⌉₊ < (Nat.sqrt ⌈156 * α⌉₊ + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have h2' : (⌈156 * α⌉₊ : ℝ) < ((Nat.sqrt ⌈156 * α⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h2
  linarith

/-- **Theorem 2.8** (deterministic) with an explicit `β = ⌊√⌈156 α⌉⌋ + 1 = Θ(√α)`: every
deterministic CONGEST `α`-approximation algorithm for minimum directed `k`-spanner (`k ≥ 5`)
with `B`-bit messages and `T` rounds satisfies `⌊n / (2β + 5)⌋ ≤ 18 · B · T + 1`, provided
`β (2β + 5) ≤ n` (i.e. `α ≤ n / c'`). -/
theorem theorem_2_8' {V σ : Type*} [Fintype V] [DecidableEq V] {B T k : ℕ} (hk : 5 ≤ k)
    {α : ℝ} (hα : 0 ≤ α)
    (hn : (Nat.sqrt ⌈156 * α⌉₊ + 1) * (2 * (Nat.sqrt ⌈156 * α⌉₊ + 1) + 5) ≤ Fintype.card V)
    (A : Algorithm V (DInput V) σ B) (pick : V → σ → V → V → Bool)
    (hA : ∀ E : Finset (V × V), (∀ v, (v, v) ∉ E) → (net E).Connected →
      IsApproxDiSpanner α E (outArcs A pick E T) k) :
    Fintype.card V / (2 * (Nat.sqrt ⌈156 * α⌉₊ + 1) + 5) ≤ 18 * T * B + 1 :=
  theorem_2_8 hk hα (lt_sq_sqrt_ceil α) hn A pick hA

/-- **Theorem 1.1** (randomized), conditional on the randomized communication complexity bound
`RandDisjLB δ κ` for set disjointness (Lemma 2.1). Let `k ≥ 5`, `α ≥ 0`, `q = ⌈34 α⌉ + 1` and
`8q ≤ n` (i.e. `α ≤ n / c'`). If a randomized CONGEST algorithm with `B`-bit messages (private
random strings) outputs, within `T` rounds and with failure probability `≤ δ`, an `α`-approximate
minimum directed `k`-spanner of every loopless `n`-vertex digraph with connected underlying
network, then `κ · ⌊√⌊n / 8q⌋⌋ ≤ 6 · B · T + 1`, i.e. `T = Ω(√(n/α) / B)`, which is
`Ω(√n / (√α · log n))` for `B = O(log n)`. -/
theorem theorem_1_1 {V ρ σ : Type} [Fintype V] [DecidableEq V] [Fintype ρ] [Nonempty ρ]
    {B T k : ℕ} (hk : 5 ≤ k) {α δ κ : ℝ} (hα : 0 ≤ α) (hDisj : RandDisjLB δ κ)
    (hn : 8 * (⌈34 * α⌉₊ + 1) ≤ Fintype.card V)
    (A : Algorithm V (DInput V × ρ) σ B) (pick : V → σ → V → V → Bool)
    (hA : ∀ E : Finset (V × V), (∀ v, (v, v) ∉ E) → (net E).Connected →
      (failCount A pick E T α k : ℝ) ≤ δ * Fintype.card (V → ρ)) :
    κ * Nat.sqrt (Fintype.card V / (8 * (⌈34 * α⌉₊ + 1))) ≤ 6 * T * B + 1 := by
  set n := Fintype.card V
  set q := ⌈34 * α⌉₊ + 1
  set M := n / (8 * q)
  set ℓ := Nat.sqrt M
  set β := q * ℓ
  have hq : 1 ≤ q := by omega
  have hM : 1 ≤ M := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa using hn)
  have hℓ : 0 < ℓ := Nat.sqrt_pos.2 hM
  have hℓM : ℓ ^ 2 ≤ M := Nat.sqrt_le' M
  have hMℓ : M < (ℓ + 1) ^ 2 := Nat.lt_succ_sqrt' M
  have h8M : 8 * q * M ≤ n := Nat.mul_div_le n (8 * q)
  have hn8 : n < 8 * q * (M + 1) := by
    have := Nat.lt_mul_div_succ n (show 0 < 8 * q by omega)
    simpa [M] using this
  -- the gadget fits: `2qℓ² + 5ℓ ≤ n`
  have hfit : 2 * ℓ * β + 5 * ℓ ≤ n := by
    have : 2 * ℓ * β + 5 * ℓ ≤ 8 * q * ℓ ^ 2 := by
      simp only [β]
      have : ℓ ≤ q * ℓ ^ 2 := by nlinarith
      nlinarith
    exact this.trans ((Nat.mul_le_mul_left _ hℓM).trans h8M)
  set p := n - (2 * ℓ * β + 5 * ℓ)
  have hcard : Fintype.card (Vtx ℓ β p) = n := by rw [Vtx.card]; omega
  let e : V ≃ Vtx ℓ β p := Fintype.equivOfCardEq hcard.symm
  have hβpos : 0 < β := Nat.mul_pos (by omega) hℓ
  -- `t ≤ n + 2ℓ² ≤ 34 q ℓ²`
  have hbound : nonDBound ℓ β p ≤ 34 * q * ℓ ^ 2 := by
    have h1 : nonDBound ℓ β p ≤ n + 2 * ℓ ^ 2 := by simp only [nonDBound]; omega
    have h2 : n ≤ 32 * q * ℓ ^ 2 := by
      have : M + 1 ≤ (ℓ + 1) ^ 2 := hMℓ
      have : (ℓ + 1) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
      have : 8 * q * (M + 1) ≤ 8 * q * (4 * ℓ ^ 2) := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have : 2 * ℓ ^ 2 ≤ 2 * q * ℓ ^ 2 := by nlinarith
    nlinarith
  have hgap : α * nonDBound ℓ β p < (β : ℝ) ^ 2 := by
    have hb : (nonDBound ℓ β p : ℝ) ≤ 34 * q * (ℓ : ℝ) ^ 2 := by exact_mod_cast hbound
    have hceil : 34 * α ≤ (q : ℝ) - 1 := by
      have := Nat.le_ceil (34 * α)
      simp only [q, Nat.cast_add, Nat.cast_one]
      linarith
    have hℓ2 : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by positivity
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc α * nonDBound ℓ β p ≤ α * (34 * q * (ℓ : ℝ) ^ 2) := by gcongr
      _ = (34 * α) * q * ℓ ^ 2 := by ring
      _ ≤ ((q : ℝ) - 1) * q * ℓ ^ 2 := by gcongr
      _ < (q : ℝ) * q * ℓ ^ 2 := by nlinarith
      _ = (β : ℝ) ^ 2 := by simp only [β]; push_cast; ring
  have h := lemma_2_4 e hα hk hDisj (by exact_mod_cast hgap) A pick T
    (fun a b => hA _ (Ev_loopless e a b) (Ev_connected e a b hℓ hβpos))
  change κ * (ℓ : ℝ) ≤ 6 * T * B + 1
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h' : κ * ℓ * ℓ ≤ (6 * T * B + 1) * ℓ := by nlinarith
  exact le_of_mul_le_mul_right h' (by linarith)

end Podc.SpannerApproximation
