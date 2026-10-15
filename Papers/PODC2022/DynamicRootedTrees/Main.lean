import Papers.PODC2022.DynamicRootedTrees.UpperBound
import Papers.PODC2022.DynamicRootedTrees.LowerBound

/-!
# Main upper bounds

* `lemma_3_5`: Lemma 3.5 of the full version (rounds graph with the paper's parameters
  `m = ⌈√2 n⌉`, `R = ⌈(1 + √2) n⌉`).
* `broadcasts_of_rooted`: the upper bound `⌈(1 + √2) n - 1⌉` for any dynamic network whose rounds
  are rooted and have self-loops (rooted trees are a special case).
* `theorem_3_6`: `t*(𝒯ₙ) ≤ ⌈(1 + √2) n⌉` (full version).
* `advBroadcastTime_trees_le`: `t*(𝒯ₙ) ≤ ⌈(1 + √2) n - 1⌉` (upper half of Theorem 3.1 of the brief
  announcement).
* `theorem_3_1`: `⌈(3n - 1)/2⌉ - 2 ≤ t*(𝒯ₙ) ≤ ⌈(1 + √2) n - 1⌉` (Theorem 3.1 of the brief
  announcement; the lower bound is Theorem 3.7 of the full version, due to Zeiner–Schwarz–Schmid).
* `advBroadcastTime_trees_le_of_sq_lt`: sharpened bound `t*(𝒯ₙ) ≤ n - 1 + m` whenever
  `2 (n-1)² < m (m+1)`.
-/

namespace DynamicRootedTrees

open Cslib.DynNet Finset Real

/-- `m = ⌈√2 n⌉` satisfies `2 n² ≤ m²`. -/
theorem two_mul_sq_le_ceil_sq (n : ℕ) : 2 * n ^ 2 ≤ ⌈√2 * n⌉₊ ^ 2 := by
  have h1 : √2 * n ≤ (⌈√2 * n⌉₊ : ℝ) := Nat.le_ceil _
  have h0 : 0 ≤ √2 * n := by positivity
  have h2 : (2 * n ^ 2 : ℝ) ≤ (⌈√2 * n⌉₊ : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    rwa [mul_pow, Real.sq_sqrt (by norm_num)] at this
  exact_mod_cast h2

/-- `⌈(1 + √2) n⌉ = ⌈√2 n⌉ + n`. -/
theorem ceil_one_add_sqrt_two_mul (n : ℕ) : ⌈(1 + √2) * n⌉₊ = ⌈√2 * n⌉₊ + n := by
  rw [show (1 + √2) * n = √2 * n + (n : ℝ) by ring, Nat.ceil_add_natCast (by positivity)]

/-- `⌈(1 + √2) n - 1⌉ = ⌈√2 n⌉ + (n - 1)` for `n ≥ 1`. -/
theorem ceil_one_add_sqrt_two_mul_sub_one {n : ℕ} (hn : 1 ≤ n) :
    ⌈(1 + √2) * n - 1⌉₊ = ⌈√2 * n⌉₊ + (n - 1) := by
  rw [show (1 + √2) * n - 1 = √2 * n + ((n - 1 : ℕ) : ℝ) by push_cast [hn]; ring,
    Nat.ceil_add_natCast (by positivity)]

/-- The counting inequality of Lemma 3.5 for `R = m + n`. -/
theorem arith_paper {n m : ℕ} (hn : 1 ≤ n) (hsq : 2 * n ^ 2 ≤ m ^ 2) :
    (n - 1) * (n + m - 1) < ∑ t ∈ Icc 1 (m + n), min m t := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  have h2 := two_mul_sum_min m (a + 1)
  rw [Nat.add_sub_cancel, show a + 1 + m - 1 = a + m by omega]
  nlinarith

section Generic

variable {α : Type*} [Fintype α] [DecidableEq α] {G : ℕ → α → α → Prop}
  (hG : ∀ i x, G i x x) {r : ℕ → α} (hr : ∀ t, IsRoot (G t) (r t))

include hG hr in
/-- **Lemma 3.5.** In the rounds graph with `m = ⌈√2 n⌉` and `R = ⌈(1 + √2) n⌉` rounds there is a
node (a process, or one of the rounds `1, …, ⌈√2 n⌉ - 1`) of out-degree at least `n`. -/
theorem lemma_3_5 :
    ∃ v : α ⊕ ℕ, (v.isLeft ∨ ∃ s, v = .inr s ∧ 1 ≤ s ∧ s < ⌈√2 * Fintype.card α⌉₊) ∧
      Fintype.card α ≤
        outdeg G r ⌈√2 * Fintype.card α⌉₊ ⌈(1 + √2) * Fintype.card α⌉₊ v := by
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨r 0⟩
  rw [ceil_one_add_sqrt_two_mul]
  exact exists_outdeg_ge hG hr (by omega) (arith_paper hn (two_mul_sq_le_ceil_sq _))

include hG hr in
/-- **Theorem 3.6 (generic form).** With rooted rounds with self-loops, some process has broadcast
after `⌈(1 + √2) n⌉` rounds. -/
theorem broadcasts_ceil : Broadcasts G ⌈(1 + √2) * Fintype.card α⌉₊ := by
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨r 0⟩
  rw [ceil_one_add_sqrt_two_mul]
  exact broadcasts_of_sum_min hG hr (by omega) (arith_paper hn (two_mul_sq_le_ceil_sq _))

include hG hr in
/-- **Upper bound of Theorem 3.1 (generic form).** With rooted rounds with self-loops, some process
has broadcast after `⌈(1 + √2) n - 1⌉` rounds. -/
theorem broadcasts_ceil_sub_one : Broadcasts G ⌈(1 + √2) * Fintype.card α - 1⌉₊ := by
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨r 0⟩
  rw [ceil_one_add_sqrt_two_mul_sub_one hn]
  apply broadcasts_of_sq_lt hG hr
  have hsq := two_mul_sq_le_ceil_sq (Fintype.card α)
  obtain ⟨a, ha⟩ : ∃ a, Fintype.card α = a + 1 := ⟨Fintype.card α - 1, by omega⟩
  rw [ha] at hsq ⊢
  rw [Nat.add_sub_cancel]
  nlinarith

end Generic

/-- **Upper bound for arbitrary rooted dynamic networks.** If every round has a self-loop at every
node and is rooted (some process reaches everybody), then some process has broadcast after
`⌈(1 + √2) n - 1⌉` rounds. -/
theorem broadcasts_of_rooted {α : Type*} [Fintype α] (G : ℕ → α → α → Prop)
    (hG : ∀ i x, G i x x) (hroot : ∀ t, ∃ r, IsRoot (G t) r) :
    Broadcasts G ⌈(1 + √2) * Fintype.card α - 1⌉₊ := by
  classical
  choose r hr using hroot
  exact broadcasts_ceil_sub_one hG hr

/-- Every sequence of rooted trees with self-loops on `n` nodes has broadcast after
`⌈(1 + √2) n - 1⌉` rounds. -/
theorem broadcasts_trees {n : ℕ} (G : ℕ → Fin n → Fin n → Prop)
    (hG : ∀ i, G i ∈ treesWithLoops n) : Broadcasts G ⌈(1 + √2) * n - 1⌉₊ := by
  have := broadcasts_of_rooted G (fun i => refl_of_mem_treesWithLoops (hG i))
    (fun t => exists_root_of_mem_treesWithLoops (hG t))
  simpa using this

/-- **Theorem 3.6** (full version): `t*(𝒯ₙ) ≤ ⌈(1 + √2) n⌉`. -/
theorem theorem_3_6 (n : ℕ) : advBroadcastTime (treesWithLoops n) ≤ ⌈(1 + √2) * n⌉₊ := by
  classical
  apply advBroadcastTime_le
  intro G hG
  choose r hr using fun t => exists_root_of_mem_treesWithLoops (hG t)
  simpa using broadcasts_ceil (fun i => refl_of_mem_treesWithLoops (hG i)) hr

/-- **Theorem 3.1, upper bound** (brief announcement): `t*(𝒯ₙ) ≤ ⌈(1 + √2) n - 1⌉`. -/
theorem advBroadcastTime_trees_le (n : ℕ) :
    advBroadcastTime (treesWithLoops n) ≤ ⌈(1 + √2) * n - 1⌉₊ :=
  advBroadcastTime_le fun G hG => broadcasts_trees G hG

/-- **Sharpened upper bound** (not in the paper; same proof with optimized parameters): if
`2 (n-1)² < m (m+1)` then `t*(𝒯ₙ) ≤ m + n - 1`. E.g. `t*(𝒯₄) ≤ 7`, `t*(𝒯₁₀) ≤ 22`, whereas
`⌈(1 + √2) n - 1⌉` gives `9` and `24`. -/
theorem advBroadcastTime_trees_le_of_sq_lt {n m : ℕ} (hm : 2 * (n - 1) ^ 2 < m * (m + 1)) :
    advBroadcastTime (treesWithLoops n) ≤ m + (n - 1) := by
  classical
  apply advBroadcastTime_le
  intro G hG
  choose r hr using fun t => exists_root_of_mem_treesWithLoops (hG t)
  simpa using broadcasts_of_sq_lt (fun i => refl_of_mem_treesWithLoops (hG i)) hr
    (by simpa using hm)

/-- `⌈(3n - 1)/2⌉ = ⌊3n/2⌋`. -/
theorem ceil_three_mul_sub_one_div_two (n : ℕ) :
    ⌈(3 * (n : ℝ) - 1) / 2⌉ = ((3 * n / 2 : ℕ) : ℤ) := by
  rw [Int.ceil_eq_iff]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 3 * (2 * k) / 2 = 3 * k by omega]
    push_cast; constructor <;> linarith
  · rw [show 3 * (2 * k + 1) / 2 = 3 * k + 1 by omega]
    push_cast; constructor <;> linarith

/-- **Theorem 3.7** (Zeiner–Schwarz–Schmid): `t*(𝒯ₙ) ≥ ⌈(3n - 1)/2⌉ - 2`. -/
theorem theorem_3_7 (n : ℕ) :
    ⌈(3 * (n : ℝ) - 1) / 2⌉ - 2 ≤ (advBroadcastTime (treesWithLoops n) : ℤ) := by
  rw [ceil_three_mul_sub_one_div_two]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : 3 * n / 2 ≤ 1 := by omega
    omega
  · have := le_advBroadcastTime (fun G hG => broadcasts_trees G hG) (lbSeq_mem n hn)
      (t := 3 * n / 2 - 2) (fun s hs => lbSeq_not_broadcasts n hn s hs)
    omega

/-- **Theorem 3.1** (brief announcement): broadcasting time in dynamic rooted trees is linear,
`⌈(3n - 1)/2⌉ - 2 ≤ t*(𝒯ₙ) ≤ ⌈(1 + √2) n - 1⌉`. -/
theorem theorem_3_1 (n : ℕ) :
    ⌈(3 * (n : ℝ) - 1) / 2⌉ - 2 ≤ (advBroadcastTime (treesWithLoops n) : ℤ) ∧
      advBroadcastTime (treesWithLoops n) ≤ ⌈(1 + √2) * n - 1⌉₊ :=
  ⟨theorem_3_7 n, advBroadcastTime_trees_le n⟩

end DynamicRootedTrees
