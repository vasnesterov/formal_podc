import Papers.PODC2022.DynamicRootedTrees.Defs

/-!
# The linear upper bound (Section 3.1 of the full version)

We work with an arbitrary finite process type `α` with `n = |α|`, a dynamic network
`G : ℕ → α → α → Prop` with a self-loop at every node in every round (`hG`) and a root `r t` of every
round `t` (`hr`, i.e. every process is reachable from `r t` in `G t`). Rooted trees with self-loops
are a special case (`Main.lean`); nothing else about trees is used.

The *rounds graph* (Definition 3.4) is parametrised here by the threshold `m` (the paper:
`m = ⌈√2 n⌉`; round nodes `s < m` may have out-edges) and the number of rounds `R` (the paper:
`R = ⌈(1 + √2) n⌉`). The generic counting lemma (`exists_outdeg_ge`, Lemma 3.5) only needs
`(n - 1)(n + m - 1) < ∑_{t=1}^{R} min(m, t)`; this lets us derive both the full version's
`⌈(1+√2)n⌉` (Theorem 3.6) and the brief announcement's sharper `⌈(1+√2)n - 1⌉` (Theorem 3.1).
-/

namespace DynamicRootedTrees

open Cslib.DynNet Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {G : ℕ → α → α → Prop}
  (hG : ∀ i x, G i x x) {r : ℕ → α} (hr : ∀ t, IsRoot (G t) (r t))

include hG hr in
/-- Strengthening of Lemma 3.3 used in its proof: counting rounds `t` whose root is not in
`I_{t+1}^{t₂}(x)`. -/
theorem card_filter_root_notMem_succ_add_one_le (x : α) :
    ∀ d t₁ t₂ : ℕ, t₁ + d = t₂ + 1 →
      ((Icc t₁ t₂).filter (fun t => r t ∉ inNbhd G (t + 1) t₂ x)).card + 1 ≤
        (inNbhd G t₁ t₂ x).card := by
  intro d
  induction d with
  | zero =>
    intro t₁ t₂ h
    obtain rfl : t₁ = t₂ + 1 := by omega
    simp [inNbhd_succ_self]
  | succ d ih =>
    intro t₁ t₂ h
    have h₁ : t₁ ≤ t₂ := by omega
    have hI : Icc t₁ t₂ = insert t₁ (Icc (t₁ + 1) t₂) := by
      ext t; simp only [mem_Icc, mem_insert]; omega
    have ih' := ih (t₁ + 1) t₂ (by omega)
    have hmono : (inNbhd G (t₁ + 1) t₂ x).card ≤ (inNbhd G t₁ t₂ x).card :=
      card_le_card (inNbhd_mono hG (Nat.le_succ t₁) le_rfl x)
    rw [hI, filter_insert]
    split_ifs with hroot
    · omega
    · rw [card_insert_of_notMem (by simp)]
      have := card_inNbhd_lt_of_root_notMem hG h₁ (hr t₁) hroot
      omega

include hG hr in
/-- **Lemma 3.3.** For `t₁ ≤ t₂ + 1`:
`|{t : t₁ ≤ t ≤ t₂, r_t ∉ I_{t₁}^{t₂}(x)}| + 1 ≤ |I_{t₁}^{t₂}(x)|`.
(The paper assumes `t₁ ≤ t₂` but applies the lemma with `t₁ = 1`, `t₂ = 0`; it holds in that case
too.) -/
theorem lemma_3_3 (x : α) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂ + 1) :
    ((Icc t₁ t₂).filter (fun t => r t ∉ inNbhd G t₁ t₂ x)).card + 1 ≤
      (inNbhd G t₁ t₂ x).card := by
  refine le_trans ?_ (card_filter_root_notMem_succ_add_one_le hG hr x (t₂ + 1 - t₁) t₁ t₂
    (by omega))
  apply Nat.add_le_add_right
  apply card_le_card
  intro t ht
  rw [mem_filter, mem_Icc] at ht ⊢
  exact ⟨ht.1, fun hmem => ht.2 (inNbhd_mono hG (by omega) le_rfl x hmem)⟩

/-! ### The rounds graph -/

noncomputable section RoundsGraph

variable (G r) (m R : ℕ)

/-- **Definition 3.4 (rounds graph)**, with threshold `m` and `R` rounds. Vertices: processes
`Sum.inl p` and rounds `Sum.inr t`. Edges: `p → t` if `1 ≤ t ≤ R` and `p ∈ I_1^{t-1}(r_t)`; and
`s → t` if `1 ≤ s < m`, `s < t ≤ R` and `r_s ∈ I_1^{t-1}(r_t)`. (Round vertices outside `[1, R]`
are isolated; the paper has no such vertices.) -/
def RoundsAdj : α ⊕ ℕ → α ⊕ ℕ → Prop
  | .inl p, .inr t => 1 ≤ t ∧ t ≤ R ∧ p ∈ inNbhd G 1 (t - 1) (r t)
  | .inr s, .inr t => 1 ≤ s ∧ s < m ∧ s < t ∧ t ≤ R ∧ r s ∈ inNbhd G 1 (t - 1) (r t)
  | _, .inl _ => False

instance : DecidableRel (RoundsAdj G r m R) := fun v w => by
  cases v <;> cases w <;> unfold RoundsAdj <;> infer_instance

/-- The rounds graph as a `Digraph`. -/
def roundsGraph : Digraph (α ⊕ ℕ) where
  Adj := RoundsAdj G r m R

/-- Out-neighbours of a vertex of the rounds graph (all of them are rounds in `[1, R]`). -/
def outRounds (v : α ⊕ ℕ) : Finset ℕ := (Icc 1 R).filter (fun t => RoundsAdj G r m R v (.inr t))

theorem mem_outRounds {v : α ⊕ ℕ} {t : ℕ} :
    t ∈ outRounds G r m R v ↔ (roundsGraph G r m R).Adj v (.inr t) := by
  unfold outRounds roundsGraph
  rw [mem_filter, and_iff_right_iff_imp, mem_Icc]
  cases v <;> simp [RoundsAdj] <;> omega

/-- The out-degree of a vertex of the rounds graph. -/
def outdeg (v : α ⊕ ℕ) : ℕ := (outRounds G r m R v).card

end RoundsGraph

/-- `∑_{t=1}^{m+k} min(m, t) = m(m+1)/2 + k m`, in doubled form. -/
theorem two_mul_sum_min (m k : ℕ) :
    2 * ∑ t ∈ Icc 1 (m + k), min m t = m * (m + 1) + 2 * k * m := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, mul_zero, zero_mul]
    rw [sum_congr rfl (g := id) (fun t ht => by simp at ht; simp [ht.2])]
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_Icc_succ_top (by omega), mul_add, ih]; simp; ring
  | succ k ih =>
    rw [← Nat.add_assoc, sum_Icc_succ_top (by omega), mul_add, ih]
    rw [min_eq_left (by omega)]; ring

theorem arith_identity (n : ℕ) {m : ℕ} (hm : 0 < m) :
    (n - 1) * (n + m - 1) = n * (n - 1) + (m - 1) * (n - 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show a + 1 + (b + 1) - 1 = a + 1 + b by omega]; ring

include hG hr in
/-- **Lemma 3.5 (generic form).** If `m ≤ R` and `(n-1)(n+m-1) < ∑_{t=1}^{R} min(m,t)`, then some
vertex of the rounds graph — a process, or a round `s` with `1 ≤ s < m` — has out-degree at
least `n`. -/
theorem exists_outdeg_ge {m R : ℕ} (hmR : m ≤ R)
    (hsum : (Fintype.card α - 1) * (Fintype.card α + m - 1) < ∑ t ∈ Icc 1 R, min m t) :
    ∃ v : α ⊕ ℕ, (v.isLeft ∨ ∃ s, v = .inr s ∧ 1 ≤ s ∧ s < m) ∧
      Fintype.card α ≤ outdeg G r m R v := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0; simp at hsum
  by_contra! hcon
  have hp : ∀ p : α, outdeg G r m R (.inl p) ≤ Fintype.card α - 1 := fun p => by
    have := hcon (.inl p) (Or.inl rfl); omega
  have hs : ∀ s ∈ Ico 1 m, outdeg G r m R (.inr s) ≤ Fintype.card α - 1 := fun s hs => by
    rw [mem_Ico] at hs
    have := hcon (.inr s) (Or.inr ⟨s, rfl, hs⟩); omega
  -- double counting: the sum of in-degrees of the rounds equals the sum of out-degrees
  have hdc₁ : ∑ t ∈ Icc 1 R, (univ.filter (fun p => RoundsAdj G r m R (.inl p) (.inr t))).card =
      ∑ p : α, outdeg G r m R (.inl p) := by
    simp only [outdeg, outRounds, card_filter]
    exact sum_comm
  have hdc₂ : ∑ t ∈ Icc 1 R, ((Ico 1 m).filter (fun s => RoundsAdj G r m R (.inr s) (.inr t))).card =
      ∑ s ∈ Ico 1 m, outdeg G r m R (.inr s) := by
    simp only [outdeg, outRounds, card_filter]
    exact sum_comm
  -- lower bound on in-degrees (via Lemma 3.3)
  have hin : ∀ t ∈ Icc 1 R, min m t ≤
      (univ.filter (fun p => RoundsAdj G r m R (.inl p) (.inr t))).card +
      ((Ico 1 m).filter (fun s => RoundsAdj G r m R (.inr s) (.inr t))).card := by
    intro t ht
    rw [mem_Icc] at ht
    have h33 := lemma_3_3 hG hr (r t) (t₁ := 1) (t₂ := t - 1) (by omega)
    have hP : univ.filter (fun p => RoundsAdj G r m R (.inl p) (.inr t)) =
        inNbhd G 1 (t - 1) (r t) := by
      ext p; rw [mem_filter]; simp [RoundsAdj, ht.1, ht.2]
    have hS : (Ico 1 (min m t)).filter (fun s => r s ∈ inNbhd G 1 (t - 1) (r t)) ⊆
        (Ico 1 m).filter (fun s => RoundsAdj G r m R (.inr s) (.inr t)) := by
      intro s hs
      rw [mem_filter, mem_Ico, lt_min_iff] at hs
      rw [mem_filter, mem_Ico]
      exact ⟨⟨hs.1.1, hs.1.2.1⟩, hs.1.1, hs.1.2.1, hs.1.2.2, ht.2, hs.2⟩
    have hN : (Ico 1 (min m t)).filter (fun s => r s ∉ inNbhd G 1 (t - 1) (r t)) ⊆
        (Icc 1 (t - 1)).filter (fun s => r s ∉ inNbhd G 1 (t - 1) (r t)) := by
      intro s hs
      rw [mem_filter, mem_Ico, lt_min_iff] at hs
      rw [mem_filter, mem_Icc]
      exact ⟨⟨hs.1.1, by omega⟩, hs.2⟩
    have hsplit := card_filter_add_card_filter_not (s := Ico 1 (min m t))
      (fun s => r s ∈ inNbhd G 1 (t - 1) (r t))
    have h1 := card_le_card hS
    have h2 := card_le_card hN
    rw [Nat.card_Ico] at hsplit
    rw [hP]
    have : 1 ≤ min m t := le_min hm0 ht.1
    omega
  have hlow := sum_le_sum hin
  rw [sum_add_distrib, hdc₁, hdc₂] at hlow
  have hup₁ : ∑ p : α, outdeg G r m R (.inl p) ≤ Fintype.card α * (Fintype.card α - 1) := by
    simpa using sum_le_sum (fun p _ => hp p) (s := (univ : Finset α))
  have hup₂ : ∑ s ∈ Ico 1 m, outdeg G r m R (.inr s) ≤ (m - 1) * (Fintype.card α - 1) := by
    simpa using sum_le_sum hs
  have := arith_identity (Fintype.card α) hm0
  omega

omit [DecidableEq α] in
include hG in
/-- The counting argument of Theorem 3.6: if the root of each round `t ∈ S` (with `t ≥ 1`) has
heard of `z` before round `t`, then `z` reaches at least `min(n, |S ∩ [1, K]|)` processes after
`K` rounds. -/
theorem min_card_le_card_outNbhd (z : α) (S : Finset ℕ)
    (hS : ∀ t ∈ S, 1 ≤ t ∧ IsRoot (G t) (r t) ∧ r t ∈ outNbhd G 1 (t - 1) z) :
    ∀ K : ℕ, min (Fintype.card α) (S.filter (· ≤ K)).card ≤ (outNbhd G 1 K z).card := by
  intro K
  induction K with
  | zero =>
    have : S.filter (· ≤ 0) = ∅ := by
      ext t; simp only [mem_filter, Finset.notMem_empty, iff_false, not_and, Nat.le_zero]
      intro ht h0; have := (hS t ht).1; omega
    rw [this]; simp
  | succ K ih =>
    have hmono : (outNbhd G 1 K z).card ≤ (outNbhd G 1 (K + 1) z).card :=
      card_le_card (outNbhd_mono hG le_rfl (Nat.le_succ K) z)
    by_cases hK : K + 1 ∈ S
    · have hfil : S.filter (· ≤ K + 1) = insert (K + 1) (S.filter (· ≤ K)) := by
        ext t; simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨h1, h2⟩; by_cases h : t = K + 1
          · exact Or.inl h
          · exact Or.inr ⟨h1, by omega⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hK, le_rfl⟩
          · exact ⟨h1, by omega⟩
      rw [hfil, card_insert_of_notMem (by simp)]
      obtain ⟨-, hroot, hmem⟩ := hS _ hK
      rw [Nat.add_sub_cancel] at hmem
      by_cases hfull : (outNbhd G 1 K z).card < Fintype.card α
      · have := card_outNbhd_lt_of_root_mem hG hroot hmem hfull
        omega
      · omega
    · have hfil : S.filter (· ≤ K + 1) = S.filter (· ≤ K) := by
        ext t; simp only [mem_filter]
        constructor
        · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
          rcases Nat.lt_or_ge K t with h | h
          · exact absurd (show t = K + 1 by omega ▸ h1) hK
          · exact h
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      rw [hfil]; omega

include hG hr in
/-- **Theorem 3.6 (generic form).** If `m ≤ R` and `(n-1)(n+m-1) < ∑_{t=1}^{R} min(m,t)`, then some
process has broadcast after `R` rounds. -/
theorem broadcasts_of_sum_min {m R : ℕ} (hmR : m ≤ R)
    (hsum : (Fintype.card α - 1) * (Fintype.card α + m - 1) < ∑ t ∈ Icc 1 R, min m t) :
    Broadcasts G R := by
  obtain ⟨v, -, hdeg⟩ := exists_outdeg_ge hG hr hmR hsum
  -- the process `z` represented by `v` (the process itself, or the root of the round)
  obtain ⟨z, hz⟩ : ∃ z : α, ∀ t ∈ outRounds G r m R v,
      1 ≤ t ∧ IsRoot (G t) (r t) ∧ r t ∈ outNbhd G 1 (t - 1) z := by
    rcases v with p | s
    · refine ⟨p, fun t ht => ?_⟩
      unfold outRounds at ht
      rw [mem_filter, mem_Icc] at ht
      exact ⟨ht.1.1, hr t, mem_outNbhd_iff_mem_inNbhd.2 ht.2.2.2⟩
    · refine ⟨r s, fun t ht => ?_⟩
      unfold outRounds at ht
      rw [mem_filter, mem_Icc] at ht
      exact ⟨ht.1.1, hr t, mem_outNbhd_iff_mem_inNbhd.2 ht.2.2.2.2.2⟩
  have key := min_card_le_card_outNbhd hG z _ hz R
  have hfil : (outRounds G r m R v).filter (· ≤ R) = outRounds G r m R v := by
    apply filter_true_of_mem; intro t ht; unfold outRounds at ht; simp at ht; omega
  unfold outdeg at hdeg
  rw [hfil, min_eq_left hdeg] at key
  have huniv : outNbhd G 1 R z = univ :=
    eq_univ_of_card _ (le_antisymm (card_le_univ _) key)
  refine ⟨z, fun y => ?_⟩
  have hy : y ∈ outNbhd G 1 R z := huniv ▸ mem_univ y
  rw [mem_outNbhd] at hy
  simpa using hy.2

include hG hr in
/-- **Sharpened upper bound.** If `2 (n-1)² < m (m+1)`, then some process has broadcast after
`n - 1 + m` rounds. (With the least such `m ≈ √2 (n-1)`, this gives `≈ (1+√2)(n-1)`.) -/
theorem broadcasts_of_sq_lt {m : ℕ} (hm : 2 * (Fintype.card α - 1) ^ 2 < m * (m + 1)) :
    Broadcasts G (m + (Fintype.card α - 1)) := by
  obtain ⟨a, ha⟩ : ∃ a, Fintype.card α = a + 1 :=
    ⟨Fintype.card α - 1, by have := Fintype.card_pos_iff.2 ⟨r 0⟩; omega⟩
  have h2 := two_mul_sum_min m a
  rw [ha, Nat.add_sub_cancel] at hm ⊢
  apply broadcasts_of_sum_min hG hr (m := m) (by omega)
  rw [ha, Nat.add_sub_cancel, show a + 1 + m - 1 = a + m by omega]
  nlinarith

end DynamicRootedTrees
