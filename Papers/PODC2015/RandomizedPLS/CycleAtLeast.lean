import Papers.PODC2015.RandomizedPLS.Biconnectivity

/-!
# Longest cycle, `cycle-at-least-c`: lower bounds of Theorem 5.4

`G = Wheel.G n c` (Figure 2a restricted to `v₀ … v_{c-1}`): a `c`-cycle `v₀ … v_{c-1}`, plus the
edges `{v₀, v_j}` for `j = 2, …, n-1`, `j ≠ c-1` (so `v_c, …, v_{n-1}` are pendant nodes at
`v₀`). It contains the `c`-cycle (`cycleAtLeast_G`). The copies are the cycle edges
`H_k = {v_{3k+1}, v_{3k+2}}`, `k < ⌊c/3⌋` (`Wheel.K`).

**The paper's `H_1` is a typo.** The paper takes `H_1 = G_e{v₀, v₁}` and `H_i = G_e{v_{3i},
v_{3i+1}}` (`i ≥ 2`). Since `v₀` is adjacent to every node, `H_1` is not independent of any
other `H_i` (Definition 4.1), see `printed_H1_not_independent`; the crossing would not even be a
simple graph. With `H_1 = G_e{v₁, v₂}` (as in Theorem 5.2) the proof goes through.

Crossing `{v_a, v_{a+1}}` and `{v_b, v_{b+1}}` (`a < b`) splits the `c`-cycle into the cycles
`v_{a+1} … v_b` and `v_{b+1} … v_{c-1} v₀ v₁ … v_a`, joined only through `v₀`. Every simple cycle
through the cut vertex `v₀` stays in `v₀` plus one component of `G - v₀`
(`cycle_support_of_cut`), so it has at most `max(b - a + 1, c - (b - a)) < c` nodes
(`not_cycleAtLeast_cross`).
-/

namespace Podc.RandomizedPLS

open Classical Wheel

variable {S : Type}

/-- `cycle-at-least-k` (Section 5.3): some simple cycle has at least `k` nodes. -/
def CycleAtLeast (k : ℕ) (c : Config S) : Prop :=
  ∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ k ≤ p.length

/-- `cycle-at-least-c(G) = TRUE`: `v₀ v₁ … v_{c-1}` is a cycle with `c` nodes. -/
lemma cycleAtLeast_G {n c : ℕ} (hc : 3 ≤ c) (hcn : c ≤ n) : CycleAtLeast c (G n c) := by
  let f : ℕ → Fin n := fun k => ⟨min k (n - 1), by omega⟩
  obtain ⟨v, p, hp, hl⟩ := exists_cycle_of_seq (G := (G n c).graph) f (c - 1) (by omega)
    (fun i hi j hj h => by simp only [f, Fin.ext_iff] at h; omega)
    (fun i hi => by rw [G_adj]; simp only [wAdj, f]; omega)
    (by rw [G_adj]; simp only [wAdj, f]; omega)
  exact ⟨v, p, hp, by omega⟩

/-- The edges of the crossing that avoid `v₀`: uncrossed cycle edges and the two new edges. -/
lemma Wheel.cross_adj_ne_zero {n c : ℕ} {hcn : c ≤ n} {i j : Fin (c / 3)} (hij : i ≠ j)
    {x y : Fin n} (hxy : ((K n c hcn).cross i j hij).graph.Adj x y) (hx : x.val ≠ 0)
    (hy : y.val ≠ 0) :
    (x.val < c ∧ y.val < c ∧ (x.val + 1 = y.val ∨ y.val + 1 = x.val) ∧
        ¬ arcN (3 * i.val + 1) (3 * j.val + 1) x.val y.val) ∨
      (x.val = 3 * i.val + 1 ∧ y.val = 3 * j.val + 2) ∨
      (x.val = 3 * j.val + 2 ∧ y.val = 3 * i.val + 1) ∨
      (x.val = 3 * j.val + 1 ∧ y.val = 3 * i.val + 2) ∨
      (x.val = 3 * i.val + 2 ∧ y.val = 3 * j.val + 1) := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rw [cross_adj_val] at hxy
  rcases hxy with ⟨h1, h2⟩ | h
  · left
    simp only [wAdj] at h1
    exact ⟨by omega, by omega, by omega, h2⟩
  · right
    simp only [sw] at h
    split_ifs at h with c1 c2 c3 c4 <;> simp only [arcN] at h <;> omega

/-- In the crossings, every simple cycle has fewer than `c` nodes. -/
lemma not_cycleAtLeast_cross {n c : ℕ} (hcn : c ≤ n) {i j : Fin (c / 3)} (hij : i ≠ j) :
    ¬ CycleAtLeast c ((K n c hcn).cross i j hij) := by
  rintro ⟨v, p, hp, hl⟩
  have hi := i.2
  have hj := j.2
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  set A := 3 * i.val + 1 with hA
  set B := 3 * j.val + 1 with hB
  set lo := min A B with hlo
  set hi := max A B with hhi
  let z : Fin n := ⟨0, by omega⟩
  -- the blocks of `G - v₀` in the crossing: `v_{lo+1} … v_hi`, the rest of the cycle, pendants
  let β : Fin n → ℕ := fun x =>
    if lo < x.val ∧ x.val ≤ hi then 0 else if x.val < c then 1 else x.val + 2
  have hβ : ∀ x y, ((K n c hcn).cross i j hij).graph.Adj x y → x ≠ z → y ≠ z → β x = β y := by
    intro x y hxy hx hy
    have hx' : x.val ≠ 0 := fun h => hx (Fin.ext h)
    have hy' : y.val ≠ 0 := fun h => hy (Fin.ext h)
    have hlohi : lo + 3 ≤ hi ∧ 1 ≤ lo ∧ hi + 2 ≤ c := by omega
    have hcases : (lo < x.val ∧ x.val ≤ hi ↔ lo < y.val ∧ y.val ≤ hi) ∧
        (x.val < c ↔ y.val < c) ∧ (c ≤ x.val → x.val = y.val) := by
      rcases cross_adj_ne_zero hij hxy hx' hy' with ⟨h1, h2, h3, h4⟩ | h | h | h | h
      · simp only [arcN] at h4
        rcases h3 with h3 | h3 <;> omega
      all_goals omega
    simp only [β]
    split_ifs <;> omega
  obtain ⟨k, l, hnd, hlen, hmem⟩ := cycle_support_of_cut z β hβ p hp
  let T : Finset ℕ :=
    if k = 0 then insert 0 (Finset.Ioc lo hi) else if k = 1 then Finset.range c \ Finset.Ioc lo hi
    else {0, k - 2}
  have hT : ∀ x ∈ l, x.val ∈ T := by
    intro x hx
    rcases hmem x hx with rfl | hk
    · simp only [T]; split_ifs <;> simp [z]; omega
    · simp only [β] at hk
      simp only [T]
      split_ifs at hk ⊢ <;> simp [Finset.mem_Ioc] <;> omega
  have hcard : T.card < c := by
    simp only [T]
    split_ifs
    · refine lt_of_le_of_lt (Finset.card_insert_le _ _) ?_
      rw [Nat.card_Ioc]; omega
    · refine lt_of_lt_of_le (Finset.card_lt_card (Finset.sdiff_ssubset ?_ ?_)) (by simp)
      · intro x hx; simp [Finset.mem_Ioc] at hx ⊢; omega
      · exact ⟨hi, by simp [Finset.mem_Ioc]; omega⟩
    · exact lt_of_le_of_lt Finset.card_le_two (by omega)
  have := length_le_of_vals hnd T hT
  omega

/-- The crossings refute `(F_con, cycle-at-least-c)`. -/
lemma refuted_cross_cycleAtLeast {n c : ℕ} (hc : 3 ≤ c) (hcn : c ≤ n) {i j : Fin (c / 3)}
    (hij : i ≠ j) : Refuted Fcon (CycleAtLeast c) ((K n c hcn).cross i j hij) :=
  Or.inl ⟨cross_connected hij (by omega), not_cycleAtLeast_cross hcn hij⟩

lemma fcon_wheelG {n c : ℕ} (hn : 0 < n) : Fcon (G n c) :=
  connected_of_descent (G := (G n c).graph) (⟨0, hn⟩ : Fin n) (fun x : Fin n => x.val)
    (fun x hx => ⟨⟨0, hn⟩, by
      have hx' : x.val ≠ 0 := fun h => hx (Fin.ext h)
      rw [G_adj]; simp only [wAdj, true_or, or_true, and_true]; omega, by
      have hx' : x.val ≠ 0 := fun h => hx (Fin.ext h)
      simp only; omega⟩)

/-- **Theorem 5.4 of [BFP15]** (deterministic lower bound). Let `F` be any family containing the
connected configurations with distinct identities (e.g. `F_con`). For `c ≥ 3`, every proof-labeling
scheme for `(F, cycle-at-least-c)` whose labels on legal `n`-node configurations have at most
`κ(n)` bits satisfies `log₂ ⌊c/3⌋ ≤ 2 (κ(n) + 1)` for every `n ≥ c`, i.e. `κ = Ω(log c)`. -/
theorem thm_5_4_det {F : Config ℕ → Prop} (hFF : ∀ c, Fcon c → Function.Injective c.state → F c)
    {c : ℕ} {ver : Verifier ℕ} {prover : ∀ G : Config ℕ, G.V → List Bool}
    (h : IsPLS ver prover F (CycleAtLeast c)) (κ : ℕ → ℕ)
    (hκ : LabelBound prover F (CycleAtLeast c) (fun G => κ (Fintype.card G.V)))
    (hc : 3 ≤ c) (n : ℕ) (hcn : c ≤ n) :
    Real.logb 2 (c / 3 : ℕ) ≤ 2 * (κ n + 1) := by
  have hF := hFF _ (fcon_wheelG (c := c) (show 0 < n by omega)) (wheelG_state_injective n c)
  have hP := cycleAtLeast_G hc hcn
  have := thm_4_4_log h hF hP (K n c hcn) (κ n)
    (fun v => by simpa [card_wheelG] using hκ _ hF hP v)
    (fun i j hij => (refuted_cross_cycleAtLeast hc hcn hij).mono hFF (wheelG_state_injective n c))
  simpa [K_s] using this

/-- **Theorem 5.4 of [BFP15]** (randomized lower bound, one-sided schemes). Let `F` be any family
containing the connected configurations with distinct identities. For `c ≥ 3`, every
one-sided RPLS for `(F, cycle-at-least-c)` whose certificates on legal `n`-node
configurations have at most `κ(n)` bits satisfies `log₂ ⌊c/3⌋ ≤ 2 · 2^(κ(n)+1)` for every
`n ≥ c`, i.e. `κ = Ω(log log c)`. -/
theorem thm_5_4_rand {F : Config ℕ → Prop}
    (hFF : ∀ c, Fcon c → Function.Injective c.state → F c)
    {c : ℕ} {L : Type} {σ : RScheme ℕ L} {prover : ∀ G : Config ℕ, G.V → L}
    (h : IsOneSided σ prover F (CycleAtLeast c)) (κ : ℕ → ℕ)
    (hκ : CertBound σ prover F (CycleAtLeast c) (fun G => κ (Fintype.card G.V)))
    (hc : 3 ≤ c) (n : ℕ) (hcn : c ≤ n) :
    Real.logb 2 (c / 3 : ℕ) ≤ 2 * 2 ^ (κ n + 1) := by
  have hF := hFF _ (fcon_wheelG (c := c) (show 0 < n by omega)) (wheelG_state_injective n c)
  have hP := cycleAtLeast_G hc hcn
  have := prop_4_8_log h hF hP (K n c hcn) (κ n)
    (fun v ω i hi => by simpa [card_wheelG] using hκ _ hF hP v ω i hi)
    (fun i j hij => (refuted_cross_cycleAtLeast hc hcn hij).mono hFF (wheelG_state_injective n c))
  simpa [K_s] using this

/-- **The printed `H_1 = G_e{v₀, v₁}` is not admissible.** In `G` (with `c ≥ 8`), the node `v₀` of
the printed `H_1` and the node `v₆` of `H_2 = G_e{v₆, v₇}` are adjacent, so they cannot lie in two
distinct copies: Definition 4.1 requires distinct copies to be independent (no edge between
them). -/
lemma printed_H1_not_independent {n c : ℕ} (hc : 8 ≤ c) (hcn : c ≤ n) {r : ℕ}
    (K' : Copies (G n c) r) (i j : Fin r) (a b : K'.W)
    (ha : K'.emb i a = ⟨0, by omega⟩) (hb : K'.emb j b = ⟨6, by omega⟩) : i = j := by
  by_contra hij
  apply K'.indep i j a b hij
  rw [ha, hb]
  change (G n c).graph.Adj _ _
  rw [G_adj]; simp [wAdj]

end Podc.RandomizedPLS
