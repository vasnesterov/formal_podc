import Papers.PODC2026.DelayOptimalOrderFairness.Defs

/-!
# Theorem 5.1: the feasible AOF region

Cai, Goharshady. *Brief Announcement: Delay-Optimal Transaction Order Fairness.* PODC 2026, §5.

We first prove a counting version (`not_hasCycle_of_count`): if `k θ > Δ` and every AOF edge is
missed by fewer than `|H| / k` honest nodes, the AOF graph is acyclic. Theorem 5.1 (`theorem_5_1`)
follows, as does the "topological sorting" consequence (`theorem_5_1_order`).

The counting version also shows that the cycle construction of Theorem 5.2 cannot work for every
fixed number of nodes `n` (`theorem_5_2_fixed_n_false`).
-/

namespace Podc.DelayOptimalOrderFairness

open Finset Relation

variable {Node Tx : Type*} [Fintype Node]

/-- Along `t ≤ k` steps all supported by honest node `p`, `p`'s timestamp grows by `t θ`. -/
private theorem ts_add_le {ts : Profile Node Tx} {θ : ℝ} {g : ℕ → Tx} {p : Node} {j k : ℕ}
    (hp : ∀ t < k, p ∈ supp ts θ (g (j + t)) (g (j + t + 1))) :
    ∀ t ≤ k, ts p (g j) + t * θ ≤ ts p (g (j + t)) := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := ih (by omega)
    have h2 := mem_supp.1 (hp t (by omega))
    push_cast
    rw [← add_assoc j t 1]
    linarith

/-- **Counting form of Theorem 5.1.** In a `Δ`-synchronous profile, if `k θ > Δ` and every edge
of the `(θ, φ)`-AOF graph is missed by fewer than a `1/k` fraction of the honest nodes, then the
AOF graph is acyclic. (After `k` edges some honest node supported all of them, so the earliest
honest receive time strictly increases: `s_j < s_{j+k}`.) -/
theorem not_hasCycle_of_count [DecidableEq Node] {H : Finset Node} {Δ θ φ : ℝ} {ts : Profile Node Tx}
    (hsync : Synchronous H Δ ts) {k : ℕ} (hθ : Δ < k * θ)
    (hcount : ∀ x y, Prec ts θ φ x y → k * (H \ supp ts θ x y).card < H.card) :
    ¬ HasCycle (Prec ts θ φ) := by
  rcases H.eq_empty_or_nonempty with rfl | hne
  · rintro ⟨x, hx⟩
    cases hx with
    | single hy => simpa using hcount _ _ hy
    | tail _ hy => simpa using hcount _ _ hy
  -- `s tx` = earliest honest receive time
  let s : Tx → ℝ := fun y => H.inf' hne fun i => ts i y
  refine not_hasCycle_of_kstep s k fun g hg j => ?_
  -- honest nodes missing one of the edges `j + t → j + t + 1`, `t < k`
  let B : Finset Node := (range k).biUnion fun t => H \ supp ts θ (g (j + t)) (g (j + t + 1))
  have hB : B.card < H.card := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [B] using hne.card_pos
    have h1 : B.card ≤ ∑ t ∈ range k, (H \ supp ts θ (g (j + t)) (g (j + t + 1))).card :=
      card_biUnion_le
    have h2 : ∑ t ∈ range k, k * (H \ supp ts θ (g (j + t)) (g (j + t + 1))).card <
        ∑ t ∈ range k, H.card :=
      sum_lt_sum_of_nonempty (nonempty_range_iff.2 hk.ne') fun t _ => hcount _ _ (hg _)
    rw [← mul_sum, sum_const, card_range, smul_eq_mul] at h2
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  obtain ⟨p, hpH, hpB⟩ : ∃ p ∈ H, p ∉ B := by
    by_contra h
    push Not at h
    exact absurd (card_le_card h) (not_le.2 hB)
  have hp : ∀ t < k, p ∈ supp ts θ (g (j + t)) (g (j + t + 1)) := by
    intro t ht
    by_contra hn
    exact hpB (mem_biUnion.2 ⟨t, mem_range.2 ht, mem_sdiff.2 ⟨hpH, hn⟩⟩)
  have hgrow := ts_add_le hp k le_rfl
  have hlo : s (g j) ≤ ts p (g j) := inf'_le _ hpH
  have hhi : ts p (g (j + k)) - Δ ≤ s (g (j + k)) :=
    le_inf' _ _ fun q hq => by linarith [hsync p hpH q hq (g (j + k))]
  linarith

/-- **Theorem 5.1 (Feasible AOF region).** In a `Δ_sync`-synchronous network with honest fraction
`h` (`|H| = h n`), fix a positive integer `k`. If `θ > Δ_sync / k` and `φ > 1 - h / k`, then the
`(θ, φ)`-AOF graph is acyclic for every execution profile.

The paper also assumes `1 - h/k ≤ h` (non-emptiness of the useful range); it is not needed. We
assume `n ≥ 1` (for `n = 0` every pair is an edge). -/
theorem theorem_5_1 [Nonempty Node] {H : Finset Node} {Δ θ φ h : ℝ} {ts : Profile Node Tx}
    (hH : (H.card : ℝ) = h * Fintype.card Node) (hsync : Synchronous H Δ ts)
    {k : ℕ} (hk : 0 < k) (hθ : Δ / k < θ) (hφ : 1 - h / k < φ) :
    ¬ HasCycle (Prec ts θ φ) := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine not_hasCycle_of_count hsync (by rwa [div_lt_iff₀' hk'] at hθ) fun x y hxy => ?_
  have hn : (0 : ℝ) < Fintype.card Node := by exact_mod_cast Fintype.card_pos
  have hsub : H \ supp ts θ x y ⊆ univ \ supp ts θ x y := sdiff_subset_sdiff (subset_univ _) le_rfl
  have hc : ((H \ supp ts θ x y).card : ℝ) ≤ Fintype.card Node - (supp ts θ x y).card := by
    have := card_le_card hsub
    rw [card_sdiff_of_subset (subset_univ _), card_univ] at this
    have h2 := card_le_univ (supp ts θ x y)
    rw [← Nat.cast_sub h2]; exact_mod_cast this
  have hxy' : φ * Fintype.card Node ≤ (supp ts θ x y).card := hxy
  have : (k : ℝ) * (H \ supp ts θ x y).card < H.card := by
    rw [hH]
    have h1 : (1 - φ) * Fintype.card Node < h / k * Fintype.card Node :=
      mul_lt_mul_of_pos_right (by linarith) hn
    have h2 : (k : ℝ) * (h / k * Fintype.card Node) = h * Fintype.card Node := by
      field_simp
    calc (k : ℝ) * (H \ supp ts θ x y).card ≤ k * ((1 - φ) * Fintype.card Node) := by
          gcongr; linarith
      _ < k * (h / k * Fintype.card Node) := by gcongr
      _ = h * Fintype.card Node := h2
  exact_mod_cast this

/-- **Theorem 5.1, second sentence**: "Hence AOF can be achieved by deterministic topological
sorting": in the feasible region some strict total (ledger) order respects every AOF constraint. -/
theorem theorem_5_1_order [Nonempty Node] {H : Finset Node} {Δ θ φ h : ℝ} {ts : Profile Node Tx}
    (hH : (H.card : ℝ) = h * Fintype.card Node) (hsync : Synchronous H Δ ts)
    {k : ℕ} (hk : 0 < k) (hθ : Δ / k < θ) (hφ : 1 - h / k < φ) :
    ∃ r : Tx → Tx → Prop, IsStrictTotalOrder Tx r ∧ ∀ x y, Prec ts θ φ x y → r x y :=
  (exists_strictTotalOrder_iff_not_hasCycle _).2 (theorem_5_1 hH hsync hk hθ hφ)

/-- **Theorem 5.2 is false for a fixed number of nodes.** Take `n = 4` nodes with `3` honest
(`h = 3/4`, the classical `n = 3f + 1`, `f = 1`), `k = 1`, `θ = Δ_sync > 0` and `φ = 3/5`.
All hypotheses of Theorem 5.2 hold: `1 - h/k = 1/4 ≤ h`, `θ ≤ Δ_sync / k` and
`φ = 0.6 < 1 - h/(k+1) = 0.625`. Yet no `Δ_sync`-synchronous profile has a cycle in its AOF graph:
an edge needs `⌈0.6 · 4⌉ = 3` supporters, hence at least `2 > 3/2` honest ones, and the counting
argument of Theorem 5.1 with `k = 2` (`θ = Δ > Δ/2`) applies. -/
theorem theorem_5_2_fixed_n_false {Tx : Type*} {Δ : ℝ} (hΔ : 0 < Δ) (ts : Profile (Fin 4) Tx)
    (hsync : Synchronous ({0, 1, 2} : Finset (Fin 4)) Δ ts) :
    ¬ HasCycle (Prec ts Δ (3 / 5)) := by
  classical
  refine not_hasCycle_of_count (k := 2) hsync (by push_cast; linarith) fun x y hxy => ?_
  have hxy' : (3 / 5 : ℝ) * 4 ≤ (supp ts Δ x y).card := by simpa [Prec] using hxy
  have h3 : 3 ≤ (supp ts Δ x y).card := by
    by_contra h; push Not at h
    have : ((supp ts Δ x y).card : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 h
    linarith
  have hsub : ({0, 1, 2} : Finset (Fin 4)) \ supp ts Δ x y ⊆ univ \ supp ts Δ x y :=
    sdiff_subset_sdiff (subset_univ _) le_rfl
  have := card_le_card hsub
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin] at this
  have hc : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
  omega

/-- Non-vacuity of Theorem 5.1: with `n = 4`, `h = 3/4`, `k = 1`, `Δ = 1`, `θ = 2`, `φ = 1/2`
there is a synchronous profile with a genuine AOF edge, and Theorem 5.1 applies to it. -/
theorem theorem_5_1_nonvacuous :
    let ts : Profile (Fin 4) Bool := fun _ b => if b then 3 else 0
    Synchronous ({0, 1, 2} : Finset (Fin 4)) 1 ts ∧ Prec ts 2 (1 / 2) false true ∧
      ¬ HasCycle (Prec ts 2 (1 / 2)) := by
  intro ts
  have hsync : Synchronous ({0, 1, 2} : Finset (Fin 4)) 1 ts := by
    intro i _ j _ b; simp [ts]
  refine ⟨hsync, ?_, theorem_5_1 (h := 3 / 4) (k := 1) (by simp) hsync one_pos
    (by norm_num) (by norm_num)⟩
  have : supp ts 2 false true = univ := eq_univ_of_forall fun i => mem_supp.2 (by norm_num [ts])
  simp only [Prec, this, card_univ, Fintype.card_fin]
  norm_num

end Podc.DelayOptimalOrderFairness
