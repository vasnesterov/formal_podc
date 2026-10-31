import Mathlib

/-!
# Claim 6: the degeneracy of `H`-free graphs

Drucker–Kuhn–Oshman, PODC 2014, Claim 6: if `G` is an `n`-node `H`-free graph, then the degeneracy
of `G` is at most `4 · ex(n, H) / n`.

The paper's proof uses that `ex(n, H)` is non-decreasing in `n` and that `ex(2n, H) ≥ 2 ex(n, H)`
(two disjoint copies of an extremal graph). Both facts need assumptions on `H`: for
`H = K₂ ∪ K₁` (an edge plus an isolated vertex) `ex(2, H) = 1 > 0 = ex(3, H) = ex(4, H)`
(`extremalNumber_edge_plus_point`). We prove Claim 6 for **connected** `H` with at least one edge
(`claim_6`), which covers all graphs for which the paper uses it (cycles, cliques, complete
bipartite graphs, trees).
-/

namespace Podc.CongestedCliquePower

open SimpleGraph Finset

variable {W : Type*} {H : SimpleGraph W}

/-- `G` is `k`-degenerate (has degeneracy at most `k`): every nonempty set of vertices contains a
vertex with at most `k` neighbours in the set (equivalently: every subgraph has a vertex of degree
at most `k`). -/
def IsDegenerate {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (G.Adj v)).card ≤ k

/-- A copy of a connected graph in a disjoint union lies in one of the two parts. -/
theorem isContained_sum_of_connected (hH : H.Connected) {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁}
    {G₂ : SimpleGraph V₂} (h : H ⊑ G₁ ⊕g G₂) : H ⊑ G₁ ∨ H ⊑ G₂ := by
  obtain ⟨f⟩ := h
  obtain ⟨a₀⟩ := hH.nonempty
  have hreach : ∀ a, (G₁ ⊕g G₂).Reachable (f a₀) (f a) := fun a =>
    (hH.preconnected a₀ a).map f.toHom
  rcases h₀ : f a₀ with x | y
  · have hl : ∀ a, ∃ z, f a = Sum.inl z := by
      intro a
      rcases hfa : f a with z | z
      · exact ⟨z, rfl⟩
      · have := hreach a
        rw [h₀, hfa] at this
        exact absurd this (not_reachable_sum_inl_inr _ _)
    choose g hg using hl
    left
    refine ⟨⟨⟨g, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
    · have : (G₁ ⊕g G₂).Adj (f a) (f b) := f.toHom.map_adj hab
      rw [hg a, hg b] at this
      simpa using this
    · apply f.injective
      change f a = f b
      rw [hg a, hg b]
      exact congrArg _ hab
  · have hr : ∀ a, ∃ z, f a = Sum.inr z := by
      intro a
      rcases hfa : f a with z | z
      · have := (hreach a).symm
        rw [h₀, hfa] at this
        exact absurd this (not_reachable_sum_inl_inr _ _)
      · exact ⟨z, rfl⟩
    choose g hg using hr
    right
    refine ⟨⟨⟨g, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
    · have : (G₁ ⊕g G₂).Adj (f a) (f b) := f.toHom.map_adj hab
      rw [hg a, hg b] at this
      simpa using this
    · apply f.injective
      change f a = f b
      rw [hg a, hg b]
      exact congrArg _ hab

lemma card_edgeFinset_sum {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] (G₁ : SimpleGraph V₁)
    (G₂ : SimpleGraph V₂) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableEq V₁]
    [DecidableEq V₂] [Fintype (G₁ ⊕g G₂).edgeSet] :
    #(G₁ ⊕g G₂).edgeFinset = #G₁.edgeFinset + #G₂.edgeFinset := by
  rw [edgeFinset_card, edgeFinset_card, edgeFinset_card, Fintype.card_congr (edgeSetSumEquiv),
    Fintype.card_sum]

/-- `ex(n, H)` is non-decreasing in `n` (for `H` connected with an edge). -/
theorem extremalNumber_le_add (hH : H.Connected) (hbot : H ≠ ⊥) (n k : ℕ) :
    extremalNumber n H ≤ extremalNumber (n + k) H := by
  classical
  obtain ⟨G, _, hG⟩ := exists_isExtremal_free (V := Fin n) hbot
  have hfree : H.Free (G ⊕g (⊥ : SimpleGraph (Fin k))) := by
    intro h
    rcases isContained_sum_of_connected hH h with h | h
    · exact hG.prop h
    · exact free_bot hbot h
  have h1 := card_edgeFinset_le_extremalNumber hfree
  have h2 := card_edgeFinset_of_isExtremal_free hG
  simp only [Fintype.card_sum, Fintype.card_fin] at h1 h2
  rw [card_edgeFinset_sum] at h1
  omega

theorem extremalNumber_mono (hH : H.Connected) (hbot : H ≠ ⊥) {n m : ℕ} (h : n ≤ m) :
    extremalNumber n H ≤ extremalNumber m H := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact extremalNumber_le_add hH hbot n k

/-- `ex(2n, H) ≥ 2 ex(n, H)` for connected `H`: two disjoint copies of an extremal graph. -/
theorem two_mul_extremalNumber_le (hH : H.Connected) (hbot : H ≠ ⊥) (n : ℕ) :
    2 * extremalNumber n H ≤ extremalNumber (2 * n) H := by
  classical
  obtain ⟨G, _, hG⟩ := exists_isExtremal_free (V := Fin n) hbot
  have hfree : H.Free (G ⊕g G) := by
    intro h
    rcases isContained_sum_of_connected hH h with h | h <;> exact hG.prop h
  have h1 := card_edgeFinset_le_extremalNumber hfree
  have h2 := card_edgeFinset_of_isExtremal_free hG
  simp only [Fintype.card_sum, Fintype.card_fin] at h1 h2
  rw [card_edgeFinset_sum] at h1
  rw [two_mul n]; omega

theorem pow_mul_extremalNumber_le (hH : H.Connected) (hbot : H ≠ ⊥) (n : ℕ) :
    ∀ k, 2 ^ k * extremalNumber n H ≤ extremalNumber (2 ^ k * n) H
  | 0 => by simp
  | k + 1 => by
      calc 2 ^ (k + 1) * extremalNumber n H = 2 * (2 ^ k * extremalNumber n H) := by ring
        _ ≤ 2 * extremalNumber (2 ^ k * n) H :=
          Nat.mul_le_mul_left 2 (pow_mul_extremalNumber_le hH hbot n k)
        _ ≤ extremalNumber (2 * (2 ^ k * n)) H := two_mul_extremalNumber_le hH hbot _
        _ = extremalNumber (2 ^ (k + 1) * n) H := by ring_nf

/-- The step `ex(n', H) / n' ≤ 2 ex(n, H) / n` of the proof of Claim 6, for `0 < n' ≤ n`
(in the form `n · ex(n', H) ≤ 2 n' · ex(n, H)`). -/
theorem mul_extremalNumber_le (hH : H.Connected) (hbot : H ≠ ⊥) {n' n : ℕ} (h0 : 0 < n')
    (h : n' ≤ n) : n * extremalNumber n' H ≤ 2 * n' * extremalNumber n H := by
  set k := Nat.log 2 (n / n')
  have hk : 2 ^ k * n' ≤ n := by
    have := Nat.pow_log_le_self 2 (Nat.div_pos h h0).ne'
    calc 2 ^ k * n' ≤ n / n' * n' := Nat.mul_le_mul_right _ this
      _ ≤ n := Nat.div_mul_le_self n n'
  have hk' : n < 2 ^ (k + 1) * n' := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n / n')
    calc n < (n / n' + 1) * n' := by
          have := Nat.lt_div_mul_add (a := n) h0
          nlinarith [Nat.div_add_mod n n', Nat.mod_lt n h0]
      _ ≤ 2 ^ (k + 1) * n' := Nat.mul_le_mul_right _ this
  have h1 := pow_mul_extremalNumber_le hH hbot n' k
  have h2 := extremalNumber_mono hH hbot hk
  calc n * extremalNumber n' H ≤ 2 ^ (k + 1) * n' * extremalNumber n' H :=
        Nat.mul_le_mul_right _ hk'.le
    _ = 2 * n' * (2 ^ k * extremalNumber n' H) := by ring
    _ ≤ 2 * n' * extremalNumber n H := Nat.mul_le_mul_left _ (h1.trans h2)

/-- **Claim 6** (for connected `H` with at least one edge). If `G` is an `n`-node `H`-free graph,
then the degeneracy of `G` is at most `4 · ex(n, H) / n`: every nonempty vertex set `s` contains a
vertex with at most `4 · ex(n, H) / n` neighbours in `s`. -/
theorem claim_6 (hH : H.Connected) (hbot : H ≠ ⊥) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : H.Free G) (s : Finset V) (hs : s.Nonempty) :
    ∃ v ∈ s, ((s.filter (G.Adj v)).card : ℝ) ≤ 4 * extremalNumber (Fintype.card V) H /
      Fintype.card V := by
  classical
  set n := Fintype.card V
  set G' := G.induce (s : Set V)
  have hfree : H.Free G' := fun h => hG (h.trans ⟨Copy.induce G _⟩)
  have hE : #G'.edgeFinset ≤ extremalNumber s.card H := by
    have := card_edgeFinset_le_extremalNumber hfree
    simpa using this
  have hdeg : ∀ v : (s : Set V), G'.degree v = (s.filter (G.Adj v)).card := by
    rintro ⟨v, hv⟩
    rw [← card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_
    · rintro ⟨w, hw⟩ h
      simp only [mem_neighborFinset, G', comap_adj, Function.Embedding.subtype_apply] at h
      exact mem_filter.2 ⟨hw, h⟩
    · rintro ⟨a, _⟩ _ ⟨b, _⟩ _ h
      exact Subtype.ext h
    · intro w hw
      obtain ⟨hw, hvw⟩ := mem_filter.1 hw
      exact ⟨⟨w, hw⟩, by simpa [G'] using hvw, rfl⟩
  have hsum : ∑ v ∈ s, (s.filter (G.Adj v)).card = 2 * #G'.edgeFinset := by
    rw [← sum_degrees_eq_twice_card_edges]
    simp_rw [hdeg]
    exact (Finset.sum_coe_sort s (fun v => (s.filter (G.Adj v)).card)).symm
  have hn : s.card ≤ n := Finset.card_le_univ s
  have hpos : 0 < s.card := hs.card_pos
  have hratio := mul_extremalNumber_le hH hbot hpos hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos.trans_le hn
  refine Finset.exists_le_of_sum_le hs ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h1 : (∑ v ∈ s, ((s.filter (G.Adj v)).card : ℝ)) ≤ 2 * extremalNumber s.card H := by
    have : (∑ v ∈ s, (s.filter (G.Adj v)).card : ℕ) ≤ 2 * extremalNumber s.card H := by
      rw [hsum]; omega
    exact_mod_cast this
  have h2 : (n : ℝ) * extremalNumber s.card H ≤ 2 * s.card * extremalNumber n H := by
    exact_mod_cast hratio
  rw [mul_div_assoc', le_div_iff₀ hnpos]
  nlinarith

/-- Claim 6 in terms of `IsDegenerate`: an `n`-node `H`-free graph is
`⌊4 · ex(n, H) / n⌋`-degenerate. -/
theorem claim_6_isDegenerate (hH : H.Connected) (hbot : H ≠ ⊥) {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : H.Free G) :
    IsDegenerate G (4 * extremalNumber (Fintype.card V) H / Fintype.card V) := by
  intro s hs
  obtain ⟨v, hv, h⟩ := claim_6 hH hbot G hG s hs
  refine ⟨v, hv, ?_⟩
  rw [Nat.le_div_iff_mul_le]
  · have hn : (0 : ℝ) < Fintype.card V := by
      exact_mod_cast (hs.card_pos.trans_le (Finset.card_le_univ s))
    rw [le_div_iff₀ hn] at h
    exact_mod_cast h
  · exact hs.card_pos.trans_le (Finset.card_le_univ s)

/-! ### The proof's monotonicity step fails for disconnected `H` -/

/-- `K₂ ∪ K₁`: an edge plus an isolated vertex. -/
def edgePlusPoint : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet {s(0, 1)}

/-- For `H = K₂ ∪ K₁`, `ex(n, H)` is not monotone: `ex(3, H) = 0 < 1 ≤ ex(2, H)` (any edge on three
vertices together with the third vertex is a copy of `H`; on two vertices `H` does not fit). So the
step "`ex(n, H)` is non-decreasing in `n`" of the proof of Claim 6 needs an assumption such as
connectivity of `H`. -/
theorem extremalNumber_edge_plus_point :
    extremalNumber 3 edgePlusPoint = 0 ∧ 1 ≤ extremalNumber 2 edgePlusPoint := by
  classical
  constructor
  · have := (extremalNumber_le_iff (V := Fin 3) edgePlusPoint 0).2 (fun G _ hG => by
      rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        rw [mem_edgeFinset, mem_edgeSet] at he
        apply hG
        -- the third vertex
        obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
          have hab := G.ne_of_adj he
          fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> decide
        refine ⟨⟨⟨![a, b, c], fun {x y} hxy => ?_⟩, ?_⟩⟩
        · simp only [edgePlusPoint, fromEdgeSet_adj, Set.mem_singleton_iff] at hxy
          obtain ⟨h1, -⟩ := hxy
          rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simpa using he
          · simpa using he.symm
        · have hab := G.ne_of_adj he
          intro x y hxy
          fin_cases x <;> fin_cases y <;> simp_all [eq_comm])
    simpa using this
  · have := (lt_extremalNumber_iff (V := Fin 2) edgePlusPoint 0).2
      ⟨⊤, inferInstance, fun ⟨f⟩ => by
        have := Fintype.card_le_of_injective f f.injective
        simp at this, Finset.card_pos.2 ⟨s(0, 1), by simp⟩⟩
    simp only [Fintype.card_fin] at this
    exact this

end Podc.CongestedCliquePower
