import Papers.PODC2021.RestorableTiebreaking.Existence

/-!
# Theorem 37 (no symmetric restorable scheme on `C₄`) and the literal Definition 17

Bodwin–Parter, PODC 2021, Appendix A and Definition 17.

* `theorem37` — on the 4-cycle, no tiebreaking scheme is symmetric (already for the non-faulty
  paths) and 1-restorable.
* `not_isRestorableLiteral`, `theorem19_literal_false` — Definition 17 as printed (no hypothesis
  that `s, t` stay connected in `G \ F`) cannot be met on the single-edge graph `K₂`; so Theorem 19
  read literally is false, and the connectivity hypothesis of Theorem 2 is needed in Definition 17.
-/

open Finset SimpleGraph SimpleGraph.Walk

namespace RestorableTiebreaking

/-! ### The 4-cycle -/

/-- The 4-cycle `0 - 1 - 2 - 3 - 0`. -/
abbrev C4 : SimpleGraph (Fin 4) := cycleGraph 4

lemma c4_edist_le (u v : Fin 4) : C4.edist u v ≤ 2 := by
  by_cases h : C4.edist u v ≤ 1
  · exact h.trans (by norm_num)
  · rw [edist_le_one_iff_adj_or_eq] at h
    rw [edist_eq_two_iff.mpr]
    refine ⟨fun h' => h (.inr h'), fun h' => h (.inl h'), ?_⟩
    revert h
    fin_cases u <;> fin_cases v <;> simp [cycleGraph_adj, Set.Nonempty, commonNeighbors] <;> decide

lemma c4_opp {u v : Fin 4} (h : C4.edist u v = 2) : v = u + 2 := by
  rw [edist_eq_two_iff] at h
  obtain ⟨h1, h2, -⟩ := h
  rw [cycleGraph_adj] at h2
  revert h1 h2
  fin_cases u <;> fin_cases v <;> decide

lemma c4_del {a b : Fin 4} (h : C4.Adj a b) : 2 < (C4.deleteEdges {s(a, b)}).edist a b := by
  rw [two_lt_edist_iff]
  revert h
  fin_cases a <;> fin_cases b <;>
    simp [cycleGraph_adj, commonNeighbors, Set.eq_empty_iff_forall_notMem, neighborSet] <;> decide

lemma c4_reach {a b : Fin 4} (h : C4.Adj a b) : (C4.deleteEdges {s(a, b)}).Reachable a b := by
  have key : ∀ a b : Fin 4, (a - b = 1 ∨ b - a = 1) →
      ((a - (a - (b - a)) = 1 ∨ (a - (b - a)) - a = 1) ∧ ¬ s(a, a - (b - a)) = s(a, b)) ∧
      (((a - (b - a)) - (a - (b - a) - (b - a)) = 1 ∨
          (a - (b - a) - (b - a)) - (a - (b - a)) = 1) ∧
        ¬ s(a - (b - a), a - (b - a) - (b - a)) = s(a, b)) ∧
      (((a - (b - a) - (b - a)) - b = 1 ∨ b - (a - (b - a) - (b - a)) = 1) ∧
        ¬ s(a - (b - a) - (b - a), b) = s(a, b)) := by decide
  obtain ⟨h1, h2, h3⟩ := key a b (cycleGraph_adj.mp h)
  have adj : ∀ x y : Fin 4, ((x - y = 1 ∨ y - x = 1) ∧ ¬ s(x, y) = s(a, b)) →
      (C4.deleteEdges {s(a, b)}).Adj x y := by
    intro x y hxy
    rw [deleteEdges_adj, cycleGraph_adj]
    exact ⟨hxy.1, by simpa using hxy.2⟩
  exact ((adj _ _ h1).reachable.trans (adj _ _ h2).reachable).trans (adj _ _ h3).reachable

private lemma walk_length_two {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.length = 2) : ∃ (m : V) (h₁ : G.Adj u m) (h₂ : G.Adj m v),
      p = cons h₁ (cons h₂ nil) := by
  rcases p with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, q⟩⟩⟩ <;> simp at hp
  exact ⟨_, h₁, h₂, rfl⟩

/-- **Theorem 37 of [Bodwin–Parter]** (after Afek et al.). On the 4-cycle, no tiebreaking scheme is
both symmetric and 1-restorable. (Symmetry is only required for the non-faulty paths, and only
the non-faulty paths need to be shortest.) -/
theorem theorem37 (π : Scheme C4) (hπ : IsRPTS C4 0 π) (hsym : IsSymmetric C4 0 π) :
    ¬ IsRestorable C4 1 π := by
  intro hres
  have h0 := hπ ∅ (by simp)
  have hsh : ∀ u v p, π ∅ u v = some p → p.length = C4.edist u v := by
    intro u v p hp
    have := (h0.1 u v p hp).2
    simpa using this
  have hsome : ∀ u v, ∃ p, π ∅ u v = some p := by
    intro u v
    have := h0.2 u v (by simpa using (cycleGraph_connected (n := 3)).preconnected u v)
    exact Option.isSome_iff_exists.mp this
  -- the two diagonal paths share an edge `s(m, m')`
  obtain ⟨p02, hp02⟩ := hsome 0 2
  obtain ⟨p13, hp13⟩ := hsome 1 3
  have hl02 : p02.length = 2 := by
    have := hsh _ _ _ hp02
    rw [edist_eq_two_iff.mpr (by simp [cycleGraph_adj, Set.Nonempty, commonNeighbors]; decide)]
      at this
    exact_mod_cast this
  have hl13 : p13.length = 2 := by
    have := hsh _ _ _ hp13
    rw [edist_eq_two_iff.mpr (by simp [cycleGraph_adj, Set.Nonempty, commonNeighbors]; decide)]
      at this
    exact_mod_cast this
  obtain ⟨m, a1, a2, rfl⟩ := walk_length_two p02 hl02
  obtain ⟨m', b1, b2, rfl⟩ := walk_length_two p13 hl13
  have hmm : C4.Adj m m' ∧ s(m, m') ∈ [s(0, m), s(m, 2)] ∧ s(m, m') ∈ [s(1, m'), s(m', 3)] := by
    rw [cycleGraph_adj] at a1 a2 b1 b2 ⊢
    revert a1 a2 b1 b2
    fin_cases m <;> fin_cases m' <;> decide
  obtain ⟨hadj, he02, he13⟩ := hmm
  -- every selected diagonal path uses `s(m, m')`
  have hdiag : ∀ u v p, v = u + 2 → π ∅ u v = some p → s(m, m') ∈ p.edges := by
    intro u v p huv hp
    subst huv
    have hs02 := hsym ∅ (by simp) 0 2
    have hs13 := hsym ∅ (by simp) 1 3
    rw [hp02] at hs02
    rw [hp13] at hs13
    fin_cases u
    · change π ∅ 0 2 = some p at hp
      rw [hp02] at hp; cases hp; exact he02
    · change π ∅ 1 3 = some p at hp
      rw [hp13] at hp; cases hp; exact he13
    · change π ∅ 2 0 = some p at hp
      rw [hs02] at hp; cases hp; rw [edges_reverse, List.mem_reverse]; exact he02
    · change π ∅ 3 1 = some p at hp
      rw [hs13] at hp; cases hp; rw [edges_reverse, List.mem_reverse]; exact he13
  -- restorability for the fault `s(m, m')`
  obtain ⟨F', hF', x, p, q, hp, hq, hW⟩ :=
    hres {s(m, m')} (by simp) (by simp) m m' (by simpa using c4_reach hadj)
  have hF'0 : F' = ∅ := by
    rcases (Finset.subset_singleton_iff.mp hF'.subset) with h | h
    · exact h
    · exact absurd h hF'.ne
  subst hF'0
  have hlen := hW.2
  rw [length_append, length_reverse, coe_singleton] at hlen
  have hgt := c4_del hadj
  rw [← hlen] at hgt
  push_cast at hgt
  rw [ hsh _ _ _ hp, hsh _ _ _ hq] at hgt
  have hav := hW.1
  simp only [avoids_append, avoids_reverse] at hav
  have hpx := c4_edist_le m x
  have hqx := c4_edist_le m' x
  -- one of the two halves is a diagonal path
  have : C4.edist m x = 2 ∨ C4.edist m' x = 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : C4.edist m x ≤ 1 := Order.le_of_lt_add_one (lt_of_le_of_ne hpx hcon.1)
    have h2 : C4.edist m' x ≤ 1 := Order.le_of_lt_add_one (lt_of_le_of_ne hqx hcon.2)
    have := add_le_add h1 h2
    have : (2 : ℕ∞) < 1 + 1 := lt_of_lt_of_le hgt this
    norm_num at this
  rcases this with h | h
  · exact hav.1 _ (hdiag m x p (c4_opp h) hp) (by simp)
  · exact hav.2 _ (hdiag m' x q (c4_opp h) hq) (by simp)

/-! ### Definition 17 needs a connectivity hypothesis -/

/-- The single-edge graph `K₂`. -/
abbrev K2 : SimpleGraph (Fin 2) := ⊤

/-- Definition 17 read literally cannot be satisfied on `K₂`: after the only edge fails, `0` and
`1` are disconnected, so no replacement path exists. -/
theorem not_isRestorableLiteral (π : Scheme K2) : ¬ IsRestorableLiteral K2 1 π := by
  intro h
  obtain ⟨F', -, x, p, q, -, -, hW⟩ := h {s(0, 1)} (by simp) (by simp) 0 1
  have hbot : K2.deleteEdges (({s(0, 1)} : Finset (Sym2 (Fin 2))) : Set (Sym2 (Fin 2))) = ⊥ := by
    ext u v
    simp only [deleteEdges_adj, top_adj, coe_singleton, Set.mem_singleton_iff, bot_adj]
    fin_cases u <;> fin_cases v <;> simp [Sym2.eq_swap]
  have := hW.2
  rw [hbot, edist_bot_of_ne (by decide)] at this
  exact ENat.natCast_ne_top _ this

/-- Theorem 19 read with the literal Definition 17 is false: `K₂` has an ATW function, but the
generated scheme is not "1-restorable" in the literal sense. -/
theorem theorem19_literal_false :
    ∃ r : Fin 2 → Fin 2 → ℝ, IsATW K2 1 r ∧ ¬ IsRestorableLiteral K2 1 (atwScheme K2 r) :=
  ⟨_, theorem23 (Fintype.equivFin (Sym2 (Fin 2))) 1, not_isRestorableLiteral _⟩

end RestorableTiebreaking
