import Podc.Foundations.Combinatorics.SimpleGraph.Power

/-!
# Lemma 6: every vertex cover of `Gʳ` is large

[BCMPP20] R. Bar-Yehuda, K. Censor-Hillel, Y. Maus, S. Pai, S. V. Pemmaraju,
*Distributed Approximation on Power Graphs*, PODC 2020 (arXiv 2006.03746).

Lemma 6: for a connected `n`-vertex graph `G` and `1 ≤ r ≤ n`, every vertex cover of `Gʳ` has
size at least `n − n/α` with `α = ⌊r/2⌋ + 1`; hence taking all vertices is a
`(1 + 1/⌊r/2⌋)`-approximation of MVC on `Gʳ`.

The proof in the paper shows `|I| < n/α` for every independent set `I` of `Gʳ`; the strict
inequality is false (`lemma_6_strict_false`: the path on 4 vertices, `r = 2`, `I = {0, 3}`).
The correct (and sufficient) bound is `|I| · α ≤ n` (`card_mul_le_of_indep`).
-/

namespace Podc.PowerGraphApproximation

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The closed `G`-ball of radius `j` around `v`, as a finset. -/
noncomputable def ballF (G : SimpleGraph V) (v : V) (j : ℕ) : Finset V :=
  by classical exact univ.filter fun w => G.edist v w ≤ j

omit [DecidableEq V] in
lemma mem_ballF {v w : V} {j : ℕ} : w ∈ ballF G v j ↔ G.edist v w ≤ j := by
  classical simp [ballF]

/-- In a connected graph, the ball of radius `j` has at least `min(n, j + 1)` vertices. -/
lemma card_ballF (hG : G.Connected) (v : V) :
    ∀ j : ℕ, j + 1 ≤ Fintype.card V → j + 1 ≤ (ballF G v j).card
  | 0, _ => by
    have : v ∈ ballF G v 0 := by simp [mem_ballF]
    exact Finset.card_pos.2 ⟨v, this⟩
  | j + 1, hj => by
    by_cases hall : ballF G v j = univ
    · have : ballF G v j ⊆ ballF G v (j + 1) := fun w hw => by
        rw [mem_ballF] at hw ⊢
        exact hw.trans (by exact_mod_cast Nat.le_succ j)
      rw [hall] at this
      rw [univ_subset_iff.1 this, card_univ]
      exact hj
    · obtain ⟨w, -, hw⟩ := (Finset.ssubset_iff_of_subset (subset_univ _)).1
        (Finset.ssubset_univ_iff.2 hall)
      obtain ⟨p⟩ := hG.preconnected v w
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (ballF G v j : Set V)
        (by simp [mem_ballF]) (by simpa using hw)
      have hsub : ballF G v j ⊂ ballF G v (j + 1) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨d.snd, ?_, by simpa using hd2⟩
          rw [mem_ballF]
          have h1 := edist_le_add_one_of_adj (u := v) d.adj
          have h2 : G.edist v d.fst ≤ j := mem_ballF.1 (by simpa using hd1)
          calc G.edist v d.snd ≤ G.edist v d.fst + 1 := h1
            _ ≤ j + 1 := by gcongr
            _ = ((j + 1 : ℕ) : ℕ∞) := by push_cast; rfl
        · intro x hx
          rw [mem_ballF] at hx ⊢
          exact hx.trans (by exact_mod_cast Nat.le_succ j)
      have := card_lt_card hsub
      have := card_ballF hG v j (by omega)
      omega

/-- The (corrected) key step of Lemma 6: an independent set `I` of `Gʳ` (connected `G`,
`r ≤ n`) satisfies `|I| · (⌊r/2⌋ + 1) ≤ n`. -/
theorem card_mul_le_of_indep (hG : G.Connected) {r : ℕ} (hrn : r ≤ Fintype.card V)
    {I : Finset V} (hI : ∀ u ∈ I, ∀ v ∈ I, ¬ (G.power r).Adj u v) :
    I.card * (r / 2 + 1) ≤ Fintype.card V := by
  set k := r / 2
  have hk : k + 1 ≤ Fintype.card V := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨hG.nonempty.some⟩
    omega
  have hdisj : (I : Set V).PairwiseDisjoint fun v => ballF G v k := by
    intro u hu v hv huv
    rw [Function.onFun, Finset.disjoint_left]
    intro w hwu hwv
    rw [mem_ballF] at hwu hwv
    apply hI u hu v hv
    refine ⟨huv, ?_⟩
    have := edist_le_natCast_add hwu (by rwa [edist_comm] at hwv)
    exact this.trans (by exact_mod_cast (by omega : k + k ≤ r))
  calc I.card * (k + 1) = ∑ _v ∈ I, (k + 1) := by simp
    _ ≤ ∑ v ∈ I, (ballF G v k).card := sum_le_sum fun v _ => card_ballF hG v k hk
    _ = (I.biUnion fun v => ballF G v k).card := (card_biUnion hdisj).symm
    _ ≤ Fintype.card V := card_le_univ _

/-- **Lemma 6 of [BCMPP20].** For a connected `n`-vertex graph `G` and `1 ≤ r ≤ n`, every vertex
cover of `Gʳ` has size at least `n − n/α`, where `α = ⌊r/2⌋ + 1`. -/
theorem lemma_6 (hG : G.Connected) {r : ℕ} (_hr : 1 ≤ r) (hrn : r ≤ Fintype.card V)
    {C : Finset V} (hC : (G.power r).IsVertexCover (C : Set V)) :
    (Fintype.card V : ℚ) - Fintype.card V / (r / 2 + 1 : ℕ) ≤ C.card := by
  set I := univ \ C
  have hI : ∀ u ∈ I, ∀ v ∈ I, ¬ (G.power r).Adj u v := by
    intro u hu v hv huv
    simp only [I, mem_sdiff, mem_univ, true_and] at hu hv
    rcases hC huv with h | h
    · exact hu h
    · exact hv h
  have h1 := card_mul_le_of_indep hG hrn hI
  have h2 : I.card + C.card = Fintype.card V := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have := card_le_univ C
    omega
  have hpos : (0 : ℚ) < (r / 2 + 1 : ℕ) := by positivity
  have h1' : (I.card : ℚ) * (r / 2 + 1 : ℕ) ≤ Fintype.card V := by exact_mod_cast h1
  have h2' : (I.card : ℚ) + C.card = Fintype.card V := by exact_mod_cast h2
  have : (Fintype.card V : ℚ) / (r / 2 + 1 : ℕ) ≥ I.card := by
    rw [ge_iff_le, le_div_iff₀ hpos]; exact h1'
  linarith

/-- **Lemma 6 of [BCMPP20]**, second sentence: for `2 ≤ r ≤ n`, the solution consisting of all
vertices is a `(1 + 1/⌊r/2⌋)`-approximation of minimum vertex cover on `Gʳ`. -/
theorem lemma_6_approx (hG : G.Connected) {r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ Fintype.card V)
    {C : Finset V} (hC : (G.power r).IsVertexCover (C : Set V)) :
    (Fintype.card V : ℚ) ≤ (1 + 1 / ((r / 2 : ℕ) : ℚ)) * C.card := by
  have h := lemma_6 hG (by omega) hrn hC
  have hk : (1 : ℚ) ≤ (r / 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ r / 2)
  set k : ℚ := ((r / 2 : ℕ) : ℚ)
  set n : ℚ := ((Fintype.card V : ℕ) : ℚ)
  have hcast : ((r / 2 + 1 : ℕ) : ℚ) = k + 1 := by simp [k]
  rw [hcast] at h
  -- `n - n/(k+1) = n k/(k+1) ≤ |C|`, so `n ≤ (k+1)/k · |C|`.
  have hk0 : (0 : ℚ) < k := by linarith
  have e : n - n / (k + 1) = n * k / (k + 1) := by field_simp; ring
  rw [e, div_le_iff₀ (by linarith)] at h
  rw [show (1 + 1 / k) * (C.card : ℚ) = (C.card * (k + 1)) / k by field_simp,
    le_div_iff₀ hk0]
  linarith

/-- The proof of Lemma 6 claims `|I| < n/α` for every independent set `I` of `Gʳ`. This strict
inequality is false: in the path `0 − 1 − 2 − 3` (`n = 4`, connected) with `r = 2` (`α = 2`), the
set `I = {0, 3}` is independent in `G²` and `|I| = 2 = n/α`. -/
theorem lemma_6_strict_false :
    let G := pathGraph 4
    G.Connected ∧ (∀ u ∈ ({0, 3} : Finset (Fin 4)), ∀ v ∈ ({0, 3} : Finset (Fin 4)),
      ¬ (G.power 2).Adj u v) ∧
      ¬ ((({0, 3} : Finset (Fin 4)).card : ℚ) < Fintype.card (Fin 4) / (2 / 2 + 1 : ℕ)) := by
  refine ⟨pathGraph_connected 3, ?_, by norm_num⟩
  have hf : ∀ x y : Fin 4, (pathGraph 4).Adj x y → (y : ℕ) ≤ x + 1 := by
    intro x y h
    rw [pathGraph_adj] at h
    omega
  have hf' : ∀ x y : Fin 4, (pathGraph 4).Adj x y → (3 - y : ℕ) ≤ (3 - x) + 1 := by
    intro x y h
    rw [pathGraph_adj] at h
    omega
  have h03 : ¬ (pathGraph 4).edist 0 3 ≤ 2 := fun h => by
    have := le_add_of_edist_le_of_lipschitz (f := fun x : Fin 4 => (x : ℕ)) hf h
    simp at this
  have h30 : ¬ (pathGraph 4).edist 3 0 ≤ 2 := fun h => by
    have := le_add_of_edist_le_of_lipschitz (f := fun x : Fin 4 => (3 - x : ℕ)) hf' h
    simp at this
  intro u hu v hv huv
  simp only [mem_insert, mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact huv.1 rfl
  · exact h03 huv.2
  · exact h30 huv.2
  · exact huv.1 rfl

end Podc.PowerGraphApproximation
