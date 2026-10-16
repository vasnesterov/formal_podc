import Papers.PODC2011.FaultTolerantSpanners.Theorem21
import Cslib.Foundations.Combinatorics.SimpleGraph.Girth
import Cslib.Foundations.Combinatorics.SimpleGraph.Cycle

/-!
# Corollary 2.2 of Dinitz–Krauthgamer (PODC'11): the greedy spanner plugged into Theorem 2.1

The paper applies Theorem 2.1 to the greedy `(2t-1)`-spanner of Althöfer et al. [ADD+93], which has
`O(n^{1 + 1/t})` edges (`k = 2t - 1`, so `1 + 2/(k+1) = 1 + 1/t`). We prove the cited fact:

* `exists_greedy_spanner` — every finite weighted graph has a subgraph `H` of girth `> 2t` with
  `d_H(x, y) ≤ (2t - 1) w(xy)` for all edges `xy` (the greedy algorithm, scanning edges by
  nondecreasing weight, written as an induction over the sorted edge list);
* `ncard_edgeSet_le_of_noShortCycles` — Moore bound relative to a vertex set `S` containing all
  endpoints: `|E| ≤ |S|^{1+1/t} + |S|` (from CSLib's `NoShortCycles.ncard_edgeSet_le`);
* `greedyAlg` — hence a `SpannerAlg G w (2t-1) (fun s => s^{1+1/t} + s)`;
* `corollary_2_2` — with probability `≥ 1 - (n+1)^{-C} - α e^{-n^{1/3}/6}` the conversion outputs
  an `r`-fault-tolerant `(2t-1)`-spanner with at most `6 (8C + 26) r^{2 - 1/t} n^{1 + 1/t} ln(n+1)`
  edges, i.e. `O(r^{2 - 2/(k+1)} n^{1 + 2/(k+1)} log n)` as in the paper.
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace DinitzKrauthgamer

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma noShortCycles_bot (L : ℕ) : (⊥ : SimpleGraph V).NoShortCycles L := by
  intro v c hc
  cases c with
  | nil => exact absurd hc (by simp [Walk.isCycle_def])
  | cons h _ => exact absurd h (by simp)

omit [Fintype V] in
/-- **The greedy spanner, as an induction over an edge list sorted by nonincreasing weight**
(head = heaviest). -/
lemma exists_greedy_aux (w : Sym2 V → ℝ≥0) {t : ℕ} (ht : 1 ≤ t) :
    ∀ L : List (V × V), (∀ p ∈ L, p.1 ≠ p.2) →
      L.Pairwise (fun a b => w s(b.1, b.2) ≤ w s(a.1, a.2)) →
      ∃ H : SimpleGraph V, (∀ e ∈ H.edgeSet, ∃ p ∈ L, s(p.1, p.2) = e) ∧
        H.NoShortCycles (2 * t) ∧
        ∀ p ∈ L, H.wdist w p.1 p.2 ≤ (2 * t - 1 : ℕ) * w s(p.1, p.2)
  | [], _, _ => ⟨⊥, by simp, noShortCycles_bot _, by simp⟩
  | (x, y) :: L, hne, hsort => by
    obtain ⟨H, hHL, hHcyc, hHst⟩ :=
      exists_greedy_aux w ht L (fun p hp => hne p (List.mem_cons_of_mem _ hp))
        (List.pairwise_cons.mp hsort).2
    have hlight : ∀ p ∈ L, w s(p.1, p.2) ≤ w s(x, y) := (List.pairwise_cons.mp hsort).1
    have hxy : x ≠ y := hne (x, y) (by simp)
    -- weights of the edges of `H` are at most `w(xy)`
    have hHw : ∀ e ∈ H.edgeSet, w e ≤ w s(x, y) := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := hHL e he
      exact hlight p hp
    by_cases hrej : H.wdist w x y ≤ (2 * t - 1 : ℕ) * w s(x, y)
    · refine ⟨H, fun e he => ?_, hHcyc, ?_⟩
      · obtain ⟨p, hp, h⟩ := hHL e he
        exact ⟨p, List.mem_cons_of_mem _ hp, h⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hrej
        · exact hHst p hp
    · push Not at hrej
      refine ⟨H ⊔ edge x y, fun e he => ?_, ?_, ?_⟩
      · rw [edgeSet_sup, Set.mem_union, edgeSet_edge_of_ne hxy, Set.mem_singleton_iff] at he
        rcases he with he | rfl
        · obtain ⟨p, hp, h⟩ := hHL e he
          exact ⟨p, List.mem_cons_of_mem _ hp, h⟩
        · exact ⟨(x, y), by simp, rfl⟩
      · intro v c hc
        by_contra hlen
        push Not at hlen
        by_cases hmem : s(x, y) ∈ c.edges
        · obtain ⟨p, -, hpe, -, hpl⟩ := hc.exists_path_of_mem_edges hmem
          have hpH : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
            intro e he
            obtain ⟨he1, he2⟩ := hpe e he
            have := p.edges_subset_edgeSet he
            rw [edgeSet_sup, Set.mem_union, edgeSet_edge_of_ne hxy,
              Set.mem_singleton_iff] at this
            exact this.resolve_right he2
          let q : H.Walk x y := p.transfer H hpH
          have hq : H.wdist w x y ≤ (2 * t - 1 : ℕ) * w s(x, y) := by
            calc H.wdist w x y ≤ q.wlength w := wdist_le q
              _ ≤ q.length * w s(x, y) := q.wlength_le_length_mul w fun e he => by
                  exact_mod_cast hHw e (q.edges_subset_edgeSet he)
              _ ≤ (2 * t - 1 : ℕ) * w s(x, y) := by
                  gcongr
                  rw [Walk.length_transfer]
                  exact_mod_cast (by omega : p.length ≤ 2 * t - 1)
          exact absurd hq (not_le.mpr hrej)
        · have hcH : ∀ e ∈ c.edges, e ∈ H.edgeSet := by
            intro e he
            have := c.edges_subset_edgeSet he
            rw [edgeSet_sup, Set.mem_union, edgeSet_edge_of_ne hxy,
              Set.mem_singleton_iff] at this
            exact this.resolve_right (fun h => hmem (h ▸ he))
          have := hHcyc v (c.transfer H hcH) (hc.transfer hcH)
          rw [Walk.length_transfer] at this
          omega
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · calc (H ⊔ edge x y).wdist w x y ≤ w s(x, y) :=
                wdist_le_of_adj (Or.inr (by simp [edge_adj, hxy]))
            _ ≤ (2 * t - 1 : ℕ) * w s(x, y) := by
                apply le_mul_of_one_le_left (zero_le)
                exact_mod_cast (by omega : 1 ≤ 2 * t - 1)
        · exact (wdist_anti le_sup_left).trans (hHst p hp)

-- CSLib candidate
/-- **Greedy spanner** [ADD+93]: every finite weighted graph `G'` has a subgraph of girth `> 2t`
which is a `(2t - 1)`-spanner. -/
theorem exists_greedy_spanner (G' : SimpleGraph V) (w : Sym2 V → ℝ≥0) {t : ℕ} (ht : 1 ≤ t) :
    ∃ H ≤ G', H.NoShortCycles (2 * t) ∧
      ∀ u v, H.wdist w u v ≤ (2 * t - 1 : ℕ) * G'.wdist w u v := by
  classical
  let L := ((univ.filter fun p : V × V => G'.Adj p.1 p.2).toList).mergeSort
    fun a b => decide (w s(b.1, b.2) ≤ w s(a.1, a.2))
  have hLmem : ∀ p, p ∈ L ↔ G'.Adj p.1 p.2 := fun p => by simp [L, List.mem_mergeSort]
  have hsort : L.Pairwise fun a b => w s(b.1, b.2) ≤ w s(a.1, a.2) := by
    have := List.pairwise_mergeSort
      (le := fun a b : V × V => decide (w s(b.1, b.2) ≤ w s(a.1, a.2)))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hbc.trans hab)
      (fun a b => by simpa using le_total _ _)
      ((univ.filter fun p : V × V => G'.Adj p.1 p.2).toList)
    simpa using this
  obtain ⟨H, hHL, hcyc, hst⟩ := exists_greedy_aux w ht L
    (fun p hp => ((hLmem p).mp hp).ne) hsort
  have hle : H ≤ G' := by
    intro a b hab
    obtain ⟨p, hp, he⟩ := hHL s(a, b) hab
    have := (hLmem p).mp hp
    rw [← mem_edgeSet, ← he]
    exact this
  refine ⟨H, hle, hcyc, fun u v => ?_⟩
  have h1 : 1 ≤ 2 * t - 1 := by omega
  exact wdist_le_mul_of_adj h1 (fun a b hab => hst (a, b) ((hLmem _).mpr hab)) u v

-- CSLib candidate
omit [DecidableEq V] in
/-- **Moore bound relative to a vertex set**: if all edges of `H` have their endpoints in `S` and
`H` has girth `> 2t`, then `|E(H)| ≤ |S|^{1+1/t} + |S|`. -/
theorem ncard_edgeSet_le_of_noShortCycles {H : SimpleGraph V} {t : ℕ} (ht : 1 ≤ t)
    (h : H.NoShortCycles (2 * t)) (S : Finset V) (hS : ∀ u v, H.Adj u v → u ∈ S) :
    (H.edgeSet.ncard : ℝ) ≤ (#S : ℝ) ^ (1 + 1 / (t : ℝ)) + #S := by
  set s := #S
  have hx : (0 : ℝ) ≤ (s : ℝ) ^ (1 / (t : ℝ)) := by positivity
  set d := ⌈(s : ℝ) ^ (1 / (t : ℝ))⌉₊
  have hd : #S ≤ d ^ t := by
    have : (s : ℝ) ≤ (d : ℝ) ^ t := by
      calc (s : ℝ) = ((s : ℝ) ^ ((t : ℝ)⁻¹)) ^ t :=
            (Real.rpow_inv_natCast_pow (Nat.cast_nonneg s) (by omega)).symm
        _ ≤ (d : ℝ) ^ t := by
            rw [← one_div]
            exact pow_le_pow_left₀ hx (Nat.le_ceil _) t
    exact_mod_cast this
  have hE := h.ncard_edgeSet_le ht S hS hd
  calc (H.edgeSet.ncard : ℝ) ≤ d * s := by exact_mod_cast hE
    _ ≤ ((s : ℝ) ^ (1 / (t : ℝ)) + 1) * s :=
        mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hx).le (Nat.cast_nonneg _)
    _ = (s : ℝ) ^ (1 + 1 / (t : ℝ)) + s := by
        rw [Real.rpow_add' (Nat.cast_nonneg _) (by positivity), Real.rpow_one]
        ring

/-- The greedy `(2t-1)`-spanner as a spanner algorithm with size bound `s^{1+1/t} + s`. -/
noncomputable def greedyAlg (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) {t : ℕ} (ht : 1 ≤ t) :
    SpannerAlg G w (2 * t - 1) (fun s => (s : ℝ) ^ (1 + 1 / (t : ℝ)) + s) where
  run S := (exists_greedy_spanner (G.deleteVerts (↑S : Set V)ᶜ) w ht).choose
  le S := (exists_greedy_spanner (G.deleteVerts (↑S : Set V)ᶜ) w ht).choose_spec.1
  stretch S u v _ _ := (exists_greedy_spanner (G.deleteVerts (↑S : Set V)ᶜ) w ht).choose_spec.2.2 u v
  size S := by
    obtain ⟨hle, hcyc, -⟩ := (exists_greedy_spanner (G.deleteVerts (↑S : Set V)ᶜ) w ht).choose_spec
    refine ncard_edgeSet_le_of_noShortCycles ht hcyc S fun u v huv => ?_
    have := (hle huv).2.1
    simpa using this

lemma monotone_greedy_size {t : ℕ} :
    Monotone (fun s : ℕ => (s : ℝ) ^ (1 + 1 / (t : ℝ)) + s) := by
  intro a b hab
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  dsimp only
  gcongr

/-- **Corollary 2.2 of Dinitz–Krauthgamer (PODC'11).** For every weighted graph and every
`t ≥ 1` (stretch `k = 2t - 1`), `1 ≤ r ≤ n` and `C ∈ ℕ`: the conversion of Theorem 2.1 applied to the
greedy spanner outputs, with probability at least `1 - (n+1)^{-C} - α e^{-n^{1/3}/6}`
(`α = numIter n r C = O(r³ log n)`), an `r`-fault-tolerant `(2t-1)`-spanner with at most
`6 (8C + 26) r^{2 - 1/t} n^{1 + 1/t} ln(n+1)` edges. -/
theorem corollary_2_2 (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) {t : ℕ} (ht : 1 ≤ t)
    {r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ Fintype.card V) (C : ℕ) :
    1 - 1 / ((Fintype.card V : ℝ) + 1) ^ C -
        numIter (Fintype.card V) r C * Real.exp (-((Fintype.card V : ℝ) ^ ((1 : ℝ) / 3) / 6)) ≤
      uprob (fun ω : Fin (numIter (Fintype.card V) r C) → V → Fin (max r 2) =>
        IsWeightedVFTSpanner G (ftUnion (greedyAlg G w ht) ω) w r (2 * t - 1) ∧
        ((ftUnion (greedyAlg G w ht) ω).edgeSet.ncard : ℝ) ≤
          6 * (8 * C + 26) * (r : ℝ) ^ (2 - 1 / (t : ℝ)) *
            (Fintype.card V : ℝ) ^ (1 + 1 / (t : ℝ)) * Real.log ((Fintype.card V : ℝ) + 1)) := by
  set n := Fintype.card V
  have hk : 1 ≤ 2 * t - 1 := by omega
  have hf2 : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (1 + 1 / (t : ℝ)) + ((2 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (1 + 1 / (t : ℝ)) := by positivity
    push_cast; linarith
  refine (theorem_2_1 (greedyAlg G w ht) hk monotone_greedy_size hf2 hr hrn C).trans
    (uprob_mono fun ω h => ⟨h.1, h.2.trans ?_⟩)
  -- arithmetic: `r³ ln(n+1) (⌊2n/r⌋^{1+1/t} + ⌊2n/r⌋) ≤ 6 r^{2-1/t} n^{1+1/t} ln(n+1)`
  set L := Real.log ((n : ℝ) + 1)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hr.trans hrn
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hC : (0 : ℝ) ≤ 8 * C + 26 := by positivity
  set e := 1 / (t : ℝ)
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [div_le_one (by exact_mod_cast (by omega : 0 < t))]; exact_mod_cast ht
  set y : ℝ := ((⌊2 * (n : ℝ) / r⌋₊ : ℕ) : ℝ)
  have hy0 : 0 ≤ y := Nat.cast_nonneg _
  have hy : y ≤ 2 * n / r := Nat.floor_le (by positivity)
  -- `y^{1+e} ≤ (2n/r)^{1+e} = 2^{1+e} n^{1+e} / r^{1+e}`
  have hry : (r : ℝ) ^ 3 * (y ^ (1 + e) + y) ≤ 6 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by
    have h1 : y ^ (1 + e) ≤ (2 * n / r) ^ (1 + e) := Real.rpow_le_rpow hy0 hy (by linarith)
    have hrpos : (0 : ℝ) < r := by linarith
    have h2 : (r : ℝ) ^ 3 * (2 * n / r) ^ (1 + e) ≤ 4 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by
      rw [Real.div_rpow (by positivity) hrpos.le, Real.mul_rpow (by norm_num) (by positivity)]
      have h2e : (2 : ℝ) ^ (1 + e) ≤ 4 := by
        calc (2 : ℝ) ^ (1 + e) ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have hr3 : (r : ℝ) ^ 3 / (r : ℝ) ^ (1 + e) = (r : ℝ) ^ (2 - e) := by
        rw [← Real.rpow_natCast, ← Real.rpow_sub hrpos]; norm_num; ring_nf
      calc (r : ℝ) ^ 3 * ((2 : ℝ) ^ (1 + e) * (n : ℝ) ^ (1 + e) / (r : ℝ) ^ (1 + e))
          = (2 : ℝ) ^ (1 + e) * ((r : ℝ) ^ 3 / (r : ℝ) ^ (1 + e)) * (n : ℝ) ^ (1 + e) := by ring
        _ = (2 : ℝ) ^ (1 + e) * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by rw [hr3]
        _ ≤ 4 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by gcongr
    have h3 : (r : ℝ) ^ 3 * y ≤ 2 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by
      -- `r³ y ≤ 2 n r² ≤ 2 r^{2-e} n^{1+e}` since `r^e ≤ n^e`
      have hry' : (r : ℝ) ^ 3 * y ≤ 2 * n * (r : ℝ) ^ 2 := by
        calc (r : ℝ) ^ 3 * y ≤ (r : ℝ) ^ 3 * (2 * n / r) := by gcongr
          _ = 2 * n * (r : ℝ) ^ 2 := by field_simp
      have hre : (r : ℝ) ^ e ≤ (n : ℝ) ^ e := Real.rpow_le_rpow (by linarith) hrn' he0
      have hsplit1 : (r : ℝ) ^ (2 : ℝ) = (r : ℝ) ^ (2 - e) * (r : ℝ) ^ e := by
        rw [← Real.rpow_add hrpos]; ring_nf
      have hsplit2 : (n : ℝ) ^ (1 + e) = n * (n : ℝ) ^ e := by
        rw [Real.rpow_add (by linarith), Real.rpow_one]
      have hr2 : (r : ℝ) ^ 2 = (r : ℝ) ^ (2 : ℝ) := by norm_cast
      rw [hsplit2]
      calc (r : ℝ) ^ 3 * y ≤ 2 * n * (r : ℝ) ^ 2 := hry'
        _ = 2 * n * ((r : ℝ) ^ (2 - e) * (r : ℝ) ^ e) := by rw [hr2, hsplit1]
        _ ≤ 2 * n * ((r : ℝ) ^ (2 - e) * (n : ℝ) ^ e) := by gcongr
        _ = 2 * (r : ℝ) ^ (2 - e) * (n * (n : ℝ) ^ e) := by ring
    have h4 : (r : ℝ) ^ 3 * y ^ (1 + e) ≤ (r : ℝ) ^ 3 * (2 * n / r) ^ (1 + e) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : (r : ℝ) ^ 3 * (y ^ (1 + e) + y) = (r : ℝ) ^ 3 * y ^ (1 + e) + (r : ℝ) ^ 3 * y := by
      ring
    linarith
  calc (8 * (C : ℝ) + 26) * (r : ℝ) ^ 3 * L * (y ^ (1 + e) + y)
      = (8 * C + 26) * L * ((r : ℝ) ^ 3 * (y ^ (1 + e) + y)) := by ring
    _ ≤ (8 * C + 26) * L * (6 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e)) := by gcongr
    _ = 6 * (8 * C + 26) * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) * L := by ring

end DinitzKrauthgamer
