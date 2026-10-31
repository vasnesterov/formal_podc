import Papers.PODC2015.DeterministicLoadBalancing.RotorRouter

/-!
# Theorem 4.3: the ROTOR-ROUTER without self-loops has discrepancy `≥ d · ϕ`

Berenbrink, Klasing, Kosowski, Mallmann-Trenn, Uznański, PODC 2015 (arXiv:1404.4344v4),
Theorem 4.3 and Appendix C.3.

Let `2ϕ + 1` be the odd girth of the `d`-regular graph `G`, fix a vertex `u` (the paper takes `u`
on a shortest odd cycle; any vertex works) and let `b v = min(dist(u, v), ϕ)`. Two adjacent
vertices with `b < ϕ` lie in consecutive BFS layers (otherwise there is an odd closed walk of
length `< 2ϕ + 1`). With `L = ϕ + 1` we use the flow
`f₀(v, w) = L ± (ϕ − min(b v, b w))` (`+` iff `b v` is even). It is symmetric
(`f₀(v,w) + f₀(w,v) = 2L`) and at every node its values differ by at most one, so the rotor-router
realises it periodically (`rotorRouter_periodic`); the load of `u` alternates between
`d (L + ϕ)` and `d (L − ϕ)` while the average load is `d L`.

**Repair of the paper's construction.** The paper sets `f₀(v₁, v₂) = L` as soon as
`b(v₁) ≥ ϕ` **or** `b(v₂) ≥ ϕ`. Then a node in layer `ϕ − 1 ≥ 1` sends `L ± 2` to layer `ϕ − 2`
and `L` to layer `ϕ`, contradicting the claim `|f_t(v, v₁) − f_t(v, v₂)| ≤ 1` (no rotor-router step
does this), and for `ϕ = 1` all values are `L` and the discrepancy is `0`. The construction works
with "and" in place of "or", i.e. with the offset `ϕ − min(b v₁, b v₂)` truncated at `0`, which is
what we formalize.
-/

open Finset Fin.NatCast

namespace Podc.DeterministicLoadBalancing

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Truncated BFS layer: `min(dist(u, v), ϕ)`, and `ϕ` outside the component of `u`. -/
noncomputable def layer (G : SimpleGraph V) (u : V) (ϕ : ℕ) (v : V) : ℕ :=
  open Classical in if G.Reachable u v then min (G.dist u v) ϕ else ϕ

lemma layer_adj {u v w : V} {ϕ : ℕ} (h : G.Adj v w) :
    layer G u ϕ v ≤ layer G u ϕ w + 1 ∧ layer G u ϕ w ≤ layer G u ϕ v + 1 := by
  unfold layer
  by_cases hv : G.Reachable u v
  · have hw : G.Reachable u w := hv.trans h.reachable
    simp only [hv, hw, ite_true]
    rcases h.diff_dist_adj (u := u) with h' | h' | h' <;> omega
  · have hw : ¬ G.Reachable u w := fun hw => hv (hw.trans h.symm.reachable)
    simp [hv, hw]

/-- Adjacent vertices in the same layer below `ϕ` would close an odd walk shorter than the odd
girth. -/
lemma le_layer_of_adj_of_eq {u v w : V} {ϕ : ℕ} (hϕ : G.oddGirth = 2 * ϕ + 1) (h : G.Adj v w)
    (heq : layer G u ϕ v = layer G u ϕ w) : ϕ ≤ layer G u ϕ v := by
  by_contra hlt
  push Not at hlt
  unfold layer at hlt heq
  by_cases hv : G.Reachable u v
  · have hw : G.Reachable u w := hv.trans h.reachable
    simp only [hv, hw, ite_true] at hlt heq
    have hdv : G.dist u v < ϕ := by omega
    have hdw : G.dist u w = G.dist u v := by omega
    obtain ⟨p, hp⟩ := hv.exists_walk_length_eq_dist
    obtain ⟨q, hq⟩ := hw.exists_walk_length_eq_dist
    let c : G.Walk u u := p.append (SimpleGraph.Walk.cons h q.reverse)
    have hc : c.length = 2 * G.dist u v + 1 := by
      simp only [c, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_reverse, hp, hq, hdw]
      ring
    have hodd : Odd c.length := ⟨G.dist u v, by omega⟩
    have := SimpleGraph.oddGirth_le_length c hodd
    rw [hϕ, hc] at this
    have : 2 * ϕ + 1 ≤ 2 * G.dist u v + 1 := by exact_mod_cast this
    omega
  · simp [hv] at hlt

/-- **Theorem 4.3** of [Berenbrink et al., PODC 2015]. Let `G` be a `d`-regular graph of odd girth
`2ϕ + 1` (in particular non-bipartite), balanced by the ROTOR-ROUTER without self-loops
(`d⁺ = d`). Then there exist edge orders, initial rotor directions and an initial load
distribution such that the discrepancy is at least `d · ϕ` at all times (the paper: `c · d ϕ`).
(`NeZero d` is implied by non-bipartiteness; it is needed to define the rotors.) -/
theorem theorem_4_3 {d : ℕ} [NeZero d] (hreg : G.IsRegularOfDegree d) {ϕ : ℕ}
    (hϕ : G.oddGirth = 2 * ϕ + 1) :
    ∃ (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d) (x₀ : V → ℕ),
      ∀ t, d * ϕ ≤ disc ((rotorRouter ord ρ₀).load x₀ t) := by
  obtain ⟨u, -, -, -, -⟩ := SimpleGraph.exists_isCycle_length_eq_oddGirth (G := G)
    (by rw [hϕ]; exact ENat.natCast_ne_top _)
  let b := layer G u ϕ
  set L := ϕ + 1 with hL
  let g : V → V → ℕ := fun v w =>
    if Even (b v) then L + (ϕ - min (b v) (b w)) else L - (ϕ - min (b v) (b w))
  let a : V → ℕ := fun v => if Even (b v) then L + (ϕ - b v) else L - (ϕ - (b v - 1))
  have hsym : ∀ v w, G.Adj v w → g v w + g w v = 2 * L := by
    intro v w h
    have hadj : b v ≤ b w + 1 ∧ b w ≤ b v + 1 := layer_adj h
    by_cases hm : ϕ ≤ min (b v) (b w)
    · have h1 : ϕ - min (b v) (b w) = 0 := by omega
      have h2 : ϕ - min (b w) (b v) = 0 := by omega
      simp only [g, h1, h2]
      split_ifs <;> omega
    · have hne : b v ≠ b w := fun heq => by
        have : ϕ ≤ b v := le_layer_of_adj_of_eq hϕ h heq
        omega
      have hpar : Even (b w) ↔ ¬ Even (b v) := by
        rcases (show b w = b v + 1 ∨ b v = b w + 1 by omega) with h' | h'
        · rw [h', Nat.even_add_one]
        · rw [h', Nat.even_add_one, not_not]
      simp only [g, min_comm (b w) (b v)]
      by_cases hev : Even (b v)
      · simp only [hev, ite_true, show ¬ Even (b w) from fun h' => hpar.1 h' hev, ite_false]; omega
      · simp only [hev, ite_false, hpar.2 hev, ite_true]; omega
  have hval : ∀ v w, G.Adj v w → g v w = a v ∨ g v w = a v + 1 := by
    intro v w h
    have hadj : b v ≤ b w + 1 ∧ b w ≤ b v + 1 := layer_adj h
    simp only [g, a]
    by_cases hev : Even (b v)
    · simp only [hev, ite_true]; omega
    · have : 1 ≤ b v := by
        rcases Nat.eq_zero_or_pos (b v) with h0 | h0
        · rw [h0] at hev; exact absurd ⟨0, rfl⟩ hev
        · exact h0
      simp only [hev, ite_false]; omega
  have ha : ∀ v, a v + 1 ≤ 2 * L := by
    intro v; simp only [a]; split_ifs <;> omega
  obtain ⟨ord, ρ₀, hper⟩ := rotorRouter_periodic hreg g L a hsym hval ha
  refine ⟨ord, ρ₀, fun v => ∑ w ∈ G.neighborFinset v, g v w, fun t => ?_⟩
  set x0 : V → ℕ := fun v => ∑ w ∈ G.neighborFinset v, g v w with hx0
  set x1 : V → ℕ := fun v => ∑ w ∈ G.neighborFinset v, g w v with hx1
  -- loads of `u`
  have hbu : b u = 0 := by simp [b, layer]
  have hgu : ∀ w ∈ G.neighborFinset u, g u w = L + ϕ := by
    intro w _; simp [g, hbu]
  have hgu' : ∀ w ∈ G.neighborFinset u, g w u = L - ϕ := by
    intro w hw
    have := hsym u w ((G.mem_neighborFinset _ _).1 hw)
    rw [hgu w hw] at this; omega
  have hcard : ∀ v, (G.neighborFinset v).card = d := fun v => by
    rw [G.card_neighborFinset_eq_degree, hreg v]
  have hx0u : x0 u = d * (L + ϕ) := by
    simp only [hx0]; rw [Finset.sum_congr rfl hgu, Finset.sum_const, hcard, smul_eq_mul]
  have hx1u : x1 u = d * (L - ϕ) := by
    simp only [hx1]; rw [Finset.sum_congr rfl hgu', Finset.sum_const, hcard, smul_eq_mul]
  -- totals
  have hswap : ∑ v, x1 v = ∑ v, x0 v := sum_sum_neighbor_swap G (fun w v => g w v)
  have htot : ∑ v, x0 v + ∑ v, x1 v = ∑ _v : V, d * (2 * L) := by
    simp only [hx0, hx1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_congr rfl fun w hw => hsym v w ((G.mem_neighborFinset _ _).1 hw),
      Finset.sum_const, hcard, smul_eq_mul]
  have hne : (Finset.univ : Finset V).Nonempty := ⟨u, Finset.mem_univ _⟩
  have hsum0 : ∑ v, x0 v = ∑ _v : V, d * L := by
    have : ∑ _v : V, d * (2 * L) = 2 * ∑ _v : V, d * L := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    omega
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · rw [(hper s).1]
    obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le hne hsum0.le
    have := sub_le_disc x0 u v
    have : d * (L + ϕ) = d * L + d * ϕ := by ring
    omega
  · rw [(hper s).2]
    have hsum1 : ∑ _v : V, d * L ≤ ∑ v, x1 v := by rw [hswap, hsum0]
    obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le hne hsum1
    have := sub_le_disc x1 v u
    have : d * L = d * (L - ϕ) + d * ϕ := by rw [← Nat.mul_add]; congr 1; omega
    omega

end Podc.DeterministicLoadBalancing
