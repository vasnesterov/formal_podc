import Mathlib

/-!
# The Bilateral Network Creation Game (BNCG)

Friedrich, Gawendowicz, Lenzner, Zahn. *The Impact of Cooperation in Bilateral Network Creation.*
PODC 2023 (full version arXiv:2207.03798v2), Section 1.1.

A state of the BNCG is identified with the created graph `G` on the agent set `V` (the paper does
the same: in equilibrium no agent pays for an edge that is not built). Agent `u` pays `α` per
incident edge and the sum of its hop distances to all agents; the distance between disconnected
agents is a constant `M` (the paper takes `M ∈ ℕ`, `M > α n³`).

We define
* `d M G u v` — the distance with penalty `M`, `distCost M G u = ∑ v, d M G u v` (`dist(u)`),
* `cost α M G u = α · deg u + dist(u)`,
* the solution concepts `RE`, `BAE`, `PS`, `BSwE`, `BGE`, `KBSE k`, `BSE`,
* the social cost, the optimum `optCost` (an infimum over *all* graphs on `V`), and the ratio
  `rho = cost(G) / cost(OPT)`.
-/

namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

variable {V : Type*} [Fintype V]

section Defs

open Classical in
/-- Hop distance, with the constant `M` for pairs that are not connected. -/
noncomputable def d (M : ℕ) (G : SimpleGraph V) (u v : V) : ℕ :=
  if G.Reachable u v then G.dist u v else M

/-- The total distance cost `dist_G(u) = ∑_v dist_G(u, v)`. -/
noncomputable def distCost (M : ℕ) (G : SimpleGraph V) (u : V) : ℕ := ∑ v, d M G u v

/-- The total distance from `u` to a set `S` of agents. -/
noncomputable def distTo (M : ℕ) (G : SimpleGraph V) (u : V) (S : Finset V) : ℕ :=
  ∑ v ∈ S, d M G u v

/-- The number of edges an agent pays for (its degree). -/
noncomputable def deg (G : SimpleGraph V) (u : V) : ℕ := (G.neighborSet u).ncard

/-- The cost of agent `u`: buying cost `α · deg u` plus distance cost. -/
noncomputable def cost (α : ℝ) (M : ℕ) (G : SimpleGraph V) (u : V) : ℝ :=
  α * deg G u + distCost M G u

variable (α : ℝ) (M : ℕ) (G : SimpleGraph V)

/-- Remove Equilibrium: no agent strictly improves by removing one incident edge. -/
def RE : Prop :=
  ∀ u v, G.Adj u v → cost α M G u ≤ cost α M (G.deleteEdges {s(u, v)}) u

/-- Bilateral Add Equilibrium: no non-adjacent pair both strictly improve by adding their edge. -/
def BAE : Prop :=
  ∀ u v, u ≠ v → ¬ G.Adj u v → cost α M (G ⊔ edge u v) u < cost α M G u →
    cost α M G v ≤ cost α M (G ⊔ edge u v) v

/-- Pairwise stability. -/
def PS : Prop := RE α M G ∧ BAE α M G

/-- The graph after agent `u` swaps its edge `uv` for `uw`. -/
def swap (u v w : V) : SimpleGraph V := G.deleteEdges {s(u, v)} ⊔ edge u w

/-- Bilateral Swap Equilibrium: there are no `u, v, w` with `uv ∈ E`, `uw ∉ E` such that both `u`
and `w` strictly improve when `u` replaces `uv` by `uw`. -/
def BSwE : Prop :=
  ∀ u v w, G.Adj u v → u ≠ w → ¬ G.Adj u w → cost α M (swap G u v w) u < cost α M G u →
    cost α M G w ≤ cost α M (swap G u v w) w

/-- Bilateral Greedy Equilibrium. -/
def BGE : Prop := PS α M G ∧ BSwE α M G

/-- `G'` arises from `G` by a move of the coalition `Γ`: removed edges have an endpoint in `Γ`,
added edges have both endpoints in `Γ`. -/
def IsCoalitionMove (G G' : SimpleGraph V) (Γ : Finset V) : Prop :=
  (∀ x y, G.Adj x y → ¬ G'.Adj x y → x ∈ Γ ∨ y ∈ Γ) ∧
  (∀ x y, G'.Adj x y → ¬ G.Adj x y → x ∈ Γ ∧ y ∈ Γ)

/-- Bilateral `k`-Strong Equilibrium: no nonempty coalition of size `≤ k` has a move after which
all its members strictly improve. (The paper does not say "nonempty"; for `Γ = ∅` the condition
"all members improve" would be vacuous.) -/
def KBSE (k : ℕ) : Prop :=
  ∀ Γ : Finset V, Γ.Nonempty → Γ.card ≤ k → ∀ G', IsCoalitionMove G G' Γ →
    ∃ x ∈ Γ, cost α M G x ≤ cost α M G' x

/-- Bilateral Strong Equilibrium (`n`-BSE). -/
def BSE : Prop := KBSE α M G (Fintype.card V)

/-- Social cost. -/
noncomputable def socialCost : ℝ := ∑ u, cost α M G u

/-- Cost of a social optimum (infimum over all graphs on `V`). -/
noncomputable def optCost : ℝ := ⨅ H : SimpleGraph V, socialCost α M H

/-- The social cost ratio `ρ(G) = cost(G) / cost(OPT)`. -/
noncomputable def rho : ℝ := socialCost α M G / optCost (V := V) α M

end Defs

/-! ### Basic facts about `d` -/

section Basic

variable {M : ℕ} {G G' : SimpleGraph V} {u v w : V}

@[simp] lemma d_self : d M G u u = 0 := by simp [d]

lemma d_of_reachable (h : G.Reachable u v) : d M G u v = G.dist u v := by simp [d, h]

lemma d_of_not_reachable (h : ¬ G.Reachable u v) : d M G u v = M := by simp [d, h]

lemma d_comm : d M G u v = d M G v u := by
  unfold d
  by_cases h : G.Reachable u v
  · simp [h, h.symm, dist_comm]
  · have h' : ¬ G.Reachable v u := fun h' => h h'.symm
    simp [h, h']

lemma d_le_of_walk (p : G.Walk u v) : d M G u v ≤ p.length := by
  rw [d_of_reachable ⟨p⟩]; exact dist_le p

lemma d_eq_one_of_adj (h : G.Adj u v) : d M G u v = 1 := by
  rw [d_of_reachable h.reachable, dist_eq_one_iff_adj.2 h]

lemma dist_lt_card (h : G.Reachable u v) : G.dist u v < Fintype.card V := by
  obtain ⟨p, hp, hl⟩ := h.exists_path_of_dist
  rw [← hl]; exact hp.length_lt

lemma d_lt_card_of_reachable (h : G.Reachable u v) : d M G u v < Fintype.card V := by
  rw [d_of_reachable h]; exact dist_lt_card h

/-- Distances do not increase when edges are added (given `M ≥ n`). -/
lemma d_anti (hGG' : G ≤ G') (hM : Fintype.card V ≤ M) : d M G' u v ≤ d M G u v := by
  by_cases h : G.Reachable u v
  · have h' : G'.Reachable u v := h.mono hGG'
    rw [d_of_reachable h, d_of_reachable h']
    obtain ⟨p, -, hl⟩ := h.exists_path_of_dist
    rw [← hl, ← Walk.length_mapLe hGG' p]; exact dist_le _
  · rw [d_of_not_reachable h]
    by_cases h' : G'.Reachable u v
    · exact (d_lt_card_of_reachable h').le.trans hM
    · rw [d_of_not_reachable h']

lemma one_le_d (hne : u ≠ v) (hM : 1 ≤ M) : 1 ≤ d M G u v := by
  by_cases h : G.Reachable u v
  · rw [d_of_reachable h]
    exact Nat.one_le_iff_ne_zero.2 (dist_ne_zero_iff_ne_and_reachable.2 ⟨hne, h⟩)
  · rwa [d_of_not_reachable h]

lemma two_le_d (hne : u ≠ v) (hna : ¬ G.Adj u v) (hM : 2 ≤ M) : 2 ≤ d M G u v := by
  by_cases h : G.Reachable u v
  · rw [d_of_reachable h]
    have h1 : G.dist u v ≠ 0 := dist_ne_zero_iff_ne_and_reachable.2 ⟨hne, h⟩
    have h2 : G.dist u v ≠ 1 := fun h' => hna (dist_eq_one_iff_adj.1 h')
    omega
  · rwa [d_of_not_reachable h]

lemma d_triangle (hM : Fintype.card V ≤ M) : d M G u w ≤ d M G u v + d M G v w := by
  by_cases h1 : G.Reachable u v
  · by_cases h2 : G.Reachable v w
    · rw [d_of_reachable h1, d_of_reachable h2, d_of_reachable (h1.trans h2)]
      exact h1.dist_triangle_left w |>.trans_eq rfl |> fun h => by
        obtain ⟨p, -, hp⟩ := h1.exists_path_of_dist
        obtain ⟨q, -, hq⟩ := h2.exists_path_of_dist
        have := dist_le (p.append q)
        rw [Walk.length_append] at this; omega
    · rw [d_of_not_reachable h2]
      by_cases h3 : G.Reachable u w
      · exact (d_lt_card_of_reachable h3).le.trans (hM.trans (Nat.le_add_left _ _))
      · rw [d_of_not_reachable h3]; omega
  · rw [d_of_not_reachable h1]
    by_cases h3 : G.Reachable u w
    · exact (d_lt_card_of_reachable h3).le.trans (hM.trans (Nat.le_add_right _ _))
    · rw [d_of_not_reachable h3]; omega

lemma distCost_anti (hGG' : G ≤ G') (hM : Fintype.card V ≤ M) :
    distCost M G' u ≤ distCost M G u :=
  Finset.sum_le_sum fun _ _ => d_anti hGG' hM

lemma deg_eq_degree [DecidableRel G.Adj] : deg G u = G.degree u := by
  simp [deg]

lemma distCost_eq_distTo_add [DecidableEq V] (S : Finset V) :
    distCost M G u = distTo M G u S + distTo M G u Sᶜ := by
  unfold distCost distTo
  rw [← Finset.sum_add_sum_compl S]

end Basic

/-! ### Social optimum: a lower bound on `optCost` -/

section Opt

variable {α : ℝ} {M : ℕ}

lemma distCost_ge_of_two_le (G : SimpleGraph V) [DecidableRel G.Adj] (hM : 2 ≤ M) (u : V) :
    2 * (Fintype.card V - 1) ≤ distCost M G u + G.degree u := by
  classical
  have key : ∀ v, (if v = u then 0 else 2) ≤ d M G u v + (if G.Adj u v then 1 else 0) := by
    intro v
    by_cases hv : v = u
    · simp [hv]
    · rw [if_neg hv]
      by_cases ha : G.Adj u v
      · rw [if_pos ha]; have := one_le_d (G := G) (Ne.symm hv) (by omega : 1 ≤ M); omega
      · rw [if_neg ha]; have := two_le_d (G := G) (Ne.symm hv) ha hM; omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun v _ => key v
  rw [Finset.sum_add_distrib] at hsum
  have h1 : ∑ v, (if v = u then 0 else 2 : ℕ) = 2 * (Fintype.card V - 1) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, zero_add]
    rw [Finset.filter_ne' Finset.univ u, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, mul_comm]
  have h2 : ∑ v, (if G.Adj u v then 1 else 0 : ℕ) = G.degree u := by
    rw [Finset.sum_boole, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    simp
  rw [h1, h2] at hsum
  exact hsum

lemma card_le_M (hα : 1 ≤ α) (hM : α * (Fintype.card V) ^ 3 < M) : Fintype.card V ≤ M := by
  have hn : (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast h
      calc (Fintype.card V : ℝ) = (Fintype.card V : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ this (by norm_num)
  have : (Fintype.card V : ℝ) < M := by nlinarith
  exact_mod_cast this.le

/-- The lower bound `cost(G) ≥ 2(n-1)(α+n-1)` for every graph, if `α ≥ 1` and `M > α n³`. -/
theorem socialCost_ge (hα : 1 ≤ α) (hM : α * (Fintype.card V) ^ 3 < M) (G : SimpleGraph V) :
    2 * ((Fintype.card V : ℝ) - 1) * (α + Fintype.card V - 1) ≤ socialCost α M G := by
  classical
  set n := Fintype.card V with hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 (by omega)
    simp [socialCost, ← hn, h0]
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
  have hcM : n ≤ M := card_le_M hα hM
  by_cases hconn : G.Connected
  · -- connected: at least `n - 1` edges and every distance is `≥ 1`, `≥ 2` for non-edges
    by_cases h1 : n = 1
    · have : (n : ℝ) = 1 := by exact_mod_cast h1
      rw [this]
      have : 0 ≤ socialCost α M G := Finset.sum_nonneg fun u _ => by
        unfold cost; have := (zero_le_one.trans hα); positivity
      simpa using this
    have hM2 : 2 ≤ M := by omega
    have hE : n ≤ #G.edgeFinset + 1 := by
      have := hconn.card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← G.edgeFinset_card] at this
      exact this
    have hsum : ∑ u, (cost α M G u) =
        α * (2 * #G.edgeFinset) + ∑ u, (distCost M G u : ℝ) := by
      unfold cost
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      simp only [deg_eq_degree]
      exact_mod_cast sum_degrees_eq_twice_card_edges G
    have hd : ∀ u, 2 * ((n : ℝ) - 1) - G.degree u ≤ distCost M G u := by
      intro u
      have := distCost_ge_of_two_le G hM2 u
      have h' : (2 * (n - 1) : ℕ) = 2 * ((n : ℝ) - 1) := by push_cast [Nat.cast_sub hpos]; ring
      have : (2 * ((n : ℝ) - 1)) ≤ distCost M G u + G.degree u := by
        rw [← h']; exact_mod_cast this
      linarith
    have hd' := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hd u
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hd'
    have hdeg : ∑ u, (G.degree u : ℝ) = 2 * #G.edgeFinset := by
      exact_mod_cast sum_degrees_eq_twice_card_edges G
    rw [hdeg] at hd'
    unfold socialCost
    rw [hsum]
    have hE' : (n : ℝ) ≤ #G.edgeFinset + 1 := by exact_mod_cast hE
    nlinarith
  · -- disconnected: every agent pays the penalty `M` at least once
    have hne : Nonempty V := ⟨(Finset.univ_nonempty_iff.1 (Finset.card_pos.1 hpos)).some⟩
    have : ¬ G.Preconnected := fun h => hconn ⟨h⟩
    obtain ⟨a, b, hab⟩ : ∃ a b, ¬ G.Reachable a b := by
      by_contra h; push Not at h; exact this h
    have hu : ∀ u, (M : ℝ) ≤ cost α M G u := by
      intro u
      have hx : ∃ x, ¬ G.Reachable u x := by
        by_cases hua : G.Reachable u a
        · exact ⟨b, fun hub => hab (hua.symm.trans hub)⟩
        · exact ⟨a, hua⟩
      obtain ⟨x, hx⟩ := hx
      have : M ≤ distCost M G u := by
        calc M = d M G u x := (d_of_not_reachable hx).symm
          _ ≤ distCost M G u :=
            Finset.single_le_sum (f := fun v => d M G u v) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ x)
      unfold cost
      have : (M : ℝ) ≤ distCost M G u := by exact_mod_cast this
      have : 0 ≤ α * deg G u := by have := (zero_le_one.trans hα); positivity
      linarith
    have := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hu u
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    unfold socialCost
    refine le_trans ?_ this
    -- `2(n-1)(α+n-1) ≤ n M`, from `M > α n³`
    have hα0 : 0 ≤ α := zero_le_one.trans hα
    have h3 : α * (n : ℝ) ^ 3 ≤ n * M := by
      calc α * (n : ℝ) ^ 3 ≤ M := hM.le
        _ ≤ n * M := by nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    have h4 : 2 * ((n : ℝ) - 1) * (α + n - 1) ≤ α * (n : ℝ) ^ 3 := by
      rcases eq_or_lt_of_le hn1 with h | h
      · rw [← h]; nlinarith
      · have h2 : (2 : ℝ) ≤ n := by
          have : 2 ≤ n := by
            have : (1 : ℝ) < n := h
            exact_mod_cast this
          exact_mod_cast this
        have e1 : α + n - 1 ≤ α * n := by nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hn1)]
        have e2 : 2 * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
        have e3 : 0 ≤ 2 * ((n : ℝ) - 1) := by linarith
        calc 2 * ((n : ℝ) - 1) * (α + n - 1) ≤ 2 * ((n : ℝ) - 1) * (α * n) :=
              mul_le_mul_of_nonneg_left e1 e3
          _ ≤ (n : ℝ) ^ 2 * (α * n) := mul_le_mul_of_nonneg_right e2 (by positivity)
          _ = α * (n : ℝ) ^ 3 := by ring
    linarith

theorem optCost_ge (hα : 1 ≤ α) (hM : α * (Fintype.card V) ^ 3 < M) :
    2 * ((Fintype.card V : ℝ) - 1) * (α + Fintype.card V - 1) ≤ optCost (V := V) α M :=
  le_ciInf fun G => socialCost_ge hα hM G

lemma socialCost_nonneg (hα : 0 ≤ α) (G : SimpleGraph V) : 0 ≤ socialCost α M G :=
  Finset.sum_nonneg fun u _ => by unfold cost; positivity

lemma optCost_le (hα : 0 ≤ α) (G : SimpleGraph V) : optCost (V := V) α M ≤ socialCost α M G :=
  ciInf_le ⟨0, by rintro _ ⟨H, rfl⟩; exact socialCost_nonneg hα H⟩ G

end Opt

end Podc.BilateralNetworkCreation
