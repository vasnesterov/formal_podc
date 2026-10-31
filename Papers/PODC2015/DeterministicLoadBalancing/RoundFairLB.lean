import Papers.PODC2015.DeterministicLoadBalancing.Model

/-!
# Theorem 4.1: round-fair balancers can have discrepancy `Ω(d · diam)`

Berenbrink, Klasing, Kosowski, Mallmann-Trenn, Uznański, PODC 2015 (arXiv:1404.4344v4),
Theorem 4.1 and its proof in Appendix C.1.

The construction: fix `u, w` at distance `diam G`, let `b v = dist(u, v)`, let every node `v` send
`min(b v, b y)` tokens to each neighbour `y` and `b v − 1` tokens over each self-loop. This flow is
symmetric, so the loads `x* v` are a fixed point; it is round-fair, and `x* u = 0` while
`x* w ≥ d⁺ (diam − 1)`.

The paper's construction yields discrepancy `0` when `diam = 1` and `d = 1` (the graph `K₂`):
we treat this case separately (one token in the system never becomes balanced on two nodes).

We also provide a default round-fair (and fully self-preferring) rule `fairRule`, used for the loads
that never occur in the constructed execution.
-/

open Finset

namespace Podc.DeterministicLoadBalancing

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-- Every load `x` can be split fairly over `S` (original edges) and `dl` self-loops, putting the
extra tokens on self-loops first. -/
lemma exists_fair_split (S : Finset V) (dl x : ℕ) (hD : 0 < S.card + dl) :
    ∃ (o : V → ℕ) (k : ℕ), k + ∑ w ∈ S, o w = x ∧
      (∀ w ∈ S, FairShare (S.card + dl) x (o w)) ∧
      ∃ g : Fin dl → ℕ, ∑ i, g i = k ∧ (∀ i, FairShare (S.card + dl) x (g i)) ∧
        min dl (x % (S.card + dl)) ≤ #{i | g i = x / (S.card + dl) + 1} := by
  set D := S.card + dl with hDdef
  set q := x / D
  set e := x % D
  have hx : D * q + e = x := Nat.div_add_mod x D
  have he : e < D := Nat.mod_lt x hD
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (s := S) (n := e - min e dl) (by omega)
  refine ⟨fun w => q + if w ∈ T then 1 else 0, dl * q + min e dl, ?_, ?_,
    fun i => q + if i.val < min e dl then 1 else 0, ?_, ?_, ?_⟩
  · rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hTS, hTc]
    rw [← hx, hDdef]; push_cast; ring_nf; omega
  · intro w _
    unfold FairShare
    dsimp only
    split_ifs with h
    · right; refine ⟨fun h0 => ?_, rfl⟩
      have he0 : e = x % D := rfl
      have := Finset.card_pos.2 ⟨w, h⟩
      omega
    · left; simp [q]
  · rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole,
      Fin.card_filter_val_lt]
    simp [Finset.card_univ]
  · intro i
    unfold FairShare
    dsimp only
    split_ifs with h
    · right; refine ⟨fun h0 => ?_, rfl⟩
      have he0 : e = x % D := rfl
      omega
    · left; simp [q]
  · have : #{i : Fin dl | (q + if i.val < min e dl then 1 else 0) = q + 1} =
        #{i : Fin dl | i.val < min e dl} := by
      congr 1; ext i; simp only [mem_filter, mem_univ, true_and]; split_ifs <;> simp_all
    rw [this, Fin.card_filter_val_lt]; omega

section Rules

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every node and load admit a step that is round-fair and `dl`-self-preferring. -/
lemma exists_fair_rule (dl : ℕ) (v : V) (x : ℕ) (hD : 0 < G.degree v + dl) :
    ∃ (o : V → ℕ) (k : ℕ), k + ∑ w ∈ G.neighborFinset v, o w = x ∧
      GoodStep dl dl (G.degree v + dl) x o (G.neighborFinset v) k := by
  have := exists_fair_split (G.neighborFinset v) dl x (by rwa [G.card_neighborFinset_eq_degree])
  rw [G.card_neighborFinset_eq_degree] at this
  obtain ⟨o, k, h1, h2, g, h3, h4, h5⟩ := this
  exact ⟨o, k, h1, h2, g, h3, h4, h5⟩

/-- A stateless balancer that, at node `v`, follows the prescribed step `(o v, k v)` when its load
is `target v`, and the default fair rule (`exists_fair_rule`) otherwise. -/
noncomputable def patchedBalancer (dl : ℕ) (hD : ∀ v, 0 < G.degree v + dl) (target : V → ℕ)
    (o : V → V → ℕ) (k : V → ℕ) (hok : ∀ v, k v + ∑ w ∈ G.neighborFinset v, o v w = target v) :
    Balancer G :=
  Balancer.stateless G
    (fun v x => if x = target v then o v else (exists_fair_rule G dl v x (hD v)).choose)
    (fun v x => if x = target v then k v else
      (exists_fair_rule G dl v x (hD v)).choose_spec.choose)
    (by
      intro v x
      split_ifs with h
      · rw [hok, h]
      · exact (exists_fair_rule G dl v x (hD v)).choose_spec.choose_spec.1)

variable {G}

lemma patchedBalancer_roundFair (dl : ℕ) (hD : ∀ v, 0 < G.degree v + dl) (target : V → ℕ)
    (o : V → V → ℕ) (k : V → ℕ) (hok : ∀ v, k v + ∑ w ∈ G.neighborFinset v, o v w = target v)
    (hfair : ∀ v, (∀ w ∈ G.neighborFinset v, FairShare (G.degree v + dl) (target v) (o v w)) ∧
      ∃ g : Fin dl → ℕ, ∑ i, g i = k v ∧ ∀ i, FairShare (G.degree v + dl) (target v) (g i)) :
    (patchedBalancer G dl hD target o k hok).RoundFair dl := by
  intro v _ x
  simp only [patchedBalancer, Balancer.stateless]
  split_ifs with h
  · subst h; exact hfair v
  · obtain ⟨h1, g, h2, h3, -⟩ := (exists_fair_rule G dl v x (hD v)).choose_spec.choose_spec.2
    exact ⟨h1, g, h2, h3⟩

/-- If the prescribed flow is balanced at every node (what a node receives equals its target
load), the target loads are a fixed point of the patched balancer. -/
lemma patchedBalancer_load (dl : ℕ) (hD : ∀ v, 0 < G.degree v + dl) (target : V → ℕ)
    (o : V → V → ℕ) (k : V → ℕ) (hok : ∀ v, k v + ∑ w ∈ G.neighborFinset v, o v w = target v)
    (hin : ∀ v, k v + ∑ w ∈ G.neighborFinset v, o w v = target v) (t : ℕ) :
    (patchedBalancer G dl hD target o k hok).load target t = target := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    rw [Balancer.load_succ, ← hin v]
    simp only [Balancer.kept, Balancer.flow, ih]
    simp [patchedBalancer, Balancer.stateless]

end Rules

/-! ### Theorem 4.1 -/

section Theorem41

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a connected graph, every `v ≠ u` has a neighbour one step closer to `u`. -/
lemma exists_adj_dist_succ (hG : G.Connected) {u v : V} (h : v ≠ u) :
    ∃ y, G.Adj v y ∧ G.dist u y + 1 = G.dist u v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v u
  cases p with
  | nil => exact absurd rfl h
  | cons hvy q =>
    rename_i y
    refine ⟨y, hvy, ?_⟩
    have h1 : G.dist y u ≤ q.length := SimpleGraph.dist_le q
    have h2 : G.dist u v ≤ G.dist u y + G.dist y v :=
      (hG.preconnected u y).dist_triangle_left v |>.trans (by rfl)
    have h3 : G.dist y v = 1 := by rw [SimpleGraph.dist_comm]; exact (G.dist_eq_one_iff_adj).2 hvy
    simp only [SimpleGraph.Walk.length_cons] at hp
    rw [SimpleGraph.dist_comm (u := v)] at hp
    rw [SimpleGraph.dist_comm (u := y)] at h1
    omega

omit [Fintype V] [DecidableEq V] in
/-- `min(b v, b y) ≥ b v − 1` along edges, for `b = dist(u, ·)`. -/
lemma le_min_dist_of_adj {u v y : V} (h : G.Adj v y) :
    G.dist u v - 1 ≤ min (G.dist u v) (G.dist u y) := by
  rcases h.diff_dist_adj (u := u) with h | h | h <;> omega

/-- The steady flow of Appendix C.1 is round-fair: at `x* v = dl (b v − 1) + Σ_{y∼v} min(b v, b y)`
every edge value `min(b v, b y)` and the self-loop value `b v − 1` is a fair share. -/
lemma steady_fair (hG : G.Connected) {d : ℕ} (hreg : G.IsRegularOfDegree d) (dl : ℕ) (u v : V) :
    (∀ y ∈ G.neighborFinset v, FairShare (d + dl)
        (dl * (G.dist u v - 1) + ∑ y ∈ G.neighborFinset v, min (G.dist u v) (G.dist u y))
        (min (G.dist u v) (G.dist u y))) ∧
      FairShare (d + dl)
        (dl * (G.dist u v - 1) + ∑ y ∈ G.neighborFinset v, min (G.dist u v) (G.dist u y))
        (G.dist u v - 1) := by
  by_cases hvu : v = u
  · subst hvu
    simp [FairShare]
  set k := G.dist u v with hk
  have hk1 : 1 ≤ k := hG.pos_dist_of_ne (Ne.symm hvu)
  have hnb : ∀ y ∈ G.neighborFinset v, min k (G.dist u y) = k - 1 ∨ min k (G.dist u y) = k := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    rcases hy.diff_dist_adj (u := u) with h | h | h <;> omega
  set m := #{y ∈ G.neighborFinset v | min k (G.dist u y) = k} with hm
  have hsum : ∑ y ∈ G.neighborFinset v, min k (G.dist u y) = d * (k - 1) + m := by
    rw [Finset.sum_congr rfl (g := fun y => (k - 1) + if min k (G.dist u y) = k then 1 else 0)
      (fun y hy => by rcases hnb y hy with h | h <;> simp [h] <;> omega),
      Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole,
      G.card_neighborFinset_eq_degree, hreg v, hm, Nat.cast_id]
  obtain ⟨y₀, hy₀, hy₀d⟩ := exists_adj_dist_succ hG hvu
  have hmd : m < d := by
    rw [← hreg v, ← G.card_neighborFinset_eq_degree, hm]
    refine Finset.card_lt_card (Finset.filter_ssubset.2 ⟨y₀, ?_, ?_⟩)
    · simpa using hy₀
    · omega
  have hx : dl * (k - 1) + ∑ y ∈ G.neighborFinset v, min k (G.dist u y) = m + (d + dl) * (k - 1) := by
    rw [hsum]; ring
  have hdiv : (m + (d + dl) * (k - 1)) / (d + dl) = k - 1 := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  have hmod : (m + (d + dl) * (k - 1)) % (d + dl) = m := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [hx]
  refine ⟨fun y hy => ?_, Or.inl hdiv.symm⟩
  unfold FairShare
  rw [hdiv, hmod]
  rcases hnb y hy with h | h
  · exact Or.inl h
  · refine Or.inr ⟨?_, by omega⟩
    have : y ∈ ({y ∈ G.neighborFinset v | min k (G.dist u y) = k} : Finset V) := by simp_all
    have := Finset.card_pos.2 ⟨y, this⟩
    omega

/-- **Theorem 4.1** of [Berenbrink et al., PODC 2015]. Let `G` be a connected `d`-regular graph
with `dl` self-loops per node (`d⁺ = d + dl ≥ 1`). There exist a round-fair balancer `A` (even a
stateless one) and an initial load distribution such that the discrepancy stays at least
`diam(G) · d / 2` forever (the paper: `c · diam(G) · d` for some constant `c > 0`). -/
theorem theorem_4_1 (hG : G.Connected) {d : ℕ} (hreg : G.IsRegularOfDegree d) (dl : ℕ)
    (hD : 0 < d + dl) :
    ∃ A : Balancer G, A.RoundFair dl ∧ ∃ x₀ : V → ℕ, ∀ t, d * G.diam ≤ 2 * disc (A.load x₀ t) := by
  have := hG.nonempty
  have hD' : ∀ v, 0 < G.degree v + dl := fun v => by rw [hreg v]; exact hD
  obtain ⟨u, w, huw⟩ := G.exists_dist_eq_diam
  by_cases hsmall : G.diam = 0 ∨ (G.diam = 1 ∧ d ≤ 1)
  · -- degenerate cases: the default rule and a single token
    let A := patchedBalancer G dl hD' (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (by simp)
    refine ⟨A, patchedBalancer_roundFair dl hD' _ _ _ _
      (fun v => ⟨fun _ _ => by simp [FairShare], fun _ => 0, by simp, fun _ => by simp [FairShare]⟩),
      fun v => if v = u then 1 else 0, fun t => ?_⟩
    rcases hsmall with h0 | ⟨h1, hd1⟩
    · simp [h0]
    · have huw' : u ≠ w := by rintro rfl; simp at huw; omega
      have hcard : 2 ≤ Fintype.card V := by
        rw [← Finset.card_pair huw']; exact Finset.card_le_univ _
      have := one_le_disc_of_not_dvd (A.load (fun v => if v = u then 1 else 0) t) (by
        rw [Balancer.sum_load]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        intro hdvd; have := Nat.le_of_dvd one_pos hdvd; omega)
      rw [h1]; omega
  · push Not at hsmall
    obtain ⟨hdiam0, hdiam1⟩ := hsmall
    -- the steady construction of Appendix C.1
    let b : V → ℕ := G.dist u
    let o : V → V → ℕ := fun v y => min (b v) (b y)
    let k : V → ℕ := fun v => dl * (b v - 1)
    let xs : V → ℕ := fun v => k v + ∑ y ∈ G.neighborFinset v, o v y
    let A := patchedBalancer G dl hD' xs o k (fun _ => rfl)
    refine ⟨A, patchedBalancer_roundFair dl hD' _ _ _ _ (fun v => ?_), xs, fun t => ?_⟩
    · obtain ⟨h1, h2⟩ := steady_fair hG hreg dl u v
      rw [hreg v]
      exact ⟨h1, fun _ => b v - 1, by simp [k], fun _ => h2⟩
    · have hload : A.load xs t = xs := patchedBalancer_load dl hD' xs o k (fun _ => rfl)
        (fun v => by simp only [xs, o]; congr 1; exact Finset.sum_congr rfl fun y _ => min_comm _ _) t
      rw [hload]
      have hxu : xs u = 0 := by simp [xs, k, o, b]
      have hdisc : xs w ≤ disc xs := by have := sub_le_disc xs w u; omega
      -- lower bound on the load of `w`
      have hsum_ge : d * (G.diam - 1) ≤ ∑ y ∈ G.neighborFinset w, o w y := by
        calc d * (G.diam - 1) = ∑ y ∈ G.neighborFinset w, (G.diam - 1) := by
              rw [Finset.sum_const, smul_eq_mul, G.card_neighborFinset_eq_degree, hreg w]
          _ ≤ _ := Finset.sum_le_sum fun y hy => by
              rw [← huw]; exact le_min_dist_of_adj ((G.mem_neighborFinset _ _).1 hy)
      have hxw : ∑ y ∈ G.neighborFinset w, o w y ≤ xs w := Nat.le_add_left _ _
      by_cases h2 : 2 ≤ G.diam
      · have : d * G.diam ≤ 2 * (d * (G.diam - 1)) := by
          obtain ⟨e, he⟩ : ∃ e, G.diam = e + 2 := ⟨G.diam - 2, by omega⟩
          rw [he, show e + 2 - 1 = e + 1 by omega]; nlinarith
        omega
      · have hdiam : G.diam = 1 := by omega
        have hd2 : 2 ≤ d := by omega
        -- all neighbours of `w` other than `u` are at distance `1` from `u`
        have hadj : G.Adj w u := by
          rw [← G.dist_eq_one_iff_adj, SimpleGraph.dist_comm, huw, hdiam]
        have hge : d - 1 ≤ ∑ y ∈ G.neighborFinset w, o w y := by
          calc d - 1 = ∑ y ∈ (G.neighborFinset w).erase u, 1 := by
                rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
                  ((G.mem_neighborFinset _ _).2 hadj), G.card_neighborFinset_eq_degree, hreg w]
            _ ≤ ∑ y ∈ (G.neighborFinset w).erase u, o w y := Finset.sum_le_sum fun y hy => by
                have hyu : y ≠ u := Finset.ne_of_mem_erase hy
                have := hG.pos_dist_of_ne (Ne.symm hyu)
                show 1 ≤ min (G.dist u w) (G.dist u y)
                rw [huw, hdiam]; omega
            _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
        rw [hdiam]; omega

end Theorem41

end Podc.DeterministicLoadBalancing
