import Papers.PODC2023.BilateralNetworkCreation.Prop38

/-!
# Proposition 3.9: a logarithmic lower bound on the PoA of trees in BGE

* `optCost_le_star`: the star costs `2(n-1)(α+n-1)`, so `cost(OPT) ≤ 2(n-1)(α+n-1)`;
* `LayerSized.isMedian`: the root of a layer-sized tree is a 1-median;
* `rho_ge_tree`: `ρ(G) ≥ (2(n-1)α + n·dist(r)) / (2(n-1)(α+n-1))` for a tree with 1-median `r`;
* `prop_3_9`: for `0 < γ ≤ 1`, `η^γ ≥ 512` (our explicit "sufficiently large") and
  `η ≤ α ≤ η^(2-γ)` there is a stretched binary tree with `η/42 ≤ n ≤ η/14` nodes in BGE with
  `ρ ≥ 25/32 + (γ/96) log₂ η`;
* `prop_3_9_uniform`: the same for every `η ≥ 512`, uniformly in `γ`.
-/

namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {α : ℝ} {M : ℕ}

/-! ### The star -/

/-- The star with center `c`. -/
def star (c : V) : SimpleGraph V := SimpleGraph.fromRel fun x _ => x = c

lemma star_adj {c x y : V} : (star c).Adj x y ↔ x ≠ y ∧ (x = c ∨ y = c) := by
  simp [star]

theorem optCost_le_star (hα : 0 ≤ α) (c : V) :
    optCost (V := V) α M ≤ 2 * ((Fintype.card V : ℝ) - 1) * (α + Fintype.card V - 1) := by
  set n := Fintype.card V
  have hn1 : 1 ≤ n := Fintype.card_pos_iff.2 ⟨c⟩
  refine (optCost_le hα (star c)).trans ?_
  -- the center
  have hc_deg : deg (star c) c = n - 1 := by
    have : (star c).neighborSet c = Set.univ \ {c} := by
      ext y; simp [star_adj, eq_comm]
    unfold deg; rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ c), Set.ncard_univ,
      Nat.card_eq_fintype_card]
  have hc_dist : distCost M (star c) c ≤ n - 1 := by
    unfold distCost
    calc ∑ y, d M (star c) c y ≤ ∑ y, (if y = c then 0 else 1) := by
          refine Finset.sum_le_sum fun y _ => ?_
          split_ifs with h
          · subst h; simp
          · rw [d_eq_one_of_adj (star_adj.2 ⟨Ne.symm h, Or.inl rfl⟩)]
      _ = n - 1 := by
          rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one,
            zero_add, Finset.filter_ne' univ c, card_erase_of_mem (mem_univ _), card_univ]
  -- the leaves
  have hx_deg : ∀ x, x ≠ c → deg (star c) x = 1 := by
    intro x hx
    have : (star c).neighborSet x = {c} := by
      ext y; simp only [mem_neighborSet, star_adj, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxy, h | h⟩
        · exact absurd h hx
        · exact h
      · rintro rfl; exact ⟨hx, Or.inr rfl⟩
    unfold deg; rw [this, Set.ncard_singleton]
  have hx_dist : ∀ x, x ≠ c → distCost M (star c) x ≤ 2 * n - 3 := by
    intro x hx
    unfold distCost
    calc ∑ y, d M (star c) x y ≤ ∑ y, (if y = x then 0 else if y = c then 1 else 2) := by
          refine Finset.sum_le_sum fun y _ => ?_
          split_ifs with h1 h2
          · subst h1; simp
          · subst h2; rw [d_eq_one_of_adj (star_adj.2 ⟨hx, Or.inr rfl⟩)]
          · have h1' : (star c).Adj x c := star_adj.2 ⟨hx, Or.inr rfl⟩
            have h2' : (star c).Adj c y := star_adj.2 ⟨Ne.symm h2, Or.inl rfl⟩
            exact (d_le_of_walk (Walk.cons h1' (Walk.cons h2' Walk.nil))).trans (by simp)
      _ = 2 * n - 3 := by
          rw [← Finset.add_sum_erase _ _ (mem_univ x), if_pos rfl, zero_add,
            ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨Ne.symm hx, mem_univ c⟩)]
          simp only [if_neg (Ne.symm hx), if_true]
          have hs : ∑ y ∈ (univ.erase x).erase c,
              (if y = x then 0 else if y = c then 1 else 2) = ∑ _y ∈ (univ.erase x).erase c, 2 :=
            Finset.sum_congr rfl fun y hy => by
              rw [mem_erase, mem_erase] at hy; rw [if_neg hy.2.1, if_neg hy.1]
          rw [hs, Finset.sum_const, card_erase_of_mem (mem_erase.2 ⟨Ne.symm hx, mem_univ c⟩),
            card_erase_of_mem (mem_univ _), card_univ, smul_eq_mul]
          have : 2 ≤ n := by
            have : ({x, c} : Finset V).card = 2 := card_pair hx
            rw [← this]; exact card_le_univ _
          omega
  unfold socialCost
  rw [← Finset.add_sum_erase _ _ (mem_univ c)]
  have h1 : cost α M (star c) c ≤ α * (n - 1) + (n - 1) := by
    unfold cost; rw [hc_deg, Nat.cast_sub hn1]
    have : (distCost M (star c) c : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hc_dist
    rw [Nat.cast_sub hn1] at this; push_cast at this ⊢; linarith
  by_cases hn : n = 1
  · have : univ.erase c = ∅ := by
      rw [← card_eq_zero, card_erase_of_mem (mem_univ _), card_univ]; omega
    rw [this, Finset.sum_empty]
    have : (n : ℝ) = 1 := by exact_mod_cast hn
    rw [this] at h1 ⊢; linarith
  have h2 : ∀ x ∈ univ.erase c, cost α M (star c) x ≤ α + (2 * n - 3) := by
    intro x hx
    have hx' := Finset.ne_of_mem_erase hx
    unfold cost; rw [hx_deg x hx']
    have : (distCost M (star c) x : ℝ) ≤ ((2 * n - 3 : ℕ) : ℝ) := by exact_mod_cast hx_dist x hx'
    rw [Nat.cast_sub (by omega)] at this; push_cast at this ⊢; linarith
  have h3 := Finset.sum_le_sum h2
  rw [Finset.sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
    Nat.cast_sub hn1] at h3
  push_cast at h3
  nlinarith

/-! ### Medians and the social cost of trees -/

variable {G : SimpleGraph V} {r : V}

theorem LayerSized.isMedian {k : ℕ} {f : ℕ → ℕ} (hT : G.IsTree) (hL : LayerSized G r k f) :
    IsMedian G r := by
  intro y
  have h := phi_eq (r := r) hT univ y
  have hterm : ∀ t ∈ range (G.dist r y), (0 : ℤ) ≤
      (((univ : Finset V).card : ℤ) -
        2 * (((univ : Finset V).filter (· ∈ sub G r (anc G r y (t + 1)))).card : ℤ)) := by
    intro t ht
    rw [mem_range] at ht
    obtain ⟨h1, -⟩ := anc_spec (r := r) hT (y := y) (t := t + 1) (by omega)
    have hf : (univ.filter (· ∈ sub G r (anc G r y (t + 1)))) = sub G r (anc G r y (t + 1)) := by
      ext; simp
    rw [hf, hL.card_sub, h1, card_univ]
    have := hL.two_mul_f_le (ℓ := t + 1) (by omega)
    have : (2 * f (t + 1) : ℤ) ≤ Fintype.card V := by exact_mod_cast this
    linarith
  have := Finset.sum_nonneg hterm
  have : ((∑ x, G.dist r x : ℕ) : ℤ) ≤ ((∑ x, G.dist y x : ℕ) : ℤ) := by linarith
  exact_mod_cast this

/-- For a tree with 1-median `r`: `ρ(G) ≥ (2(n-1)α + n·dist(r)) / (2(n-1)(α+n-1))`. -/
theorem rho_ge_tree (hT : G.IsTree) (hr : IsMedian G r) (hα : 1 ≤ α)
    (hM : α * (Fintype.card V) ^ 3 < M) (hn : 2 ≤ Fintype.card V) :
    (2 * ((Fintype.card V : ℝ) - 1) * α + Fintype.card V * ∑ x, (G.dist r x : ℝ)) /
      (2 * ((Fintype.card V : ℝ) - 1) * (α + Fintype.card V - 1)) ≤ rho α M G := by
  classical
  set n := Fintype.card V
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hG := hT.connected
  have hpos : 0 < 2 * ((n : ℝ) - 1) * (α + n - 1) := by
    have : 0 < (n : ℝ) - 1 := by linarith
    have : 0 < α + n - 1 := by linarith
    positivity
  have hO1 := optCost_ge (V := V) hα hM
  have hO2 := optCost_le_star (V := V) (α := α) (M := M) (by linarith) r
  -- social cost of the tree
  have hdeg : ∑ x, (deg G x : ℝ) = 2 * (n - 1) := by
    simp only [deg_eq_degree]
    have h1 := sum_degrees_eq_twice_card_edges G
    have h2 := hT.card_edgeFinset
    have : (∑ x, (G.degree x : ℝ)) = ((∑ x, G.degree x : ℕ) : ℝ) := by push_cast; rfl
    rw [this, h1]; push_cast
    have : (#G.edgeFinset : ℝ) = n - 1 := by
      have : (#G.edgeFinset : ℝ) + 1 = n := by exact_mod_cast h2
      linarith
    rw [this]
  have hdist : (n : ℝ) * ∑ x, (G.dist r x : ℝ) ≤ ∑ v, (distCost M G v : ℝ) := by
    have : ∀ v, (∑ x, (G.dist r x : ℝ)) ≤ distCost M G v := by
      intro v
      rw [distCost_eq_sum_dist hG]
      exact_mod_cast hr v
    have := Finset.sum_le_sum fun v (_ : v ∈ univ) => this v
    rw [Finset.sum_const, card_univ, nsmul_eq_mul] at this
    exact this
  have hsoc : 2 * ((n : ℝ) - 1) * α + n * ∑ x, (G.dist r x : ℝ) ≤ socialCost α M G := by
    unfold socialCost cost
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdeg]
    linarith
  unfold rho
  have hnum : 0 ≤ 2 * ((n : ℝ) - 1) * α + n * ∑ x, (G.dist r x : ℝ) := by
    have : 0 ≤ (n : ℝ) - 1 := by linarith
    positivity
  calc _ ≤ (2 * ((n : ℝ) - 1) * α + n * ∑ x, (G.dist r x : ℝ)) / optCost α M :=
        div_le_div_of_nonneg_left hnum (hpos.trans_le hO1) hO2
    _ ≤ socialCost α M G / optCost α M :=
        div_le_div_of_nonneg_right hsoc (hpos.trans_le hO1).le

/-! ### Choosing the depth (Lemma D.8) -/

/-- Number of nodes of the `k`-stretched binary tree of depth `d`. -/
def nS (d k : ℕ) : ℕ := (2 ^ (d + 1) - 2) * k + 1

lemma nS_succ (d k : ℕ) : nS (d + 1) k = 2 * nS d k + 2 * k - 1 := by
  unfold nS
  have h1 : 2 ≤ 2 ^ (d + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) by ring]
  have : (2 * 2 ^ (d + 1) - 2) * k = 2 * ((2 ^ (d + 1) - 2) * k) + 2 * k := by
    rw [show 2 * 2 ^ (d + 1) - 2 = 2 * (2 ^ (d + 1) - 2) + 2 by omega]; ring
  rw [this]; omega

lemma nS_le_pow (d k : ℕ) (hk : 1 ≤ k) : nS d k ≤ 2 ^ (d + 1) * k := by
  unfold nS
  have h1 : 2 ≤ 2 ^ (d + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.sub_mul]
  have : 2 * k ≤ 2 ^ (d + 1) * k := Nat.mul_le_mul_right _ h1
  omega

/-- Lemma D.8 (the parts used): for `t ≥ 2k + 1` the maximal depth `d` with `n(d) ≤ t` satisfies
`d ≥ 1`, `t/3 ≤ n(d) ≤ t` and `t < 2^(d+2) k`. -/
lemma exists_depth (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 2 * k + 1 ≤ t) :
    ∃ d, 1 ≤ d ∧ (nS d k : ℝ) ≤ t ∧ t / 3 ≤ nS d k ∧ t < 2 ^ (d + 2) * k := by
  have hex : ∃ d, t < nS (d + 1) k := by
    obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : ℝ) < 2)
    refine ⟨d, lt_of_lt_of_le hd ?_⟩
    have : 2 ^ d ≤ nS (d + 1) k := by
      unfold nS
      have h1 : 2 ^ d * 2 ≤ 2 ^ (d + 1 + 1) - 2 := by
        rw [show 2 ^ (d + 1 + 1) = 2 ^ d * 4 by ring]
        have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
        omega
      have : 2 ^ (d + 1 + 1) - 2 ≤ (2 ^ (d + 1 + 1) - 2) * k := Nat.le_mul_of_pos_right _ hk
      omega
    exact_mod_cast this
  classical
  set d := Nat.find hex with hd
  have hP : t < nS (d + 1) k := Nat.find_spec hex
  have hd1 : 1 ≤ d := by
    by_contra h
    push Not at h
    have h0 : d = 0 := by omega
    rw [h0] at hP
    have : nS (0 + 1) k = 2 * k + 1 := by unfold nS; norm_num
    rw [this] at hP
    push_cast at hP
    linarith
  have hle : (nS d k : ℝ) ≤ t := by
    have := Nat.find_min hex (show d - 1 < d by omega)
    push Not at this
    rwa [show d - 1 + 1 = d by omega] at this
  have h3 : nS (d + 1) k ≤ 3 * nS d k := by
    rw [nS_succ]
    have : 2 * k + 1 ≤ nS d k := by
      unfold nS
      have h1 : 4 ≤ 2 ^ (d + 1) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 * k ≤ (2 ^ (d + 1) - 2) * k := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  refine ⟨d, hd1, hle, ?_, ?_⟩
  · have : (nS (d + 1) k : ℝ) ≤ 3 * nS d k := by exact_mod_cast h3
    linarith
  · have := nS_le_pow (d + 1) k hk
    have : (nS (d + 1) k : ℝ) ≤ 2 ^ (d + 2) * k := by exact_mod_cast this
    linarith

lemma card_SVert_eq_nS (d k : ℕ) : Fintype.card (SVert d k) = nS d k := card_SVert

/-- Proposition 3.9. For `0 < γ ≤ 1`, `η ∈ ℕ` with `η^γ ≥ 512` (an explicit version of "`η`
sufficiently large") and `η ≤ α ≤ η^(2-γ)`, there is a stretched binary tree `G` with
`η/42 ≤ n ≤ η/14` nodes that is in BGE (for every `M > α n³`) with
`ρ(G) ≥ 25/32 + (γ/96) log₂ η`. -/
theorem prop_3_9 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (η : ℕ) (hη : (512 : ℝ) ≤ (η : ℝ) ^ γ)
    (α : ℝ) (hα1 : (η : ℝ) ≤ α) (hα2 : α ≤ (η : ℝ) ^ (2 - γ)) :
    ∃ d k : ℕ, 1 ≤ k ∧ (η : ℝ) / 42 ≤ Fintype.card (SVert d k) ∧
      (Fintype.card (SVert d k) : ℝ) ≤ η / 14 ∧
      ∀ M : ℕ, α * (Fintype.card (SVert d k)) ^ 3 < M →
        BGE α M (stretchedTree d k) ∧
          25 / 32 + γ / 96 * Real.logb 2 η ≤ rho α M (stretchedTree d k) := by
  set e : ℝ := (η : ℝ) with he
  have he1 : 1 ≤ e := by
    by_contra h
    push Not at h
    have : η = 0 := by
      have : (η : ℝ) < 1 := h
      exact_mod_cast (show η < 1 by exact_mod_cast this) |> Nat.lt_one_iff.1
    rw [he, this, Nat.cast_zero, Real.zero_rpow hγ0.ne'] at hη
    linarith
  have hepos : 0 < e := by linarith
  have heγ : e ^ γ ≤ e := by
    calc e ^ γ ≤ e ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le he1 hγ1
      _ = e := Real.rpow_one e
  have he512 : 512 ≤ e := le_trans hη heγ
  have heγpos : 0 < e ^ γ := Real.rpow_pos_of_pos hepos γ
  have h2γ : e ^ (2 - γ) = e ^ 2 / e ^ γ := by
    rw [Real.rpow_sub hepos, Real.rpow_two]
  -- the stretch factor `k = ⌈α/η⌉`
  set k := ⌈α / e⌉₊ with hkdef
  have hαe : 1 ≤ α / e := by rw [le_div_iff₀ hepos]; linarith
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
  have hkge : α / e ≤ k := Nat.le_ceil _
  have hklt : (k : ℝ) < α / e + 1 := Nat.ceil_lt_add_one (by linarith)
  have hk2 : (k : ℝ) ≤ 2 * α / e := by
    have : 2 * α / e = α / e + α / e := by ring
    linarith
  have hαe2 : α / e ≤ e / 512 := by
    rw [div_le_div_iff₀ hepos (by norm_num)]
    have : α * e ^ γ ≤ e ^ 2 := by
      rw [h2γ, le_div_iff₀ heγpos] at hα2; exact hα2
    nlinarith
  -- the target size `t = η/14`
  have ht : 2 * k + 1 ≤ e / 14 := by
    have : (2 * k + 1 : ℝ) ≤ 2 * (e / 512 + 1) + 1 := by linarith
    have hk' : ((2 * k + 1 : ℕ) : ℝ) = 2 * k + 1 := by push_cast; ring
    rw [hk'] at *
    linarith
  obtain ⟨d, hd1, hnle, hnge, hpow⟩ := exists_depth k hk1 (e / 14) (by exact_mod_cast ht)
  refine ⟨d, k, hk1, ?_, ?_, ?_⟩
  · rw [card_SVert_eq_nS]; linarith
  · rw [card_SVert_eq_nS]; linarith
  intro M hM
  have hcard : (Fintype.card (SVert d k) : ℝ) = nS d k := by rw [card_SVert_eq_nS]
  have hn14 : (Fintype.card (SVert d k) : ℝ) ≤ e / 14 := by rw [hcard]; exact hnle
  have hn42 : e / 42 ≤ (Fintype.card (SVert d k) : ℝ) := by rw [hcard]; linarith
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hα0 : 0 ≤ α := by linarith
  have h2αe : 0 ≤ 2 * α / e := div_nonneg (by linarith) hepos.le
  have h7 : 7 * (k : ℝ) * Fintype.card (SVert d k) ≤ α := by
    have hn0 : (0 : ℝ) ≤ Fintype.card (SVert d k) := Nat.cast_nonneg _
    have h1 := mul_le_mul hk2 hn14 hn0 h2αe
    have h2 : 2 * α / e * (e / 14) = α / 7 := by field_simp; ring
    nlinarith
  have hα1' : 1 ≤ α := by linarith
  refine ⟨prop_3_8 d k hk1 (by push_cast; linarith) hM, ?_⟩
  -- the cost ratio
  have hn2 : 2 ≤ Fintype.card (SVert d k) := by
    have : (2 : ℝ) ≤ Fintype.card (SVert d k) := by linarith
    exact_mod_cast this
  have hρ := rho_ge_tree (r := sRoot) stretchedTree_isTree
    ((stretched_layerSized d k hk1).isMedian stretchedTree_isTree) hα1' hM hn2
  have hD1 := lemmaD1 (d := d) hk1
  have hsum : ∑ x, ((stretchedTree d k).dist sRoot x : ℝ) = ∑ x : SVert d k, ((x.1.val : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun x _ => by rw [stretchedTree_dist_root]
  rw [hsum] at hρ
  refine le_trans ?_ hρ
  generalize (Fintype.card (SVert d k) : ℝ) = n at hρ hn14 hn42 hD1 ⊢
  generalize (∑ x : SVert d k, ((x.1.val : ℕ) : ℝ)) = S at hρ hD1 ⊢
  -- the depth bound `d > γ log η - 7`
  set L := Real.logb 2 e
  have hγL : 9 ≤ γ * L := by
    have : Real.logb 2 512 ≤ Real.logb 2 (e ^ γ) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) hη
    rw [Real.logb_rpow_eq_mul_logb_of_pos hepos] at this
    have h512 : Real.logb 2 512 = 9 := by
      rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    linarith
  have hdL : γ * L - 7 < d := by
    have h1 : e ^ γ / 112 < 2 ^ d := by
      have : e / 14 < 2 ^ d * (4 * k) := by
        calc e / 14 < 2 ^ (d + 2) * k := hpow
          _ = 2 ^ d * (4 * k) := by ring
      have h2 : e ^ γ / 112 ≤ e / (56 * k) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have h3 : (k : ℝ) * e ≤ 2 * α := by
          have := hk2; rw [le_div_iff₀ hepos] at this; linarith
        have h4 : α * e ^ γ ≤ e ^ 2 := by
          rw [h2γ, le_div_iff₀ heγpos] at hα2; exact hα2
        nlinarith
      have h5 : e / (56 * k) < 2 ^ d := by
        rw [div_lt_iff₀ (by positivity)]; linarith
      linarith
    have h6 := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h1
    rw [Real.logb_div heγpos.ne' (by norm_num), Real.logb_rpow_eq_mul_logb_of_pos hepos] at h6
    have h7' : Real.logb 2 ((2 : ℝ) ^ d) = d := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
    have h8 : Real.logb 2 112 < 7 := by
      have : Real.logb 2 112 < Real.logb 2 128 :=
        Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
      have h128 : Real.logb 2 128 = 7 := by
        rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num)]
        norm_num
      linarith
    linarith
  -- final estimate
  have hn1 : 0 ≤ n - 1 := by linarith
  have hd0 : 0 ≤ γ * L - 9 := by linarith
  have hX : α / 42 * (γ * L - 9) ≤ (k : ℝ) * ((d : ℝ) - 3 / 2) * n := by
    have h1 : α / e * (e / 42) = α / 42 := by field_simp
    have h2 : (γ * L - 9) ≤ (d : ℝ) - 3 / 2 := by linarith
    have hae : 0 ≤ α / e := div_nonneg hα0 hepos.le
    have h3 : α / e * (γ * L - 9) ≤ (k : ℝ) * ((d : ℝ) - 3 / 2) :=
      mul_le_mul hkge h2 hd0 (by linarith)
    have h4 : 0 ≤ α / e * (γ * L - 9) := mul_nonneg hae hd0
    calc α / 42 * (γ * L - 9) = (α / e) * (γ * L - 9) * (e / 42) := by rw [← h1]; ring
      _ ≤ (k : ℝ) * ((d : ℝ) - 3 / 2) * n :=
          mul_le_mul h3 hn42 (by positivity) (by linarith)
  have hS : 0 ≤ S := by
    have : 0 ≤ α / 42 * (γ * L - 9) := mul_nonneg (by linarith) hd0
    linarith
  have hden : 2 * (α + n - 1) ≤ 15 / 7 * α := by linarith
  have hpos : 0 < 2 * (n - 1) * (α + n - 1) := by
    have : 0 < n - 1 := by linarith
    have : 0 < α + n - 1 := by linarith
    positivity
  rw [le_div_iff₀ hpos]
  have hγ96 : γ / 96 * L = γ * L / 96 := by ring
  have hR : 0 ≤ 25 / 32 + γ / 96 * L := by rw [hγ96]; linarith
  have key : (25 / 32 + γ / 96 * L) * (15 / 7 * α) ≤ 2 * α + α / 42 * (γ * L - 9) := by
    rw [hγ96]
    have hP : 0 ≤ α * (γ * L) := mul_nonneg hα0 (by linarith)
    have e1 : (25 / 32 + γ * L / 96) * (15 / 7 * α) = 375 / 224 * α + 15 / 672 * (α * (γ * L)) := by
      ring
    have e2 : 2 * α + α / 42 * (γ * L - 9) = (2 - 9 / 42) * α + 1 / 42 * (α * (γ * L)) := by ring
    rw [e1, e2]
    linarith
  have hnS : (n - 1) * S ≤ n * S := by
    have : n * S - (n - 1) * S = S := by ring
    linarith
  have hXS : α / 42 * (γ * L - 9) ≤ S := le_trans hX hD1
  calc (25 / 32 + γ / 96 * L) * (2 * (n - 1) * (α + n - 1))
      = (n - 1) * ((25 / 32 + γ / 96 * L) * (2 * (α + n - 1))) := by ring
    _ ≤ (n - 1) * ((25 / 32 + γ / 96 * L) * (15 / 7 * α)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden hR) hn1
    _ ≤ (n - 1) * (2 * α + α / 42 * (γ * L - 9)) := mul_le_mul_of_nonneg_left key hn1
    _ ≤ (n - 1) * (2 * α + S) := mul_le_mul_of_nonneg_left (by linarith) hn1
    _ = 2 * (n - 1) * α + (n - 1) * S := by ring
    _ ≤ 2 * (n - 1) * α + n * S := by linarith

/-! ### Proposition 3.9 with a threshold independent of `γ` -/

/-- `ρ(G) ≥ 1` for every graph (`α ≥ 1`, `n ≥ 2`, `M > α n³`). -/
theorem one_le_rho {V : Type*} [Fintype V] {α : ℝ} {M : ℕ} (hα : 1 ≤ α)
    (hM : α * (Fintype.card V) ^ 3 < M) (hn : 2 ≤ Fintype.card V) (G : SimpleGraph V) :
    1 ≤ rho α M G := by
  have hO := optCost_ge (V := V) hα hM
  have hn' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hpos : 0 < 2 * ((Fintype.card V : ℝ) - 1) * (α + Fintype.card V - 1) := by
    have : 0 < (Fintype.card V : ℝ) - 1 := by linarith
    have : 0 < α + Fintype.card V - 1 := by linarith
    positivity
  unfold rho
  rw [one_le_div (hpos.trans_le hO)]
  exact optCost_le (by linarith) G

/-- Proposition 3.9, read with a threshold on `η` that does not depend on `γ`: the conclusion of
`prop_3_9` holds for all `0 < γ ≤ 1` and all `η ≥ 512`. If `η^γ < 512`, the claimed bound is
below `1 ≤ ρ`, and the complete binary tree (`k = 1`) of the right size is in BGE. -/
theorem prop_3_9_uniform (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (η : ℕ) (hη : 512 ≤ η)
    (α : ℝ) (hα1 : (η : ℝ) ≤ α) (hα2 : α ≤ (η : ℝ) ^ (2 - γ)) :
    ∃ d k : ℕ, 1 ≤ k ∧ (η : ℝ) / 42 ≤ Fintype.card (SVert d k) ∧
      (Fintype.card (SVert d k) : ℝ) ≤ η / 14 ∧
      ∀ M : ℕ, α * (Fintype.card (SVert d k)) ^ 3 < M →
        BGE α M (stretchedTree d k) ∧
          25 / 32 + γ / 96 * Real.logb 2 η ≤ rho α M (stretchedTree d k) := by
  by_cases h : (512 : ℝ) ≤ (η : ℝ) ^ γ
  · exact prop_3_9 γ hγ0 hγ1 η h α hα1 hα2
  push Not at h
  have he : (512 : ℝ) ≤ η := by exact_mod_cast hη
  have hepos : (0 : ℝ) < η := by linarith
  obtain ⟨d, -, hnle, hnge, -⟩ := exists_depth 1 le_rfl ((η : ℝ) / 14)
    (by push_cast; linarith)
  have hcard : (Fintype.card (SVert d 1) : ℝ) = nS d 1 := by rw [card_SVert_eq_nS]
  refine ⟨d, 1, le_rfl, by rw [hcard]; linarith, by rw [hcard]; exact hnle, fun M hM => ?_⟩
  refine ⟨prop_3_8 d 1 le_rfl (by push_cast; rw [hcard]; linarith) hM, ?_⟩
  have hn2 : 2 ≤ Fintype.card (SVert d 1) := by
    have : (2 : ℝ) ≤ Fintype.card (SVert d 1) := by rw [hcard]; linarith
    exact_mod_cast this
  refine le_trans ?_ (one_le_rho (by linarith) hM hn2 _)
  have hL : γ * Real.logb 2 η < 9 := by
    have := Real.logb_lt_logb (b := 2) (by norm_num) (Real.rpow_pos_of_pos hepos γ) h
    rw [Real.logb_rpow_eq_mul_logb_of_pos hepos] at this
    have h512 : Real.logb 2 512 = 9 := by
      rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    linarith
  have : γ / 96 * Real.logb 2 η = γ * Real.logb 2 η / 96 := by ring
  rw [this]; linarith

end Podc.BilateralNetworkCreation
