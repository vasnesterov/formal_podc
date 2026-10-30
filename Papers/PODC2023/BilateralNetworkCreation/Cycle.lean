import Papers.PODC2023.BilateralNetworkCreation.Levels
import Papers.PODC2023.BilateralNetworkCreation.Removal
import Cslib.Foundations.Combinatorics.SimpleGraph.CycleGraph

/-!
# Lemma 2.4: cycles in Bilateral Strong Equilibrium

`C_n` (Mathlib's `cycleGraph n` on `Fin n`) has distance cost `⌊n²/4⌋` at every vertex. We show
(`cycle_BSE`) that `C_n` is in BSE whenever

  `⌊n²/4⌋ - (n - 1) < α ≤ n(n-1)/2 - ⌊n²/4⌋`

(and `α ≥ 1`, `M > α n³`). For even `n` this is the paper's range
`n²/4 - (n-1) < α < n(n-2)/4` (with the right end included). For odd `n` the paper claims the range
`(n²-1)/4 - (n-1) < α < (n+1)(n-1)/4`, but the right end is wrong: for
`(n-1)²/4 < α < (n²-1)/4` the cycle is not even in RE (`cycle_not_RE`), e.g. `C_5` with `α = 5`
(`C5_not_BSE`). Lemma 2.4 itself (existence of a `Θ(n²)` range) is true: `lemma_2_4`.
-/

namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

/-! ### General facts used for coalition moves -/

section General

variable {V : Type*} [Fintype V] {M : ℕ} {G : SimpleGraph V}

lemma card_sub_one_le_distCost (hM : 1 ≤ M) (u : V) : Fintype.card V - 1 ≤ distCost M G u := by
  classical
  unfold distCost
  calc Fintype.card V - 1 = ∑ v ∈ univ.erase u, 1 := by simp [card_erase_of_mem]
    _ ≤ ∑ v ∈ univ.erase u, d M G u v :=
        Finset.sum_le_sum fun v hv => one_le_d (Finset.ne_of_mem_erase hv).symm hM
    _ ≤ ∑ v, d M G u v := Finset.sum_le_sum_of_subset (erase_subset _ _)

lemma M_le_distCost_of_not_connected [Nonempty V] (h : ¬ G.Connected) (u : V) :
    M ≤ distCost M G u := by
  have : ¬ G.Preconnected := fun h' => h ⟨h'⟩
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ G.Reachable a b := by
    by_contra h; push Not at h; exact this h
  obtain ⟨x, hx⟩ : ∃ x, ¬ G.Reachable u x := by
    by_cases hua : G.Reachable u a
    · exact ⟨b, fun hub => hab (hua.symm.trans hub)⟩
    · exact ⟨a, hua⟩
  calc M = d M G u x := (d_of_not_reachable hx).symm
    _ ≤ distCost M G u :=
      Finset.single_le_sum (f := fun v => d M G u v) (fun _ _ => Nat.zero_le _) (mem_univ x)

end General

/-! ### The cycle -/

section Cycle

open Fin.NatCast

variable {n : ℕ} [NeZero n] {M : ℕ}

lemma deg_cycle (hn : 3 ≤ n) (v : Fin n) : deg (cycleGraph n) v = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [deg_eq_degree, cycleGraph_degree_three_le]

lemma cycle_connected : (cycleGraph n).Connected := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  exact cycleGraph_connected

lemma exists_walk_forward (hn : 2 ≤ n) (u : Fin n) :
    ∀ k : ℕ, ∃ p : (cycleGraph n).Walk u (u + (k : Fin n)), p.length = k := by
  intro k
  induction k with
  | zero => exact ⟨Walk.nil.copy rfl (by simp), by simp⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih
    have h : u + ((k + 1 : ℕ) : Fin n) = (u + (k : Fin n)) + 1 := by push_cast; rw [add_assoc]
    exact ⟨(p.concat (cycleGraph_adj_add_one hn _)).copy rfl h.symm, by simp [hp]⟩

lemma d_cycle_le (hn : 2 ≤ n) (u v : Fin n) :
    d M (cycleGraph n) u v ≤ min (v - u).val (u - v).val := by
  refine le_min ?_ ?_
  · obtain ⟨p, hp⟩ := exists_walk_forward hn u (v - u).val
    have e : u + (((v - u).val : ℕ) : Fin n) = v := by rw [Fin.cast_val_eq_self, add_sub_cancel]
    have := d_le_of_walk (M := M) (p.copy rfl e)
    simpa [hp] using this
  · obtain ⟨p, hp⟩ := exists_walk_forward hn v (u - v).val
    have e : v + (((u - v).val : ℕ) : Fin n) = u := by rw [Fin.cast_val_eq_self, add_sub_cancel]
    have := d_le_of_walk (M := M) (p.copy rfl e).reverse
    simpa [hp] using this

lemma sum_range_min (m : ℕ) : ∑ i ∈ range m, min i (m - i) = m ^ 2 / 4 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp
    | 1 => simp
    | m + 2 =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have h : ∀ j ∈ range m, min (j + 1) (m + 2 - (j + 1)) = min j (m - j) + 1 := by
        intro j hj; rw [mem_range] at hj; omega
      rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih m (by omega)]
      have : (m + 2) ^ 2 = m ^ 2 + 4 * (m + 1) := by ring
      rw [this]; simp; omega

/-- The distance cost in `C_n` is at most `⌊n²/4⌋` (in fact equal, see `distCost_ge_deg_two`). -/
lemma distCost_cycle_le (hn : 2 ≤ n) (u : Fin n) :
    distCost M (cycleGraph n) u ≤ n ^ 2 / 4 := by
  unfold distCost
  calc ∑ v, d M (cycleGraph n) u v ≤ ∑ v : Fin n, min (v - u).val (u - v).val :=
        Finset.sum_le_sum fun v _ => d_cycle_le hn u v
    _ = ∑ k : Fin n, min k.val (-k).val := by
        refine Fintype.sum_equiv (Equiv.subRight u) _ _ fun v => ?_
        simp [neg_sub]
    _ = ∑ i ∈ range n, min i ((n - i) % n) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => min i ((n - i) % n))]
        congr 1
    _ = ∑ i ∈ range n, min i (n - i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [mem_range] at hi
        rcases Nat.eq_zero_or_pos i with rfl | h
        · simp
        · rw [Nat.mod_eq_of_lt (by omega)]
    _ = n ^ 2 / 4 := sum_range_min n

lemma distCost_cycle (hn : 3 ≤ n) (u : Fin n) : distCost M (cycleGraph n) u = n ^ 2 / 4 := by
  refine le_antisymm (distCost_cycle_le (by omega) u) ?_
  have := distCost_ge_deg_two (M := M) (cycle_connected (n := n))
    (fun x => (deg_cycle hn x).le) u (deg_cycle hn u)
  simpa using this

/-- The upper end of the BSE range of `C_n`: `n(n-1)/2 - ⌊n²/4⌋` (`= n(n-2)/4` for even `n`,
`(n-1)²/4` for odd `n`). -/
noncomputable def cycleHi (n : ℕ) : ℝ := ((n * (n - 1) / 2 : ℕ) : ℝ) - ((n ^ 2 / 4 : ℕ) : ℝ)

/-- The lower end of the BSE range of `C_n`: `⌊n²/4⌋ - (n - 1)`. -/
noncomputable def cycleLo (n : ℕ) : ℝ := ((n ^ 2 / 4 : ℕ) : ℝ) - ((n : ℝ) - 1)

/-- Lemma 2.4 (corrected range): `C_n` is in BSE for `cycleLo n < α ≤ cycleHi n`. -/
theorem cycle_BSE (hn : 3 ≤ n) {α : ℝ} (hα : 1 ≤ α) (hM : α * (n : ℝ) ^ 3 < M)
    (hlo : cycleLo n < α) (hhi : α ≤ cycleHi n) : BSE α M (cycleGraph n) := by
  classical
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hcM : n ≤ M := by have := card_le_M (V := Fin n) hα (by rwa [hcard]); rwa [hcard] at this
  set q : ℕ := n ^ 2 / 4 with hq
  -- the cost of any agent in `C_n`
  have hcost : ∀ x, cost α M (cycleGraph n) x = 2 * α + q := by
    intro x; unfold cost; rw [deg_cycle hn, distCost_cycle hn]; push_cast; ring
  intro Γ hΓ _ G' hmove
  by_contra hcon
  push Not at hcon
  -- every member strictly improves
  have himp : ∀ x ∈ Γ, cost α M G' x < 2 * α + q := fun x hx => by
    rw [← hcost]; exact hcon x hx
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hq4 : (q : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
    rw [hq]
    have : 4 * (n ^ 2 / 4) ≤ n ^ 2 := Nat.mul_div_le _ _
    have : (4 : ℝ) * ((n ^ 2 / 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  by_cases hbig : ∃ y, 3 ≤ deg G' y
  · -- a vertex of degree `≥ 3` is in the coalition and pays one more edge
    obtain ⟨y, hy⟩ := hbig
    have hyΓ : y ∈ Γ := by
      by_contra hyΓ
      have hsub : G'.neighborSet y ⊆ (cycleGraph n).neighborSet y := by
        intro z hz
        by_contra hz'
        exact hyΓ (hmove.2 y z hz hz').1
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := deg_cycle hn y
      unfold deg at hy h2; omega
    have h1 := himp y hyΓ
    have hd : n - 1 ≤ distCost M G' y := by
      have := card_sub_one_le_distCost (G := G') (M := M) (by omega) y; rwa [hcard] at this
    have hd' : (n : ℝ) - 1 ≤ distCost M G' y := by
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [show 1 ≤ n by omega]; ring
      rw [← this]; exact_mod_cast hd
    have hy' : (3 : ℝ) ≤ deg G' y := by exact_mod_cast hy
    unfold cost at h1
    unfold cycleLo at hlo
    nlinarith
  · push Not at hbig
    have hdeg2 : ∀ x, deg G' x ≤ 2 := fun x => by have := hbig x; omega
    obtain ⟨x, hx⟩ := hΓ
    have h1 := himp x hx
    unfold cost at h1
    have hdx0 : (0 : ℝ) ≤ α * deg G' x := by positivity
    by_cases hconn : G'.Connected
    · rcases (show deg G' x = 2 ∨ deg G' x = 1 ∨ deg G' x = 0 by have := hdeg2 x; omega)
        with h2 | h1' | h0
      · have := distCost_ge_deg_two (M := M) hconn hdeg2 x h2
        rw [hcard] at this
        have : (q : ℝ) ≤ distCost M G' x := by exact_mod_cast this
        rw [h2] at h1; push_cast at h1; linarith
      · have := distCost_ge_deg_le_one (M := M) hconn hdeg2 x h1'.le
        rw [hcard] at this
        have : ((n * (n - 1) / 2 : ℕ) : ℝ) ≤ distCost M G' x := by exact_mod_cast this
        unfold cycleHi at hhi
        rw [h1'] at h1; push_cast at h1
        linarith
      · have := distCost_ge_levels (M := M) hconn hdeg2 x
        rw [h0, sum_range_sub_one, hcard] at this
        have h2hh : 2 * (n * (n - 1) / 2) ≤ n * (n - 1) := Nat.mul_div_le _ _
        have : 2 * ((n * (n - 1) / 2 : ℕ) : ℝ) ≤ distCost M G' x := by
          exact_mod_cast h2hh.trans this
        unfold cycleHi at hhi
        rw [h0] at h1; push_cast at h1
        have hq0 : (0 : ℝ) ≤ q := by positivity
        linarith
    · have := M_le_distCost_of_not_connected (M := M) hconn x
      have hMd : (M : ℝ) ≤ distCost M G' x := by exact_mod_cast this
      -- `M > α n³ ≥ 2α + n²/4`
      have : 2 * α + (n : ℝ) ^ 2 / 4 ≤ α * (n : ℝ) ^ 3 := by
        have h3 : 3 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
        have hα0 : (0 : ℝ) ≤ α := by linarith
        nlinarith [mul_le_mul_of_nonneg_left h3 hα0, mul_nonneg (sub_nonneg.2 hα) (sq_nonneg (n : ℝ))]
      linarith

/-- For `α > n(n-1)/2 - ⌊n²/4⌋` the cycle is not in RE: an agent drops one of its edges. -/
theorem cycle_not_RE (hn : 3 ≤ n) {α : ℝ} (hM : n ≤ M) (hα : cycleHi n < α) :
    ¬ RE α M (cycleGraph n) := by
  classical
  intro hRE
  have h2 : 2 ≤ n := by omega
  have hadj : (cycleGraph n).Adj 0 (-1) := by
    have := cycleGraph_adj_add_one h2 (-1 : Fin n); simp at this; exact this.symm
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have h := hRE 0 (-1) hadj
  -- the path graph survives the removal
  have hpath : pathGraph n ≤ (cycleGraph n).deleteEdges {s(0, -1)} := by
    intro a b hab
    rw [deleteEdges_adj]
    refine ⟨pathGraph_le_cycleGraph hab, ?_⟩
    rw [pathGraph_adj] at hab
    have hm1 : ((-1 : Fin n) : ℕ) = n - 1 := by
      rw [Fin.val_neg', Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega),
        Nat.mod_eq_of_lt (show n - 1 < n by omega)]
    intro he
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hm1] at hab <;> omega
  have hwalk : ∀ j : ℕ, (hj : j < n) → ∃ p : (pathGraph n).Walk 0 ⟨j, hj⟩, p.length = j := by
    intro j
    induction j with
    | zero => intro hj; exact ⟨Walk.nil.copy rfl (by ext; simp), rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨p, hp⟩ := ih (by omega)
      have hadj' : (pathGraph n).Adj ⟨j, by omega⟩ ⟨j + 1, hj⟩ := by
        rw [pathGraph_adj]; left; rfl
      exact ⟨p.concat hadj', by simp [hp]⟩
  have hdist : distCost M ((cycleGraph n).deleteEdges {s(0, -1)}) 0 ≤ n * (n - 1) / 2 := by
    unfold distCost
    calc ∑ v, d M ((cycleGraph n).deleteEdges {s(0, -1)}) 0 v ≤ ∑ v : Fin n, v.val := by
          refine Finset.sum_le_sum fun v _ => ?_
          obtain ⟨p, hp⟩ := hwalk v.val v.isLt
          have := d_le_of_walk (M := M) (p.mapLe hpath)
          rw [Walk.length_mapLe, hp] at this
          exact this
      _ = ∑ i ∈ range n, i := Fin.sum_univ_eq_sum_range (fun i => i) n
      _ = n * (n - 1) / 2 := Finset.sum_range_id n
  have hlow : n ^ 2 / 4 ≤ distCost M (cycleGraph n) 0 := (distCost_cycle hn 0).ge
  unfold cost at h
  rw [deg_deleteEdges_single hadj, deg_cycle hn] at h
  have : (distCost M ((cycleGraph n).deleteEdges {s(0, -1)}) 0 : ℝ) ≤ ((n * (n - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hdist
  have : ((n ^ 2 / 4 : ℕ) : ℝ) ≤ distCost M (cycleGraph n) 0 := by exact_mod_cast hlow
  unfold cycleHi at hα
  push_cast at h
  linarith

/-- BSE implies RE (a one-agent coalition removing one edge). -/
theorem BSE.RE {V : Type*} [Fintype V] {α : ℝ} {G : SimpleGraph V} (h : BSE α M G) :
    RE α M G := by
  classical
  intro u v huv
  obtain ⟨x, hx, hle⟩ := h {u} (by simp)
    (by rw [card_singleton]; exact Fintype.card_pos_iff.2 ⟨u⟩)
    (G.deleteEdges {s(u, v)}) ⟨fun a b hab hab' => by
      simp only [deleteEdges_adj, Set.mem_singleton_iff, not_and, not_not] at hab'
      rcases Sym2.eq_iff.1 (hab' hab) with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp,
      fun a b hab hab' => absurd (deleteEdges_le _ hab) hab'⟩
  rw [mem_singleton] at hx; subst hx; exact hle

/-- The paper's odd-`n` range is too large: `C_5` with `α = 5` (inside the claimed range
`2 < α < 6`) is not in BSE (agent `0` improves by dropping an edge). -/
theorem C5_not_BSE : ¬ BSE (5 : ℝ) 626 (cycleGraph 5) := by
  intro h
  refine cycle_not_RE (n := 5) (by norm_num) (by norm_num) ?_ h.RE
  unfold cycleHi; norm_num

/-- For every odd `n ≥ 3` and `(n-1)²/4 < α < (n²-1)/4` (a sub-interval of the range claimed in the
proof of Lemma 2.4) `C_n` is not in BSE. -/
theorem cycle_odd_not_BSE (hn : 3 ≤ n) (hodd : n % 2 = 1) {α : ℝ} (hM : n ≤ M)
    (hα : ((n : ℝ) - 1) ^ 2 / 4 < α) : ¬ BSE α M (cycleGraph n) := by
  intro h
  refine cycle_not_RE hn hM ?_ h.RE
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  unfold cycleHi
  have e1 : (2 * m + 1) * (2 * m + 1 - 1) / 2 = (2 * m + 1) * m := by
    rw [show 2 * m + 1 - 1 = 2 * m by omega, show (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m)
      by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  have e2 : (2 * m + 1) ^ 2 / 4 = m * (m + 1) := by
    rw [show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]; omega
  rw [e1, e2]; push_cast at hα ⊢; nlinarith

end Cycle

/-- Lemma 2.4 of the paper: for every `n ≥ 3` there is a range of `α` of order `n²` for which
`C_n` is in BSE. Precisely: for all `α ≥ 1` with `cycleLo n < α ≤ cycleHi n` and all `M > α n³`,
`C_n` is in BSE; this range is nonempty, and `n²/8 ≤ cycleLo n`, `cycleHi n ≤ n²/4` for `n ≥ 8`. -/
theorem lemma_2_4 (n : ℕ) (hn : 3 ≤ n) :
    (∃ α : ℝ, 1 ≤ α ∧ cycleLo n < α ∧ α ≤ cycleHi n) ∧
    (8 ≤ n → (n : ℝ) ^ 2 / 8 ≤ cycleLo n) ∧ cycleHi n ≤ (n : ℝ) ^ 2 / 4 ∧
    ∀ α : ℝ, 1 ≤ α → cycleLo n < α → α ≤ cycleHi n → ∀ M : ℕ, α * (n : ℝ) ^ 3 < M →
      haveI : NeZero n := ⟨by omega⟩; BSE α M (cycleGraph n) := by
  -- arithmetic of the two ends
  have hq : (4 * (n ^ 2 / 4) + 1 ≥ n ^ 2) ∧ 4 * (n ^ 2 / 4) ≤ n ^ 2 := by
    constructor
    · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · rw [show (m + m) ^ 2 = 4 * (m * m) by ring]; omega
      · rw [show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]; omega
    · exact Nat.mul_div_le _ _
  have hh : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [show (m + m) * (m + m - 1) = 2 * (m * (m + m - 1)) by ring]; omega
    · rw [show 2 * m + 1 - 1 = 2 * m by omega,
        show (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) by ring]; omega
  have hq1 : (n : ℝ) ^ 2 ≤ 4 * ((n ^ 2 / 4 : ℕ) : ℝ) + 1 := by exact_mod_cast hq.1
  have hq2 : 4 * ((n ^ 2 / 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hq.2
  have hh' : 2 * ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    have : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      push_cast [show 1 ≤ n by omega]; ring
    rw [← this]; exact_mod_cast hh
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlohi : cycleLo n < cycleHi n := by unfold cycleLo cycleHi; nlinarith
  have hhi1 : 1 ≤ cycleHi n := by
    have hlt : ((n ^ 2 / 4 : ℕ) : ℝ) < ((n * (n - 1) / 2 : ℕ) : ℝ) := by nlinarith
    have hlt' : n ^ 2 / 4 + 1 ≤ n * (n - 1) / 2 := by exact_mod_cast hlt
    have : ((n ^ 2 / 4 : ℕ) : ℝ) + 1 ≤ ((n * (n - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hlt'
    unfold cycleHi; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h : cycleLo n < 1
    · exact ⟨1, le_rfl, h, hhi1⟩
    · exact ⟨cycleHi n, hhi1, hlohi, le_rfl⟩
  · intro h8
    have : (8 : ℝ) ≤ n := by exact_mod_cast h8
    unfold cycleLo; nlinarith
  · unfold cycleHi; nlinarith
  · intro α hα hlo hhi M hM
    haveI : NeZero n := ⟨by omega⟩
    exact cycle_BSE hn hα hM hlo hhi

end Podc.BilateralNetworkCreation
