import Papers.PODC2022.DominatingSetArboricity.Basic

/-!
# The partial dominating set (Lemma 4.1) and the deterministic algorithm (Theorems 1.1, 3.1)

The primal–dual partial dominating set procedure of Section 4.1, as a centralized description of
the synchronous rounds (the distributed implementation is in `Distributed.lean`):

* every vertex starts with packing value `x_v = τ_v / (Δ + 1)`;
* in each iteration, every `u` with `X_u = ∑_{v ∈ N⁺_u} x_v ≥ w_u / (1 + ε)` joins `S`, and every
  vertex not dominated by (the new) `S` multiplies its packing value by `1 + ε`;
* the number of iterations is the least `r` with `λ < (1+ε)^r / (Δ+1)`.

Main results:

* `charging` — the charging argument via an orientation of out-degree `≤ α` (the core of
  Lemma 4.1(a) and of Lemma 3.2(1)).
* `lemma_4_1` — Lemma 4.1: feasibility, properties (a), (b).
* `numIter_le` — the number of iterations is `≤ 1 + 2 log(max 1 (λ(Δ+1)))/ε` (for `ε ≤ 1`).
* `theorem_1_1` — Theorem 1.1: the deterministic algorithm outputs a dominating set of weight
  `≤ (2α+1)(1+ε) · w(D)` for every dominating set `D`.
* `theorem_3_1` — Theorem 3.1 (unweighted case).
-/

set_option linter.unusedSectionVars false

namespace DominatingSetArboricity

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `X_u = ∑_{v ∈ N⁺_u} x_v`. -/
def X (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (u : V) : ℝ := ∑ v ∈ cnbr G u, x v

/-- In-neighbours of `u` w.r.t. an orientation. -/
def inNbr {α : ℕ} (o : G.OutOrientation α) (u : V) : Finset V :=
  (G.neighborFinset u).filter fun v => u ∈ o.out v

omit [Fintype V] in
theorem sum_union3_le {s t r : Finset V} {f : V → ℝ} (hf : ∀ v, 0 ≤ f v) :
    ∑ v ∈ s ∪ t ∪ r, f v ≤ ∑ v ∈ s, f v + ∑ v ∈ t, f v + ∑ v ∈ r, f v := by
  have h1 : ∀ a b : Finset V, ∑ v ∈ a ∪ b, f v ≤ ∑ v ∈ a, f v + ∑ v ∈ b, f v := fun a b => by
    rw [← sum_union_inter]; linarith [sum_nonneg fun v (_ : v ∈ a ∩ b) => hf v]
  exact (h1 _ _).trans (by linarith [h1 s t])

/-- `X_u ≤ x_u + ∑_{out} x + ∑_{in} x`. -/
theorem X_le_out_in {α : ℕ} (o : G.OutOrientation α) {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) (u : V) :
    X G x u ≤ x u + ∑ v ∈ o.out u, x v + ∑ v ∈ inNbr o u, x v := by
  have hsub : cnbr G u ⊆ {u} ∪ o.out u ∪ inNbr o u := by
    intro v hv
    rcases mem_cnbr.1 hv with rfl | h
    · simp
    · rcases o.mem_or_mem h with h' | h'
      · simp [h']
      · simp [inNbr, h, h']
  calc X G x u ≤ ∑ v ∈ {u} ∪ o.out u ∪ inNbr o u, x v :=
        sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => hx v
    _ ≤ _ := by simpa using sum_union3_le (s := {u}) (t := o.out u) (r := inNbr o u) hx

/-- **The charging argument** (proof of Lemma 4.1(a), and of Lemma 3.2(1) for unit weights).
If every `u ∈ S` has `X_u ≥ w_u/(1+ε)` and every dominated vertex has `x_v ≤ λ τ_v`, then
`w_S ≤ α (1/(1+ε) - λ(α+1))⁻¹ ∑_{v ∈ N⁺_S} x_v`. -/
theorem charging {α : ℕ} (o : G.OutOrientation α) {w x : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (hx : ∀ v, 0 ≤ x v) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 ≤ lam)
    (hc : 0 < 1 / (1 + ε) - lam * (α + 1)) {S : Finset V}
    (hS : ∀ u ∈ S, w u / (1 + ε) ≤ X G x u) (hdom : ∀ v ∈ dom G S, x v ≤ lam * tau G w v) :
    wt w S ≤ α * (1 / (1 + ε) - lam * (α + 1))⁻¹ * ∑ v ∈ dom G S, x v := by
  set c := 1 / (1 + ε) - lam * (α + 1) with hcdef
  -- per-vertex bound: `w_u · c ≤ ∑_{in u} x`
  have hu : ∀ u ∈ S, w u * c ≤ ∑ v ∈ inNbr o u, x v := by
    intro u huS
    have hmem : ∀ v ∈ cnbr G u, v ∈ dom G S := fun v hv =>
      mem_dom.2 ⟨u, huS, mem_cnbr_comm.1 hv⟩
    have h1 : x u ≤ lam * w u :=
      (hdom u (hmem u (self_mem_cnbr u))).trans
        (mul_le_mul_of_nonneg_left (tau_le_self w u) hlam)
    have h2 : ∑ v ∈ o.out u, x v ≤ α * (lam * w u) := by
      calc ∑ v ∈ o.out u, x v ≤ ∑ _v ∈ o.out u, lam * w u := by
            refine sum_le_sum fun v hv => ?_
            have hadj := o.adj_of_mem hv
            refine (hdom v (hmem v (mem_cnbr.2 (Or.inr hadj)))).trans ?_
            exact mul_le_mul_of_nonneg_left
              (tau_le (mem_cnbr.2 (Or.inr hadj.symm))) hlam
        _ = (o.out u).card * (lam * w u) := by simp
        _ ≤ α * (lam * w u) := by
            gcongr
            · exact mul_nonneg hlam (hw u)
            · exact_mod_cast o.card_out_le u
    have h3 := X_le_out_in o hx u
    have h4 := hS u huS
    have : w u * c = w u / (1 + ε) - lam * w u - α * (lam * w u) := by
      rw [hcdef]; field_simp; ring
    linarith
  -- sum over `S` and exchange the order of summation
  have hsum : ∑ u ∈ S, ∑ v ∈ inNbr o u, x v ≤ α * ∑ v ∈ dom G S, x v := by
    calc ∑ u ∈ S, ∑ v ∈ inNbr o u, x v
        = ∑ u ∈ S, ∑ v ∈ dom G S, if u ∈ o.out v then x v else 0 := by
          refine sum_congr rfl fun u huS => ?_
          rw [← sum_filter]
          refine sum_congr ?_ fun _ _ => rfl
          ext v
          simp only [inNbr, mem_filter, mem_neighborFinset]
          constructor
          · rintro ⟨h, h'⟩
            exact ⟨mem_dom.2 ⟨u, huS, mem_cnbr.2 (Or.inr h.symm)⟩, h'⟩
          · rintro ⟨-, h'⟩; exact ⟨(o.adj_of_mem h').symm, h'⟩
      _ = ∑ v ∈ dom G S, ∑ u ∈ S, if u ∈ o.out v then x v else 0 := sum_comm
      _ = ∑ v ∈ dom G S, (S.filter fun u => u ∈ o.out v).card * x v := by
          refine sum_congr rfl fun v _ => ?_
          rw [← sum_filter]; simp
      _ ≤ ∑ v ∈ dom G S, α * x v := by
          refine sum_le_sum fun v _ => ?_
          gcongr
          · exact hx v
          · exact_mod_cast (card_le_card fun u hu => (mem_filter.1 hu).2).trans
              (o.card_out_le v)
      _ = α * ∑ v ∈ dom G S, x v := by rw [mul_sum]
  calc wt w S = ∑ u ∈ S, w u := rfl
    _ ≤ ∑ u ∈ S, c⁻¹ * ∑ v ∈ inNbr o u, x v := by
        refine sum_le_sum fun u huS => ?_
        rw [le_inv_mul_iff₀ hc, mul_comm]; exact hu u huS
    _ = c⁻¹ * ∑ u ∈ S, ∑ v ∈ inNbr o u, x v := by rw [mul_sum]
    _ ≤ c⁻¹ * (α * ∑ v ∈ dom G S, x v) := by gcongr
    _ = _ := by ring

/-! ### The procedure -/

/-- State of the partial dominating set procedure: packing values and the partial set `S`. -/
structure PState (V : Type*) where
  /-- packing values -/
  x : V → ℝ
  /-- the partial dominating set -/
  S : Finset V

variable (G)

/-- One iteration (Lemma 4.1, steps 1–3). -/
noncomputable def iter (ε : ℝ) (w : V → ℝ) (p : PState V) : PState V :=
  let S' := p.S ∪ univ.filter fun u => w u / (1 + ε) ≤ X G p.x u
  ⟨fun v => if v ∈ dom G S' then p.x v else p.x v * (1 + ε), S'⟩

/-- Initial state: `x_v = τ_v / (Δ + 1)`, `S = ∅`. -/
noncomputable def init (w : V → ℝ) : PState V :=
  ⟨fun v => tau G w v / (G.maxDegree + 1), ∅⟩

/-- State after `k` iterations. -/
noncomputable def runP (ε : ℝ) (w : V → ℝ) (k : ℕ) : PState V := (iter G ε w)^[k] (init G w)

/-- The number of iterations `r`: the least `r` with `λ < (1+ε)^r / (Δ+1)` (the paper takes
`S = ∅`, i.e. `r = 0`, when `λ < 1/(Δ+1)`, and otherwise `r ≥ 1` with
`(1+ε)^{r-1}/(Δ+1) ≤ λ < (1+ε)^r/(Δ+1)`). -/
noncomputable def numIter (ε lam : ℝ) : ℕ :=
  sInf {r : ℕ | lam < (1 + ε) ^ r / (G.maxDegree + 1)}

/-- The partial dominating set and packing of Lemma 4.1. -/
noncomputable def partialDS (ε lam : ℝ) (w : V → ℝ) : PState V := runP G ε w (numIter G ε lam)

variable {G}

theorem runP_succ (ε : ℝ) (w : V → ℝ) (k : ℕ) :
    runP G ε w (k + 1) = iter G ε w (runP G ε w k) :=
  Function.iterate_succ_apply' _ _ _

theorem maxDeg_pos : (0 : ℝ) < G.maxDegree + 1 := by positivity

theorem exists_pow_gt {ε lam : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, lam < (1 + ε) ^ r / (G.maxDegree + 1) := by
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (lam * (G.maxDegree + 1)) (by linarith : 1 < 1 + ε)
  exact ⟨r, by rw [lt_div_iff₀ maxDeg_pos]; exact hr⟩

theorem lt_pow_numIter {ε lam : ℝ} (hε : 0 < ε) :
    lam < (1 + ε) ^ numIter G ε lam / (G.maxDegree + 1) :=
  Nat.sInf_mem (exists_pow_gt hε)

theorem pow_pred_numIter_le {ε lam : ℝ} (_hε : 0 < ε) (h : 1 ≤ numIter G ε lam) :
    (1 + ε) ^ (numIter G ε lam - 1) / (G.maxDegree + 1) ≤ lam := by
  have := Nat.notMem_of_lt_sInf (s := {r : ℕ | lam < (1 + ε) ^ r / (G.maxDegree + 1)})
    (m := numIter G ε lam - 1) (by unfold numIter at *; omega)
  simpa using this

/-- Invariants of the procedure after `k` iterations. -/
structure Inv (ε : ℝ) (w : V → ℝ) (k : ℕ) (p : PState V) : Prop where
  undom : ∀ v ∉ dom G p.S, p.x v = tau G w v * (1 + ε) ^ k / (G.maxDegree + 1)
  domd : ∀ v ∈ dom G p.S, ∃ j < k, p.x v = tau G w v * (1 + ε) ^ j / (G.maxDegree + 1)
  inS : ∀ u ∈ p.S, w u / (1 + ε) ≤ X G p.x u
  nonneg : ∀ v, 0 ≤ p.x v
  feas : ∀ u, X G p.x u ≤ w u

theorem dom_mono {S T : Finset V} (h : S ⊆ T) : dom G S ⊆ dom G T := fun v hv => by
  obtain ⟨u, hu, h'⟩ := mem_dom.1 hv; exact mem_dom.2 ⟨u, h hu, h'⟩

theorem inv_init {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (ε : ℝ) : Inv (G := G) ε w 0 (init G w) := by
  have hτ : ∀ v, 0 ≤ tau G w v := fun v => le_inf' _ _ fun u _ => hw u
  refine ⟨fun v _ => by simp [init], fun v hv => by simp [init, dom] at hv, by simp [init],
    fun v => div_nonneg (hτ v) maxDeg_pos.le, fun u => ?_⟩
  calc X G (init G w).x u = ∑ v ∈ cnbr G u, tau G w v / (G.maxDegree + 1) := rfl
    _ ≤ ∑ _v ∈ cnbr G u, w u / (G.maxDegree + 1) := by
        gcongr with v hv
        exact tau_le (mem_cnbr_comm.1 hv)
    _ = (cnbr G u).card * w u / (G.maxDegree + 1) := by simp; ring
    _ ≤ (G.maxDegree + 1) * w u / (G.maxDegree + 1) := by
        gcongr
        · exact hw u
        · exact_mod_cast card_cnbr_le u
    _ = w u := by field_simp

theorem inv_iter {ε : ℝ} (hε : 0 < ε) {w : V → ℝ} {k : ℕ} {p : PState V}
    (h : Inv (G := G) ε w k p) : Inv (G := G) ε w (k + 1) (iter G ε w p) := by
  set J := p.S ∪ univ.filter fun u => w u / (1 + ε) ≤ X G p.x u with hJ
  have hS : (iter G ε w p).S = J := rfl
  have hx : ∀ v, (iter G ε w p).x v = if v ∈ dom G J then p.x v else p.x v * (1 + ε) :=
    fun v => rfl
  -- frozen around members of `J`
  have hfrozen : ∀ u ∈ J, X G (iter G ε w p).x u = X G p.x u := by
    intro u hu
    refine sum_congr rfl fun v hv => ?_
    rw [hx, ite_eq_left (mem_dom.2 ⟨u, hu, mem_cnbr_comm.1 hv⟩)]
  have hJmem : ∀ u ∈ J, w u / (1 + ε) ≤ X G p.x u := by
    intro u hu
    rcases mem_union.1 hu with hu | hu
    · exact h.inS u hu
    · exact (mem_filter.1 hu).2
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun u hu => ?_, fun v => ?_, fun u => ?_⟩
  · rw [hS] at hv
    rw [hx, ite_eq_right hv, h.undom v fun h' => hv (dom_mono subset_union_left h'), pow_succ]
    ring
  · rw [hS] at hv
    rw [hx, ite_eq_left hv]
    by_cases hv' : v ∈ dom G p.S
    · obtain ⟨j, hj, e⟩ := h.domd v hv'
      exact ⟨j, by omega, e⟩
    · exact ⟨k, by omega, h.undom v hv'⟩
  · rw [hS] at hu; rw [hfrozen u hu]; exact hJmem u hu
  · rw [hx]; split_ifs
    · exact h.nonneg v
    · exact mul_nonneg (h.nonneg v) (by linarith)
  · by_cases hu : u ∈ J
    · rw [hfrozen u hu]; exact h.feas u
    · have hlt : X G p.x u < w u / (1 + ε) := by
        by_contra hc
        exact hu (mem_union_right _ (mem_filter.2 ⟨mem_univ _, not_lt.1 hc⟩))
      calc X G (iter G ε w p).x u ≤ ∑ v ∈ cnbr G u, p.x v * (1 + ε) := by
            refine sum_le_sum fun v _ => ?_
            rw [hx]; split_ifs
            · nlinarith [h.nonneg v]
            · exact le_rfl
        _ = X G p.x u * (1 + ε) := by rw [X, sum_mul]
        _ ≤ w u / (1 + ε) * (1 + ε) := by gcongr
        _ = w u := by field_simp

theorem inv_runP {ε : ℝ} (hε : 0 < ε) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (k : ℕ) :
    Inv (G := G) ε w k (runP G ε w k) := by
  induction k with
  | zero => exact inv_init hw ε
  | succ k ih => rw [runP_succ]; exact inv_iter hε ih

/-- **Lemma 4.1** (Dory–Ghaffari–Ilchi). For `0 < ε` and `0 ≤ λ < 1/((α+1)(1+ε))` and an
orientation with out-degree `≤ α`, the procedure outputs a feasible packing `x` and a set `S` with
(a) `w_S ≤ α (1/(1+ε) - λ(α+1))⁻¹ ∑_{v ∈ N⁺_S} x_v`, and
(b) `x_v ≥ λ τ_v` for every vertex `v ∉ N⁺_S`.
(The orientation is only used in the analysis; the procedure does not depend on it.) -/
theorem lemma_4_1 {α : ℕ} (o : G.OutOrientation α) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 ≤ lam) (hlam' : lam < 1 / ((α + 1) * (1 + ε))) :
    IsPacking G w (partialDS G ε lam w).x ∧
    wt w (partialDS G ε lam w).S ≤
      α * (1 / (1 + ε) - lam * (α + 1))⁻¹ * ∑ v ∈ dom G (partialDS G ε lam w).S,
        (partialDS G ε lam w).x v ∧
    ∀ v ∉ dom G (partialDS G ε lam w).S, lam * tau G w v ≤ (partialDS G ε lam w).x v := by
  have hI := inv_runP (G := G) hε hw (numIter G ε lam)
  have hτ : ∀ v, 0 ≤ tau G w v := fun v => le_inf' _ _ fun u _ => hw u
  have hc : 0 < 1 / (1 + ε) - lam * (α + 1) := by
    rw [lt_div_iff₀ (by positivity)] at hlam'
    rw [sub_pos, lt_div_iff₀ (by linarith)]; linarith
  refine ⟨⟨hI.nonneg, hI.feas⟩, charging o hw hI.nonneg hε hlam hc hI.inS fun v hv => ?_,
    fun v hv => ?_⟩
  · obtain ⟨j, hj, e⟩ := hI.domd v hv
    rw [e]
    have h1 := pow_pred_numIter_le (G := G) (lam := lam) hε (by omega)
    calc tau G w v * (1 + ε) ^ j / (G.maxDegree + 1)
        ≤ tau G w v * ((1 + ε) ^ (numIter G ε lam - 1) / (G.maxDegree + 1)) := by
          rw [mul_div_assoc]
          gcongr
          · exact hτ v
          · linarith
          · omega
      _ ≤ tau G w v * lam := by gcongr; exact hτ v
      _ = lam * tau G w v := mul_comm _ _
  · simp only [partialDS] at hv ⊢
    rw [hI.undom v hv, mul_div_assoc, mul_comm (tau G w v)]
    exact mul_le_mul_of_nonneg_right (lt_pow_numIter hε).le (hτ v)

/-- Number of iterations: `r ≤ 1 + 2 log(max 1 (λ(Δ+1))) / ε` for `0 < ε ≤ 1`, i.e.
`r = O(log(Δλ)/ε)` (each iteration takes `O(1)` rounds, see `Distributed.lean`). -/
theorem numIter_le {ε lam : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (numIter G ε lam : ℝ) ≤ 1 + 2 * Real.log (max 1 (lam * (G.maxDegree + 1))) / ε := by
  set r := numIter G ε lam
  have hL : 0 ≤ Real.log (max 1 (lam * (G.maxDegree + 1))) := Real.log_nonneg (le_max_left _ _)
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · rw [h0]; push_cast; have : 0 ≤ 2 * Real.log (max 1 (lam * (G.maxDegree + 1))) / ε := by
      positivity
    linarith
  have h1 := pow_pred_numIter_le (G := G) (lam := lam) hε hpos
  rw [div_le_iff₀ maxDeg_pos] at h1
  have h2 : ((r - 1 : ℕ) : ℝ) * Real.log (1 + ε) ≤ Real.log (max 1 (lam * (G.maxDegree + 1))) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (h1.trans (le_max_right _ _))
  have h3 : ε / 2 ≤ Real.log (1 + ε) := by
    have := Real.add_one_le_exp (-(ε / 2))
    have h4 : 1 + ε ≥ Real.exp (ε / 2) := by
      -- `exp(ε/2) ≤ 1 + ε` for `0 ≤ ε ≤ 1`
      have := Real.exp_bound' (x := ε / 2) (by linarith) (by linarith) (n := 2) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      nlinarith
    rw [ge_iff_le, ← Real.le_log_iff_exp_le (by linarith)] at h4
    exact h4
  have h5 : ((r - 1 : ℕ) : ℝ) * (ε / 2) ≤ Real.log (max 1 (lam * (G.maxDegree + 1))) :=
    le_trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)) h2
  have h6 : ((r - 1 : ℕ) : ℝ) ≤ 2 * Real.log (max 1 (lam * (G.maxDegree + 1))) / ε := by
    rw [le_div_iff₀ hε]; linarith
  have : (r : ℝ) = ((r - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hpos]; push_cast; ring
  linarith

end DominatingSetArboricity
