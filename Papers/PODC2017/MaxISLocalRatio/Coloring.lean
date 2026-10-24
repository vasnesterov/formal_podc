import Papers.PODC2017.MaxISLocalRatio.SeqLR
import Cslib.Computability.Distributed.Local.LocallyIterative

/-!
# The colouring-based choice of `U` (Section 2.3, Algorithm 3, centralized view)

Given a proper colouring `c` with `k` colours (`c v < k`), Algorithm 3 lets a remaining vertex
reduce its weight from its neighbourhood when its colour is larger than the colours of all its
remaining neighbours (line 18). As a rule for Algorithm 1 this is `U = localMax c w`.

* `colorRule` — this choice is an admissible rule (independent, nonempty while vertices remain).
* `colorRule_pos_iter` — after `i` iterations every remaining vertex has colour `< k - i`;
  hence the removal stage ends after `k` iterations (`colorRule_removal`).
* `colorRule_isApprox` — the output is a `Δ`-approximation (from `algorithm_1`).

The distributed implementation is in `Distributed.lean`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio

open Finset Cslib.LocallyIterative

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (c : V → ℕ)

/-- The remaining vertices whose colour is a strict local maximum among the remaining vertices
(line 18 of Algorithm 3). -/
noncomputable def localMax (w : V → ℝ) : Finset V :=
  (pos w).filter fun v => ∀ u ∈ pos w, G.Adj v u → c u < c v

variable {G c}

theorem mem_localMax {w : V → ℝ} {v : V} :
    v ∈ localMax G c w ↔ 0 < w v ∧ ∀ u, 0 < w u → G.Adj v u → c u < c v := by
  simp [localMax]

/-- A remaining vertex of the largest remaining colour is a local maximum. -/
theorem mem_localMax_of_max (hc : IsProper G c) {w : V → ℝ} {v : V} (hv : 0 < w v)
    (hmax : ∀ u, 0 < w u → c u ≤ c v) : v ∈ localMax G c w :=
  mem_localMax.2 ⟨hv, fun u hu hadj => lt_of_le_of_ne (hmax u hu) (hc hadj.symm)⟩

variable (G c)

/-- **Algorithm 3's choice of `U`** (local colour maxima) is an admissible rule for
Algorithm 1. -/
noncomputable def colorRule (hc : IsProper G c) : Rule G where
  pick := localMax G c
  pick_subset _ := filter_subset _ _
  pick_indep w := by
    intro a ha b hb _ hadj
    have ha := mem_localMax.1 (mem_coe.1 ha)
    have hb := mem_localMax.1 (mem_coe.1 hb)
    exact lt_asymm (ha.2 b hb.1 hadj) (hb.2 a ha.1 hadj.symm)
  pick_nonempty w h := by
    obtain ⟨v, hv, hmax⟩ := exists_max_image (pos w) c h
    exact ⟨v, mem_localMax_of_max hc (mem_pos.1 hv) fun u hu => hmax u (mem_pos.2 hu)⟩

variable {G c}

/-- After `i` iterations of the colouring rule, every remaining vertex has colour `< k - i`. -/
theorem colorRule_pos_iter (hc : IsProper G c) {k : ℕ} (hk : ∀ v, c v < k) (w : V → ℝ)
    (i : ℕ) : ∀ v, 0 < (colorRule G c hc).iter w i v → c v + i < k := by
  induction i with
  | zero => exact fun v _ => hk v
  | succ i ih =>
    intro v hv
    set R := colorRule G c hc
    have hv' : v ∈ pos (R.iter w i) \ R.pick (R.iter w i) := by
      have := R.pos_next_subset (R.iter w i) (mem_pos.2 (by rwa [← Rule.iter_succ]))
      exact this
    obtain ⟨hvpos, hvU⟩ := mem_sdiff.1 hv'
    have h1 := ih v (mem_pos.1 hvpos)
    by_contra hcon
    -- `v` has the largest possible remaining colour, hence it is a local maximum
    refine hvU (mem_localMax_of_max hc (mem_pos.1 hvpos) fun u hu => ?_)
    have := ih u hu
    omega

/-- **Removal stage of Algorithm 3**: with `k` colours, no vertex remains after `k` iterations;
in particular every vertex is picked (becomes a candidate) or removed within `k` iterations. -/
theorem colorRule_removal (hc : IsProper G c) {k : ℕ} (hk : ∀ v, c v < k) (w : V → ℝ) :
    pos ((colorRule G c hc).iter w k) = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv => ?_
  have := colorRule_pos_iter hc hk w k v (mem_pos.1 hv)
  omega

/-- Picked levels are below `k`. -/
theorem colorRule_level_lt (hc : IsProper G c) {k : ℕ} (hk : ∀ v, c v < k) (w : V → ℝ)
    {i : ℕ} {v : V} (hv : v ∈ (colorRule G c hc).U w i) : i < k := by
  by_contra h
  rw [(colorRule G c hc).U_eq_empty_of_le w (colorRule_removal hc hk w) (not_lt.1 h)] at hv
  simp at hv

/-- **Correctness of Algorithm 3 (centralized form).** The colouring rule yields a
`Δ`-approximate maximum-weight independent set. -/
theorem colorRule_isApprox (hc : IsProper G c) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (h1 : 1 ≤ Δ)
    (w : V → ℝ) : IsApprox G Δ w (seqLR (colorRule G c hc) w) :=
  algorithm_1 _ hΔ h1 w

end Podc.MaxISLocalRatio
