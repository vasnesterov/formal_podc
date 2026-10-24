import Papers.PODC2017.MaxISLocalRatio.SeqLR

/-!
# Weight layers: the removal stage of Algorithm 2 (Section 2.2, Lemma A.1, deterministic part)

Algorithm 2 splits the vertices into layers `Lᵢ = {v | 2^{i-1} < w(v) ≤ 2^i}` and, in each phase,
computes a maximal independent set of the top layer (nodes wait while they have a neighbour in a
higher layer). The randomized MIS black box is out of scope; we formalize the deterministic part
of Lemma A.1 and Theorem 2.3: if, in every phase, the chosen set `U` contains a maximal independent
set of the top layer, then the top layer is emptied, and with integer weights in `[1, W]` the
removal stage ends after `⌈log₂ W⌉ + 1` phases.

`IsTopMIS R`: whenever all remaining weights are at most `2^m`, every vertex with weight in
`(2^{m-1}, 2^m]` is in `U` or has a neighbour in `U` with weight in that range (if `m` is the top
layer, this says that `U ∩ L_top` is a maximal independent set of `G[L_top]`; for larger `m` it is
vacuous).

* `top_layer_drops` — Lemma A.1 (deterministic): one phase halves the weight bound.
* `removal_stage` — after `⌈log₂ W⌉ + 1` phases no vertex remains.
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The choice rule picks (a superset of) a maximal independent set of the top weight layer. -/
def Rule.IsTopMIS (R : Rule G) : Prop :=
  ∀ (w : V → ℝ) (m : ℤ), (∀ v, 0 < w v → w v ≤ 2 ^ m) →
    ∀ v, 2 ^ (m - 1) < w v → v ∈ R.pick w ∨ ∃ u ∈ R.pick w, G.Adj v u ∧ 2 ^ (m - 1) < w u

/-- **Lemma A.1 (deterministic part).** If all remaining weights are at most `2^m`, then after one
phase all remaining weights are at most `2^{m-1}`: the top layer `L_m` is emptied. -/
theorem top_layer_drops {R : Rule G} (hR : R.IsTopMIS) {w : V → ℝ} {m : ℤ}
    (hw : ∀ v, 0 < w v → w v ≤ 2 ^ m) : ∀ v, 0 < R.next w v → R.next w v ≤ 2 ^ (m - 1) := by
  intro v hv
  have hle := R.next_le w v
  by_contra hgt
  push Not at hgt
  have hv' : 2 ^ (m - 1) < w v := hgt.trans_le hle
  rcases hR w m hw v hv' with hU | ⟨u, hu, hadj, hwu⟩
  · rw [R.next_pick w hU] at hv; exact lt_irrefl _ hv
  · -- `v` loses at least `w(u) > 2^{m-1}`
    have hred : w u ≤ red G (R.pick w) w v := by
      unfold red
      exact single_le_sum (f := w) (fun u' hu' => R.pick_nonneg w u' (mem_filter.1 hu').1)
        (mem_filter.2 ⟨hu, mem_cl.2 (Or.inr hadj.symm)⟩)
    have hwv : w v ≤ 2 ^ m := hw v (hv.trans_le hle)
    have h2 : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring_nf
    have : R.next w v = w v - red G (R.pick w) w v := rfl
    linarith

/-- Integer weights stay integers. -/
theorem next_int {R : Rule G} {w : V → ℝ} (hw : ∀ v, ∃ n : ℤ, w v = n) :
    ∀ v, ∃ n : ℤ, R.next w v = n := by
  classical
  choose f hf using hw
  intro v
  refine ⟨f v - ∑ u ∈ (R.pick w).filter (fun u => v ∈ cl G u), f u, ?_⟩
  simp [Rule.next, red, hf]

/-- **Removal stage of Algorithm 2 (Theorem 2.3, deterministic part).** With integer weights at
most `W` and a rule that picks a maximal independent set of the top layer in each phase, no
vertex remains after `⌈log₂ W⌉ + 1` phases. -/
theorem removal_stage {R : Rule G} (hR : R.IsTopMIS) {w : V → ℝ} (hint : ∀ v, ∃ n : ℤ, w v = n)
    {W : ℕ} (hW : ∀ v, w v ≤ W) : pos (R.iter w (Nat.clog 2 W + 1)) = ∅ := by
  set L := Nat.clog 2 W
  -- after `i` phases all remaining weights are at most `2^(L - i)` and integral
  have key : ∀ i, (∀ v, 0 < R.iter w i v → R.iter w i v ≤ 2 ^ ((L : ℤ) - i)) ∧
      ∀ v, ∃ n : ℤ, R.iter w i v = n := by
    intro i
    induction i with
    | zero =>
      refine ⟨fun v _ => ?_, hint⟩
      simp only [Rule.iter_zero, CharP.cast_eq_zero, sub_zero, zpow_natCast]
      exact (hW v).trans (by exact_mod_cast Nat.le_pow_clog (by norm_num) W)
    | succ i ih =>
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [Rule.iter_succ] at hv ⊢
        have := top_layer_drops hR ih.1 v hv
        rwa [show (L : ℤ) - i - 1 = L - (i + 1 : ℕ) by push_cast; ring] at this
      · rw [Rule.iter_succ]; exact next_int ih.2
  refine eq_empty_of_forall_notMem fun v hv => ?_
  have hpos := mem_pos.1 hv
  obtain ⟨n, hn⟩ := (key (L + 1)).2 v
  have hle := (key (L + 1)).1 v hpos
  rw [show ((L : ℤ) - (L + 1 : ℕ)) = -1 by push_cast; ring, hn] at hle
  rw [hn] at hpos
  have h1 : (0 : ℤ) < n := by exact_mod_cast hpos
  have h2 : (n : ℝ) ≤ 1 / 2 := by simpa using hle
  have h3 : (1 : ℝ) ≤ n := by exact_mod_cast h1
  linarith

/-! ### Non-vacuity: a rule picking a maximal independent set of the top layer -/

variable (G)

/-- The layer index `⌈log₂ w(v)⌉` (`v ∈ L_i` iff `2^{i-1} < w(v) ≤ 2^i`). -/
noncomputable def layer (w : V → ℝ) (v : V) : ℤ := Int.clog 2 (w v)

theorem lt_iff_le_layer {w : V → ℝ} {v : V} (hv : 0 < w v) (m : ℤ) :
    (2 : ℝ) ^ (m - 1) < w v ↔ m ≤ layer w v := by
  have := Int.zpow_lt_iff_lt_clog (b := 2) (by norm_num) (x := m - 1) hv
  simp only [Nat.cast_ofNat] at this
  rw [this, layer]; omega

theorem le_iff_layer_le {w : V → ℝ} {v : V} (hv : 0 < w v) (m : ℤ) :
    w v ≤ (2 : ℝ) ^ m ↔ layer w v ≤ m := by
  have := Int.le_zpow_iff_clog_le (b := 2) (by norm_num) (x := m) hv
  simp only [Nat.cast_ofNat] at this
  rw [this, layer]

/-- The top layer `L_top` of the remaining vertices. -/
noncomputable def topLayer (w : V → ℝ) : Finset V :=
  (pos w).filter fun v => ∀ u ∈ pos w, layer w u ≤ layer w v

-- CSLib candidate
open scoped Classical in
theorem exists_mis (S : Finset V) : ∃ M : Finset V, (M ⊆ S ∧ G.IsIndepSet (M : Set V)) ∧
    ∀ T ⊆ S, G.IsIndepSet (T : Set V) → #T ≤ #M := by
  obtain ⟨M, hM, hmax⟩ := exists_max_image
    (S.powerset.filter fun T : Finset V => G.IsIndepSet (T : Set V)) card ⟨∅, by simp⟩
  simp only [mem_filter, mem_powerset] at hM hmax
  exact ⟨M, hM, fun T hT hind => hmax T ⟨hT, hind⟩⟩

/-- A maximal independent subset of `S` (one of maximum cardinality). -/
noncomputable def mis (S : Finset V) : Finset V := Classical.choose (exists_mis G S)

theorem mis_spec (S : Finset V) :
    (mis G S ⊆ S ∧ G.IsIndepSet (mis G S : Set V)) ∧
      ∀ T ⊆ S, G.IsIndepSet (T : Set V) → #T ≤ #(mis G S) :=
  Classical.choose_spec (exists_mis G S)

/-- Maximality: every vertex of `S` is in `mis S` or has a neighbour in it. -/
theorem mis_maximal (S : Finset V) {v : V} (hv : v ∈ S) :
    v ∈ mis G S ∨ ∃ u ∈ mis G S, G.Adj v u := by
  by_contra h
  push Not at h
  obtain ⟨⟨hsub, hind⟩, hmax⟩ := mis_spec G S
  have hind' : G.IsIndepSet ((insert v (mis G S) : Finset V) : Set V) := by
    intro a ha b hb hab hadj
    simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hab rfl
    · exact h.2 b hb hadj
    · exact h.2 a ha hadj.symm
    · exact hind ha hb hab hadj
  have := hmax _ (insert_subset hv hsub) hind'
  rw [card_insert_of_notMem h.1] at this
  omega

/-- Algorithm 2's choice as a rule: a maximal independent set of the top layer. -/
noncomputable def topMISRule : Rule G where
  pick w := mis G (topLayer w)
  pick_subset w := (mis_spec G _).1.1.trans (filter_subset _ _)
  pick_indep w := (mis_spec G _).1.2
  pick_nonempty w h := by
    obtain ⟨v, hv, hmax⟩ := exists_max_image (pos w) (layer w) h
    have hvT : v ∈ topLayer w := mem_filter.2 ⟨hv, hmax⟩
    rcases mis_maximal G _ hvT with h' | ⟨u, hu, _⟩
    · exact ⟨v, h'⟩
    · exact ⟨u, hu⟩

/-- `topMISRule` satisfies `IsTopMIS` (so `removal_stage` is not vacuous). -/
theorem topMISRule_isTopMIS : (topMISRule G).IsTopMIS := by
  intro w m hw v hv
  have hv0 : 0 < w v := lt_trans (zpow_pos (by norm_num) _) hv
  have hlv : m ≤ layer w v := (lt_iff_le_layer hv0 m).1 hv
  have hvT : v ∈ topLayer w := by
    refine mem_filter.2 ⟨mem_pos.2 hv0, fun u hu => ?_⟩
    have := (le_iff_layer_le (mem_pos.1 hu) m).1 (hw u (mem_pos.1 hu))
    omega
  rcases mis_maximal G _ hvT with h' | ⟨u, hu, hadj⟩
  · exact Or.inl h'
  · refine Or.inr ⟨u, hu, hadj, ?_⟩
    have huT := (mis_spec G _).1.1 hu
    obtain ⟨hupos, humax⟩ := mem_filter.1 huT
    have := humax v (mem_pos.2 hv0)
    exact (lt_iff_le_layer (mem_pos.1 hupos) m).2 (by omega)

end Podc.MaxISLocalRatio
