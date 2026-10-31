import Papers.PODC2021.WakeUpMatching.Radio
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Lemma 5.2: the probability that a given edge joins the matching in one round

Dani, Gupta, Hayes, Pettie, PODC 2021 (arXiv:2104.09096v2), Lemma 5.2.

Conditioned on the matching `M(t−1)` (here: fixed partner variables `partner`), every node
independently recruits with probability `r/2`, accepts with probability `r/2` and sleeps with
probability `1 − r` (`roleLaw r`); the probability of an event of the role vector is
`prob r E = ∑_{ρ ∈ E} ∏_u roleLaw r (ρ u)`. (The roles drawn by matched nodes are ignored by the
protocol.) Lemma 5.2: for unmatched neighbours `v, w` whose residual degrees are at most `Δ`
(in the paper `Δ = Δ(t−1)`, the maximum residual degree),

`P(v and w get matched to each other in this round) ≥ r²/2 · (1 − r)^(Δ − 1)`.

The proof is the paper's: the event contains the two disjoint "isolated handshake" events
(`v` recruits, `w` accepts, the common unmatched neighbours sleep, the other unmatched
neighbours of `v` do not accept and those of `w` do not recruit, and symmetrically), whose
probability is `(r/2)² (1−r)^A (1−r/2)^B` with `2A + B = d(v) + d(w) − 2`.
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset Fintype

/-- The law of the role of a node in round `t`, with `r = r(t)`. -/
noncomputable def roleLaw (r : ℝ) : Role → ℝ
  | .recruit => r / 2
  | .accept => r / 2
  | .sleep => 1 - r

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Probability of an event of the role vector, roles independent with law `roleLaw r`. -/
noncomputable def prob (r : ℝ) (E : (V → Role) → Prop) [DecidablePred E] : ℝ :=
  ∑ ρ ∈ univ.filter E, ∏ u, roleLaw r (ρ u)

variable (partner : V → Option V)

/-- Unmatched neighbours (the residual neighbourhood `N(z, t−1)`). -/
def resN (z : V) : Finset V := {u | G.Adj z u ∧ partner u = none}

/-- The roles allowed for `u` in the isolated handshake event with recruiter `x` and acceptor
`y`. -/
def isoSet (x y u : V) : Finset Role :=
  if u = x then {.recruit}
  else if u = y then {.accept}
  else if u ∈ resN G partner x ∧ u ∈ resN G partner y then {.sleep}
  else if u ∈ resN G partner x then {.recruit, .sleep}
  else if u ∈ resN G partner y then {.accept, .sleep}
  else univ

variable {G partner}

theorem round_of_mem_piFinset {x y : V} (hxy : G.Adj x y) (hx : partner x = none)
    (hy : partner y = none) {ρ : V → Role} (hρ : ρ ∈ piFinset (isoSet G partner x y)) :
    round G partner ρ x = some y ∧ round G partner ρ y = some x := by
  rw [mem_piFinset] at hρ
  have hxy' : x ≠ y := hxy.ne
  have hρx : ρ x = .recruit := by simpa [isoSet] using hρ x
  have hρy : ρ y = .accept := by simpa [isoSet, hxy'.symm] using hρ y
  refine round_matches_of_isolated hxy ⟨hx, hρx⟩ ⟨hy, hρy⟩ (fun u hu hux hrec => ?_)
    (fun u hu huy hacc => ?_)
  · have huy : u ≠ y := (hu.ne).symm
    have hmem : u ∈ resN G partner y := by simp [resN, hu, hrec.1]
    have := hρ u
    by_cases hux' : u ∈ resN G partner x
    · simp [isoSet, hux, huy, hux', hmem, hrec.2] at this
    · simp [isoSet, hux, huy, hux', hmem, hrec.2] at this
  · have hux : u ≠ x := (hu.ne).symm
    have hmem : u ∈ resN G partner x := by simp [resN, hu, hacc.1]
    have := hρ u
    by_cases huy' : u ∈ resN G partner y
    · simp [isoSet, hux, huy, huy', hmem, hacc.2] at this
    · simp [isoSet, hux, huy, huy', hmem, hacc.2] at this

theorem prod_ite_mem_const (s : Finset V) (c : ℝ) :
    ∏ u, (if u ∈ s then c else 1) = c ^ #s := by
  rw [Finset.prod_ite, prod_const, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter]

/-- The probability of the isolated handshake event. -/
theorem prod_sum_isoSet {x y : V} (hxy : G.Adj x y) (r : ℝ) :
    ∏ u, ∑ a ∈ isoSet G partner x y u, roleLaw r a =
      (r / 2) ^ 2 * (1 - r) ^ #(resN G partner x ∩ resN G partner y) *
        (1 - r / 2) ^ (#((resN G partner x \ resN G partner y).erase y) +
          #((resN G partner y \ resN G partner x).erase x)) := by
  set Nx := resN G partner x
  set Ny := resN G partner y
  have hxNx : x ∉ Nx := by simp [Nx, resN]
  have hyNy : y ∉ Ny := by simp [Ny, resN]
  have hxy' : x ≠ y := hxy.ne
  have hdisj : Disjoint ((Nx \ Ny).erase y) ((Ny \ Nx).erase x) := by
    rw [disjoint_left]; intro u h1 h2; simp at h1 h2; tauto
  rw [← card_union_of_disjoint hdisj, ← prod_ite_mem_const, ← prod_ite_mem_const,
    show (r / 2) ^ 2 = (r / 2) ^ #({x, y} : Finset V) by rw [card_pair hxy'],
    ← prod_ite_mem_const, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun u _ => ?_
  have sumU : ∑ a : Role, roleLaw r a = 1 := by
    simp [Finset.univ, Fintype.elems, roleLaw]; ring
  by_cases hux : u = x
  · subst hux; simp [isoSet, roleLaw, hxNx, hxy']
  by_cases huy : u = y
  · subst huy; simp [isoSet, roleLaw, hyNy, hux]
  by_cases h1 : u ∈ Nx <;> by_cases h2 : u ∈ Ny
  · simp [isoSet, roleLaw, hux, huy, h1, h2, Nx, Ny]
  · simp [isoSet, roleLaw, hux, huy, h1, h2, Nx, Ny]; ring
  · simp [isoSet, roleLaw, hux, huy, h1, h2, Nx, Ny]; ring
  · simp [isoSet, hux, huy, h1, h2, Nx, Ny, sumU]

/-- **Lemma 5.2.** Let `v, w` be unmatched neighbours whose residual degrees are at most `Δ`,
and `0 ≤ r ≤ 1`. Then the probability (over the independent role choices of one round) that
`v` and `w` get matched to each other is at least `r²/2 · (1 − r)^(Δ − 1)`. -/
theorem lemma_5_2 {v w : V} (hvw : G.Adj v w) (hv : partner v = none) (hw : partner w = none)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {Δ : ℕ} (hΔv : #(resN G partner v) ≤ Δ)
    (hΔw : #(resN G partner w) ≤ Δ) :
    r ^ 2 / 2 * (1 - r) ^ (Δ - 1) ≤ prob r fun ρ => round G partner ρ v = some w := by
  set Nv := resN G partner v
  set Nw := resN G partner w
  have hq : ∀ a, 0 ≤ roleLaw r a := by
    intro a; cases a <;> simp [roleLaw] <;> linarith
  have hS1 : piFinset (isoSet G partner v w) ⊆ univ.filter fun ρ => round G partner ρ v = some w :=
    fun ρ hρ => mem_filter.2 ⟨mem_univ _, (round_of_mem_piFinset hvw hv hw hρ).1⟩
  have hS2 : piFinset (isoSet G partner w v) ⊆ univ.filter fun ρ => round G partner ρ v = some w :=
    fun ρ hρ => mem_filter.2 ⟨mem_univ _, (round_of_mem_piFinset hvw.symm hw hv hρ).2⟩
  have hdisj : Disjoint (piFinset (isoSet G partner v w)) (piFinset (isoSet G partner w v)) := by
    rw [disjoint_left]
    intro ρ h1 h2
    rw [mem_piFinset] at h1 h2
    have a := h1 v; have b := h2 v
    simp [isoSet, hvw.ne] at a b
    rw [a] at b; cases b
  have hP : (r / 2) ^ 2 * (1 - r) ^ #(Nv ∩ Nw) *
        (1 - r / 2) ^ (#((Nv \ Nw).erase w) + #((Nw \ Nv).erase v)) * 2 ≤
      prob r fun ρ => round G partner ρ v = some w := by
    unfold prob
    calc _ = ∑ ρ ∈ piFinset (isoSet G partner v w), ∏ u, roleLaw r (ρ u) +
          ∑ ρ ∈ piFinset (isoSet G partner w v), ∏ u, roleLaw r (ρ u) := by
          rw [← prod_univ_sum (κ := fun _ => Role) _ (fun _ a => roleLaw r a),
            ← prod_univ_sum (κ := fun _ => Role) _ (fun _ a => roleLaw r a),
            prod_sum_isoSet hvw, prod_sum_isoSet hvw.symm, inter_comm, add_comm (#_)]
          ring
      _ = ∑ ρ ∈ piFinset (isoSet G partner v w) ∪ piFinset (isoSet G partner w v),
            ∏ u, roleLaw r (ρ u) := (sum_union hdisj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (union_subset hS1 hS2)
            (fun ρ _ _ => prod_nonneg fun u _ => hq _)
  -- cardinalities: `d(v) = 1 + A + B_v`, `d(w) = 1 + A + B_w`
  have hwNv : w ∈ Nv \ Nw := by simp [Nv, Nw, resN, hvw, hw]
  have hvNw : v ∈ Nw \ Nv := by simp [Nv, Nw, resN, hvw.symm, hv]
  have cv : #Nv = #(Nv ∩ Nw) + (#((Nv \ Nw).erase w) + 1) := by
    rw [card_erase_add_one hwNv, card_inter_add_card_sdiff]
  have cw : #Nw = #(Nv ∩ Nw) + (#((Nw \ Nv).erase v) + 1) := by
    rw [card_erase_add_one hvNw, inter_comm, card_inter_add_card_sdiff]
  set A := #(Nv ∩ Nw)
  set B := #((Nv \ Nw).erase w) + #((Nw \ Nv).erase v)
  have hAB : 2 * A + B ≤ 2 * (Δ - 1) := by omega
  -- `(1−r)^A (1−r/2)^B ≥ (1−r)^(Δ−1)`, by squaring
  have h1r : 0 ≤ 1 - r := by linarith
  have h1r2 : 0 ≤ 1 - r / 2 := by linarith
  have hsq : ((1 - r) ^ (Δ - 1)) ^ 2 ≤ ((1 - r) ^ A * (1 - r / 2) ^ B) ^ 2 := by
    calc ((1 - r) ^ (Δ - 1)) ^ 2 = (1 - r) ^ (2 * (Δ - 1)) := by ring
      _ ≤ (1 - r) ^ (2 * A + B) := pow_le_pow_of_le_one h1r (by linarith) hAB
      _ = ((1 - r) ^ A) ^ 2 * (1 - r) ^ B := by ring
      _ ≤ ((1 - r) ^ A) ^ 2 * ((1 - r / 2) ^ 2) ^ B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ h1r (by nlinarith) B
      _ = ((1 - r) ^ A * (1 - r / 2) ^ B) ^ 2 := by
          rw [mul_pow, ← pow_mul (1 - r / 2) 2 B, ← pow_mul (1 - r / 2) B 2, mul_comm 2 B]
  have hroot : (1 - r) ^ (Δ - 1) ≤ (1 - r) ^ A * (1 - r / 2) ^ B :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  calc r ^ 2 / 2 * (1 - r) ^ (Δ - 1) ≤ r ^ 2 / 2 * ((1 - r) ^ A * (1 - r / 2) ^ B) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (r / 2) ^ 2 * (1 - r) ^ A * (1 - r / 2) ^ B * 2 := by ring
    _ ≤ _ := hP

end Podc.WakeUpMatching
