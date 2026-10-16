import Papers.PODC2016.VertexCoverLocalRatio.Invariants

/-!
# Correctness of Algorithm 1 (Lemma 3.2)

* `actN_step`: the neighbourhood bookkeeping of the pseudocode — `N_{i+1}(v)` is `N_i(v)` without
  the neighbours that answered `v`'s request only partially (line 16) and those that returned
  `InCover` (line 30) — coincides with "running neighbours".
* `delta T`: the edge function `δ(e) = ∑_{i<T} (budget_i(u,v) + budget_i(v,u))`.
* `isValid_delta`: `δ` is `G`-valid, with `w(v) - ∑_{e ∋ v} δ(e) = w_T(v)`.
* `lemma_3_2`: once every vertex has returned, the `InCover` vertices form a vertex cover equal to
  `S_δ`, hence (Theorem 2.1) of weight at most `(2+ε)` times the weight of any vertex cover.
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {θ a σ : ℝ} {R : Rule V} {w0 : V → ℝ}

/-- A neighbour that keeps running answered `v`'s request in full. -/
theorem bud_eq_req_of_active (h : Hyp θ a σ R w0) {s : GState V} (hs : Inv G θ a w0 s) {v u : V}
    (hv : s.st v = .active) (hu : u ∈ actN G s v)
    (hu' : ¬ cov G θ a R w0 s u) : bud G a R w0 s u v = req G a w0 s v := by
  have hua := (mem_actN.1 hu).2
  have hvu := actN_symm hv hu
  refine le_antisymm (bud_le_req h hs hua hvu) (not_lt.1 fun hlt => hu' ⟨hua, ?_⟩)
  exact partial_cov h hs hua hvu hlt

open scoped Classical in
/-- The pseudocode's bookkeeping of `N_{i+1}(v)` (lines 9, 15–16, 29–31) gives exactly the
running neighbours. -/
theorem actN_step (h : Hyp θ a σ R w0) {s : GState V} (hs : Inv G θ a w0 s) {v : V}
    (hv : (step G θ a R w0 s).st v = .active) :
    actN G (step G θ a R w0 s) v =
      (actN G s v).filter fun u =>
        bud G a R w0 s u v = req G a w0 s v ∧ ¬ cov G θ a R w0 s u := by
  obtain ⟨hv0, hvn, -⟩ := step_active_iff.1 hv
  ext u
  simp only [mem_filter, mem_actN]
  constructor
  · rintro ⟨hadj, hu⟩
    obtain ⟨hu0, hun, -⟩ := step_active_iff.1 hu
    have hnc : ¬ cov G θ a R w0 s u := fun hc => hun hc.2
    exact ⟨⟨hadj, hu0⟩, bud_eq_req_of_active h hs hv0 (mem_actN.2 ⟨hadj, hu0⟩) hnc, hnc⟩
  · rintro ⟨⟨hadj, hu0⟩, -, hnc⟩
    refine ⟨hadj, step_active_iff.2 ⟨hu0, fun hle => hnc ⟨hu0, hle⟩, v, ?_, ?_⟩⟩
    · exact mem_actN.2 ⟨hadj.symm, hv0⟩
    · exact fun hc => hvn hc.2

/-! ### The edge function `δ` -/

section delta
variable (G θ a R w0)

/-- Amount exchanged over the pair `u, v` in iteration `i`. -/
noncomputable def flow (i : ℕ) (u v : V) : ℝ :=
  if (run G θ a R w0 i).st u = .active ∧ (run G θ a R w0 i).st v = .active ∧ G.Adj u v then
    bud G a R w0 (run G θ a R w0 i) u v + bud G a R w0 (run G θ a R w0 i) v u
  else 0

theorem flow_comm (i : ℕ) (u v : V) : flow G θ a R w0 i u v = flow G θ a R w0 i v u := by
  unfold flow
  by_cases hc : (run G θ a R w0 i).st u = .active ∧ (run G θ a R w0 i).st v = .active ∧ G.Adj u v
  · rw [if_pos hc, if_pos ⟨hc.2.1, hc.1, hc.2.2.symm⟩, add_comm]
  · rw [if_neg hc, if_neg fun hc' => hc ⟨hc'.2.1, hc'.1, hc'.2.2.symm⟩]

/-- `δ(e) = ∑_{i<T} (budget_i(u,v) + budget_i(v,u))` for `e = {u,v}`. -/
noncomputable def delta (T : ℕ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => ∑ i ∈ range T, flow G θ a R w0 i u v,
    fun u v => sum_congr rfl fun i _ => flow_comm G θ a R w0 i u v⟩

end delta

theorem sum_flow (h : Hyp θ a σ R w0) (i : ℕ) (v : V) :
    ∑ u ∈ G.neighborFinset v, flow G θ a R w0 i v u =
      (run G θ a R w0 i).w v - (run G θ a R w0 (i + 1)).w v := by
  set s := run G θ a R w0 i
  rw [run_succ]
  by_cases hv : s.st v = .active
  · rw [step_w, newW_active h (inv_run h i) hv]
    have : ∑ u ∈ G.neighborFinset v, flow G θ a R w0 i v u =
        ∑ u ∈ actN G s v, (bud G a R w0 s v u + bud G a R w0 s u v) := by
      rw [actN, sum_filter]
      refine sum_congr rfl fun u hu => ?_
      have hadj := (mem_neighborFinset G v u).1 hu
      unfold flow
      by_cases hu' : s.st u = .active
      · rw [if_pos ⟨hv, hu', hadj⟩, if_pos hu']
      · rw [if_neg fun hc => hu' hc.2.1, if_neg hu']
    rw [this, sum_add_distrib]
    unfold recv given
    ring
  · rw [step_w_of_ne hv, sub_self]
    exact sum_eq_zero fun u _ => by unfold flow; rw [if_neg fun hc => hv hc.1]

theorem tilde_delta (h : Hyp θ a σ R w0) (T : ℕ) (v : V) :
    tilde G (delta G θ a R w0 T) v = w0 v - (run G θ a R w0 T).w v := by
  unfold tilde delta
  simp only [Sym2.lift_mk]
  rw [sum_comm]
  simp_rw [sum_flow h]
  rw [sum_range_sub']
  rfl

theorem flow_nonneg (h : Hyp θ a σ R w0) (i : ℕ) (u v : V) : 0 ≤ flow G θ a R w0 i u v := by
  unfold flow
  split_ifs with hc
  · have hs : Inv G θ a w0 (run G θ a R w0 i) := inv_run h i
    have hv : v ∈ actN G (run G θ a R w0 i) u := mem_actN.2 ⟨hc.2.2, hc.2.1⟩
    exact add_nonneg (bud_nonneg h hs hc.1 hv) (bud_nonneg h hs hc.2.1 (actN_symm hc.1 hv))
  · exact le_rfl

/-- `δ` is `G`-valid (first part of the proof of Lemma 3.2). -/
theorem isValid_delta (h : Hyp θ a σ R w0) (T : ℕ) : IsValid G w0 (delta G θ a R w0 T) := by
  refine ⟨fun e _ => ?_, fun v => ?_⟩
  · induction e using Sym2.ind with
    | h u v =>
      simp only [delta, Sym2.lift_mk]
      exact sum_nonneg fun i _ => flow_nonneg h i u v
  · rw [tilde_delta h]
    have := (inv_run h T : Inv G θ a w0 (run G θ a R w0 T)).w_nonneg v
    linarith

/-- **Lemma 3.2** (correctness). Suppose every vertex has returned by the beginning of iteration
`T`. Then the set `C` of vertices that returned `InCover` is a vertex cover, it equals `S_δ` for the
`G`-valid function `δ = delta T`, and its weight is at most `(2+ε)` times the weight of any vertex
cover. Here `θ = ε' = ε/(2+ε)`; the response rule is any rule meeting the specification (for the
paper's algorithm: `a = θ`, `σ = 0`, greedy in an arbitrary order). -/
theorem lemma_3_2 {ε : ℝ} (hε : 0 < ε) (hθ : θ = epsP ε) (h : Hyp θ a σ R w0) {T : ℕ}
    (hT : ∀ v, (run G θ a R w0 T).st v ≠ .active) :
    G.IsVertexCover ↑(output G θ a R w0 T) ∧
      output G θ a R w0 T = Sdelta G ε w0 (delta G θ a R w0 T) ∧
      ∀ C : Finset V, G.IsVertexCover ↑C → wt w0 (output G θ a R w0 T) ≤ (2 + ε) * wt w0 C := by
  have hs : Inv G θ a w0 (run G θ a R w0 T) := inv_run h T
  have hS : output G θ a R w0 T = Sdelta G ε w0 (delta G θ a R w0 T) := by
    ext v
    simp only [output, Sdelta, mem_filter, mem_univ, true_and, tilde_delta h, ← hθ]
    rw [show w0 v - (w0 v - (run G θ a R w0 T).w v) = (run G θ a R w0 T).w v by ring]
    rcases hst : (run G θ a R w0 T).st v with _ | _ | _
    · exact absurd hst (hT v)
    · simpa using hs.inC v hst
    · simpa using hs.notC v hst
  refine ⟨?_, hS, fun C hC => hS ▸ theorem_2_1 hε (isValid_delta h T) hC⟩
  intro u v huv
  simp only [output, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
  rcases hu : (run G θ a R w0 T).st u with _ | _ | _
  · exact absurd hu (hT u)
  · exact Or.inl rfl
  · exact Or.inr (hs.edge u v huv hu)

end VertexCoverLocalRatio
