import Papers.PODC2019.SharpThresholdLLL.Basic

/-!
# Sinkless orientation is an LLL instance exactly at the threshold

The paper ("Applications") observes that sinkless orientation is the prime example of a problem
exactly at the threshold `p = 2^{-d}`, and that the lower bounds for `p ≥ 2^{-d}` come from it.
We make the instance explicit. Let `G` be a finite simple graph. Each edge carries a variable,
its head, uniform on its two endpoints. The event at a node `v` is "`v` is a sink" (`v` is the
head of all its edges). Then:

* every variable affects exactly two events (rank 2): `sinklessInstance_evs_card`;
* the dependency graph is `G`: `sinklessInstance_dep`;
* `Pr[E_v] = 2^{-deg v}`: `sinklessInstance_pr`;
* an assignment avoids all bad events iff it is a sinkless orientation (definitional).

So on a `Δ`-regular graph, `p = 2^{-d}` exactly (`sinkless_at_threshold`). The cited
`Ω(log n)` deterministic and `Ω(log log n)` randomized lower bounds for sinkless orientation are
not formalized here. A port-numbering version of the round-elimination lower bound is in
`Papers/PODC2019/AutomaticSpeedup` (`sinklessOrientation_lower_bound`).
-/

open Finset Cslib.Probability

set_option linter.unusedSectionVars false

namespace SharpThresholdLLL

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The endpoints of an edge. -/
abbrev Ends (e : G.edgeSet) := {w : V // w ∈ (e : Sym2 V)}

lemma card_ends (e : G.edgeSet) : Fintype.card (Ends G e) = 2 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hab : a ≠ b := G.ne_of_adj (by simpa using he)
    rw [Fintype.card_subtype]
    have : (univ.filter fun w => w ∈ s(a, b)) = {a, b} := by ext w; simp
    simp only [this, card_pair hab]

/-- The LLL instance of sinkless orientation on `G`. -/
noncomputable def sinklessInstance : Instance G.edgeSet (Ends G) V where
  prob _ _ := 1 / 2
  prob_nonneg _ _ := by norm_num
  prob_sum e := by rw [Finset.sum_const, card_univ, card_ends]; norm_num
  vbl v := univ.filter fun e => v ∈ (e : Sym2 V)
  bad v x := ∀ e : G.edgeSet, v ∈ (e : Sym2 V) → (x e).1 = v
  bad_local v x y h := by
    constructor
    · intro hx e he; rw [← h e (by simpa using he)]; exact hx e he
    · intro hy e he; rw [h e (by simpa using he)]; exact hy e he

/-- Avoiding all bad events = being a sinkless orientation (every node is the tail of some
edge). -/
lemma sinklessInstance_good_iff (x : ∀ e : G.edgeSet, Ends G e) :
    (∀ v, ¬ (sinklessInstance G).bad v x) ↔
      ∀ v, ∃ e : G.edgeSet, v ∈ (e : Sym2 V) ∧ (x e).1 ≠ v := by
  simp [sinklessInstance]

/-- Rank 2: the variable of an edge affects exactly the events of its two endpoints. -/
lemma sinklessInstance_evs_card (e : G.edgeSet) : ((sinklessInstance G).evs e).card = 2 := by
  have : (sinklessInstance G).evs e = univ.filter fun w => w ∈ (e : Sym2 V) := by
    ext w; simp [Instance.evs, sinklessInstance]
  rw [this, ← Fintype.card_subtype, card_ends]

/-- The dependency graph is `G`. -/
lemma sinklessInstance_dep (v : V) : (sinklessInstance G).dep v = G.neighborFinset v := by
  ext u
  simp only [Instance.dep, sinklessInstance, mem_filter, mem_univ, true_and,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨huv, ⟨e, he⟩, hu, hv⟩
    have : e = s(u, v) := (Sym2.mem_and_mem_iff huv).1 ⟨hu, hv⟩
    subst this
    exact (G.mem_edgeSet.1 he).symm
  · intro h
    exact ⟨G.ne_of_adj h |>.symm, ⟨s(u, v), G.mem_edgeSet.2 h.symm⟩, by simp, by simp⟩

/-- `Pr[v is a sink] = 2^{-deg v}`. -/
lemma sinklessInstance_pr (v : V) : (sinklessInstance G).pr v = (1 / 2) ^ G.degree v := by
  classical
  rw [Instance.pr, Instance.condProb]
  -- the indicator of "`v` is a sink" is a product over edges
  have hind : ∀ x : ∀ e : G.edgeSet, Ends G e,
      (if (sinklessInstance G).bad v x then (1 : ℝ) else 0) =
        ∏ e : G.edgeSet, (if v ∈ (e : Sym2 V) then (if (x e).1 = v then 1 else 0) else 1) := by
    intro x
    by_cases h : ∀ e : G.edgeSet, v ∈ (e : Sym2 V) → (x e).1 = v
    · simp only [show (sinklessInstance G).bad v x from h, ↓reduceIte]; symm
      apply prod_eq_one; intro e _
      by_cases he : v ∈ (e : Sym2 V)
      · simp [he, h e he]
      · simp [he]
    · simp only [show ¬ (sinklessInstance G).bad v x from h, ↓reduceIte]; symm
      push Not at h
      obtain ⟨e, he, hne⟩ := h
      exact prod_eq_zero (mem_univ e) (by simp [he, hne])
  have hprob : ∀ e (w : Ends G e), (sinklessInstance G).prob e w = 1 / 2 := fun _ _ => rfl
  simp_rw [hind]
  rw [piExpect_prod _ fun (e : G.edgeSet) (w : Ends G e) =>
    if v ∈ (e : Sym2 V) then (if w.1 = v then (1 : ℝ) else 0) else 1]
  simp only [Instance.marg_empty, hprob]
  have hfac : ∀ e : G.edgeSet, (∑ w : Ends G e,
      1 / 2 * (if v ∈ (e : Sym2 V) then (if w.1 = v then (1 : ℝ) else 0) else 1)) =
        if v ∈ (e : Sym2 V) then 1 / 2 else 1 := by
    intro e
    by_cases he : v ∈ (e : Sym2 V)
    · simp only [he, ↓reduceIte, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      have : (univ.filter fun w : Ends G e => w.1 = v) = {⟨v, he⟩} := by
        ext w; simp [Subtype.ext_iff]
      rw [this, card_singleton]; norm_num
    · simp only [he, ↓reduceIte, mul_one]
      rw [Finset.sum_const, card_univ, card_ends]; norm_num
  simp_rw [hfac]
  rw [prod_ite, prod_const_one, mul_one, prod_const]
  congr 1
  rw [← G.card_incidenceFinset_eq_degree]
  apply card_bij (fun (e : G.edgeSet) _ => (e : Sym2 V))
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨e.2, he⟩
  · intro e₁ _ e₂ _ h; exact Subtype.ext h
  · intro e he
    rw [SimpleGraph.mem_incidenceFinset] at he
    exact ⟨⟨e, he.1⟩, by simpa using he.2, rfl⟩

/-- **Sinkless orientation is exactly at the threshold.** On a `Δ`-regular graph, the sinkless
orientation instance has rank 2, dependency degree `Δ`, and `Pr[E_v] · 2^Δ = 1`. It violates
the criterion `p · 2^d < 1` of Theorems 1.1 and 1.3 only by equality. -/
theorem sinkless_at_threshold {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    (∀ e, ((sinklessInstance G).evs e).card = 2) ∧
      (∀ v, ((sinklessInstance G).dep v).card = Δ) ∧
      ∀ v, (sinklessInstance G).pr v * 2 ^ Δ = 1 := by
  refine ⟨sinklessInstance_evs_card G, fun v => ?_, fun v => ?_⟩
  · rw [sinklessInstance_dep, G.card_neighborFinset_eq_degree, hreg v]
  · rw [sinklessInstance_pr, hreg v, ← mul_pow]; norm_num

end SharpThresholdLLL
