import Papers.PODC2024.MinWeightCycleCongest.UndirectedGadget

/-!
# From gap instances to CONGEST lower bounds for approximation

Generic glue between the lower-bound graphs and `Cslib.Congest.LBFamily`:

* `WDigraph.comap`, `WGraph.comap`: relabel the vertices along an equivalence (the vertex names of
  the CONGEST model are the IDs `0, …, n-1`; the lower-bound graphs are built on `Vtx k p`).
  `mwc_comap`: relabelling does not change the minimum weight cycle.
* `ediam_le_two_of_hub`: a vertex adjacent to all others gives diameter `≤ 2`.
* `LBFamily.ofWeights`: a family of lower-bound graphs given by input-dependent arc weights.
* `approx_lowerBound` (deterministic) and `approx_rand_lowerBound` (randomized): an algorithm that
  `α`-approximates a quantity `opt` which is `≤ a` on intersecting and `≥ b` on disjoint inputs,
  with `α · a < b`, decides set disjointness, so the simulation theorem applies.
-/

namespace Podc.MinWeightCycleCongest

open Finset Cslib.Congest Cslib.CommunicationComplexity Cslib.CommunicationComplexity.Protocol

open scoped ENNReal

variable {V V' : Type*} {W : ℕ}

/-! ### Relabelling -/

/-- Relabel a digraph along `e : V → V'`. -/
def WDigraph.comap (D : WDigraph V' W) (e : V → V') : WDigraph V W where
  wt u v := D.wt (e u) (e v)

/-- Relabel an undirected graph along an injective map `e : V → V'`. -/
def WGraph.comap (G : WGraph V' W) (e : V ↪ V') : WGraph V W where
  wt u v := G.wt (e u) (e v)
  symm u v := G.symm (e u) (e v)
  loopless v := G.loopless (e v)

/-- Transport a cycle of `D` to the relabelled digraph. -/
def WDigraph.Cycle.comap {D : WDigraph V' W} (e : V ≃ V') (c : D.Cycle) : (D.comap e).Cycle where
  len := c.len
  two_le_len := c.two_le_len
  vtx i := e.symm (c.vtx i)
  periodic i := by simp [c.periodic]
  inj i hi j hj h := c.inj i hi j hj (e.symm.injective h)
  arc i := by simpa [WDigraph.comap] using c.arc i

/-- Transport a cycle of the relabelled digraph back to `D`. -/
def WDigraph.Cycle.unComap {D : WDigraph V' W} (e : V ≃ V') (c : (D.comap e).Cycle) : D.Cycle where
  len := c.len
  two_le_len := c.two_le_len
  vtx i := e (c.vtx i)
  periodic i := by simp [c.periodic]
  inj i hi j hj h := c.inj i hi j hj (e.injective h)
  arc i := c.arc i

/-- Relabelling along an equivalence does not change the minimum weight cycle. -/
lemma WDigraph.mwc_comap (D : WDigraph V' W) (e : V ≃ V') : (D.comap e).mwc = D.mwc := by
  apply le_antisymm
  · refine le_iInf fun c => (iInf_le _ (c.comap e)).trans (le_of_eq ?_)
    simp [WDigraph.Cycle.comap, WDigraph.Cycle.weight, WDigraph.w, WDigraph.comap]
  · exact le_iInf fun c => (iInf_le _ (c.unComap e)).trans (le_of_eq rfl)

/-- Relabelling along an equivalence does not change the minimum weight cycle. -/
lemma WGraph.mwc_comap (G : WGraph V' W) (e : V ≃ V') : (G.comap e.toEmbedding).mwc = G.mwc := by
  apply le_antisymm
  · refine le_iInf fun c => ?_
    let c' : (G.comap e.toEmbedding).Cycle :=
      { len := c.len, three_le_len := c.three_le_len, vtx := fun i => e.symm (c.vtx i)
        periodic := fun i => by simp [c.periodic]
        inj := fun i hi j hj h => c.inj i hi j hj (e.symm.injective h)
        adj := fun i => by simpa [WGraph.comap] using c.adj i }
    refine (iInf_le _ c').trans (le_of_eq ?_)
    simp [c', WGraph.Cycle.weight, WGraph.w, WGraph.comap]
  · refine le_iInf fun c => ?_
    let c' : G.Cycle :=
      { len := c.len, three_le_len := c.three_le_len, vtx := fun i => e (c.vtx i)
        periodic := fun i => by simp [c.periodic]
        inj := fun i hi j hj h => c.inj i hi j hj (e.injective h)
        adj := fun i => c.adj i }
    exact (iInf_le _ c').trans (le_of_eq rfl)

/-- A vertex adjacent to every other vertex makes the diameter at most `2`. -/
lemma ediam_le_two_of_hub {G : SimpleGraph V} (h : V) (hh : ∀ v, v ≠ h → G.Adj v h) :
    G.ediam ≤ 2 := by
  rw [SimpleGraph.ediam_le_iff]
  intro u v
  by_cases huv : u = v
  · subst huv; simp
  by_cases hu : u = h
  · subst hu
    exact (SimpleGraph.edist_le (SimpleGraph.Walk.cons (hh v (Ne.symm huv)).symm .nil)).trans
      (by norm_num)
  by_cases hv : v = h
  · subst hv
    exact (SimpleGraph.edist_le (SimpleGraph.Walk.cons (hh u hu) .nil)).trans (by norm_num)
  exact (SimpleGraph.edist_le
    (SimpleGraph.Walk.cons (hh u hu) (SimpleGraph.Walk.cons (hh v hv).symm .nil))).trans
    (by norm_num)

/-! ### Families of lower-bound graphs given by arc weights -/

-- CSLib candidate
/-- A family of lower-bound graphs whose members are given by input-dependent arc weights
`wt x y u v` (`none` = no arc). The network is the underlying undirected graph; the input of node
`v` is `loc (wt x y v ·) (wt x y · v)` (its outgoing and incoming arcs). -/
def ofWeights {X Y α I : Type*} (wt : X → Y → V → V → Option α)
    (loc : (V → Option α) → (V → Option α) → I) (alice : V → Bool) (Ecut : Finset (V × V))
    (Ecut_sub : ∀ p ∈ Ecut, alice p.1 = true ∧ alice p.2 = false)
    (cut : ∀ x y a b, alice a = true → alice b = false →
      ((wt x y a b).isSome ∨ (wt x y b a).isSome) → (a, b) ∈ Ecut)
    (indep_y : ∀ x y y' u v, (alice u = true ∨ alice v = true) → wt x y u v = wt x y' u v)
    (indep_x : ∀ x x' y u v, (alice u = false ∨ alice v = false) → wt x y u v = wt x' y u v) :
    LBFamily X Y V I where
  G x y := SimpleGraph.fromRel fun u v => (wt x y u v).isSome
  inp x y v := loc (wt x y v) (fun u => wt x y u v)
  alice := alice
  Ecut := Ecut
  Ecut_sub := Ecut_sub
  adj_cut x y a b ha hb h := by
    rw [SimpleGraph.fromRel_adj] at h
    exact cut x y a b ha hb h.2
  adj_alice x y y' a b ha hb := by
    simp only [SimpleGraph.fromRel_adj, indep_y x y y' a b (Or.inl ha),
      indep_y x y y' b a (Or.inl hb)]
  adj_bob x x' y a b ha hb := by
    simp only [SimpleGraph.fromRel_adj, indep_x x x' y a b (Or.inl ha),
      indep_x x x' y b a (Or.inl hb)]
  adj_fixed x x' y y' a b ha hb := by
    simp only [SimpleGraph.fromRel_adj, indep_y x y y' a b (Or.inl ha),
      indep_y x y y' b a (Or.inr ha), indep_x x x' y' a b (Or.inr hb),
      indep_x x x' y' b a (Or.inl hb)]
  inp_alice x y y' v hv := by
    congr 1
    · funext u; exact indep_y x y y' v u (Or.inl hv)
    · funext u; exact indep_y x y y' u v (Or.inr hv)
  inp_bob x x' y v hv := by
    congr 1
    · funext u; exact indep_x x x' y v u (Or.inl hv)
    · funext u; exact indep_x x x' y u v (Or.inr hv)

/-! ### Approximation algorithms decide set disjointness on gap families -/

section Approx

variable {I σ : Type*} {B : ℕ}

/-- The decision version of an estimating algorithm: node `v` rejects iff it outputs an estimate
`e ≥ b`. -/
noncomputable def thresholdAlg (A : Algorithm V I σ B) (est : V → σ → Option ℝ≥0∞) (b : ℝ≥0∞) :
    Algorithm V I σ B :=
  { A with out := fun v s => match est v s with
      | none => true
      | some e => decide (e < b) }

lemma thresholdAlg_run (A : Algorithm V I σ B) (est : V → σ → Option ℝ≥0∞) (b : ℝ≥0∞)
    (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I) :
    ∀ t, (thresholdAlg A est b).run G inp t = A.run G inp t
  | 0 => rfl
  | t + 1 => by
      funext v
      simp only [Algorithm.run, thresholdAlg_run A est b G inp t]
      rfl

/-- With a gap `α · a < b`, the threshold algorithm accepts iff `opt ≤ a`, on instances where
`opt ≤ a` or `b ≤ opt`. -/
lemma thresholdAlg_accepts (A : Algorithm V I σ B) (est : V → σ → Option ℝ≥0∞)
    {α a b opt : ℝ≥0∞} (hab : α * a < b) (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I)
    (T : ℕ) (h : ApproxOutput α opt (outputs A est G inp T)) :
    (opt ≤ a → (thresholdAlg A est b).Accepts G inp T) ∧
      (b ≤ opt → ¬ (thresholdAlg A est b).Accepts G inp T) := by
  obtain ⟨⟨v₀, hv₀⟩, hok⟩ := h
  simp only [Algorithm.Accepts, thresholdAlg_run]
  constructor
  · intro hopt v
    simp only [thresholdAlg]
    cases he : est v (A.run G inp T v) with
    | none => rfl
    | some e =>
      have := (hok v e he).2
      simp only [decide_eq_true_eq]
      exact lt_of_le_of_lt (this.trans (mul_le_mul_right hopt α)) hab
  · intro hopt hacc
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hv₀
    have h1 := hacc v₀
    simp only [thresholdAlg] at h1
    simp only [outputs] at he
    rw [he] at h1
    simp only [decide_eq_true_eq] at h1
    exact absurd (hopt.trans (hok v₀ e he).1) (not_le.2 h1)

lemma disj_false_iff {ι : Type*} [Fintype ι] {x y : ι → Bool} :
    disj x y = false ↔ ∃ q, x q = true ∧ y q = true := by
  simp [disj]

lemma disj_true_iff {ι : Type*} [Fintype ι] {x y : ι → Bool} :
    disj x y = true ↔ ∀ q, ¬ (x q = true ∧ y q = true) := by
  simp [disj]

-- CSLib candidate
/-- **Gap lower bound (deterministic).** On a family of lower-bound graphs for set disjointness
where `opt ≤ a` on intersecting and `opt ≥ b` on disjoint inputs, an algorithm whose outputs
`α`-approximate `opt` within `T` rounds, with `α · a < b`, needs `K ≤ T · 2 · |Ecut| · B + 2`. -/
theorem approx_lowerBound {ι : Type*} [Fintype ι] [Finite V]
    (F : LBFamily (ι → Bool) (ι → Bool) V I) [∀ x y, DecidableRel (F.G x y).Adj]
    (A : Algorithm V I σ B) (est : V → σ → Option ℝ≥0∞) (T : ℕ) {α a b : ℝ≥0∞}
    (hab : α * a < b) (opt : (ι → Bool) → (ι → Bool) → ℝ≥0∞)
    (hA : ∀ x y, ApproxOutput α (opt x y) (outputs A est (F.G x y) (F.inp x y) T))
    (hint : ∀ x y, (∃ q, x q = true ∧ y q = true) → opt x y ≤ a)
    (hdisj : ∀ x y, (∀ q, ¬ (x q = true ∧ y q = true)) → b ≤ opt x y) :
    Fintype.card ι ≤ T * (2 * (F.Ecut.card * B)) + 2 := by
  refine F.not_disj_lowerBound (thresholdAlg A est b) T fun x y => ?_
  have h := thresholdAlg_accepts A est hab (F.G x y) (F.inp x y) T (hA x y)
  by_cases hq : ∃ q, x q = true ∧ y q = true
  · have hd : disj x y = false := disj_false_iff.2 hq
    simp only [hd, iff_true]
    exact h.1 (hint x y hq)
  · have hq' : ∀ q, ¬ (x q = true ∧ y q = true) := fun q h' => hq ⟨q, h'⟩
    have hd : disj x y = true := disj_true_iff.2 hq'
    simp only [hd, Bool.true_eq_false, iff_false]
    exact h.2 (hdisj x y hq')

/-- Number of random strings on which a randomized estimating algorithm fails to output an
`α`-approximation of `opt`. -/
noncomputable def failCount {ρ : Type*} [Fintype V] [Fintype ρ] (A : Algorithm V (I × ρ) σ B)
    (est : V → σ → Option ℝ≥0∞) (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I) (T : ℕ)
    (α opt : ℝ≥0∞) : ℕ := by
  classical
  exact (univ.filter fun r : V → ρ =>
    ¬ ApproxOutput α opt (outputs A est G (fun v => (inp v, r v)) T)).card

-- CSLib candidate
/-- **Gap lower bound (randomized).** As `approx_lowerBound`, for a randomized algorithm (private
random strings `r v : ρ`) failing with probability at most `δ` on every instance of the family; the
communication lower bound `C` for `δ`-error private-coin protocols for `¬DISJ` is a hypothesis
(Razborov / Kalyanasundaram–Schnitger: `C = Ω(K)`). -/
theorem approx_rand_lowerBound {ι ρ : Type*} [Fintype ι] [Fintype V] [DecidableEq V] [Fintype ρ]
    [Nonempty ρ] (F : LBFamily (ι → Bool) (ι → Bool) V I) [∀ x y, DecidableRel (F.G x y).Adj]
    (A : Algorithm V (I × ρ) σ B) (est : V → σ → Option ℝ≥0∞) (T : ℕ) {α a b : ℝ≥0∞}
    (hab : α * a < b) (opt : (ι → Bool) → (ι → Bool) → ℝ≥0∞) (δ : ℝ)
    (hA : ∀ x y, (failCount A est (F.G x y) (F.inp x y) T α (opt x y) : ℝ) ≤
      δ * Fintype.card (V → ρ))
    (hint : ∀ x y, (∃ q, x q = true ∧ y q = true) → opt x y ≤ a)
    (hdisj : ∀ x y, (∀ q, ¬ (x q = true ∧ y q = true)) → b ≤ opt x y) (C : ℕ)
    (hC : ∀ (P : Protocol ((ι → Bool) × ({v // F.alice v = true} → ρ))
      ((ι → Bool) × ({v // F.alice v = false} → ρ)) Bool) (c : ℕ),
      P.RandComputes (fun x y => !disj x y) δ → P.CostLE c → C ≤ c) :
    C ≤ T * (2 * (F.Ecut.card * B)) + 2 := by
  classical
  refine F.rand_lowerBound (thresholdAlg A est b) T (fun x y => !disj x y) δ
    (fun x y => le_trans ?_ (hA x y)) C hC
  simp only [LBFamily.Algorithm.randErr, failCount]
  norm_cast
  refine Finset.card_le_card fun r => ?_
  simp only [mem_filter, mem_univ, true_and]
  intro hr hok
  apply hr
  have h := thresholdAlg_accepts A est hab (F.G x y) (fun v => (F.inp x y v, r v)) T hok
  by_cases hq : ∃ q, x q = true ∧ y q = true
  · have hd : disj x y = false := disj_false_iff.2 hq
    simp [hd, h.1 (hint x y hq)]
  · have hq' : ∀ q, ¬ (x q = true ∧ y q = true) := fun q h' => hq ⟨q, h'⟩
    have hd : disj x y = true := disj_true_iff.2 hq'
    simp [hd, h.2 (hdisj x y hq')]

end Approx

end Podc.MinWeightCycleCongest
