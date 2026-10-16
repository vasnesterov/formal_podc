import Papers.PODC2011.FaultTolerantSpanners.TwoSpanner.Defs

/-!
# Lemma 3.8 of Dinitz–Krauthgamer [DK11] is false as stated; a corrected version

[DK11] M. Dinitz, R. Krauthgamer, *Fault-Tolerant Spanners: Better and Simpler*, PODC 2011
(arXiv 1101.5753), Section 3.5.

For a partition of `V` into clusters (here: a labelling `cl : V → ι`, cluster `C = cl⁻¹ i`) the
paper defines

* `N(C)` — the vertices outside `C` adjacent (in either direction) to a vertex of `C`;
* `δ(C)` — the arcs with exactly one endpoint in `C`; `E(C)` — the arcs with both endpoints in `C`;
* `G(C)` — the subgraph of `G` induced by `C ∪ N(C)`;
* `LP(C)` — LP (4) for `G(C)`, where the arcs of `δ(C)` get cost `0`.

**Lemma 3.8** claims `∑_{C ∈ P} LP*(C) ≤ LP*`. This is false: an arc of `G(C)` with both endpoints
in `N(C)` keeps its cost in `LP(C)`, but may lack (in `G(C)`) the length-2 paths that serve it in
`G`. In the proof, the solution `⟨x^C, f^C⟩` puts `x^C_e = x_e` on `E(C)` and `x^C_e = 1` on
`δ(C)`, but says nothing about such arcs. `lemma_3_8_counterexample` gives an explicit
counterexample (`r = 0`, four vertices).

`lemma_3_8_corrected` proves the statement for the modified program `LP'(C)` in which **every** arc
of `G(C)` outside `E(C)` has cost `0` (this is what the analysis of Theorem 3.9 uses: "`x̃_e / 4` are
the averages of the `LP(C)` values for the rounds in which `e` does not have cost `0`", i.e. the
rounds in which `e ∈ E(C)`).

Optimal values `LP*` are not formalised: the counterexample is stated as "there is a feasible
solution of LP (4) of value `4`, while every family of feasible solutions of the `LP(C)` has total
value `≥ M`", and the corrected lemma as "every feasible solution of LP (4) yields feasible
solutions of the `LP'(C)` of no larger total value".
-/

open Finset

namespace DinitzKrauthgamer

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [DecidableEq ι]

/-- `N(C)` for the cluster `C = cl⁻¹ i`: the vertices outside `C` that are adjacent (in either
direction) to some vertex of `C`. -/
def clusterNbhd (E : Finset (V × V)) (cl : V → ι) (i : ι) : Finset V :=
  univ.filter fun w => cl w ≠ i ∧ ∃ a, cl a = i ∧ ((a, w) ∈ E ∨ (w, a) ∈ E)

/-- The arcs of `G(C)`, the subgraph induced by `C ∪ N(C)`. -/
def clusterArcs (E : Finset (V × V)) (cl : V → ι) (i : ι) : Finset (V × V) :=
  E.filter fun e => (cl e.1 = i ∨ e.1 ∈ clusterNbhd E cl i) ∧ (cl e.2 = i ∨ e.2 ∈ clusterNbhd E cl i)

/-- The costs of `LP(C)` as defined in [DK11]: arcs of `δ(C)` (exactly one endpoint in `C`) get
cost `0`, all other arcs keep their cost. -/
def clusterCost (c : V × V → ℝ) (cl : V → ι) (i : ι) : V × V → ℝ :=
  fun e => if (cl e.1 = i ∧ cl e.2 ≠ i) ∨ (cl e.1 ≠ i ∧ cl e.2 = i) then 0 else c e

/-- The costs of the corrected program `LP'(C)`: only arcs of `E(C)` (both endpoints in `C`) keep
their cost. -/
def clusterCost' (c : V × V → ℝ) (cl : V → ι) (i : ι) : V × V → ℝ :=
  fun e => if cl e.1 = i ∧ cl e.2 = i then c e else 0

lemma clusterArcs_subset (E : Finset (V × V)) (cl : V → ι) (i : ι) : clusterArcs E cl i ⊆ E :=
  Finset.filter_subset _ _

lemma mids_clusterArcs_subset {E : Finset (V × V)} {cl : V → ι} {i : ι} {u v : V} :
    mids (clusterArcs E cl i) u v ⊆ mids E u v := by
  intro z hz
  rw [mem_mids] at hz ⊢
  exact ⟨clusterArcs_subset E cl i hz.1, clusterArcs_subset E cl i hz.2⟩

/-- For an arc inside a cluster, all its length-2 paths in `G` survive in `G(C)`. -/
lemma mids_clusterArcs {E : Finset (V × V)} {cl : V → ι} {i : ι} {u v : V} (hu : cl u = i)
    (hv : cl v = i) : mids (clusterArcs E cl i) u v = mids E u v := by
  ext z
  simp only [mem_mids, clusterArcs, mem_filter, clusterNbhd, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, Or.inl hu, ?_⟩, ⟨h2, ?_, Or.inl hv⟩⟩
    · by_cases hz : cl z = i
      · exact Or.inl hz
      · exact Or.inr ⟨hz, u, hu, Or.inl h1⟩
    · by_cases hz : cl z = i
      · exact Or.inl hz
      · exact Or.inr ⟨hz, v, hv, Or.inr h2⟩

/-! ### The counterexample -/

namespace Lemma38Counterexample

/-- Vertices `a = 0`, `b = 1`, `c = 2`, `d = 3`. -/
abbrev Vtx := Fin 4

/-- Arcs `c → a`, `c → b`, `a → b`, `a → d`, `d → b`. -/
def arcs : Finset (Vtx × Vtx) := {(2, 0), (2, 1), (0, 1), (0, 3), (3, 1)}

/-- Costs: `M` on `a → b`, `1` on all other arcs. -/
def costs (M : ℝ) : Vtx × Vtx → ℝ := fun e => if e = (0, 1) then M else 1

/-- The partition `{{c}, {a, b, d}}`: the label `true` is the cluster `{c}`. -/
def cl : Vtx → Bool := fun z => decide (z = 2)

lemma loopless : Loopless arcs := by unfold Loopless; decide

lemma clusterArcs_c : clusterArcs arcs cl true = {(2, 0), (2, 1), (0, 1)} := by decide

lemma mids_c : mids (clusterArcs arcs cl true) 0 1 = ∅ := by
  rw [clusterArcs_c]; decide

lemma mids_ab : mids arcs 0 1 = {3} := by decide

/-- The LP (4) solution for `G`: `x = 1` on all arcs but `a → b`, one unit of flow on
`a → d → b`. -/
noncomputable def x₀ : Vtx × Vtx → ℝ := fun e => if e = (0, 1) then 0 else 1

/-- The flow of `x₀`. -/
noncomputable def f₀ : Vtx × Vtx → Vtx → ℝ := fun uv z => if uv = (0, 1) ∧ z = 3 then 1 else 0

lemma x₀_nonneg (e : Vtx × Vtx) : 0 ≤ x₀ e := by
  simp only [x₀]; split_ifs <;> norm_num

lemma lp4_feasible : IsLP4Feasible arcs 0 x₀ f₀ where
  capacity := by
    intro uv huv e he
    by_cases h : uv = (0, 1)
    · subst h
      simp only [mids_ab, Finset.sum_filter, Finset.sum_singleton]
      split_ifs with he'
      · rcases he' with rfl | rfl <;> simp [x₀, f₀]
      · exact x₀_nonneg e
    · rw [Finset.sum_eq_zero fun z _ => by simp [f₀, h]]
      exact x₀_nonneg e
  knapsack := by
    intro uv huv W hW hWr
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hWr)]
    simp only [Finset.card_empty, CharP.cast_eq_zero, zero_add, sub_zero, one_mul,
      Finset.sdiff_empty]
    by_cases h : uv = (0, 1)
    · subst h
      simp [mids_ab, x₀, f₀]
    · have : 0 ≤ ∑ z ∈ mids arcs uv.1 uv.2, f₀ uv z :=
        Finset.sum_nonneg fun z _ => by simp only [f₀]; split_ifs <;> norm_num
      simp only [x₀, h, ite_false]
      linarith
  x_nonneg := fun e _ => x₀_nonneg e
  x_le_one := fun e _ => by simp only [x₀]; split_ifs <;> norm_num
  f_nonneg := fun uv _ z _ => by simp only [f₀]; split_ifs <;> norm_num

lemma lp4_value (M : ℝ) : lpValue (costs M) arcs x₀ = 4 := by
  simp [lpValue, arcs, costs, x₀]
  norm_num

/-- Every feasible solution of `LP({c})` (as defined in [DK11]) has `x_{(a,b)} = 1`: in `G({c})`
(induced by `{c, a, b}`) the arc `a → b` has no length-2 path, and its cost `M` is kept since
`a, b ∈ N({c})`. -/
lemma lpC_value_ge {M : ℝ} (hM : 0 ≤ M) {x : Vtx × Vtx → ℝ} {f : Vtx × Vtx → Vtx → ℝ}
    (h : IsLP4Feasible (clusterArcs arcs cl true) 0 x f) :
    M ≤ lpValue (clusterCost (costs M) cl true) (clusterArcs arcs cl true) x := by
  have hab : ((0, 1) : Vtx × Vtx) ∈ clusterArcs arcs cl true := by rw [clusterArcs_c]; decide
  have hk := h.knapsack _ hab ∅ (Finset.empty_subset _) (by simp)
  simp only [mids_c, Finset.sdiff_empty, Finset.sum_empty, Finset.card_empty,
    CharP.cast_eq_zero, zero_add, sub_zero, one_mul, add_zero] at hk
  have hx1 : x (0, 1) = 1 := le_antisymm (h.x_le_one _ hab) hk
  have := Finset.single_le_sum (f := fun e => clusterCost (costs M) cl true e * x e)
    (fun e he => mul_nonneg (by
      simp only [clusterCost, costs]; split_ifs <;> linarith) (h.x_nonneg e he)) hab
  have hc : clusterCost (costs M) cl true (0, 1) = M := by
    simp [clusterCost, costs, cl]
  simpa [lpValue, hc, hx1] using this

/-- `LP(C)` values are nonnegative for nonnegative costs. -/
lemma lpC_value_nonneg {M : ℝ} (hM : 0 ≤ M) (i : Bool) {x : Vtx × Vtx → ℝ}
    {f : Vtx × Vtx → Vtx → ℝ} (h : IsLP4Feasible (clusterArcs arcs cl i) 0 x f) :
    0 ≤ lpValue (clusterCost (costs M) cl i) (clusterArcs arcs cl i) x :=
  Finset.sum_nonneg fun e he => mul_nonneg (by
    simp only [clusterCost, costs]; split_ifs <;> linarith) (h.x_nonneg e he)

end Lemma38Counterexample

open Lemma38Counterexample in
/-- **Lemma 3.8 of [DK11] is false.** Take `r = 0`, vertices `a, b, c, d`, arcs `c → a`,
`c → b`, `a → b` (cost `M > 4`), `a → d`, `d → b` (cost `1` each, as are `c → a`, `c → b`), and the
partition `{{c}, {a, b, d}}`. LP (4) for `G` has a feasible solution of value `4`, but every
choice of feasible solutions of `LP({c})` and `LP({a, b, d})` has total value `≥ M > 4`; hence
`∑_C LP*(C) ≥ M > 4 ≥ LP*`. -/
theorem lemma_3_8_counterexample (M : ℝ) (hM : 4 < M) :
    Loopless arcs ∧ (∀ e ∈ arcs, 0 ≤ costs M e) ∧
    (∃ x f, IsLP4Feasible arcs 0 x f ∧ lpValue (costs M) arcs x = 4) ∧
    ∀ (xC : Bool → Vtx × Vtx → ℝ) (fC : Bool → Vtx × Vtx → Vtx → ℝ),
      (∀ i, IsLP4Feasible (clusterArcs arcs cl i) 0 (xC i) (fC i)) →
      M ≤ ∑ i, lpValue (clusterCost (costs M) cl i) (clusterArcs arcs cl i) (xC i) := by
  refine ⟨loopless, fun e _ => ?_, ⟨x₀, f₀, lp4_feasible, lp4_value M⟩, fun xC fC h => ?_⟩
  · simp only [costs]; split_ifs <;> linarith
  · rw [Fintype.sum_bool]
    have h1 := lpC_value_ge (by linarith) (h true)
    have h2 := lpC_value_nonneg (M := M) (by linarith) false (h false)
    linarith

/-! ### The corrected Lemma 3.8 -/

/-- **Lemma 3.8 of [DK11], corrected.** Let `LP'(C)` be LP (4) for `G(C)` (the subgraph induced
by `C ∪ N(C)`) where every arc not inside `C` has cost `0`. For every partition into clusters
(`cl : V → ι`) and every feasible solution `(x, f)` of LP (4) for `G` (nonnegative costs), there are
feasible solutions `(x^C, f^C)` of the `LP'(C)` with `∑_C value(LP'(C), x^C) ≤ ∑_e c_e x_e`.
In particular `∑_C LP'*(C) ≤ LP*`.

Construction (as in the paper): `x^C = x` on `E(C)` and `x^C = 1` on the other arcs of `G(C)`;
the flows are copied from `f` (the paper sets them to `0` for arcs outside `E(C)`, which also
works). -/
theorem lemma_3_8_corrected [Fintype ι] {E : Finset (V × V)} {r : ℕ} {c : V × V → ℝ}
    (hc : ∀ e ∈ E, 0 ≤ c e) (cl : V → ι) {x : V × V → ℝ} {f : V × V → V → ℝ}
    (h : IsLP4Feasible E r x f) :
    ∃ (xC : ι → V × V → ℝ) (fC : ι → V × V → V → ℝ),
      (∀ i, IsLP4Feasible (clusterArcs E cl i) r (xC i) (fC i)) ∧
      ∑ i, lpValue (clusterCost' c cl i) (clusterArcs E cl i) (xC i) ≤ lpValue c E x := by
  set xC : ι → V × V → ℝ := fun i e => if cl e.1 = i ∧ cl e.2 = i then x e else 1 with hxC
  have hxle : ∀ i, ∀ e ∈ E, x e ≤ xC i e := by
    intro i e he
    simp only [hxC]; split_ifs
    · exact le_refl _
    · exact h.x_le_one e he
  refine ⟨xC, fun _ => f, fun i => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- capacity
    intro uv huv e he
    have huvE := clusterArcs_subset E cl i huv
    have heE := clusterArcs_subset E cl i he
    refine le_trans ?_ ((h.capacity uv huvE e heE).trans (hxle i e heE))
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (mids_clusterArcs_subset)) ?_
    intro z hz _
    exact h.f_nonneg uv huvE z (Finset.mem_filter.mp hz).1
  · -- knapsack
    intro uv huv W hW hWr
    have huvE := clusterArcs_subset E cl i huv
    by_cases hin : cl uv.1 = i ∧ cl uv.2 = i
    · rw [mids_clusterArcs hin.1 hin.2] at hW ⊢
      simp only [hxC, hin, and_self, ite_true]
      exact h.knapsack uv huvE W hW hWr
    · simp only [hxC, hin, ite_false, mul_one]
      have : 0 ≤ ∑ z ∈ mids (clusterArcs E cl i) uv.1 uv.2 \ W, f uv z :=
        Finset.sum_nonneg fun z hz => h.f_nonneg uv huvE z
          (mids_clusterArcs_subset (Finset.mem_sdiff.mp hz).1)
      linarith
  · intro e he
    simp only [hxC]; split_ifs
    · exact h.x_nonneg e (clusterArcs_subset E cl i he)
    · norm_num
  · intro e he
    simp only [hxC]; split_ifs
    · exact h.x_le_one e (clusterArcs_subset E cl i he)
    · exact le_refl _
  · intro uv huv z hz
    exact h.f_nonneg uv (clusterArcs_subset E cl i huv) z
      (mids_clusterArcs_subset hz)
  · -- the cost bound
    have hterm : ∀ i, lpValue (clusterCost' c cl i) (clusterArcs E cl i) (xC i) =
        ∑ e ∈ E, if cl e.1 = i ∧ cl e.2 = i then c e * x e else 0 := by
      intro i
      rw [lpValue]
      refine Finset.sum_subset_zero_on_sdiff (clusterArcs_subset E cl i) ?_ ?_
      · intro e he
        have hnot : ¬(cl e.1 = i ∧ cl e.2 = i) := by
          rintro ⟨h1, h2⟩
          exact (Finset.mem_sdiff.mp he).2
            (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, Or.inl h1, Or.inl h2⟩)
        simp [hnot]
      · intro e _
        simp only [clusterCost', hxC]
        split_ifs <;> simp
    simp only [hterm]
    rw [Finset.sum_comm, lpValue]
    refine Finset.sum_le_sum fun e he => ?_
    have : ∀ i, (if cl e.1 = i ∧ cl e.2 = i then c e * x e else 0) =
        if cl e.1 = i then (if cl e.2 = cl e.1 then c e * x e else 0) else 0 := by
      intro i
      by_cases h1 : cl e.1 = i
      · subst h1; simp
      · simp [h1]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have := mul_nonneg (hc e he) (h.x_nonneg e he)
    split_ifs <;> linarith

end DinitzKrauthgamer
