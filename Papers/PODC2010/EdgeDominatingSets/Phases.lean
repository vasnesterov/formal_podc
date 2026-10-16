import Papers.PODC2010.EdgeDominatingSets.Distinguishable

/-!
# The phases of the algorithms of §6 and §7, as global processes on edge sets

The algorithms of Theorems 4 and 5 process the matchings `M_G(i, j)` one pair `(i, j)` at a time,
all edges of a matching in parallel. Step `n` processes the pair `(n / Δ, n % Δ)`; `Δ²` steps
cover all pairs with `i, j < Δ`.

* `addStep` (phase I of Theorem 4): add `e ∈ M_G(i, j)` unless both endpoints are already covered.
* `remStep` (phase II of Theorem 4): remove `e ∈ D ∩ M_G(i, j)` if both endpoints are covered by
  `D \ {e}`.
* `matchStep` (phase I of Theorem 5): add `e ∈ M_G(i, j)` if neither endpoint is covered.

Results: after phase I of Theorem 4 every node with a distinguishable neighbour is covered
(`covered_phase1`); phase II keeps covered nodes covered (`covered_phase2`) and afterwards every
edge has an endpoint not covered by any other edge (`private_phase2`); `card_mul_le` is the
counting argument `|D| ≤ d|V|/(d+1)` for such "star forests".
-/

namespace Podc.EdgeDominatingSets

open Cslib.PortNumbering Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `x` is covered by the edge set `D`. -/
def Covered (D : Finset (Sym2 V)) (x : V) : Prop := ∃ e ∈ D, x ∈ e

omit [Fintype V] [DecidableEq V] in
theorem Covered.mono {D D' : Finset (Sym2 V)} (h : D ⊆ D') {x : V} (hx : Covered D x) :
    Covered D' x := let ⟨e, he, hxe⟩ := hx; ⟨e, h he, hxe⟩

open Classical in
/-- Phase I step of Theorem 4: add each edge of `M_G(i, j)` unless both endpoints are covered. -/
noncomputable def addStep (G : PNGraph V) (i j : ℕ) (D : Finset (Sym2 V)) : Finset (Sym2 V) :=
  D ∪ (M G i j).filter fun e => ¬ ∀ x ∈ e, Covered D x

open Classical in
/-- Phase II step of Theorem 4: remove each edge of `D ∩ M_G(i, j)` whose endpoints are both
covered by other edges of `D`. -/
noncomputable def remStep (G : PNGraph V) (i j : ℕ) (D : Finset (Sym2 V)) : Finset (Sym2 V) :=
  D.filter fun e => ¬ (e ∈ M G i j ∧ ∀ x ∈ e, ∃ e' ∈ D, e' ≠ e ∧ x ∈ e')

open Classical in
/-- Phase I step of Theorem 5: add each edge of `M_G(i, j)` whose endpoints are both uncovered. -/
noncomputable def matchStep (G : PNGraph V) (i j : ℕ) (D : Finset (Sym2 V)) : Finset (Sym2 V) :=
  D ∪ (M G i j).filter fun e => ∀ x ∈ e, ¬ Covered D x

/-- `n` steps of a pair-indexed process, starting from `D₀`; step `n` uses `(n / Δ, n % Δ)`. -/
def iterPairs (step : ℕ → ℕ → Finset (Sym2 V) → Finset (Sym2 V)) (Δ : ℕ)
    (D₀ : Finset (Sym2 V)) : ℕ → Finset (Sym2 V)
  | 0 => D₀
  | n + 1 => step (n / Δ) (n % Δ) (iterPairs step Δ D₀ n)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem iterPairs_zero (step) (Δ : ℕ) (D₀ : Finset (Sym2 V)) :
    iterPairs step Δ D₀ 0 = D₀ := rfl

omit [Fintype V] [DecidableEq V] in
theorem iterPairs_succ (step) (Δ : ℕ) (D₀ : Finset (Sym2 V)) (n : ℕ) :
    iterPairs step Δ D₀ (n + 1) = step (n / Δ) (n % Δ) (iterPairs step Δ D₀ n) := rfl

omit [Fintype V] [DecidableEq V] in
theorem iterPairs_mono {step : ℕ → ℕ → Finset (Sym2 V) → Finset (Sym2 V)}
    (h : ∀ i j D, D ⊆ step i j D) (Δ : ℕ) (D₀ : Finset (Sym2 V)) {m n : ℕ} (hmn : m ≤ n) :
    iterPairs step Δ D₀ m ⊆ iterPairs step Δ D₀ n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (h _ _ _)

omit [Fintype V] [DecidableEq V] in
theorem iterPairs_anti {step : ℕ → ℕ → Finset (Sym2 V) → Finset (Sym2 V)}
    (h : ∀ i j D, step i j D ⊆ D) (Δ : ℕ) (D₀ : Finset (Sym2 V)) {m n : ℕ} (hmn : m ≤ n) :
    iterPairs step Δ D₀ n ⊆ iterPairs step Δ D₀ m := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => exact (h _ _ _).trans ih

theorem subset_addStep (G : PNGraph V) (i j : ℕ) (D : Finset (Sym2 V)) : D ⊆ addStep G i j D :=
  subset_union_left

theorem subset_matchStep (G : PNGraph V) (i j : ℕ) (D : Finset (Sym2 V)) :
    D ⊆ matchStep G i j D := subset_union_left

theorem remStep_subset (G : PNGraph V) (i j : ℕ) (D : Finset (Sym2 V)) : remStep G i j D ⊆ D :=
  filter_subset _ _

/-- The pair `(i, j)` with `i, j < Δ` is processed in step `i * Δ + j < Δ²`. -/
theorem pair_step {Δ i j : ℕ} (hi : i < Δ) (hj : j < Δ) :
    (i * Δ + j) / Δ = i ∧ (i * Δ + j) % Δ = j ∧ i * Δ + j < Δ * Δ := by
  have hΔ : 0 < Δ := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [add_comm, Nat.add_mul_div_right _ _ hΔ, Nat.div_eq_of_lt hj, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  · nlinarith

omit [DecidableEq V] in
/-- Edges of `M_G(i, j)` have `i, j` below the maximum degree. -/
theorem lt_of_mem_M {G : PNGraph V} {Δ : ℕ} (hΔ : ∀ v, G.deg v ≤ Δ) {i j : ℕ} {e : Sym2 V}
    (he : e ∈ M G i j) : i < Δ ∧ j < Δ := by
  obtain ⟨v, hv, rfl, -⟩ := mem_M.1 he
  have hi := (G.dn_spec hv).1
  exact ⟨lt_of_lt_of_le hi (hΔ v), lt_of_lt_of_le (G.rport_lt hi) (hΔ _)⟩

omit [DecidableEq V] in
/-- All edges ever added come from the matchings `M_G(i, j)`. -/
theorem mem_M_of_mem_iterPairs {G : PNGraph V} {step : ℕ → ℕ → Finset (Sym2 V) → Finset (Sym2 V)}
    (h : ∀ i j D, ∀ e ∈ step i j D, e ∈ D ∨ e ∈ M G i j) (Δ : ℕ) {D₀ : Finset (Sym2 V)}
    (h₀ : ∀ e ∈ D₀, ∃ i j, e ∈ M G i j) (n : ℕ) :
    ∀ e ∈ iterPairs step Δ D₀ n, ∃ i j, e ∈ M G i j := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    intro e he
    rcases h _ _ _ e he with h' | h'
    · exact ih e h'
    · exact ⟨_, _, h'⟩

theorem addStep_cases (G : PNGraph V) (i j : ℕ) (D : Finset (Sym2 V)) :
    ∀ e ∈ addStep G i j D, e ∈ D ∨ e ∈ M G i j := by
  classical
  intro e he
  rcases mem_union.1 he with h | h
  · exact Or.inl h
  · exact Or.inr (mem_filter.1 h).1

theorem matchStep_cases (G : PNGraph V) (i j : ℕ) (D : Finset (Sym2 V)) :
    ∀ e ∈ matchStep G i j D, e ∈ D ∨ e ∈ M G i j := by
  classical
  intro e he
  rcases mem_union.1 he with h | h
  · exact Or.inl h
  · exact Or.inr (mem_filter.1 h).1

omit [DecidableEq V] in
/-- The edges of `M_G(i, j)` are edges of the underlying simple graph. -/
theorem mem_edgeSet_of_mem_M {G : PNGraph V} (hG : G.IsSimple) {i j : ℕ} {e : Sym2 V}
    (he : e ∈ M G i j) : e ∈ G.toSimpleGraph.edgeSet := by
  obtain ⟨v, hv, -, rfl⟩ := mem_M.1 he
  exact G.edge_mem_edgeSet hG (G.dn_spec hv).1

/-! ### Phase I of Theorem 4 -/

/-- The edge set after phase I of the algorithm of Theorem 4. -/
noncomputable def phase1 (G : PNGraph V) (Δ : ℕ) (n : ℕ) : Finset (Sym2 V) :=
  iterPairs (addStep G) Δ ∅ n

/-- After phase I, every node with a distinguishable neighbour is covered. -/
theorem covered_phase1 {G : PNGraph V} {Δ : ℕ} (hΔ : ∀ v, G.deg v ≤ Δ) {v : V} {i : ℕ}
    (hv : G.dn v = some i) : Covered (phase1 G Δ (Δ * Δ)) v := by
  classical
  have he := edge_dn_mem_M hv
  obtain ⟨hi, hj⟩ := lt_of_mem_M hΔ he
  obtain ⟨h1, h2, h3⟩ := pair_step hi hj
  refine Covered.mono (iterPairs_mono (subset_addStep G) Δ ∅ (Nat.succ_le_of_lt h3)) ?_
  rw [iterPairs_succ, h1, h2]
  by_cases hc : ∀ x ∈ G.edge v i, Covered (iterPairs (addStep G) Δ ∅ (i * Δ + G.rport v i)) x
  · exact Covered.mono (subset_addStep G _ _ _) (hc v (Sym2.mem_mk_left _ _))
  · exact ⟨G.edge v i, mem_union_right _ (mem_filter.2 ⟨he, hc⟩), Sym2.mem_mk_left _ _⟩

/-! ### Phase II of Theorem 4 -/

/-- The edge set after `n` steps of phase II, starting from `D₀`. -/
noncomputable def phase2 (G : PNGraph V) (Δ : ℕ) (D₀ : Finset (Sym2 V)) (n : ℕ) :
    Finset (Sym2 V) :=
  iterPairs (remStep G) Δ D₀ n

/-- One removal step keeps every covered node covered (because `M_G(i, j)` is a matching). -/
theorem covered_remStep {G : PNGraph V} {i j : ℕ} {D : Finset (Sym2 V)} {x : V}
    (hx : Covered D x) : Covered (remStep G i j D) x := by
  classical
  obtain ⟨e, he, hxe⟩ := hx
  by_cases hr : e ∈ M G i j ∧ ∀ y ∈ e, ∃ e' ∈ D, e' ≠ e ∧ y ∈ e'
  · obtain ⟨e', he', hne, hxe'⟩ := hr.2 x hxe
    refine ⟨e', mem_filter.2 ⟨he', ?_⟩, hxe'⟩
    rintro ⟨hM', -⟩
    exact M_matching hr.1 hM' hne.symm hxe hxe'
  · exact ⟨e, mem_filter.2 ⟨he, hr⟩, hxe⟩

theorem covered_phase2 {G : PNGraph V} {Δ : ℕ} {D₀ : Finset (Sym2 V)} {x : V}
    (hx : Covered D₀ x) (n : ℕ) : Covered (phase2 G Δ D₀ n) x := by
  induction n with
  | zero => exact hx
  | succ n ih => exact covered_remStep ih

/-- After phase II, every remaining edge has an endpoint that is not covered by any other
remaining edge. -/
theorem private_phase2 {G : PNGraph V} {Δ : ℕ} (hΔ : ∀ v, G.deg v ≤ Δ) {D₀ : Finset (Sym2 V)}
    (h₀ : ∀ e ∈ D₀, ∃ i j, e ∈ M G i j) :
    ∀ e ∈ phase2 G Δ D₀ (Δ * Δ), ∃ x ∈ e, ∀ e' ∈ phase2 G Δ D₀ (Δ * Δ), x ∈ e' → e' = e := by
  classical
  intro e he
  obtain ⟨i, j, hM⟩ := h₀ e (iterPairs_anti (remStep_subset G) Δ D₀ (Nat.zero_le _) he)
  obtain ⟨hi, hj⟩ := lt_of_mem_M hΔ hM
  obtain ⟨h1, h2, h3⟩ := pair_step hi hj
  set n := i * Δ + j
  have hfin : phase2 G Δ D₀ (Δ * Δ) ⊆ phase2 G Δ D₀ n :=
    iterPairs_anti (remStep_subset G) Δ D₀ h3.le
  have hfin' : phase2 G Δ D₀ (Δ * Δ) ⊆ phase2 G Δ D₀ (n + 1) :=
    iterPairs_anti (remStep_subset G) Δ D₀ (Nat.succ_le_of_lt h3)
  have he' := hfin' he
  rw [phase2, iterPairs_succ, h1, h2] at he'
  have hnot := (mem_filter.1 he').2
  simp only [not_and, not_forall, not_exists] at hnot
  obtain ⟨x, hxe, hx⟩ := hnot hM
  refine ⟨x, hxe, fun e' he' hxe' => ?_⟩
  by_contra hne
  exact hx e' (hfin he') hne hxe'

/-! ### Counting -/

/-- **Counting for star forests.** If every edge of `D` has an endpoint covered by no other edge
of `D`, and every node is covered by at most `d` edges of `D` (`d ≥ 1`), then
`(d + 1)|D| ≤ d|V|`. -/
theorem card_mul_le {D : Finset (Sym2 V)} {d : ℕ} (hd : 1 ≤ d)
    (hD : ∀ e ∈ D, ¬ e.IsDiag) (hdeg : ∀ v, (D.filter (v ∈ ·)).card ≤ d)
    (hpriv : ∀ e ∈ D, ∃ x ∈ e, ∀ e' ∈ D, x ∈ e' → e' = e) :
    (d + 1) * D.card ≤ d * Fintype.card V := by
  classical
  -- charge `c v` to `v` for each edge at `v`
  let c : V → ℕ := fun v => if (D.filter (v ∈ ·)).card = 1 then d else 1
  have hedge : ∀ e ∈ D, d + 1 ≤ ∑ v ∈ univ.filter (· ∈ e), c v := by
    intro e he
    obtain ⟨x, hxe, hx⟩ := hpriv e he
    obtain ⟨y, rfl⟩ : ∃ y, e = s(x, y) := ⟨_, (Sym2.other_spec hxe).symm⟩
    have hxy : x ≠ y := by
      intro h
      apply hD _ he
      rw [h, Sym2.mk_isDiag_iff]
    have hfil : univ.filter (· ∈ s(x, y)) = {x, y} := by
      ext z; simp [Sym2.mem_iff]
    rw [hfil, sum_pair hxy]
    have hcx : c x = d := by
      have : D.filter (x ∈ ·) = {s(x, y)} := by
        ext e'
        simp only [mem_filter, mem_singleton]
        exact ⟨fun h => hx e' h.1 h.2, fun h => h ▸ ⟨he, hxe⟩⟩
      simp [c, this]
    have hcy : 1 ≤ c y := by
      simp only [c]; split_ifs <;> omega
    omega
  have hvert : ∀ v, c v * (D.filter (v ∈ ·)).card ≤ d := by
    intro v
    simp only [c]
    split_ifs with h
    · rw [h, mul_one]
    · rw [one_mul]; exact hdeg v
  calc (d + 1) * D.card = ∑ _e ∈ D, (d + 1) := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ e ∈ D, ∑ v ∈ univ.filter (· ∈ e), c v := sum_le_sum hedge
    _ = ∑ v, ∑ e ∈ D.filter (v ∈ ·), c v := by
        simp only [sum_filter]
        exact sum_comm
    _ = ∑ v, c v * (D.filter (v ∈ ·)).card := by
        simp only [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ _v : V, d := sum_le_sum fun v _ => hvert v
    _ = d * Fintype.card V := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]

end Podc.EdgeDominatingSets
