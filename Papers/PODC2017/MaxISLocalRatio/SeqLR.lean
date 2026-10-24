import Papers.PODC2017.MaxISLocalRatio.Lemma22

/-!
# Algorithm 1: sequential local-ratio meta-algorithm `SeqLR`

```
SeqLR(V, E, w):
 1  if V = ∅ then return ∅
 3  remove every v with w(v) ≤ 0
 7  let U ⊆ V be an independent set
 8  w₁ = w;  for u ∈ U, v ∈ N[u]: w₁(v) = w₁(v) - w(u)
12  R = SeqLR(V, E, w₁)
13  U = U \ ⋃_{v ∈ R} N(v)
14  return R ∪ U
```

We keep the graph fixed and let the current vertex set be `pos w` (the vertices of positive
weight): weights only decrease, so a vertex removed in line 5 never comes back, and the reductions
applied to removed vertices are irrelevant. The choice of `U` (line 7) is an arbitrary
*rule* (`Rule G`): any function of the current weights returning an independent set of
positive-weight vertices, nonempty whenever `pos w` is (otherwise `SeqLR` does not terminate; the
paper leaves this implicit). The paper's two distributed algorithms are instances: Algorithm 3
picks the local colour maxima (`Coloring.lean`).

Main results:
* `seqLR_isApprox` — for every rule, `SeqLR` returns an `r`-approximate maximum-weight independent
  set whenever every picked `U` satisfies the local bound `r` (Lemma 2.2 + induction).
* `algorithm_1` — the `Δ`-approximation (`Δ ≥ 1` an upper bound on the degrees).
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An admissible choice of the independent set `U` in line 7 of Algorithm 1, as a function of the
current weights. -/
structure Rule where
  /-- The independent set chosen for the current weights. -/
  pick : (V → ℝ) → Finset V
  /-- `U` consists of current (positive-weight) vertices. -/
  pick_subset : ∀ w, pick w ⊆ pos w
  /-- `U` is independent. -/
  pick_indep : ∀ w, G.IsIndepSet (pick w : Set V)
  /-- `U` is nonempty as long as some vertex is left (needed for termination). -/
  pick_nonempty : ∀ w, (pos w).Nonempty → (pick w).Nonempty

variable {G}

/-- The reduced weights `w₁ = w - w₂` of one step (lines 8–11). -/
def Rule.next (R : Rule G) (w : V → ℝ) : V → ℝ := w - red G (R.pick w) w

theorem Rule.pick_nonneg (R : Rule G) (w : V → ℝ) : ∀ u ∈ R.pick w, 0 ≤ w u :=
  fun _ hu => (mem_pos.1 (R.pick_subset w hu)).le

theorem Rule.next_le (R : Rule G) (w : V → ℝ) (v : V) : R.next w v ≤ w v := by
  simp only [Rule.next, Pi.sub_apply, sub_le_self_iff]
  exact red_nonneg (R.pick_nonneg w) v

theorem Rule.next_pick (R : Rule G) (w : V → ℝ) {u : V} (hu : u ∈ R.pick w) : R.next w u = 0 := by
  simp [Rule.next, red_of_mem (R.pick_indep w) w hu]

/-- The surviving vertices after one step: `pos w₁ ⊆ pos w \ U`. -/
theorem Rule.pos_next_subset (R : Rule G) (w : V → ℝ) : pos (R.next w) ⊆ pos w \ R.pick w := by
  intro v hv
  rw [mem_pos] at hv
  refine mem_sdiff.2 ⟨mem_pos.2 (hv.trans_le (R.next_le w v)), fun hu => ?_⟩
  rw [R.next_pick w hu] at hv
  exact lt_irrefl _ hv

theorem Rule.card_pos_next_lt (R : Rule G) {w : V → ℝ} (h : (pos w).Nonempty) :
    #(pos (R.next w)) < #(pos w) := by
  refine (card_le_card (R.pos_next_subset w)).trans_lt ?_
  rw [card_sdiff_of_subset (R.pick_subset w)]
  have := (R.pick_nonempty w h).card_pos
  have := card_le_card (R.pick_subset w)
  omega

set_option linter.unusedVariables false in
/-- **Algorithm 1** (`SeqLR`) with the choice rule `R`. -/
noncomputable def seqLR (R : Rule G) (w : V → ℝ) : Finset V :=
  if h : (pos w).Nonempty then extend G (R.pick w) (seqLR R (R.next w)) else ∅
termination_by #(pos w)
decreasing_by exact R.card_pos_next_lt h

theorem seqLR_of_nonempty (R : Rule G) {w : V → ℝ} (h : (pos w).Nonempty) :
    seqLR R w = extend G (R.pick w) (seqLR R (R.next w)) := by
  rw [seqLR, dite_eq_left h]

theorem seqLR_of_not_nonempty (R : Rule G) {w : V → ℝ} (h : ¬ (pos w).Nonempty) :
    seqLR R w = ∅ := by
  rw [seqLR, dite_eq_right h]

/-- The output consists of positive-weight vertices. -/
theorem seqLR_subset_pos (R : Rule G) (w : V → ℝ) : seqLR R w ⊆ pos w := by
  induction h : #(pos w) using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hne : (pos w).Nonempty
    · rw [seqLR_of_nonempty R hne]
      refine extend_subset.trans (union_subset ?_ (R.pick_subset w))
      exact (ih _ (h ▸ R.card_pos_next_lt hne) _ rfl).trans
        ((R.pos_next_subset w).trans sdiff_subset)
    · rw [seqLR_of_not_nonempty R hne]; exact empty_subset _

/-- **Correctness of Algorithm 1** (Lemma 2.2 + induction + Theorem 2.1): if every set `U` the rule
can pick satisfies the local independence bound `r ≥ 0`, then `SeqLR` returns an `r`-approximate
maximum-weight independent set. -/
theorem seqLR_isApprox (R : Rule G) {r : ℝ} (hr : 0 ≤ r)
    (hloc : ∀ w, LocalBound G (R.pick w) r) (w : V → ℝ) : IsApprox G r w (seqLR R w) := by
  induction h : #(pos w) using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hne : (pos w).Nonempty
    · rw [seqLR_of_nonempty R hne]
      exact lemma_2_2_total (R.pick_indep w) (R.pick_nonneg w) hr (hloc w)
        (ih _ (h ▸ R.card_pos_next_lt hne) _ rfl)
    · rw [seqLR_of_not_nonempty R hne]
      refine ⟨by simp, fun T _ => ?_⟩
      have : ∀ v, w v ≤ 0 := fun v => not_lt.1 fun hv => hne ⟨v, mem_pos.2 hv⟩
      simp only [wt, sum_empty, mul_zero]
      exact sum_nonpos fun v _ => this v

/-- **Algorithm 1 is a `Δ`-approximation** for maximum-weight independent set, for every admissible
choice of the independent sets `U`, whenever `Δ ≥ 1` bounds all degrees. -/
theorem algorithm_1 (R : Rule G) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (h1 : 1 ≤ Δ) (w : V → ℝ) :
    IsApprox G Δ w (seqLR R w) :=
  seqLR_isApprox R (Nat.cast_nonneg Δ) (fun _ => localBound_of_degree_le hΔ h1 _) w

/-! ### The iterations of Algorithm 1

The `i`-th recursive call of `SeqLR` sees the weights `wᵢ = next^[i] w` and picks `Uᵢ`. We
characterize the output level by level; this is what the distributed implementations need. -/

/-- The weights `wᵢ` seen by the `i`-th recursive call. -/
def Rule.iter (R : Rule G) (w : V → ℝ) (i : ℕ) : V → ℝ := R.next^[i] w

/-- The independent set `Uᵢ` picked by the `i`-th recursive call (empty once no vertex is left). -/
def Rule.U (R : Rule G) (w : V → ℝ) (i : ℕ) : Finset V := R.pick (R.iter w i)

@[simp] theorem Rule.iter_zero (R : Rule G) (w : V → ℝ) : R.iter w 0 = w := rfl

theorem Rule.iter_succ (R : Rule G) (w : V → ℝ) (i : ℕ) :
    R.iter w (i + 1) = R.next (R.iter w i) := Function.iterate_succ_apply' _ _ _

theorem Rule.iter_succ' (R : Rule G) (w : V → ℝ) (i : ℕ) :
    R.iter w (i + 1) = R.iter (R.next w) i := Function.iterate_succ_apply _ _ _

theorem Rule.U_succ' (R : Rule G) (w : V → ℝ) (i : ℕ) : R.U w (i + 1) = R.U (R.next w) i := by
  simp [Rule.U, Rule.iter_succ']

theorem Rule.iter_anti (R : Rule G) (w : V → ℝ) {i j : ℕ} (hij : i ≤ j) (v : V) :
    R.iter w j v ≤ R.iter w i v := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => rw [Rule.iter_succ]; exact (R.next_le _ v).trans ih

theorem Rule.U_subset_pos (R : Rule G) (w : V → ℝ) (i : ℕ) : R.U w i ⊆ pos (R.iter w i) :=
  R.pick_subset _

theorem Rule.iter_succ_of_mem_U (R : Rule G) (w : V → ℝ) {i : ℕ} {v : V} (hv : v ∈ R.U w i) :
    R.iter w (i + 1) v = 0 := by
  rw [Rule.iter_succ]; exact R.next_pick _ hv

/-- A vertex is picked at most once. -/
theorem Rule.U_inj (R : Rule G) (w : V → ℝ) {i j : ℕ} {v : V} (hi : v ∈ R.U w i)
    (hj : v ∈ R.U w j) : i = j := by
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hj hi (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have h1 := R.iter_succ_of_mem_U w hi
  have h2 := mem_pos.1 (R.U_subset_pos w j hj)
  have h3 := R.iter_anti w (Nat.succ_le_of_lt hlt) v
  linarith

/-- Every output vertex was picked at some iteration. -/
theorem seqLR_subset_U (R : Rule G) (w : V → ℝ) {v : V} (hv : v ∈ seqLR R w) :
    ∃ j, v ∈ R.U w j := by
  induction h : #(pos w) using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hne : (pos w).Nonempty
    · rw [seqLR_of_nonempty R hne] at hv
      rcases mem_union.1 (extend_subset hv) with hv | hv
      · obtain ⟨j, hj⟩ := ih _ (h ▸ R.card_pos_next_lt hne) _ hv rfl
        exact ⟨j + 1, by rwa [Rule.U_succ']⟩
      · exact ⟨0, hv⟩
    · rw [seqLR_of_not_nonempty R hne] at hv; simp at hv

/-- One level of the recursion, valid at every iteration (also after termination). -/
theorem seqLR_iter (R : Rule G) (w : V → ℝ) (i : ℕ) :
    seqLR R (R.iter w i) = extend G (R.U w i) (seqLR R (R.iter w (i + 1))) := by
  by_cases hne : (pos (R.iter w i)).Nonempty
  · rw [seqLR_of_nonempty R hne, Rule.iter_succ]; rfl
  · have hU : R.U w i = ∅ := subset_empty.1 <| (R.U_subset_pos w i).trans
      (not_nonempty_iff_eq_empty.1 hne).le
    have hne' : ¬ (pos (R.iter w (i + 1))).Nonempty := fun ⟨v, hv⟩ =>
      hne ⟨v, mem_pos.2 ((mem_pos.1 hv).trans_le (R.iter_anti w (Nat.le_succ i) v))⟩
    rw [seqLR_of_not_nonempty R hne, seqLR_of_not_nonempty R hne', hU]
    simp [extend]

theorem Rule.iter_iter (R : Rule G) (w : V → ℝ) (i j : ℕ) :
    R.iter (R.iter w i) j = R.iter w (j + i) :=
  (Function.iterate_add_apply _ _ _ _).symm

/-- The output of the `i`-th recursive call is the part of the final output picked at levels
`≥ i`. -/
theorem mem_seqLR_iter (R : Rule G) (w : V → ℝ) (i : ℕ) {v : V} :
    v ∈ seqLR R (R.iter w i) ↔ v ∈ seqLR R w ∧ ∃ j, i ≤ j ∧ v ∈ R.U w j := by
  induction i generalizing v with
  | zero =>
    simp only [Rule.iter_zero, zero_le, true_and, iff_self_and]
    exact seqLR_subset_U R w
  | succ i ih =>
    have hsub : ∀ v ∈ seqLR R (R.iter w (i + 1)), ∃ j, i + 1 ≤ j ∧ v ∈ R.U w j := by
      intro v hv
      obtain ⟨j, hj⟩ := seqLR_subset_U R _ hv
      refine ⟨j + (i + 1), by omega, ?_⟩
      rwa [Rule.U, Rule.iter_iter] at hj
    constructor
    · intro hv
      exact ⟨(ih.1 (by rw [seqLR_iter]; exact subset_extend _ _ hv)).1, hsub v hv⟩
    · rintro ⟨hv, j, hj, hvj⟩
      have := ih.2 ⟨hv, j, by omega, hvj⟩
      rw [seqLR_iter] at this
      rcases mem_union.1 (extend_subset this) with hv | hv
      · exact hv
      · exact absurd (R.U_inj w hv hvj) (by omega)

/-- **Level characterization of the output.** A vertex picked at level `i` is in the output of
`SeqLR` iff none of its neighbours picked at a later level is in the output. -/
theorem mem_seqLR_iff (R : Rule G) (w : V → ℝ) {i : ℕ} {v : V} (hv : v ∈ R.U w i) :
    v ∈ seqLR R w ↔ ∀ u ∈ seqLR R w, (∃ j, i < j ∧ u ∈ R.U w j) → ¬ G.Adj v u := by
  have h1 : v ∈ seqLR R w ↔ v ∈ seqLR R (R.iter w i) := by
    rw [mem_seqLR_iter]
    exact ⟨fun h => ⟨h, i, le_rfl, hv⟩, fun h => h.1⟩
  rw [h1, seqLR_iter]
  simp only [extend, mem_union, mem_filter, mem_seqLR_iter]
  constructor
  · rintro (⟨-, j, hj, hvj⟩ | ⟨-, h⟩)
    · exact absurd (R.U_inj w hv hvj) (by omega)
    · rintro u hu ⟨j, hj, huj⟩
      exact h u ⟨hu, j, hj, huj⟩
  · intro h
    exact Or.inr ⟨hv, fun u ⟨hu, j, hj, huj⟩ => h u hu ⟨j, hj, huj⟩⟩

/-- If no vertex is left after `k` iterations, nothing is picked from level `k` on. -/
theorem Rule.U_eq_empty_of_le (R : Rule G) (w : V → ℝ) {k i : ℕ} (hk : pos (R.iter w k) = ∅)
    (hki : k ≤ i) : R.U w i = ∅ := by
  refine subset_empty.1 ((R.U_subset_pos w i).trans fun v hv => ?_)
  rw [← hk]
  exact mem_pos.2 ((mem_pos.1 hv).trans_le (R.iter_anti w hki v))

variable (G)

/-- The classical sequential local-ratio rule: `U` = one positive-weight vertex. Shows that `Rule G`
is inhabited for every graph (non-vacuity of `algorithm_1`). -/
noncomputable def singletonRule : Rule G where
  pick w := if h : (pos w).Nonempty then {h.choose} else ∅
  pick_subset w := by
    split_ifs with h
    · exact singleton_subset_iff.2 h.choose_spec
    · exact empty_subset _
  pick_indep w := by
    split_ifs
    · simp
    · simp
  pick_nonempty w h := by simp [h]

end Podc.MaxISLocalRatio
