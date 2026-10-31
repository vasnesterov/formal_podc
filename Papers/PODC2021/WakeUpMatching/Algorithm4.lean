import Papers.PODC2021.WakeUpMatching.Theorem63
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Algorithm 4 and Theorem 6.5 (deterministic core)

Dani, Gupta, Hayes, Pettie, PODC 2021 (arXiv:2104.09096v2), Section 6, Algorithm 4 and
Theorem 6.5.

```
1: Run our Maximal Matching algorithm on G.
2: For each edge {u,v} in the matching, mark u,v as assigned, and assign them to each other.
3: for i ← 1 to k do
4:   Run the maximal matching algorithm on G, modified so that only unassigned nodes are allowed
     to recruit, and only assigned nodes are allowed to accept.
5:   For each edge {u,v} in the matching, mark u,v as assigned, and (re-)assign them to each other.
6: end for
```

The randomised maximal matching subroutine (Algorithm 1) is a black box here: an execution is a
sequence `m 0, m 1, …, m k` of partner functions, where `m 0` is a maximal matching of `G` and
`m (j+1)` is a maximal matching of the *cross graph* `crossGraph G (assigned m j)` (edges of `G`
between an assigned and an unassigned vertex — the effect of the modification in line 4, as the
paper's proof says). Theorem 6.5's probabilistic statement is "with probability `1 − O(k/n²)`
(the probability that all `k + 1` calls succeed, by Theorem 1.1) the output has coverage … and
maximum load at most `k`". We prove what holds for **every** execution in which all calls
succeed (`IsRun`):

* the output is a partial NAF (`out_isPartialNAF`);
* its maximum load is at most `k + 1` (`theorem_6_5_load`), and **not** at most `k` as claimed:
  on `c` disjoint copies of the path `P₃` with `k = 1`, every such execution outputs load `2`
  (`theorem_6_5_load_false`, with `exists_run` showing such executions exist);
* the coverage bounds hold (`theorem_6_5_coverage`, `theorem_6_5_coverage_exp`,
  `theorem_6_5_full_coverage`), but with a repaired proof: the paper bounds the number of
  *unassigned vertices of `S ∪ R`*, which need not shrink (the maximal matchings may pick
  unassigned vertices outside `S ∪ R`); we bound the number of *assigned* vertices instead.
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The graph on which the modified maximal matching runs in line 4: edges of `G` with exactly
one assigned endpoint. -/
def crossGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∈ A ↔ v ∉ A)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

theorem crossGraph_le (A : Finset V) : crossGraph G A ≤ G := fun _ _ h => h.1

/-- Vertices assigned after call `j` (call `0` is line 1, call `j + 1` is iteration `j + 1`). -/
def assigned (m : ℕ → V → Option V) : ℕ → Finset V
  | 0 => {v | (m 0 v).isSome}
  | j + 1 => assigned m j ∪ univ.filter (fun v => (m (j + 1) v).isSome)

/-- The assignment after call `j`: a vertex matched in call `j` is (re-)assigned to its partner,
the others keep their previous assignment. Algorithm 4 with parameter `k` outputs `out m k`. -/
def out (m : ℕ → V → Option V) : ℕ → V → Option V
  | 0 => m 0
  | j + 1 => fun v => (m (j + 1) v).or (out m j v)

/-- `m` is an execution of Algorithm 4 with parameter `k` in which every call of the maximal
matching subroutine returned a maximal matching of the graph it runs on. -/
structure IsRun (G : SimpleGraph V) (k : ℕ) (m : ℕ → V → Option V) : Prop where
  first : ∃ M : PMatching G, M.p = m 0 ∧ M.IsMaximal
  step : ∀ j < k, ∃ M : PMatching (crossGraph G (assigned m j)), M.p = m (j + 1) ∧ M.IsMaximal

theorem mem_assigned {m : ℕ → V → Option V} {j : ℕ} {v : V} :
    v ∈ assigned m j ↔ (out m j v).isSome := by
  induction j with
  | zero => simp [assigned, out]
  | succ j ih =>
    simp only [assigned, out, mem_union, ih, mem_filter, mem_univ, true_and]
    cases m (j + 1) v <;> simp

theorem assigned_eq_domain (m : ℕ → V → Option V) (j : ℕ) : assigned m j = domain (out m j) := by
  ext v; simp [mem_assigned, domain]

theorem assigned_mono (m : ℕ → V → Option V) {j j' : ℕ} (h : j ≤ j') :
    assigned m j ⊆ assigned m j' := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans subset_union_left

/-- Theorem 6.5: the output of Algorithm 4 is a partial NAF. -/
theorem out_isPartialNAF {k : ℕ} {m : ℕ → V → Option V} (hrun : IsRun G k m) :
    ∀ j ≤ k, IsPartialNAF G (out m j) := by
  intro j
  induction j with
  | zero =>
    intro _ v w h
    obtain ⟨M, hM, -⟩ := hrun.first
    exact M.adj v w (hM ▸ h)
  | succ j ih =>
    intro hj v w h
    obtain ⟨M, hM, -⟩ := hrun.step j (by omega)
    simp only [out] at h
    cases hmv : m (j + 1) v with
    | none => rw [hmv] at h; exact ih (by omega) v w h
    | some w' =>
      rw [hmv] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      exact crossGraph_le _ (M.adj v w' (hM ▸ hmv))

theorem card_fiber_le_one {H : SimpleGraph V} (M : PMatching H) (w : V) :
    #({x | M.p x = some w} : Finset V) ≤ 1 :=
  card_le_one.2 fun a ha b hb => by
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact PMatching.inj ha hb

/-- Each call adds at most one vertex to the preimage of `w`, hence load `≤ j + 1` after call `j`. -/
theorem pInDeg_out_le {k : ℕ} {m : ℕ → V → Option V} (hrun : IsRun G k m) (w : V) :
    ∀ j ≤ k, pInDeg (out m j) w ≤ j + 1 := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨M, hM, -⟩ := hrun.first
    simpa [pInDeg, out, ← hM] using card_fiber_le_one M w
  | succ j ih =>
    intro hj
    obtain ⟨M, hM, -⟩ := hrun.step j (by omega)
    have hsub : ({x | out m (j + 1) x = some w} : Finset V) ⊆
        ({x | out m j x = some w} : Finset V) ∪ ({x | M.p x = some w} : Finset V) := by
      intro x hx
      have hx2 : (m (j + 1) x).or (out m j x) = some w := (mem_filter.1 hx).2
      rw [mem_union, mem_filter, mem_filter, hM]
      cases hmx : m (j + 1) x with
      | none => rw [hmx] at hx2; exact Or.inl ⟨mem_univ _, by simpa using hx2⟩
      | some y => rw [hmx] at hx2; exact Or.inr ⟨mem_univ _, by simpa using hx2⟩
    calc pInDeg (out m (j + 1)) w ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ (j + 1) + 1 := add_le_add (ih (by omega)) (card_fiber_le_one M w)

/-- Theorem 6.5, load part, **corrected**: in every execution in which all `k + 1` calls return
maximal matchings, the output has maximum load at most `k + 1`. (The paper claims `k`; see
`theorem_6_5_load_false`.) -/
theorem theorem_6_5_load {k : ℕ} {m : ℕ → V → Option V} (hrun : IsRun G k m) :
    pLoad (out m k) ≤ k + 1 :=
  pLoad_le_iff.2 fun w => pInDeg_out_le hrun w k le_rfl

/-! ### The load bound `k` is false: disjoint copies of `P₃` -/

/-- `c` disjoint copies of the path `P₃`; `(a, 1)` is the centre of copy `a`. -/
def threePaths (c : ℕ) : SimpleGraph (Fin c × Fin 3) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2 ∧ (x.2 = 1 ∨ y.2 = 1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.1 rfl⟩

theorem threePaths_adj_leaf {c : ℕ} {x y : Fin c × Fin 3} (hx : x.2 ≠ 1)
    (h : (threePaths c).Adj x y) : y = (x.1, 1) := by
  obtain ⟨h1, -, h3⟩ := h
  exact Prod.ext h1.symm (h3.resolve_left hx)

theorem threePaths_adj_center {c : ℕ} {a : Fin c} {y : Fin c × Fin 3}
    (h : (threePaths c).Adj (a, 1) y) : y.1 = a ∧ y.2 ≠ 1 :=
  ⟨h.1.symm, fun h' => h.2.1 h'.symm⟩

/-- In every successful execution on `threePaths c` with `k = 1`, both leaves of a copy end up
assigned to its centre. -/
theorem threePaths_out {c : ℕ} {m : ℕ → Fin c × Fin 3 → Option (Fin c × Fin 3)}
    (hrun : IsRun (threePaths c) 1 m) (a : Fin c) {ℓ ℓ' : Fin c × Fin 3}
    (hℓ : m 0 (a, 1) = some ℓ) (hℓ' : ℓ'.1 = a ∧ ℓ'.2 ≠ 1) (hne : ℓ ≠ ℓ') :
    out m 1 ℓ = some (a, 1) ∧ out m 1 ℓ' = some (a, 1) := by
  obtain ⟨M0, hM0, -⟩ := hrun.first
  obtain ⟨M1, hM1, hmax1⟩ := hrun.step 0 (by omega)
  have hℓl := threePaths_adj_center (M0.adj _ _ (hM0 ▸ hℓ))
  have hctr : ((a, 1) : Fin c × Fin 3) = (ℓ'.1, 1) := by rw [hℓ'.1]
  -- `ℓ'` is unmatched in the first call
  have h0ℓ' : m 0 ℓ' = none := by
    cases h : m 0 ℓ' with
    | none => rfl
    | some w =>
      exfalso
      have hw := threePaths_adj_leaf hℓ'.2 (M0.adj _ _ (hM0 ▸ h))
      have := M0.symm _ _ (hM0 ▸ h)
      rw [hw, ← hctr, hM0, hℓ] at this
      exact hne (Option.some_injective _ this)
  have h0ℓ : m 0 ℓ = some (a, 1) := hM0 ▸ M0.symm _ _ (hM0 ▸ hℓ)
  have hA_ctr : ((a, 1) : Fin c × Fin 3) ∈ assigned m 0 := by simp [assigned, hℓ]
  have hA_ℓ : ℓ ∈ assigned m 0 := by simp [assigned, h0ℓ]
  have hA_ℓ' : ℓ' ∉ assigned m 0 := by simp [assigned, h0ℓ']
  -- the second call matches the centre with `ℓ'`
  have hcross : (crossGraph (threePaths c) (assigned m 0)).Adj (a, 1) ℓ' :=
    ⟨⟨hℓ'.1.symm, fun h => hℓ'.2 h.symm, Or.inl rfl⟩, by tauto⟩
  have h1ℓ' : m 1 ℓ' = some (a, 1) := by
    rcases hmax1 _ _ hcross with h | h
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
      have hadj := M1.adj _ _ hx
      have hxl := threePaths_adj_center hadj.1
      have hxA : x ∉ assigned m 0 := hadj.2.1 hA_ctr
      have hxℓ : x ≠ ℓ := fun h => hxA (h ▸ hA_ℓ)
      have hxℓ' : x = ℓ' := by
        refine Prod.ext (hxl.1.trans hℓ'.1.symm) ?_
        have h1 : x.2 ≠ ℓ.2 := fun h => hxℓ (Prod.ext (hxl.1.trans hℓl.1.symm) h)
        have h2 : ℓ.2 ≠ ℓ'.2 := fun h => hne (Prod.ext (hℓl.1.trans hℓ'.1.symm) h)
        have := hxl.2; have := hℓl.2; have := hℓ'.2
        omega
      subst hxℓ'
      rw [← hM1]; exact M1.symm _ _ hx
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h
      have := threePaths_adj_leaf hℓ'.2 (crossGraph_le _ (M1.adj _ _ hw))
      rw [← hM1, hw, this, ← hctr]
  have h1ℓ : m 1 ℓ = none := by
    cases h : m 1 ℓ with
    | none => rfl
    | some w =>
      exfalso
      have hw := threePaths_adj_leaf hℓl.2 (crossGraph_le _ (M1.adj _ _ (hM1 ▸ h)))
      have e1 := M1.symm _ _ (hM1 ▸ h)
      have e2 := M1.symm _ _ (hM1 ▸ h1ℓ')
      rw [hw, hℓl.1] at e1
      rw [e1] at e2
      exact hne (Option.some_injective _ e2)
  simp [out, h1ℓ, h0ℓ, h1ℓ']

/-- **Theorem 6.5 is false as stated (load part).** On `c ≥ 1` disjoint copies of `P₃` (so
`n = 3c`), Algorithm 4 with parameter `k = 1` outputs a partial NAF of maximum load `2 > k` in
*every* execution in which both calls of the maximal matching subroutine succeed — an event of
probability `1 − O(1/n²)` by the paper's own Theorem 1.1. The claimed "maximum load at most `k`"
therefore holds with probability `O(1/n²)` only. -/
theorem theorem_6_5_load_false {c : ℕ} (hc : 0 < c)
    {m : ℕ → Fin c × Fin 3 → Option (Fin c × Fin 3)} (hrun : IsRun (threePaths c) 1 m) :
    pLoad (out m 1) = 2 := by
  refine le_antisymm (theorem_6_5_load hrun) ?_
  set a : Fin c := ⟨0, hc⟩
  obtain ⟨M0, hM0, hmax0⟩ := hrun.first
  -- the centre is matched in the first call
  have hctr : ∃ ℓ, m 0 (a, 1) = some ℓ := by
    rcases hmax0 (a, 1) (a, 0) ⟨rfl, by simp, Or.inl rfl⟩ with h | h
    · exact Option.isSome_iff_exists.1 (hM0 ▸ h)
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h
      have := threePaths_adj_leaf (by simp) (M0.adj _ _ hw)
      exact ⟨(a, 0), hM0 ▸ this ▸ M0.symm _ _ hw⟩
  obtain ⟨ℓ, hℓ⟩ := hctr
  have hℓl := threePaths_adj_center (M0.adj _ _ (hM0 ▸ hℓ))
  -- the other leaf
  set ℓ' : Fin c × Fin 3 := (a, if ℓ.2 = 0 then 2 else 0)
  have hℓ' : ℓ'.1 = a ∧ ℓ'.2 ≠ 1 := ⟨rfl, by simp only [ℓ']; split_ifs <;> decide⟩
  have hne : ℓ ≠ ℓ' := by
    intro h
    have h2 := congrArg Prod.snd h
    simp only [ℓ'] at h2
    split_ifs at h2 with h0
    · rw [h0] at h2; exact absurd h2 (by decide)
    · exact h0 h2
  obtain ⟨o1, o2⟩ := threePaths_out hrun a hℓ hℓ' hne
  calc 2 = #({ℓ, ℓ'} : Finset _) := (card_pair hne).symm
    _ ≤ pInDeg (out m 1) (a, 1) := card_le_card (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [o1, o2])
    _ ≤ pLoad (out m 1) := Finset.le_sup (f := pInDeg (out m 1)) (mem_univ _)

/-- The first call of the canonical execution on `threePaths c`: centres matched to leaf `0`. -/
def run0 {c : ℕ} (x : Fin c × Fin 3) : Option (Fin c × Fin 3) :=
  if x.2 = 1 then some (x.1, 0) else if x.2 = 0 then some (x.1, 1) else none

/-- The second call: centres matched to leaf `2`. -/
def run1 {c : ℕ} (x : Fin c × Fin 3) : Option (Fin c × Fin 3) :=
  if x.2 = 1 then some (x.1, 2) else if x.2 = 2 then some (x.1, 1) else none

/-- Non-vacuity of `theorem_6_5_load_false`: successful executions exist. -/
theorem exists_run (c : ℕ) :
    ∃ m : ℕ → Fin c × Fin 3 → Option (Fin c × Fin 3), IsRun (threePaths c) 1 m := by
  let m : ℕ → Fin c × Fin 3 → Option (Fin c × Fin 3) :=
    fun j => if j = 0 then run0 else if j = 1 then run1 else fun _ => none
  have hA : ∀ x : Fin c × Fin 3, x ∈ assigned m 0 ↔ x.2 ≠ 2 := by
    intro x
    simp only [assigned, m, run0, mem_filter, mem_univ, true_and, ite_true]
    obtain ⟨a, i⟩ := x
    fin_cases i <;> simp
  refine ⟨m, ⟨⟨⟨run0, ?_, ?_⟩, rfl, ?_⟩, ?_⟩⟩
  · rintro ⟨a, i⟩ w h
    fin_cases i <;> simp [run0] at h <;> subst h <;> simp [threePaths]
  · rintro ⟨a, i⟩ w h
    fin_cases i <;> simp [run0] at h <;> subst h <;> simp [run0]
  · rintro x y ⟨-, -, h | h⟩
    · left; simp [run0, h]
    · right; simp [run0, h]
  · intro j hj
    obtain rfl : j = 0 := by omega
    refine ⟨⟨run1, ?_, ?_⟩, rfl, ?_⟩
    · rintro ⟨a, i⟩ w h
      fin_cases i <;> simp [run1] at h <;> subst h <;>
        exact ⟨by simp [threePaths], by simp [hA]⟩
    · rintro ⟨a, i⟩ w h
      fin_cases i <;> simp [run1] at h <;> subst h <;> simp [run1]
    · rintro x y ⟨⟨-, -, h | h⟩, -⟩
      · left; simp [run1, h]
      · right; simp [run1, h]

/-! ### Coverage -/

/-- Lift a matching of the subgraph induced on `D` to a matching of `G`. -/
def liftMatching {D : Finset V} (N : PMatching (G.comap (Subtype.val : D → V))) :
    PMatching G where
  p v := if hv : v ∈ D then (N.p ⟨v, hv⟩).map Subtype.val else none
  adj v w h := by
    by_cases hv : v ∈ D
    · simp only [hv, dite_true, Option.map_eq_some_iff] at h
      obtain ⟨w', hw', rfl⟩ := h
      exact N.adj _ _ hw'
    · simp [hv] at h
  symm v w h := by
    by_cases hv : v ∈ D
    · simp only [hv, dite_true, Option.map_eq_some_iff] at h
      obtain ⟨w', hw', rfl⟩ := h
      simp [w'.2, N.symm _ _ hw']
    · simp [hv] at h

theorem mem_liftMatching_covered {D : Finset V} {N : PMatching (G.comap (Subtype.val : D → V))}
    {v : D} (hv : v ∈ N.covered) : v.1 ∈ (liftMatching N).covered := by
  obtain ⟨w, hw⟩ := PMatching.mem_covered.1 hv
  exact PMatching.mem_covered.2 ⟨w.1, by simp [liftMatching, v.2, hw]⟩

/-- Proof of Theorem 6.5, first step: a partial NAF of load `≤ L` (`L ≥ 1`) extends to a NAF of
load `≤ L + 1` on `S ∪ R`, so by Theorem 6.3 `L + 1` matchings cover its domain `S`. -/
theorem exists_cover_of_partialNAF {f : V → Option V} {L : ℕ} (hL : 1 ≤ L)
    (hf : IsPartialNAF G f) (hfl : pLoad f ≤ L) :
    ∃ M : Fin (L + 1) → PMatching G, ∀ v ∈ domain f, ∃ i, v ∈ (M i).covered := by
  classical
  set D : Finset V := {v | (f v).isSome ∨ ∃ x, f x = some v}
  let H := G.comap (Subtype.val : D → V)
  have hmemD : ∀ v w, f v = some w → w ∈ D := fun v w h => by simp [D]; exact Or.inr ⟨v, h⟩
  let h : D → D := fun v =>
    if hs : (f v.1).isSome then ⟨(f v.1).get hs, hmemD _ _ (Option.some_get hs).symm⟩
    else
      have hex : ∃ x, f x = some v.1 := by
        have := v.2; simp only [D, mem_filter, mem_univ, true_and] at this
        exact this.resolve_left hs
      ⟨hex.choose, by simp [D, hex.choose_spec]⟩
  have hh : IsNAF H h := by
    intro v
    change G.Adj v.1 (h v).1
    by_cases hs : (f v.1).isSome
    · simp only [h, hs, dite_true]
      exact hf _ _ (Option.some_get hs).symm
    · simp only [h, hs]
      have hex : ∃ x, f x = some v.1 := by
        have := v.2; simp only [D, mem_filter, mem_univ, true_and] at this
        exact this.resolve_left hs
      exact (hf _ _ hex.choose_spec).symm
  have hhl : ∀ w, inDeg h w ≤ L + 1 := by
    intro w
    calc inDeg h w ≤ #(({x | f x = some w.1} : Finset V) ∪ (f w.1).toFinset) := by
          refine card_le_card_of_injOn Subtype.val (fun v hv => ?_) Subtype.val_injective.injOn
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
          simp only [coe_union, coe_filter, mem_univ, true_and, Set.mem_union,
            Set.mem_ofPred_eq, mem_coe, Option.mem_toFinset, Option.mem_def]
          by_cases hs : (f v.1).isSome
          · left
            simp only [h, hs, dite_true] at hv
            rw [← hv]; exact (Option.some_get hs).symm
          · right
            simp only [h, hs] at hv
            rw [← hv]
            exact Exists.choose_spec (p := fun x => f x = some v.1) _
      _ ≤ #({x | f x = some w.1} : Finset V) + #(f w.1).toFinset := card_union_le _ _
      _ ≤ L + 1 := add_le_add ((pLoad_le_iff.1 hfl) w.1) (by cases f w.1 <;> simp)
  obtain ⟨M, hM⟩ := exists_cover_of_naf (by omega) hh hhl
  refine ⟨fun i => liftMatching (PMatching.ofSubgraph (hM.1 i)), fun v hv => ?_⟩
  have hvD : v ∈ D := by simp [D]; left; simpa [domain] using hv
  obtain ⟨i, hi⟩ := hM.2 ⟨v, hvD⟩
  exact ⟨i, mem_liftMatching_covered (v := ⟨v, hvD⟩)
    ((PMatching.ofSubgraph_covered (hM.1 i) _).2 hi)⟩

/-- Pigeonhole: one of `L + 1` matchings covering `Y` covers `≥ |Y| / (L + 1)` vertices of `Y`. -/
theorem exists_large {L : ℕ} (M : Fin (L + 1) → PMatching G) {Y : Finset V}
    (hY : ∀ v ∈ Y, ∃ i, v ∈ (M i).covered) : ∃ i, #Y ≤ (L + 1) * #(Y ∩ (M i).covered) := by
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun i => #(Y ∩ (M i).covered)) univ_nonempty
  refine ⟨i, ?_⟩
  calc #Y ≤ #(univ.biUnion fun j => Y ∩ (M j).covered) := card_le_card fun v hv => by
          obtain ⟨j, hj⟩ := hY v hv; exact mem_biUnion.2 ⟨j, mem_univ _, mem_inter.2 ⟨hv, hj⟩⟩
    _ ≤ ∑ j, #(Y ∩ (M j).covered) := card_biUnion_le
    _ ≤ ∑ _j : Fin (L + 1), #(Y ∩ (M i).covered) := sum_le_sum fun j _ => hi j (mem_univ _)
    _ = (L + 1) * #(Y ∩ (M i).covered) := by simp

/-- A maximal matching `M` of `H` versus another matching `N`: if every vertex of `X ⊆ U` has an
`N`-partner joined to it in `H`, and `M`-partners of these partners lie in `U`, then `M` covers
at least `|X| / 2` vertices of `U`. -/
theorem card_le_two_mul {H G' : SimpleGraph V} (M : PMatching H) (hM : M.IsMaximal)
    (N : PMatching G') {X U : Finset V} (hXU : X ⊆ U)
    (hX : ∀ x ∈ X, ∀ y, N.p x = some y → H.Adj x y)
    (hXc : ∀ x ∈ X, (N.p x).isSome)
    (hU : ∀ x ∈ X, ∀ y z, N.p x = some y → M.p y = some z → z ∈ U) :
    #X ≤ 2 * #(M.covered ∩ U) := by
  let φ : V → V := fun x => if (M.p x).isSome then x else ((N.p x).bind M.p).getD x
  -- for `x ∈ X` not covered by `M`, its `N`-partner `y` is covered by `M`
  have key : ∀ x ∈ X, (M.p x).isSome = false →
      ∃ y z, N.p x = some y ∧ M.p y = some z ∧ φ x = z := by
    intro x hx hxM
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hXc x hx)
    rcases hM x y (hX x hx y hy) with h | h
    · simp [hxM] at h
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 h
      exact ⟨y, z, hy, hz, by simp [φ, hxM, hy, hz]⟩
  refine card_le_mul_card_image_of_maps_to (f := φ) (fun x hx => ?_) 2 (fun z _ => ?_)
  · rw [mem_inter]
    by_cases hxM : (M.p x).isSome
    · simp only [φ, hxM, ite_true]
      exact ⟨by simpa [PMatching.covered] using hxM, hXU hx⟩
    · obtain ⟨y, z, hy, hz, hφ⟩ := key x hx (by simpa using hxM)
      rw [hφ]
      exact ⟨PMatching.mem_covered.2 ⟨y, M.symm _ _ hz⟩, hU x hx y z hy hz⟩
  · calc #({x ∈ X | φ x = z} : Finset V) ≤ #({z, ((M.p z).bind N.p).getD z} : Finset V) := by
          apply card_le_card
          intro x hx
          simp only [mem_filter] at hx
          simp only [mem_insert, mem_singleton]
          by_cases hxM : (M.p x).isSome
          · left; simpa [φ, hxM] using hx.2
          · right
            obtain ⟨y, z', hy, hz', hφ⟩ := key x hx.1 (by simpa using hxM)
            rw [hx.2] at hφ; subst hφ
            simp [M.symm _ _ hz', N.symm _ _ hy]
      _ ≤ 2 := card_le_two

/-- **Proposition 2.2** (`β(G) ≥ ν(G)/2`), in vertex form: a maximal matching `M` covers at least
half as many vertices as any matching `N` (a matching with `e` edges covers `2e` vertices). -/
theorem proposition_2_2 (M : PMatching G) (hM : M.IsMaximal) (N : PMatching G) :
    #N.covered ≤ 2 * #M.covered := by
  have := card_le_two_mul M hM N (X := N.covered) (U := univ) (subset_univ _)
    (fun x _ y hy => N.adj _ _ hy) (fun x hx => by simpa [PMatching.covered] using hx)
    (fun _ _ _ _ _ _ => mem_univ _)
  rwa [inter_univ] at this

variable {k L : ℕ} {m : ℕ → V → Option V} {f : V → Option V}

/-- First call: the maximal matching covers at least `|S| / (2L + 2)` vertices. -/
theorem first_bound (hrun : IsRun G k m) (M : Fin (L + 1) → PMatching G)
    (hM : ∀ v ∈ domain f, ∃ i, v ∈ (M i).covered) :
    #(domain f) ≤ (2 * L + 2) * #(assigned m 0) := by
  obtain ⟨M0, hM0, hmax⟩ := hrun.first
  obtain ⟨i, hi⟩ := exists_large M hM
  have h2 := card_le_two_mul M0 hmax (M i) (X := domain f ∩ (M i).covered) (U := univ)
    (subset_univ _) (fun x _ y hy => (M i).adj _ _ hy)
    (fun x hx => by simpa [PMatching.covered] using (mem_inter.1 hx).2)
    (fun _ _ _ _ _ _ => mem_univ _)
  have : M0.covered ∩ univ = assigned m 0 := by
    ext v; simp [PMatching.covered, assigned, hM0]
  rw [this] at h2
  calc #(domain f) ≤ (L + 1) * #(domain f ∩ (M i).covered) := hi
    _ ≤ (L + 1) * (2 * #(assigned m 0)) := Nat.mul_le_mul_left _ h2
    _ = (2 * L + 2) * #(assigned m 0) := by ring

/-- Iteration `j + 1`: the cross-graph maximal matching assigns at least `|S \ A_j| / (2L + 2)` new
vertices. -/
theorem step_bound (hrun : IsRun G k m) (M : Fin (L + 1) → PMatching G)
    (hM : ∀ v ∈ domain f, ∃ i, v ∈ (M i).covered) {j : ℕ} (hj : j < k) :
    #(domain f \ assigned m j) ≤
      (2 * L + 2) * #(({v | (m (j + 1) v).isSome} : Finset V) \ assigned m j) := by
  set A := assigned m j with hAdef
  obtain ⟨M0, hM0, hmax0⟩ := hrun.first
  obtain ⟨Mj, hMj, hmax⟩ := hrun.step j hj
  obtain ⟨i, hi⟩ := exists_large M (Y := domain f \ A)
    (fun v hv => hM v (mem_sdiff.1 hv).1)
  -- no edge of `G` joins two unassigned vertices
  have hA0 : ∀ x y, G.Adj x y → x ∉ A → y ∈ A := by
    intro x y hxy hx
    rcases hmax0 x y hxy with h | h
    · exact absurd (assigned_mono m (Nat.zero_le j) (by simp [assigned, ← hM0, h])) hx
    · exact assigned_mono m (Nat.zero_le j) (by simp [assigned, ← hM0, h])
  have h2 := card_le_two_mul Mj hmax (M i) (X := (domain f \ A) ∩ (M i).covered) (U := univ \ A)
    (fun x hx => by
      have := (mem_sdiff.1 (mem_inter.1 hx).1).2
      simpa using this)
    (fun x hx y hy => by
      have hxA := (mem_sdiff.1 (mem_inter.1 hx).1).2
      have hG := (M i).adj _ _ hy
      exact ⟨hG, by have := hA0 x y hG hxA; tauto⟩)
    (fun x hx => by simpa [PMatching.covered] using (mem_inter.1 hx).2)
    (fun x hx y z hy hz => by
      have hxA := (mem_sdiff.1 (mem_inter.1 hx).1).2
      have hyA := hA0 x y ((M i).adj _ _ hy) hxA
      have := (Mj.adj _ _ hz).2
      simpa using this.1 hyA)
  have : Mj.covered ∩ (univ \ A) = ({v | (m (j + 1) v).isSome} : Finset V) \ A := by
    ext v; simp only [PMatching.covered, hMj, mem_inter, mem_filter, mem_univ, true_and,
      mem_sdiff]
  rw [this] at h2
  calc #(domain f \ A) ≤ (L + 1) * #((domain f \ A) ∩ (M i).covered) := hi
    _ ≤ (L + 1) * (2 * _) := Nat.mul_le_mul_left _ h2
    _ = _ := by ring

theorem card_assigned_succ (m : ℕ → V → Option V) (j : ℕ) :
    #(assigned m (j + 1)) =
      #(assigned m j) + #(({v | (m (j + 1) v).isSome} : Finset V) \ assigned m j) := by
  rw [assigned, ← card_union_of_disjoint disjoint_sdiff, union_sdiff_self_eq_union]

/-- The geometric decay of `|S| − |assigned|`. -/
theorem coverage_aux (hrun : IsRun G k m) (hL : 1 ≤ L) (hf : IsPartialNAF G f)
    (hfl : pLoad f ≤ L) :
    ∀ j ≤ k, (#(domain f) : ℝ) - #(assigned m j) ≤
      #(domain f) * (1 - 1 / (2 * L + 2)) ^ (j + 1) := by
  obtain ⟨M, hM⟩ := exists_cover_of_partialNAF hL hf hfl
  have hpos : (0 : ℝ) < 2 * L + 2 := by positivity
  intro j
  induction j with
  | zero =>
    intro _
    have h := first_bound (L := L) hrun M hM
    have h' : (#(domain f) : ℝ) ≤ (2 * L + 2) * (#(assigned m 0) : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 h; push_cast at this; exact this
    rw [zero_add, pow_one, mul_sub, mul_one, mul_one_div]
    have : (#(domain f) : ℝ) / (2 * L + 2) ≤ #(assigned m 0) := by rw [div_le_iff₀ hpos]; linarith
    linarith
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    have hs := step_bound (L := L) hrun M hM (j := j) (by omega)
    have hc := card_assigned_succ m j
    have hsd : #(domain f) ≤ #(domain f \ assigned m j) + #(assigned m j) := by
      calc #(domain f) ≤ #((domain f \ assigned m j) ∪ assigned m j) :=
            card_le_card fun v hv => by by_cases h : v ∈ assigned m j <;> simp [h, hv]
        _ ≤ _ := card_union_le _ _
    set d : ℝ := (#(({v | (m (j + 1) v).isSome} : Finset V) \ assigned m j) : ℝ)
    have hs' : (#(domain f) : ℝ) - #(assigned m j) ≤ (2 * L + 2) * d := by
      have : (#(domain f) : ℝ) ≤ #(domain f \ assigned m j) + #(assigned m j) := by
        exact_mod_cast hsd
      have h2 : (#(domain f \ assigned m j) : ℝ) ≤ (2 * L + 2) * d := by
        have := (Nat.cast_le (α := ℝ)).2 hs; push_cast at this; exact this
      linarith
    have hc' : (#(assigned m (j + 1)) : ℝ) = #(assigned m j) + d := by
      have := congrArg (Nat.cast (R := ℝ)) hc; push_cast at this; exact this
    have hq : 0 ≤ 1 - 1 / (2 * (L : ℝ) + 2) := by
      rw [sub_nonneg, div_le_one hpos]; linarith
    have hd : ((#(domain f) : ℝ) - #(assigned m j)) / (2 * L + 2) ≤ d := by rw [div_le_iff₀ hpos]; linarith
    calc (#(domain f) : ℝ) - #(assigned m (j + 1)) = ((#(domain f) : ℝ) - #(assigned m j)) - d := by rw [hc']; ring
      _ ≤ ((#(domain f) : ℝ) - #(assigned m j)) * (1 - 1 / (2 * L + 2)) := by
          have : ((#(domain f) : ℝ) - #(assigned m j)) * (1 - 1 / (2 * L + 2)) =
              ((#(domain f) : ℝ) - #(assigned m j)) - ((#(domain f) : ℝ) - #(assigned m j)) / (2 * L + 2) := by ring
          linarith
      _ ≤ (#(domain f) : ℝ) * (1 - 1 / (2 * L + 2)) ^ (j + 1) * (1 - 1 / (2 * L + 2)) :=
          mul_le_mul_of_nonneg_right ih hq
      _ = (#(domain f) : ℝ) * (1 - 1 / (2 * L + 2)) ^ (j + 1 + 1) := by ring

theorem domain_eq_empty_of_pLoad_zero (hfl : pLoad f ≤ 0) : domain f = ∅ := by
  ext v
  simp only [domain, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro hv
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hv
  have := (pLoad_le_iff.1 hfl) w
  have : 0 < pInDeg f w := card_pos.2 ⟨v, by simp [hw]⟩
  omega

/-- **Theorem 6.5, coverage** (deterministic core, sharp form): if `G` has a partial NAF `f` of
maximum load `L`, then in every execution of Algorithm 4 with parameter `k` in which all calls
return maximal matchings, the output assigns at least `|S| (1 − (1 − 1/(2L+2))^(k+1))` vertices,
`S` the domain of `f` (`|S| = (1 − ε) n`). -/
theorem theorem_6_5_coverage (hrun : IsRun G k m) (hf : IsPartialNAF G f) (hfl : pLoad f ≤ L) :
    (#(domain f) : ℝ) * (1 - (1 - 1 / (2 * L + 2)) ^ (k + 1)) ≤ #(domain (out m k)) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · rw [domain_eq_empty_of_pLoad_zero hfl]; simp
  · have := coverage_aux hrun hL hf hfl k le_rfl
    rw [← assigned_eq_domain]
    linarith

/-- **Theorem 6.5, coverage** in the paper's form: coverage at least
`(1 − ε)(1 − e^{−k/(2L+2)})`, i.e. at least `|S| (1 − e^{−k/(2L+2)})` assigned vertices. -/
theorem theorem_6_5_coverage_exp (hrun : IsRun G k m) (hf : IsPartialNAF G f)
    (hfl : pLoad f ≤ L) :
    (#(domain f) : ℝ) * (1 - Real.exp (-(k / (2 * L + 2)))) ≤ #(domain (out m k)) := by
  refine le_trans ?_ (theorem_6_5_coverage hrun hf hfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpos : (0 : ℝ) < 2 * L + 2 := by positivity
  have hq0 : 0 ≤ 1 - 1 / (2 * (L : ℝ) + 2) := by
    rw [sub_nonneg, div_le_one hpos]; linarith
  have hq1 : 1 - 1 / (2 * (L : ℝ) + 2) ≤ 1 := by
    have : 0 ≤ 1 / (2 * (L : ℝ) + 2) := by positivity
    linarith
  have hexp : 1 - 1 / (2 * (L : ℝ) + 2) ≤ Real.exp (-(1 / (2 * L + 2))) := by
    have := Real.add_one_le_exp (-(1 / (2 * (L : ℝ) + 2))); linarith
  have : (1 - 1 / (2 * (L : ℝ) + 2)) ^ (k + 1) ≤ Real.exp (-(k / (2 * L + 2))) := by
    calc (1 - 1 / (2 * (L : ℝ) + 2)) ^ (k + 1) ≤ (1 - 1 / (2 * (L : ℝ) + 2)) ^ k :=
          pow_le_pow_of_le_one hq0 hq1 (Nat.le_succ k)
      _ ≤ Real.exp (-(1 / (2 * L + 2))) ^ k := pow_le_pow_left₀ hq0 hexp k
      _ = Real.exp (-(k / (2 * L + 2))) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  linarith

/-- **Theorem 6.5, "in particular"**: if `k ≥ (2L + 2) ln n` for some `n ≥ |V|`, the output covers
at least as many vertices as the partial NAF `f` (coverage `≥ 1 − ε`). -/
theorem theorem_6_5_full_coverage (hrun : IsRun G k m) (hf : IsPartialNAF G f)
    (hfl : pLoad f ≤ L) {n : ℕ} (hn : Fintype.card V ≤ n)
    (hk : (2 * L + 2) * Real.log n ≤ k) : #(domain f) ≤ #(domain (out m k)) := by
  rcases Nat.eq_zero_or_pos #(domain f) with h0 | hN
  · rw [h0]; exact Nat.zero_le _
  have hpos : (0 : ℝ) < 2 * L + 2 := by positivity
  have hnpos : (0 : ℝ) < n := by
    have : 0 < Fintype.card V := (card_pos.1 hN).card_pos.trans_le (card_le_univ _)
    exact_mod_cast this.trans_le hn
  have hNn : (#(domain f) : ℝ) ≤ n := by exact_mod_cast (card_le_univ _).trans hn
  have h := theorem_6_5_coverage hrun hf hfl
  set q : ℝ := 1 / (2 * L + 2)
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [div_le_one hpos]; linarith
  -- `(1 - q)^(k+1) < e^{-q k} ≤ 1/n`
  have hlt : 1 - q < Real.exp (-q) := by
    have := Real.add_one_lt_exp (x := -q) (by linarith); linarith
  have hpow : (1 - q) ^ (k + 1) < 1 / n := by
    calc (1 - q) ^ (k + 1) < Real.exp (-q) ^ (k + 1) :=
          pow_lt_pow_left₀ hlt (by linarith) (Nat.succ_ne_zero k)
      _ ≤ Real.exp (-q) ^ k := by
          have : Real.exp (-q) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          exact pow_le_pow_of_le_one (by positivity) this (Nat.le_succ k)
      _ = Real.exp (-(q * k)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (-Real.log n) := by
          apply Real.exp_le_exp.2
          have : Real.log n ≤ q * k := by
            rw [show q * k = k / (2 * L + 2) by simp [q]; ring, le_div_iff₀ hpos]; linarith
          linarith
      _ = 1 / n := by rw [Real.exp_neg, Real.exp_log hnpos, one_div]
  have hN' : (0 : ℝ) < #(domain f) := by exact_mod_cast hN
  have : (#(domain f) : ℝ) - 1 < #(domain (out m k)) := by
    have h1 : (#(domain f) : ℝ) * (1 - q) ^ (k + 1) < 1 := by
      calc (#(domain f) : ℝ) * (1 - q) ^ (k + 1) < #(domain f) * (1 / n) :=
            mul_lt_mul_of_pos_left hpow hN'
        _ ≤ 1 := by rw [mul_one_div, div_le_one hnpos]; exact hNn
    nlinarith
  have : (#(domain f) : ℝ) < #(domain (out m k)) + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)

end Podc.WakeUpMatching
