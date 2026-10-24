import Papers.PODC2010.ArbdefectiveColoring.Extension
import Papers.PODC2010.ArbdefectiveColoring.LocalTools
import Cslib.Computability.Distributed.Local.Identifiers

/-!
# Colouring along an acyclic orientation: Procedure Simple-Arbdefective (Theorem 3.2)

A vertex waits until all its parents have selected their colours, then selects a colour by a
`rule` from the numbers `cnt j` of parents with colour `j`, and broadcasts it. We implement this
in CSLib's synchronous round model `Cslib.LocallyIterative.Algorithm` (a vertex sees its own state
and the set of its neighbours' states). A state stores the identifier of its vertex, its parent set
(the input orientation) and the selected colour (`none` before the selection). Vertices without
parents select in round `0` without communication (as in the paper).

* `orientRun_spec`: on an orientation with a height function bounded by `ℓ`, after `ℓ` rounds every
  vertex has selected, and the selected colours satisfy `c v = rule (cnt_v)`.
* `orientRun_isLocal`: the procedure is an `ℓ`-round LOCAL algorithm (for all inputs).
* `simpleArbdefective` (**Theorem 3.2**): with the rule "a colour `< k` used by the minimum number
  of parents", on an acyclic partial orientation of length `ℓ`, out-degree `≤ m` and deficit `≤ τ`
  the procedure computes a `(τ + ⌊m/k⌋)`-arbdefective `k`-colouring in `ℓ` rounds.
* `greedyAlongOrientation`: with the rule "the least colour not used by a parent", on a complete
  acyclic orientation of length `ℓ` and out-degree `≤ m` it computes a legal `(m+1)`-colouring in
  `ℓ` rounds (the last step of Lemma 2.2(1) / Lemma 3.3).
-/

open Finset Cslib.Local Cslib.LocallyIterative

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- The state of a vertex during the procedure. -/
structure OState (V : Type*) where
  /-- The identifier of the vertex. -/
  id : V
  /-- Its parents (the input orientation). -/
  par : Finset V
  /-- Its colour, once selected. -/
  col : Option ℕ

/-- The number of parents of `s` with colour `j` among the neighbour states `N`. -/
noncomputable def cntOf (s : OState V) (N : Set (OState V)) (j : ℕ) : ℕ :=
  {y ∈ N | y.id ∈ s.par ∧ y.col = some j}.ncard

/-- All parents of `s` have selected a colour. -/
def Ready (s : OState V) (N : Set (OState V)) : Prop :=
  ∀ u ∈ s.par, ∃ y ∈ N, y.id = u ∧ y.col.isSome

/-- One round: an undecided vertex whose parents have all decided selects `rule cnt`. -/
noncomputable def orientStep (rule : (ℕ → ℕ) → ℕ) (s : OState V) (N : Set (OState V)) :
    OState V :=
  if s.col = none ∧ Ready s N then { s with col := some (rule (cntOf s N)) } else s

/-- The procedure as a locally-iterative algorithm. -/
noncomputable def orientAlg (rule : (ℕ → ℕ) → ℕ) : Algorithm (OState V) :=
  Algorithm.ofStep (orientStep rule)

/-- The initial state: vertices without parents select immediately. -/
noncomputable def orientInit (rule : (ℕ → ℕ) → ℕ) (v : V) (p : Finset V) : OState V :=
  orientStep rule ⟨v, p, none⟩ ∅

/-- The configuration after `t` rounds, on input orientation `par`. -/
noncomputable def orientCfg (rule : (ℕ → ℕ) → ℕ) (G : SimpleGraph V) (par : V → Finset V)
    (t : ℕ) : V → OState V :=
  (orientAlg rule).run G (fun v => orientInit rule v (par v)) t

/-- The output after `ℓ` rounds (`0` for a vertex that has not decided). -/
noncomputable def orientRun (rule : (ℕ → ℕ) → ℕ) (ℓ : ℕ) (G : SimpleGraph V)
    (par : V → Finset V) (v : V) : ℕ :=
  ((orientCfg rule G par ℓ) v).col.getD 0

/-- The procedure runs in `ℓ` rounds (for every graph and every input). -/
theorem orientRun_isLocal (rule : (ℕ → ℕ) → ℕ) (ℓ : ℕ) :
    IsLocal (V := V) ℓ (fun G par v => orientRun rule ℓ G par v) := by
  have h := ((orientAlg (V := V) rule).run_isLocal ℓ).comp
    (isLocal_self (V := V) (fun v (p : Finset V) => orientInit rule v p))
  have h2 := IsLocal.map h (fun s : OState V => s.col.getD 0)
  simpa [orientRun, orientCfg] using h2

section Run

variable {G : SimpleGraph V} {par : V → Finset V} (rule : (ℕ → ℕ) → ℕ)

lemma orientCfg_succ (t : ℕ) (v : V) :
    orientCfg rule G par (t + 1) v =
      orientStep rule (orientCfg rule G par t v) (nbrColors G (orientCfg rule G par t) v) := rfl

lemma orientStep_id (s : OState V) (N) : (orientStep rule s N).id = s.id := by
  unfold orientStep; split_ifs <;> rfl

lemma orientStep_par (s : OState V) (N) : (orientStep rule s N).par = s.par := by
  unfold orientStep; split_ifs <;> rfl

lemma orientStep_col_of_some (s : OState V) (N) {j : ℕ} (h : s.col = some j) :
    (orientStep rule s N).col = some j := by
  unfold orientStep; split_ifs with h' <;> simp_all

lemma orientCfg_id (t : ℕ) (v : V) : (orientCfg rule G par t v).id = v := by
  induction t with
  | zero => simp [orientCfg, orientInit, orientStep_id]
  | succ t ih => rw [orientCfg_succ, orientStep_id, ih]

lemma orientCfg_par (t : ℕ) (v : V) : (orientCfg rule G par t v).par = par v := by
  induction t with
  | zero => simp [orientCfg, orientInit, orientStep_par]
  | succ t ih => rw [orientCfg_succ, orientStep_par, ih]

lemma orientCfg_col_mono {t : ℕ} {v : V} {j : ℕ} (h : (orientCfg rule G par t v).col = some j)
    {t' : ℕ} (ht : t ≤ t') : (orientCfg rule G par t' v).col = some j := by
  induction ht with
  | refl => exact h
  | step _ ih => rw [orientCfg_succ]; exact orientStep_col_of_some rule _ _ ih

variable (hP : IsPartialOrientation G par)
include hP

lemma cntOf_orientCfg (t : ℕ) (v : V) (j : ℕ) :
    cntOf (orientCfg rule G par t v) (nbrColors G (orientCfg rule G par t) v) j =
      #{u ∈ par v | (orientCfg rule G par t u).col = some j} := by
  rw [cntOf, orientCfg_par]
  have := ncard_nbrColors_filter (G := G) (c := orientCfg rule G par t) (v := v) OState.id
    (orientCfg_id rule t) (par v) (hP.1 v) (fun y => y.col = some j)
  convert this using 3

lemma ready_orientCfg (t : ℕ) (v : V) :
    Ready (orientCfg rule G par t v) (nbrColors G (orientCfg rule G par t) v) ↔
      ∀ u ∈ par v, (orientCfg rule G par t u).col.isSome := by
  rw [Ready, orientCfg_par]
  refine forall₂_congr fun u hu => ?_
  rw [exists_mem_nbrColors_id OState.id (orientCfg_id rule t)]
  exact ⟨fun h => h.2, fun h => ⟨hP.1 v u hu, h⟩⟩

/-- The invariant: a vertex that has selected a colour `j` did so after all its parents, and
`j = rule cnt`, where `cnt` counts the colours of its parents. -/
lemma orientCfg_inv (t : ℕ) (v : V) (j : ℕ) (h : (orientCfg rule G par t v).col = some j) :
    (∀ u ∈ par v, (orientCfg rule G par t u).col.isSome) ∧
      j = rule (fun i => #{u ∈ par v | (orientCfg rule G par t u).col = some i}) := by
  induction t generalizing v j with
  | zero =>
    have hpar : par v = ∅ := by
      by_contra hne
      obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.2 hne
      simp only [orientCfg, Algorithm.run_zero, orientInit, orientStep, Ready,
        Set.mem_empty_iff_false, false_and, exists_false, imp_false] at h
      split_ifs at h with hc
      exact hc.2 u hu
    simp only [orientCfg, Algorithm.run_zero, orientInit, orientStep, Ready, hpar,
      notMem_empty, IsEmpty.forall_iff, implies_true, and_self, ↓reduceIte, Option.some.injEq,
      filter_empty, card_empty] at h ⊢
    refine ⟨trivial, ?_⟩
    rw [← h]
    congr 1
    funext i
    simp [cntOf]
  | succ t ih =>
    -- parents' colours do not change between `t` and `t+1` once set
    have hstable : ∀ u, (orientCfg rule G par t u).col.isSome →
        (orientCfg rule G par (t + 1) u).col = (orientCfg rule G par t u).col := by
      intro u hu
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hu
      rw [hi]; exact orientCfg_col_mono rule hi (Nat.le_succ t)
    have hcnt : ∀ (w : V), (∀ u ∈ par w, (orientCfg rule G par t u).col.isSome) →
        ∀ i, #{u ∈ par w | (orientCfg rule G par (t + 1) u).col = some i} =
          #{u ∈ par w | (orientCfg rule G par t u).col = some i} := by
      intro w hw i
      congr 1
      exact filter_congr fun u hu => by rw [hstable u (hw u hu)]
    rcases hcol : (orientCfg rule G par t v).col with _ | j'
    · -- `v` selects in round `t + 1`
      rw [orientCfg_succ] at h
      unfold orientStep at h
      split_ifs at h with hc
      · simp only [Option.some.injEq] at h
        have hr := (ready_orientCfg rule hP t v).1 hc.2
        refine ⟨fun u hu => ?_, ?_⟩
        · rw [hstable u (hr u hu)]; exact hr u hu
        · rw [← h]
          congr 1
          funext i
          rw [hcnt v hr i, cntOf_orientCfg rule hP]
      · exact absurd h (by simp [hcol])
    · have hj : j' = j := by
        have := orientCfg_col_mono rule hcol (Nat.le_succ t)
        rw [this] at h; exact Option.some.inj h
      subst hj
      obtain ⟨hpar, hrule⟩ := ih v j' hcol
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [hstable u (hpar u hu)]; exact hpar u hu
      · rw [hrule]
        congr 1
        funext i
        rw [hcnt v hpar i]

/-- Progress: after `t` rounds, every vertex of height `≤ t` has selected. -/
lemma orientCfg_isSome {h : V → ℕ} (hh : ∀ v u, u ∈ par v → h u < h v) (t : ℕ) (v : V)
    (hv : h v ≤ t) : (orientCfg rule G par t v).col.isSome := by
  induction t generalizing v with
  | zero =>
    have hpar : par v = ∅ := by
      by_contra hne
      obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.2 hne
      have := hh v u hu
      omega
    simp [orientCfg, orientInit, orientStep, Ready, hpar]
  | succ t ih =>
    rw [orientCfg_succ]
    rcases hcol : (orientCfg rule G par t v).col with _ | j
    · have hr : Ready (orientCfg rule G par t v) (nbrColors G (orientCfg rule G par t) v) :=
        (ready_orientCfg rule hP t v).2 fun u hu => ih u (by have := hh v u hu; omega)
      simp [orientStep, hcol, hr]
    · simp [orientStep_col_of_some rule _ _ hcol]

/-- **Correctness of the procedure.** On an orientation with a height function bounded by `ℓ`,
after `ℓ` rounds every vertex `v` has selected the colour `rule cnt_v`, where `cnt_v j` is the
number of parents of `v` of colour `j`. -/
theorem orientRun_spec {h : V → ℕ} {ℓ : ℕ} (hh : ∀ v u, u ∈ par v → h u < h v)
    (hle : ∀ v, h v ≤ ℓ) (v : V) :
    orientRun rule ℓ G par v = rule (fun j => #{u ∈ par v | orientRun rule ℓ G par u = j}) := by
  have hsome : ∀ w, (orientCfg rule G par ℓ w).col.isSome :=
    fun w => orientCfg_isSome rule hP hh ℓ w (hle w)
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (hsome v)
  obtain ⟨-, hrule⟩ := orientCfg_inv rule hP ℓ v j hj
  have hval : ∀ w, (orientCfg rule G par ℓ w).col = some (orientRun rule ℓ G par w) := by
    intro w
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (hsome w)
    simp [orientRun, hi]
  simp only [orientRun, hj, Option.getD_some]
  rw [hrule]
  congr 1
  funext i
  congr 1
  exact filter_congr fun u _ => by rw [hval u, Option.some.injEq]; rfl

end Run

/-! ### Procedure Simple-Arbdefective -/

/-- The least colour `< k` minimizing `cnt` (the colour "used by the minimum number of parents";
`0` if `k = 0`). -/
noncomputable def argminRule (k : ℕ) (cnt : ℕ → ℕ) : ℕ :=
  if h : (range k).Nonempty then Classical.choose ((range k).exists_min_image cnt h) else 0

lemma argminRule_lt {k : ℕ} (hk : 0 < k) (cnt : ℕ → ℕ) : argminRule k cnt < k := by
  have h : (range k).Nonempty := nonempty_range_iff.2 hk.ne'
  simp only [argminRule, h, ↓reduceDIte]
  exact mem_range.1 (Classical.choose_spec ((range k).exists_min_image cnt h)).1

lemma argminRule_le {k : ℕ} (hk : 0 < k) (cnt : ℕ → ℕ) {j : ℕ} (hj : j < k) :
    cnt (argminRule k cnt) ≤ cnt j := by
  have h : (range k).Nonempty := nonempty_range_iff.2 hk.ne'
  simp only [argminRule, h, ↓reduceDIte]
  exact (Classical.choose_spec ((range k).exists_min_image cnt h)).2 j (mem_range.2 hj)

/-- Pigeonhole: if the colours `< k` of the parents of `v` are counted by `cnt`, the least used
colour is used by at most `⌊#par/k⌋` parents. -/
lemma card_argmin_le {k : ℕ} (hk : 0 < k) (s : Finset V) (c : V → ℕ) :
    #{u ∈ s | c u = argminRule k (fun j => #{u ∈ s | c u = j})} ≤ #s / k := by
  set cnt : ℕ → ℕ := fun j => #{u ∈ s | c u = j}
  set j₀ := argminRule k cnt
  rw [Nat.le_div_iff_mul_le hk]
  have hsum : ∑ j ∈ range k, cnt j ≤ #s := by
    rw [← card_biUnion]
    · exact card_le_card (biUnion_subset.2 fun j _ => filter_subset _ _)
    · intro i _ j _ hij
      exact disjoint_filter.2 fun u _ hi hj => hij (hi.symm.trans hj)
  calc cnt j₀ * k = ∑ _j ∈ range k, cnt j₀ := by simp [mul_comm]
    _ ≤ ∑ j ∈ range k, cnt j := sum_le_sum fun j hj => argminRule_le hk cnt (mem_range.1 hj)
    _ ≤ #s := hsum

/-- Procedure Simple-Arbdefective with `k` colours, run for `ℓ` rounds on the orientation `par`. -/
noncomputable def simpleArb (k ℓ : ℕ) (G : SimpleGraph V) (par : V → Finset V) : V → ℕ :=
  orientRun (argminRule k) ℓ G par

/-- **Theorem 3.2.** Suppose that Procedure Simple-Arbdefective is invoked with an acyclic partial
orientation of length `ℓ`, out-degree at most `m` and deficit at most `τ`, and an integer `k > 0`.
Then it produces a `(τ + ⌊m/k⌋)`-arbdefective `k`-colouring in `ℓ` rounds (`simpleArb_isLocal`). -/
theorem simpleArbdefective {G : SimpleGraph V} {par : V → Finset V}
    (hP : IsPartialOrientation G par) {ℓ m τ k : ℕ} (hL : LengthLE par ℓ) (hm : OutDegLE par m)
    (hτ : DeficitLE G par τ) (hk : 0 < k) :
    IsArbdefective G (simpleArb k ℓ G par) (τ + m / k) ∧ ∀ v, simpleArb k ℓ G par v < k := by
  obtain ⟨h, hle, hh⟩ := exists_height_of_lengthLE hL
  have hspec := orientRun_spec (argminRule k) hP hh hle
  refine ⟨?_, fun v => ?_⟩
  · rw [add_comm]
    refine isArbdefective_of_parents hP hL.isAcyclic hτ _ fun v => ?_
    have hv := hspec v
    unfold simpleArb
    conv_lhs => rw [hv]
    convert (card_argmin_le hk (par v) (orientRun (argminRule k) ℓ G par)).trans
      (Nat.div_le_div_right (hm v)) using 3
  · rw [simpleArb, hspec v]; exact argminRule_lt hk _

/-- Procedure Simple-Arbdefective runs in `ℓ` rounds. -/
theorem simpleArb_isLocal (k ℓ : ℕ) :
    IsLocal (V := V) ℓ (fun G par v => simpleArb k ℓ G par v) :=
  orientRun_isLocal _ ℓ

/-! ### Greedy colouring along a complete orientation -/

/-- The least colour not used by any parent. -/
noncomputable def firstFreeRule (cnt : ℕ → ℕ) : ℕ := sInf {j | cnt j = 0}

/-- Greedy colouring along the orientation `par`, run for `ℓ` rounds. -/
noncomputable def greedyOrient (ℓ : ℕ) (G : SimpleGraph V) (par : V → Finset V) : V → ℕ :=
  orientRun firstFreeRule ℓ G par

/-- **Greedy colouring along an orientation** (Appendix A / Lemma 2.2(1) of [4]): on a complete
acyclic orientation of length `ℓ` and out-degree `≤ m`, the greedy procedure computes a legal
colouring with colours `≤ m` in `ℓ` rounds (`greedyOrient_isLocal`). -/
theorem greedyAlongOrientation {G : SimpleGraph V} {par : V → Finset V}
    (hP : IsPartialOrientation G par) (hC : IsComplete G par) {ℓ m : ℕ} (hL : LengthLE par ℓ)
    (hm : OutDegLE par m) :
    IsLegal G (greedyOrient ℓ G par) ∧ ∀ v, greedyOrient ℓ G par v ≤ m := by
  obtain ⟨h, hle, hh⟩ := exists_height_of_lengthLE hL
  have hspec := orientRun_spec firstFreeRule hP hh hle
  set c := greedyOrient ℓ G par
  -- the colour of `v` is used by no parent, and is at most the number of parents
  have hfree : ∀ v, #{u ∈ par v | c u = c v} = 0 ∧ c v ≤ #(par v) := by
    intro v
    set cnt : ℕ → ℕ := fun j => #{u ∈ par v | c u = j}
    have hcv : c v = sInf {j | cnt j = 0} := hspec v
    have hne : ∃ j ≤ #(par v), cnt j = 0 := by
      by_contra hall
      push Not at hall
      have hsum : ∑ j ∈ range (#(par v) + 1), cnt j ≤ #(par v) := by
        rw [← card_biUnion]
        · exact card_le_card (biUnion_subset.2 fun j _ => filter_subset _ _)
        · intro i _ j _ hij
          exact disjoint_filter.2 fun u _ hi hj => hij (hi.symm.trans hj)
      have : #(par v) + 1 ≤ ∑ j ∈ range (#(par v) + 1), cnt j := by
        calc #(par v) + 1 = ∑ _j ∈ range (#(par v) + 1), 1 := by simp
          _ ≤ _ := sum_le_sum fun j hj =>
              Nat.one_le_iff_ne_zero.2 (hall j (Nat.lt_succ_iff.1 (mem_range.1 hj)))
      omega
    obtain ⟨j, hj, hj0⟩ := hne
    have hmem : c v ∈ {j | cnt j = 0} := by rw [hcv]; exact Nat.sInf_mem ⟨j, hj0⟩
    have hle : c v ≤ j := by rw [hcv]; exact Nat.sInf_le hj0
    exact ⟨hmem, hle.trans hj⟩
  refine ⟨isLegal_of_complete_of_parents hC c fun v u hu huv => ?_, fun v =>
    (hfree v).2.trans (hm v)⟩
  have := (hfree v).1
  rw [card_eq_zero, filter_eq_empty_iff] at this
  exact this hu huv

/-- The greedy procedure runs in `ℓ` rounds. -/
theorem greedyOrient_isLocal (ℓ : ℕ) :
    IsLocal (V := V) ℓ (fun G par v => greedyOrient ℓ G par v) :=
  orientRun_isLocal _ ℓ

end Podc.ArbdefectiveColoring
