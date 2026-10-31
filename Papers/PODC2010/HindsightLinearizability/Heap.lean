import Mathlib

/-!
# Heap states, the integrity properties of Fig. 4, and the Hindsight Lemma

O'Hearn, Rinetzky, Vechev, Yahav, Yorsh, *Verifying Linearizability with Hindsight*, PODC 2010.

This file formalizes the algorithm-independent part of the paper (Sections 4 and 5):

* `HeapState N K`: the part of a memory state that the integrity properties talk about: the
  allocated nodes `alloc` (the paper's `N_σ`), the fields `n`, `k`, `m` of every node and the
  shared variables `H` and `T`. `null` is `none`.
* links, heap paths (`Reach`), backbone and exterior nodes (Section 3, "Terminology");
* the state and step properties of Fig. 4;
* shape-legal and data-shape-legal traces (Definitions 5.1, 5.5);
* the Hindsight Lemma (Lemma 5.2) `hindsight`, temporal backbones (Definition 5.3), the
  Backbone Lemma (Lemma 5.4, corrected form `backbone_lemma`; the statement of the paper is
  refuted in `Counterexample.lean`), backbone keys (Definition 5.6) and the Local Window Lemma
  (Lemma 5.7) `local_window` (in the form used in the proof of Theorem 7.5).

A trace is a function `τ : ℕ → HeapState N K` together with its length `n`; only the states
`τ 0, …, τ (n - 1)` matter.
-/

namespace Podc.HindsightLinearizability

/-- The thread-shared part of a memory state seen as a heap of list nodes: allocated nodes
`alloc` (`N_σ` in the paper), the `n`-field (`none` = `null`), `k`-field and `m`-field of every
node, and the shared variables `H` and `T`. -/
structure HeapState (N K : Type*) where
  /-- The allocated nodes. -/
  alloc : Set N
  /-- The `n`-field (successor pointer). -/
  next : N → Option N
  /-- The `k`-field (key). -/
  key : N → K
  /-- The `m`-field (mark bit). -/
  mark : N → Bool
  /-- The shared variable `H` (head node). -/
  H : N
  /-- The shared variable `T` (tail node). -/
  T : N

variable {N K : Type*}

namespace HeapState

variable (σ : HeapState N K)

/-- `u.n ↦ v` is a link in `σ`. -/
def Link (u v : N) : Prop := σ.next u = some v

/-- `v` is reachable from `u` in `σ` (there is a heap path from `u` to `v`; the empty path is
allowed). -/
def Reach : N → N → Prop := Relation.ReflTransGen σ.Link

/-- A backbone node: reachable from the head node. -/
def Backbone (u : N) : Prop := σ.Reach σ.H u

/-- An exterior node: an allocated node which is not a backbone node. -/
def Exterior (u : N) : Prop := u ∈ σ.alloc ∧ ¬ σ.Backbone u

/-- A backbone link: a link whose source is a backbone node. -/
def BackboneLink (u v : N) : Prop := σ.Backbone u ∧ σ.Link u v

/-! ### State properties of Fig. 4 -/

/-- `φ_H`: the head node exists. -/
def PhiH : Prop := σ.H ∈ σ.alloc
/-- `φ_T`: the tail node exists. -/
def PhiT : Prop := σ.T ∈ σ.alloc
/-- `φ_{T n -}`: the tail node has no successor. -/
def PhiTn : Prop := σ.next σ.T = none
/-- `φ_n`: every node other than the tail node has a successor. -/
def PhiN : Prop := ∀ u ∈ σ.alloc, u ≠ σ.T → ∃ v, σ.next u = some v
/-- Pointers only point to allocated nodes (part of the memory model of Section 4: a value is
`null` or the location of an object; memory is not reclaimed). -/
def Closed : Prop := ∀ u ∈ σ.alloc, ∀ v, σ.next u = some v → v ∈ σ.alloc
/-- `φ_∞`: the key of the tail node is `∞`. -/
def PhiInf [Top K] : Prop := σ.key σ.T = ⊤
/-- `φ_{-∞}`: the key of the head node is `-∞`. -/
def PhiNegInf [Bot K] : Prop := σ.key σ.H = ⊥
/-- `φ_<`: the key of every node is smaller than the key of its successor. -/
def PhiLt [LT K] : Prop := ∀ u ∈ σ.alloc, ∀ v, σ.next u = some v → σ.key u < σ.key v
/-- `φ_{rT}`: the tail node is reachable from every node. -/
def PhiRT : Prop := ∀ u ∈ σ.alloc, σ.Reach u σ.T
/-- `φ_{ac}`: there are no cyclic heap paths. -/
def PhiAc : Prop := ∀ u, ¬ Relation.TransGen σ.Link u u
/-- `φ_s`: every list of nodes is sorted (keys are non-decreasing along heap paths). -/
def PhiS [LE K] : Prop := ∀ u v, σ.Reach u v → σ.key u ≤ σ.key v
/-- `φ_{UB}`: a node is unmarked if and only if it is a backbone node. -/
def PhiUB : Prop := ∀ u ∈ σ.alloc, (σ.mark u = false ↔ σ.Backbone u)

end HeapState

/-! ### Step properties of Fig. 4 -/

section Steps

variable (σ σ' : HeapState N K)

/-- `δ_H`: the value of `H` never changes. -/
def DeltaH : Prop := σ'.H = σ.H
/-- `δ_T`: the value of `T` never changes. -/
def DeltaT : Prop := σ'.T = σ.T
/-- `δ_k`: the key of a node does not change. -/
def DeltaK : Prop := ∀ u ∈ σ.alloc, σ'.key u = σ.key u
/-- `δ_m`: a marked node does not become unmarked. -/
def DeltaM : Prop := ∀ u ∈ σ.alloc, σ.mark u = true → σ'.mark u = true
/-- `δ_e`: an exterior node does not become a backbone node. -/
def DeltaE : Prop := ∀ u, σ.Exterior u → ¬ σ'.Backbone u
/-- `δ_{en}`: the successor of an exterior node does not change. -/
def DeltaEN : Prop := ∀ u, σ.Exterior u → σ'.next u = σ.next u
/-- `δ_{bn}`: if the successor of a backbone node changes, the node remains a backbone node. -/
def DeltaBN : Prop := ∀ u, σ.Backbone u → σ'.next u ≠ σ.next u → σ'.Backbone u
/-- Memory is not reclaimed (standing assumption of Section 4). -/
def NoReclaim : Prop := σ.alloc ⊆ σ'.alloc

end Steps

/-! ### Shape-legal and data-shape-legal traces (Definitions 5.1 and 5.5) -/

/-- The set's shape-state property `φ^s = φ_H ∧ φ_T ∧ φ_n ∧ φ_{rT} ∧ φ_{ac}` (plus the memory
model's closedness). -/
def ShapeState (σ : HeapState N K) : Prop :=
  σ.PhiH ∧ σ.PhiT ∧ σ.PhiN ∧ σ.PhiRT ∧ σ.PhiAc ∧ σ.Closed

/-- The set's shape-step property `δ^s = δ_H ∧ δ_T ∧ δ_e ∧ δ_{en} ∧ δ_{bn}` (plus the memory
model's "no reclamation"). -/
def ShapeStep (σ σ' : HeapState N K) : Prop :=
  DeltaH σ σ' ∧ DeltaT σ σ' ∧ DeltaE σ σ' ∧ DeltaEN σ σ' ∧ DeltaBN σ σ' ∧ NoReclaim σ σ'

/-- Definition 5.1: the trace `τ 0, …, τ (n-1)` is shape-legal. -/
def ShapeLegal (τ : ℕ → HeapState N K) (n : ℕ) : Prop :=
  (∀ i < n, ShapeState (τ i)) ∧ (∀ i, i + 1 < n → ShapeStep (τ i) (τ (i + 1)))

/-- Definition 5.5: a data-shape-legal trace (data-state property `φ^d = φ_s`, data-step
property `δ^d = δ_k`). -/
def DataShapeLegal [LE K] (τ : ℕ → HeapState N K) (n : ℕ) : Prop :=
  ShapeLegal τ n ∧ (∀ i < n, (τ i).PhiS) ∧ (∀ i, i + 1 < n → DeltaK (τ i) (τ (i + 1)))

namespace HeapState

variable {σ : HeapState N K}

/-! ### Basic facts about heap paths -/

lemma Reach.refl' (u : N) : σ.Reach u u := Relation.ReflTransGen.refl

lemma Reach.trans {u v w : N} (h₁ : σ.Reach u v) (h₂ : σ.Reach v w) : σ.Reach u w :=
  Relation.ReflTransGen.trans h₁ h₂

lemma Reach.of_link {u v : N} (h : σ.Link u v) : σ.Reach u v :=
  Relation.ReflTransGen.single h

lemma Reach.tail' {u v w : N} (h₁ : σ.Reach u v) (h₂ : σ.Link v w) : σ.Reach u w :=
  Relation.ReflTransGen.tail h₁ h₂

lemma Reach.head' {u v w : N} (h₁ : σ.Link u v) (h₂ : σ.Reach v w) : σ.Reach u w :=
  Relation.ReflTransGen.head h₁ h₂

/-- A heap path from `u` either is empty or starts with the (unique) link out of `u`. -/
lemma Reach.cases_head {u w : N} (h : σ.Reach u w) :
    w = u ∨ ∃ v, σ.Link u v ∧ σ.Reach v w := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨v, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨v, h1, h2⟩

/-- In a heap (every node has at most one successor), two nodes reachable from the same node
are ordered by reachability. -/
lemma Reach.total {u v w : N} (hv : σ.Reach u v) (hw : σ.Reach u w) :
    σ.Reach v w ∨ σ.Reach w v := by
  induction hv using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl hw
  | @head a c h₁ hcv ih =>
    rcases hw.cases_head with rfl | ⟨x, hx, hxw⟩
    · exact Or.inr (Reach.head' h₁ hcv)
    · have : c = x := by unfold Link at h₁ hx; rw [h₁] at hx; exact Option.some.inj hx
      subst this
      exact ih hxw

lemma Backbone.of_link {u v : N} (hu : σ.Backbone u) (h : σ.Link u v) : σ.Backbone v :=
  Reach.tail' hu h

lemma BackboneLink.backbone_target {u v : N} (h : σ.BackboneLink u v) : σ.Backbone v :=
  h.1.of_link h.2

/-- Reachable nodes of allocated nodes are allocated. -/
lemma Reach.mem_alloc (hc : σ.Closed) {u v : N} (h : σ.Reach u v) (hu : u ∈ σ.alloc) :
    v ∈ σ.alloc := by
  induction h with
  | refl => exact hu
  | tail _ hl ih => exact hc _ ih _ hl

lemma Backbone.mem_alloc (hH : σ.PhiH) (hc : σ.Closed) {u : N} (h : σ.Backbone u) :
    u ∈ σ.alloc := Reach.mem_alloc hc h hH

/-- `φ_<` implies that keys strictly increase along non-empty heap paths. -/
lemma key_lt_of_transGen [Preorder K] (hlt : σ.PhiLt) (hc : σ.Closed) {u v : N}
    (hu : u ∈ σ.alloc) (h : Relation.TransGen σ.Link u v) : σ.key u < σ.key v := by
  induction h with
  | single h => exact hlt _ hu _ h
  | tail h₁ h₂ ih =>
    exact ih.trans (hlt _ (Reach.mem_alloc hc (Relation.TransGen.to_reflTransGen h₁) hu) _ h₂)

/-- `φ_<` implies `φ_s`. -/
lemma phiS_of_phiLt [Preorder K] (hlt : σ.PhiLt) (hc : σ.Closed) :
    ∀ u ∈ σ.alloc, ∀ v, σ.Reach u v → σ.key u ≤ σ.key v := by
  intro u hu v h
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with rfl | h
  · exact le_rfl
  · exact (key_lt_of_transGen hlt hc hu h).le

/-- `φ_<` implies `φ_{ac}` for allocated nodes. -/
lemma not_cycle_of_phiLt [Preorder K] (hlt : σ.PhiLt) (hc : σ.Closed) {u : N}
    (hu : u ∈ σ.alloc) : ¬ Relation.TransGen σ.Link u u :=
  fun h => lt_irrefl _ (key_lt_of_transGen hlt hc hu h)

/-- `φ_<`, `φ_n` and a finite heap imply `φ_{rT}`. -/
lemma phiRT_of [Preorder K] (hlt : σ.PhiLt) (hc : σ.Closed) (hn : σ.PhiN)
    (hfin : σ.alloc.Finite) : σ.PhiRT := by
  classical
  intro u hu
  -- strong induction on the number of allocated nodes with a larger key
  suffices ∀ m, ∀ u ∈ σ.alloc, (hfin.toFinset.filter (fun w => σ.key u < σ.key w)).card ≤ m →
      σ.Reach u σ.T from this _ u hu le_rfl
  intro m
  induction m with
  | zero =>
    intro u hu hm
    by_cases hT : u = σ.T
    · subst hT; exact Reach.refl' _
    obtain ⟨v, hv⟩ := hn u hu hT
    have hva := hc u hu v hv
    have : v ∈ hfin.toFinset.filter (fun w => σ.key u < σ.key w) := by
      simp [hva, hlt u hu v hv]
    simp_all
  | succ m ih =>
    intro u hu hm
    by_cases hT : u = σ.T
    · subst hT; exact Reach.refl' _
    obtain ⟨v, hv⟩ := hn u hu hT
    have hva := hc u hu v hv
    have hlt' := hlt u hu v hv
    refine Reach.head' hv (ih v hva ?_)
    have hsub : hfin.toFinset.filter (fun w => σ.key v < σ.key w) ⊂
        hfin.toFinset.filter (fun w => σ.key u < σ.key w) := by
      refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨v, ?_, ?_⟩
      · intro w; simp only [Finset.mem_filter]; exact fun ⟨h1, h2⟩ => ⟨h1, hlt'.trans h2⟩
      · simp [hva, hlt']
      · simp
    have := Finset.card_lt_card hsub
    omega

/-! ### Backbones given by an explicit list -/

/-- If `x :: l` is a heap path whose last node has no successor, then the nodes reachable from
`x` are exactly the nodes of the list. -/
lemma reach_iff_mem_of_isChain {x : N} {l : List N} (hc : (x :: l).IsChain σ.Link)
    (hlast : σ.next ((x :: l).getLast (List.cons_ne_nil _ _)) = none) (u : N) :
    σ.Reach x u ↔ u ∈ x :: l := by
  constructor
  · intro h
    induction h with
    | refl => exact List.mem_cons_self
    | @tail a b _ hl ih =>
      -- `a ∈ x :: l`, `a.n = b`, so `b` is the next element of the list
      clear * - hc hlast ih hl
      induction l generalizing x with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ih
        subst ih
        simp only [List.getLast_singleton] at hlast
        simp [Link, hlast] at hl
      | cons y l ihl =>
        rw [List.isChain_cons_cons] at hc
        rcases List.mem_cons.1 ih with rfl | ih
        · have : b = y := by unfold Link at hl hc; rw [hc.1] at hl; exact (Option.some.inj hl).symm
          subst this; simp
        · exact List.mem_cons_of_mem _ (ihl hc.2 (by simpa using hlast) ih)
  · intro h
    induction l generalizing x with
    | nil =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact Reach.refl' _
    | cons y l ihl =>
      rw [List.isChain_cons_cons] at hc
      rcases List.mem_cons.1 h with rfl | h
      · exact Reach.refl' _
      · exact Reach.head' hc.1 (ihl hc.2 (by simpa using hlast) h)

/-! ### Backbone keys (Definition 5.6) and the local window -/

/-- Definition 5.6: the set `K_σ` of backbone keys. -/
def backboneKeys (σ : HeapState N K) : Set K := σ.key '' {u | σ.Backbone u}

/-- The local window at one state: if `u.n ↦ v` is a backbone link of a state satisfying `φ_s`,
then the only backbone keys in the interval `[u.k, v.k]` are `u.k` and `v.k`. -/
lemma backboneKeys_inter_Icc [LinearOrder K] (hs : σ.PhiS) {u v : N}
    (h : σ.BackboneLink u v) :
    σ.backboneKeys ∩ Set.Icc (σ.key u) (σ.key v) = {σ.key u, σ.key v} := by
  ext z
  simp only [backboneKeys, Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h1, h2⟩
    rcases Reach.total hx h.1 with hxu | hux
    · exact Or.inl (le_antisymm (hs _ _ hxu) h1)
    · rcases hux.cases_head with rfl | ⟨w, hw, hwx⟩
      · exact Or.inl rfl
      · have : w = v := by
          have h2 := h.2; unfold Link at hw h2; rw [h2] at hw; exact (Option.some.inj hw).symm
        subst this
        exact Or.inr (le_antisymm h2 (hs _ _ hwx))
  · have hsuv : σ.key u ≤ σ.key v := hs _ _ (Reach.of_link h.2)
    rintro (rfl | rfl)
    · exact ⟨⟨u, h.1, rfl⟩, le_rfl, hsuv⟩
    · exact ⟨⟨v, h.backbone_target, rfl⟩, hsuv, le_rfl⟩

end HeapState

/-! ### The Hindsight Lemma (Lemma 5.2) -/

open HeapState

/-- The core of the Hindsight Lemma: if `v` is a backbone node at time `i` and `v.n ↦ w` at time
`k ≥ i`, then at some time `j ∈ [i, k]` the node `v` is a backbone node with successor `w`.
Only the steps between `i` and `k` are used, and only `δ_{en}`, `δ_{bn}`, no reclamation, and
`φ_H` + closedness at time `i`. -/
theorem hindsight_node {τ : ℕ → HeapState N K} {i k : ℕ} (hik : i ≤ k)
    (hstep : ∀ h, i ≤ h → h < k →
      DeltaEN (τ h) (τ (h + 1)) ∧ DeltaBN (τ h) (τ (h + 1)) ∧ NoReclaim (τ h) (τ (h + 1)))
    {v w : N} (hv : (τ i).Backbone v) (hva : v ∈ (τ i).alloc) (hw : (τ k).Link v w) :
    ∃ j, i ≤ j ∧ j ≤ k ∧ (τ j).Backbone v ∧ (τ j).Link v w := by
  induction k, hik using Nat.le_induction with
  | base => exact ⟨i, le_rfl, le_rfl, hv, hw⟩
  | succ k hik ih =>
    obtain ⟨hen, hbn, hrec⟩ := hstep k hik (Nat.lt_succ_self k)
    by_cases hb : (τ (k + 1)).Backbone v
    · exact ⟨k + 1, by omega, le_rfl, hb, hw⟩
    -- `v` is allocated at every time `≥ i`
    have halloc : ∀ h, i ≤ h → h ≤ k → v ∈ (τ h).alloc := by
      intro h hih hhk
      induction h, hih using Nat.le_induction with
      | base => exact hva
      | succ h hih ihh => exact (hstep h hih (by omega)).2.2 (ihh (by omega))
    have hvk := halloc k hik le_rfl
    by_cases hbk : (τ k).Backbone v
    · -- `v` turns exterior at the step `k → k+1`, so its successor did not change
      have : (τ (k + 1)).next v = (τ k).next v := by
        by_contra hne; exact hb (hbn v hbk hne)
      exact ⟨k, hik, Nat.le_succ k, hbk, by unfold Link at hw ⊢; rw [← this]; exact hw⟩
    · have : (τ (k + 1)).next v = (τ k).next v := hen v ⟨hvk, hbk⟩
      obtain ⟨j, h1, h2, h3, h4⟩ := ih (fun h h1 h2 => hstep h h1 (by omega))
        (by unfold Link at hw ⊢; rw [← this]; exact hw)
      exact ⟨j, h1, by omega, h3, h4⟩

/-- **Lemma 5.2 (Hindsight).** Let `τ` be a shape-legal trace of length `n`, `0 ≤ i ≤ k < n`.
If `u.n ↦ v` is a backbone link in `τ i` and `v.n ↦ w` is a link in `τ k`, then there is
`j ∈ [i, k]` such that `v.n ↦ w` is a backbone link in `τ j`. -/
theorem hindsight {τ : ℕ → HeapState N K} {n : ℕ} (hτ : ShapeLegal τ n) {i k : ℕ}
    (hik : i ≤ k) (hkn : k < n) {u v w : N} (huv : (τ i).BackboneLink u v)
    (hvw : (τ k).Link v w) :
    ∃ j, i ≤ j ∧ j ≤ k ∧ (τ j).BackboneLink v w := by
  obtain ⟨hH, -, -, -, -, hc⟩ := hτ.1 i (by omega)
  have hv := huv.backbone_target
  obtain ⟨j, h1, h2, h3, h4⟩ := hindsight_node (τ := τ) hik
    (fun h _ hh => by
      obtain ⟨-, -, -, hen, hbn, hrec⟩ := hτ.2 h (by omega)
      exact ⟨hen, hbn, hrec⟩) hv (hv.mem_alloc hH hc) hvw
  exact ⟨j, h1, h2, h3, h4⟩

/-! ### Temporal backbones (Definition 5.3) and the Backbone Lemma (Lemma 5.4) -/

/-- Definition 5.3: `ζ 0, …, ζ k` (a node-pair path) is a temporal backbone in `τ` going through
the subsequence `τ (idx 0), …, τ (idx k)` (`idx` strictly increasing): `ζ 0` is a backbone link
in `τ (idx 0)` and `ζ m` is a link in `τ (idx m)` for `0 < m ≤ k`. -/
structure TemporalBackbone (τ : ℕ → HeapState N K) (ζ : ℕ → N × N) (idx : ℕ → ℕ) (k : ℕ) :
    Prop where
  path : ∀ m < k, (ζ m).2 = (ζ (m + 1)).1
  idx_lt : ∀ m < k, idx m < idx (m + 1)
  first : (τ (idx 0)).BackboneLink (ζ 0).1 (ζ 0).2
  link : ∀ m, 0 < m → m ≤ k → (τ (idx m)).Link (ζ m).1 (ζ m).2

/-- **Lemma 5.4 (Backbone Lemma), corrected.** Let `ζ` be a temporal backbone in a shape-legal
trace going through `τ (i₀), …, τ (i_k)`. There are indices `i₀ = j₀ ≤ j₁ ≤ … ≤ j_k` with
`i₀ ≤ j_m ≤ i_m` such that `ζ m` is a backbone link in `τ (j_m)`.

The paper claims strict inequalities `j₀ < j₁ < … < j_k` and `j_k = i_k`; both are false
(`Counterexample.lean`). -/
theorem backbone_lemma {τ : ℕ → HeapState N K} {n : ℕ} (hτ : ShapeLegal τ n)
    {ζ : ℕ → N × N} {idx : ℕ → ℕ} {k : ℕ} (hζ : TemporalBackbone τ ζ idx k)
    (hk : idx k < n) :
    ∃ j : ℕ → ℕ, j 0 = idx 0 ∧ (∀ m < k, j m ≤ j (m + 1)) ∧
      ∀ m ≤ k, idx 0 ≤ j m ∧ j m ≤ idx m ∧ (τ (j m)).BackboneLink (ζ m).1 (ζ m).2 := by
  -- `idx` is monotone on `[0, k]`
  have hmono : ∀ a b, a ≤ b → b ≤ k → idx a ≤ idx b := by
    intro a b hab hbk
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by omega)).trans (hζ.idx_lt b (by omega)).le
  -- build the sequence by recursion, proving its properties along the way
  suffices H : ∀ m ≤ k, ∃ js : ℕ → ℕ, js 0 = idx 0 ∧ (∀ a < m, js a ≤ js (a + 1)) ∧
      ∀ a ≤ m, idx 0 ≤ js a ∧ js a ≤ idx a ∧ (τ (js a)).BackboneLink (ζ a).1 (ζ a).2 by
    obtain ⟨js, h0, h1, h2⟩ := H k le_rfl
    exact ⟨js, h0, h1, h2⟩
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun _ => idx 0, rfl, fun a ha => absurd ha (Nat.not_lt_zero _), ?_⟩
    intro a ha
    obtain rfl : a = 0 := by omega
    exact ⟨le_rfl, le_rfl, hζ.first⟩
  | succ m ih =>
    intro hm
    obtain ⟨js, h0, h1, h2⟩ := ih (by omega)
    obtain ⟨hlo, hhi, hbl⟩ := h2 m le_rfl
    have hlink := hζ.link (m + 1) (Nat.succ_pos _) hm
    rw [← hζ.path m (by omega)] at hlink
    have hle : js m ≤ idx (m + 1) := hhi.trans (hζ.idx_lt m (by omega)).le
    obtain ⟨j', hj1, hj2, hj3⟩ := hindsight hτ hle (lt_of_le_of_lt (hmono _ _ hm le_rfl) hk)
      hbl hlink
    rw [hζ.path m (by omega)] at hj3
    refine ⟨Function.update js (m + 1) j', by simp [h0], ?_, ?_⟩
    · intro a ha
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · simp only [Function.update_apply, show a ≠ m + 1 by omega, show a + 1 ≠ m + 1 by omega,
          if_false]
        exact h1 a ha
      · simp [hj1]
    · intro a ha
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ha) with ha | rfl
      · simp only [Function.update_apply, show a ≠ m + 1 by omega, if_false]
        exact h2 a (by omega)
      · simp only [Function.update_self]
        exact ⟨hlo.trans hj1, hj2, hj3⟩

/-! ### The Local Window Lemma (Lemma 5.7) -/

/-- **Lemma 5.7 (Local Window Lemma)**, in the form used in the proof of Theorem 7.5: for every
pair `⟨u, v⟩ = ζ m` of a temporal backbone (from the `i₀`-th to the `i_k`-th state) of a
data-shape-legal trace there is a state `σ = τ h`, `i₀ ≤ h ≤ i_m ≤ i_k`, in which `u.n ↦ v` is a
backbone link and `K_σ ∩ [u.k_σ, v.k_σ] = {u.k_σ, v.k_σ}`.

The paper states the conclusion as `K_σ ∩ {u.k_σ, v.k_σ} = {u.k_σ, v.k_σ}` (a typo for the
interval, as the proof of Theorem 7.5 shows). -/
theorem local_window [LinearOrder K] {τ : ℕ → HeapState N K} {n : ℕ} (hτ : DataShapeLegal τ n)
    {ζ : ℕ → N × N} {idx : ℕ → ℕ} {k : ℕ} (hζ : TemporalBackbone τ ζ idx k) (hk : idx k < n)
    {m : ℕ} (hm : m ≤ k) :
    ∃ h, idx 0 ≤ h ∧ h ≤ idx m ∧ (τ h).BackboneLink (ζ m).1 (ζ m).2 ∧
      (τ h).backboneKeys ∩ Set.Icc ((τ h).key (ζ m).1) ((τ h).key (ζ m).2) =
        {(τ h).key (ζ m).1, (τ h).key (ζ m).2} := by
  obtain ⟨j, -, -, hj⟩ := backbone_lemma hτ.1 hζ hk
  obtain ⟨h1, h2, h3⟩ := hj m hm
  have hmono : idx m ≤ idx k := by
    clear hj h1 h2 h3
    induction k, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih =>
      exact (ih ⟨fun a ha => hζ.path a (by omega), fun a ha => hζ.idx_lt a (by omega), hζ.first,
        fun a h0 ha => hζ.link a h0 (by omega)⟩ (lt_of_le_of_lt (hζ.idx_lt b (by omega)).le hk)
        ).trans (hζ.idx_lt b (by omega)).le
  exact ⟨j m, h1, h2, h3, backboneKeys_inter_Icc (hτ.2.1 _ (by omega)) h3⟩

/-- Lemma 5.7 with the conclusion literally as printed, `K_σ ∩ {u.k_σ, v.k_σ} = {u.k_σ, v.k_σ}`
(i.e. both keys are backbone keys). It is a weak consequence of `local_window`. -/
theorem local_window_as_printed [LinearOrder K] {τ : ℕ → HeapState N K} {n : ℕ}
    (hτ : DataShapeLegal τ n) {ζ : ℕ → N × N} {idx : ℕ → ℕ} {k : ℕ}
    (hζ : TemporalBackbone τ ζ idx k) (hk : idx k < n) {m : ℕ} (hm : m ≤ k) :
    ∃ h, idx 0 ≤ h ∧ h ≤ idx k ∧
      (τ h).backboneKeys ∩ {(τ h).key (ζ m).1, (τ h).key (ζ m).2} =
        {(τ h).key (ζ m).1, (τ h).key (ζ m).2} := by
  obtain ⟨h, h1, h2, h3, -⟩ := local_window hτ hζ hk hm
  have hmono : idx m ≤ idx k := by
    clear h1 h2 h3
    induction k, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih =>
      exact (ih ⟨fun a ha => hζ.path a (by omega), fun a ha => hζ.idx_lt a (by omega), hζ.first,
        fun a h0 ha => hζ.link a h0 (by omega)⟩ (lt_of_le_of_lt (hζ.idx_lt b (by omega)).le hk)
        ).trans (hζ.idx_lt b (by omega)).le
  refine ⟨h, h1, h2.trans hmono, Set.inter_eq_right.2 ?_⟩
  rintro _ (rfl | rfl)
  · exact ⟨_, h3.1, rfl⟩
  · exact ⟨_, h3.backbone_target, rfl⟩

end Podc.HindsightLinearizability
