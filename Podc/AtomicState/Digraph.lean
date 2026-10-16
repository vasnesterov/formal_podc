import Mathlib

/-!
# Ancestors, bounded reachability and source components of digraphs

-- CSLib candidate

Graph-theoretic vocabulary for self-stabilization on *directed* networks (Altisen–Cournier–Defalque–
Devismes, PODC 2024, and the anonymous-unison paper [ACDD23]). An arc `G.Adj q p` means that `q` is
a *predecessor* of `p` (`p` reads `q`).

* `Anc G q p` : `q` is an ancestor of `p` (there is a directed path, possibly empty, from `q` to `p`).
* `ReachIn G n q p` : there is a directed path of length `≤ n` from `q` to `p`.
* `MADLe G α` : every ancestor of every node is at distance `≤ α`, i.e. `α ≥ MAD` (the maximum
  ancestor distance); `mad G` is the least such `α`.
* `IsStronglyConnected`, `IsSCC`, `IsSourceComponent` : the paper's definitions (strong connectivity
  of the *induced* subgraph, maximality, no predecessor outside).
* `isSourceComponent_iff` : `S` is a source component iff `S = Anc(r)` for a node `r` that is an
  ancestor of all its ancestors.
* `exists_sourceComponent_subset_anc` : every node has a source component among its ancestors
  (finite digraphs); hence with a *unique* source component `SC`, `SC ⊆ Anc(p)` for every `p`.
-/

namespace Podc.AtomicState

variable {V : Type*} (G : Digraph V)

/-- `q` is an ancestor of `p`: there is a (possibly empty) directed path from `q` to `p`. -/
def Anc (q p : V) : Prop := Relation.ReflTransGen G.Adj q p

/-- `ReachIn G n q p`: there is a directed path of length at most `n` from `q` to `p`. -/
def ReachIn : ℕ → V → V → Prop
  | 0, q, p => q = p
  | n + 1, q, p => ReachIn n q p ∨ ∃ r, ReachIn n q r ∧ G.Adj r p

/-- `α ≥ MAD`: every ancestor `q` of every node `p` satisfies `‖q, p‖ ≤ α`. -/
def MADLe (α : ℕ) : Prop := ∀ q p, Anc G q p → ReachIn G α q p

variable {G}

@[refl] theorem Anc.refl (p : V) : Anc G p p := Relation.ReflTransGen.refl

theorem Anc.trans {a b c : V} (h₁ : Anc G a b) (h₂ : Anc G b c) : Anc G a c :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Anc.of_adj {a b : V} (h : G.Adj a b) : Anc G a b := Relation.ReflTransGen.single h

theorem Anc.tail {a b c : V} (h₁ : Anc G a b) (h₂ : G.Adj b c) : Anc G a c :=
  Relation.ReflTransGen.tail h₁ h₂

theorem reachIn_zero {q p : V} : ReachIn G 0 q p ↔ q = p := Iff.rfl

theorem reachIn_succ {n : ℕ} {q p : V} :
    ReachIn G (n + 1) q p ↔ ReachIn G n q p ∨ ∃ r, ReachIn G n q r ∧ G.Adj r p := Iff.rfl

theorem ReachIn.refl (n : ℕ) (p : V) : ReachIn G n p p := by
  induction n with
  | zero => rfl
  | succ n ih => exact Or.inl ih

theorem ReachIn.mono {n m : ℕ} {q p : V} (h : ReachIn G n q p) (hnm : n ≤ m) : ReachIn G m q p := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem ReachIn.tail {n : ℕ} {q r p : V} (h : ReachIn G n q r) (hr : G.Adj r p) :
    ReachIn G (n + 1) q p := Or.inr ⟨r, h, hr⟩

theorem ReachIn.anc {n : ℕ} {q p : V} (h : ReachIn G n q p) : Anc G q p := by
  induction n generalizing p with
  | zero => cases h; rfl
  | succ n ih =>
    rcases h with h | ⟨r, hr, hrp⟩
    · exact ih h
    · exact (ih hr).tail hrp

theorem Anc.exists_reachIn {q p : V} (h : Anc G q p) : ∃ n, ReachIn G n q p := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, hn.tail hbc⟩

theorem anc_iff_exists_reachIn {q p : V} : Anc G q p ↔ ∃ n, ReachIn G n q p :=
  ⟨Anc.exists_reachIn, fun ⟨_, h⟩ => h.anc⟩

/-- A path of length `≤ n + 1` that is not of length `≤ n` ends with an arc. -/
theorem ReachIn.exists_pred_of_not {n : ℕ} {q p : V} (h : ReachIn G (n + 1) q p)
    (hn : ¬ ReachIn G n q p) : ∃ r, ReachIn G n q r ∧ G.Adj r p := by
  rcases h with h | h
  · exact absurd h hn
  · exact h

theorem MADLe.mono {α β : ℕ} (h : MADLe G α) (hαβ : α ≤ β) : MADLe G β :=
  fun q p hqp => (h q p hqp).mono hαβ

/-- Paths in a finite digraph can be shortened to length `≤ |V| - 1`; we only need `≤ |V|`. -/
theorem ReachIn.of_card [Fintype V] {n : ℕ} {q p : V} (h : ReachIn G n q p) :
    ReachIn G (Fintype.card V) q p := by
  classical
  -- the set of nodes reachable within `k` steps grows strictly until it stabilises
  let R : ℕ → Finset V := fun k => Finset.univ.filter (fun x => ReachIn G k q x)
  have hmono : ∀ k, R k ⊆ R (k + 1) := fun k x hx => by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact Or.inl hx
  have hstab : ∀ k, R k = R (k + 1) → ∀ j, R (k + j) = R k := by
    intro k hk j
    induction j with
    | zero => rfl
    | succ j ih =>
      apply Finset.Subset.antisymm _ (by
        intro x hx; exact (hmono (k + j)) (ih ▸ hx))
      intro x hx
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with hx | ⟨r, hr, hrx⟩
      · rw [← ih]; simpa [R] using hx
      · have hr' : r ∈ R k := by rw [← ih]; simpa [R] using hr
        rw [hk]; simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hr' ⊢
        exact Or.inr ⟨r, hr', hrx⟩
  -- the card of `R k` is at least `k + 1` as long as it has not stabilised
  have hcard : ∀ k, (∀ j < k, R j ≠ R (j + 1)) → k + 1 ≤ (R k).card := by
    intro k
    induction k with
    | zero =>
      intro _
      have : q ∈ R 0 := by simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
      exact Finset.card_pos.mpr ⟨q, this⟩
    | succ k ih =>
      intro hne
      have h1 := ih (fun j hj => hne j (by omega))
      have h2 : (R k).card < (R (k + 1)).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hmono k, hne k (by omega)⟩)
      omega
  by_cases hn : n ≤ Fintype.card V
  · exact h.mono hn
  · by_contra hcon
    -- some `j < |V|` is a stabilisation point
    have : ∃ j < Fintype.card V, R j = R (j + 1) := by
      by_contra hne
      push Not at hne
      have := hcard (Fintype.card V) hne
      have := Finset.card_le_univ (R (Fintype.card V))
      omega
    obtain ⟨j, hj, hjs⟩ := this
    have h1 : p ∈ R n := by simpa [R] using h
    have h2 : R n = R j := by
      have := hstab j hjs (n - j); rwa [show j + (n - j) = n by omega] at this
    rw [h2] at h1
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    exact hcon (h1.mono (by omega))

theorem madLe_card [Fintype V] : MADLe G (Fintype.card V) := fun _ _ h =>
  let ⟨_, hn⟩ := h.exists_reachIn; hn.of_card

/-- The maximum ancestor distance `MAD` of a finite digraph: the least `α` with `MADLe G α`. -/
noncomputable def mad [Fintype V] (G : Digraph V) : ℕ :=
  @Nat.find (fun α => MADLe G α) (Classical.decPred _) ⟨_, madLe_card⟩

theorem madLe_mad [Fintype V] : MADLe G (mad G) :=
  @Nat.find_spec (fun α => MADLe G α) (Classical.decPred _) ⟨_, madLe_card⟩

theorem mad_le [Fintype V] {α : ℕ} (h : MADLe G α) : mad G ≤ α :=
  @Nat.find_min' (fun α => MADLe G α) (Classical.decPred _) ⟨_, madLe_card⟩ _ h

theorem madLe_iff [Fintype V] {α : ℕ} : MADLe G α ↔ mad G ≤ α :=
  ⟨mad_le, fun h => madLe_mad.mono h⟩

/-! ### Strongly connected components and source components -/

/-- Reachability inside the subgraph induced by `S`. -/
def InducedReach (G : Digraph V) (S : Set V) : V → V → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ G.Adj a b)

/-- The induced subgraph `G(S)` is strongly connected. -/
def IsStronglyConnected (G : Digraph V) (S : Set V) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, InducedReach G S p q

/-- `G(S)` is a strongly connected component: nonempty, strongly connected and maximal. -/
def IsSCC (G : Digraph V) (S : Set V) : Prop :=
  S.Nonempty ∧ IsStronglyConnected G S ∧ ∀ T, S ⊆ T → IsStronglyConnected G T → T = S

/-- A source component: a strongly connected component none of whose nodes has a predecessor
outside the component. -/
def IsSourceComponent (G : Digraph V) (S : Set V) : Prop :=
  IsSCC G S ∧ ∀ p ∈ S, ∀ q, G.Adj q p → q ∈ S

theorem InducedReach.anc {S : Set V} {p q : V} (h : InducedReach G S p q) : Anc G p q := by
  induction h with
  | refl => exact Anc.refl _
  | tail _ hbc ih => exact ih.tail hbc.2.2

/-- Predecessor-closed sets contain all ancestors of their members. -/
theorem mem_of_anc_of_closed {S : Set V} (hS : ∀ p ∈ S, ∀ q, G.Adj q p → q ∈ S) {x p : V}
    (h : Anc G x p) (hp : p ∈ S) : x ∈ S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hp
  | head hab _ ih => exact hS _ ih _ hab

theorem inducedReach_of_anc_of_closed {S : Set V} (hS : ∀ p ∈ S, ∀ q, G.Adj q p → q ∈ S)
    {x p : V} (h : Anc G x p) (hp : p ∈ S) : InducedReach G S x p := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hab hbc ih =>
    have hb := mem_of_anc_of_closed hS hbc hp
    exact Relation.ReflTransGen.head ⟨hS _ hb _ hab, hb, hab⟩ ih

/-- Characterisation of source components: `S = Anc(r)` where `r` is an ancestor of each of its
ancestors. -/
theorem isSourceComponent_iff {S : Set V} :
    IsSourceComponent G S ↔ ∃ r, S = {x | Anc G x r} ∧ ∀ x, Anc G x r → Anc G r x := by
  constructor
  · rintro ⟨⟨⟨r, hr⟩, hsc, -⟩, hcl⟩
    have hS : S = {x | Anc G x r} := by
      ext x
      exact ⟨fun hx => (hsc x hx r hr).anc, fun hx => mem_of_anc_of_closed hcl hx hr⟩
    refine ⟨r, hS, fun x hx => ?_⟩
    have hx' : x ∈ S := hS ▸ hx
    exact (hsc r hr x hx').anc
  · rintro ⟨r, rfl, hr⟩
    have hcl : ∀ p ∈ {x | Anc G x r}, ∀ q, G.Adj q p → q ∈ {x | Anc G x r} :=
      fun p hp q hq => (Anc.of_adj hq).trans hp
    refine ⟨⟨⟨r, Anc.refl r⟩, ?_, ?_⟩, hcl⟩
    · intro p hp q hq
      exact inducedReach_of_anc_of_closed hcl ((hp : Anc G p r).trans (hr q hq)) hq
    · intro T hST hT
      apply Set.Subset.antisymm _ hST
      intro t ht
      exact (hT t ht r (hST (Anc.refl r))).anc

theorem IsSourceComponent.eq_anc {S : Set V} (hS : IsSourceComponent G S) {r : V} (hr : r ∈ S) :
    S = {x | Anc G x r} := by
  obtain ⟨⟨-, hsc, -⟩, hcl⟩ := hS
  ext x
  exact ⟨fun hx => (hsc x hx r hr).anc, fun hx => mem_of_anc_of_closed hcl hx hr⟩

theorem IsSourceComponent.closed {S : Set V} (hS : IsSourceComponent G S) :
    ∀ p ∈ S, ∀ q, G.Adj q p → q ∈ S := hS.2

theorem IsSourceComponent.nonempty {S : Set V} (hS : IsSourceComponent G S) : S.Nonempty :=
  hS.1.1

theorem IsSourceComponent.anc_of_mem {S : Set V} (hS : IsSourceComponent G S) {p q : V}
    (hp : p ∈ S) (hq : q ∈ S) : Anc G p q := (hS.1.2.1 p hp q hq).anc

/-- Two source components sharing a node are equal. -/
theorem IsSourceComponent.eq_of_mem {S T : Set V} (hS : IsSourceComponent G S)
    (hT : IsSourceComponent G T) {r : V} (hrS : r ∈ S) (hrT : r ∈ T) : S = T := by
  rw [hS.eq_anc hrS, hT.eq_anc hrT]

/-- Every node of a finite digraph has a source component among its ancestors. -/
theorem exists_sourceComponent_subset_anc [Finite V] (p : V) :
    ∃ S, IsSourceComponent G S ∧ S ⊆ {x | Anc G x p} := by
  classical
  induction h : Set.ncard {x | Anc G x p} using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hall : ∀ x, Anc G x p → Anc G p x
    · exact ⟨_, isSourceComponent_iff.mpr ⟨p, rfl, hall⟩, le_rfl⟩
    · push Not at hall
      obtain ⟨x, hxp, hpx⟩ := hall
      have hsub : {y | Anc G y x} ⊂ {y | Anc G y p} := by
        refine Set.ssubset_iff_subset_ne.mpr ⟨fun y hy => (hy : Anc G y x).trans hxp, ?_⟩
        intro heq
        have : p ∈ {y | Anc G y x} := heq ▸ (Anc.refl p : Anc G p p)
        exact hpx this
      have hlt : Set.ncard {y | Anc G y x} < n := h ▸ Set.ncard_lt_ncard hsub (Set.toFinite _)
      obtain ⟨S, hS, hSx⟩ := ih _ hlt x rfl
      exact ⟨S, hS, hSx.trans hsub.subset⟩

/-- A nonempty finite digraph has a source component. -/
theorem exists_sourceComponent [Finite V] [Nonempty V] : ∃ S, IsSourceComponent G S :=
  let ⟨S, hS, _⟩ := exists_sourceComponent_subset_anc (G := G) (Classical.arbitrary V)
  ⟨S, hS⟩

/-- With a unique source component `SC`, every node of `SC` is an ancestor of every node. -/
theorem subset_anc_of_unique [Finite V] {SC : Set V} (_hSC : IsSourceComponent G SC)
    (huniq : ∀ S, IsSourceComponent G S → S = SC) (p : V) : SC ⊆ {x | Anc G x p} := by
  obtain ⟨S, hS, hSp⟩ := exists_sourceComponent_subset_anc (G := G) p
  exact huniq S hS ▸ hSp

/-- Distinct source components are disjoint. -/
theorem IsSourceComponent.disjoint {S T : Set V} (hS : IsSourceComponent G S)
    (hT : IsSourceComponent G T) (hne : S ≠ T) : Disjoint S T :=
  Set.disjoint_left.mpr fun _ hrS hrT => hne (hS.eq_of_mem hT hrS hrT)

end Podc.AtomicState
