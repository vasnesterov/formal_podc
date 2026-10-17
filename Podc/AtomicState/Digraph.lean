import Mathlib
import Podc.Digraph.Walk

/-!
# Ancestors and the maximum ancestor distance in the atomic-state model

-- CSLib candidate

Vocabulary of self-stabilization on *directed* networks (Altisen–Cournier–Defalque–Devismes,
PODC 2024, and the anonymous-unison paper [ACDD23]). An arc `G.Adj q p` means that `q` is a
*predecessor* of `p` (`p` reads `q`). Reachability and source components are the general ones of
`Podc/Digraph/Walk.lean`; this file adds the papers' notation.

* `Anc G q p` : `q` is an ancestor of `p`, i.e. `G.Reachable q p`.
* `ReachIn G n q p` : there is a directed path of length `≤ n` from `q` to `p`
  (`reachIn_iff_relatesWithinSteps`: it is `Relation.RelatesWithinSteps G.Adj q p n`).
* `MADLe G α` : every ancestor of every node is at distance `≤ α`, i.e. `α ≥ MAD` (the maximum
  ancestor distance); `mad G` is the least such `α`.
* `IsSourceComponent` : `Digraph.IsSourceComponent` (compatibility abbreviation).
-/

namespace Podc.AtomicState

open Relation

variable {V : Type*} (G : Digraph V)

/-- `q` is an ancestor of `p`: there is a (possibly empty) directed path from `q` to `p`. -/
abbrev Anc (q p : V) : Prop := G.Reachable q p

/-- `ReachIn G n q p`: there is a directed path of length at most `n` from `q` to `p`. -/
def ReachIn : ℕ → V → V → Prop
  | 0, q, p => q = p
  | n + 1, q, p => ReachIn n q p ∨ ∃ r, ReachIn n q r ∧ G.Adj r p

/-- `α ≥ MAD`: every ancestor `q` of every node `p` satisfies `‖q, p‖ ≤ α`. -/
def MADLe (α : ℕ) : Prop := ∀ q p, Anc G q p → ReachIn G α q p

/-- A source component (compatibility abbreviation for `Digraph.IsSourceComponent`). -/
abbrev IsSourceComponent (S : Set V) : Prop := G.IsSourceComponent S

variable {G}

@[deprecated Digraph.Reachable.refl (since := "2026-10-17")]
theorem Anc.refl (p : V) : Anc G p p := Digraph.Reachable.refl p

@[deprecated Digraph.Reachable.trans (since := "2026-10-17")]
theorem Anc.trans {a b c : V} (h₁ : Anc G a b) (h₂ : Anc G b c) : Anc G a c :=
  Digraph.Reachable.trans h₁ h₂

@[deprecated Digraph.Adj.reachable (since := "2026-10-17")]
theorem Anc.of_adj {a b : V} (h : G.Adj a b) : Anc G a b := h.reachable

@[deprecated Digraph.Reachable.tail (since := "2026-10-17")]
theorem Anc.tail {a b c : V} (h₁ : Anc G a b) (h₂ : G.Adj b c) : Anc G a c :=
  Digraph.Reachable.tail h₁ h₂

theorem reachIn_zero {q p : V} : ReachIn G 0 q p ↔ q = p := Iff.rfl

theorem reachIn_succ {n : ℕ} {q p : V} :
    ReachIn G (n + 1) q p ↔ ReachIn G n q p ∨ ∃ r, ReachIn G n q r ∧ G.Adj r p := Iff.rfl

/-- `ReachIn` is the bounded-walk relation `Relation.RelatesWithinSteps` of the arcs. -/
theorem reachIn_iff_relatesWithinSteps {n : ℕ} {q p : V} :
    ReachIn G n q p ↔ RelatesWithinSteps G.Adj q p n := by
  induction n generalizing p with
  | zero => simp [reachIn_zero]
  | succ n ih => simp only [reachIn_succ, relatesWithinSteps_succ_iff, ih]

theorem ReachIn.refl (n : ℕ) (p : V) : ReachIn G n p p :=
  reachIn_iff_relatesWithinSteps.2 (RelatesWithinSteps.mono n.zero_le (RelatesWithinSteps.refl p))

theorem ReachIn.mono {n m : ℕ} {q p : V} (h : ReachIn G n q p) (hnm : n ≤ m) : ReachIn G m q p :=
  reachIn_iff_relatesWithinSteps.2 (RelatesWithinSteps.mono hnm (reachIn_iff_relatesWithinSteps.1 h))

theorem ReachIn.tail {n : ℕ} {q r p : V} (h : ReachIn G n q r) (hr : G.Adj r p) :
    ReachIn G (n + 1) q p := Or.inr ⟨r, h, hr⟩

theorem ReachIn.anc {n : ℕ} {q p : V} (h : ReachIn G n q p) : Anc G q p :=
  (reachIn_iff_relatesWithinSteps.1 h).reflTransGen

theorem Anc.exists_reachIn {q p : V} (h : Anc G q p) : ∃ n, ReachIn G n q p :=
  let ⟨n, h⟩ := Digraph.reachable_iff_exists_relatesWithinSteps.1 h
  ⟨n, reachIn_iff_relatesWithinSteps.2 h⟩

theorem anc_iff_exists_reachIn {q p : V} : Anc G q p ↔ ∃ n, ReachIn G n q p :=
  ⟨Anc.exists_reachIn, fun ⟨_, h⟩ => h.anc⟩

/-- A path of length `≤ n + 1` that is not of length `≤ n` ends with an arc. -/
theorem ReachIn.exists_pred_of_not {n : ℕ} {q p : V} (h : ReachIn G (n + 1) q p)
    (hn : ¬ ReachIn G n q p) : ∃ r, ReachIn G n q r ∧ G.Adj r p :=
  h.resolve_left hn

theorem MADLe.mono {α β : ℕ} (h : MADLe G α) (hαβ : α ≤ β) : MADLe G β :=
  fun q p hqp => (h q p hqp).mono hαβ

/-- Paths in a finite digraph can be shortened to length `≤ |V| - 1`; we only need `≤ |V|`. -/
theorem ReachIn.of_card [Fintype V] {n : ℕ} {q p : V} (h : ReachIn G n q p) :
    ReachIn G (Fintype.card V) q p :=
  reachIn_iff_relatesWithinSteps.2
    (RelatesWithinSteps.mono (Nat.sub_le _ _) (Digraph.Reachable.relatesWithinSteps h.anc))

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

/-! ### Source components (compatibility names) -/

@[deprecated Digraph.mem_of_reachable_of_closed +typeChanged (since := "2026-10-17")]
theorem mem_of_anc_of_closed {S : Set V} (hS : ∀ p ∈ S, ∀ q, G.Adj q p → q ∈ S) {x p : V}
    (h : Anc G x p) (hp : p ∈ S) : x ∈ S :=
  Digraph.mem_of_reachable_of_closed hS h hp

@[deprecated Digraph.isSourceComponent_iff (since := "2026-10-17")]
theorem isSourceComponent_iff {S : Set V} :
    IsSourceComponent G S ↔ ∃ r, S = {x | Anc G x r} ∧ ∀ x, Anc G x r → Anc G r x :=
  Digraph.isSourceComponent_iff

@[deprecated Digraph.IsSourceComponent.eq_setOf_reachable +typeChanged (since := "2026-10-17")]
theorem IsSourceComponent.eq_anc {S : Set V} (hS : IsSourceComponent G S) {r : V} (hr : r ∈ S) :
    S = {x | Anc G x r} :=
  Digraph.IsSourceComponent.eq_setOf_reachable hS hr

@[deprecated Digraph.IsSourceComponent.reachable +typeChanged (since := "2026-10-17")]
theorem IsSourceComponent.anc_of_mem {S : Set V} (hS : IsSourceComponent G S) {p q : V}
    (hp : p ∈ S) (hq : q ∈ S) : Anc G p q :=
  Digraph.IsSourceComponent.reachable hS hp hq

@[deprecated Digraph.exists_isSourceComponent_subset (since := "2026-10-17")]
theorem exists_sourceComponent_subset_anc [Finite V] (p : V) :
    ∃ S, IsSourceComponent G S ∧ S ⊆ {x | Anc G x p} :=
  Digraph.exists_isSourceComponent_subset p

@[deprecated Digraph.exists_isSourceComponent (since := "2026-10-17")]
theorem exists_sourceComponent [Finite V] [Nonempty V] : ∃ S, IsSourceComponent G S :=
  Digraph.exists_isSourceComponent

@[deprecated Digraph.subset_setOf_reachable_of_unique +typeChanged (since := "2026-10-17")]
theorem subset_anc_of_unique [Finite V] {SC : Set V} (_hSC : IsSourceComponent G SC)
    (huniq : ∀ S, IsSourceComponent G S → S = SC) (p : V) : SC ⊆ {x | Anc G x p} :=
  Digraph.subset_setOf_reachable_of_unique huniq p

end Podc.AtomicState
