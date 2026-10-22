import Podc.Computability.Distributed.DistributedAutomata.Fairness

/-!
# Labelled stars

The proofs of Lemmas 3.4 and 3.5 work on *stars*: a centre `none` adjacent to the leaves
`some l`, `l : L`. Every admissible graph has a star with the same label count
(`exists_star`), so a labelling property is determined by its values on stars.
-/

namespace Podc.WeakAsyncDecisionPower

open Cslib.DistributedAutomata Set

variable {Λ Q : Type*}

/-- The star with centre `none` and leaves `some l`. -/
def starG (L : Type*) : SimpleGraph (Option L) :=
  SimpleGraph.fromRel fun a b => a = none ∧ b ≠ none

variable {L : Type*}

lemma starG_adj {a b : Option L} :
    (starG L).Adj a b ↔ (a = none ∧ b ≠ none) ∨ (b = none ∧ a ≠ none) := by
  simp only [starG, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h | h <;> exact h.2 h.1

@[simp] lemma starG_adj_none_some (l : L) : (starG L).Adj none (some l) := by
  simp [starG_adj]

@[simp] lemma starG_adj_some_none (l : L) : (starG L).Adj (some l) none := by
  simp [starG_adj]

@[simp] lemma starG_not_adj_some_some (l l' : L) : ¬ (starG L).Adj (some l) (some l') := by
  simp [starG_adj]

lemma starG_nbr_some (l : L) : {u | (starG L).Adj (some l) u} = {none} := by
  ext u; cases u <;> simp

lemma starG_nbr_none : {u | (starG L).Adj (none : Option L) u} = range some := by
  ext u; cases u <;> simp

/-- A labelled star: centre label `c`, leaf labels `lab`. -/
@[reducible] def starL (L : Type) [Finite L] (c : Λ) (lab : L → Λ) : LGraph Λ where
  V := Option L
  graph := starG L
  label := fun o => o.elim c lab

lemma starL_admissible {L : Type} [Finite L] (c : Λ) (lab : L → Λ) (hL : 2 ≤ Nat.card L) :
    (starL L c lab).Admissible ⊤ where
  connected := by
    have hne : Nonempty L := by
      by_contra h; rw [not_nonempty_iff] at h; rw [Nat.card_of_isEmpty] at hL; omega
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨none, fun u => ?_⟩
    cases u with
    | none => exact SimpleGraph.Reachable.refl _
    | some l => exact (starG_adj_none_some l).reachable
  three_le := by
    show 3 ≤ Nat.card (Option L)
    rw [Finite.card_option]; omega
  degree_le := fun _ => le_top

lemma ncard_option {L : Type*} [Finite L] (p : Option L → Prop) [Decidable (p none)] :
    {o | p o}.ncard = (if p none then 1 else 0) + {l | p (some l)}.ncard := by
  have hdisj : Disjoint {o : Option L | o = none ∧ p o} (some '' {l | p (some l)}) := by
    rw [Set.disjoint_left]; rintro o ⟨rfl, -⟩ ⟨l, -, h⟩; cases h
  have : {o | p o} = {o : Option L | o = none ∧ p o} ∪ some '' {l | p (some l)} := by
    ext o; cases o <;> simp
  rw [this, ncard_union_eq hdisj (toFinite _) (toFinite _),
    ncard_image_of_injective _ (Option.some_injective L)]
  congr 1
  split_ifs with h
  · rw [show {o : Option L | o = none ∧ p o} = {none} by ext o; cases o <;> simp [h]]; simp
  · rw [show {o : Option L | o = none ∧ p o} = ∅ by ext o; cases o <;> simp [h]]; simp

lemma starL_count {L : Type} [Finite L] (c : Λ) (lab : L → Λ) (ℓ : Λ) [Decidable (c = ℓ)] :
    (starL L c lab).count ℓ = (if c = ℓ then 1 else 0) + {l | lab l = ℓ}.ncard := by
  simp only [LGraph.count, starL]
  exact @ncard_option _ _ (fun o => o.elim c lab = ℓ) (inferInstanceAs (Decidable (c = ℓ)))

/-- Label-preserving bijections preserve label counts. -/
lemma count_eq_of_equiv {G H : LGraph Λ} (e : G.V ≃ H.V) (he : ∀ v, H.label (e v) = G.label v) :
    G.count = H.count := by
  funext ℓ
  simp only [LGraph.count]
  rw [← ncard_image_of_injective _ e.injective]
  congr 1
  ext w
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩; rw [he, hv]
  · intro hw; exact ⟨e.symm w, by rw [← he, e.apply_symm_apply, hw], e.apply_symm_apply w⟩

/-- Every admissible graph has a star with the same label count (and the same number of nodes),
with an arbitrary node as centre. -/
lemma exists_star {k : ℕ∞} {G : LGraph Λ} (hG : G.Admissible k) (v₀ : G.V) :
    ∃ (L : Type) (_ : Finite L) (lab : L → Λ), 2 ≤ Nat.card L ∧ Nat.card L + 1 = Nat.card G.V ∧
      (starL L (G.label v₀) lab).count = G.count := by
  classical
  have hcard : Nat.card {v // v ≠ v₀} + 1 = Nat.card G.V := by
    rw [← Finite.card_option]; exact Nat.card_congr (Equiv.optionSubtypeNe v₀)
  refine ⟨{v // v ≠ v₀}, inferInstance, fun v => G.label v.1, ?_, hcard, ?_⟩
  · have h := hG.three_le
    omega
  · refine count_eq_of_equiv (Equiv.optionSubtypeNe v₀) fun o => ?_
    cases o <;> rfl

end Podc.WeakAsyncDecisionPower
