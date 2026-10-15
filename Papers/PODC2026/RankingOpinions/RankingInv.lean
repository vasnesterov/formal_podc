import Papers.PODC2026.RankingOpinions.RankingSteps
import Papers.PODC2026.RankingOpinions.Dynamics

/-!
# The Ranking protocol: global invariants (Lemma 6.7)

Every configuration reachable from the initial configuration satisfies:
* the bra color of every agent is its input color;
* the multiset of ket colors is the multiset of input colors;
* every color has at least one token (on a ket of that color);
* every state is normal (self-synchronised).
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Ranking

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Finset

variable {k : ℕ} [NeZero k] {A : Type*} [DecidableEq A] [Fintype A]

/-- The initial configuration (rule (1)). -/
def initConfig (input : A → Fin k) : Config A (RState k) := fun a => initState (input a)

/-- The multiset of ket colors. -/
def kcs (C : Config A (RState k)) : Multiset (Fin k) := univ.val.map fun a => (C a).kc

/-- Global invariants of reachable configurations (Lemma 6.7). -/
structure Inv (input : A → Fin k) (C : Config A (RState k)) : Prop where
  bc : ∀ a, (C a).bc = input a
  kc : kcs C = univ.val.map input
  tok : ∀ c, ∃ a, (C a).tok ∧ (C a).kc = c
  normal : ∀ a, Normal (C a)

lemma interact_apply (C : Config A (RState k)) (a b x : A) :
    (ranking k).interact C a b x =
      if x = a then (rδ (C a) (C b)).1 else if x = b then (rδ (C a) (C b)).2 else C x := rfl

lemma kcs_interact (C : Config A (RState k)) (a b : A) :
    kcs ((ranking k).interact C a b) = kcs C := by
  have hp := rδ_inv (C a) (C b)
  rcases hp.kc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · unfold kcs; congr 1; funext x
    rw [interact_apply]; split_ifs with hx hx'
    · rw [hx, h1]
    · rw [hx', h2]
    · rfl
  · have : (fun x => ((ranking k).interact C a b x).kc) =
        (fun x => (C x).kc) ∘ Equiv.swap a b := by
      funext x
      simp only [Function.comp, interact_apply]
      split_ifs with hx hx'
      · rw [hx, h1, Equiv.swap_apply_left]
      · rw [hx', h2, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
    unfold kcs; rw [this, ← Multiset.map_map, Multiset.map_univ_val_equiv]

lemma Inv.step {input : A → Fin k} {C C' : Config A (RState k)} (hC : Inv input C)
    (h : (ranking k).Step C C') : Inv input C' := by
  obtain ⟨a, b, hab, rfl⟩ := h
  have hp := rδ_inv (C a) (C b)
  have hn := rδ_normal (C a) (C b)
  refine ⟨fun x => ?_, by rw [kcs_interact C a b, hC.kc], fun c => ?_, fun x => ?_⟩
  · rw [interact_apply]; split_ifs with hx hx'
    · rw [hp.bc1, hx, hC.bc]
    · rw [hp.bc2, hx', hC.bc]
    · exact hC.bc x
  · obtain ⟨x, hx⟩ := hC.tok c
    by_cases hxa : x = a
    · subst hxa
      rcases hp.tok c (Or.inl hx) with h' | h'
      · exact ⟨x, by rw [interact_apply, ite_eq_left rfl]; exact h'⟩
      · exact ⟨b, by rw [interact_apply, ite_eq_right (Ne.symm hab), ite_eq_left rfl]; exact h'⟩
    by_cases hxb : x = b
    · subst hxb
      rcases hp.tok c (Or.inr hx) with h' | h'
      · exact ⟨a, by rw [interact_apply, ite_eq_left rfl]; exact h'⟩
      · exact ⟨x, by rw [interact_apply, ite_eq_right (Ne.symm hab), ite_eq_left rfl]; exact h'⟩
    · exact ⟨x, by rw [interact_apply, ite_eq_right hxa, ite_eq_right hxb]; exact hx⟩
  · rw [interact_apply]; split_ifs
    · exact hn.1
    · exact hn.2
    · exact hC.normal x

lemma Inv.reachable {input : A → Fin k} {C C' : Config A (RState k)} (hC : Inv input C)
    (h : (ranking k).Reachable C C') : Inv input C' := by
  induction h with
  | refl => exact hC
  | tail _ hst ih => exact ih.step hst

/-- Lemma 6.7 needs every color to be present. -/
lemma inv_init (input : A → Fin k) (hall : ∀ c, ∃ a, input a = c) :
    Inv input (initConfig input) where
  bc _ := rfl
  kc := rfl
  tok c := by obtain ⟨a, ha⟩ := hall c; exact ⟨a, rfl, ha⟩
  normal _ _ _ := rfl

/-! ### Updating a pair of agents -/

/-- The configuration after the interaction `a, b` when `rδ (C a) (C b) = (s, t)`. -/
lemma interact_eq {C : Config A (RState k)} {a b : A} {s t : RState k}
    (h : rδ (C a) (C b) = (s, t)) :
    (ranking k).interact C a b = fun x => if x = a then s else if x = b then t else C x := by
  funext x; rw [interact_apply, h]

lemma step_of {C : Config A (RState k)} {a b : A} (hab : a ≠ b) :
    (ranking k).Reachable C ((ranking k).interact C a b) :=
  Relation.ReflTransGen.single ⟨a, b, hab, rfl⟩

end RankingOpinions.Ranking
