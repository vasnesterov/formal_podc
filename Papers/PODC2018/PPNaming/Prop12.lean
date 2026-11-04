import Papers.PODC2018.PPNaming.Model
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Defs

/-!
# Proposition 12: asymmetric self-stabilizing naming with `P` states, without leader

Burman, Beauquier, Sohier, *Space-Optimal Naming in Population Protocols*, Proposition 12.

The protocol has states `Fin P` and the single (asymmetric) rule `(s, s) → (s, s + 1 mod P)`.
For every population of size `n ≤ P`, from any initial configuration, every weakly fair and every
globally fair execution solves naming (`prop12_solvesWeak`, `prop12_solvesGlobal`).

Proof: a natural-number potential strictly decreases at every non-null step
(`prop12_pot_lt`). Instead of the paper's lexicographic pair (number of holes, hole distance) we
use the single sum `∑_{holes h} ∑_{agents x} ((h - C x) mod P)`: the set of holes can only shrink,
and for every remaining hole `h` the distance of the moving agent to `h` drops by one.
Hence only finitely many non-null steps occur (`eventually_const_of_potential`); in the final
constant configuration, a remaining pair of homonyms would make a non-null step when it interacts
(weak fairness), and from every configuration a configuration without homonyms (which is silent)
is reachable (global fairness).
-/

namespace Podc.PPNaming

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

-- CSLib candidate (general fact about executions; e.g. `Cslib/.../PopulationProtocols/Basic.lean`)
/-- **Potential argument.** If at every step of an execution the configuration either does not
change or a natural-number potential strictly decreases, then the configuration is eventually
constant. -/
theorem eventually_const_of_potential {Q Ag : Type*} [DecidableEq Ag] {P : Protocol Q}
    (E : P.Execution Ag) (V : Config Ag Q → ℕ)
    (h : ∀ t, E.config (t + 1) = E.config t ∨ V (E.config (t + 1)) < V (E.config t)) :
    ∃ T, ∀ t ≥ T, E.config t = E.config T := by
  classical
  have hex : ∃ v, ∃ t, V (E.config t) = v := ⟨_, 0, rfl⟩
  obtain ⟨T, hT⟩ := Nat.find_spec hex
  have hmin : ∀ t, Nat.find hex ≤ V (E.config t) := fun t => Nat.find_min' hex ⟨t, rfl⟩
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rcases h t with h | h
    · rw [h, ih]
    · have := hmin (t + 1); rw [ih] at h; omega

variable {P : ℕ} [NeZero P]

/-- The asymmetric protocol of Proposition 12: `(s, s) → (s, s + 1 mod P)`, all other
interactions are null. -/
def prop12Protocol (P : ℕ) [NeZero P] : Protocol (Fin P) where
  δ p q := if p = q then (p, q + 1) else (p, q)

section

variable {A : Type*} [DecidableEq A]

lemma prop12_interact (C : Config A (Fin P)) {a b : A} (hab : a ≠ b) :
    (prop12Protocol P).interact C a b =
      if C a = C b then Function.update C b (C b + 1) else C := by
  funext x
  by_cases hxa : x = a
  · subst hxa; split_ifs with h <;> simp [Protocol.interact, prop12Protocol, h, hab]
  · by_cases hxb : x = b
    · subst hxb; split_ifs with h <;> simp [Protocol.interact, prop12Protocol, h, hxa]
    · split_ifs <;> simp [Protocol.interact, hxa, hxb]

/-- The holes of a configuration: the states held by no agent. -/
def holes [Fintype A] (C : Config A (Fin P)) : Finset (Fin P) :=
  Finset.univ.filter fun h => ∀ x, C x ≠ h

/-- The potential: for every hole `h`, the sum over all agents of the distance to `h`
(`(h - C x) mod P`). -/
def prop12Pot [Fintype A] (C : Config A (Fin P)) : ℕ :=
  ∑ h ∈ holes C, ∑ x, (h - C x).val

lemma Fin.val_sub_add_one_lt {h v : Fin P} (hv : h ≠ v) : (h - (v + 1)).val < (h - v).val := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 1 := ⟨P - 1, (Nat.sub_add_cancel (NeZero.one_le)).symm⟩
  have e : h - (v + 1) = (h - v) - 1 := sub_add_eq_sub_sub _ _ _
  have hne : h - v ≠ 0 := sub_ne_zero.2 hv
  rw [e, Fin.coe_sub_one]; simp only [hne, ↓reduceIte]
  have := Fin.pos_iff_ne_zero.2 hne
  omega

lemma prop12_pot_lt [Fintype A] (hA : Fintype.card A ≤ P) {C : Config A (Fin P)} {a b : A}
    (hab : a ≠ b) (heq : C a = C b) :
    prop12Pot (Function.update C b (C b + 1)) < prop12Pot C := by
  set C' := Function.update C b (C b + 1)
  have hsub : holes C' ⊆ holes C := by
    intro h hh
    simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    intro x hx
    by_cases hxb : x = b
    · subst hxb; apply hh a; simp [C', hab, heq, hx]
    · apply hh x; simp [C', hxb, hx]
  have hne : (holes C).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hsurj : Function.Surjective C := by
      intro h
      by_contra hh
      push Not at hh
      have : h ∈ holes C := by simp [holes, hh]
      simp [hemp] at this
    have hcard : Fintype.card A = Fintype.card (Fin P) :=
      le_antisymm (by simpa using hA) (Fintype.card_le_of_surjective _ hsurj)
    have hinj : Function.Injective C :=
      (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).2 hsurj
    exact hab (hinj heq)
  have hlt : ∀ h ∈ holes C, ∑ x, (h - C' x).val < ∑ x, (h - C x).val := by
    intro h hh
    simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    apply Finset.sum_lt_sum
    · intro x _
      by_cases hxb : x = b
      · subst hxb; simp only [C', Function.update_self]
        exact (Fin.val_sub_add_one_lt (Ne.symm (hh x))).le
      · simp [C', hxb]
    · exact ⟨b, Finset.mem_univ _, by
        simp only [C', Function.update_self]; exact Fin.val_sub_add_one_lt (Ne.symm (hh b))⟩
  calc prop12Pot C' = ∑ h ∈ holes C', ∑ x, (h - C' x).val := rfl
    _ ≤ ∑ h ∈ holes C, ∑ x, (h - C' x).val :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ < ∑ h ∈ holes C, ∑ x, (h - C x).val := Finset.sum_lt_sum_of_nonempty hne hlt
    _ = prop12Pot C := rfl

lemma prop12_step [Fintype A] (hA : Fintype.card A ≤ P) (C : Config A (Fin P)) {a b : A}
    (hab : a ≠ b) :
    (prop12Protocol P).interact C a b = C ∨
      prop12Pot ((prop12Protocol P).interact C a b) < prop12Pot C := by
  rw [prop12_interact C hab]
  split_ifs with h
  · exact Or.inr (prop12_pot_lt hA hab h)
  · exact Or.inl rfl

lemma add_one_ne_self_of_two_le (hP : 2 ≤ P) (v : Fin P) : v + 1 ≠ v := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 2 := ⟨P - 2, by omega⟩
  intro h
  have := congrArg (· - v) h
  simp at this

/-- A configuration without homonyms is silent: every interaction is null. -/
lemma prop12_interact_of_injective {C : Config A (Fin P)} (hC : Function.Injective C) {a b : A}
    (hab : a ≠ b) : (prop12Protocol P).interact C a b = C := by
  rw [prop12_interact C hab]; simp only [show C a ≠ C b from fun h => hab (hC h), ↓reduceIte]

lemma prop12_stablyNamed {C : Config A (Fin P)} (hC : Function.Injective C) :
    StablyNamed (prop12Protocol P) (nameOut id) C := by
  refine ⟨hC, fun D hD => ?_⟩
  have : D = C := by
    induction hD with
    | refl => rfl
    | tail _ hst ih =>
      obtain ⟨a, b, hab, rfl⟩ := hst
      subst ih
      exact prop12_interact_of_injective hC hab
  rw [this]

/-- From every configuration, a configuration without homonyms (hence stably named) is
reachable. -/
lemma prop12_reach_named [Fintype A] (hA : Fintype.card A ≤ P) (C : Config A (Fin P)) :
    ∃ D, (prop12Protocol P).Reachable C D ∧ StablyNamed (prop12Protocol P) (nameOut id) D := by
  induction hV : prop12Pot C using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    by_cases hinj : Function.Injective C
    · exact ⟨C, .refl, prop12_stablyNamed hinj⟩
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨a, b, heq, hab⟩ := hinj
      have hlt := prop12_pot_lt hA hab heq
      obtain ⟨D, hD, hDs⟩ := ih _ (hV ▸ hlt) _ rfl
      refine ⟨D, Relation.ReflTransGen.head ⟨a, b, hab, ?_⟩ hD, hDs⟩
      rw [prop12_interact C hab]; simp [heq]

end

/-- **Proposition 12** of [Burman–Beauquier–Sohier] (weak fairness). The asymmetric protocol
`(s, s) → (s, s + 1 mod P)` with `P` states solves naming without leader and without
initialization (from every configuration) for every population of size at most `P`, under weak
fairness. -/
theorem prop12_solvesWeak (A : Type*) [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ P) :
    SolvesWeak (prop12Protocol P) (Set.univ : Set (Config A (Fin P))) (nameOut id) := by
  intro E _ hE
  obtain ⟨T, hT⟩ := eventually_const_of_potential E prop12Pot fun t => by
    rw [E.step t]; exact prop12_step hA _ (E.sched_ne t)
  refine ⟨T, ?_, fun t ht => by simp [hT t ht]⟩
  show Function.Injective (E.config T)
  by_contra hinj
  simp only [Function.Injective, not_forall] at hinj
  obtain ⟨a, b, heq, hab⟩ := hinj
  have h2 : 2 ≤ P := le_trans (Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩) hA
  -- a non-null interaction of the homonyms `a`, `b`
  have hnn : ∀ x y, x ≠ y → E.config T x = E.config T y →
      (prop12Protocol P).interact (E.config T) x y ≠ E.config T := by
    intro x y hxy hxy' h
    rw [prop12_interact _ hxy] at h; simp only [hxy', ↓reduceIte] at h
    have := congrFun h y
    simp only [Function.update_self] at this
    exact add_one_ne_self_of_two_le h2 _ this
  obtain ⟨t, ht, hs⟩ := hE a b hab T
  have hstep := E.step t
  rw [hT t ht, hT (t + 1) (by omega)] at hstep
  rcases hs with hs | hs <;> rw [hs] at hstep
  · exact hnn a b hab heq hstep.symm
  · exact hnn b a (Ne.symm hab) heq.symm hstep.symm

/-- **Proposition 12** of [Burman–Beauquier–Sohier] (global fairness). The same protocol solves
naming without leader and without initialization under global fairness. -/
theorem prop12_solvesGlobal (A : Type*) [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ P) :
    SolvesGlobal (prop12Protocol P) (Set.univ : Set (Config A (Fin P))) (nameOut id) := by
  intro E hE0 hE
  exact stabilizes_of_globallyFair (fun _ _ C _ => prop12_reach_named hA C) E hE0 hE

/-- Sanity check: the protocol of Proposition 12 is not symmetric (for `P ≥ 2`). -/
theorem prop12_not_isSymmetric (hP : 2 ≤ P) : ¬ IsSymmetric (prop12Protocol P) := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 2 := ⟨P - 2, by omega⟩
  intro h
  have := congrArg Prod.fst (h 0 0)
  simp [prop12Protocol] at this

end Podc.PPNaming
