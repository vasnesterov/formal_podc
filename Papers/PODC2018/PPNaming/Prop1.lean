import Papers.PODC2018.PPNaming.Basic

/-!
# Proposition 1: no symmetric naming without leader under weak fairness

In a population of even size, starting from a uniform configuration, the scheduler lets the
agents interact along perfect matchings: by symmetry the configuration stays uniform forever,
and choosing for each pair of agents a perfect matching containing it makes the execution weakly
fair (`exists_weaklyFair_of_phases`). The number of states is arbitrary (even infinite).
-/

namespace Podc.PPNaming

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {Q A N : Type*} [DecidableEq A]

/-- The agents occurring in a list of pairs. -/
def pairAgents (l : List (A × A)) : List A := l.flatMap fun p => [p.1, p.2]

lemma mem_pairAgents {l : List (A × A)} {x : A} :
    x ∈ pairAgents l ↔ ∃ p ∈ l, x = p.1 ∨ x = p.2 := by
  simp [pairAgents, List.mem_flatMap, eq_comm]

/-- Every finite set of even size has a perfect matching (as a list of pairs). -/
lemma exists_matching (T : Finset A) (hT : Even T.card) :
    ∃ l : List (A × A), (pairAgents l).Nodup ∧ ∀ x, x ∈ pairAgents l ↔ x ∈ T := by
  induction h : T.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨[], by simp [pairAgents], by simp [pairAgents]⟩
    have h1 : 1 ≤ (T.erase x).card := by
      have hc := Finset.card_erase_of_mem hx
      rcases hT with ⟨k, hk⟩
      have : 0 < T.card := Finset.card_pos.2 ⟨x, hx⟩
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.1 h1
    have hyx : y ≠ x := Finset.ne_of_mem_erase hy
    set T' := (T.erase x).erase y with hT'
    have hcard : T'.card + 2 = T.card := by
      have e1 := Finset.card_erase_of_mem hx
      have e2 := Finset.card_erase_of_mem hy
      rw [hT']; omega
    obtain ⟨l, hnd, hmem⟩ := ih T'.card (by omega) T'
      (by rw [← hcard] at hT; simpa [Nat.even_add] using hT) rfl
    refine ⟨(x, y) :: l, ?_, fun z => ?_⟩
    · have hxl : x ∉ pairAgents l := fun h => by simpa [hT'] using (hmem x).1 h
      have hyl : y ∉ pairAgents l := fun h => by simpa [hT'] using (hmem y).1 h
      simp only [pairAgents, List.flatMap_cons, List.cons_append, List.nil_append,
        List.nodup_cons, List.mem_cons] at hnd ⊢
      exact ⟨by simpa [pairAgents, hyx.symm] using hxl, by simpa [pairAgents] using hyl, hnd⟩
    · have := hmem z
      simp only [pairAgents, List.flatMap_cons, List.cons_append, List.nil_append,
        List.mem_cons] at this ⊢
      rw [this, hT']
      simp only [Finset.mem_erase]
      constructor
      · rintro (rfl | rfl | ⟨-, -, h⟩) <;> first | exact hx | exact Finset.mem_of_mem_erase hy | exact h
      · intro hz
        by_cases hzx : z = x
        · exact Or.inl hzx
        · by_cases hzy : z = y
          · exact Or.inr (Or.inl hzy)
          · exact Or.inr (Or.inr ⟨hzy, hzx, hz⟩)

lemma ne_of_nodup_pairAgents {l : List (A × A)} (hnd : (pairAgents l).Nodup) :
    ∀ p ∈ l, p.1 ≠ p.2 := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [pairAgents, List.flatMap_cons, List.cons_append, List.nil_append,
      List.nodup_cons, List.mem_cons] at hnd
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact fun h => hnd.1 (Or.inl h)
    · exact ih hnd.2.2 p hp

/-- Running a matching of agents all in state `s` puts them all in state `(δ s s).1`. -/
lemma runList_matching {P : Protocol Q} (hs : IsSymmetric P) (s : Q) (l : List (A × A))
    (hnd : (pairAgents l).Nodup) (C : Config A Q) (hC : ∀ x ∈ pairAgents l, C x = s) (x : A) :
    P.runList l C x = if x ∈ pairAgents l then (P.δ s s).1 else C x := by
  induction l generalizing C with
  | nil => simp [pairAgents]
  | cons p l ih =>
    simp only [pairAgents, List.flatMap_cons, List.cons_append, List.nil_append,
      List.nodup_cons, List.mem_cons] at hnd hC ⊢
    obtain ⟨hp1, hp2, hnd⟩ := hnd
    have hne : p.1 ≠ p.2 := fun h => hp1 (Or.inl h)
    have hp1' : p.1 ∉ pairAgents l := fun h => hp1 (Or.inr h)
    rw [runList_cons, ih hnd]
    · have h1 := hC p.1 (Or.inl rfl)
      have h2 := hC p.2 (Or.inr (Or.inl rfl))
      by_cases hx1 : x = p.1
      · subst hx1; simp [hp1', h1, h2]
      · by_cases hx2 : x = p.2
        · subst hx2; simp [hp2, h1, h2, hs.diag, hne]
        · simp only [Protocol.interact, hx1, hx2, if_false, false_or]; rfl
    · intro y hy
      have hy1 : y ≠ p.1 := fun h => hp1' (h ▸ hy)
      have hy2 : y ≠ p.2 := fun h => hp2 (h ▸ hy)
      rw [interact_other _ _ hy1 hy2]
      exact hC y (Or.inr (Or.inr hy))

/-- **Proposition 1.** Without leader, under weak fairness, no symmetric protocol (with any
number of states) solves naming in a population of even size `n ≥ 2`, even if all agents are
initialized to the same state. -/
theorem prop1 [Fintype A] (hA : Even (Fintype.card A)) (h2 : 2 ≤ Fintype.card A)
    (P : Protocol Q) (hs : IsSymmetric P) (name : Q → N) (q₀ : Q) :
    ¬ SolvesWeak P ({fun _ => q₀} : Set (Config A Q)) (nameOut name) := by
  intro h
  obtain ⟨a₀, b₀, hab₀⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  let G : Config A Q → Prop := fun C => ∃ s, C = fun _ => s
  let R : Config A Q → Config A Q → Prop := fun C _ => HasHomonyms C
  have hph : ∀ C, G C → ∀ a b, a ≠ b → ∃ C₁ C₂, P.Reachable C C₁ ∧
      P.Reachable (P.interact C₁ a b) C₂ ∧ G C₂ ∧ R C C₂ := by
    rintro C ⟨s, rfl⟩ a b hab
    have hcard : Even ((Finset.univ.erase a).erase b).card := by
      rw [Finset.card_erase_of_mem (by simp [Ne.symm hab]), Finset.card_erase_of_mem (by simp)]
      rcases hA with ⟨k, hk⟩
      rw [Finset.card_univ, hk]
      exact ⟨k - 1, by omega⟩
    obtain ⟨l, hnd, hmem⟩ := exists_matching _ hcard
    have hnd' : (pairAgents ((a, b) :: l)).Nodup := by
      simp only [pairAgents, List.flatMap_cons, List.cons_append, List.nil_append,
        List.nodup_cons, List.mem_cons]
      refine ⟨?_, ?_, hnd⟩
      · rintro (h | h)
        · exact hab h
        · simpa using (hmem a).1 h
      · intro h; simpa using (hmem b).1 h
    have hl := ne_of_nodup_pairAgents hnd'
    have hrun := runList_matching (P := P) hs s ((a, b) :: l) hnd' (fun _ => s) (fun _ _ => rfl)
    · refine ⟨fun _ => s, P.runList l (P.interact (fun _ => s) a b), .refl,
        P.reachable_runList (fun p hp => hl p (List.mem_cons_of_mem _ hp)) _,
        ⟨(P.δ s s).1, funext fun x => ?_⟩, hasHomonyms_const h2 s⟩
      have := hrun x
      rw [runList_cons] at this
      rw [this]
      have : x ∈ pairAgents ((a, b) :: l) := by
        simp only [pairAgents, List.flatMap_cons, List.cons_append, List.nil_append,
          List.mem_cons]
        by_cases hxa : x = a
        · exact Or.inl hxa
        · by_cases hxb : x = b
          · exact Or.inr (Or.inl hxb)
          · exact Or.inr (Or.inr ((hmem x).2 (by simp [hxa, hxb])))
      simp [this]
  obtain ⟨E, hE0, hEf, hinf⟩ := P.exists_weaklyFair_of_phases G R hph .refl ⟨q₀, rfl⟩ hab₀
  obtain ⟨T, hgT, hT⟩ := h E (by rw [hE0]; rfl) hEf
  obtain ⟨t, ht, t', ht', hG, hR⟩ := hinf T
  apply not_injective_of_hasHomonyms (name := name) hR
  have := hT t ht
  change Function.Injective (nameOut name (E.config t))
  rw [this]; exact hgT

end Podc.PPNaming
