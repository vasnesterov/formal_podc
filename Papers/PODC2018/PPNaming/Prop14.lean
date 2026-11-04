import Papers.PODC2018.PPNaming.Prop12

/-!
# Proposition 14: symmetric naming with an initialized leader and `P` states

Burman, Beauquier, Sohier, *Space-Optimal Naming in Population Protocols*, Proposition 14.

`P = k + 1` mobile states `Fin (k + 1)`; mobile agents start in `Fin.last k` (the paper's state
`P`), the leader holds a counter in `Fin (k + 1)` starting at `0`. When the leader (counter `c`)
meets an agent in state `Fin.last k` and `c < Fin.last k`, the agent takes the name `c` and the
counter is incremented; every other interaction is null (in particular all mobile-mobile ones).
The rules do not depend on who initiates (`prop14_symmetric`).

Invariant (`Inv14`): the agents not in `Fin.last k` hold pairwise distinct names `< c`, and there
are exactly `c` of them. The counter increases at every non-null step, so the configuration is
eventually constant; once it is constant, no agent in `Fin.last k` can be named any more, which by
the invariant forces `c = Fin.last k` and then at most one agent can still be in `Fin.last k`
(`n ≤ k + 1`).
-/

namespace Podc.PPNaming

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {k : ℕ}

/-- The leader-mobile rule of Proposition 14: the leader's counter `c` meets a mobile state `q`. -/
def prop14lm (k : ℕ) (c q : Fin (k + 1)) : Fin (k + 1) × Fin (k + 1) :=
  if q = Fin.last k ∧ c < Fin.last k then (c + 1, c) else (c, q)

/-- The protocol of Proposition 14 (leader with a counter, `k + 1` mobile states). -/
def prop14 (k : ℕ) : LeaderProtocol (Fin (k + 1)) (Fin (k + 1)) where
  mm p q := (p, q)
  lm := prop14lm k
  ml q c := (prop14lm k c q).swap

/-- The protocol of Proposition 14 is symmetric. -/
theorem prop14_symmetric : (prop14 k).Symmetric := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

section

variable {A : Type*} [DecidableEq A] [Fintype A]

/-- The invariant of Proposition 14. -/
structure Inv14 (c : Fin (k + 1)) (m : A → Fin (k + 1)) : Prop where
  lt : ∀ a, m a ≠ Fin.last k → m a < c
  inj : ∀ a b, m a = m b → m a ≠ Fin.last k → a = b
  card : (Finset.univ.filter fun a => m a ≠ Fin.last k).card = c.val

omit [Fintype A] in
/-- Every step is null or names an agent in state `Fin.last k`. -/
lemma prop14_step {c : Fin (k + 1)} {m : A → Fin (k + 1)} {D : Config (Option A) _}
    (h : (prop14 k).toProtocol.Step (ofLM c m) D) :
    D = ofLM c m ∨ ∃ a, m a = Fin.last k ∧ c < Fin.last k ∧
      D = ofLM (c + 1) (Function.update m a c) := by
  obtain ⟨x, y, hxy, rfl⟩ := h
  have key : ∀ b, ofLM (prop14lm k c (m b)).1 (Function.update m b (prop14lm k c (m b)).2) =
      ofLM c m ∨ ∃ a, m a = Fin.last k ∧ c < Fin.last k ∧
        ofLM (prop14lm k c (m b)).1 (Function.update m b (prop14lm k c (m b)).2) =
          ofLM (c + 1) (Function.update m a c) := by
    intro b
    by_cases hcond : m b = Fin.last k ∧ c < Fin.last k
    · exact Or.inr ⟨b, hcond.1, hcond.2, by simp [prop14lm, hcond]⟩
    · left; simp [prop14lm, hcond]
  rcases x with _ | a <;> rcases y with _ | b
  · exact absurd rfl hxy
  · rw [interact_leader_mobile]; exact key b
  · rw [interact_mobile_leader]; exact key a
  · left
    rw [interact_mobile_mobile _ _ _ (fun h => hxy (by rw [h]))]
    simp [LeaderProtocol.mmUpd, prop14]

lemma Inv14.step {c : Fin (k + 1)} {m : A → Fin (k + 1)} (hI : Inv14 c m) {a : A}
    (ha : m a = Fin.last k) (hc : c < Fin.last k) :
    Inv14 (c + 1) (Function.update m a c) := by
  have hcv : (c + 1).val = c.val + 1 := Fin.val_add_one_of_lt hc
  have hlt : c < c + 1 := by rw [Fin.lt_def, hcv]; omega
  have hcne : c ≠ Fin.last k := ne_of_lt hc
  refine ⟨fun x hx => ?_, fun x y hxy hx => ?_, ?_⟩
  · by_cases hxa : x = a
    · subst hxa; simpa using hlt
    · rw [Function.update_of_ne hxa] at hx ⊢; exact lt_trans (hI.lt x hx) hlt
  · by_cases hxa : x = a <;> by_cases hya : y = a
    · rw [hxa, hya]
    · subst hxa; simp only [Function.update_self, Function.update_of_ne hya] at hxy
      exact absurd (hI.lt y (hxy ▸ hcne)) (by rw [← hxy]; exact lt_irrefl _)
    · subst hya; simp only [Function.update_self, Function.update_of_ne hxa] at hxy
      exact absurd (hI.lt x (hxy ▸ hcne)) (by rw [hxy]; exact lt_irrefl _)
    · simp only [Function.update_of_ne hxa, Function.update_of_ne hya] at hxy hx
      exact hI.inj x y hxy hx
  · have : (Finset.univ.filter fun x => Function.update m a c x ≠ Fin.last k) =
        insert a (Finset.univ.filter fun x => m x ≠ Fin.last k) := by
      ext x
      by_cases hxa : x = a
      · subst hxa; simp [hcne]
      · simp [hxa]
    rw [this, Finset.card_insert_of_notMem (by simp [ha]), hI.card, hcv]

/-- The reachable configurations: `ofLM c m` satisfying the invariant. -/
def Reach14 (X : Config (Option A) (Fin (k + 1) ⊕ Fin (k + 1))) : Prop :=
  ∃ c m, X = ofLM c m ∧ Inv14 c m

lemma reach14_closed : (prop14 k).toProtocol.Closed (Reach14 (A := A)) := by
  rintro X X' ⟨c, m, rfl, hI⟩ hst
  rcases prop14_step hst with h | ⟨a, ha, hc, h⟩
  · exact ⟨c, m, h, hI⟩
  · exact ⟨_, _, h, hI.step ha hc⟩

omit [DecidableEq A] in
lemma reach14_init : Reach14 (ofLM (0 : Fin (k + 1)) (fun _ : A => Fin.last k)) :=
  ⟨0, _, rfl, ⟨fun _ h => absurd rfl h, fun _ _ _ h => absurd rfl h, by simp⟩⟩

/-- When no agent in state `Fin.last k` can be named any more, the names are distinct. -/
lemma Inv14.injective (hA : Fintype.card A ≤ k + 1) {c : Fin (k + 1)} {m : A → Fin (k + 1)}
    (hI : Inv14 c m) (hstop : ∀ a, m a = Fin.last k → c = Fin.last k) :
    Function.Injective m := by
  intro a b hab
  by_cases ha : m a = Fin.last k
  · by_contra hne
    have hc := hstop a ha
    have hsub : (Finset.univ.filter fun x => m x ≠ Fin.last k) ⊆
        (Finset.univ.erase a).erase b := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hx (h ▸ hab ▸ ha), fun h => hx (h ▸ ha)⟩
    have := Finset.card_le_card hsub
    rw [hI.card, hc, Finset.card_erase_of_mem (by simp [Ne.symm hne]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    simp at this
    have h2 : 2 ≤ Fintype.card A := Fintype.one_lt_card_iff.2 ⟨a, b, hne⟩
    omega
  · exact hI.inj a b hab ha

/-- The potential: `k` minus the leader's counter. -/
def pot14 (X : Config (Option A) (Fin (k + 1) ⊕ Fin (k + 1))) : ℕ :=
  match X none with
  | .inl c => k - c.val
  | .inr _ => 0

omit [DecidableEq A] [Fintype A] in
lemma ofLM_succ_ne {c : Fin (k + 1)} (hc : c < Fin.last k) (m m' : A → Fin (k + 1)) :
    ofLM (c + 1) m' ≠ ofLM c m := by
  intro h
  have := congrArg Fin.val (ofLM_injective h).1
  rw [Fin.val_add_one_of_lt hc] at this
  omega

omit [DecidableEq A] [Fintype A] in
lemma pot14_lt {c : Fin (k + 1)} (hc : c < Fin.last k) (m m' : A → Fin (k + 1)) :
    pot14 (ofLM (c + 1) m') < pot14 (ofLM c m) := by
  simp only [pot14, ofLM_none, Fin.val_add_one_of_lt hc]
  have := Fin.lt_def.1 hc
  simp at this
  omega

end

/-- **Proposition 14** of [Burman–Beauquier–Sohier] (weak fairness). With an initialized leader
(counter `0`) and uniformly initialized mobile agents (state `Fin.last k`), the symmetric protocol
`prop14 k` with `P = k + 1` mobile states solves naming for every population of `n ≤ P` mobile
agents under weak fairness. -/
theorem prop14_solvesWeak (A : Type*) [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ k + 1) :
    SolvesWeak (prop14 k).toProtocol
      (initUniform 0 (Fin.last k) : Set (Config (Option A) (Fin (k + 1) ⊕ Fin (k + 1))))
      (leaderNames id) := by
  intro E hE0 hE
  have hR : ∀ t, Reach14 (E.config t) := fun t =>
    reach14_closed.execution E (T := 0) (by rw [hE0]; exact reach14_init) t (Nat.zero_le _)
  obtain ⟨T, hT⟩ := eventually_const_of_potential E pot14 fun t => by
    obtain ⟨c, m, hX, -⟩ := hR t
    rcases prop14_step (hX ▸ E.step_rel t) with h | ⟨a, -, hc, h⟩
    · exact Or.inl (h.trans hX.symm)
    · exact Or.inr (by rw [h, hX]; exact pot14_lt hc _ _)
  obtain ⟨c, m, hX, hI⟩ := hR T
  have hstop : ∀ a, m a = Fin.last k → c = Fin.last k := by
    intro a ha
    by_contra hc
    have hc : c < Fin.last k := Fin.lt_last_iff_ne_last.2 hc
    obtain ⟨t, ht, hs⟩ := hE none (some a) (by simp) T
    have hstep := E.step t
    rw [hT t ht, hT (t + 1) (by omega), hX] at hstep
    rcases hs with hs | hs <;> rw [hs] at hstep
    · rw [interact_leader_mobile] at hstep
      simp only [prop14, prop14lm, ha, hc, and_self, ↓reduceIte] at hstep
      exact ofLM_succ_ne hc _ _ hstep.symm
    · rw [interact_mobile_leader] at hstep
      simp only [prop14, prop14lm, ha, hc, and_self, ↓reduceIte, Prod.swap_prod_mk] at hstep
      exact ofLM_succ_ne hc _ _ hstep.symm
  refine ⟨T, ?_, fun t ht => by rw [hT t ht]⟩
  rw [hX, leaderNames_ofLM_injective_iff]
  exact hI.injective hA hstop

/-- **Proposition 14** of [Burman–Beauquier–Sohier] (global fairness). The same protocol solves
naming under global fairness. -/
theorem prop14_solvesGlobal (A : Type*) [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ k + 1) :
    SolvesGlobal (prop14 k).toProtocol
      (initUniform 0 (Fin.last k) : Set (Config (Option A) (Fin (k + 1) ⊕ Fin (k + 1))))
      (leaderNames id) := by
  intro E hE0 hE
  refine stabilizes_of_globallyFair (fun C₀ hC₀ C hC => ?_) E hE0 hE
  have hRC : Reach14 C :=
    reach14_closed.reachable (by rw [hC₀]; exact reach14_init) hC
  clear hC hC₀
  obtain ⟨c, m, rfl, hI⟩ := hRC
  induction hV : k - c.val using Nat.strong_induction_on generalizing c m with
  | _ n ih =>
    by_cases hmove : ∃ a, m a = Fin.last k ∧ c < Fin.last k
    · obtain ⟨a, ha, hc⟩ := hmove
      have hst : (prop14 k).toProtocol.Step (ofLM c m) (ofLM (c + 1) (Function.update m a c)) :=
        ⟨none, some a, by simp, by
          rw [interact_leader_mobile]; simp [prop14, prop14lm, ha, hc]⟩
      have hlt : k - (c + 1).val < n := by
        have := pot14_lt hc m (Function.update m a c)
        simp only [pot14, ofLM_none] at this; omega
      obtain ⟨D, hD, hDs⟩ := ih _ hlt _ _ (hI.step ha hc) rfl
      exact ⟨D, Relation.ReflTransGen.head hst hD, hDs⟩
    · push Not at hmove
      have hstop : ∀ a, m a = Fin.last k → c = Fin.last k := by
        intro a ha
        by_contra hc
        exact hmove a ha |>.not_gt (Fin.lt_last_iff_ne_last.2 hc)
      refine ⟨_, .refl, ?_, fun D hD => ?_⟩
      · show Function.Injective (leaderNames id (ofLM c m))
        rw [leaderNames_ofLM_injective_iff]
        exact hI.injective hA hstop
      · have : D = ofLM c m := by
          induction hD with
          | refl => rfl
          | tail _ hst ih =>
            subst ih
            rcases prop14_step hst with h | ⟨a, ha, hc, -⟩
            · exact h
            · exact absurd (hmove a ha) (not_le.2 hc)
        rw [this]

end Podc.PPNaming
