import Papers.PODC2018.PPNaming.Model

/-!
# Lemma 2, Propositions 3 and 4: symmetric naming with `P` states

* `ReachNamed P I names`: from every configuration reachable from `I` a stably named
  configuration is reachable. Both weak and global fairness correctness imply it
  (`SolvesWeak.reachNamed`, `SolvesGlobal.reachNamed`); all impossibility results of this file
  only use this consequence, hence hold under both fairness assumptions.
* **Lemma 2** (`lemma2`, `lemma2_leader`): in a naming protocol with `P` states per mobile agent
  (and a population of `P` mobile agents), names are an injective function of the states and the
  only non-null rules between two mobile agents are between homonyms. (Symmetry is not needed.)
* **Proposition 3** (`prop3_weak`, `prop3_global`): without leader, with `P` states, symmetric
  naming is impossible (even with uniform initialization), under weak or global fairness.
* **Proposition 4** (`prop4_weak`, `prop4_global`): with an arbitrarily initialized leader, with
  `P` states, symmetric naming is impossible (mobile agents arbitrarily or uniformly initialized),
  under weak or global fairness.
-/

namespace Podc.PPNaming

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {S Ag A Q L N : Type*}

/-- From every configuration reachable from `I`, some stably named configuration is
reachable. -/
def ReachNamed [DecidableEq Ag] (P : Protocol S) (I : Set (Config Ag S))
    (names : Config Ag S → A → N) : Prop :=
  ∀ C₀ ∈ I, ∀ C, P.Reachable C₀ C → ∃ D, P.Reachable C D ∧ StablyNamed P names D

lemma SolvesWeak.reachNamed [Fintype Ag] [DecidableEq Ag] {P : Protocol S} {I : Set (Config Ag S)}
    {names : Config Ag S → A → N} (h : SolvesWeak P I names) {a₀ b₀ : Ag} (hab : a₀ ≠ b₀) :
    ReachNamed P I names :=
  fun _ hC₀ _ hC => exists_stablyGood_of_weaklyFair hab h hC₀ hC

lemma SolvesGlobal.reachNamed [Finite Ag] [Finite S] [DecidableEq Ag] {P : Protocol S}
    {I : Set (Config Ag S)} {names : Config Ag S → A → N} (h : SolvesGlobal P I names)
    {a₀ b₀ : Ag} (hab : a₀ ≠ b₀) : ReachNamed P I names :=
  fun _ hC₀ _ hC => exists_stablyGood_of_globallyFair hab h hC₀ hC

/-- To refute weak-fairness correctness it suffices to exhibit *phases*: a set `G` of
configurations with non-injective names, reachable from `I`, such that from every configuration
of `G` and for every pair of agents some path back into `G` uses this pair. -/
lemma SolvesWeak.false_of_phases [Fintype Ag] [DecidableEq Ag] {P : Protocol S}
    {I : Set (Config Ag S)} {names : Config Ag S → A → N} (h : SolvesWeak P I names)
    (G : Config Ag S → Prop)
    (hph : ∀ C, G C → ∀ a b, a ≠ b → ∃ C₁ C₂, P.Reachable C C₁ ∧
      P.Reachable (P.interact C₁ a b) C₂ ∧ G C₂ ∧ ¬ Function.Injective (names C))
    {C₀ C₁ : Config Ag S} (hC₀ : C₀ ∈ I) (h₀₁ : P.Reachable C₀ C₁) (hG : G C₁) {a₀ b₀ : Ag}
    (hab : a₀ ≠ b₀) : False := by
  obtain ⟨E, hE0, hEf, hinf⟩ := P.exists_weaklyFair_of_phases G
    (fun C _ => ¬ Function.Injective (names C)) hph h₀₁ hG hab
  obtain ⟨T, hgT, hT⟩ := h E (hE0 ▸ hC₀) hEf
  obtain ⟨t, ht, t', ht', -, hR⟩ := hinf T
  exact hR (by rw [hT t ht]; exact hgT)

/-! ### Lemma 2 -/

section Lemma2

variable [Fintype A] [Fintype Q] [DecidableEq A]

/-- With as many agents as states, injective names force the configuration to be a bijection
and the naming function to be injective. -/
lemma bijective_of_injective_names (hA : Fintype.card A = Fintype.card Q) {name : Q → N}
    {c : A → Q} (hc : Function.Injective (fun a => name (c a))) :
    Function.Bijective c ∧ Function.Injective name := by
  have hci : Function.Injective c := fun a b h => hc (by simp [h])
  have hcb : Function.Bijective c := (Fintype.bijective_iff_injective_and_card c).2 ⟨hci, hA⟩
  refine ⟨hcb, fun p q hpq => ?_⟩
  obtain ⟨a, rfl⟩ := hcb.2 p
  obtain ⟨b, rfl⟩ := hcb.2 q
  rw [hc hpq]

/-- Core of Lemma 2 (no leader): a stably named configuration of `P` agents with `P` states. -/
theorem lemma2_core (hA : Fintype.card A = Fintype.card Q) {P : Protocol Q} {name : Q → N}
    {D : Config A Q} (hD : StablyNamed P (nameOut name) D) :
    Function.Injective name ∧ ∀ p q, p ≠ q → P.δ p q = (p, q) := by
  obtain ⟨hDb, hname⟩ := bijective_of_injective_names hA hD.1
  refine ⟨hname, fun p q hpq => ?_⟩
  obtain ⟨a, rfl⟩ := hDb.2 p
  obtain ⟨b, rfl⟩ := hDb.2 q
  have hab : a ≠ b := fun h => hpq (by rw [h])
  have hst := hD.2 _ (.single ⟨a, b, hab, rfl⟩)
  have ha := hname (congrFun hst a)
  have hb := hname (congrFun hst b)
  simp only [interact_self_left, interact_self_right _ _ hab] at ha hb
  exact Prod.ext ha hb

/-- **Lemma 2** (no leader). In a naming protocol with `P` states per agent, in a population of
`P` agents, the names are an injective function of the states and the only non-null rules are
between homonyms. -/
theorem lemma2 (hA : Fintype.card A = Fintype.card Q) {P : Protocol Q} {I : Set (Config A Q)}
    (hI : I.Nonempty) {name : Q → N} (h : ReachNamed P I (nameOut name)) :
    Function.Injective name ∧ ∀ p q, p ≠ q → P.δ p q = (p, q) := by
  obtain ⟨C₀, hC₀⟩ := hI
  obtain ⟨D, -, hD⟩ := h C₀ hC₀ C₀ .refl
  exact lemma2_core hA hD

omit [Fintype A] [Fintype Q] in
/-- In a stably named configuration `ofLM l c` (with a leader), the mobile states never change
again (the names are an injective function of the states). -/
lemma ofLM_stable {LP : LeaderProtocol L Q} {name : Q → N} (hname : Function.Injective name)
    {l : L} {c : A → Q} (hD : StablyNamed LP.toProtocol (leaderNames name) (ofLM l c))
    {l' : L} {c' : A → Q} (h : LP.toProtocol.Reachable (ofLM l c) (ofLM l' c')) : c' = c := by
  funext a
  have := congrFun (hD.2 _ h) a
  simp only [leaderNames_ofLM, Option.some.injEq] at this
  exact hname this

/-- Core of Lemma 2 (with a leader). -/
theorem lemma2_leader_core (hA : Fintype.card A = Fintype.card Q) {LP : LeaderProtocol L Q}
    {name : Q → N} {l : L} {c : A → Q}
    (hD : StablyNamed LP.toProtocol (leaderNames name) (ofLM l c)) :
    Function.Injective name ∧ ∀ p q, p ≠ q → LP.mm p q = (p, q) := by
  obtain ⟨hcb, hname⟩ := bijective_of_injective_names hA
    ((leaderNames_ofLM_injective_iff name l c).1 hD.1)
  refine ⟨hname, fun p q hpq => ?_⟩
  obtain ⟨a, rfl⟩ := hcb.2 p
  obtain ⟨b, rfl⟩ := hcb.2 q
  have hab : a ≠ b := fun h => hpq (by rw [h])
  have hst : LP.toProtocol.Reachable (ofLM l c) (ofLM l (LP.mmUpd c a b)) := by
    rw [← interact_mobile_mobile LP l c hab]
    exact .single ⟨some a, some b, by simpa using hab, rfl⟩
  have hc := ofLM_stable hname hD hst
  have ha := congrFun hc a
  have hb := congrFun hc b
  simp only [LeaderProtocol.mmUpd, Function.update_self, Function.update_of_ne hab] at ha hb
  exact Prod.ext ha hb

/-- **Lemma 2** (with a leader). -/
theorem lemma2_leader (hA : Fintype.card A = Fintype.card Q) {LP : LeaderProtocol L Q}
    {I : Set (Config (Option A) (L ⊕ Q))} {l₀ : L} {c₀ : A → Q} (hI : ofLM l₀ c₀ ∈ I)
    {name : Q → N} (h : ReachNamed LP.toProtocol I (leaderNames name)) :
    Function.Injective name ∧ ∀ p q, p ≠ q → LP.mm p q = (p, q) := by
  obtain ⟨D, hD, hDs⟩ := h _ hI _ .refl
  obtain ⟨l, c, rfl⟩ := exists_ofLM_of_reachable LP hD
  exact lemma2_leader_core hA hDs

end Lemma2

/-! ### Homonyms persist -/

/-- A configuration has two distinct agents in the same state. -/
def HasHomonyms (c : A → Q) : Prop := ∃ a b, a ≠ b ∧ c a = c b

lemma not_injective_of_hasHomonyms {name : Q → N} {c : A → Q} (h : HasHomonyms c) :
    ¬ Function.Injective (fun a => name (c a)) := by
  obtain ⟨a, b, hab, he⟩ := h
  exact fun hi => hab (hi (by simp [he]))

/-- In a symmetric protocol whose only non-null rules are between homonyms, an interaction keeps
some pair of homonyms. -/
lemma hasHomonyms_mm [DecidableEq A] {mm : Q → Q → Q × Q} (hsym : ∀ s, (mm s s).2 = (mm s s).1)
    (hnull : ∀ p q, p ≠ q → mm p q = (p, q)) {c : A → Q} (hc : HasHomonyms c) {a b : A}
    (hab : a ≠ b) :
    HasHomonyms (Function.update (Function.update c a (mm (c a) (c b)).1) b (mm (c a) (c b)).2) := by
  by_cases he : c a = c b
  · refine ⟨a, b, hab, ?_⟩
    rw [Function.update_of_ne hab, Function.update_self, Function.update_self, he, hsym]
  · rw [hnull _ _ he]
    simpa using hc

/-! ### Proposition 3 -/

section Prop3

variable [Fintype A] [Fintype Q] [DecidableEq A]

/-- Core of Proposition 3: with `P` states and `P` agents (no leader), a symmetric protocol
cannot have a stably named configuration reachable from a configuration with homonyms. -/
theorem prop3_core (hA : Fintype.card A = Fintype.card Q) {P : Protocol Q} (hs : IsSymmetric P)
    {name : Q → N} {I : Set (Config A Q)} (h : ReachNamed P I (nameOut name)) {C₀ : Config A Q}
    (hC₀ : C₀ ∈ I) (hhom : HasHomonyms C₀) : False := by
  obtain ⟨-, hnull⟩ := lemma2 hA ⟨C₀, hC₀⟩ h
  have inv : ∀ C, P.Reachable C₀ C → HasHomonyms C := by
    intro C hC
    induction hC with
    | refl => exact hhom
    | tail _ hst ih =>
      obtain ⟨a, b, hab, rfl⟩ := hst
      have := hasHomonyms_mm (mm := P.δ) (fun s => hs.diag s) hnull ih hab
      convert this using 1
      funext x
      by_cases hxa : x = a
      · subst hxa; simp [Function.update_of_ne hab]
      · by_cases hxb : x = b
        · subst hxb; simp [hab]
        · simp [Protocol.interact, hxa, hxb]
  obtain ⟨D, hD, hDs⟩ := h C₀ hC₀ C₀ .refl
  exact not_injective_of_hasHomonyms (inv D hD) hDs.1

/-- **Proposition 3** (weak fairness). Without leader and with `P` states per agent, symmetric
naming of `P` agents is impossible, even with a uniform initialization. -/
theorem prop3_weak (hA : Fintype.card A = Fintype.card Q) (h2 : 2 ≤ Fintype.card Q)
    (P : Protocol Q) (hs : IsSymmetric P) (name : Q → N) (q₀ : Q) :
    ¬ SolvesWeak P ({fun _ => q₀} : Set (Config A Q)) (nameOut name) := by
  intro h
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  exact prop3_core hA hs (h.reachNamed hab) rfl ⟨a, b, hab, rfl⟩

/-- **Proposition 3** (global fairness). -/
theorem prop3_global (hA : Fintype.card A = Fintype.card Q) (h2 : 2 ≤ Fintype.card Q)
    (P : Protocol Q) (hs : IsSymmetric P) (name : Q → N) (q₀ : Q) :
    ¬ SolvesGlobal P ({fun _ => q₀} : Set (Config A Q)) (nameOut name) := by
  intro h
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  exact prop3_core hA hs (h.reachNamed hab) rfl ⟨a, b, hab, rfl⟩

/-- Proposition 3 also holds for arbitrary initialization (a fortiori). -/
theorem prop3_weak_arb (hA : Fintype.card A = Fintype.card Q) (h2 : 2 ≤ Fintype.card Q)
    (P : Protocol Q) (hs : IsSymmetric P) (name : Q → N) :
    ¬ SolvesWeak P (Set.univ : Set (Config A Q)) (nameOut name) := by
  intro h
  obtain ⟨q₀⟩ : Nonempty Q := Fintype.card_pos_iff.1 (by omega)
  exact prop3_weak hA h2 P hs name q₀ (fun E hE hf => h E trivial hf)

end Prop3

/-! ### Proposition 4 -/

section Prop4

variable [Fintype A] [Fintype Q] [DecidableEq A]

/-- Core of Proposition 4. Let `LP` be a symmetric leader protocol with `P` states per mobile
agent, `P` mobile agents, and suppose the allowed initial configurations contain, for some
mobile configuration `c₀` with homonyms, `ofLM l c₀` for every leader state `l`. Then naming is
impossible. -/
theorem prop4_core [Nonempty L] (hA : Fintype.card A = Fintype.card Q) {LP : LeaderProtocol L Q}
    (hs : LP.Symmetric) {name : Q → N} {I : Set (Config (Option A) (L ⊕ Q))}
    (h : ReachNamed LP.toProtocol I (leaderNames name)) {c₀ : A → Q} (hhom : HasHomonyms c₀)
    (hI : ∀ l, ofLM l c₀ ∈ I) : False := by
  obtain ⟨l₁⟩ := ‹Nonempty L›
  obtain ⟨D, hD, hDs⟩ := h _ (hI l₁) _ .refl
  obtain ⟨lst, cst, rfl⟩ := exists_ofLM_of_reachable LP hD
  obtain ⟨hname, hnull⟩ := lemma2_leader_core hA hDs
  obtain ⟨hcb, -⟩ := bijective_of_injective_names hA
    ((leaderNames_ofLM_injective_iff name lst cst).1 hDs.1)
  have hsymP := hs.isSymmetric
  have hdiag : ∀ s, (LP.mm s s).2 = (LP.mm s s).1 := fun s => by
    have := congrArg Prod.fst (hs.1 s s); simpa using this.symm
  -- the world `ofLM l c` (with homonyms) shadows the stable world `ofLM l cst`
  let Inv : Config (Option A) (L ⊕ Q) → Prop := fun Y => ∃ l c, Y = ofLM l c ∧
    LP.toProtocol.Reachable (ofLM lst cst) (ofLM l cst) ∧ HasHomonyms c
  have inv : ∀ Y, LP.toProtocol.Reachable (ofLM lst c₀) Y → Inv Y := by
    intro Y hY
    induction hY with
    | refl => exact ⟨lst, c₀, rfl, .refl, hhom⟩
    | tail _ hst ih =>
      obtain ⟨l, c, rfl, hr, hh⟩ := ih
      obtain ⟨x, y, hxy, rfl⟩ := hst
      have key : ∀ a, Inv (LP.toProtocol.interact (ofLM l c) none (some a)) := by
        intro a
        obtain ⟨z, hz⟩ := hcb.2 (c a)
        have hr' : LP.toProtocol.Reachable (ofLM lst cst)
            (LP.toProtocol.interact (ofLM l cst) none (some z)) :=
          hr.tail ⟨none, some z, by simp, rfl⟩
        rw [interact_leader_mobile] at hr'
        have hc := ofLM_stable hname hDs hr'
        have hv : (LP.lm l (c a)).2 = c a := by
          have := congrFun hc z
          rwa [Function.update_self, hz] at this
        rw [hc, hz] at hr'
        refine ⟨_, c, ?_, hr', hh⟩
        rw [interact_leader_mobile, hv, Function.update_eq_self]
      rcases x with _ | a <;> rcases y with _ | b
      · exact absurd rfl hxy
      · exact key b
      · rw [← hsymP.interact_comm _ hxy]; exact key a
      · have hab : a ≠ b := fun h => hxy (by rw [h])
        rw [interact_mobile_mobile LP l c hab]
        exact ⟨l, _, rfl, hr, hasHomonyms_mm hdiag hnull hh hab⟩
  obtain ⟨D', hD', hD's⟩ := h _ (hI lst) _ .refl
  obtain ⟨l, c, rfl, -, hh⟩ := inv D' hD'
  exact not_injective_of_hasHomonyms hh ((leaderNames_ofLM_injective_iff _ _ _).1 hD's.1)

omit [Fintype Q] in
lemma exists_pair_option (h2 : 2 ≤ Fintype.card A) : ∃ a b : Option A, a ≠ b := by
  obtain ⟨a, -, -⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  exact ⟨none, some a, by simp⟩

omit [Fintype Q] in
lemma hasHomonyms_const (h2 : 2 ≤ Fintype.card A) (q₀ : Q) : HasHomonyms (fun _ : A => q₀) := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  exact ⟨a, b, hab, rfl⟩

/-- **Proposition 4** (weak fairness). With an arbitrarily initialized leader and `P` states per
mobile agent, symmetric naming of `P` mobile agents is impossible. -/
theorem prop4_weak [Nonempty L] (hA : Fintype.card A = Fintype.card Q) (h2 : 2 ≤ Fintype.card Q)
    (LP : LeaderProtocol L Q) (hs : LP.Symmetric) (name : Q → N) :
    ¬ SolvesWeak LP.toProtocol (initArb : Set (Config (Option A) (L ⊕ Q))) (leaderNames name) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_option (A := A) (by omega)
  obtain ⟨q₀⟩ : Nonempty Q := Fintype.card_pos_iff.1 (by omega)
  exact prop4_core hA hs (h.reachNamed hab) (hasHomonyms_const (by omega) q₀)
    (fun l => ⟨l, _, rfl⟩)

/-- **Proposition 4** (weak fairness), uniformly initialized mobile agents. -/
theorem prop4_weak_uniform [Nonempty L] (hA : Fintype.card A = Fintype.card Q)
    (h2 : 2 ≤ Fintype.card Q) (LP : LeaderProtocol L Q) (hs : LP.Symmetric) (name : Q → N)
    (q₀ : Q) :
    ¬ SolvesWeak LP.toProtocol (initArbLeaderUniform q₀ : Set (Config (Option A) (L ⊕ Q)))
      (leaderNames name) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_option (A := A) (by omega)
  exact prop4_core hA hs (h.reachNamed hab) (hasHomonyms_const (by omega) q₀)
    (fun l => ⟨l, rfl⟩)

/-- **Proposition 4** (global fairness). -/
theorem prop4_global [Nonempty L] [Fintype L] (hA : Fintype.card A = Fintype.card Q)
    (h2 : 2 ≤ Fintype.card Q) (LP : LeaderProtocol L Q) (hs : LP.Symmetric) (name : Q → N) :
    ¬ SolvesGlobal LP.toProtocol (initArb : Set (Config (Option A) (L ⊕ Q)))
      (leaderNames name) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_option (A := A) (by omega)
  obtain ⟨q₀⟩ : Nonempty Q := Fintype.card_pos_iff.1 (by omega)
  exact prop4_core hA hs (h.reachNamed hab) (hasHomonyms_const (by omega) q₀)
    (fun l => ⟨l, _, rfl⟩)

/-- **Proposition 4** (global fairness), uniformly initialized mobile agents. -/
theorem prop4_global_uniform [Nonempty L] [Fintype L] (hA : Fintype.card A = Fintype.card Q)
    (h2 : 2 ≤ Fintype.card Q) (LP : LeaderProtocol L Q) (hs : LP.Symmetric) (name : Q → N)
    (q₀ : Q) :
    ¬ SolvesGlobal LP.toProtocol (initArbLeaderUniform q₀ : Set (Config (Option A) (L ⊕ Q)))
      (leaderNames name) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_option (A := A) (by omega)
  exact prop4_core hA hs (h.reachNamed hab) (hasHomonyms_const (by omega) q₀)
    (fun l => ⟨l, rfl⟩)

end Prop4

end Podc.PPNaming
