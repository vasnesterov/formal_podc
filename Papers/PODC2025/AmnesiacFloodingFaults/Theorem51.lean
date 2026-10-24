import Papers.PODC2025.AmnesiacFloodingFaults.Balance

/-!
# Theorem 5.1, Corollary 5.1.1 and Theorem 5.5 with the paper's notion of balance

`Balanced G S` is Definition 5.4: `S` is balanced on every cycle of `G` and on the even cycle
representation (`FEC.walk`) of every faux-even cycle of `G`. We show it is equivalent to balance
along every closed walk (`balancedAll_iff_balanced`), using the spanning theorems
`walkFlow_eq_zero_of_isCycle` and `walkSig_eq_zero_of_isCycle_of_fec`.
-/

namespace AmnesiacFloodingFaults

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- **Definition 5.4.** A configuration is *balanced* on `G` if it is balanced on every cycle
subgraph (in each direction for odd cycles; in each parity class of heads for even cycles) and,
for every faux-even cycle `H`, its even cycle representation `S^{2,H}` is balanced on `H²`. -/
def Balanced (G : SimpleGraph V) (S : Config V) : Prop :=
  (∀ (u : V) (c : G.Walk u u), c.IsCycle → BalancedOn S (toFun c)) ∧
    ∀ F : FEC G, BalancedOn S (toFun F.walk)

lemma FEC.walk_length (F : FEC G) :
    F.walk.length = F.c₁.length + (F.p.length + (F.c₂.length + F.p.length)) := by
  simp [FEC.walk]

lemma FEC.even_walk_length (F : FEC G) : Even F.walk.length := by
  rw [F.walk_length]
  obtain ⟨a, ha⟩ := F.odd₁; obtain ⟨b, hb⟩ := F.odd₂
  exact ⟨a + b + 1 + F.p.length, by omega⟩

lemma FEC.walk_length_pos (F : FEC G) : 0 < F.walk.length := by
  rw [F.walk_length]; have := F.odd₁.pos; omega

lemma BalancedAll.balanced {S : Config V} (h : BalancedAll G S) : Balanced G S := by
  refine ⟨fun u c hc => ?_, fun F => ?_⟩
  · have hpos : 0 < c.length := by have := hc.three_le_length; omega
    have : NeZero c.length := ⟨by omega⟩
    exact h _ _ (isClosedWalk_toFun c hpos)
  · have : NeZero F.walk.length := ⟨F.walk_length_pos.ne'⟩
    exact h _ _ (isClosedWalk_toFun _ F.walk_length_pos)

lemma Balanced.balancedAll {S : Config V} (h : Balanced G S) : BalancedAll G S := by
  intro L _ w hw
  have hflowc : ∀ (u : V) (c : G.Walk u u), c.IsCycle → walkFlow (gS S) c = 0 := by
    intro u c hc
    have : NeZero c.length := ⟨by have := hc.three_le_length; omega⟩
    rw [← flowSum_toFun]
    exact ((balancedOn_iff S _).1 (h.1 u c hc)).1
  have hsigc : ∀ (u : V) (c : G.Walk u u), c.IsCycle → Even c.length →
      walkSig (oS S) c = 0 := by
    intro u c hc he
    have : NeZero c.length := ⟨by have := hc.three_le_length; omega⟩
    rw [← sigSum_toFun]
    exact ((balancedOn_iff S _).1 (h.1 u c hc)).2 he
  have hsigF : ∀ F : FEC G, walkSig (oS S) F.walk = 0 := by
    intro F
    have : NeZero F.walk.length := ⟨F.walk_length_pos.ne'⟩
    rw [← sigSum_toFun]
    exact ((balancedOn_iff S _).1 (h.2 F)).2 F.even_walk_length
  rw [balancedOn_iff, flowSum_eq_walkFlow_ofFun S w hw, sigSum_eq_walkSig_ofFun S w hw]
  refine ⟨walkFlow_eq_zero_of_isCycle (gS_antisymm S) hflowc _ _, fun he => ?_⟩
  exact walkSig_eq_zero_of_isCycle_of_fec (oS_symm S) hsigc hsigF _ _
    (by rwa [ofFun_length])

/-- Balance in the sense of Definition 5.4 (cycles and faux-even cycles) is equivalent to balance
along every closed walk. -/
theorem balancedAll_iff_balanced {S : Config V} : BalancedAll G S ↔ Balanced G S :=
  ⟨BalancedAll.balanced, Balanced.balancedAll⟩

/-- **Theorem 5.1.** Let `S` be a configuration on a finite graph `G`. Then `A_∅^k(S) = ∅` for some
`k ≥ 0` iff `S` is balanced on `G`. -/
theorem theorem_5_1 [Fintype V] {S : Config V} (hS : IsConfig G S) :
    (∃ k, (af G)^[k] S = ∅) ↔ Balanced G S := by
  rw [← balancedAll_iff_balanced]; exact terminates_iff_balancedAll hS

/-- **Corollary 5.1.1.** A balanced configuration terminates within `2|E|` rounds. -/
theorem corollary_5_1_1 [Fintype V] [DecidableRel G.Adj] {S : Config V} (hS : IsConfig G S)
    (h : Balanced G S) : ∃ k ≤ 2 * #G.edgeFinset, (af G)^[k] S = ∅ :=
  ⟨_, le_rfl, iterate_eq_empty_of_balancedAll hS h.balancedAll⟩

/-- **Theorem 5.5.** For a configuration `S` on a finite graph, the following are equivalent:
(1) `A_∅^k(S) = ∅` for some `k`; (2) `A_{I_k} ⋯ A_{I_1}(∅) = S` for some sequence of initiator
sets; (3) `S` is balanced on `G`. -/
theorem theorem_5_5 [Fintype V] {S : Config V} (hS : IsConfig G S) :
    [∃ k, (af G)^[k] S = ∅, ∃ Is : List (Set V), runFrom G Is ∅ = S, Balanced G S].TFAE := by
  have := theorem_5_5_walks hS
  rw [← balancedAll_iff_balanced]
  exact this

/-- **Lemma 5.4.** `S̄` is balanced iff `S` is. -/
theorem lemma_5_4 {S : Config V} : Balanced G (rev S) ↔ Balanced G S := by
  rw [← balancedAll_iff_balanced, ← balancedAll_iff_balanced]; exact balancedAll_rev_iff

/-- **Lemma A.1.** Balance is preserved and reflected by `A_{I,G}` for every initiator set. -/
theorem lemma_A_1 (I : Set V) {S : Config V} : Balanced G (step G I S) ↔ Balanced G S := by
  rw [← balancedAll_iff_balanced, ← balancedAll_iff_balanced]; exact balancedAll_step_iff

end AmnesiacFloodingFaults
