import Papers.PODC2019.ComposableCRN.Basic

-- CSLib candidate: Cslib/Computability/ChemicalReactionNetworks/Composition.lean
/-!
# Composition of output-oblivious CRNs (Observation 2.2, generalized)

Given CRNs `C_k` (`k : κ`) stably computing `f_k : ℕ^ι → ℕ`, all output-oblivious, and a CRN `C_g`
stably computing `g : ℕ^κ → ℕ`, the composite CRN

* `L → Σ_k L_k + L_g` (one copy of each leader),
* `X_i → Σ_k X^{(k)}_i` (fan-out of every input to every upstream module),
* the reactions of every `C_k` and of `C_g`,
* `Y^{(k)} → X^{(g)}_k` (transfer of the output of `C_k` to the `k`-th input of `C_g`),

stably computes `x ↦ g (f_1 x, …, f_κ x)`; it is output-oblivious if `C_g` is.

The paper composes by *renaming* the output species of `C_f` to the input species of `C_g`
(Observation 2.2, for `κ = 1`; "more generally, g can take any number of inputs ..."). We use
an explicit transfer reaction instead, which keeps the species of the modules disjoint; this
only delays the hand-over and does not change what is computed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.ComposableCRN

open CRN

theorem CRN.Step.congr_right {S : Type*} {N : CRN S} {A B B' : Config S} (h : N.Step A B)
    (hB : B = B') : N.Step A B' := hB ▸ h

theorem CRN.Reach.of_eq {S : Type*} {N : CRN S} {A B A' B' : Config S} (h : N.Reach A B)
    (hA : A = A') (hB : B = B') : N.Reach A' B' := hA ▸ hB ▸ h

/-- In an output-oblivious CRN, extra output molecules are inert: a run from `U + t·Y` is a run
from `U` with `t·Y` added. -/
theorem FunCRN.reach_split_output {S ι : Type*} [DecidableEq S] (N : FunCRN S ι)
    (hO : N.OutputOblivious) {U B : Config S} {t : ℕ}
    (h : N.Reach (U + Pi.single N.Y t) B) :
    ∃ U', B = U' + Pi.single N.Y t ∧ N.Reach U U' := by
  induction h with
  | refl => exact ⟨U, rfl, Reach.refl _⟩
  | tail _ hs ih =>
    obtain ⟨U', rfl, hU'⟩ := ih
    obtain ⟨ρ, hρ, hle, rfl⟩ := hs
    have hY := hO ρ hρ
    have hle' : ρ.reactants ≤ U' := fun s => by
      have h1 := hle s
      simp only [Pi.add_apply] at h1
      by_cases hs : s = N.Y
      · subst hs; rw [hY]; exact Nat.zero_le _
      · simpa [hs] using h1
    refine ⟨U' - ρ.reactants + ρ.products, ?_, hU'.tail ⟨ρ, hρ, hle', rfl⟩⟩
    funext s
    have : ρ.reactants s ≤ U' s := hle' s
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [Nat.sub_add_comm this]
    ring

namespace Comp

/-- Species of the composite CRN. -/
inductive Sp (ι κ : Type) (Sf : κ → Type) (Sg : Type) where
  | lead
  | inp (i : ι)
  | up (k : κ) (s : Sf k)
  | down (s : Sg)

variable {ι κ : Type} {Sf : κ → Type} {Sg : Type}

/-- `Sp ≃ Unit ⊕ ι ⊕ (Σ k, Sf k) ⊕ Sg`. -/
def Sp.equiv (ι κ : Type) (Sf : κ → Type) (Sg : Type) :
    Sp ι κ Sf Sg ≃ Unit ⊕ ι ⊕ (Σ k, Sf k) ⊕ Sg where
  toFun
    | .lead => .inl ()
    | .inp i => .inr (.inl i)
    | .up k s => .inr (.inr (.inl ⟨k, s⟩))
    | .down s => .inr (.inr (.inr s))
  invFun
    | .inl () => .lead
    | .inr (.inl i) => .inp i
    | .inr (.inr (.inl ⟨k, s⟩)) => .up k s
    | .inr (.inr (.inr s)) => .down s
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | i | ⟨k, s⟩ | s <;> rfl

instance [DecidableEq ι] [DecidableEq κ] [∀ k, DecidableEq (Sf k)] [DecidableEq Sg] :
    DecidableEq (Sp ι κ Sf Sg) :=
  (Sp.equiv ι κ Sf Sg).decidableEq

instance [Fintype ι] [Fintype κ] [∀ k, Fintype (Sf k)] [Fintype Sg] :
    Fintype (Sp ι κ Sf Sg) :=
  Fintype.ofEquiv _ (Sp.equiv ι κ Sf Sg).symm

/-- A composite configuration from its parts: leaders `ℓ`, unfanned inputs `r`, the
configurations `U k` of the upstream modules and `G` of the downstream module. -/
def mk (ℓ : ℕ) (r : ι → ℕ) (U : ∀ k, Sf k → ℕ) (G : Sg → ℕ) : Config (Sp ι κ Sf Sg) := fun s =>
  match s with
  | .lead => ℓ
  | .inp i => r i
  | .up k s => U k s
  | .down s => G s

theorem eta (C : Config (Sp ι κ Sf Sg)) :
    C = mk (C .lead) (fun i => C (.inp i)) (fun k s => C (.up k s)) (fun s => C (.down s)) := by
  funext s; cases s <;> rfl

theorem mk_sub_add (ℓ a b : ℕ) (r r₁ r₂ : ι → ℕ) (U U₁ U₂ : ∀ k, Sf k → ℕ) (G G₁ G₂ : Sg → ℕ) :
    mk ℓ r U G - mk a r₁ U₁ G₁ + mk b r₂ U₂ G₂ =
      mk (ℓ - a + b) (r - r₁ + r₂) (fun k => U k - U₁ k + U₂ k) (G - G₁ + G₂) := by
  funext s; cases s <;> rfl

theorem mk_le_mk {ℓ a : ℕ} {r r₁ : ι → ℕ} {U U₁ : ∀ k, Sf k → ℕ} {G G₁ : Sg → ℕ} :
    mk a r₁ U₁ G₁ ≤ mk ℓ r U G ↔ a ≤ ℓ ∧ r₁ ≤ r ∧ (∀ k, U₁ k ≤ U k) ∧ G₁ ≤ G := by
  constructor
  · intro h
    exact ⟨h .lead, fun i => h (.inp i), fun k s => h (.up k s), fun s => h (.down s)⟩
  · rintro ⟨h1, h2, h3, h4⟩ s
    cases s with
    | lead => exact h1
    | inp i => exact h2 i
    | up k s => exact h3 k s
    | down s => exact h4 s

theorem mk_inj {ℓ a : ℕ} {r r₁ : ι → ℕ} {U U₁ : ∀ k, Sf k → ℕ} {G G₁ : Sg → ℕ} :
    mk a r₁ U₁ G₁ = mk ℓ r U G ↔ a = ℓ ∧ r₁ = r ∧ U₁ = U ∧ G₁ = G := by
  constructor
  · intro h
    refine ⟨congrFun h .lead, funext fun i => congrFun h (.inp i),
      funext fun k => funext fun s => congrFun h (.up k s), funext fun s => congrFun h (.down s)⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [∀ k, Fintype (Sf k)] [∀ k, DecidableEq (Sf k)] [Fintype Sg] [DecidableEq Sg]
  (Cf : ∀ k, FunCRN (Sf k) ι) (Cg : FunCRN Sg κ)

/-- `L → Σ_k L_k + L_g`. -/
def splitR : Reaction (Sp ι κ Sf Sg) where
  reactants := mk 1 0 0 0
  products := mk 0 0 (fun k => (Cf k).leaderConf) Cg.leaderConf

/-- `X_i → Σ_k X^{(k)}_i`. -/
def fanR (i : ι) : Reaction (Sp ι κ Sf Sg) where
  reactants := mk 0 (Pi.single i 1) 0 0
  products := mk 0 0 (fun k => (Cf k).inputConf (Pi.single i 1)) 0

/-- A reaction of the upstream module `k`. -/
def upR (k : κ) (ρ : Reaction (Sf k)) : Reaction (Sp ι κ Sf Sg) where
  reactants := mk 0 0 (Pi.single k ρ.reactants) 0
  products := mk 0 0 (Pi.single k ρ.products) 0

/-- `Y^{(k)} → X^{(g)}_k`. -/
def transR (k : κ) : Reaction (Sp ι κ Sf Sg) where
  reactants := mk 0 0 (Pi.single k (Pi.single (Cf k).Y 1)) 0
  products := mk 0 0 0 (Cg.inputConf (Pi.single k 1))

/-- A reaction of the downstream module. -/
def downR (ρ : Reaction Sg) : Reaction (Sp ι κ Sf Sg) where
  reactants := mk 0 0 0 ρ.reactants
  products := mk 0 0 0 ρ.products

/-- The composite CRN. -/
def comp : FunCRN (Sp ι κ Sf Sg) ι where
  reactions := {splitR Cf Cg} ∪ Set.range (fanR Cf (Sg := Sg)) ∪
    (⋃ k, upR k '' (Cf k).reactions) ∪ Set.range (transR Cf Cg) ∪ downR '' Cg.reactions
  finite := by
    refine ((((Set.finite_singleton _).union (Set.finite_range _)).union ?_).union
      (Set.finite_range _)).union (Cg.finite.image _)
    exact Set.finite_iUnion fun k => (Cf k).finite.image _
  X := .inp
  Y := .down Cg.Y
  L := some .lead
  X_injective _ _ h := by cases h; rfl
  Y_ne_X _ := by simp
  L_ne_X := by simp
  L_ne_Y := by simp

theorem init_eq (x : ι → ℕ) : (comp Cf Cg).init x = mk 1 x 0 0 := by
  funext s
  cases s with
  | lead => simp [FunCRN.init, FunCRN.leaderConf, FunCRN.inputConf, comp, mk]
  | inp i =>
    have := (comp Cf Cg).inputConf_X x i
    rw [show (comp Cf Cg).X i = .inp i from rfl] at this
    rw [FunCRN.init, Pi.add_apply, this]
    simp [FunCRN.leaderConf, comp, mk]
  | up k s => simp [FunCRN.init, FunCRN.leaderConf, FunCRN.inputConf, comp, mk]
  | down s => simp [FunCRN.init, FunCRN.leaderConf, FunCRN.inputConf, comp, mk]

/-- The step relation applied to `mk`-configurations. -/
theorem step_mk {ℓ : ℕ} {r : ι → ℕ} {U : ∀ k, Sf k → ℕ} {G : Sg → ℕ} {ρ : Reaction (Sp ι κ Sf Sg)}
    (hρ : ρ ∈ (comp Cf Cg).reactions) (hle : ρ.reactants ≤ mk ℓ r U G) :
    (comp Cf Cg).Step (mk ℓ r U G) (mk ℓ r U G - ρ.reactants + ρ.products) :=
  ⟨ρ, hρ, hle, rfl⟩

theorem leaderConf_add_nsmul (N : FunCRN Sg κ) (a : ℕ) :
    a • N.leaderConf + N.leaderConf = (a + 1) • N.leaderConf := by
  rw [add_smul, one_smul]

variable {Cf Cg}

/-- **Simulation invariant.** Every configuration reachable from `mk ℓ r U G` has the form
`mk ℓ' r' U' G'` where each upstream part, together with the `t k` outputs already transferred,
is reachable in `C_k` from `U k` plus the leaders and inputs handed over, and the downstream
part is reachable in `C_g` from `G` plus the handed-over leaders and the transferred inputs. -/
theorem reach_inv {ℓ : ℕ} {r : ι → ℕ} {U : ∀ k, Sf k → ℕ} {G : Sg → ℕ} {D}
    (h : (comp Cf Cg).Reach (mk ℓ r U G) D) :
    ∃ (ℓ' : ℕ) (r' : ι → ℕ) (U' : ∀ k, Sf k → ℕ) (G' : Sg → ℕ) (t : κ → ℕ), D = mk ℓ' r' U' G' ∧ ℓ' ≤ ℓ ∧ r' ≤ r ∧
      (∀ k, (Cf k).Reach (U k + (ℓ - ℓ') • (Cf k).leaderConf + (Cf k).inputConf (r - r'))
        (U' k + Pi.single (Cf k).Y (t k))) ∧
      Cg.Reach (G + (ℓ - ℓ') • Cg.leaderConf + Cg.inputConf t) G' := by
  induction h with
  | refl =>
    refine ⟨ℓ, r, U, G, 0, rfl, le_rfl, le_rfl, fun k => ?_, ?_⟩
    · refine (Reach.refl (U k)).of_eq ?_ ?_ <;> funext s <;>
        simp [FunCRN.inputConf]
    · refine (Reach.refl G).of_eq ?_ rfl
      funext s; simp [FunCRN.inputConf]
  | tail _ hs ih =>
    obtain ⟨ℓ', r', U', G', t, rfl, hℓ, hr, hU, hG⟩ := ih
    obtain ⟨ρ, hρ, hle, rfl⟩ := hs
    rcases hρ with ((((rfl | ⟨i, rfl⟩) | hρ) | ⟨k, rfl⟩) | ⟨ρ, hρ, rfl⟩)
    · -- split
      obtain ⟨h1, -, -, -⟩ := mk_le_mk.mp hle
      refine ⟨ℓ' - 1, r', fun k => U' k + (Cf k).leaderConf, G' + Cg.leaderConf, t, ?_, by omega,
        hr, fun k => ?_, ?_⟩
      · simp only [splitR, mk_sub_add, mk_inj]
        refine ⟨by omega, by simp, funext fun k => by simp, by simp⟩
      · refine ((hU k).add (Cf k).leaderConf).of_eq ?_ ?_
        · rw [show ℓ - (ℓ' - 1) = ℓ - ℓ' + 1 by omega, add_smul, one_smul]
          funext s; simp only [Pi.add_apply]; ring
        · funext s; simp only [Pi.add_apply]; ring
      · refine (hG.add Cg.leaderConf).of_eq ?_ rfl
        rw [show ℓ - (ℓ' - 1) = ℓ - ℓ' + 1 by omega, add_smul, one_smul]
        funext s; simp only [Pi.add_apply]; ring
    · -- fan-out of input `i`
      obtain ⟨-, h2, -, -⟩ := mk_le_mk.mp hle
      have hri : 1 ≤ r' i := by simpa using h2 i
      refine ⟨ℓ', r' - Pi.single i 1, fun k => U' k + (Cf k).inputConf (Pi.single i 1), G', t,
        ?_, hℓ, fun j => ?_, fun k => ?_, hG⟩
      · simp only [fanR, mk_sub_add, mk_inj]
        refine ⟨by simp, by simp, funext fun k => by simp, by simp⟩
      · have : r' j ≤ r j := hr j
        simp only [Pi.sub_apply]; omega
      · refine ((hU k).add ((Cf k).inputConf (Pi.single i 1))).of_eq ?_ ?_
        · rw [add_assoc, ← FunCRN.inputConf_add]
          congr 2
          funext j
          have : r' j ≤ r j := hr j
          by_cases hj : j = i
          · subst hj; simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]; omega
          · simp [hj]
        · funext s; simp only [Pi.add_apply]; ring
    · -- a reaction of an upstream module
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hρ
      obtain ⟨ρ, hρk, rfl⟩ := hk
      obtain ⟨-, -, h3, -⟩ := mk_le_mk.mp hle
      have hk3 : ρ.reactants ≤ U' k := by simpa using h3 k
      refine ⟨ℓ', r', Function.update U' k (U' k - ρ.reactants + ρ.products), G', t, ?_, hℓ,
        hr, fun k' => ?_, hG⟩
      · simp only [upR, mk_sub_add, mk_inj]
        refine ⟨by simp, by simp, funext fun k' => ?_, by simp⟩
        by_cases hk' : k' = k
        · subst hk'; simp
        · simp [hk']
      · by_cases hk' : k' = k
        · subst hk'
          refine ((hU k').tail ⟨ρ, hρk, le_trans hk3 le_self_add, rfl⟩).of_eq rfl ?_
          funext s
          have : ρ.reactants s ≤ U' k' s := hk3 s
          simp only [Function.update_self, Pi.add_apply, Pi.sub_apply]
          rw [Nat.sub_add_comm this]
          ring
        · simpa [hk'] using hU k'
    · -- transfer from module `k`
      obtain ⟨-, -, h3, -⟩ := mk_le_mk.mp hle
      have hY : 1 ≤ U' k (Cf k).Y := by simpa using h3 k (Cf k).Y
      refine ⟨ℓ', r', Function.update U' k (U' k - Pi.single (Cf k).Y 1),
        G' + Cg.inputConf (Pi.single k 1), t + Pi.single k 1, ?_, hℓ, hr, fun k' => ?_, ?_⟩
      · simp only [transR, mk_sub_add, mk_inj]
        refine ⟨by simp, by simp, funext fun k' => ?_, by simp⟩
        by_cases hk' : k' = k
        · subst hk'; simp
        · simp [hk']
      · by_cases hk' : k' = k
        · subst hk'
          refine (hU k').of_eq rfl ?_
          funext s
          by_cases hs : s = (Cf k').Y
          · subst hs; simp; omega
          · simp [hs]
        · simpa [hk'] using hU k'
      · refine (hG.add (Cg.inputConf (Pi.single k 1))).of_eq ?_ rfl
        rw [FunCRN.inputConf_add]; funext s; simp only [Pi.add_apply]; ring
    · -- a reaction of the downstream module
      obtain ⟨-, -, -, h4⟩ := mk_le_mk.mp hle
      refine ⟨ℓ', r', U', G' - ρ.reactants + ρ.products, t, ?_, hℓ, hr, hU, ?_⟩
      · simp only [downR, mk_sub_add, mk_inj]
        exact ⟨by simp, by simp, funext fun k => by simp, trivial⟩
      · exact hG.tail ⟨ρ, hρ, h4, rfl⟩

/-- Running one upstream module inside the composite. -/
theorem reach_lift_up {ℓ : ℕ} {r : ι → ℕ} {U : ∀ k, Sf k → ℕ} {G : Sg → ℕ} {k : κ}
    {W : Sf k → ℕ} (h : (Cf k).Reach (U k) W) :
    (comp Cf Cg).Reach (mk ℓ r U G) (mk ℓ r (Function.update U k W) G) := by
  induction h with
  | refl => simp only [Function.update_eq_self]; exact Reach.refl _
  | tail _ hs ih =>
    rename_i W₁ W₂ _
    obtain ⟨ρ, hρ, hle, rfl⟩ := hs
    refine ih.tail ((step_mk Cf Cg (ρ := upR k ρ) (Or.inl (Or.inl (Or.inr
      (Set.mem_iUnion.mpr ⟨k, ρ, hρ, rfl⟩)))) ?_).congr_right ?_)
    · refine mk_le_mk.mpr ⟨by simp [upR], by simp [upR], fun k' => ?_, by simp [upR]⟩
      by_cases hk : k' = k
      · subst hk; simpa [upR] using hle
      · simp [upR, hk]
    · simp only [upR, mk_sub_add, mk_inj]
      refine ⟨by simp, by simp, funext fun k' => ?_, by simp⟩
      by_cases hk : k' = k
      · subst hk; simp
      · simp [hk]

/-- Running all upstream modules inside the composite. -/
theorem reach_lift_up_all {ℓ : ℕ} {r : ι → ℕ} {U V : ∀ k, Sf k → ℕ} {G : Sg → ℕ}
    (h : ∀ k, (Cf k).Reach (U k) (V k)) :
    (comp Cf Cg).Reach (mk ℓ r U G) (mk ℓ r V G) := by
  classical
  have key : ∀ s : Finset κ,
      (comp Cf Cg).Reach (mk ℓ r U G) (mk ℓ r (fun k => if k ∈ s then V k else U k) G) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Reach.refl _
    | insert k s hk ih =>
      refine ih.trans ((reach_lift_up (k := k) (W := V k) ?_).of_eq rfl ?_)
      · simpa [hk] using h k
      · congr 1
        funext k'
        by_cases hk' : k' = k
        · subst hk'; simp
        · simp [hk', Finset.mem_insert]
  simpa using key Finset.univ

/-- Running the downstream module inside the composite. -/
theorem reach_lift_down {ℓ : ℕ} {r : ι → ℕ} {U : ∀ k, Sf k → ℕ} {G G' : Sg → ℕ}
    (h : Cg.Reach G G') : (comp Cf Cg).Reach (mk ℓ r U G) (mk ℓ r U G') := by
  induction h with
  | refl => exact Reach.refl _
  | tail _ hs ih =>
    obtain ⟨ρ, hρ, hle, rfl⟩ := hs
    refine ih.tail ((step_mk Cf Cg (ρ := downR ρ) (Or.inr ⟨ρ, hρ, rfl⟩)
      (mk_le_mk.mpr ⟨by simp [downR], by simp [downR], fun k => by simp [downR], hle⟩)).congr_right
      ?_)
    simp only [downR, mk_sub_add, mk_inj]
    exact ⟨by simp, by simp, funext fun k => by simp, trivial⟩

/-- The leader splits. -/
theorem reach_split {ℓ : ℕ} {r : ι → ℕ} {U : ∀ k, Sf k → ℕ} {G : Sg → ℕ} :
    (comp Cf Cg).Reach (mk (ℓ + 1) r U G)
      (mk ℓ r (fun k => U k + (Cf k).leaderConf) (G + Cg.leaderConf)) := by
  refine Reach.single ((step_mk Cf Cg (ρ := splitR Cf Cg) (Or.inl (Or.inl (Or.inl (Or.inl rfl))))
    (mk_le_mk.mpr ⟨by simp [splitR], by simp [splitR], fun k => by simp [splitR],
      by simp [splitR]⟩)).congr_right ?_)
  simp only [splitR, mk_sub_add, mk_inj]
  exact ⟨by simp, by simp, funext fun k => by simp, by simp⟩

/-- All remaining inputs are fanned out. -/
theorem reach_fan_all {ℓ : ℕ} {r : ι → ℕ} {U : ∀ k, Sf k → ℕ} {G : Sg → ℕ} :
    (comp Cf Cg).Reach (mk ℓ r U G) (mk ℓ 0 (fun k => U k + (Cf k).inputConf r) G) := by
  induction hn : ∑ i, r i generalizing r U with
  | zero =>
    have : r = 0 := funext fun i => (Finset.sum_eq_zero_iff.mp hn) i (Finset.mem_univ _)
    subst this
    refine (Reach.refl _).of_eq rfl ?_
    congr 1; funext k s; simp [FunCRN.inputConf]
  | succ n ih =>
    obtain ⟨i, hi⟩ : ∃ i, 1 ≤ r i := by
      by_contra hne
      push Not at hne
      have : ∑ i, r i = 0 := Finset.sum_eq_zero fun i _ => by have := hne i; omega
      omega
    have hstep : (comp Cf Cg).Step (mk ℓ r U G)
        (mk ℓ (r - Pi.single i 1) (fun k => U k + (Cf k).inputConf (Pi.single i 1)) G) := by
      refine (step_mk Cf Cg (ρ := fanR Cf i) (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
        (mk_le_mk.mpr ⟨by simp [fanR], fun j => ?_, fun k => by simp [fanR],
          by simp [fanR]⟩)).congr_right ?_
      · by_cases hj : j = i
        · subst hj; simpa [fanR] using hi
        · simp [fanR, hj]
      · simp only [fanR, mk_sub_add, mk_inj]
        exact ⟨by simp, by simp, funext fun k => by simp, by simp⟩
    refine Reach.head hstep ((ih ?_).of_eq rfl ?_)
    · have hterm : ∀ j, r j = (r - Pi.single i 1 : ι → ℕ) j + if j = i then 1 else 0 := by
        intro j
        by_cases hj : j = i
        · subst hj; simp; omega
        · simp [hj]
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
        Finset.sum_ite_eq'] at hn
      simp at hn
      omega
    · congr 1
      funext k
      rw [add_assoc, ← FunCRN.inputConf_add]
      congr 2
      funext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [hj]

/-- All upstream outputs are transferred. -/
theorem reach_transfer_all {ℓ : ℕ} {r : ι → ℕ} {U : ∀ k, Sf k → ℕ} {G : Sg → ℕ} :
    (comp Cf Cg).Reach (mk ℓ r U G)
      (mk ℓ r (fun k => U k - Pi.single (Cf k).Y (U k (Cf k).Y))
        (G + Cg.inputConf (fun k => U k (Cf k).Y))) := by
  induction hn : ∑ k, U k (Cf k).Y generalizing U G with
  | zero =>
    have h0 : ∀ k, U k (Cf k).Y = 0 := fun k =>
      (Finset.sum_eq_zero_iff.mp hn) k (Finset.mem_univ _)
    refine (Reach.refl _).of_eq rfl ?_
    simp only [h0, Pi.single_zero, tsub_zero]
    congr 1
    funext s; simp [FunCRN.inputConf]
  | succ n ih =>
    obtain ⟨k, hk⟩ : ∃ k, 1 ≤ U k (Cf k).Y := by
      by_contra hne
      push Not at hne
      have : ∑ k, U k (Cf k).Y = 0 := Finset.sum_eq_zero fun k _ => by have := hne k; omega
      omega
    set U' := Function.update U k (U k - Pi.single (Cf k).Y 1) with hU'
    have hU'Y : ∀ k', U' k' (Cf k').Y = U k' (Cf k').Y - if k' = k then 1 else 0 := by
      intro k'
      by_cases hk' : k' = k
      · subst hk'; simp [hU']
      · simp [hU', hk']
    have hstep : (comp Cf Cg).Step (mk ℓ r U G) (mk ℓ r U' (G + Cg.inputConf (Pi.single k 1))) := by
      refine (step_mk Cf Cg (ρ := transR Cf Cg k) (Or.inl (Or.inr ⟨k, rfl⟩))
        (mk_le_mk.mpr ⟨by simp [transR], by simp [transR], fun k' => ?_,
          by simp [transR]⟩)).congr_right ?_
      · by_cases hk' : k' = k
        · subst hk'
          intro s
          by_cases hs : s = (Cf k').Y
          · subst hs; simpa [transR] using hk
          · simp [transR, hs]
        · simp [transR, hk']
      · simp only [transR, mk_sub_add, mk_inj]
        refine ⟨by simp, by simp, funext fun k' => ?_, by simp⟩
        by_cases hk' : k' = k
        · subst hk'; simp [hU']
        · simp [hU', hk']
    refine Reach.head hstep ((ih (U := U') ?_).of_eq rfl ?_)
    · rw [Finset.sum_congr rfl (fun k' _ => hU'Y k')]
      have : ∀ k', U k' (Cf k').Y = (U k' (Cf k').Y - if k' = k then 1 else 0) +
          if k' = k then 1 else 0 := by
        intro k'
        by_cases hk' : k' = k
        · subst hk'; simp; omega
        · simp [hk']
      rw [Finset.sum_congr rfl (fun k' _ => this k'), Finset.sum_add_distrib,
        Finset.sum_ite_eq'] at hn
      simp at hn
      omega
    · rw [mk_inj]
      refine ⟨rfl, rfl, funext fun k' => ?_, ?_⟩
      · funext s
        by_cases hk' : k' = k
        · subst hk'
          by_cases hs : s = (Cf k').Y
          · subst hs; simp [hU']
          · simp [hU', hs]
        · simp [hU', hk']
      · rw [add_assoc, ← FunCRN.inputConf_add]
        congr 2
        funext k'
        rw [Pi.add_apply, hU'Y]
        by_cases hk' : k' = k
        · subst hk'; simp; omega
        · simp [hk']

/-- **Composition (Observation 2.2, generalized to several upstream modules).** If every `C_k`
is output-oblivious and stably computes `f k`, and `C_g` stably computes `g`, then the composite
CRN stably computes `x ↦ g (f · x)`. -/
theorem stablyComputes {f : κ → (ι → ℕ) → ℕ} {g : (κ → ℕ) → ℕ}
    (hfO : ∀ k, (Cf k).OutputOblivious) (hf : ∀ k, (Cf k).StablyComputes (f k))
    (hg : Cg.StablyComputes g) :
    (comp Cf Cg).StablyComputes (fun x => g (fun k => f k x)) := by
  intro x D hD
  rw [init_eq] at hD
  obtain ⟨ℓ', r', U', G', t, rfl, hℓ, hr, hU, hG⟩ := reach_inv hD
  -- Step 1: the leader has split
  obtain ⟨U₁, G₁, h₁, hU₁, hG₁⟩ : ∃ U₁ G₁, (comp Cf Cg).Reach (mk ℓ' r' U' G') (mk 0 r' U₁ G₁) ∧
      (∀ k, (Cf k).Reach ((Cf k).init (x - r')) (U₁ k + Pi.single (Cf k).Y (t k))) ∧
      Cg.Reach (Cg.init t) G₁ := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
    · refine ⟨U', G', Reach.refl _, fun k => (hU k).of_eq ?_ rfl, hG.of_eq ?_ rfl⟩
      · simp [FunCRN.init, add_comm]
      · simp [FunCRN.init, add_comm]
    · refine ⟨fun k => U' k + (Cf k).leaderConf, G' + Cg.leaderConf, reach_split,
        fun k => ((hU k).add (Cf k).leaderConf).of_eq ?_ ?_, (hG.add Cg.leaderConf).of_eq ?_ rfl⟩
      · simp [FunCRN.init, add_comm]
      · funext s; simp only [Pi.add_apply]; ring
      · simp [FunCRN.init, add_comm]
  -- Step 2: fan out the remaining inputs
  have h₂ := reach_fan_all (Cf := Cf) (Cg := Cg) (ℓ := 0) (r := r') (U := U₁) (G := G₁)
  have hU₂ : ∀ k, (Cf k).Reach ((Cf k).init x)
      ((U₁ k + (Cf k).inputConf r') + Pi.single (Cf k).Y (t k)) := fun k => by
    refine ((hU₁ k).add ((Cf k).inputConf r')).of_eq ?_ ?_
    · rw [← FunCRN.init_add]; congr 1; funext i; have : r' i ≤ x i := hr i
      simp only [Pi.add_apply, Pi.sub_apply]; omega
    · funext s; simp only [Pi.add_apply]; ring
  -- Step 3: every upstream module reaches its stable output
  choose O hO₁ hO₂ hO₃ using fun k => hf k x _ (hU₂ k)
  choose W hW₁ hW₂ using fun k => (Cf k).reach_split_output (hfO k) (hO₁ k)
  have h₃ := reach_lift_up_all (Cf := Cf) (Cg := Cg) (ℓ := 0) (r := 0) (G := G₁) hW₂
  -- Step 4: transfer all outputs
  have h₄ := reach_transfer_all (Cf := Cf) (Cg := Cg) (ℓ := 0) (r := 0) (U := W) (G := G₁)
  have hWY : ∀ k, t k + W k (Cf k).Y = f k x := fun k => by
    rw [← hO₂ k, hW₁ k]; simp [add_comm]
  have hG₄ : Cg.Reach (Cg.init (fun k => f k x)) (G₁ + Cg.inputConf (fun k => W k (Cf k).Y)) := by
    refine (hG₁.add _).of_eq ?_ rfl
    rw [← FunCRN.init_add]; congr 1; funext k; exact (hWY k)
  -- Step 5: the downstream module reaches its stable output
  obtain ⟨Og, hOg₁, hOg₂, hOg₃⟩ := hg _ _ hG₄
  have h₅ := reach_lift_down (Cf := Cf) (Cg := Cg) (ℓ := 0) (r := 0)
    (U := fun k => W k - Pi.single (Cf k).Y (W k (Cf k).Y)) hOg₁
  refine ⟨_, h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))), hOg₂, ?_⟩
  -- stability
  intro E hE
  obtain ⟨ℓ'', r'', U'', G'', t'', rfl, hℓ'', hr'', hU'', hG''⟩ := reach_inv hE
  have ht'' : ∀ k, t'' k = 0 := fun k => by
    have hk : (Cf k).Reach (O k)
        (U'' k + Pi.single (Cf k).Y (t'' k) + Pi.single (Cf k).Y (f k x)) := by
      refine ((hU'' k).add (Pi.single (Cf k).Y (f k x))).of_eq ?_ rfl
      have h1 := hWY k
      funext s
      rw [hW₁ k]
      by_cases hs : s = (Cf k).Y
      · subst hs; simp [FunCRN.inputConf]; omega
      · simp [FunCRN.inputConf, hs]
    have := hO₃ k _ hk
    simp only [Pi.add_apply, Pi.single_eq_same] at this
    rw [hO₂ k] at this
    omega
  have hG0 : Cg.Reach Og G'' := hG''.of_eq (by
    have : t'' = 0 := funext ht''
    subst this; funext s; simp [FunCRN.inputConf]) rfl
  exact hOg₃ _ hG0

/-- The composite is output-oblivious if the downstream module is. -/
theorem outputOblivious (hgO : Cg.OutputOblivious) : (comp Cf Cg).OutputOblivious := by
  rintro ρ ((((rfl | ⟨i, rfl⟩) | hρ) | ⟨k, rfl⟩) | ⟨ρ, hρ, rfl⟩)
  · rfl
  · rfl
  · obtain ⟨k, ρ, -, rfl⟩ := Set.mem_iUnion.mp hρ; rfl
  · rfl
  · exact hgO ρ hρ

end Comp

open _root_.Podc.ComposableCRN.Comp in
/-- **Closure under composition** (Observation 2.2 and the remark after it): if each `f k` is
obliviously-computable and `g : ℕ^κ → ℕ` is obliviously-computable, so is `x ↦ g (f₁ x, …)`. -/
theorem ObliviouslyComputable.comp {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {g : (κ → ℕ) → ℕ} {f : κ → (ι → ℕ) → ℕ} (hg : ObliviouslyComputable g)
    (hf : ∀ k, ObliviouslyComputable (f k)) :
    ObliviouslyComputable (fun x => g (fun k => f k x)) := by
  obtain ⟨Sg, _, _, Cg, -, hgO, hgS⟩ := hg
  choose Sf iF iD Cf _hL hfO hfS using hf
  exact ⟨Sp ι κ Sf Sg, inferInstance, inferInstance, Comp.comp Cf Cg, rfl,
    outputOblivious hgO, stablyComputes hfO hfS hgS⟩

open _root_.Podc.ComposableCRN.Comp in
/-- Observation 2.2: if `f` is computed by an output-oblivious CRN and `g` by any CRN, the
composite stably computes `g ∘ f` (here for any number of upstream modules). -/
theorem StablyComputable.comp_oblivious {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {g : (κ → ℕ) → ℕ} {f : κ → (ι → ℕ) → ℕ} (hg : StablyComputable g)
    (hf : ∀ k, ObliviouslyComputable (f k)) :
    StablyComputable (fun x => g (fun k => f k x)) := by
  obtain ⟨Sg, _, _, Cg, hgS⟩ := hg
  choose Sf iF iD Cf _hL hfO hfS using hf
  exact ⟨Sp ι κ Sf Sg, inferInstance, inferInstance, Comp.comp Cf Cg,
    stablyComputes hfO hfS hgS⟩

end Podc.ComposableCRN
