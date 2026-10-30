import Papers.PODC2022.PPLeadersStateComplexity.Model
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ENat.Lattice

/-!
# Protocols, stable computation and interaction-width (Sections 2–4 of Leroux)

A protocol `(P, →*, ρ_L, I, γ)` has a finite set of states `P`, an *additive preorder* `→*` on
`P`-configurations (agents may be created and destroyed), a configuration of leaders `ρ_L`, a set
of initial states `I` and an output function `γ : P → {0, ★, 1}`. It *stably computes* a
predicate `φ : ℕ^I → {0, 1}` if every configuration reachable from an initial configuration
`ρ_L + ρ|_P` can reach a `φ(ρ)`-output stable configuration.

The interaction-width of an additive preorder `R` is the least `m` such that every `(α, β) ∈ R`
is realised by a word of transitions of `R` of width `≤ m`. A protocol of finite width is the
reachability relation of the finite Petri net `{t ∈ R | |t| ≤ m}` (`Protocol.reach_iff`).

## Model choices

* `ℕ^I` is represented by the `P`-configurations vanishing outside `I`; `ρ|_P` is then `ρ`.
* The predicate is a `Bool`-valued function on such configurations.
* `HasWidthLE R m` is "width `≤ m`"; `Protocol.width` is the paper's `width` as an `ℕ∞`.
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Output values `{0, ★, 1}`. -/
inductive Out
  | zero
  | star
  | one
  deriving DecidableEq

/-- A protocol `(P, →*, ρ_L, I, γ)`; `R` is the additive preorder `→*`. -/
structure Protocol (P : Type*) [Fintype P] [DecidableEq P] where
  /-- The additive preorder `→*`. -/
  R : Config P → Config P → Prop
  refl : ∀ α, R α α
  trans : ∀ α β γ, R α β → R β γ → R α γ
  add : ∀ α β ρ, R α β → R (α + ρ) (β + ρ)
  /-- The configuration of leaders `ρ_L`. -/
  leaders : Config P
  /-- The set of initial states. -/
  I : Finset P
  /-- The output function. -/
  γ : P → Out

namespace Protocol

variable (Pr : Protocol P)

/-- `γ(ρ) = {j | ∃ p, ρ(p) > 0 ∧ γ(p) = j}`. -/
def outputs (ρ : Config P) : Set Out := {j | ∃ p, 0 < ρ p ∧ Pr.γ p = j}

/-- The `0`-output stable configurations `S₀`. -/
def S0 : Set (Config P) := {α | ∀ β, Pr.R α β → Pr.outputs β ⊆ {Out.zero}}

/-- The `1`-output stable configurations `S₁`. -/
def S1 : Set (Config P) := {α | ∀ β, Pr.R α β → Pr.outputs β = {Out.one}}

/-- `S_b` for `b ∈ {0, 1}`. -/
def stable (b : Bool) : Set (Config P) := if b then Pr.S1 else Pr.S0

/-- `ρ ∈ ℕ^I`, represented as a `P`-configuration vanishing outside `I`. -/
def IsInput (ρ : Config P) : Prop := ∀ p ∉ Pr.I, ρ p = 0

/-- The protocol stably computes `φ`: for every `ρ ∈ ℕ^I` and every `α` with
`ρ_L + ρ|_P →* α` there is `β ∈ S_{φ(ρ)}` with `α →* β`. -/
def StablyComputes (φ : Config P → Bool) : Prop :=
  ∀ ρ, Pr.IsInput ρ → ∀ α, Pr.R (Pr.leaders + ρ) α → ∃ β, Pr.R α β ∧ β ∈ Pr.stable (φ ρ)

/-- The protocol is conservative. -/
def Conservative : Prop := ∀ α β, Pr.R α β → size α = size β

/-- The number of leaders `|ρ_L|`. -/
def numLeaders : ℕ := size Pr.leaders

end Protocol

/-- The counting predicate `φ_{i ≥ n}`: `ρ ↦ [ρ(i) ≥ n]`. -/
def countingPred (i : P) (n : ℕ) (ρ : Config P) : Bool := decide (n ≤ ρ i)

/-- The protocol stably computes the `(i ≥ n)` predicate (with `I = {i}`). -/
def Protocol.StablyComputesGe (Pr : Protocol P) (i : P) (n : ℕ) : Prop :=
  Pr.I = {i} ∧ Pr.StablyComputes (countingPred i n)

/-! ### Interaction-width (Section 3) -/

/-- `R` has interaction-width at most `m`: every pair of `R` is realised by a word of
transitions of `R` of width `≤ m`. -/
def HasWidthLE (R : Config P → Config P → Prop) (m : ℕ) : Prop :=
  ∀ α β, R α β → ∃ σ : List (Trans P), (∀ t ∈ σ, R t.1 t.2 ∧ t.width ≤ m) ∧ Run σ α β

/-- The interaction-width `width(R) ∈ ℕ ∪ {ω}`. -/
noncomputable def width (R : Config P → Config P → Prop) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : HasWidthLE R m), (m : ℕ∞)

theorem hasWidthLE_of_width_le {R : Config P → Config P → Prop} {m : ℕ} (h : width R ≤ m) :
    ∃ m' ≤ m, HasWidthLE R m' := by
  classical
  by_contra hne
  push_neg at hne
  have : (m : ℕ∞) < width R := by
    simp only [width]
    refine lt_of_lt_of_le (ENat.coe_lt_coe.2 (Nat.lt_succ_self m)) (le_iInf₂ fun m' hm' => ?_)
    have := hne m'
    by_contra hlt
    push_neg at hlt
    exact this (by exact_mod_cast Order.lt_add_one_iff.1 (by exact_mod_cast hlt)) hm'
  exact absurd h (not_le.2 this)

theorem width_le_of_hasWidthLE {R : Config P → Config P → Prop} {m : ℕ} (h : HasWidthLE R m) :
    width R ≤ m :=
  iInf₂_le m h

/-- All configurations with entries `≤ m`. -/
def box (m : ℕ) : Finset (Config P) := Fintype.piFinset fun _ => Finset.range (m + 1)

theorem mem_box {m : ℕ} {ρ : Config P} : ρ ∈ box m ↔ ∀ p, ρ p ≤ m := by
  simp [box, Fintype.mem_piFinset, Nat.lt_succ_iff]

/-- The Petri net `{t ∈ R | |t| ≤ m}`. -/
noncomputable def widthNet (R : Config P → Config P → Prop) (m : ℕ) : Finset (Trans P) := by
  classical
  exact ((box m) ×ˢ (box m)).filter fun t => R t.1 t.2 ∧ t.width ≤ m

theorem mem_widthNet {R : Config P → Config P → Prop} {m : ℕ} {t : Trans P} :
    t ∈ widthNet R m ↔ R t.1 t.2 ∧ t.width ≤ m := by
  classical
  simp only [widthNet, Finset.mem_filter, Finset.mem_product, mem_box, and_iff_right_iff_imp]
  rintro ⟨-, h⟩
  constructor
  · intro p
    exact (le_supNorm _ p).trans ((supNorm_le_size _).trans
      ((le_max_left _ _).trans h))
  · intro p
    exact (le_supNorm _ p).trans ((supNorm_le_size _).trans
      ((le_max_right _ _).trans h))

theorem netNorm_widthNet_le (R : Config P → Config P → Prop) (m : ℕ) :
    netNorm (widthNet R m) ≤ m := by
  simp only [netNorm, Finset.sup_le_iff]
  intro t ht
  exact (Trans.supNorm_le_width t).trans (mem_widthNet.1 ht).2

/-- A run of transitions of an additive preorder stays in the preorder. -/
theorem run_sub_preorder {R : Config P → Config P → Prop} (hrefl : ∀ α, R α α)
    (htrans : ∀ α β γ, R α β → R β γ → R α γ) (hadd : ∀ α β ρ, R α β → R (α + ρ) (β + ρ))
    {σ : List (Trans P)} (hσ : ∀ t ∈ σ, R t.1 t.2) {α β : Config P} (h : Run σ α β) :
    R α β := by
  induction σ generalizing α with
  | nil => rw [h]; exact hrefl _
  | cons t σ ih =>
    obtain ⟨γ, ⟨ρ, rfl, rfl⟩, h2⟩ := h
    exact htrans _ _ _ (hadd _ _ _ (hσ t (List.mem_cons_self ..)))
      (ih (fun t' ht' => hσ t' (List.mem_cons_of_mem _ ht')) h2)

/-- **Section 3.** An additive preorder of interaction-width `≤ m` is the reachability relation
of the Petri net `{t ∈ R | |t| ≤ m}`. -/
theorem Protocol.reach_iff (Pr : Protocol P) {m : ℕ} (hw : HasWidthLE Pr.R m) {α β : Config P} :
    Pr.R α β ↔ Reach (widthNet Pr.R m) α β := by
  constructor
  · intro h
    obtain ⟨σ, hσ, hrun⟩ := hw α β h
    exact ⟨σ, fun t ht => mem_widthNet.2 (hσ t ht), hrun⟩
  · rintro ⟨σ, hσ, hrun⟩
    exact run_sub_preorder Pr.refl Pr.trans Pr.add (fun t ht => (mem_widthNet.1 (hσ t ht)).1) hrun

/-- **Section 3.** The reachability relation of a Petri net `T` is an additive preorder of
interaction-width at most `max_{t ∈ T} |t|`. -/
theorem hasWidthLE_reach (T : Finset (Trans P)) :
    HasWidthLE (Reach T) (T.sup Trans.width) := by
  rintro α β ⟨σ, hσ, h⟩
  refine ⟨σ, fun t ht => ⟨⟨[t], fun u hu => ?_, ?_⟩, Finset.le_sup (f := Trans.width) (hσ t ht)⟩, h⟩
  · simp only [List.mem_singleton] at hu; exact hu ▸ hσ t ht
  · exact run_singleton.2 ⟨0, by simp, by simp⟩

/-- The protocol of a Petri net. -/
def Protocol.ofNet (T : Finset (Trans P)) (leaders : Config P) (I : Finset P) (γ : P → Out) :
    Protocol P where
  R := Reach T
  refl := Reach.refl T
  trans _ _ _ := Reach.trans
  add _ _ ρ h := h.add ρ
  leaders := leaders
  I := I
  γ := γ

end Podc.PPLeadersStateComplexity
