import Mathlib

-- CSLib candidate: Cslib/Computability/ChemicalReactionNetworks/Basic.lean
/-!
# Discrete chemical reaction networks and output-oblivious stable computation

Severson, Haley, Doty. *Composable computation in discrete chemical reaction networks.* PODC 2019
(arXiv:1903.02637v2), Section 2.

* A CRN over a finite species type `S` is a finite set of reactions `(R, P) ∈ ℕ^S × ℕ^S`;
  a configuration is `C : S → ℕ`; reaction `(R, P)` is applicable to `C` if `R ≤ C` and
  yields `C - R + P` (§2.2).
* A function-computing CRN (`FunCRN S ι`) has input species `X i` (`i : ι`), an output species
  `Y` and (optionally) a leader species `L`; all distinct. The initial configuration for input
  `x : ι → ℕ` has `x i` copies of `X i`, one `L` (if there is a leader) and nothing else.
* `StablyComputes f`: from every configuration reachable from `I_x` a stable configuration
  with output `f x` is reachable; `OutputOblivious`: `Y` is never a reactant (§2.3).
* `ObliviouslyComputable f`: stably computed by an output-oblivious CRN with a leader.

The paper's `ℕ^d` is `ι → ℕ` for a finite index type `ι` (`ι = Fin d`).
-/

namespace Podc.ComposableCRN

/-- A configuration: a count for every species. -/
abbrev Config (S : Type*) := S → ℕ

/-- A reaction `(R, P)`: `reactants` are consumed, `products` produced. -/
structure Reaction (S : Type*) where
  /-- Counts of consumed species `R`. -/
  reactants : S → ℕ
  /-- Counts of produced species `P`. -/
  products : S → ℕ

/-- A chemical reaction network: a finite set of reactions. -/
structure CRN (S : Type*) where
  /-- The reactions. -/
  reactions : Set (Reaction S)
  /-- There are finitely many reactions. -/
  finite : reactions.Finite

namespace CRN

variable {S : Type*} (N : CRN S)

/-- One reaction step `C → D`. -/
def Step (C D : Config S) : Prop :=
  ∃ ρ ∈ N.reactions, ρ.reactants ≤ C ∧ D = C - ρ.reactants + ρ.products

/-- Reachability `C →* D`. -/
def Reach : Config S → Config S → Prop := Relation.ReflTransGen N.Step

variable {N}

theorem Reach.refl (C : Config S) : N.Reach C C := Relation.ReflTransGen.refl

theorem Reach.trans {A B C : Config S} (h₁ : N.Reach A B) (h₂ : N.Reach B C) : N.Reach A C :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Reach.single {A B : Config S} (h : N.Step A B) : N.Reach A B :=
  Relation.ReflTransGen.single h

theorem Reach.tail {A B C : Config S} (h₁ : N.Reach A B) (h₂ : N.Step B C) : N.Reach A C :=
  Relation.ReflTransGen.tail h₁ h₂

theorem Reach.head {A B C : Config S} (h₁ : N.Step A B) (h₂ : N.Reach B C) : N.Reach A C :=
  Relation.ReflTransGen.head h₁ h₂

/-- Steps are additive: `C → D` implies `C + E → D + E`. -/
theorem Step.add {C D : Config S} (h : N.Step C D) (E : Config S) : N.Step (C + E) (D + E) := by
  obtain ⟨ρ, hρ, hle, rfl⟩ := h
  refine ⟨ρ, hρ, fun s => le_trans (hle s) (Nat.le_add_right _ _), ?_⟩
  funext s
  have := hle s
  change C s - ρ.reactants s + ρ.products s + E s = C s + E s - ρ.reactants s + ρ.products s
  rw [Nat.sub_add_comm this]; ring

/-- Reachability is additive (§2.2): `C →* D` implies `C + E →* D + E`. -/
theorem Reach.add {C D : Config S} (h : N.Reach C D) (E : Config S) :
    N.Reach (C + E) (D + E) := by
  induction h with
  | refl => exact Reach.refl _
  | tail _ hs ih => exact ih.tail (hs.add E)

theorem Reach.add_left {C D : Config S} (h : N.Reach C D) (E : Config S) :
    N.Reach (E + C) (E + D) := by
  simpa [add_comm] using h.add E

/-- `Y` is never a reactant. -/
def NeverConsumes (Y : S) : Prop := ∀ ρ ∈ N.reactions, ρ.reactants Y = 0

theorem NeverConsumes.step_le {Y : S} (hY : N.NeverConsumes Y) {C D : Config S}
    (h : N.Step C D) : C Y ≤ D Y := by
  obtain ⟨ρ, hρ, _, rfl⟩ := h
  simp [hY ρ hρ]

/-- A species that is never consumed never decreases. -/
theorem NeverConsumes.reach_le {Y : S} (hY : N.NeverConsumes Y) {C D : Config S}
    (h : N.Reach C D) : C Y ≤ D Y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans (hY.step_le hs)

/-- A configuration is terminal if no reaction is applicable. -/
def Terminal (C : Config S) : Prop := ∀ ρ ∈ N.reactions, ¬ ρ.reactants ≤ C

theorem Terminal.reach_eq {C D : Config S} (hC : N.Terminal C) (h : N.Reach C D) : D = C := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨ρ, hρ, hle, -⟩ := hs
    exact absurd hle (hC ρ hρ)

end CRN

/-- A CRN computing a function `ℕ^ι → ℕ`: input species `X i`, output species `Y`, optional
leader species `L`, all pairwise distinct (§2.2). -/
structure FunCRN (S ι : Type*) extends CRN S where
  /-- Input species. -/
  X : ι → S
  /-- Output species. -/
  Y : S
  /-- Leader species (`none`: leaderless CRN, §9). -/
  L : Option S
  X_injective : Function.Injective X
  Y_ne_X : ∀ i, Y ≠ X i
  L_ne_X : ∀ l ∈ L, ∀ i, l ≠ X i
  L_ne_Y : ∀ l ∈ L, l ≠ Y

namespace FunCRN

variable {S ι : Type*} [DecidableEq S] [Fintype ι] (C : FunCRN S ι)

/-- The input part `∑ᵢ x(i) Xᵢ` of the initial configuration. -/
def inputConf (x : ι → ℕ) : Config S := fun s => ∑ i, if C.X i = s then x i else 0

/-- The leader part of the initial configuration (one `L`, if there is a leader). -/
def leaderConf : Config S := fun s => if C.L = some s then 1 else 0

/-- The initial configuration `I_x`. -/
def init (x : ι → ℕ) : Config S := C.inputConf x + C.leaderConf

theorem inputConf_add (x y : ι → ℕ) : C.inputConf (x + y) = C.inputConf x + C.inputConf y := by
  funext s
  simp only [inputConf, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem init_add (x y : ι → ℕ) : C.init (x + y) = C.init x + C.inputConf y := by
  simp only [init, inputConf_add]
  abel

theorem inputConf_X (x : ι → ℕ) (i : ι) : C.inputConf x (C.X i) = x i := by
  rw [inputConf, Finset.sum_eq_single i (fun j _ hj => by simp [C.X_injective.ne hj]) (by simp)]
  simp

theorem inputConf_of_ne (x : ι → ℕ) (s : S) (hs : ∀ i, C.X i ≠ s) : C.inputConf x s = 0 := by
  simp [inputConf, hs]

theorem inputConf_Y (x : ι → ℕ) : C.inputConf x C.Y = 0 :=
  C.inputConf_of_ne x _ fun i h => C.Y_ne_X i h.symm

omit [Fintype ι] in
theorem leaderConf_Y : C.leaderConf C.Y = 0 := by
  simp only [leaderConf, ite_eq_right_iff, one_ne_zero, imp_false]
  intro h
  exact C.L_ne_Y _ h rfl

theorem init_Y (x : ι → ℕ) : C.init x C.Y = 0 := by
  simp [init, inputConf_Y, leaderConf_Y]

/-- `O` is stable: its output count never changes again. -/
def Stable (O : Config S) : Prop := ∀ D, C.Reach O D → D C.Y = O C.Y

/-- `C` stably computes `f` (§2.2): from every configuration reachable from `I_x` some stable
configuration with output `f x` is reachable. -/
def StablyComputes (f : (ι → ℕ) → ℕ) : Prop :=
  ∀ x D, C.Reach (C.init x) D → ∃ O, C.Reach D O ∧ O C.Y = f x ∧ C.Stable O

/-- `C` is output-oblivious (§2.3): the output species is never a reactant. -/
def OutputOblivious : Prop := C.NeverConsumes C.Y

theorem StablyComputes.exists {C : FunCRN S ι} {f : (ι → ℕ) → ℕ} (h : C.StablyComputes f) (x : ι → ℕ) :
    ∃ O, C.Reach (C.init x) O ∧ O C.Y = f x ∧ C.Stable O :=
  h x _ (CRN.Reach.refl _)

end FunCRN

/-- `f` is stably computable by a CRN (§2.2), with or without a leader (both give the same class
of functions, the semilinear ones [10, 17]). -/
def StablyComputable {ι : Type} [Fintype ι] (f : (ι → ℕ) → ℕ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (C : FunCRN S ι), C.StablyComputes f

/-- `f` is obliviously-computable (§2.3): stably computed by an output-oblivious CRN with a
leader. -/
def ObliviouslyComputable {ι : Type} [Fintype ι] (f : (ι → ℕ) → ℕ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (C : FunCRN S ι),
    C.L.isSome ∧ C.OutputOblivious ∧ C.StablyComputes f

/-- `f` is obliviously-computable by a leaderless CRN (§9). -/
def LeaderlessObliviouslyComputable {ι : Type} [Fintype ι] (f : (ι → ℕ) → ℕ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (C : FunCRN S ι),
    C.L = none ∧ C.OutputOblivious ∧ C.StablyComputes f

/-- A function `ℕ^ι → ℕ` is semilinear if its graph is a semilinear set (§2.4; the paper's
Definition 2.6 is an equivalent form, [10, Lemma 4.3]). -/
def IsSemilinearFun {ι : Type*} (f : (ι → ℕ) → ℕ) : Prop :=
  IsSemilinearSet {p : (ι → ℕ) × ℕ | f p.1 = p.2}

/-- The "only if" half of Lemma 2.7 ([10], Chen–Doty–Soloveichik): every stably computable
function is semilinear. Cited by the paper, not proved; used here only as a hypothesis. -/
def StablyComputableImpliesSemilinear : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : (ι → ℕ) → ℕ), StablyComputable f → IsSemilinearFun f

/-- Definition 5.1: `g : ℕ^ι → ℤ` is quilt-affine if it is nondecreasing and
`g x = ∇g · x + B (x mod p)` for some period `p > 0`, gradient `∇g ∈ ℚ^ι_{≥0}` and periodic
offset `B : (ℤ/pℤ)^ι → ℚ`. -/
def IsQuiltAffine {ι : Type*} [Fintype ι] (g : (ι → ℕ) → ℤ) : Prop :=
  Monotone g ∧ ∃ (p : ℕ) (_ : 0 < p) (grad : ι → ℚ) (B : (ι → ZMod p) → ℚ),
    (∀ i, 0 ≤ grad i) ∧ ∀ x, (g x : ℚ) = ∑ i, grad i * x i + B (fun i => (x i : ZMod p))

end Podc.ComposableCRN
