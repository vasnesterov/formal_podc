import Cslib.Computability.Distributed.Byzantine.Specs

-- CSLib candidate: append to Cslib/Computability/Distributed/Byzantine/Specs.lean

/-!
# Specifications of agreement problems: broadcast, interactive consistency, approximate agreement

More clauses of the shared problem vocabulary `Cslib.Byzantine.Problem` (see
`Cslib.Computability.Distributed.Byzantine.Specs` for the conventions: inputs `inp : P → V`,
honest set `H : Set P`, decision relation `dec : P → O → Prop`; a paper with a faulty set
`F : Finset P` uses `H = (↑F)ᶜ`, and then `p ∈ H` is definitionally `p ∉ F`).

## Main definitions

* `SenderValidity inp H s dec`: an honest sender's input is decided by every honest process
  (validity of Byzantine broadcast and gradecast).
* `VectorValidity inp H dec`: honest decision vectors carry the honest inputs (validity of
  interactive consistency).
* `InputValidity inp H dec`: honest decisions are honest inputs (validity of consensus with
  "honest-input" validity).
* `InRange inp H v`: `v` lies between two honest inputs.
* `RangeValidity inp H dec`: every honest decision is `InRange` (validity of approximate
  agreement).
* `EpsAgreement ε H dec`: any two honest decisions are at distance at most `ε`.
* `ApproxAgreement ε`: `ε`-approximate agreement, i.e. termination, range validity and
  `ε`-agreement.

## Main statements

* `bb_iff`, `ic_iff`, `weakAgreement_iff`: CSLib's lock-step `BB`, `IC` and `WeakAgreement` are
  conjunctions of these clauses (by `Iff.rfl`; `ba_iff` is the case of `BA`).
* `InRange.of_le_of_le`, `InRange.eq_of_forall_eq`, `inRange_iff_exists`: basic facts on ranges.
-/

namespace Cslib.Byzantine.Problem

variable {P I V : Type*}

/-! ### Broadcast and interactive consistency -/

section Relations

variable (inp : P → V) (H : Set P)

/-- **Sender validity** (validity of Byzantine broadcast with sender `s`): if `s` is honest, every
honest process decides the input of `s`. -/
def SenderValidity (s : P) (dec : P → V → Prop) : Prop := s ∈ H → ∀ p ∈ H, dec p (inp s)

/-- **Vector validity** (validity of interactive consistency): in every decision vector of an
honest process, the entry of each honest process is its input. -/
def VectorValidity (dec : P → (P → V) → Prop) : Prop :=
  ∀ p ∈ H, ∀ d, dec p d → ∀ q ∈ H, d q = inp q

/-- **Input validity** (honest-input validity): every decision of an honest process is the input of
some honest process. -/
def InputValidity (dec : P → V → Prop) : Prop := ∀ p ∈ H, ∀ v, dec p v → ∃ q ∈ H, inp q = v

/-- CSLib's lock-step Byzantine broadcast is termination, sender validity and agreement. -/
theorem bb_iff (s : P) (dec : P → V → Prop) :
    LockStep.BB s inp H dec ↔ Termination H dec ∧ SenderValidity inp H s dec ∧ Agreement H dec :=
  Iff.rfl

/-- CSLib's lock-step interactive consistency is termination, vector validity and agreement. -/
theorem ic_iff (dec : P → (P → V) → Prop) :
    LockStep.IC inp H dec ↔ Termination H dec ∧ VectorValidity inp H dec ∧ Agreement H dec :=
  Iff.rfl

/-- CSLib's lock-step weak agreement is agreement on the non-`⊥` outputs. -/
theorem weakAgreement_iff (x : P → I) (dec : P → Option V → Prop) :
    LockStep.WeakAgreement x H dec ↔ Agreement H fun p v => dec p (some v) :=
  Iff.rfl

end Relations

/-! ### Approximate agreement -/

section Range

variable {inp : P → V} {H H' : Set P} {v w x : V}

/-- `v` lies in the **range of the honest inputs**: `inp p ≤ v ≤ inp q` for some honest `p` and
`q` (for real inputs: `v` lies in the interval `[min, max]` of the honest inputs). -/
def InRange [LE V] (inp : P → V) (H : Set P) (v : V) : Prop :=
  (∃ p ∈ H, inp p ≤ v) ∧ ∃ q ∈ H, v ≤ inp q

/-- `InRange` with both witnesses up front. -/
theorem inRange_iff_exists [LE V] :
    InRange inp H v ↔ ∃ p ∈ H, ∃ q ∈ H, inp p ≤ v ∧ v ≤ inp q :=
  ⟨fun ⟨⟨p, hp, h₁⟩, q, hq, h₂⟩ => ⟨p, hp, q, hq, h₁, h₂⟩,
    fun ⟨p, hp, q, hq, h₁, h₂⟩ => ⟨⟨p, hp, h₁⟩, q, hq, h₂⟩⟩

/-- An honest input lies in the honest range. -/
theorem InRange.self [Preorder V] {p : P} (hp : p ∈ H) : InRange inp H (inp p) :=
  ⟨⟨p, hp, le_rfl⟩, p, hp, le_rfl⟩

/-- The honest range is convex: a value between two values of the range is in the range. -/
theorem InRange.of_le_of_le [Preorder V] (hv : InRange inp H v) (hw : InRange inp H w) {u : V}
    (h₁ : v ≤ u) (h₂ : u ≤ w) : InRange inp H u :=
  ⟨hv.1.imp fun _ ⟨hp, h⟩ => ⟨hp, h.trans h₁⟩, hw.2.imp fun _ ⟨hq, h⟩ => ⟨hq, h₂.trans h⟩⟩

/-- The range grows with the set of processes. -/
theorem InRange.mono [LE V] (h : InRange inp H v) (hH : H ⊆ H') : InRange inp H' v :=
  ⟨h.1.imp fun _ ⟨hp, h⟩ => ⟨hH hp, h⟩, h.2.imp fun _ ⟨hq, h⟩ => ⟨hH hq, h⟩⟩

/-- If all honest inputs are `x`, the only value in the honest range is `x`. -/
theorem InRange.eq_of_forall_eq [PartialOrder V] (h : InRange inp H v)
    (hx : ∀ p ∈ H, inp p = x) : v = x := by
  obtain ⟨⟨p, hp, h₁⟩, q, hq, h₂⟩ := h
  rw [hx p hp] at h₁
  rw [hx q hq] at h₂
  exact le_antisymm h₂ h₁

end Range

section Approx

/-- **Range validity** (validity of approximate agreement): every decision of an honest process
lies in the range of the honest inputs. -/
def RangeValidity [LE V] (inp : P → V) (H : Set P) (dec : P → V → Prop) : Prop :=
  ∀ p ∈ H, ∀ v, dec p v → InRange inp H v

/-- **`ε`-agreement**: any two decisions of honest processes are at distance at most `ε`. -/
def EpsAgreement [Lattice V] [AddGroup V] (ε : V) (H : Set P) (dec : P → V → Prop) : Prop :=
  ∀ p ∈ H, ∀ q ∈ H, ∀ v w, dec p v → dec q w → |v - w| ≤ ε

/-- **`ε`-approximate agreement**: every honest process decides (termination), every honest
decision lies in the range of the honest inputs (validity), and any two honest decisions are at
distance at most `ε` (`ε`-agreement). -/
def ApproxAgreement [Lattice V] [AddGroup V] (ε : V) : LockStep.Spec P V V := fun inp H dec =>
  Termination H dec ∧ RangeValidity inp H dec ∧ EpsAgreement ε H dec

variable {inp : P → V} {H : Set P} {dec : P → V → Prop}

/-- `ε`-agreement is monotone in `ε`. -/
theorem EpsAgreement.mono [Lattice V] [AddGroup V] {ε ε' : V} (h : EpsAgreement ε H dec)
    (hε : ε ≤ ε') : EpsAgreement ε' H dec :=
  fun p hp q hq v w hv hw => (h p hp q hq v w hv hw).trans hε

/-- Range validity with unanimous honest inputs `x`: every honest decision is `x`. -/
theorem RangeValidity.eq_of_forall_eq [PartialOrder V] {x : V} (h : RangeValidity inp H dec)
    (hx : ∀ p ∈ H, inp p = x) {p : P} (hp : p ∈ H) {v : V} (hv : dec p v) : v = x :=
  (h p hp v hv).eq_of_forall_eq hx

end Approx

end Cslib.Byzantine.Problem
