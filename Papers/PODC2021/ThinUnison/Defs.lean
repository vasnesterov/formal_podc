import Cslib.Computability.Distributed.SelfStabilization.StoneAge
import Mathlib

/-!
# AlgAU: definitions

Emek, Keren. *A Thin Self-Stabilizing Asynchronous Unison Algorithm with Applications to Fault
Tolerant Biological Networks*, PODC 2021 (arXiv 2102.12787), Section 2.2.

Levels are integers `ℓ` with `1 ≤ |ℓ| ≤ k`; a turn is a level together with a flag `faulty`
(able turn `ℓ̄` / faulty turn `ℓ̂`, the latter only for `|ℓ| ≥ 2`). We work with plain integers
and keep the validity constraints as hypotheses, so that all local reasoning is linear integer
arithmetic (`omega`).

* `fwd k ℓ` is the forward operator `φ(ℓ)` (the cyclic order `-k, …, -1, 1, …, k, -k`);
* `inw ℓ = ψ⁻¹(ℓ)` (one unit inwards), `outw ℓ = ψ⁺¹(ℓ)` (one unit outwards);
* `Outward ℓ m` : `m ∈ Ψ^>(ℓ)`; `FarOut ℓ m` : `m ∈ Ψ^≫(ℓ)` (at least two units outwards);
* `LAdj k ℓ m` : the levels are adjacent (equal or consecutive in the cyclic order).
-/

namespace ThinUnison

open Cslib.StoneAge

/-! ## Levels -/

/-- `ℓ` is a level: `1 ≤ |ℓ| ≤ k`. -/
def IsLevel (k : ℕ) (ℓ : ℤ) : Prop := (1 ≤ ℓ ∧ ℓ ≤ k) ∨ (-k ≤ ℓ ∧ ℓ ≤ -1)

/-- The forward operator `φ`. -/
def fwd (k : ℕ) (ℓ : ℤ) : ℤ := if ℓ = -1 then 1 else if ℓ = k then -k else ℓ + 1

/-- `ψ⁻¹(ℓ)`: one unit inwards. -/
def inw (ℓ : ℤ) : ℤ := if 0 < ℓ then ℓ - 1 else ℓ + 1

/-- `ψ⁺¹(ℓ)`: one unit outwards. -/
def outw (ℓ : ℤ) : ℤ := if 0 < ℓ then ℓ + 1 else ℓ - 1

/-- Adjacent levels: `ℓ = m`, `ℓ = φ(m)` or `m = φ(ℓ)`. -/
def LAdj (k : ℕ) (ℓ m : ℤ) : Prop := ℓ = m ∨ ℓ = fwd k m ∨ m = fwd k ℓ

/-- `m ∈ Ψ^>(ℓ)`: `m` is (strictly) outwards of `ℓ`. -/
def Outward (ℓ m : ℤ) : Prop := (0 < ℓ ∧ ℓ < m) ∨ (ℓ < 0 ∧ m < ℓ)

/-- `m ∈ Ψ^≫(ℓ)`: `m` is at least two units outwards of `ℓ`. -/
def FarOut (ℓ m : ℤ) : Prop := (0 < ℓ ∧ ℓ + 2 ≤ m) ∨ (ℓ < 0 ∧ m + 2 ≤ ℓ)

/-- `m ∈ Ψ^≥(ℓ)`. -/
def OutEq (ℓ m : ℤ) : Prop := m = ℓ ∨ Outward ℓ m

instance (k : ℕ) (ℓ : ℤ) : Decidable (IsLevel k ℓ) := by unfold IsLevel; infer_instance
instance (k : ℕ) (ℓ m : ℤ) : Decidable (LAdj k ℓ m) := by unfold LAdj; infer_instance
instance (ℓ m : ℤ) : Decidable (Outward ℓ m) := by unfold Outward; infer_instance
instance (ℓ m : ℤ) : Decidable (FarOut ℓ m) := by unfold FarOut; infer_instance

/-! ## Turns -/

/-- A turn of AlgAU: an able turn `ℓ̄` (`faulty = false`, `1 ≤ |ℓ| ≤ k`) or a faulty turn `ℓ̂`
(`faulty = true`, `2 ≤ |ℓ| ≤ k`). -/
@[ext]
structure Turn (k : ℕ) where
  /-- The level of the turn. -/
  lvl : ℤ
  /-- Whether the turn is faulty. -/
  faulty : Bool
  isLevel : IsLevel k lvl
  faulty_two : faulty = true → 2 ≤ lvl ∨ lvl ≤ -2
deriving DecidableEq

/-- The able turn `φ(ℓ)‾` (target of an AA transition). -/
def Turn.aa {k : ℕ} (ν : Turn k) : Turn k :=
  ⟨fwd k ν.lvl, false, by
    have := ν.isLevel; unfold IsLevel at *; unfold fwd; split_ifs <;> omega, by simp⟩

/-- The faulty turn `ℓ̂` (target of an AF transition). -/
def Turn.af {k : ℕ} (ν : Turn k) (h : 2 ≤ ν.lvl ∨ ν.lvl ≤ -2) : Turn k :=
  ⟨ν.lvl, true, ν.isLevel, fun _ => h⟩

/-- The able turn `ψ⁻¹(ℓ)‾` (target of an FA transition). -/
def Turn.fa {k : ℕ} (ν : Turn k) (h : ν.faulty = true) : Turn k :=
  ⟨inw ν.lvl, false, by
    have := ν.isLevel; have := ν.faulty_two h; unfold IsLevel at *; unfold inw; split_ifs <;> omega,
    by simp⟩

/-! ## The transition function -/

/-- Condition of a type AA transition: every sensed turn is able and its level is `ℓ` or `φ(ℓ)`.
(Equivalent to the paper's "`v` is good and `Λ ⊆ {ℓ, φ(ℓ)}`", see `aaCond_iff`.) -/
def AACond {k : ℕ} (ν : Turn k) (S : Set (Turn k)) : Prop :=
  ∀ q ∈ S, q.faulty = false ∧ (q.lvl = ν.lvl ∨ q.lvl = fwd k ν.lvl)

/-- Condition of a type AF transition: `2 ≤ |ℓ|` and (some sensed level is not adjacent, or the
faulty turn `ψ⁻¹(ℓ)^` is sensed). -/
def AFCond {k : ℕ} (ν : Turn k) (S : Set (Turn k)) : Prop :=
  (2 ≤ ν.lvl ∨ ν.lvl ≤ -2) ∧
    ((∃ q ∈ S, ¬ LAdj k ν.lvl q.lvl) ∨ ∃ q ∈ S, q.faulty = true ∧ q.lvl = inw ν.lvl)

/-- Condition of a type FA transition: no sensed level is in `Ψ^>(ℓ)`. -/
def FACond {k : ℕ} (ν : Turn k) (S : Set (Turn k)) : Prop := ∀ q ∈ S, ¬ Outward ν.lvl q.lvl

open Classical in
/-- The transition function of AlgAU (Table 1). -/
noncomputable def δ (k : ℕ) (ν : Turn k) (S : Set (Turn k)) : Turn k :=
  if h : ν.faulty = true then
    if FACond ν S then ν.fa h else ν
  else if AACond ν S then ν.aa
  else if h' : AFCond ν S then ν.af h'.1
  else ν

/-- The algorithm AlgAU with parameter `k` (the paper takes `k = 3D + 2`). -/
noncomputable def algAU (k : ℕ) : Algorithm (Turn k) := ⟨δ k⟩

/-- Sanity check: the AA condition is the paper's (`v` is good, i.e. protected and senses no
faulty turn, and `Λ ⊆ {ℓ, φ(ℓ)}`). -/
theorem aaCond_iff {k : ℕ} (ν : Turn k) (S : Set (Turn k)) :
    AACond ν S ↔ ((∀ q ∈ S, LAdj k ν.lvl q.lvl) ∧ (∀ q ∈ S, q.faulty = false)) ∧
      ∀ q ∈ S, q.lvl = ν.lvl ∨ q.lvl = fwd k ν.lvl := by
  constructor
  · intro h
    refine ⟨⟨fun q hq => ?_, fun q hq => (h q hq).1⟩, fun q hq => (h q hq).2⟩
    rcases (h q hq).2 with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inr h1)
  · rintro ⟨⟨-, h1⟩, h2⟩ q hq; exact ⟨h1 q hq, h2 q hq⟩

/-! ## Clock values -/

/-- Position of a level on the cycle `-k, …, -1, 1, …, k` (in `0, …, 2k - 1`). -/
def pos (k : ℕ) (ℓ : ℤ) : ℤ := if ℓ < 0 then ℓ + k else ℓ + k - 1

/-- The AU clock value of a turn (meaningful for able turns, which are the output states):
an element of the cyclic group `ℤ / 2k`. -/
def clock {k : ℕ} (ν : Turn k) : ZMod (2 * k) := (pos k ν.lvl : ℤ)

/-- The output of a turn: its clock value if it is able (an output state), none otherwise. -/
def output {k : ℕ} (ν : Turn k) : Option (ZMod (2 * k)) :=
  if ν.faulty then none else some (clock ν)

/-! ## Predicates on configurations of an execution -/

section Predicates

variable {V : Type*} (G : SimpleGraph V) {k : ℕ} (C : ℕ → V → Turn k)

/-- The edge `(u, v)` is protected at time `t`. -/
def EProt (t : ℕ) (u v : V) : Prop := LAdj k (C t u).lvl (C t v).lvl

/-- Node `v` is protected at time `t`: all its incident edges are protected. -/
def Prot (t : ℕ) (v : V) : Prop := ∀ u, G.Adj v u → LAdj k (C t v).lvl (C t u).lvl

/-- Node `v` is good at time `t`: protected and senses no faulty turn (including its own). -/
def Good (t : ℕ) (v : V) : Prop :=
  Prot G C t v ∧ (C t v).faulty = false ∧ ∀ u, G.Adj v u → (C t u).faulty = false

/-- Node `v` is out-protected at time `t`: `Λ_v ∩ Ψ^≫(λ_v) = ∅`. -/
def OutProt (t : ℕ) (v : V) : Prop := ∀ u, G.Adj v u → ¬ FarOut (C t v).lvl (C t u).lvl

/-- The graph is `ℓ`-out-protected at time `t`: `L(Ψ^≥(ℓ)) ⊆ V_op`. -/
def LOutProt (t : ℕ) (ℓ : ℤ) : Prop := ∀ v, OutEq ℓ (C t v).lvl → OutProt G C t v

/-- The graph is out-protected / protected / good at time `t`. -/
def AllOutProt (t : ℕ) : Prop := ∀ v, OutProt G C t v
/-- The graph is protected at time `t`. -/
def AllProt (t : ℕ) : Prop := ∀ v, Prot G C t v
/-- The graph is good at time `t`. -/
def AllGood (t : ℕ) : Prop := ∀ v, Good G C t v

/-- `v` is justifiably faulty: faulty, and not protected or has a neighbour in turn
`ψ⁻¹(ℓ)^`. -/
def JustFaulty (t : ℕ) (v : V) : Prop :=
  (C t v).faulty = true ∧ (¬ Prot G C t v ∨
    ∃ u, G.Adj v u ∧ (C t u).faulty = true ∧ (C t u).lvl = inw (C t v).lvl)

/-- The graph is justified at time `t`: every faulty node is justifiably faulty. -/
def Justified (t : ℕ) : Prop := ∀ v, (C t v).faulty = true → JustFaulty G C t v

end Predicates

end ThinUnison
