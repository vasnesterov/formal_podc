import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Recoverable

/-!
# Two-shot objects solving two-process consensus — definitions

Minh Tung Nguyen, Pierre Sutra, *An Exact Characterization of the Two-shot Deterministic Objects
Solving Two-process Consensus*, PODC 2025 (DOI 10.1145/3732772.3733534).

This file contains the combinatorial side of the paper (Section 4):

* a deterministic sequential type is a CSLib `ObjSpec` (`State`, `Op`, `Resp`,
  `δ : State → Op → State × Resp`); the *process-allowance map* is `m : Fin 2 → Set O.Op`
  (process `0` = `p₀`, process `1` = `p₁`);
* an *interleaving* is a list of steps `(p, c)` (process `p` applies operation `c`);
  `view O s σ p` is the list of responses obtained by `p` when `σ` is applied from state `s`;
* `Dist O s p σ τ` — `σ` and `τ` are distinguishable to `p` in state `s` (Section 4.1);
* the three classes `C1`, `C15` (the paper's `C₁.₅`) and `C2` (Section 4.2), stated with the
  exclusions of the paper (`C15` excludes `C1`, `C2` excludes `C1` and `C15`); the "raw"
  conditions without exclusions are `C15Cond a b` (process `a` plays the role of `p₀`) and
  `C2Cond`.
-/

namespace TwoShotCons

open Cslib.SharedMemory

variable (O : ObjSpec)

/-- Responses (tagged with the calling process) of the interleaving `σ` applied from `s`. -/
def resps : O.State → List (Fin 2 × O.Op) → List (Fin 2 × O.Resp)
  | _, [] => []
  | s, (p, c) :: σ => (p, (O.δ s c).2) :: resps (O.δ s c).1 σ

/-- The state reached from `s` by applying the operations of the interleaving `σ`. -/
def after : O.State → List (Fin 2 × O.Op) → O.State
  | s, [] => s
  | s, (_, c) :: σ => after (O.δ s c).1 σ

/-- What process `p` observes of the interleaving `σ` applied from `s`: the responses of its own
operations, in order. -/
def view (s : O.State) (σ : List (Fin 2 × O.Op)) (p : Fin 2) : List O.Resp :=
  (resps O s σ).filterMap fun x => if x.1 = p then some x.2 else none

/-- `σ` and `τ` are *distinguishable to `p` in state `s`*: the responses of some operation of `p`
differ (Section 4.1). -/
def Dist (s : O.State) (p : Fin 2) (σ τ : List (Fin 2 × O.Op)) : Prop :=
  view O s σ p ≠ view O s τ p

/-- `σ` and `τ` are distinguishable to both processes. -/
def DistBoth (s : O.State) (σ τ : List (Fin 2 × O.Op)) : Prop :=
  Dist O s 0 σ τ ∧ Dist O s 1 σ τ

variable (m : Fin 2 → Set O.Op)

/-- **Class `C₁`** (Section 4.2.2): for some state `s` and operations `f ∈ m(p₀)`, `g ∈ m(p₁)`,
`fg` and `gf` are distinguishable to both processes. -/
def C1 : Prop :=
  ∃ (s : O.State) (f g : O.Op), f ∈ m 0 ∧ g ∈ m 1 ∧ DistBoth O s [(0, f), (1, g)] [(1, g), (0, f)]

/-- The five properties of **class `C₁.₅`** (Section 4.2.3), with process `a` in the role of `p₀`
and process `b` in the role of `p₁` (`f, f' ∈ m(a)`, `g, g' ∈ m(b)`). -/
def C15Cond (a b : Fin 2) : Prop :=
  ∃ (s : O.State) (f f' g g' : O.Op), f ∈ m a ∧ f' ∈ m a ∧ g ∈ m b ∧ g' ∈ m b ∧
    -- (1) `fg` and `gf` are distinguishable to `p₀`
    Dist O s a [(a, f), (b, g)] [(b, g), (a, f)] ∧
    -- (2) `fg` and `gf` are indistinguishable to `p₁`
    ¬ Dist O s b [(a, f), (b, g)] [(b, g), (a, f)] ∧
    -- (3) `fgg'f'` and `gfg'f'` are distinguishable to both processes
    DistBoth O s [(a, f), (b, g), (b, g'), (a, f')] [(b, g), (a, f), (b, g'), (a, f')] ∧
    -- (4) `gg'ff'` and `fgg'f'` are distinguishable to both processes
    DistBoth O s [(b, g), (b, g'), (a, f), (a, f')] [(a, f), (b, g), (b, g'), (a, f')] ∧
    -- (5) (a) `gg'f` and `f` are distinguishable to `p₀`, or
    --     (b) `gg'ff'` and `fgf'g'` are distinguishable to both processes
    (Dist O s a [(b, g), (b, g'), (a, f)] [(a, f)] ∨
      DistBoth O s [(b, g), (b, g'), (a, f), (a, f')] [(a, f), (b, g), (a, f'), (b, g')])

/-- **Class `C₁.₅`** (Section 4.2.3): not in `C₁`, and the five properties hold for `p₀, p₁` or
with the roles of `p₀` and `p₁` interchanged. -/
def C15 : Prop := ¬ C1 O m ∧ (C15Cond O m 0 1 ∨ C15Cond O m 1 0)

/-- The process calling `cᵢ` in the definition of class `C₂`: `p₀` for even `i`, `p₁` for odd
`i`. -/
def own (i : ℕ) : Fin 2 := if i % 2 = 0 then 0 else 1

/-- The properties of **class `C₂`** (Section 4.2.4): a state `s`, `f ∈ m(p₀)`, `g ∈ m(p₁)` and
operations `c₀, …, cₙ` (`n ≥ 1` odd, `cᵢ ∈ m(p₀)` for even `i`, `cᵢ ∈ m(p₁)` for odd `i`) with
properties (1)–(6). The operation `cᵢ` is called by process `own i`. -/
def C2Cond : Prop :=
  ∃ (s : O.State) (f g : O.Op) (n : ℕ) (c : ℕ → O.Op),
    Odd n ∧ f ∈ m 0 ∧ g ∈ m 1 ∧ (∀ i ≤ n, c i ∈ m (own i)) ∧
    -- (1) `fg` and `gf` are indistinguishable to both processes
    ¬ Dist O s 0 [(0, f), (1, g)] [(1, g), (0, f)] ∧
    ¬ Dist O s 1 [(0, f), (1, g)] [(1, g), (0, f)] ∧
    -- (2) for all `0 ≤ i < n`, the four pairs are distinguishable to both processes
    (∀ i < n,
      DistBoth O s [(0, f), (1, g), (own i, c i), (own (i + 1), c (i + 1))]
        [(1, g), (0, f), (own i, c i), (own (i + 1), c (i + 1))] ∧
      DistBoth O s [(0, f), (1, g), (own i, c i), (own (i + 1), c (i + 1))]
        [(1, g), (0, f), (own (i + 1), c (i + 1)), (own i, c i)] ∧
      DistBoth O s [(0, f), (1, g), (own (i + 1), c (i + 1)), (own i, c i)]
        [(1, g), (0, f), (own i, c i), (own (i + 1), c (i + 1))] ∧
      DistBoth O s [(0, f), (1, g), (own (i + 1), c (i + 1)), (own i, c i)]
        [(1, g), (0, f), (own (i + 1), c (i + 1)), (own i, c i)]) ∧
    -- (3) `fc₀gc₁` and `gfc₀c₁` are distinguishable to both processes
    DistBoth O s [(0, f), (0, c 0), (1, g), (1, c 1)] [(1, g), (0, f), (0, c 0), (1, c 1)] ∧
    -- (4) `fc₀g` and `g` are distinguishable to `p₁`, or `fc₀gc₁` and `gfc₁c₀` are
    -- distinguishable to both processes
    (Dist O s 1 [(0, f), (0, c 0), (1, g)] [(1, g)] ∨
      DistBoth O s [(0, f), (0, c 0), (1, g), (1, c 1)] [(1, g), (0, f), (1, c 1), (0, c 0)]) ∧
    -- (5) `gcₙfcₙ₋₁` and `fgcₙcₙ₋₁` are distinguishable to both processes
    DistBoth O s [(1, g), (1, c n), (0, f), (0, c (n - 1))]
      [(0, f), (1, g), (1, c n), (0, c (n - 1))] ∧
    -- (6) `gcₙf` and `f` are distinguishable to `p₀`, or `gcₙfcₙ₋₁` and `fgcₙ₋₁cₙ` are
    -- distinguishable to both processes
    (Dist O s 0 [(1, g), (1, c n), (0, f)] [(0, f)] ∨
      DistBoth O s [(1, g), (1, c n), (0, f), (0, c (n - 1))]
        [(0, f), (1, g), (0, c (n - 1)), (1, c n)])

/-- **Class `C₂`** (Section 4.2.4): not in `C₁` or `C₁.₅`, and the properties of `C2Cond`. -/
def C2 : Prop := ¬ C1 O m ∧ ¬ C15 O m ∧ C2Cond O m

/-! ## Basic lemmas -/

@[simp] lemma resps_nil (s : O.State) : resps O s [] = [] := rfl

@[simp] lemma resps_cons (s : O.State) (p : Fin 2) (c : O.Op) (σ : List (Fin 2 × O.Op)) :
    resps O s ((p, c) :: σ) = (p, (O.δ s c).2) :: resps O (O.δ s c).1 σ := rfl

@[simp] lemma after_nil (s : O.State) : after O s [] = s := rfl

@[simp] lemma after_cons (s : O.State) (p : Fin 2) (c : O.Op) (σ : List (Fin 2 × O.Op)) :
    after O s ((p, c) :: σ) = after O (O.δ s c).1 σ := rfl

lemma view_nil (s : O.State) (p : Fin 2) : view O s [] p = [] := rfl

lemma view_cons_self (s : O.State) (p : Fin 2) (c : O.Op) (σ : List (Fin 2 × O.Op)) :
    view O s ((p, c) :: σ) p = (O.δ s c).2 :: view O (O.δ s c).1 σ p := by
  simp [view]

lemma view_cons_other (s : O.State) {p q : Fin 2} (h : q ≠ p) (c : O.Op)
    (σ : List (Fin 2 × O.Op)) : view O s ((q, c) :: σ) p = view O (O.δ s c).1 σ p := by
  simp [view, h]

lemma distBoth_iff {s : O.State} {σ τ : List (Fin 2 × O.Op)} {a b : Fin 2} (hab : a ≠ b) :
    DistBoth O s σ τ ↔ Dist O s a σ τ ∧ Dist O s b σ τ := by
  unfold DistBoth
  fin_cases a <;> fin_cases b <;> simp_all [and_comm]

/-- The union of the three classes is the union of the conditions without exclusions. -/
lemma classes_iff : (C1 O m ∨ C15 O m ∨ C2 O m) ↔
    (C1 O m ∨ C15Cond O m 0 1 ∨ C15Cond O m 1 0 ∨ C2Cond O m) := by
  unfold C15 C2
  tauto

end TwoShotCons
