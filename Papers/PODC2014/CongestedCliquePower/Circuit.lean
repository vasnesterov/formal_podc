import Mathlib

/-!
# Boolean circuits with `b`-separable gates (Section 2 of [DKO14])

[DKO14]: A. Drucker, F. Kuhn, R. Oshman, *On the power of the congested clique model*, PODC 2014.

A circuit is a DAG of gates. Following the paper, the inputs of the circuit are gates without
in-wires: a gate `h` with `src h = some i` reads the input bit `x i`; every other gate `h` computes
a Boolean function `op h` (of unbounded fan-in) of the values of its in-neighbours
`in(h) = {g | wire g h}`. There are no multi-wires (`wire` is a relation). Instead of the
"longest path" we use a layering `rank` that strictly increases along wires; a circuit has depth
at most `D` iff it admits such a layering with values `≤ D` (take `rank g` = the length of the
longest path ending in `g`).

## Main definitions

* `Circuit X C`: a circuit with inputs `X` and gates `C`; `Circuit.eval`.
* `Separable b f` (Definition 1): `f` is `b`-separable.
* `Circuit.numWires`, `Circuit.DepthLE`.

## Main statements

* `separable_and`, `separable_or`: AND and OR are `1`-separable.
* `andCircuit_eval`: a small concrete circuit (non-vacuity).
* `heavy_count_counterexample`: with the paper's thresholds (weight `|in G| + |out G|`, heavy iff
  weight `≥ n * s` where `N = n² * s`) there can be more than `n` heavy gates, contradicting the
  first sentence of "Construction of I" in the proof of Theorem 2.
-/

namespace Podc.CongestedCliquePower

/-- A Boolean circuit with inputs indexed by `X` and gates `C`. -/
structure Circuit (X C : Type) where
  /-- `wire g h`: there is a wire from `g` to `h`, i.e. `g ∈ in(h)`. -/
  wire : C → C → Prop
  /-- `src h = some i`: `h` is the input gate of the input `i`. -/
  src : C → Option X
  /-- Every input has at most one input gate. -/
  src_inj : ∀ g h i, src g = some i → src h = some i → g = h
  /-- The Boolean function computed by a (non-input) gate from the values of its in-neighbours. -/
  op : (h : C) → ({g // wire g h} → Bool) → Bool
  /-- A layering of the DAG. -/
  rank : C → ℕ
  rank_lt : ∀ g h, wire g h → rank g < rank h

namespace Circuit

variable {X C : Type} (Γ : Circuit X C)

/-- The value of gate `h` on the input `x`. -/
def eval (x : X → Bool) (h : C) : Bool :=
  match Γ.src h with
  | some i => x i
  | none => Γ.op h fun g => eval x g.1
termination_by Γ.rank h
decreasing_by exact Γ.rank_lt _ _ g.2

lemma eval_of_src_some {x : X → Bool} {h : C} {i : X} (hi : Γ.src h = some i) :
    Γ.eval x h = x i := by
  rw [eval, hi]

lemma eval_of_src_none {x : X → Bool} {h : C} (hi : Γ.src h = none) :
    Γ.eval x h = Γ.op h fun g => Γ.eval x g.1 := by
  rw [eval, hi]

/-- The number of wires `N`. -/
noncomputable def numWires : ℕ := Nat.card {p : C × C // Γ.wire p.1 p.2}

/-- The circuit has depth at most `D` (its layering takes values in `[0, D]`). -/
def DepthLE (D : ℕ) : Prop := ∀ g, Γ.rank g ≤ D

/-- Gate `out` of `Γ` computes `f`. -/
def Computes (out : C) (f : (X → Bool) → Bool) : Prop := ∀ x, Γ.eval x out = f x

end Circuit

/-- **Definition 1 of [DKO14].** `f : {0,1}^ι → {0,1}` is `b`-separable if for every partition of
the inputs (given as a map `π : ι → κ` to the part index; empty parts are allowed) there are
functions `g j : {0,1}^{π⁻¹(j)} → {0,1}^b` and `h : ({0,1}^b)^κ → {0,1}` with
`f x = h (g j (x|π⁻¹(j)))_j`. -/
def Separable {ι : Type} (b : ℕ) (f : (ι → Bool) → Bool) : Prop :=
  ∀ (κ : Type) (π : ι → κ), ∃ (g : (j : κ) → ({i // π i = j} → Bool) → Fin b → Bool)
    (h : (κ → Fin b → Bool) → Bool), ∀ x, f x = h fun j => g j fun i => x i.1

open Classical in
/-- AND of unbounded fan-in is `1`-separable. -/
theorem separable_and {ι : Type} : Separable 1 fun x : ι → Bool => decide (∀ i, x i = true) := by
  intro κ π
  refine ⟨fun _ y _ => decide (∀ i, y i = true), fun z => decide (∀ j, z j 0 = true), fun x => ?_⟩
  simp only [decide_eq_decide, decide_eq_true_eq]
  exact ⟨fun h j i => h i.1, fun h i => h (π i) ⟨i, rfl⟩⟩

open Classical in
/-- OR of unbounded fan-in is `1`-separable. -/
theorem separable_or {ι : Type} : Separable 1 fun x : ι → Bool => decide (∃ i, x i = true) := by
  intro κ π
  refine ⟨fun _ y _ => decide (∃ i, y i = true), fun z => decide (∃ j, z j 0 = true), fun x => ?_⟩
  simp only [decide_eq_decide, decide_eq_true_eq]
  exact ⟨fun ⟨i, h⟩ => ⟨π i, ⟨i, rfl⟩, h⟩, fun ⟨_, i, h⟩ => ⟨i.1, h⟩⟩

/-! ### A small concrete circuit -/

/-- The circuit `x₀ ∧ x₁`: gates `0, 1` are the inputs, gate `2` is an AND gate. -/
def andCircuit : Circuit (Fin 2) (Fin 3) where
  wire g h := g.val < 2 ∧ h = 2
  src g := if hg : g.val < 2 then some ⟨g.val, hg⟩ else none
  src_inj := by decide
  op _ y := decide (∀ i, y i = true)
  rank g := if g = 2 then 1 else 0
  rank_lt := by decide

theorem andCircuit_eval (x : Fin 2 → Bool) : andCircuit.eval x 2 = (x 0 && x 1) := by
  rw [andCircuit.eval_of_src_none (by decide)]
  have h0 : andCircuit.eval x 0 = x 0 := andCircuit.eval_of_src_some (by decide)
  have h1 : andCircuit.eval x 1 = x 1 := andCircuit.eval_of_src_some (by decide)
  simp only [andCircuit]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨h0 ▸ h ⟨0, by decide⟩, h1 ▸ h ⟨1, by decide⟩⟩
  · rintro ⟨ha, hb⟩ ⟨g, hg, -⟩
    match g, hg with
    | 0, _ => exact h0 ▸ ha
    | 1, _ => exact h1 ▸ hb

instance : DecidableRel andCircuit.wire :=
  inferInstanceAs (DecidableRel fun g h : Fin 3 => g.val < 2 ∧ h = 2)

theorem andCircuit_numWires : andCircuit.numWires = 2 := by
  rw [Circuit.numWires, Nat.card_eq_fintype_card]
  rfl

/-! ### The paper's weight count is off by a factor of two -/

/-- The paper's weight `w(G) = |in(G)| + |out(G)|`. -/
def paperWeight {X C : Type} [Fintype C] (Γ : Circuit X C) [DecidableRel Γ.wire] (G : C) : ℕ :=
  (Finset.univ.filter (Γ.wire · G)).card + (Finset.univ.filter (Γ.wire G ·)).card

/-- The path `0 → 1 → 2 → 3 → 4`; gate `0` is the (only) input, the others are identity gates. -/
def pathCircuit : Circuit Unit (Fin 5) where
  wire g h := h.val = g.val + 1
  src g := if g.val = 0 then some () else none
  src_inj := by decide
  op _ y := decide (∀ i, y i = true)
  rank g := g.val
  rank_lt := fun g h hw => by change h.val = g.val + 1 at hw; omega

instance : DecidableRel pathCircuit.wire :=
  inferInstanceAs (DecidableRel fun g h : Fin 5 => h.val = g.val + 1)

/-- **The paper's heavy-gate count fails.** In the proof of Theorem 2 of [DKO14], with `N = n² s`
wires, a gate is heavy iff `w(G) = |in G| + |out G| ≥ n s`, and it is claimed that there are at
most `n` heavy gates. For `n = 2`, `s = 1` the path on 5 gates has `N = 4 = n² s` wires and
`3 > n` heavy gates (the inner ones, of weight `2`), so no assignment gives every player at most
one heavy gate. (The total weight is `2N`, not `N`.) -/
theorem heavy_count_counterexample :
    pathCircuit.numWires = 2 ^ 2 * 1 ∧
      2 < (Finset.univ.filter fun G => 2 * 1 ≤ paperWeight pathCircuit G).card ∧
      ¬ ∃ I : Fin 5 → Fin 2, ∀ G G', 2 * 1 ≤ paperWeight pathCircuit G →
        2 * 1 ≤ paperWeight pathCircuit G' → I G = I G' → G = G' := by
  refine ⟨?_, by decide, ?_⟩
  · rw [Circuit.numWires, Nat.card_eq_fintype_card]
    rfl
  · rintro ⟨I, hI⟩
    have := Fintype.card_le_of_injective
      (fun G : {G : Fin 5 // 2 * 1 ≤ paperWeight pathCircuit G} => I G.1)
      (fun G G' h => Subtype.ext (hI _ _ G.2 G'.2 h))
    revert this
    decide

end Podc.CongestedCliquePower
