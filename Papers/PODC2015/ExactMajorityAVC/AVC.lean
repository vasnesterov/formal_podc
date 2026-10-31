import Cslib.Computability.Distributed.PopulationProtocols.Basic
import Mathlib.Tactic

/-!
# The Average-and-Conquer (AVC) protocol (Figure 1 of the paper)

Alistarh, Gelashvili, Vojnović, *Fast and Exact Majority in Population Protocols*, PODC 2015
(full version MSR-TR-2015-13), Section 3, Figure 1.

States carry a sign and a weight; the *value* is `sign · weight`:

* `St.zero pos` — the weak states `+0` (`pos = true`) and `−0`;
* `St.one pos j` — the intermediate states `±1_j` (level `j`, `1 ≤ j ≤ d`);
* `St.strong v` — the strong states, `v` odd with `3 ≤ |v| ≤ m`.

The transition function `update` follows the pseudocode of Figure 1 line by line. Line 12 is
printed as `weight(x) · weight(y) = 0 and value(x) + value(y) > 0`; with that condition a weak
state never adopts a *negative* sign, contradicting the prose ("if a node with 0 weight meets a
node with non-zero weight, then it will adopt the sign of the interaction partner") and breaking
the protocol when `B` is the majority (see `AVCLiteral.lean`). We formalize both versions:
`avcLiteral d` (as printed) and `avc d` (line 12 with `weight(x) + weight(y) > 0`, i.e. "zero meets
non-zero", as described in the prose).

The transition function does not depend on `m`; `m` only bounds the valid states (`St.Valid m d`),
and the set of valid states is closed under interactions (`valid_update`).

## Main statements

* `value_update`: interactions preserve the sum of values (Invariant 4.3, local form);
* `valid_update`: valid states stay valid;
* `update_neg`: the corrected protocol is symmetric under negating all signs (with the roles of
  initiator and responder exchanged);
* `sgn_update_of_pos`: two positive states interact into two positive states.
-/

namespace Podc.ExactMajorityAVC

/-- States of the AVC protocol. -/
inductive St
  /-- The weak states `+0` (`pos = true`) and `−0` (`pos = false`). -/
  | zero (pos : Bool)
  /-- The intermediate states `+1_j` (`pos = true`) and `−1_j`, `1 ≤ j ≤ d`. -/
  | one (pos : Bool) (j : ℕ)
  /-- The strong state of value `v` (odd, `3 ≤ |v| ≤ m`). -/
  | strong (v : ℤ)
  deriving DecidableEq

namespace St

/-- `value(x) = sgn(x) · weight(x)` (Figure 1, line 3). -/
def value : St → ℤ
  | zero _ => 0
  | one pos _ => if pos then 1 else -1
  | strong v => v

/-- `weight(x)` (Figure 1, line 1). -/
def weight : St → ℤ
  | zero _ => 0
  | one _ _ => 1
  | strong v => |v|

/-- `sgn(x)` (Figure 1, line 2), as a Boolean: `true` is `+1`. -/
def sgn : St → Bool
  | zero pos => pos
  | one pos _ => pos
  | strong v => decide (0 < v)

@[simp] lemma value_zero (p : Bool) : (zero p).value = 0 := rfl
@[simp] lemma value_one_true (j : ℕ) : (one true j).value = 1 := rfl
@[simp] lemma value_one_false (j : ℕ) : (one false j).value = -1 := rfl
@[simp] lemma value_strong (v : ℤ) : (strong v).value = v := rfl
@[simp] lemma weight_zero (p : Bool) : (zero p).weight = 0 := rfl
@[simp] lemma weight_one (p : Bool) (j : ℕ) : (one p j).weight = 1 := rfl
@[simp] lemma weight_strong (v : ℤ) : (strong v).weight = max v (-v) := abs_eq_max_neg
@[simp] lemma sgn_zero (p : Bool) : (zero p).sgn = p := rfl
@[simp] lemma sgn_one (p : Bool) (j : ℕ) : (one p j).sgn = p := rfl
@[simp] lemma sgn_strong (v : ℤ) : (strong v).sgn = decide (0 < v) := rfl

/-- Valid states for parameters `m` (odd) and `d`. -/
def Valid (m d : ℕ) : St → Prop
  | zero _ => True
  | one _ j => 1 ≤ j ∧ j ≤ d
  | strong v => v % 2 = 1 ∧ 3 ≤ |v| ∧ |v| ≤ m

/-- `x ∈ {−1_d, +1_d}`. -/
def IsTop (d : ℕ) : St → Prop
  | one _ j => j = d
  | _ => False

instance (d : ℕ) (x : St) : Decidable (IsTop d x) := by
  cases x <;> unfold IsTop <;> infer_instance

@[simp] lemma isTop_zero (d : ℕ) (p : Bool) : ¬ (zero p).IsTop d := id
@[simp] lemma isTop_one (d : ℕ) (p : Bool) (j : ℕ) : (one p j).IsTop d ↔ j = d := Iff.rfl
@[simp] lemma isTop_strong (d : ℕ) (v : ℤ) : ¬ (strong v).IsTop d := id

/-- Negation of all signs. -/
def neg : St → St
  | zero pos => zero (!pos)
  | one pos j => one (!pos) j
  | strong v => strong (-v)

end St

open St

/-- `ϕ` (Figure 1, line 4): the state of an odd value `k` (`±1` become `±1_1`). -/
def ofVal (k : ℤ) : St :=
  if k = 1 then one true 1 else if k = -1 then one false 1 else strong k

/-- `R↓` (Figure 1, line 5). -/
def roundDown (k : ℤ) : St := ofVal (if k % 2 = 0 then k - 1 else k)

/-- `R↑` (Figure 1, line 6). -/
def roundUp (k : ℤ) : St := ofVal (if k % 2 = 0 then k + 1 else k)

/-- `Shift-to-Zero` (Figure 1, line 7). -/
def shift (d : ℕ) : St → St
  | one pos j => if j < d then one pos (j + 1) else one pos j
  | x => x

/-- `Sign-to-Zero` (Figure 1, line 8). -/
def toZero (x : St) : St := zero x.sgn

/-- The procedure `update⟨x, y⟩` of Figure 1. With `lit = true` line 12 is as printed
(`value(x) + value(y) > 0`); with `lit = false` it is the corrected condition
`weight(x) + weight(y) > 0` ("zero meets non-zero"). -/
def update (lit : Bool) (d : ℕ) (x y : St) : St × St :=
  if (0 < x.weight ∧ 1 < y.weight) ∨ (0 < y.weight ∧ 1 < x.weight) then
    (roundDown ((x.value + y.value) / 2), roundUp ((x.value + y.value) / 2))
  else if x.weight * y.weight = 0 ∧
      (if lit then 0 < x.value + y.value else 0 < x.weight + y.weight) then
    if x.weight ≠ 0 then (shift d x, toZero x) else (toZero y, shift d y)
  else if (IsTop d x ∧ y.weight = 1 ∧ x.sgn ≠ y.sgn) ∨
      (IsTop d y ∧ x.weight = 1 ∧ y.sgn ≠ x.sgn) then
    (zero false, zero true)
  else (shift d x, shift d y)

open Cslib.PopulationProtocol

/-- The AVC protocol with `d` levels of intermediate states (corrected line 12). -/
def avc (d : ℕ) : Protocol St := ⟨update false d⟩

/-- The AVC protocol exactly as printed in Figure 1. -/
def avcLiteral (d : ℕ) : Protocol St := ⟨update true d⟩

/-! ### Basic facts about the auxiliary functions -/

@[simp] lemma value_ofVal (k : ℤ) : (ofVal k).value = k := by
  unfold ofVal; split_ifs <;> simp_all [value]

lemma value_roundDown (k : ℤ) :
    (roundDown k).value = if k % 2 = 0 then k - 1 else k := by simp [roundDown]

lemma value_roundUp (k : ℤ) :
    (roundUp k).value = if k % 2 = 0 then k + 1 else k := by simp [roundUp]

@[simp] lemma value_shift (d : ℕ) (x : St) : (shift d x).value = x.value := by
  cases x with
  | one p j => simp only [shift]; split_ifs <;> rfl
  | _ => rfl

@[simp] lemma sgn_shift (d : ℕ) (x : St) : (shift d x).sgn = x.sgn := by
  cases x with
  | one p j => simp only [shift]; split_ifs <;> rfl
  | _ => rfl

@[simp] lemma weight_shift (d : ℕ) (x : St) : (shift d x).weight = x.weight := by
  cases x with
  | one p j => simp only [shift]; split_ifs <;> rfl
  | _ => rfl

@[simp] lemma value_toZero (x : St) : (toZero x).value = 0 := rfl

@[simp] lemma sgn_toZero (x : St) : (toZero x).sgn = x.sgn := rfl

lemma weight_eq_abs_value (x : St) : x.weight = |x.value| := by
  cases x with
  | zero => simp [weight, value]
  | one pos j => cases pos <;> simp [weight, value]
  | strong v => simp [weight, value]

lemma valid_ofVal {m d : ℕ} (hd : 1 ≤ d) {k : ℤ} (hk : k % 2 = 1) (hkm : |k| ≤ m) :
    (ofVal k).Valid m d := by
  unfold ofVal
  split_ifs with h1 h2
  · exact ⟨le_rfl, hd⟩
  · exact ⟨le_rfl, hd⟩
  · refine ⟨hk, ?_, hkm⟩
    rw [le_abs]; omega

lemma valid_shift {m d : ℕ} {x : St} (hx : x.Valid m d) : (shift d x).Valid m d := by
  cases x with
  | zero => trivial
  | one pos j =>
    simp only [shift]; split_ifs with h
    · exact ⟨by omega, by omega⟩
    · exact hx
  | strong v => exact hx

/-- On valid states, the value is odd iff the weight is positive. -/
lemma value_odd {m d : ℕ} {x : St} (hx : x.Valid m d) (hw : 0 < x.weight) :
    x.value % 2 = 1 := by
  cases x with
  | zero => simp [weight] at hw
  | one pos j => cases pos <;> simp [value]
  | strong v => exact hx.1

lemma weight_le {m d : ℕ} (hm : 1 ≤ m) {x : St} (hx : x.Valid m d) : x.weight ≤ m := by
  cases x with
  | zero => simp [weight]
  | one => simp [weight]; exact_mod_cast hm
  | strong v => exact hx.2.2

lemma valid_strong_iff {m d : ℕ} {v : ℤ} :
    (strong v).Valid m d ↔ v % 2 = 1 ∧ (3 ≤ v ∨ v ≤ -3) ∧ -(m : ℤ) ≤ v ∧ v ≤ m := by
  simp only [Valid, abs_eq_max_neg]; omega

/-! ### Interactions of valid states -/

section Update

variable {m d : ℕ}

/-- **Invariant 4.3 (local form).** An interaction preserves the sum of the two values. -/
theorem value_update (lit : Bool) {x y : St} (hx : x.Valid m d) (hy : y.Valid m d) :
    (update lit d x y).1.value + (update lit d x y).2.value = x.value + y.value := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> rcases y with ⟨_ | _⟩ | ⟨_ | _, k⟩ | w <;>
    (try simp only [valid_strong_iff] at hx) <;> (try simp only [valid_strong_iff] at hy) <;>
    simp only [update, weight_zero, weight_one, weight_strong, value_zero, value_one_true,
      value_one_false, value_strong, sgn_zero, sgn_one, sgn_strong, isTop_zero, isTop_one,
      isTop_strong] <;>
    split_ifs <;>
    simp_all [value_roundDown, value_roundUp] <;>
    (try split_ifs) <;> omega

lemma valid_roundDown (hd : 1 ≤ d) (hm : m % 2 = 1) {k : ℤ} (hk1 : -(m : ℤ) ≤ k)
    (hk2 : k ≤ m) : (roundDown k).Valid m d := by
  unfold roundDown
  split_ifs <;> exact valid_ofVal hd (by omega) (by rw [abs_le]; omega)

lemma valid_roundUp (hd : 1 ≤ d) (hm : m % 2 = 1) {k : ℤ} (hk1 : -(m : ℤ) ≤ k)
    (hk2 : k ≤ m) : (roundUp k).Valid m d := by
  unfold roundUp
  split_ifs <;> exact valid_ofVal hd (by omega) (by rw [abs_le]; omega)

lemma valid_toZero (x : St) : (toZero x).Valid m d := trivial

/-- Valid states interact into valid states (the state space of Figure 1 is closed). -/
theorem valid_update (lit : Bool) (hd : 1 ≤ d) (hm : m % 2 = 1) {x y : St}
    (hx : x.Valid m d) (hy : y.Valid m d) :
    (update lit d x y).1.Valid m d ∧ (update lit d x y).2.Valid m d := by
  have hvx := weight_le (m := m) (by omega) hx
  have hvy := weight_le (m := m) (by omega) hy
  rw [weight_eq_abs_value, abs_le] at hvx hvy
  unfold update
  split_ifs <;> first
    | exact ⟨valid_roundDown hd hm (by omega) (by omega), valid_roundUp hd hm (by omega) (by omega)⟩
    | exact ⟨valid_shift hx, trivial⟩
    | exact ⟨trivial, valid_shift hy⟩
    | exact ⟨trivial, trivial⟩
    | exact ⟨valid_shift hx, valid_shift hy⟩

lemma sgn_ofVal (k : ℤ) : (ofVal k).sgn = decide (0 < k) := by
  unfold ofVal; split_ifs <;> simp_all

/-- Two states of positive sign interact into two states of positive sign. -/
theorem sgn_update_of_pos {x y : St} (hx : x.Valid m d) (hy : y.Valid m d)
    (hpx : x.sgn = true) (hpy : y.sgn = true) :
    (update false d x y).1.sgn = true ∧ (update false d x y).2.sgn = true := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> rcases y with ⟨_ | _⟩ | ⟨_ | _, k⟩ | w <;>
    (try simp only [valid_strong_iff] at hx) <;> (try simp only [valid_strong_iff] at hy) <;>
    simp_all [update, roundDown, roundUp, toZero] <;>
    (try split_ifs) <;> (try rw [sgn_ofVal]) <;> (try rw [sgn_ofVal]) <;>
    simp <;> omega

/-- Phase 2 of Lemma A.1: two intermediate states of opposite signs. -/
lemma update_one_one {i j : ℕ} (hi : i ≤ d) (hj : j ≤ d) :
    update false d (one false i) (one true j) =
      if i = d ∨ j = d then (zero false, zero true) else (one false (i + 1), one true (j + 1)) := by
  simp only [update, weight_one, value_one_false, value_one_true, sgn_one, isTop_one]
  by_cases h : i = d ∨ j = d
  · rcases h with h | h <;> simp [h]
  · push Not at h
    simp [h.1, h.2, shift, lt_of_le_of_ne hi h.1, lt_of_le_of_ne hj h.2]

/-- Phase 3 of Lemma A.1: `−0` meets a state of positive value and becomes `+0`. -/
lemma update_zero_pos {y : St} (hy : 0 < y.value) :
    update false d (zero false) y = (zero true, shift d y) := by
  have hw : 0 < y.weight := by rw [weight_eq_abs_value]; exact abs_pos_of_pos hy
  have hs : y.sgn = true := by
    rcases y with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp_all
  simp [update, hw, toZero, hs]

/-- The negative part `max 0 (−value)` of a state. -/
def negPart (x : St) : ℤ := max 0 (-x.value)

/-- Phase 1 of Lemma A.1: when a positive state meets a negative state and one of them is strong,
the total negative weight strictly decreases. -/
lemma negPart_update_lt {x y : St} (hx : x.Valid m d) (hy : y.Valid m d)
    (hpx : 0 < x.value) (hny : y.value < 0) (hs : 1 < x.weight ∨ 1 < y.weight) :
    negPart (update false d x y).1 + negPart (update false d x y).2 < negPart x + negPart y := by
  have hwx := weight_eq_abs_value x
  have hwy := weight_eq_abs_value y
  have hox := value_odd hx (by rw [hwx]; exact abs_pos_of_pos hpx)
  have hoy := value_odd hy (by rw [hwy]; exact abs_pos_of_neg hny)
  rw [abs_eq_max_neg] at hwx hwy
  have h1 : (0 < x.weight ∧ 1 < y.weight) ∨ (0 < y.weight ∧ 1 < x.weight) := by omega
  simp only [update, h1, ↓reduceIte, negPart, value_roundDown, value_roundUp]
  split_ifs <;> omega

/-! ### Symmetry under negation -/

@[simp] lemma value_neg (x : St) : x.neg.value = -x.value := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp [neg]

@[simp] lemma weight_neg (x : St) : x.neg.weight = x.weight := by
  rw [weight_eq_abs_value, weight_eq_abs_value, value_neg, abs_neg]

@[simp] lemma isTop_neg (x : St) : x.neg.IsTop d ↔ x.IsTop d := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp [neg]

@[simp] lemma neg_neg (x : St) : x.neg.neg = x := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp [neg]

lemma sgn_neg {x : St} (hx : x.Valid m d) : x.neg.sgn = !x.sgn := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp [neg]
  rw [valid_strong_iff] at hx
  rcases lt_or_gt_of_ne (show v ≠ 0 by omega) with h | h <;> simp [h, h.not_gt]

lemma valid_neg {x : St} (hx : x.Valid m d) : x.neg.Valid m d := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp_all [neg, Valid]

lemma neg_ofVal (k : ℤ) : (ofVal k).neg = ofVal (-k) := by
  unfold ofVal; split_ifs <;> simp_all [neg]; omega

lemma roundDown_neg (k : ℤ) : roundDown (-k) = (roundUp k).neg := by
  unfold roundDown roundUp; rw [neg_ofVal]; congr 1; split_ifs <;> omega

lemma roundUp_neg (k : ℤ) : roundUp (-k) = (roundDown k).neg := by
  unfold roundDown roundUp; rw [neg_ofVal]; congr 1; split_ifs <;> omega

lemma shift_neg (x : St) : shift d x.neg = (shift d x).neg := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp [neg, shift] <;> split_ifs <;> simp

lemma toZero_neg {x : St} (hx : x.Valid m d) : toZero x.neg = (toZero x).neg := by
  show zero x.neg.sgn = zero (!x.sgn)
  rw [sgn_neg hx]

/-- **Sign symmetry.** Negating both states and exchanging the roles of initiator and responder
commutes with the (corrected) AVC transition function. -/
theorem update_neg {x y : St} (hx : x.Valid m d) (hy : y.Valid m d) :
    update false d y.neg x.neg = ((update false d x y).2.neg, (update false d x y).1.neg) := by
  have hox := value_odd hx
  have hoy := value_odd hy
  have hwx := weight_eq_abs_value x
  have hwy := weight_eq_abs_value y
  simp only [update, weight_neg, value_neg, isTop_neg, sgn_neg hx, sgn_neg hy, Bool.false_eq_true,
    ↓reduceIte]
  by_cases h1 : (0 < x.weight ∧ 1 < y.weight) ∨ (0 < y.weight ∧ 1 < x.weight)
  · have h1' : (0 < y.weight ∧ 1 < x.weight) ∨ (0 < x.weight ∧ 1 < y.weight) := h1.symm
    have hev : (-y.value + -x.value) / 2 = -((x.value + y.value) / 2) := by
      rw [abs_eq_max_neg] at hwx hwy
      have hpos : 0 < x.weight ∧ 0 < y.weight := by omega
      have := hox hpos.1; have := hoy hpos.2; omega
    simp only [h1, h1', ↓reduceIte, hev, roundDown_neg, roundUp_neg]
  · have h1' : ¬ ((0 < y.weight ∧ 1 < x.weight) ∨ (0 < x.weight ∧ 1 < y.weight)) :=
      fun h => h1 h.symm
    simp only [h1, h1', ↓reduceIte]
    by_cases h2 : x.weight * y.weight = 0 ∧ 0 < x.weight + y.weight
    · have h2' : y.weight * x.weight = 0 ∧ 0 < y.weight + x.weight := by
        rw [mul_comm, add_comm]; exact h2
      simp only [h2, h2', and_self, ↓reduceIte]
      by_cases hx0 : x.weight ≠ 0
      · have hy0 : ¬ y.weight ≠ 0 := by
          intro h; exact h.elim (by rcases mul_eq_zero.1 h2.1 with h | h <;> simp_all)
        simp only [hx0, hy0, ↓reduceIte, toZero_neg hx, shift_neg, ne_eq, not_false_eq_true]
      · have hy0 : y.weight ≠ 0 := by intro h; simp_all
        simp only [hx0, hy0, ↓reduceIte, toZero_neg hy, shift_neg, ne_eq, not_false_eq_true]
    · have h2' : ¬ (y.weight * x.weight = 0 ∧ 0 < y.weight + x.weight) := by
        rw [mul_comm, add_comm]; exact h2
      simp only [h2, h2', ↓reduceIte]
      by_cases h3 : (x.IsTop d ∧ y.weight = 1 ∧ x.sgn ≠ y.sgn) ∨
          (y.IsTop d ∧ x.weight = 1 ∧ y.sgn ≠ x.sgn)
      · have h3' : (y.IsTop d ∧ x.weight = 1 ∧ (!y.sgn) ≠ !x.sgn) ∨
            (x.IsTop d ∧ y.weight = 1 ∧ (!x.sgn) ≠ !y.sgn) := by
          simp only [ne_eq, Bool.not_inj_iff]; exact h3.symm
        simp only [h3, h3', ↓reduceIte]; rfl
      · have h3' : ¬ ((y.IsTop d ∧ x.weight = 1 ∧ (!y.sgn) ≠ !x.sgn) ∨
            (x.IsTop d ∧ y.weight = 1 ∧ (!x.sgn) ≠ !y.sgn)) := by
          simp only [ne_eq, Bool.not_inj_iff]; exact fun h => h3 h.symm
        simp only [h3, h3', ↓reduceIte, shift_neg]

end Update

end Podc.ExactMajorityAVC
