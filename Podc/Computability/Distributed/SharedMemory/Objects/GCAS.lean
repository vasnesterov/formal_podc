import Cslib.Computability.Distributed.SharedMemory.Spec
import Mathlib.Order.Basic

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Objects/GCAS.lean

/-!
# Generalized compare-and-swap (GCAS)

The *generalized compare-and-swap* object of Hadzilacos, Thiessen and Toueg (PODC 2026): a
compare-and-swap whose equality test is replaced by a comparator `C ∈ {<, =, >}` supplied with the
operation. Over a linearly ordered value type `V`,

* `gcas C v₁ v₂` compares the current value `v` with `v₁` using `C` and, if `v C v₁`, replaces it
  by `v₂` (response: success flag);
* `read` returns the current value, `write v` overwrites it.

`gcas .eq` is the ordinary compare-and-swap (`gcasObject_gcas_eq`).
-/

namespace Cslib.SharedMemory

/-- The comparators of GCAS. -/
inductive Cmp where
  | lt
  | eq
  | gt
  deriving DecidableEq

/-- `Cmp.test c v w` is `v c w`. -/
def Cmp.test {V : Type} [LinearOrder V] : Cmp → V → V → Bool
  | .lt, v, w => decide (v < w)
  | .eq, v, w => decide (v = w)
  | .gt, v, w => decide (w < v)

@[simp] lemma Cmp.test_lt {V : Type} [LinearOrder V] (v w : V) : Cmp.lt.test v w = decide (v < w) :=
  rfl
@[simp] lemma Cmp.test_eq {V : Type} [LinearOrder V] (v w : V) : Cmp.eq.test v w = decide (v = w) :=
  rfl
@[simp] lemma Cmp.test_gt {V : Type} [LinearOrder V] (v w : V) : Cmp.gt.test v w = decide (w < v) :=
  rfl

/-- Operations of a GCAS object. -/
inductive GCASOp (V : Type) where
  | read
  | write (v : V)
  | gcas (c : Cmp) (v₁ v₂ : V)

/-- A generalized compare-and-swap object over a linearly ordered `V` with initial value `v₀`.
Responses are `Sum V Bool`: the value for `read`, the success flag for `gcas`, `true` for
`write`. -/
abbrev gcasObject (V : Type) [LinearOrder V] (v₀ : V) : ObjSpec where
  State := V
  Op := GCASOp V
  Resp := V ⊕ Bool
  init := v₀
  δ q
    | .read => (q, .inl q)
    | .write v => (v, .inr true)
    | .gcas c v₁ v₂ => if c.test q v₁ then (v₂, .inr true) else (q, .inr false)

variable {V : Type} [LinearOrder V] {v₀ : V}

@[simp] lemma gcasObject_read (q : V) : (gcasObject V v₀).δ q .read = (q, .inl q) := rfl

@[simp] lemma gcasObject_write (q v : V) : (gcasObject V v₀).δ q (.write v) = (v, .inr true) := rfl

lemma gcasObject_gcas (q : V) (c : Cmp) (v₁ v₂ : V) :
    (gcasObject V v₀).δ q (.gcas c v₁ v₂) =
      if c.test q v₁ then (v₂, .inr true) else (q, .inr false) := rfl

/-- `gcas .eq` is compare-and-swap. -/
lemma gcasObject_gcas_eq (q v₁ v₂ : V) :
    (gcasObject V v₀).δ q (.gcas .eq v₁ v₂) = (casObject V v₀).δ q (.cas v₁ v₂) := by
  simp only [Cmp.test_eq, decide_eq_true_eq]

/-- The new state after a `gcas`. -/
lemma gcasObject_gcas_fst (q : V) (c : Cmp) (v₁ v₂ : V) :
    ((gcasObject V v₀).δ q (.gcas c v₁ v₂)).1 = if c.test q v₁ then v₂ else q := by
  rw [gcasObject_gcas]; split <;> rfl

end Cslib.SharedMemory
