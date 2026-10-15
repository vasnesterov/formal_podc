import Papers.PODC2016.ComplexityHierarchy.RacingCounters
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting

/-!
# `n`-consensus from one location with `read` and `multiply` (Theorem 3.3 of [EGSZ16])

A single memory location storing a natural number, initially `1`, supporting `read()` and
`multiply(x)`, simulates an unbounded `m`-component counter: component `c_v` is the exponent of the
`(v+1)`-st prime `p_v = Nat.nth Nat.Prime v` in the stored value; `multiply(p_v)` increments `c_v`
and `read()` returns all components at once. Plugging this simulation (`mulSim`) into the racing
counters algorithm of Lemma 3.1 gives obstruction-free `m`-valued consensus among any finite set of
processes, in particular `n`-consensus (`n` processes, `n` values).

Deviation: `multiply(x)` returns the dummy acknowledgement `0` (responses of all operations of an
`ObjSpec` share one type).
-/

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory

/-- Operations of a location supporting `read` and `multiply`. -/
inductive MulOp where
  /-- Return the stored value. -/
  | read
  /-- Multiply the stored value by `x`. -/
  | multiply (x : ℕ)

/-- A memory location storing a natural number, supporting `read()` and `multiply(x)` (the latter
acknowledged by the dummy response `0`). -/
abbrev mulLoc : ObjSpec where
  State := ℕ
  Op := MulOp
  Resp := ℕ
  init := 1
  δ s o := match o with
    | .read => (s, s)
    | .multiply x => (s * x, 0)

/-- The `(v+1)`-st prime. -/
noncomputable abbrev pr (v : ℕ) : ℕ := Nat.nth Nat.Prime v

lemma pr_prime (v : ℕ) : (pr v).Prime := Nat.prime_nth_prime v

lemma pr_injective : Function.Injective pr := Nat.nth_injective Nat.infinite_setOfPred_prime

/-- The counter simulation of Theorem 3.3 (multiply): `c_v` is the exponent of `pr v`. -/
noncomputable def mulSim (m : ℕ) (P : Type) [DecidableEq P] : CounterSim m P where
  B := mulLoc
  init := 1
  incOp _ v _ := .multiply (pr v)
  scanOp := .read
  decode x v := x.factorization (pr v)
  cnt x v := x.factorization (pr v)
  Inv s _ := s ≠ 0
  inv_init := one_ne_zero
  cnt_init := by funext v; simp
  inv_inc s _ _ v hs := mul_ne_zero hs (pr_prime v).ne_zero
  cnt_inc s _ _ v hs := by
    funext u
    simp only [Nat.factorization_mul hs (pr_prime v).ne_zero, (pr_prime v).factorization,
      Finsupp.add_apply, Finsupp.single_apply, Function.update_apply]
    by_cases h : u = v
    · subst h; simp
    · have : pr v ≠ pr u := fun e => h (Fin.ext (pr_injective e).symm)
      simp [h, this]
  scan_state _ := rfl
  scan_resp _ _ _ := rfl

/-- Theorem 3.3 of [EGSZ16] (`multiply`, general form): obstruction-free `m`-valued consensus among
any finite set `P` of processes can be solved with a single location supporting only `read()` and
`multiply(x)`, initialized to `1`. -/
theorem theorem_3_3_multiply_general (m : ℕ) [NeZero m] (P : Type) [DecidableEq P] [Fintype P] :
    ∃ (L : Type) (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => mulLoc) P L),
      I.memInit () = 1 ∧ (∀ p v, I.allowed p v) ∧ I.Solves (consensus P (Fin m)) ∧
        I.ObstructionFree :=
  ⟨RacingLoc m, racing (mulSim m P) (Fintype.card P), rfl, fun _ _ => trivial,
    racing_solves le_rfl, racing_obstructionFree le_rfl⟩

/-- Theorem 3.3 of [EGSZ16] (`multiply`): `n`-consensus (obstruction-free `n`-valued consensus
among `n` processes) can be solved using a single memory location that supports only `read()` and
`multiply(x)`, initialized to `1`. -/
theorem theorem_3_3_multiply (n : ℕ) [NeZero n] :
    ∃ (L : Type) (I : Impl (taskObj (Fin n) (Fin n)) (fun _ : Unit => mulLoc) (Fin n) L),
      I.memInit () = 1 ∧ (∀ p v, I.allowed p v) ∧ I.Solves (consensus (Fin n) (Fin n)) ∧
        I.ObstructionFree :=
  theorem_3_3_multiply_general n (Fin n)

end Cslib.SharedMemory.ComplexityHierarchy
