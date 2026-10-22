import Podc.Computability.Distributed.SWMR.Basic
import Mathlib.Tactic

/-!
# Algorithm 2: solving a two-process task with an ε-agreement black box

Section 5.2 of the full version (proof of Theorem 1.2). A two-process task `Δ` (processes
`Bool`, inputs `In`, outputs `O`) is given together with a *path system* (`PathSystem`): for every
full input `X` and every process `i` a path `Y₀, …, Y_L` of output vectors from `δ(X)` to
`δ(X^i)` (the output chosen for the partial input in which the input of `i` is missing) such that
`Y₀, …, Y_{L-1}` are legal for `X`, consecutive vectors differ in at most one entry, and `Y_{L-1}`,
`Y_L` agree on the entry of the process `!i` whose input is known. Biran–Moran–Zaks' conditions
give such path systems (`BMZ.lean`).

Algorithm 2 for process `me`: write the task input to the write-once register `I_me`, read
`I_other`, run an ε-agreement algorithm `E` (resolution `L`) with input `1` if `I_other` was `⊥` and
`0` otherwise, read `I_other` again, and output the `me`-entry of `Y_d` where `d` is the
ε-agreement decision, on the path chosen as in lines 6–21.

`E` is a black box: we only use that it solves `1/L`-agreement wait-free, Lemma 5.6 (decision `0`,
resp. `L`, implies input `0`, resp. `1`), that a decision strictly between `0` and `L` implies
distinct inputs and a step of the other process (`EBox`), and a bound on its step complexity.
-/

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

variable {In O : Type}

/-- The full input vector of the process `me` with input `x` when the other input is `v`. -/
def vec (me : Bool) (x v : In) : Bool → In := fun b => if b = me then x else v

/-- The task given by the relation `Δ` on full input and output vectors: a partial output vector
is legal if it extends to a legal full one. -/
def taskOf (Δ : (Bool → In) → (Bool → O) → Prop) : Task Bool In O := fun x y =>
  ∃ Y, Δ x Y ∧ ∀ b c, y b = some c → Y b = c

/-- A path system of length `L` for the task `Δ` (see the module docstring). `part i xj` is
`δ(X^i)`: the output vector chosen when only the input `xj` of `!i` is known. -/
structure PathSystem (Δ : (Bool → In) → (Bool → O) → Prop) (L : ℕ) where
  part : Bool → In → (Bool → O)
  path : (Bool → In) → Bool → ℕ → (Bool → O)
  /-- All paths start at the same node `δ(X)`. -/
  path_zero : ∀ X i j, path X i 0 = path X j 0
  path_L : ∀ X i, path X i L = part i (X (!i))
  legal : ∀ X i m, m < L → Δ X (path X i m)
  adj : ∀ X i m, m < L → ∃ b, path X i m (!b) = path X i (m + 1) (!b)
  last : ∀ X i, path X i (L - 1) (!i) = path X i L (!i)
  /-- Covering: `δ(X^i)` restricted to `!i` extends legally for every input of `i`. -/
  cover : ∀ X i, ∃ Y, Δ X Y ∧ Y (!i) = part i (X (!i)) (!i)

variable {KE : Type} [DecidableEq KE] {VE : KE → Type}

/-- Registers of Algorithm 2: `none` is the write-once task input register `I`, `some i` the
registers of the ε-agreement algorithm. -/
abbrev Reg2 (In : Type) (VE : KE → Type) : Option KE → Type
  | none => Option In
  | some i => VE i

/-- Local states of Algorithm 2. `xo` is the value read from `I_other` at line 3, `d` the
ε-agreement decision, `xo2` the value read from `I_other` after it (line 11). -/
inductive St2 (S In : Type)
  | wIn (x : In)
  | rIn (x : In)
  | sub (x : In) (xo : Option In) (s : S)
  | post (x : In) (xo : Option In) (d : ℕ) (xo2 : Option In)
  | done (x : In) (xo : Option In) (d : ℕ) (xo2 : Option In)

/-- The ε-agreement input: `1` iff `I_other` was `⊥` at line 3. -/
def myIn (xo : Option In) : Bool := xo.isNone

variable {Δ : (Bool → In) → (Bool → O) → Prop} {L : ℕ}

/-- The decision of Algorithm 2 (lines 6–21). Fallback values in impossible cases are arbitrary. -/
def out2 (PS : PathSystem Δ L) (me : Bool) (x : In) (xo : Option In) (d : ℕ) (xo2 : Option In) :
    O :=
  if d = 0 then
    match xo with
    | some v => PS.path (vec me x v) me 0 me
    | none => PS.part (!me) x me
  else if d < L then
    match xo2 with
    | some v => PS.path (vec me x v) (if myIn xo then !me else me) d me
    | none => PS.part (!me) x me
  else PS.part (!me) x me

/-- Algorithm 2 built on the ε-agreement algorithm `E`. -/
@[reducible] def alg2 (E : Alg Bool KE VE Bool ℕ) (PS : PathSystem Δ L) : Alg Bool (Option KE) (Reg2 In VE) In O
    where
  S := St2 E.S In
  v₀ := fun | none => (none : Option In) | some i => E.v₀ i
  init _ x := .wIn x
  next me s := match s with
    | .wIn x => .write (K := Option KE) none (some x) (.rIn x)
    | .rIn x => .read (!me) none (fun v => .sub x v (E.init me (myIn v)))
    | .sub x xo s =>
      match E.next me s with
      | .write i v s' => .write (some i) v (.sub x xo s')
      | .read q i k => .read q (some i) (fun v => .sub x xo (k v))
      | .decide d _ => .read (!me) none (fun v => .post x xo d v)
    | .post x xo d xo2 => .decide (out2 PS me x xo d xo2) (.done x xo d xo2)
    | .done x xo d xo2 => .read me none (fun _ => .done x xo d xo2)

end Podc.BoundedRegisterPower
