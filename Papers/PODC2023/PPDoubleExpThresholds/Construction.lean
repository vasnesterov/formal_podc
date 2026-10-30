import Papers.PODC2023.PPDoubleExpThresholds.Decide
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# The succinct population program of Section 6

Registers `Q = Q₁ ∪ ⋯ ∪ Qₙ ∪ {R}` with `Qᵢ = {xᵢ, x̄ᵢ, yᵢ, ȳᵢ}` (`Reg n`; the register `k` of level
`i` is `reg n i k`, `k = 0, 1, 2, 3` standing for `x, x̄, y, ȳ`; `bar` exchanges `x ↔ x̄`, `y ↔ ȳ`).
Constants `N₁ = 1`, `N_{i+1} = (Nᵢ + 1)²`.

Procedures (parameters as in the paper): `AssertEmpty(i)`, `AssertProper(i)`, `Zero(x)`,
`IncrPair(x, y)`, `Large(x)` and `Main`. They are written in the structured syntax (`Stmt`) as in
the paper's pseudocode and compiled to flat code. The `for`-loops are macros (expanded).
The paper's `CheckProper(i − 2)` in line 12 of `Large` is a typo for `AssertProper(i − 2)`.
-/

namespace Podc.PPDoubleExpThresholds

/-- Registers of the program with `n` levels: `r i k` is register `k` of level `i + 1`. -/
inductive Reg (n : ℕ)
  | r (i : Fin n) (k : Fin 4)
  | R
  deriving DecidableEq, Fintype, Repr

/-- Procedure names (with their parameters). -/
inductive Proc
  | assertEmpty (i : ℕ)
  | assertProper (i : ℕ)
  | zero (i : ℕ) (k : Fin 4)
  | incrPair (i : ℕ) (bx by' : Bool)
  | large (i : ℕ) (k : Fin 4)
  | main
  deriving DecidableEq, Repr

/-- The constants `N₁ = 1`, `N_{i+1} = (Nᵢ + 1)²` (and `N₀ = 0`). -/
def N : ℕ → ℕ
  | 0 => 0
  | i + 1 => (N i + 1) ^ 2

/-- `x̄`: exchanges `x ↔ x̄` and `y ↔ ȳ`. -/
def bar : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

/-- `kx` for `IncrPair`: `x` or `x̄`. -/
def kx (b : Bool) : Fin 4 := if b then 1 else 0

/-- `ky` for `IncrPair`: `y` or `ȳ`. -/
def ky (b : Bool) : Fin 4 := if b then 3 else 2

variable (n : ℕ)

/-- Register `k` of level `i` (levels `1, …, n`; out-of-range levels are never used). -/
def reg (i : ℕ) (k : Fin 4) : Reg n := if h : i - 1 < n then .r ⟨i - 1, h⟩ k else .R

/-- The loop of level `j` in `Main`:
`while ¬Large(x̄ⱼ) ∨ ¬Large(ȳⱼ) do AssertProper(j); AssertEmpty(j + 1)`. -/
def mainIt (j : ℕ) : Stmt (Reg n) Proc :=
  .whileDo (.or (.not (.call (.large j 1))) (.not (.call (.large j 3))))
    (.seq (.call (.assertProper j)) (.call (.assertEmpty (j + 1))))

open Stmt in
/-- The structured body of each procedure (Section 6). -/
def body : Proc → Stmt (Reg n) Proc
  | .assertEmpty i =>
      if i ≤ n then
        seqs [call (.assertEmpty (i + 1)),
          ifThen (.detect (reg n i 0)) restart, ifThen (.detect (reg n i 1)) restart,
          ifThen (.detect (reg n i 2)) restart, ifThen (.detect (reg n i 3)) restart]
      else if i = n + 1 then ifThen (.detect .R) restart
      else skip
  | .assertProper i =>
      if i = 0 then skip else
        seqs [call (.assertProper (i - 1)),
          ifThen (.detect (reg n i 0)) restart, call (.large i 1),
          ifThen (.detect (reg n i 0)) restart,
          ifThen (.detect (reg n i 2)) restart, call (.large i 3),
          ifThen (.detect (reg n i 2)) restart]
  | .zero i k =>
      whileDo .tt (seqs [call (.assertProper (i - 1)),
        ifThen (.detect (reg n i k)) (ret false),
        ifThen (.call (.large i (bar k))) (ret true)])
  | .incrPair i bx by' =>
      ite (.call (.zero i (bar (ky by'))))
        (seqs [swap (reg n i (ky by')) (reg n i (bar (ky by'))),
          ite (.call (.zero i (bar (kx bx))))
            (swap (reg n i (kx bx)) (reg n i (bar (kx bx))))
            (move (reg n i (bar (kx bx))) (reg n i (kx bx)))])
        (move (reg n i (bar (ky by'))) (reg n i (ky by')))
  | .large i k =>
      if i ≤ 1 then
        ite (.detect (reg n i k))
          (seqs [move (reg n i k) (reg n i (bar k)), swap (reg n i k) (reg n i (bar k)), ret true])
          (ret false)
      else
        seqs [ifThen (.or (.not (.call (.zero (i - 1) 0))) (.not (.call (.zero (i - 1) 2)))) restart,
          whileDo .tt (seqs [call (.assertProper (i - 2)),
            ite (.detect (reg n i k))
              (seqs [move (reg n i k) (reg n i (bar k)), call (.incrPair (i - 1) false false),
                ifThen (.and (.call (.zero (i - 1) 0)) (.call (.zero (i - 1) 2)))
                  (seqs [swap (reg n i k) (reg n i (bar k)), ret true])])
              (seqs [ifThen (.and (.call (.zero (i - 1) 0)) (.call (.zero (i - 1) 2))) (ret false),
                ifThen (.detect (reg n i (bar k)))
                  (seqs [move (reg n i (bar k)) (reg n i k), call (.incrPair (i - 1) true true)])])])]
  | .main =>
      seqs ([setOF false] ++
        (List.range n).map (fun j => mainIt n (j + 1)) ++
        [setOF true, whileDo .tt (call (.assertProper n))])

/-- The procedures of the program. -/
def procs : Finset Proc :=
  {Proc.main} ∪ (Finset.range (n + 2)).image Proc.assertEmpty ∪
    (Finset.range (n + 1)).image Proc.assertProper ∪
    ((Finset.Icc 1 n) ×ˢ (Finset.univ : Finset (Fin 4))).image (fun p => Proc.zero p.1 p.2) ∪
    ((Finset.Icc 1 n) ×ˢ (Finset.univ : Finset (Bool × Bool))).image
      (fun p => Proc.incrPair p.1 p.2.1 p.2.2) ∪
    ((Finset.Icc 1 n) ×ˢ (Finset.univ : Finset (Fin 4))).image (fun p => Proc.large p.1 p.2)

/-- The population program of Section 6 with `n` levels. -/
def prog : Program (Reg n) Proc where
  code p := (body n p).body
  main := .main
  procs := procs n

end Podc.PPDoubleExpThresholds
