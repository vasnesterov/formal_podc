import Papers.PODC2023.PPDoubleExpThresholds.Levels

/-!
# The flat code of the procedures of Section 6

Explicit listings of the compiled code (`Stmt.body`) of every procedure, used to step through the
procedures. Instruction indices are 0-based.
-/

namespace Podc.PPDoubleExpThresholds

variable (n : ℕ)

open Stmt in
theorem code_assertEmpty {i : ℕ} (hi : i ≤ n) : (prog n).code (.assertEmpty i) =
    [.call (.assertEmpty (i + 1)) 1 1,
     .detect (reg n i 0) 2 4, .restart, .goto 4,
     .detect (reg n i 1) 5 7, .restart, .goto 7,
     .detect (reg n i 2) 8 10, .restart, .goto 10,
     .detect (reg n i 3) 11 13, .restart, .goto 13, .ret false] := by
  simp [prog, body, hi, Stmt.body, Stmt.compile, BExp.compile, Stmt.seqs, Stmt.ifThen, Stmt.len,
    BExp.len]

theorem code_assertEmpty_last : (prog n).code (.assertEmpty (n + 1)) =
    [.detect .R 1 3, .restart, .goto 3, .ret false] := by
  simp [prog, body, Stmt.body, Stmt.compile, BExp.compile, Stmt.seqs, Stmt.ifThen, Stmt.len,
    BExp.len]

theorem code_assertProper_zero : (prog n).code (.assertProper 0) = [.ret false] := by
  simp [prog, body, Stmt.body, Stmt.compile]

theorem code_assertProper {i : ℕ} (hi : 1 ≤ i) : (prog n).code (.assertProper i) =
    [.call (.assertProper (i - 1)) 1 1,
     .detect (reg n i 0) 2 4, .restart, .goto 4,
     .call (.large i 1) 5 5,
     .detect (reg n i 0) 6 8, .restart, .goto 8,
     .detect (reg n i 2) 9 11, .restart, .goto 11,
     .call (.large i 3) 12 12,
     .detect (reg n i 2) 13 15, .restart, .goto 15, .ret false] := by
  have : i ≠ 0 := by omega
  simp [prog, body, this, Stmt.body, Stmt.compile, BExp.compile, Stmt.seqs, Stmt.ifThen, Stmt.len,
    BExp.len]

theorem code_zero (i : ℕ) (k : Fin 4) : (prog n).code (.zero i k) =
    [.goto 1, .call (.assertProper (i - 1)) 2 2,
     .detect (reg n i k) 3 5, .ret false, .goto 5,
     .call (.large i (bar k)) 6 8, .ret true, .goto 8, .goto 0, .ret false] := by
  simp [prog, body, Stmt.body, Stmt.compile, BExp.compile, Stmt.seqs, Stmt.ifThen, Stmt.len,
    BExp.len]

theorem code_incrPair (i : ℕ) (bx by' : Bool) : (prog n).code (.incrPair i bx by') =
    [.call (.zero i (bar (ky by'))) 1 7,
     .swap (reg n i (ky by')) (reg n i (bar (ky by'))),
     .call (.zero i (bar (kx bx))) 3 5,
     .swap (reg n i (kx bx)) (reg n i (bar (kx bx))), .goto 6,
     .move (reg n i (bar (kx bx))) (reg n i (kx bx)),
     .goto 8,
     .move (reg n i (bar (ky by'))) (reg n i (ky by')), .ret false] := by
  simp [prog, body, Stmt.body, Stmt.compile, BExp.compile, Stmt.seqs, Stmt.ifThen, Stmt.len,
    BExp.len]

theorem code_large_one {i : ℕ} (hi : i ≤ 1) (k : Fin 4) : (prog n).code (.large i k) =
    [.detect (reg n i k) 1 5, .move (reg n i k) (reg n i (bar k)),
     .swap (reg n i k) (reg n i (bar k)), .ret true, .goto 6, .ret false, .ret false] := by
  simp [prog, body, hi, Stmt.body, Stmt.compile, BExp.compile, Stmt.seqs, Stmt.ifThen, Stmt.len,
    BExp.len]

theorem code_large {i : ℕ} (hi : 2 ≤ i) (k : Fin 4) : (prog n).code (.large i k) =
    [.call (.zero (i - 1) 0) 1 2, .call (.zero (i - 1) 2) 4 2, .restart, .goto 4, .goto 5,
     .call (.assertProper (i - 2)) 6 6, .detect (reg n i k) 7 15,
     .move (reg n i k) (reg n i (bar k)),
     .call (.incrPair (i - 1) false false) 9 9, .call (.zero (i - 1) 0) 10 14,
     .call (.zero (i - 1) 2) 11 14,
     .swap (reg n i k) (reg n i (bar k)), .ret true, .goto 14, .goto 23,
     .call (.zero (i - 1) 0) 16 19, .call (.zero (i - 1) 2) 17 19, .ret false, .goto 19,
     .detect (reg n i (bar k)) 20 23, .move (reg n i (bar k)) (reg n i k),
     .call (.incrPair (i - 1) true true) 22 22, .goto 23, .goto 4, .ret false] := by
  have : ¬ i ≤ 1 := by omega
  simp [prog, body, this, Stmt.body, Stmt.compile, BExp.compile, Stmt.seqs, Stmt.ifThen, Stmt.len,
    BExp.len]

end Podc.PPDoubleExpThresholds
