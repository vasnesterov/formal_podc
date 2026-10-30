import Papers.PODC2023.PPDoubleExpThresholds.Levels9to12

/-!
# The flat code of `Main`

`Main` consists of `OF := false`, one copy of the loop
`while ¬Large(x̄ⱼ) ∨ ¬Large(ȳⱼ) do AssertProper(j); AssertEmpty(j + 1)` for every level
`j = 1, …, n` (the `for`-loop is a macro), `OF := true` and `while true do AssertProper(n)`.
The loop of level `j` occupies the instructions `5j − 4, …, 5j`.
-/

namespace Podc.PPDoubleExpThresholds

open Program

namespace Stmt

variable {R P : Type*}

theorem len_seqs_append (l₁ l₂ : List (Stmt R P)) :
    (seqs (l₁ ++ l₂)).len = (seqs l₁).len + (seqs l₂).len := by
  induction l₁ with
  | nil => simp [seqs, len]
  | cons s l ih => simp [seqs, len, ih]; omega

theorem compile_seqs_append (l₁ l₂ : List (Stmt R P)) (a : ℕ) :
    (seqs (l₁ ++ l₂)).compile a = (seqs l₁).compile a ++ (seqs l₂).compile (a + (seqs l₁).len) := by
  induction l₁ generalizing a with
  | nil => simp [seqs, compile, len]
  | cons s l ih => simp [seqs, compile, len, ih, Nat.add_assoc]

end Stmt

variable (n : ℕ)

/-- Its code, placed at address `a`. -/
def itCode (j a : ℕ) : List (Instr (Reg n) Proc) :=
  [.call (.large j 1) (a + 1) (a + 2), .call (.large j 3) (a + 5) (a + 2),
   .call (.assertProper j) (a + 3) (a + 3), .call (.assertEmpty (j + 1)) (a + 4) (a + 4), .goto a]

theorem compile_mainIt (j a : ℕ) : (mainIt n j).compile a = itCode n j a := by
  simp [mainIt, itCode, Stmt.compile, BExp.compile, Stmt.len, BExp.len]

theorem len_mainIt (j : ℕ) : (mainIt n j).len = 5 := by
  simp [mainIt, Stmt.len, BExp.len]

/-- The code of all the loops. -/
def itsCode : ℕ → ℕ → List (Instr (Reg n) Proc)
  | 0, _ => []
  | m + 1, a => itsCode m a ++ itCode n (m + 1) (a + 5 * m)

theorem len_itsCode (m a : ℕ) : (itsCode n m a).length = 5 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [itsCode, ih, itCode]; omega

theorem seqs_its (m a : ℕ) :
    (Stmt.seqs ((List.range m).map fun j => mainIt n (j + 1))).compile a = itsCode n m a ∧
    (Stmt.seqs ((List.range m).map fun j => mainIt n (j + 1))).len = 5 * m := by
  induction m with
  | zero => simp [Stmt.seqs, Stmt.compile, Stmt.len, itsCode]
  | succ m ih =>
    rw [List.range_succ, List.map_append, Stmt.compile_seqs_append, Stmt.len_seqs_append, ih.1, ih.2]
    simp [Stmt.seqs, Stmt.compile, Stmt.len, compile_mainIt, len_mainIt, itsCode]
    omega

theorem itsCode_get {m a j r : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) (hr : r < 5) :
    (itsCode n m a)[5 * j - 5 + r]? = (itCode n j (a + 5 * j - 5))[r]? := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [itsCode]
    rcases Nat.lt_or_ge j (m + 1) with h | h
    · rw [List.getElem?_append_left (by rw [len_itsCode]; omega), ih (by omega)]
    · obtain rfl : j = m + 1 := by omega
      rw [List.getElem?_append_right (by rw [len_itsCode]; omega), len_itsCode]
      congr 2 <;> omega

theorem code_main : (prog n).code .main =
    [.setOF false] ++ itsCode n n 1 ++
      [.setOF true, .goto (5 * n + 3), .call (.assertProper n) (5 * n + 4) (5 * n + 4),
       .goto (5 * n + 2), .ret false] := by
  simp only [prog, body, Stmt.body]
  rw [Stmt.compile_seqs_append, Stmt.compile_seqs_append, Stmt.len_seqs_append]
  obtain ⟨h1, h2⟩ := seqs_its n n (0 + (Stmt.seqs [Stmt.setOF false]).len)
  rw [h1, h2]
  simp [Stmt.seqs, Stmt.compile, Stmt.len, BExp.compile, BExp.len]
  omega

/-- The instructions of `Main` inside the loop of level `j`. -/
theorem instr_main_it {j r : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) (hr : r < 5) :
    (prog n).instr .main (5 * j - 4 + r) = (itCode n j (5 * j - 4))[r]? := by
  rw [Program.instr, code_main, List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by simp [len_itsCode]; omega)]
  simp only [List.length_singleton]
  rw [show 5 * j - 4 + r - 1 = 5 * j - 5 + r by omega, itsCode_get n hj hjn hr]
  congr 2; omega

theorem instr_main_zero : (prog n).instr .main 0 = some (.setOF false) := by
  rw [Program.instr, code_main]; simp

theorem instr_main_fin {r : ℕ} (hr : r < 5) : (prog n).instr .main (5 * n + 1 + r) =
    ([.setOF true, .goto (5 * n + 3), .call (.assertProper n) (5 * n + 4) (5 * n + 4),
      .goto (5 * n + 2), .ret false] : List (Instr (Reg n) Proc))[r]? := by
  rw [Program.instr, code_main, List.getElem?_append_right (by simp [len_itsCode])]
  simp [len_itsCode]

theorem instr_main_none {pc : ℕ} (h : 5 * n + 6 ≤ pc) : (prog n).instr .main pc = none := by
  rw [Program.instr, code_main]
  simp [len_itsCode]; omega

end Podc.PPDoubleExpThresholds
