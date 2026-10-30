import Papers.PODC2023.PPDoubleExpThresholds.Theorem3
import Papers.PODC2023.PPDoubleExpThresholds.ProgramToMachine
import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocol

/-!
# Theorems 5, 1 and 2

Theorem 5 (programs to protocols) is the composition of Propositions 14 and 16; Theorem 1 combines
it with Theorem 3 (applied with `n + 1` levels); Theorem 2 (almost self-stabilisation) comes with
Proposition 16.
-/

namespace Podc.PPDoubleExpThresholds

/-- **Theorem 5** of [Czerner, PODC 2023]: a well-formed population program of size `s` deciding
`φ` yields a population protocol with `O(s)` states (and a single initial state) deciding
`φ'(x) ⇔ x ≥ i ∧ φ(x - i)` for some `i ∈ O(s)`; the protocol is moreover almost self-stabilising. -/
theorem theorem_5 {R P : Type} [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R]
    (prog : Program R P) (hwf : prog.WellFormed) {φ : ℕ → Bool} (h : prog.Decides φ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (PP : PProtocol Q) (i : ℕ),
      i ≤ 20 * prog.size + 20 ∧ Fintype.card Q ≤ 320 * prog.size + 320 ∧ (∃ q, PP.I = {q}) ∧
      PP.DecidesCount (fun x => decide (i ≤ x) && φ (x - i)) ∧
      PP.AlmostSelfStabilising (fun x => decide (i ≤ x) && φ (x - i)) := by
  obtain ⟨F, _, _, A, hA, hsize, hdom, -⟩ := proposition_14 prog hwf h
  obtain ⟨Q, _, _, PP, i, hi, hcard, hI, hdec, hss⟩ := proposition_16 A hA hdom
  exact ⟨Q, _, _, PP, i, by omega, by omega, hI, hdec, hss⟩

theorem threshold_shift (k i : ℕ) :
    (fun x => decide (i ≤ x) && decide (k ≤ x - i)) = fun x => decide (k + i ≤ x) := by
  funext x
  by_cases h1 : i ≤ x <;> by_cases h2 : k ≤ x - i <;> simp [h1, h2] <;> omega

/-- **Theorems 1 and 2** of [Czerner, PODC 2023]: for every `n` there is a population protocol
with `O(n)` states (at most `116160 n + 151040`) and a single initial state deciding `x ≥ k` for
some `k ≥ 2^(2^n)`; it is almost self-stabilising (Theorem 2). -/
theorem theorem_1 (n : ℕ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (PP : PProtocol Q) (k : ℕ),
      2 ^ 2 ^ n ≤ k ∧ Fintype.card Q ≤ 116160 * n + 151040 ∧ (∃ q, PP.I = {q}) ∧
      PP.DecidesCount (fun x => decide (k ≤ x)) ∧
      PP.AlmostSelfStabilising (fun x => decide (k ≤ x)) := by
  have : Nonempty (Reg (n + 1)) := ⟨.R⟩
  obtain ⟨Q, _, _, PP, i, -, hcard, hI, hdec, hss⟩ :=
    theorem_5 (prog (n + 1)) (wellFormed _) (prog_decides (n + 1))
  rw [threshold_shift] at hdec hss
  have hS := S_ge (n := n + 1) (by omega)
  have hsize := size_le (n := n + 1)
  simp only [Nat.add_sub_cancel] at hS
  exact ⟨Q, _, _, PP, S (n + 1) + i, by omega, by nlinarith, hI, hdec, hss⟩

end Podc.PPDoubleExpThresholds
