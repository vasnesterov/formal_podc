import Papers.PODC2021.ContentionPredictions.LowerBounds

/-!
# Counterexamples around Theorem 3.3

1. **The proof step "`F = {V(s)}` is `(n, n)`-strongly selective" is false.** A non-interactive
   algorithm only guarantees that *some* participant of `P` is isolated by the first-round
   transmitter set `V(f P)`, not that *every* participant is isolated by some set. For `n = 2` and
   one bit of advice, the sets `V(0) = {0}`, `V(1) = {0, 1}` solve non-interactive contention
   resolution, but no set isolates `1` inside `Z = {0, 1}` (`not_stronglySelective_example`).
   Theorem 3.3 itself is true (`theorem_3_3`, via a parity argument instead of Theorem 3.2).

2. **Theorem 3.3 is false if "at most `b` bits" allows advice strings of different lengths**, as
   the definition of `b(n)`-non-interactive contention resolution says ("the advice `f_A(P)`
   contains no more than `b(n)` bits"). With the three strings `ε, 0, 1` of length `≤ 1`, three
   players can be told who transmits, but `1 < log₂ 3` (`theorem_3_3_false_variable_length`).
   The theorem holds for fixed-length `b`-bit advice (`{0,1}^b`, Section 3.1).
-/

namespace Podc.ContentionPredictions

open Finset

/-- Definition 3.1: a family `F` of subsets of `Fin n` is `(n, k)`-strongly selective if for
every `Z` with `|Z| ≤ k` and every `z ∈ Z` some `F ∈ F` satisfies `Z ∩ F = {z}`. -/
def StronglySelective {n : ℕ} (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ Z : Finset (Fin n), Z.card ≤ k → ∀ z ∈ Z, ∃ S ∈ F, Z ∩ S = {z}

/-- Non-interactive algorithm for `n = 2` with one bit: advice `0` lets player `0` transmit, advice
`1` lets both transmit. -/
def exAlg : DetAlg 2 (Bits 1) := fun a _ v => decide (a 0 = false → v = 0)

/-- The advice: `0` iff player `0` participates. -/
def exAdvice (P : Finset (Fin 2)) : Bits 1 := fun _ => decide ((0 : Fin 2) ∉ P)

theorem exAlg_nonInteractive : NonInteractive exAlg exAdvice := by
  rw [nonInteractive_iff]; decide

/-- **The proof of Theorem 3.3 fails**: the first-round transmitter sets of a correct
non-interactive algorithm need not form an `(n, n)`-strongly selective family. -/
theorem not_stronglySelective_example :
    NonInteractive exAlg exAdvice ∧
      ¬ StronglySelective 2 (univ.image fun a : Bits 1 => univ.filter fun v => exAlg a [] v) := by
  refine ⟨exAlg_nonInteractive, ?_⟩
  unfold StronglySelective
  decide

/-- Advice strings of length *at most* `b`. -/
abbrev VarBits (b : ℕ) := {l : List Bool // l.length ≤ b}

/-- Three players, advice `ε`, `0`, `1` (length `≤ 1`): `ε` lets player `0` transmit, `0` player `1`,
`1` player `2`. -/
def varAlg : DetAlg 3 (VarBits 1) := fun a _ v =>
  match a.1 with
  | [] => decide (v = 0)
  | [false] => decide (v = 1)
  | _ => decide (v = 2)

/-- The advice names the smallest participant. -/
def varAdvice (P : Finset (Fin 3)) : VarBits 1 :=
  if (0 : Fin 3) ∈ P then ⟨[], by simp⟩ else if (1 : Fin 3) ∈ P then ⟨[false], by simp⟩
  else ⟨[true], by simp⟩

theorem varAlg_nonInteractive : NonInteractive varAlg varAdvice := by
  rw [nonInteractive_iff]; decide

/-- **Theorem 3.3 is false for variable-length advice of at most `b` bits**: `b = 1` bit of advice
(strings `ε, 0, 1`) solves non-interactive contention resolution on `n = 3` players, although
`b = 1 < log₂ 3`. -/
theorem theorem_3_3_false_variable_length :
    NonInteractive varAlg varAdvice ∧ ¬ (Real.logb 2 3 ≤ (1 : ℕ)) := by
  refine ⟨varAlg_nonInteractive, ?_⟩
  rw [not_le, Nat.cast_one, Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num), Real.rpow_one]
  norm_num

/-- Group of the advice string: `ε ↦ 0`, `0 ↦ 1`, `1 ↦ 2`. -/
def varGroup (a : VarBits 1) : ℕ :=
  match a.1 with
  | [] => 0
  | [false] => 1
  | _ => 2

/-- Nine players in three groups `{3g, 3g+1, 3g+2}`; the advice names the group `g` of the smallest
participant. Round 0: `3g` and `3g+1` transmit. After silence, `3g+2` transmits; after a collision,
`3g` transmits. -/
def varAlgCD : DetAlg 9 (VarBits 1) := fun a h v =>
  match h with
  | [] => decide ((v : ℕ) = 3 * varGroup a ∨ (v : ℕ) = 3 * varGroup a + 1)
  | [false] => decide ((v : ℕ) = 3 * varGroup a + 2)
  | _ => decide ((v : ℕ) = 3 * varGroup a)

/-- The advice: the group of the smallest participant. -/
def varAdviceCD (P : Finset (Fin 9)) : VarBits 1 :=
  if ∃ v ∈ P, (v : ℕ) < 3 then ⟨[], by simp⟩
  else if ∃ v ∈ P, (v : ℕ) < 6 then ⟨[false], by simp⟩ else ⟨[true], by simp⟩

set_option maxRecDepth 100000 in
theorem varAlgCD_solves : SolvesIn true varAlgCD varAdviceCD 2 := by
  unfold SolvesIn SolvedAt
  decide

/-- **Theorem 3.5 is false for variable-length advice of at most `b` bits**: with collision
detection, `b = 1` bit of advice (strings `ε, 0, 1`) solves contention resolution on `n = 9` players
in `t = 2` rounds, although `t = 2 < log₂ 9 − 1`. -/
theorem theorem_3_5_false_variable_length :
    SolvesIn true varAlgCD varAdviceCD 2 ∧ ¬ (Real.logb 2 9 - (1 : ℕ) ≤ (2 : ℕ)) := by
  refine ⟨varAlgCD_solves, ?_⟩
  rw [not_le, Nat.cast_one, Nat.cast_ofNat, lt_sub_iff_add_lt,
    Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  norm_num

end Podc.ContentionPredictions
