import Papers.PODC2024.AnonymousCoverings.WriteScan
import Papers.PODC2024.AnonymousCoverings.Periodic

/-!
# Counterexamples for Section 4

All executions are periodic executions of the write–scan loop (Figure 1) from the initial
configuration, checked by kernel computation.

* `theorem_4_8_needs_registers`: with one register and two processors (inputs `0`, `1`), the two
  processors alternate *write; scan* forever, each reading only its own value: the stable views
  `{0}` and `{1}` are incomparable, so Theorem 4.8 fails. (The paper's Section 2.1 shows `N − 1`
  registers are useless; Section 4 tacitly uses `N` registers.)
* `theorem_4_8_needs_registers'`: the same with two registers and four processors in two
  groups of two (inputs `0, 0, 1, 1`): each group in turn covers both registers and scans.
* `lemma_4_6_needs_registers`: the same execution violates Lemma 4.6 (and hence Lemma 4.7) with
  `A = {0}`: Lemma 4.6 also needs `N ≤ |R|` (`Exec.lemma_4_6` proves it under that hypothesis).
-/

namespace Podc.AnonymousCoverings

open Finset

deriving instance DecidableEq for Loc
deriving instance DecidableEq for Cell
deriving instance DecidableEq for Act

instance {P R D X : Type*} [Fintype P] [Fintype R] [DecidableEq P] [DecidableEq R]
    [DecidableEq D] [DecidableEq X] : DecidableEq (Cfg P R D X) := fun a b =>
  decidable_of_iff (a.reg = b.reg ∧ a.loc = b.loc) (by cases a; cases b; simp)

instance {R V : Type*} [DecidableEq V] : DecidablePred (writeScan (R := R) (V := V)).stop :=
  fun _ => isFalse id

/-- Initial configuration of Figure 1 with inputs `0` and `1`. -/
abbrev ws0 (R : Type*) : Cfg (Fin 2) R (Finset (Fin 2)) (Finset (Fin 2)) :=
  initCfg (fun p : Fin 2 => ({p} : Finset (Fin 2))) ∅

/-! ### One register, two processors -/

/-- The cycle: `0` writes and reads, then `1` writes and reads. -/
def cyc1 : List (Act (Fin 2) (Fin 1)) := [.write 0 0, .read 0 0, .write 1 0, .read 1 0]

theorem cyc1_per : runOf cyc1 cyc1 (.idle 0) writeScan (ws0 (Fin 1)) (cyc1.length + cyc1.length) =
    runOf cyc1 cyc1 (.idle 0) writeScan (ws0 (Fin 1)) cyc1.length := by decide

/-- The execution with one register. -/
def exec1 : Exec (P := Fin 2) (writeScan (R := Fin 1) (V := Fin 2)) :=
  periodicExec writeScan (ws0 (Fin 1)) (by decide) cyc1_per (by decide)

theorem exec1_view (t : ℕ) (p : Fin 2) : (exec1.loc t p).d = {p} := by
  have := periodic_forall (pre := cyc1) (cyc := cyc1) (dflt := .idle 0) writeScan (ws0 (Fin 1))
    (by decide) cyc1_per (fun _ c => ∀ p : Fin 2, (c.loc p).d = {p}) (by decide) t
  exact this p

theorem exec1_live (p : Fin 2) : exec1.Live p := by
  intro T
  obtain ⟨t, ht, h⟩ := exists_ge_actOf (pre := cyc1) (cyc := cyc1) (dflt := .idle 0) (by decide)
    (i := 2 * p.val) (by have := p.isLt; simp [cyc1]; omega) T
  refine ⟨t, ht, 0, Or.inl ?_⟩
  change actOf cyc1 cyc1 (.idle 0) t = _
  rw [h]; fin_cases p <;> rfl

/-- **Theorem 4.8 needs at least as many registers as processors.** With two processors and one
register there is an infinite execution of Figure 1 whose stable views `{0}` and `{1}` are
incomparable: there is no least stable view (two sources). -/
theorem theorem_4_8_needs_registers :
    ∃ e : Exec (P := Fin 2) (writeScan (R := Fin 1) (V := Fin 2)), e.cfg 0 = ws0 (Fin 1) ∧
      IsStableView e id {0} ∧ IsStableView e id {1} ∧
      ¬ ∃ W₀, IsStableView e id W₀ ∧ ∀ W, IsStableView e id W → W₀ ⊆ W := by
  have hst : ∀ p : Fin 2, IsStableView exec1 id {p} := fun p =>
    ⟨p, exec1_live p, 0, fun t _ => exec1_view t p⟩
  refine ⟨exec1, rfl, hst 0, hst 1, ?_⟩
  rintro ⟨W₀, ⟨p, -, T, hT⟩, hmin⟩
  have hW : W₀ = {p} := by rw [← hT T le_rfl]; exact exec1_view T p
  subst hW
  fin_cases p
  · exact absurd (hmin {1} (hst 1)) (by decide)
  · exact absurd (hmin {0} (hst 0)) (by decide)

/-! ### Two registers, four processors in two groups -/

/-- Inputs: processors `0, 1` have input `0`, processors `2, 3` have input `1`. -/
def grp4 : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- Initial configuration of Figure 1 with four processors in two groups. -/
abbrev ws4 : Cfg (Fin 4) (Fin 2) (Finset (Fin 2)) (Finset (Fin 2)) :=
  initCfg (fun p : Fin 4 => ({grp4 p} : Finset (Fin 2))) ∅

/-- The cycle: each group in turn covers both registers (one write per member) and both members
scan; the members alternate registers in round-robin order. -/
def cyc4 : List (Act (Fin 4) (Fin 2)) :=
  [.write 0 0, .write 1 1, .read 0 0, .read 0 1, .read 1 0, .read 1 1,
   .write 2 0, .write 3 1, .read 2 0, .read 2 1, .read 3 0, .read 3 1,
   .write 0 1, .write 1 0, .read 0 0, .read 0 1, .read 1 0, .read 1 1,
   .write 2 1, .write 3 0, .read 2 0, .read 2 1, .read 3 0, .read 3 1]

theorem cyc4_per : runOf cyc4 cyc4 (.idle 0) writeScan ws4 (cyc4.length + cyc4.length) =
    runOf cyc4 cyc4 (.idle 0) writeScan ws4 cyc4.length := by decide +kernel

/-- The execution with two registers and four processors. -/
def exec4 : Exec (P := Fin 4) (writeScan (R := Fin 2) (V := Fin 2)) :=
  periodicExec writeScan ws4 (by decide) cyc4_per (by decide +kernel)

theorem exec4_view (t : ℕ) (p : Fin 4) : (exec4.loc t p).d = {grp4 p} := by
  have := periodic_forall (pre := cyc4) (cyc := cyc4) (dflt := .idle 0) writeScan ws4
    (by decide) cyc4_per (fun _ c => ∀ p : Fin 4, (c.loc p).d = {grp4 p}) (by decide +kernel) t
  exact this p

theorem exec4_live (p : Fin 4) : exec4.Live p := by
  intro T
  have hi : ∃ i < cyc4.length, ∃ r, cyc4.getD i (.idle 0) = .write p r := by
    fin_cases p
    · exact ⟨0, by decide, 0, rfl⟩
    · exact ⟨1, by decide, 1, rfl⟩
    · exact ⟨6, by decide, 0, rfl⟩
    · exact ⟨7, by decide, 1, rfl⟩
  obtain ⟨i, hi, r, hr⟩ := hi
  obtain ⟨t, ht, h⟩ := exists_ge_actOf (pre := cyc4) (cyc := cyc4) (dflt := .idle 0) (by decide)
    hi T
  refine ⟨t, ht, r, Or.inl ?_⟩
  change actOf cyc4 cyc4 (.idle 0) t = _
  rw [h, hr]

/-- **Theorem 4.8 fails with two registers and four processors.** Two groups of two processors
(inputs `0, 0, 1, 1`) take turns covering both registers; each processor only ever reads its own
group's value, so the stable views `{0}` and `{1}` are incomparable. This instance is not
degenerate: each scan reads two registers, and `N = 2M` as in the 1-register case. -/
theorem theorem_4_8_needs_registers' :
    ∃ e : Exec (P := Fin 4) (writeScan (R := Fin 2) (V := Fin 2)), e.cfg 0 = ws4 ∧
      IsStableView e id {0} ∧ IsStableView e id {1} ∧
      ¬ ∃ W₀, IsStableView e id W₀ ∧ ∀ W, IsStableView e id W → W₀ ⊆ W := by
  have hst : ∀ p : Fin 4, IsStableView exec4 id {grp4 p} := fun p =>
    ⟨p, exec4_live p, 0, fun t _ => exec4_view t p⟩
  refine ⟨exec4, rfl, hst 0, hst 2, ?_⟩
  rintro ⟨W₀, ⟨p, -, T, hT⟩, hmin⟩
  have hW : W₀ = {grp4 p} := by rw [← hT T le_rfl]; exact exec4_view T p
  subst hW
  fin_cases p
  · exact absurd (hmin {1} (hst 2)) (by decide)
  · exact absurd (hmin {1} (hst 2)) (by decide)
  · exact absurd (hmin {0} (hst 0)) (by decide)
  · exact absurd (hmin {0} (hst 0)) (by decide)

/-- **Lemma 4.6 needs at least as many registers as processors.** In the one-register execution,
take `A = {0}`, so `Ā = {1}`: at most `1 = |A|` register is ever last written by `Ā`, and `Ā` is
live, yet processor `1` only ever reads its own value, never from `A`. (Lemma 4.6 holds with
`N ≤ |R|`: `Exec.lemma_4_6`.) -/
theorem lemma_4_6_needs_registers :
    ∃ e : Exec (P := Fin 2) (writeScan (R := Fin 1) (V := Fin 2)), e.cfg 0 = ws0 (Fin 1) ∧
      ∃ (S : Finset (Fin 2)), (∀ t, (e.writtenBy Sᶜ t).card ≤ S.card) ∧ (∃ a ∈ Sᶜ, e.Live a) ∧
        ¬ ∃ t, ∃ a ∈ Sᶜ, ∃ r, e.act t = .read a r ∧ ∃ b ∈ S, (e.reg t r).writer = some b := by
  refine ⟨exec1, rfl, {0}, fun t => ?_, ⟨1, by decide, exec1_live 1⟩, ?_⟩
  · exact (card_le_univ _).trans (by simp)
  · rintro ⟨t, a, ha, r, hr, b, hb, hw⟩
    have := periodic_forall (pre := cyc1) (cyc := cyc1) (dflt := .idle 0) writeScan (ws0 (Fin 1))
      (by decide) cyc1_per
      (fun act c => ∀ r, act = .read 1 r → (c.reg r).writer ≠ some 0) (by decide +kernel) t r
    have ha1 : a = 1 := by
      have h : ∀ x : Fin 2, x ∈ ({0} : Finset (Fin 2))ᶜ → x = 1 := by decide
      exact h a ha
    simp only [mem_singleton] at hb; subst ha1 hb
    exact this hr hw

end Podc.AnonymousCoverings
