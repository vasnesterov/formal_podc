import Papers.PODC2021.GoodCaseLatencyBB.PsyncLowerBound
import Papers.PODC2021.GoodCaseLatencyBB.SplitBrain
import Papers.PODC2021.GoodCaseLatencyBB.SmallCases
import Podc.Computability.Distributed.Byzantine.PartialSync.Merge

/-!
# Partially synchronous Byzantine broadcast is impossible for `n ∈ {2, 3}`, `f ≥ 1`

For `n = 2` or `n = 3` and `f ≥ 1`, no (authenticated) protocol solves partially synchronous
Byzantine broadcast (`IsPsyncBB`), by the classic partition arguments (runs with at most one
faulty process suffice):

* `n = 2`, `P = {s, p}`. Run `Rₐ`: `s` faulty and silent, `GST = 0`: by termination `p` commits
  some `w`. Run `R_b`: `p` faulty and silent, `s` has input `v ≠ w`: by validity `s` commits `v`.
  Run `R_c`: nobody faulty, `GST = T + 1` and the messages between `s` and `p` are delayed until
  `T + 1`: up to `T`, `p` behaves as in `Rₐ` and `s` as in `R_b`, so agreement fails.
* `n = 3`, `P = {s, p, q}`. `R₁`: `q` faulty and silent, `s` has input `a`: `p` commits `a`.
  `R₂`: `p` faulty and silent, `s` has input `b`: `q` commits `b`. `R₃`: `s` faulty, it replays
  its `R₁`-messages to `p` and its `R₂`-messages to `q` until `T`; messages between `p` and `q`
  are delayed until `T + 1 = GST`. Then `p` behaves as in `R₁` and `q` as in `R₂`.

Both `R_c` and `R₃` are the library run `Run.merge` of the two silent runs.

Consequently Theorems 6 and 7 hold for all `n ≥ 2` (`theorem_6_all`, `theorem_7_all`); for
`n = 1` they are false (`theorem_7_false_one` in `SmallCases.lean`).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P]

variable [Fintype P] {A : Algorithm P M S V V} {Au : Auth P M K}

theorem three_cases (h3 : Fintype.card P = 3) {s p q x : P} (hps : p ≠ s) (hqs : q ≠ s)
    (hpq : p ≠ q) (hxs : x ≠ s) (hxp : x ≠ p) : x = q := by
  by_contra hxq
  have : ({x, p, q, s} : Finset P).card ≤ 3 := h3 ▸ card_le_univ _
  rw [card_insert_of_notMem (by simp [hxp, hxq, hxs]),
    card_insert_of_notMem (by simp [hpq, hps]), card_insert_of_notMem (by simp [hqs])] at this
  simp at this

/-- Partially synchronous BB is impossible for `n = 2` and `f ≥ 1` (for every algorithm: all
runs used are canonical, so unforgeability is not needed). -/
theorem psyncBB_impossible_two {s : P} {f D : ℕ} (hf : 1 ≤ f)
    (h2 : Fintype.card P = 2) {a b : V} (hab : a ≠ b) : ¬ IsPsyncBB Au A s f D := by
  intro hA
  obtain ⟨p, hps⟩ := Fintype.exists_ne_of_one_lt_card (by omega) s
  have hall : ∀ x, x ≠ s → x = p := fun x hx => two_cases h2 hx hps
  let Ra := Run.quiet (M := M) {s} (fun _ => a)
  obtain ⟨w, Ta, hTa⟩ := hA.termination Ra (Run.quiet_valid (by simpa using hf) _)
    Run.quiet_authValid p (by simp [Ra, Run.quiet, hps])
  obtain ⟨v, hvw⟩ : ∃ v, v ≠ w := by
    classical
    exact if h : a = w then ⟨b, fun e => hab (h.trans e.symm)⟩ else ⟨a, h⟩
  let I : P → V := Function.update (fun _ => a) s v
  let Rb := Run.quiet (M := M) {p} I
  obtain ⟨Tb, hTb⟩ := hA.validity Rb (Run.quiet_valid (by simpa using hf) _) Run.quiet_authValid
    rfl (by simp [Rb, Run.quiet, hps.symm]) s (by simp [Rb, Run.quiet, hps.symm])
  -- `R_c`: merge `Rₐ` (seen by `p`) and `R_b` (seen by `s`); nobody is correct in both
  have hcov : ∀ x, x ∈ Ra.faulty ∨ x ∈ Rb.faulty := fun x => by
    by_cases hx : x = s
    · exact Or.inl (by simp [Ra, Run.quiet, hx])
    · exact Or.inr (by simp [Rb, Run.quiet, hall x hx])
  set Rc := Ra.merge A Rb (max Ta Tb)
  refine hvw (hA.agreement Rc
    (Run.merge_valid_of_forall_mem hcov (fun _ _ _ _ _ => le_rfl) fun _ _ _ _ _ => le_rfl)
    (Run.merge_authValid_of_forall_mem hcov) s (by simp [Rc, Ra, Run.quiet]) p
    (by simp [Rc, Rb, Run.quiet]) v w ?_ ?_)
  · exact Run.merge_decides_right Run.quiet_canonical (by simp [Ra, Run.quiet])
      (by simp [Run.quiet, hps.symm]) (le_max_right _ _) (by rw [hTb]; simp [Rb, Run.quiet, I])
  · exact Run.merge_decides_left Run.quiet_canonical (by simp [Run.quiet, hps])
      (by simp [Rb, Run.quiet]) (le_max_left _ _) hTa

/-- Partially synchronous BB is impossible for `n = 3` and `f ≥ 1`. -/
theorem psyncBB_impossible_three (hU : A.Unforging Au) {s : P} {f D : ℕ} (hf : 1 ≤ f)
    (h3 : Fintype.card P = 3) {a b : V} (hab : a ≠ b) : ¬ IsPsyncBB Au A s f D := by
  intro hA
  obtain ⟨p, q, hpq, hps, hqs⟩ := exists_three s (by omega)
  have hall : ∀ x, x ≠ s → x ≠ p → x = q := fun x hxs hxp => three_cases h3 hps hqs hpq hxs hxp
  let I0 : P → V := fun _ => a
  let R1 := Run.quiet (M := M) {q} I0
  obtain ⟨T1, hT1⟩ := hA.validity R1 (Run.quiet_valid (by simpa using hf) _) Run.quiet_authValid
    rfl (by simp [R1, Run.quiet, hqs.symm]) p (by simp [R1, Run.quiet, hpq])
  let R2 := Run.quiet (M := M) {p} (Function.update I0 s b)
  obtain ⟨T2, hT2⟩ := hA.validity R2 (Run.quiet_valid (by simpa using hf) _) Run.quiet_authValid
    rfl (by simp [R2, Run.quiet, hps.symm]) q (by simp [R2, Run.quiet, hpq.symm])
  -- `R₃`: merge `R₁` (seen by `p`) and `R₂` (seen by `q`); `s`, correct in both, is Byzantine
  set R3 := R1.merge A R2 (max T1 T2)
  have hR3f : R3.faulty ⊆ {s} := fun x hx => by
    simp only [R3, Run.mem_merge_faulty, R1, R2, Run.quiet, mem_singleton] at hx
    by_contra hxs
    exact hx.1 (hall x (by simpa using hxs) hx.2)
  refine hab (hA.agreement R3
    (Run.merge_valid ((card_le_card hR3f).trans (by simpa using hf)) (fun _ _ _ _ _ => le_rfl)
      fun _ _ _ _ _ => le_rfl)
    (Run.merge_authValid hU Run.quiet_canonical Run.quiet_canonical) p
    (by simp [R3, R2, Run.quiet]) q (by simp [R3, R1, Run.quiet]) a b ?_ ?_)
  · exact Run.merge_decides_left Run.quiet_canonical (by simp [Run.quiet, hpq])
      (by simp [R2, Run.quiet]) (le_max_left _ _) (by rw [hT1]; rfl)
  · exact Run.merge_decides_right Run.quiet_canonical (by simp [R1, Run.quiet])
      (by simp [Run.quiet, hpq.symm]) (le_max_right _ _) (by rw [hT2]; simp [R2, Run.quiet])

/-- **Partially synchronous Byzantine broadcast is impossible for `n ∈ {2, 3}`** (with `f ≥ 1`,
authenticated, any unforging algorithm, at least two values). -/
theorem psyncBB_impossible (hU : A.Unforging Au) {s : P} {f D : ℕ} (hf : 1 ≤ f)
    (h23 : Fintype.card P = 2 ∨ Fintype.card P = 3) {a b : V} (hab : a ≠ b) :
    ¬ IsPsyncBB Au A s f D := by
  rcases h23 with h | h
  · exact psyncBB_impossible_two (A := A) (Au := Au) hf h hab
  · exact psyncBB_impossible_three hU hf h hab

/-- **Theorem 6 of [ANRX21]** for all `n ≥ 2`, `f ≥ 1`: partially synchronous BB does not have
good-case latency of one round. (False for `n = 1`, see `theorem_7_false_one`.) -/
theorem theorem_6_all (hU : A.Unforging Au) {s : P} {f D : ℕ} (hD : 0 < D) (hf : 1 ≤ f)
    (h2 : 2 ≤ Fintype.card P) {a b : V} (hab : a ≠ b) (hA : IsPsyncBB Au A s f D) :
    ¬ PsyncGoodCaseRounds Au A s f D 1 := by
  by_cases h3 : 3 ≤ Fintype.card P
  · exact theorem_6_rounds hU hD hf h3 hab hA
  · exact absurd hA (psyncBB_impossible hU hf (by omega) hab)

/-- **Theorem 7 of [ANRX21]** for all `n ≥ 2`, `f ≥ 1` with `n ≤ 5f − 2`: partially synchronous
BB does not have good-case latency of two rounds. (False for `n = 1`, see
`theorem_7_false_one`.) -/
theorem theorem_7_all (hU : A.Unforging Au) {s : P} {f D : ℕ} (hD : 0 < D) (hf : 1 ≤ f)
    (h2 : 2 ≤ Fintype.card P) (hn : Fintype.card P ≤ 5 * f - 2) {a b : V} (hab : a ≠ b)
    (hA : IsPsyncBB Au A s f D) : ¬ PsyncGoodCaseRounds Au A s f D 2 := by
  by_cases h : 2 ≤ f ∧ 3 ≤ Fintype.card P
  · exact theorem_7 hU hD h.1 h.2 hn hab hA
  · exact absurd hA (psyncBB_impossible hU hf (by omega) hab)

end GoodCaseLatencyBB
