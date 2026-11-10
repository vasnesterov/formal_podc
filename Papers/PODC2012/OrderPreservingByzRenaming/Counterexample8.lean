import Papers.PODC2012.OrderPreservingByzRenaming.TwoRound

/-!
# Algorithm 8 needs `n > 2t² + t`: a counterexample for `n = 9 > t² + 2t`, `t = 2`

The heading of §6.3 (and the table of contents) announce Algorithm 8 for `n > t² + 2t`; the caption of
Algorithm 8, the text and Theorem 45 say `n > 2t² + t`. The two bounds differ for `t ≥ 2`. We show
that the stronger heading is false: for `n = 9`, `t = 2` (so `n > t² + 2t = 8`) Algorithm 8 violates
order preservation.

*Execution.* Correct processes `0, …, 6` with ids `10, …, 16`; Byzantine processes `7, 8`.
In Round 1 the Byzantine processes send the ids `1` and `2` to process `0` only (nothing to the
others). In Round 2 both send to process `0` the echo `{10, …, 14, 1, 2, 3, 4}` (9 ids, 7 of them
timely at process `0`: valid), and nothing to the others. Then process `0` computes
`newid[10] = 3 + 3 + 2 + 2 + 7 = 17`, while process `1` computes `newid[11] = 1 + 1 + 7 + 7 = 16`:
the correct process with the smaller id gets the larger name.
-/

namespace Podc.OrderPreservingByzRenaming.TwoRound

open Cslib.Byzantine.LockStep

section Concrete

variable {n : ℕ}

/-- `inb1` with a decidable Byzantine set (for computation). -/
def inb1C (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg) (p : Fin n) :
    Fin n → Option Msg := fun j =>
  if j = p then some (.ident (x p)) else if j ∈ F then adv 0 j p else some (.ident (x j))

/-- `inb2` with a decidable Byzantine set (for computation). -/
def inb2C (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg) (p : Fin n) :
    Fin n → Option Msg := fun j =>
  if j = p then some (.echo (timely (inb1C F x adv p)))
  else if j ∈ F then adv 1 j p else some (.echo (timely (inb1C F x adv j)))

lemma inb1_eq_inb1C {s : Scenario (Fin n) ℕ Msg} {F : Finset (Fin n)} (hF : ∀ j, j ∈ s.byz ↔ j ∈ F)
    (p : Fin n) : inb1 s p = inb1C F s.input s.adv p := by
  funext j
  by_cases h1 : j = p
  · simp [inb1, inb1C, h1]
  · by_cases h2 : j ∈ F
    · simp [inb1, inb1C, h1, h2, (hF j).2 h2]
    · simp [inb1, inb1C, h1, h2, mt (hF j).1 h2]

lemma inb2_eq_inb2C {s : Scenario (Fin n) ℕ Msg} {F : Finset (Fin n)} (hF : ∀ j, j ∈ s.byz ↔ j ∈ F)
    (p : Fin n) : inb2 s p = inb2C F s.input s.adv p := by
  funext j
  by_cases h1 : j = p
  · simp [inb2, inb2C, h1, inb1_eq_inb1C hF]
  · by_cases h2 : j ∈ F
    · simp [inb2, inb2C, h1, h2, (hF j).2 h2]
    · simp [inb2, inb2C, h1, h2, mt (hF j).1 h2, inb1_eq_inb1C hF]

end Concrete

/-- The Byzantine processes `7, 8`. -/
def cexF : Finset (Fin 9) := {7, 8}

/-- Ids: process `j` has id `10 + j`. -/
def cexX (j : Fin 9) : ℕ := j.val + 10

/-- The adversary of the counterexample. -/
def cexAdv (r : ℕ) (b p : Fin 9) : Option Msg :=
  if p.val = 0 then
    if r = 0 then (if b.val = 7 then some (.ident 1) else some (.ident 2))
    else if r = 1 then some (.echo {10, 11, 12, 13, 14, 1, 2, 3, 4})
    else none
  else none

/-- The scenario of the counterexample. -/
def cexScenario : Scenario (Fin 9) ℕ Msg where
  byz := ↑cexF
  input := cexX
  adv := cexAdv

lemma cex_newid0 : newid 2 (inb1C cexF cexX cexAdv 0) (inb2C cexF cexX cexAdv 0) 10 = 17 := by
  decide +kernel

lemma cex_newid1 : newid 2 (inb1C cexF cexX cexAdv 1) (inb2C cexF cexX cexAdv 1) 11 = 16 := by
  decide +kernel

/-- **The heading of §6.3 is false**: for `n = 9`, `t = 2` (`n > t² + 2t`) Algorithm 8 does not solve
order-preserving renaming, whatever the target namespace: correct process `0` (id `10`) decides `17`
and correct process `1` (id `11`) decides `16`. Theorem 45's bound `n > 2t² + t` is needed. -/
theorem alg8_not_solves_t2_add_2t :
    9 > 2 ^ 2 + 2 * 2 ∧ ∀ M, ¬ Solves (⊤ : SimpleGraph (Fin 9)) (alg 9 2) (atMost 2) (OPRenaming M) := by
  refine ⟨by norm_num, fun M h => ?_⟩
  have hF : ∀ j, j ∈ cexScenario.byz ↔ j ∈ cexF := fun j => Iff.rfl
  have hbyz : cexScenario.byz ∈ (atMost 2 : AdvStructure (Fin 9)) := by
    simp [cexScenario, Set.ncard_coe_finset, cexF]
  have hrel : cexScenario.Reliable := fun _ _ _ h => h
  have h0 : (0 : Fin 9) ∈ cexScenario.honest := by simp [cexScenario, Scenario.honest, cexF]
  have h1 : (1 : Fin 9) ∈ cexScenario.honest := by simp [cexScenario, Scenario.honest, cexF]
  obtain ⟨-, -, -, hord⟩ := h cexScenario hbyz hrel ⟨fun p _ q _ hpq => by
    simpa [cexScenario, cexX, Fin.ext_iff] using hpq, fun _ _ => trivial⟩
  have d0 : Decides ⊤ (alg 9 2) cexScenario 0 17 := by
    rw [decides_iff 2 hrel, inb1_eq_inb1C hF, inb2_eq_inb2C hF]
    exact cex_newid0.symm
  have d1 : Decides ⊤ (alg 9 2) cexScenario 1 16 := by
    rw [decides_iff 2 hrel, inb1_eq_inb1C hF, inb2_eq_inb2C hF]
    exact cex_newid1.symm
  have := hord 0 h0 1 h1 17 16 d0 d1 (by simp [cexScenario, cexX])
  omega

end Podc.OrderPreservingByzRenaming.TwoRound
