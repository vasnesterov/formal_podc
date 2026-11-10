import Papers.PODC2022.AdaptiveBAFewerWords.WeakBAModel

/-!
# Lemma 15, Lemma 20 and Theorem 5 of [CKS22] fail: a commit-level attack

A run of Algorithm 3/4 with `n = 5`, `t = 2`, Byzantine `F = {p1, p2}` (the leaders of phases 1
and 2) and correct `p3, p4, p0` (`p0` leads phase 5). Values are `Bool`, every value is valid,
`q = ⌈(n+t+1)/2⌉ = 4`. Inputs: `p3` has `false`, `p4` and `p0` have `true`.

* **Phase 1** (Byzantine `p1`): proposes `true`; the three correct processes have `commit = ⊥` and
  vote. With the two Byzantine votes `p1` holds `QC_commit(true)` of level 1, which it keeps.
* **Phase 2** (Byzantine `p2`): proposes `false`; the correct processes still have `commit = ⊥` and
  vote, so the adversary now also holds `QC_commit(false)` of **level 2**. In round 3, `p2` sends
  the old `QC_commit(true)` of level 1: its level `1 ≥ commit_level = 0`, so every correct process
  sends `⟨decide, true, 2⟩` and sets `commit = true`, `commit_level = 1`. `p2` forms
  `QC_finalized(true)` and sends it to `p0` only: **`p0` decides `true`**.
* **Phase 3** (correct `p3`, undecided): `p3` proposes; the correct processes answer with their
  commit (level 1), and Byzantine `p1` answers with `QC_commit(false)` of level 2. `p3` relays the
  commit of maximal level, `false`/level 2; `2 ≥ 1`, so every correct process sends
  `⟨decide, false, 3⟩`; with the Byzantine decide messages `p3` forms and broadcasts
  `QC_finalized(false)`: **`p3` and `p4` decide `false`**.
* Phases 4 and 5 are led by decided correct processes and are silent. No correct process asks for
  help and the fallback never runs.

The proof of Lemma 15 assumes that the processes that send `decide` in the phase `l` of the first
finalize certificate set `commit_level = l` (line 47), but line 47 sets it to the level of the
*relayed* certificate, which may be older than certificates the adversary formed meanwhile.

The run is valid for every number of phases `K ∈ {3, 4, 5}` (the printed `t + 1 = 3` and the
text's `n = 5`), both readings of line 15 and of the leader guard. The same adversary also works
for `n = 11`, `t = 5`, `f = 2`, where `f < (n − t − 1)/2`: the regime in which the paper claims
that all correct processes decide in the phases (Lemma 16) and the fallback never runs (Lemma 6), so
nothing can repair the disagreement later.
-/

namespace Podc.AdaptiveBAFewerWords.WeakBA.Counterexample

open Finset

variable (n : ℕ) [NeZero n]

/-- The adversary of the run (Byzantine `p1`, `p2`; the run needs `n ≥ 4`). -/
def advA : Adv n Bool where
  F := {1, 2}
  inp := fun q => if q = 3 then false else true
  prop := fun j _ => if j = 1 then some true else if j = 2 then some false else none
  com := fun j _ => if j = 2 then some ⟨true, 1⟩ else none
  fin := fun j q => if j = 2 ∧ q = 0 then some true else none
  reply := fun j b => if j = 3 ∧ b = 1 then some (.commit ⟨false, 2⟩) else none
  dec := fun j _ => if j = 3 then some false else none
  helpReq := fun _ _ => false
  help := fun _ _ => none
  fbMsg := fun _ _ => none
  fbOut := none

/-- The parameters: resilience `t`, `K` phases, all values valid. -/
def parA (t K : ℕ) (ib g : Bool) : Params Bool where
  t := t
  K := K
  valid := fun _ => true
  intendedBu := ib
  guard := g
  voteOnce := false

/-- Everything that has to be computed about the run, as one boolean. -/
def runOK (t K : ℕ) (ib g : Bool) : Bool :=
  outcome (parA t K ib g) (advA n) 0 == some (some true) &&
  outcome (parA t K ib g) (advA n) 3 == some (some false) &&
  decide (¬ FbRuns (parA t K ib g) (advA n)) &&
  decide (CommitAvail (parA t K ib g) (advA n) ⟨true, 1⟩ 2) &&
  decide (FinAvail (parA t K ib g) (advA n) ⟨true, 2⟩ 2) &&
  decide (CommitAvail (parA t K ib g) (advA n) ⟨false, 2⟩ 3) &&
  decide (FinAvail (parA t K ib g) (advA n) ⟨false, 3⟩ 3) &&
  decide ((advA n).F.card ≤ t) && decide (3 ≤ K) &&
  decide ((advA n).F = {1, 2}) && decide ((1 : Fin n) ≠ 0) && decide ((2 : Fin n) ≠ 0) &&
  decide ((3 : Fin n) ≠ 1) && decide ((3 : Fin n) ≠ 2) && decide ((1 : Fin n) ≠ 2)

variable {n}

lemma runOK_5 (K : ℕ) (hK : 3 ≤ K ∧ K ≤ 5) (ib g : Bool) : runOK 5 2 K ib g = true := by
  obtain ⟨h1, h2⟩ := hK
  interval_cases K <;> cases ib <;> cases g <;> decide +kernel

lemma runOK_11 (K : ℕ) (hK : K = 6 ∨ K = 11) (ib g : Bool) : runOK 11 5 K ib g = true := by
  rcases hK with rfl | rfl <;> cases ib <;> cases g <;> decide +kernel

section
variable {t K : ℕ} {ib g : Bool} (h : runOK n t K ib g = true)
include h

lemma advValid_of : AdvValid (parA t K ib g) (advA n) := by
  simp only [runOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hc1, hf1, hc2, -, hF, -⟩ := h
  constructor
  · exact hF
  · intro j _ _ _ q c hc
    by_cases hj : j = 2
    · subst hj; simp only [advA, ite_true] at hc; cases hc; exact hc1
    · simp [advA, hj] at hc
  · intro j _ _ _ q v hv
    by_cases hj : j = 2 ∧ q = 0
    · obtain ⟨rfl, rfl⟩ := hj; simp only [advA, and_self, ite_true] at hv; cases hv; exact hf1
    · simp [advA, hj] at hv
  · intro j _ _ b c hc
    by_cases hj : j = 3 ∧ b = 1
    · obtain ⟨rfl, rfl⟩ := hj; simp only [advA, and_self, ite_true] at hc; cases hc; exact hc2
    · simp [advA, hj] at hc
  · intro b q c hc; simp [advA] at hc
  · intro b q m hm; simp [advA] at hm
  · intro b q c hc; simp [advA] at hc

lemma admissible_of : Admissible (parA t K ib g) (advA n) := by
  simp only [runOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  exact fun _ _ hrun => absurd hrun h.2.2.1

lemma not_agreement_of : ¬ Agreement {q | q ∉ (advA n).F} (outcome (parA t K ib g) (advA n)) := by
  simp only [runOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h0, h3, -, -, -, -, -, -, -, hF, h10, h20, h31, h32, -⟩ := h
  intro hag
  have := hag 0 (by simp [hF, h10.symm, h20.symm]) 3 (by simp [hF, h31, h32]) _ _ h0 h3
  simp at this

end

/-- **Theorem 5 (= Theorem 24) of [CKS22] is false**: Algorithm 3 violates Agreement (Lemma 20).
For `n = 5`, `t = 2` (two Byzantine processes) and any number of phases `3 ≤ K ≤ 5` (the printed
`t + 1` or the text's `n`), any reading of line 15 and of the leader guard: the adversary is valid
(unforgeable certificates), all inputs are valid, the fallback never runs (so the black box plays
no role), and two correct processes decide differently. -/
theorem theorem5_false (K : ℕ) (hK : 3 ≤ K ∧ K ≤ 5) (ib g : Bool) :
    ∃ A : Adv 5 Bool, AdvValid (parA 2 K ib g) A ∧ Admissible (parA 2 K ib g) A ∧
      (∀ q, q ∉ A.F → (parA 2 K ib g).valid (A.inp q)) ∧
      ¬ Agreement {q | q ∉ A.F} (outcome (parA 2 K ib g) A) :=
  have h := runOK_5 K hK ib g
  ⟨advA 5, advValid_of h, admissible_of h, fun _ _ => rfl, not_agreement_of h⟩

/-- The same attack with `n = 11`, `t = 5` and only two Byzantine processes, so `f < (n − t − 1)/2`
(the regime of Lemma 6 and Lemma 16), with `K = t + 1 = 6` or `K = n = 11` phases. -/
theorem theorem5_false_small_f (K : ℕ) (hK : K = 6 ∨ K = 11) (ib g : Bool) :
    ∃ A : Adv 11 Bool, 2 * A.F.card < 11 - 5 - 1 ∧ AdvValid (parA 5 K ib g) A ∧
      Admissible (parA 5 K ib g) A ∧ (∀ q, q ∉ A.F → (parA 5 K ib g).valid (A.inp q)) ∧
      ¬ Agreement {q | q ∉ A.F} (outcome (parA 5 K ib g) A) :=
  have h := runOK_11 K hK ib g
  ⟨advA 11, by decide, advValid_of h, admissible_of h, fun _ _ => rfl, not_agreement_of h⟩

/-- **Lemma 15 of [CKS22] is false**: in the run of `theorem5_false`, two correct processes update
`decision` during `invokePhase` to different values, and finalize certificates on both values can be
formed (on `true` in phase 2 and on `false` in phase 3). -/
theorem lemma15_false :
    dAfter (parA 2 5 true true) (advA 5) 0 = some true ∧
      dAfter (parA 2 5 true true) (advA 5) 3 = some false ∧
      FinAvail (parA 2 5 true true) (advA 5) ⟨true, 2⟩ 5 ∧
      FinAvail (parA 2 5 true true) (advA 5) ⟨false, 3⟩ 5 := by
  decide +kernel

end Podc.AdaptiveBAFewerWords.WeakBA.Counterexample
