import Papers.PODC2022.AdaptiveBAFewerWords.WeakBAAdaptive

/-!
# Algorithm 3 of [CKS22] as printed: `t + 1` phases and unguarded leaders

Two slips of the pseudocode that break the adaptive complexity (Lemma 6, Section 6.1), each with a
run with `n = 7`, `t = 3` and a single Byzantine process `p1`, so `f = 1 < (n − t − 1)/2 = 3/2`.

**Line 1 runs `t + 1` phases** (the text, Lemma 6's proof and Section 6.1 say `n`).
`lemma6_false_printed_phases`: the Byzantine leader of phase 1 drives a full phase but sends the
finalize certificate only to `p2, p3, p4`, the leaders of phases 2–4, which are therefore silent.
After the `t + 1 = 4` phases, `p5, p6, p0` are undecided and send `help_req`; with the Byzantine
`help_req` that is `t + 1` requests, so they form a fallback certificate and the (quadratic)
fallback runs. With the text's `n = 7` phases the same adversary is harmless (`lemma6_n_phases_ok`):
phases 5–7 are led by undecided correct processes and everybody decides.

**Lines 37 and 48 are not guarded** by "the leader proposed". `unguarded_silent_phases_cost`: after
phase 1 everybody has decided, so phases 2–7 should be silent, but the Byzantine process sends each
correct leader an unsolicited `commit` message; the leader relays it, everybody answers `decide`,
and the leader broadcasts a finalize certificate: `3n − 1` words per phase, `132` words in total
against `5n + 2nf = 49` for the guarded reading (`words_le`).
-/

namespace Podc.AdaptiveBAFewerWords.WeakBA.PhaseCount

open Finset

/-- The adversary of the `t + 1`-phases run. -/
def advP : Adv 7 Bool where
  F := {1}
  inp := fun _ => true
  prop := fun j _ => if j = 1 then some true else none
  com := fun j _ => if j = 1 then some ⟨true, 1⟩ else none
  fin := fun j q => if j = 1 ∧ (q = 2 ∨ q = 3 ∨ q = 4) then some true else none
  reply := fun _ _ => none
  dec := fun _ _ => none
  helpReq := fun _ _ => true
  help := fun _ _ => none
  fbMsg := fun _ _ => none
  fbOut := some true

/-- `t = 3`, `K` phases, all values valid. -/
def parP (K : ℕ) (ib g : Bool) : Params Bool where
  t := 3
  K := K
  valid := fun _ => true
  intendedBu := ib
  guard := g
  voteOnce := false

/-- The facts computed about the run with `K` phases. -/
def runP (K : ℕ) (ib g : Bool) : Bool :=
  decide (CommitAvail (parP K ib g) advP ⟨true, 1⟩ 1) &&
  decide (FinAvail (parP K ib g) advP ⟨true, 1⟩ 1) &&
  decide (Former (parP K ib g) advP 5) && decide (FbRuns (parP K ib g) advP) &&
  (dAfter (parP K ib g) advP 5).isNone &&
  decide (∀ q, q ∉ advP.F → bu (parP K ib g) advP q = some true)

lemma advValid_P (K : ℕ) (ib g : Bool)
    (hc : CommitAvail (parP K ib g) advP ⟨true, 1⟩ 1)
    (hf : FinAvail (parP K ib g) advP ⟨true, 1⟩ 1) : AdvValid (parP K ib g) advP := by
  refine ⟨show ({1} : Finset (Fin 7)).card ≤ 3 by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _ _ _ q c h
    by_cases hj : j = 1
    · subst hj; simp only [advP, ite_true] at h; cases h; exact hc
    · simp [advP, hj] at h
  · intro j _ _ _ q v h
    by_cases hj : j = 1 ∧ (q = 2 ∨ q = 3 ∨ q = 4)
    · obtain ⟨rfl, -⟩ := hj; simp only [advP] at h; split at h <;> cases h; exact hf
    · simp [advP, hj] at h
  · intro j _ _ b c h; simp [advP] at h
  · intro b q c h; simp [advP] at h
  · intro b q m h; simp [advP] at h
  · intro b q c h; simp [advP] at h

/-- **Lemma 6 of [CKS22] fails for the printed line 1** (`t + 1` phases): `n = 7`, `t = 3`, one
Byzantine process (`2f < n − t − 1`), valid inputs, a valid adversary and an admissible fallback,
yet a correct process forms a fallback certificate and the fallback runs. -/
theorem lemma6_false_printed_phases (ib g : Bool) :
    ∃ A : Adv 7 Bool, 7 = 2 * (parP 4 ib g).t + 1 ∧ (parP 4 ib g).K = (parP 4 ib g).t + 1 ∧
      2 * A.F.card < 7 - (parP 4 ib g).t - 1 ∧ AdvValid (parP 4 ib g) A ∧
      Admissible (parP 4 ib g) A ∧ (∀ q, q ∉ A.F → (parP 4 ib g).valid (A.inp q)) ∧
      Former (parP 4 ib g) A 5 ∧ FbRuns (parP 4 ib g) A := by
  have h : runP 4 ib g = true := by cases ib <;> cases g <;> decide +kernel
  simp only [runP, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hc, hf, hform, hrun, -, hbu⟩ := h
  refine ⟨advP, rfl, rfl, show 2 * ({1} : Finset (Fin 7)).card < 7 - 3 - 1 by decide, advValid_P 4 ib g hc hf, ?_, fun _ _ => rfl,
    hform, hrun⟩
  intro x hx _
  rw [← hx 0 (by decide), hbu 0 (by decide)]; rfl

/-- With the text's `n` phases the same adversary does not trigger the fallback. -/
theorem lemma6_n_phases_ok (ib g : Bool) : ¬ FbRuns (parP 7 ib g) advP := by
  cases ib <;> cases g <;> decide +kernel

/-! ### Unguarded leaders -/

/-- Everybody decides in phase 1; afterwards the Byzantine process sends an unsolicited commit
message to every correct leader. -/
def advG : Adv 7 Bool where
  F := {1}
  inp := fun _ => true
  prop := fun j _ => if j = 1 then some true else none
  com := fun j _ => if j = 1 then some ⟨true, 1⟩ else none
  fin := fun j _ => if j = 1 then some true else none
  reply := fun j _ => if 2 ≤ j then some (.commit ⟨true, 1⟩) else none
  dec := fun _ _ => none
  helpReq := fun _ _ => false
  help := fun _ _ => none
  fbMsg := fun _ _ => none
  fbOut := none

/-- **Section 6.1 of [CKS22] fails for the printed (unguarded) lines 37 and 48**: in a valid run
with `n = 7` phases, `t = 3`, one Byzantine process and valid inputs, in which every correct process
decides in phase 1, the correct processes still send `196 > 5n + 2nf = 49` words in the phases:
every phase of a decided correct leader costs `4n` words. With the guard the same run costs
`2n = 14` words. -/
theorem unguarded_silent_phases_cost :
    AdvValid (parP 7 true false) advG ∧ (∀ q, q ∉ advG.F → (dAfter (parP 7 true false) advG q).isSome) ∧
      phasesWords (parP 7 true false) advG = 132 ∧ phasesWords (parP 7 true true) advG = 12 := by
  have hc : CommitAvail (parP 7 true false) advG ⟨true, 1⟩ 1 := by decide +kernel
  have hc' : ∀ j, 2 ≤ j → j ≤ 7 → CommitAvail (parP 7 true false) advG ⟨true, 1⟩ j := by
    intro j h1 h2; interval_cases j <;> decide +kernel
  have hf : FinAvail (parP 7 true false) advG ⟨true, 1⟩ 1 := by decide +kernel
  refine ⟨⟨show ({1} : Finset (Fin 7)).card ≤ 3 by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro j _ _ _ q c h
    by_cases hj : j = 1
    · subst hj; simp only [advG, ite_true] at h; cases h; exact hc
    · simp [advG, hj] at h
  · intro j _ _ _ q v h
    by_cases hj : j = 1
    · subst hj; simp only [advG, ite_true] at h; cases h; exact hf
    · simp [advG, hj] at h
  · intro j h1 h2 b c h
    by_cases hj : 2 ≤ j
    · simp only [advG, hj, ite_true] at h; cases h; exact hc' j hj h2
    · simp [advG, hj] at h
  · intro b q c h; simp [advG] at h
  · intro b q m h; simp [advG] at h
  · intro b q c h; simp [advG] at h
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-! ### The "vote at most once per run" reading of line 33 -/

/-- The Byzantine leader of phase 1 collects one vote from everybody and does nothing else. -/
def advV : Adv 7 Bool where
  F := {1}
  inp := fun _ => true
  prop := fun j _ => if j = 1 then some true else none
  com := fun _ _ => none
  fin := fun _ _ => none
  reply := fun _ _ => none
  dec := fun _ _ => none
  helpReq := fun _ _ => false
  help := fun _ _ => none
  fbMsg := fun _ _ => none
  fbOut := some true

/-- `t = 3`, `n` phases, guarded leaders, "vote once per run". -/
def parV (ib : Bool) : Params Bool where
  t := 3
  K := 7
  valid := fun _ => true
  intendedBu := ib
  guard := true
  voteOnce := true

/-- **Lemmas 16 and 6 of [CKS22] fail if "for the first time" (line 33) means "once per run"**:
`n = 7` phases, `t = 3`, one Byzantine process. The Byzantine leader of phase 1 spends everybody's
single vote; the non-silent phase 2 of the correct, undecided leader `p2` then gets no vote, nobody
decides in any phase, and the fallback runs. (Under the per-phase reading, `lemma16` and `lemma6`
hold and `theorem5_false` breaks agreement instead.) -/
theorem lemma16_lemma6_false_voteOnce (ib : Bool) :
    AdvValid (parV ib) advV ∧ 2 * advV.F.card < 7 - 3 - 1 ∧ leader 7 2 ∉ advV.F ∧
      proposes 2 (stateAt (parV ib) advV 1) = true ∧
      (∀ q, finRcv (parV ib) advV 2 (stateAt (parV ib) advV 1) q = none) ∧
      (∀ q, q ∉ advV.F → dAfter (parV ib) advV q = none) ∧ FbRuns (parV ib) advV := by
  refine ⟨⟨show ({1} : Finset (Fin 7)).card ≤ 3 by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide,
    by decide, ?_, ?_, ?_, ?_⟩
  · intro j _ _ _ q c h; simp [advV] at h
  · intro j _ _ _ q v h; simp [advV] at h
  · intro j _ _ b c h; simp [advV] at h
  · intro b q c h; simp [advV] at h
  · intro b q m h; simp [advV] at h
  · intro b q c h; simp [advV] at h
  all_goals cases ib <;> decide +kernel

end Podc.AdaptiveBAFewerWords.WeakBA.PhaseCount
