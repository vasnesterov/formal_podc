import Papers.PODC2022.AdaptiveBAFewerWords.WeakBAModel

/-!
# The hand-off to `A_fallback` in Algorithm 3 of [CKS22]: Lemma 19 and Lemma 22 fail

Two runs with `n = 3`, `t = 1`, one Byzantine process `p1` (the leader of phase 1) and correct
`p2`, `p0`; `q = ⌈(n+t+1)/2⌉ = 3`, so no quorum forms without the Byzantine process.

**Lemma 19 / Agreement (`lemma19_false`).** All values are valid; both correct inputs are `false`.
In phase 1 the Byzantine leader proposes `true`, gets the three votes, sends `QC_commit(true)` to
everybody, collects the three `decide` messages and keeps `QC_finalized(true)`. In phases 2 and 3
the correct leaders relay the commit on `true`, but without the Byzantine `decide` they get only two
of the three messages: nobody decides. Both correct processes broadcast `help_req`, receive
`t + 1 = 2` of them, and broadcast the fallback certificate with `decision = undecided` (line 11)
and set `fallback_start` (so they never echo, line 21). In round 3 the Byzantine process answers
`p2`'s help request with `⟨help, true, QC_finalized(true)⟩`: **`p2` decides `true`** (line 14).
`p2` never sends `true` with its proof to anybody, so `p0` adopts nothing and runs `A_fallback`
with its input `false` (or with `undecided`, line 15) while `p2` runs it with `true`. The inputs
differ, so a strong-BA fallback may output `false` (e.g. interactive consistency + majority, with the
Byzantine input `false`): **`p0` decides `false`**. The proof of Lemma 19 claims that in the `2δ`
window every correct process learns the decisions of the others ("Specifically, they receive `v`
from `p`"), but a decision made at line 14 is never broadcast with its proof.

**Lemma 22 / Unique validity (`lemma22_false`, the printed line 15).** Only `true` is valid and
both correct inputs are `true`; the Byzantine process is silent. Nobody decides in the phases
(two votes `< q`), the fallback runs, and line 15 sets `bu_decision ← decision = undecided` at both
correct processes. By strong unanimity the fallback returns `undecided`, which is not valid, so both
decide `⊥` (line 29) although only one valid value exists. The proof of Lemma 22 says the fallback
runs "with valid inputs (either their initial valid values, or a valid value they adopt)": with that
reading (`intendedBu = true`) the run decides `true` (`lemma22_intended_ok`).
-/

namespace Podc.AdaptiveBAFewerWords.WeakBA.Fallback

open Finset

/-! ### Lemma 19 -/

/-- The adversary of the Lemma 19 run. -/
def advB (out : Option Bool) : Adv 3 Bool where
  F := {1}
  inp := fun _ => false
  prop := fun j _ => if j = 1 then some true else none
  com := fun j _ => if j = 1 then some ⟨true, 1⟩ else none
  fin := fun _ _ => none
  reply := fun _ _ => none
  dec := fun _ _ => none
  helpReq := fun _ _ => false
  help := fun b q => if b = 1 ∧ q = 2 then some ⟨true, 1⟩ else none
  fbMsg := fun _ _ => none
  fbOut := out

/-- `t = 1`, `K` phases, every value valid. -/
def parB (K : ℕ) (ib g vo : Bool) : Params Bool where
  t := 1
  K := K
  valid := fun _ => true
  intendedBu := ib
  guard := g
  voteOnce := vo

/-- The facts computed about the Lemma 19 run. -/
def runB (K : ℕ) (ib g vo : Bool) : Bool :=
  dAfter (parB K ib g vo) (advB (some false)) 2 == none &&
  dH3 (parB K ib g vo) (advB (some false)) 2 == some true &&
  outcome (parB K ib g vo) (advB (some false)) 2 == some (some true) &&
  outcome (parB K ib g vo) (advB (some false)) 0 == some (some false) &&
  bu (parB K ib g vo) (advB (some false)) 0 != bu (parB K ib g vo) (advB (some false)) 2 &&
  decide (CommitAvail (parB K ib g vo) (advB (some false)) ⟨true, 1⟩ 1) &&
  decide (FinAvail (parB K ib g vo) (advB (some false)) ⟨true, 1⟩ K) &&
  decide (FbRuns (parB K ib g vo) (advB (some false)))

lemma runB_ok (K : ℕ) (hK : K = 2 ∨ K = 3) (ib g vo : Bool) : runB K ib g vo = true := by
  rcases hK with rfl | rfl <;> cases ib <;> cases g <;> cases vo <;> decide +kernel

/-- **Lemma 19 and Lemma 20 (Agreement) of [CKS22] fail**: with `n = 3`, `t = 1`, one Byzantine
process, `K = t + 1 = 2` or `K = n = 3` phases, either reading of line 15 and either reading of line 33, a correct process `p2`
decides `true` before the fallback (at line 14, on a Byzantine help answer), the fallback runs on
different inputs and outputs `false`, which the other correct process `p0` decides. -/
theorem lemma19_false (K : ℕ) (hK : K = 2 ∨ K = 3) (ib g vo : Bool) :
    ∃ A : Adv 3 Bool, AdvValid (parB K ib g vo) A ∧ Admissible (parB K ib g vo) A ∧
      (∀ q, q ∉ A.F → (parB K ib g vo).valid (A.inp q)) ∧
      outcome (parB K ib g vo) A 2 = some (some true) ∧ outcome (parB K ib g vo) A 0 = some (some false) ∧
      ¬ Agreement {q | q ∉ A.F} (outcome (parB K ib g vo) A) := by
  have h := runB_ok K hK ib g vo
  simp only [runB, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨-, -, h2, h0, hbu, hc, hf, -⟩ := h
  refine ⟨advB (some false), ⟨show ({1} : Finset (Fin 3)).card ≤ 1 by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ => rfl, h2, h0, ?_⟩
  · intro j _ _ _ q c hc'
    by_cases hj : j = 1
    · subst hj; simp only [advB, ite_true] at hc'; cases hc'; exact hc
    · simp [advB, hj] at hc'
  · intro j _ _ _ q v hv; simp [advB] at hv
  · intro j _ _ b c hc'; simp [advB] at hc'
  · intro b q c hc'
    by_cases hb : b = 1 ∧ q = 2
    · simp only [advB, hb, and_self, ite_true] at hc'; cases hc'; exact hf
    · simp [advB, hb] at hc'
  · intro b q m hm; simp [advB] at hm
  · intro b q c hc'; simp [advB] at hc'
  · intro x hx _
    exfalso; apply hbu
    rw [hx 0 (by decide), hx 2 (by decide)]
  · intro hag
    have := hag 2 (by decide) 0 (by decide) _ _ h2 h0
    simp at this

/-! ### Lemma 22 -/

/-- The adversary of the Lemma 22 run: a silent Byzantine `p1`, inputs `true`. -/
def advC (out : Option Bool) : Adv 3 Bool where
  F := {1}
  inp := fun _ => true
  prop := fun _ _ => none
  com := fun _ _ => none
  fin := fun _ _ => none
  reply := fun _ _ => none
  dec := fun _ _ => none
  helpReq := fun _ _ => false
  help := fun _ _ => none
  fbMsg := fun _ _ => none
  fbOut := out

/-- `t = 1`, `K` phases, only `true` is valid. -/
def parC (K : ℕ) (ib g : Bool) : Params Bool where
  t := 1
  K := K
  valid := fun v => v
  intendedBu := ib
  guard := g
  voteOnce := false

lemma advValid_C (K : ℕ) (ib g : Bool) (out : Option Bool) : AdvValid (parC K ib g) (advC out) :=
  ⟨show ({1} : Finset (Fin 3)).card ≤ 1 by decide, by simp [advC], by simp [advC], by simp [advC], by simp [advC], by simp [advC],
    by simp [advC]⟩

/-- **Lemma 22 (unique validity) of [CKS22] fails for the printed line 15**: `n = 3`, `t = 1`, a
silent Byzantine process, both correct inputs `true`, only `true` valid. The only admissible
fallback output is `undecided` (strong unanimity on the inputs `undecided`), and both correct
processes decide `⊥`, although there are no two different valid values at all. -/
theorem lemma22_false (K : ℕ) (hK : K = 2 ∨ K = 3) (g : Bool) (out : Option Bool)
    (hadm : Admissible (parC K false g) (advC out)) :
    outcome (parC K false g) (advC out) 0 = some none ∧
      ∀ Ex : Set Bool, ¬ UniqueValidity (fun v => (parC K false g).valid v = true) Ex
        {q | q ∉ (advC out).F} (outcome (parC K false g) (advC out)) := by
  have hrun : FbRuns (parC K false g) (advC out) := by
    rcases hK with rfl | rfl <;> cases g <;> rcases out with _ | _ | _ <;> decide +kernel
  have hbu : ∀ q, q ∉ (advC out).F → bu (parC K false g) (advC out) q = none := by
    rcases hK with rfl | rfl <;> cases g <;> rcases out with _ | _ | _ <;> decide +kernel
  have hout : out = none := hadm none hbu hrun
  subst hout
  have h0 : outcome (parC K false g) (advC none) 0 = some none := by
    rcases hK with rfl | rfl <;> cases g <;> decide +kernel
  refine ⟨h0, fun Ex hU => ?_⟩
  obtain ⟨a, -, b, -, ha, hb, hab⟩ := hU 0 (by decide) none h0
  simp only [parC] at ha hb
  exact hab (ha.trans hb.symm)

/-- With the reading of the proof of Lemma 22 (`bu_decision` = input unless decided) the same run
decides `true`: the fallback must return the common input. -/
theorem lemma22_intended_ok (K : ℕ) (hK : K = 2 ∨ K = 3) (g : Bool) (out : Option Bool)
    (hadm : Admissible (parC K true g) (advC out)) :
    outcome (parC K true g) (advC out) 0 = some (some true) ∧
      outcome (parC K true g) (advC out) 2 = some (some true) := by
  have hrun : FbRuns (parC K true g) (advC out) := by
    rcases hK with rfl | rfl <;> cases g <;> rcases out with _ | _ | _ <;> decide +kernel
  have hbu : ∀ q, q ∉ (advC out).F → bu (parC K true g) (advC out) q = some true := by
    rcases hK with rfl | rfl <;> cases g <;> rcases out with _ | _ | _ <;> decide +kernel
  have hout : out = some true := hadm (some true) hbu hrun
  subst hout
  rcases hK with rfl | rfl <;> cases g <;> decide +kernel

end Podc.AdaptiveBAFewerWords.WeakBA.Fallback
