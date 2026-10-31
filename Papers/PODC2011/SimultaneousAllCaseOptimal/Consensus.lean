import Papers.PODC2011.SimultaneousAllCaseOptimal.Optimality

/-!
# Consensus as a decision task

Consensus (`1`-set agreement, §5.1): inputs from `I` (complete: all vectors allowed), outputs in
`I`; every output is some process's input and all outputs are equal. Also: the failure-free run
with a given input vector, and the fact that in a run with at most `t < n` crashes some process is
correct.
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I M O : Type} [Fintype P]

/-- Consensus (`k = 1` of `k`-set agreement, §5.1) as a decision task: all input vectors are
allowed; the output vector is constant, equal to some process's input. -/
def consensus (P I : Type) : Task P I I where
  inputs := Set.univ
  rel ι o := ∃ v, (∃ q, ι q = v) ∧ ∀ q, o q = v

/-- To prove consensus correctness it suffices that all decisions are equal to one input value. -/
lemma consensus_correct_of {A : Protocol P I M I} {r : Run P I} {v : I} (hv : ∃ q, r.input q = v)
    (h : ∀ p m d, Decides A r p m d → d = v) :
    ∃ o, (consensus P I).rel r.input o ∧ ∀ p m d, Decides A r p m d → o p = d :=
  ⟨fun _ => v, ⟨v, hv, fun _ => rfl⟩, fun p m d hd => (h p m d hd).symm⟩

/-- In a correct consensus protocol, two decisions in the same run are equal. -/
lemma consensus_agree {A : Protocol P I M I} {t : ℕ} (hA : Solves A (consensus P I) t)
    {r : Run P I} (hr : (consensus P I).IsRun t r) {p q : P} {m m' : ℕ} {d d' : I}
    (hp : Decides A r p m d) (hq : Decides A r q m' d') : d = d' := by
  obtain ⟨o, ⟨v, -, hv⟩, ho⟩ := hA.correct r hr
  rw [← ho p m d hp, ← ho q m' d' hq, hv, hv]

/-- In a correct consensus protocol, a decision is some process's input. -/
lemma consensus_valid {A : Protocol P I M I} {t : ℕ} (hA : Solves A (consensus P I) t)
    {r : Run P I} (hr : (consensus P I).IsRun t r) {p : P} {m : ℕ} {d : I}
    (hp : Decides A r p m d) : ∃ q, r.input q = d := by
  obtain ⟨o, ⟨v, hv, hov⟩, ho⟩ := hA.correct r hr
  rw [← ho p m d hp, hov]; exact hv

/-- The failure-free run with input vector `ι`. -/
def ffRun (ι : P → I) : Run P I := ⟨ι, fun _ => none, fun _ => ∅⟩

lemma ffRun_isRun {T : Task P I O} (t : ℕ) {ι : P → I} (hι : ι ∈ T.inputs) :
    T.IsRun t (ffRun ι) := by
  refine ⟨⟨?_, fun p c hc => by simp [ffRun] at hc⟩, hι⟩
  have : (ffRun ι).faulty = ∅ := by
    ext p; simp [Run.Faulty, ffRun]
  rw [this]; simp

lemma ffRun_not_faulty {ι : P → I} (p : P) : ¬ (ffRun ι).Faulty p := by
  simp [Run.Faulty, ffRun]

end Podc.SimultaneousAllCaseOptimal
