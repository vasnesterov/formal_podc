import Papers.PODC2013.ConstantBarriersMutex.RMRMain

namespace Podc.ConstantBarriersMutex

/-- `n` steps of `q`. -/
def evSteps {h : ℕ} (q : Proc h) (n : ℕ) : List (Ev h) := List.replicate n (.step q)
/-- `n` flushes of `q`. -/
def evFlushes {h : ℕ} (q : Proc h) (n : ℕ) : List (Ev h) := List.replicate n (.flush q)

/-- Events of the witness execution (4 processes, `h = 2`), up to the point where process `0`
leaves statement 25. -/
def tightEvs : List (Ev 2) :=
  evSteps 2 12 ++ evSteps 0 5 ++ evSteps 2 13 ++ evFlushes 2 2 ++ evSteps 0 8 ++ evSteps 1 12 ++ evSteps 3 11 ++
  evSteps 0 2 ++ evFlushes 2 1 ++ evSteps 3 1 ++ evSteps 0 2 ++ evSteps 3 22 ++ evFlushes 3 2 ++ evSteps 0 1 ++ evFlushes 3 6 ++
  evSteps 0 2 ++ evSteps 2 14 ++ evSteps 1 5 ++ evSteps 1 24 ++ evFlushes 1 9 ++ evSteps 0 2

/-- The run that executes the events of `l` and then `d` forever. -/
def Run.ofEvents {h : ℕ} (l : List (Ev h)) (d : Ev h) : Run h where
  ev t := l.getD t d
  s t := Nat.rec Cfg.init (fun i s => s.next (l.getD i d)) t
  init := rfl
  step _ := rfl

instance {h : ℕ} (c : PC h) : Decidable c.At25 := by unfold PC.At25; split <;> infer_instance

/-- The witness run: `tightEvs`, then process `0` fails its CAS (statement 26) and busy-waits at
statement 27 until process `2` hands the lock over to it; then nothing happens. -/
def tightRun : Run 2 :=
  Run.ofEvents (tightEvs ++ evSteps 0 2 ++ evFlushes 1 1 ++ evSteps 2 45 ++ evSteps 0 1) (.flush 0)

set_option maxRecDepth 100000 in
lemma tightRun_25 : (tightRun.s 39).pc 0 = .e24 ∧ tightRun.ev 39 = .step 0 ∧
    (∀ t ∈ Finset.Ioo 39 156, ((tightRun.s t).pc 0).At25) ∧ tightRun.rmr 0 40 156 = 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma tightRun_27 : (∀ t ∈ Finset.Ico 157 205, (tightRun.s t).pc 0 = .e27) ∧
    tightRun.rmr 0 157 205 = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma tightRun_passage : (tightRun.s 0).pc 2 = .rem ∧ tightRun.ev 0 = .step 2 ∧
    (tightRun.s 103).pc 2 = .rem ∧ (∀ t ∈ Finset.Ioo 0 103, (tightRun.s t).pc 2 ≠ .rem) := by
  decide +kernel

/-- **The bound of `stmt25_rmr_le` is tight.** There is a run (4 processes) in which process `0`
incurs `6` RMRs while busy-waiting at statement 25: it reads `lock` remotely 4 times (values
`2, 3, 1, 2`: a release followed by a successful CAS in the epoch `exits = 1`, hand-overs in the
epochs `exits = 2` and `exits = 3`) and `exits` remotely twice. The proof of Lemma 10 in the paper
claims "at most 4 RMRs ... at most twice when it reads variable `exits` and at most twice when it
reads `lock`". -/
theorem stmt25_tight : ∃ (r : Run 2) (p : Proc 2) (t₀ t₂ : ℕ), (r.s t₀).pc p = .e24 ∧
    r.ev t₀ = .step p ∧ (∀ t, t₀ < t → t < t₂ → ((r.s t).pc p).At25) ∧
    r.rmr p (t₀ + 1) t₂ = 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := tightRun_25
  exact ⟨tightRun, 0, 39, 156, h1, h2, fun t ht1 ht2 => h3 t (Finset.mem_Ioo.2 ⟨ht1, ht2⟩), h4⟩

/-- **Statement 27 can cost two RMRs** (the paper: "`p` cannot incur more than a single RMR"): in
its first passage, process `0`'s first read of `signal[0]` is a first read (an RMR by rule (1) of
Section 3), and the second one follows the write `signal[0] ← true` of the process handing over
the lock. -/
theorem stmt27_two : ∃ (r : Run 2) (p : Proc 2) (t₀ t₂ : ℕ),
    (∀ t, t₀ ≤ t → t < t₂ → (r.s t).pc p = .e27) ∧ r.rmr p t₀ t₂ = 2 := by
  obtain ⟨h1, h2⟩ := tightRun_27
  exact ⟨tightRun, 0, 157, 205, fun t ht1 ht2 => h1 t (Finset.mem_Ico.2 ⟨ht1, ht2⟩), h2⟩

/-- Non-vacuity of `lemma10_barriers`: complete passages exist. -/
theorem passage_exists : ∃ (r : Run 2) (p : Proc 2) (t₁ t₂ : ℕ), r.Passage p t₁ t₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := tightRun_passage
  exact ⟨tightRun, 2, 0, 103, by norm_num, h1, h2, h3,
    fun t ht1 ht2 => h4 t (Finset.mem_Ioo.2 ⟨ht1, ht2⟩)⟩

end Podc.ConstantBarriersMutex
