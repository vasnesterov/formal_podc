import Papers.PODC2026.ForgetIT.Protocol

/-!
# Robust good-case latency is not `3δ` (Theorem 3, first item)

The paper defines (Section 3) the *robust good-case latency* `T_rgc` as the worst-case decision
latency, measured from GST, over all executions in which **GST coincides with a correct leader
entering its view**, and claims `T_rgc = 3δ` for Forget-IT (Theorem 1, Theorem 3).

We exhibit such an execution in which the correct processes decide only `14` ticks after GST,
where one message delay after GST is one tick (`δ = 1` in the paper's time) and `Δ = 2` ticks.

Setting: `n = 4`, `f = 1`, processes `0, 1, 2, 3`, round-robin leaders `leader(V) = V - 1 mod 4`;
process `0` (leader of view 1) is Byzantine, process `1` (leader of view 2) is correct.

1. Before GST every message to process `1` from another process is delayed until GST. Process
   `0` never sends a `prepare`; it sends `echo-1/2/3` for view 1 with value `SAFE` to processes
   `2` and `3` (and nothing else, ever).
2. Processes `1, 2, 3` time out in view 1 and broadcast `vote-2`; processes `2`, `3` complete the
   view change of view 1 with the Byzantine echoes and enter view 2 (tick 11).
3. In view 2 the leader `1` is absent, so processes `2` and `3` time out: at tick `19` they have
   started the view change of view 2 (`vc[2] = true`), after which they never send `vote-1` in
   view 2 (line 37).
4. At GST = 21 process `1` receives the delayed messages, among them `f + 1` `echo-3` messages
   for view 1, and enters view 2 (line 80) — GST coincides with a correct leader entering its
   view. Its proposal cannot gather `2f + 1` `vote-1` messages, so view 2 decides nothing; the
   view change of view 2 waits for process `1`'s own timeout, and the processes decide only in
   view 3, at tick 35 = GST + 14.

The run is a valid run of CSLib's partially synchronous model (`Run.Valid 1 0`: correct-to-correct
messages are delivered by `max(τ, GST)`, i.e. one tick per hop in the paper's time, since a
message produced in the step at `τ` is sent at `τ + 1`). All facts are checked by evaluating the
run with `decide +kernel` through CSLib's memoised simulator. Processes start at time 0 and
clocks do not drift, so the run is also an execution of the paper's model.
-/

namespace Podc.ForgetIT.RobustLatency

open Cslib.Byzantine.PartialSync

/-- `n = 4`, `f = 1`, `leader(V) = V − 1 mod 4`, `Δ = 2` ticks. -/
def prm : Params (Fin 4) := { f := 1, leader := fun V => ⟨(V + 3) % 4, by omega⟩, Δ := 2 }

/-- The algorithm (1 rule pass per tick). -/
abbrev A := forgetIT (Val := Bool) prm 1

/-- Global stabilization time. -/
def gst : ℕ := 21

/-- The Byzantine process `0` sends `SAFE` echoes for view 1 to processes `2` and `3` at time 0,
and nothing else. -/
def byz : Fin 4 → ℕ → Fin 4 → List (Msg Bool) := fun q τ p =>
  if q = 0 ∧ τ = 0 ∧ (p = 2 ∨ p = 3) then [.echo 0 1 .safe, .echo 1 1 .safe, .echo 2 1 .safe]
  else []

/-- Messages from other processes to process `1` sent before GST arrive at GST; all other
messages arrive immediately. -/
def dl : Fin 4 → ℕ → Fin 4 → ℕ := fun q τ p => if p = 1 ∧ q ≠ 1 ∧ τ < gst then gst else τ

/-- The run: process `0` is Byzantine, all proposals are `true`. -/
def R : Run (Fin 4) (Msg Bool) Bool where
  faulty := {0}
  inp := fun _ => true
  gst := gst
  byz := byz
  dl := dl

theorem R_valid : R.Valid 1 0 where
  card_faulty := by decide
  dl_ge := by intro q τ p _ _; simp only [R, dl]; split_ifs <;> omega
  dl_le := by intro q τ p _ _; simp only [R, dl]; split_ifs <;> omega

/-- Process `1` is correct and is the leader of view 2. -/
theorem leader_correct : prm.leader 2 = 1 ∧ (1 : Fin 4) ∉ R.faulty := by decide

def bad : Fin 4 → Bool := fun q => q = 0

lemma bad_iff (q : Fin 4) : bad q = true ↔ q ∈ R.faulty := by
  fin_cases q <;> decide

def d0 : LS (Fin 4) Bool := startLS true

/-- The simulated history up to time 36. -/
def H : List (List (LS (Fin 4) Bool)) := simHist A R.inp bad R.byz R.dl d0 36

lemma st_eq (τ : ℕ) (hτ : τ ≤ 36) (p : Fin 4) : R.st A τ p = (H.getD τ []).getD p d0 := by
  rw [Run.st_eq_simHist A R bad_iff d0 τ p, H, simHist_getD_of_le _ _ _ _ _ _ hτ]

set_option maxRecDepth 100000 in
/-- All facts about the run, checked by evaluation. -/
lemma facts :
    ((H.getD 21 []).getD 1 d0).view = 1 ∧ ((H.getD 22 []).getD 1 d0).view = 2 ∧
    ((H.getD 22 []).getD 1 d0).active = true ∧
    ((H.getD 21 []).getD 2 d0).vc 2 = true ∧ ((H.getD 21 []).getD 3 d0).vc 2 = true ∧
    ((List.range 35).all fun τ => ([1, 2, 3] : List (Fin 4)).all fun p =>
      ((H.getD τ []).getD p d0).decided.isNone) = true ∧
    (([1, 2, 3] : List (Fin 4)).all fun p => ((H.getD 36 []).getD p d0).decided = some (3, true))
      = true := by
  decide +kernel

/-- In the run, the correct leader `1` of view 2 actively enters view 2 in the step at GST. -/
theorem enters_at_gst : (R.st A gst 1).view = 1 ∧ (R.st A (gst + 1) 1).view = 2 ∧
    (R.st A (gst + 1) 1).active = true := by
  rw [st_eq _ (by decide), st_eq _ (by decide)]
  exact ⟨facts.1, facts.2.1, facts.2.2.1⟩

/-- When process `1` enters view 2, processes `2` and `3` have already started the view change
of view 2. -/
theorem others_timed_out : (R.st A gst 2).vc 2 = true ∧ (R.st A gst 3).vc 2 = true := by
  rw [st_eq _ (by decide), st_eq _ (by decide)]
  exact ⟨facts.2.2.2.1, facts.2.2.2.2.1⟩

lemma correct_mem (p : Fin 4) (hp : p ∉ R.faulty) : p ∈ ([1, 2, 3] : List (Fin 4)) := by
  fin_cases p <;> simp_all [R]

/-- **No correct process decides before time `GST + 14`**, although the correct leader of view 2
entered its view at GST: the robust good-case latency of Forget-IT is not `3δ`. -/
theorem no_decision_before (p : Fin 4) (hp : p ∉ R.faulty) (τ : ℕ) (hτ : τ < gst + 14) :
    A.decide p (R.st A τ p) = none := by
  have h := facts.2.2.2.2.2.1
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h τ (by simpa [gst] using hτ) p (correct_mem p hp)
  rw [st_eq τ (by simp [gst] at hτ; omega)]
  simpa [A, forgetIT] using h'

/-- Sanity check: the correct processes do decide `true`, at time `GST + 15` (in view 3). -/
theorem decides_later (p : Fin 4) (hp : p ∉ R.faulty) :
    A.decide p (R.st A (gst + 15) p) = some true := by
  have h := facts.2.2.2.2.2.2
  simp only [List.all_eq_true] at h
  have h' := h p (correct_mem p hp)
  simp only [decide_eq_true_eq] at h'
  rw [st_eq _ (by decide)]
  show Option.map Prod.snd ((H.getD 36 []).getD p d0).decided = some true
  rw [h']; rfl

end Podc.ForgetIT.RobustLatency

namespace Podc.ForgetIT.RobustLatency

open Cslib.Byzantine.PartialSync

/-- **Theorem 3 (robust good-case latency `3δ`) fails.** A valid run (`n = 4`, `f = 1`, `Δ = 2`
ticks, one message delay after GST = one tick) in which GST is the time at which the correct
leader of view 2 actively enters view 2, but no correct process decides before `GST + 14`. -/
theorem robust_latency_counterexample :
    R.Valid prm.f 0 ∧ prm.leader 2 ∉ R.faulty ∧
      (R.st A R.gst (prm.leader 2)).view = 1 ∧ (R.st A (R.gst + 1) (prm.leader 2)).view = 2 ∧
      (R.st A (R.gst + 1) (prm.leader 2)).active = true ∧
      ∀ p ∉ R.faulty, ∀ τ < R.gst + 14, A.decide p (R.st A τ p) = none := by
  obtain ⟨h1, h2⟩ := leader_correct
  rw [h1]
  exact ⟨R_valid, h2, enters_at_gst.1, enters_at_gst.2.1, enters_at_gst.2.2,
    fun p hp τ hτ => no_decision_before p hp τ hτ⟩

end Podc.ForgetIT.RobustLatency
