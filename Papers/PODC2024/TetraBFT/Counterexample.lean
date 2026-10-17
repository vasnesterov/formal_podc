import Papers.PODC2024.TetraBFT.Refinement
import Podc.PartialSync.Sim

/-!
# Termination fails: a view-synchronization deadlock (counterexample to Theorem 1, termination)

The view-change rule of Section 3.2 is: on a timeout, broadcast a view-change message for the next
view; on `f + 1` view-change messages for a view `v'`, send a view-change message for `v'` *if no
view-change message for `v'` or any higher view was sent*; on `n − f` view-change messages for a
view, move to that view. Nothing is ever retransmitted, and the timer fires once per view.

With `n = 7`, `f = 2` (nodes `0, 1` Byzantine; leaders round-robin, so views `0, 1` have
Byzantine leaders) there is a run of the partially synchronous model with **reliable** channels
(every message between correct nodes is delivered by `max(send time, GST) + Δ`; CSLib's
`Run.Valid`), `GST = 30`, `Δ = 1`, timeout `9Δ`, in which, from time 41 on:

* nodes `2, 3, 4` are in view 1, have sent view-change messages for views 1 and 2, and see only
  4 (< n − f = 5) view-change messages for view 2 and 2 (< f + 1 = 3) for view 3;
* nodes `5, 6` are in view 2 and have sent view-change messages for view 3, which only 2 correct
  nodes ever send; node 6 entered view 2 without ever sending a view-change message for view 2,
  because it had echoed the view-3 message of node 5 (supported by the two Byzantine nodes)
  first, and the echo rule forbids echoing a *lower* view afterwards;
* no timer will ever fire again and no message is in transit: the system is stuck forever and no
  correct node ever decides (`termination_fails`).

The schedule: all correct nodes time out in view 0 at time 9; nodes 2–5 enter view 1 at once,
node 6 receives their messages only at time 31. Nodes 2–5 time out in view 1 at time 19; node 5
enters view 2 thanks to one Byzantine view-2 message. Node 5 times out at time 29; its view-3
message, together with two Byzantine ones, reaches node 6, which echoes view 3; at time 30 node 6
receives the delayed view-2 messages of nodes 2–5 plus a Byzantine one and enters view 2.

The same pattern works for every `f ≥ 2` with `n = 3f + 1` (informal; see the README). With
message loss before GST, which the paper's model explicitly allows, already `n = 4`, `f = 1`
deadlocks (`termination_fails_lossy`).
-/

namespace TetraBFT

open Finset Cslib.Byzantine.PartialSync

section Quiet

variable {n : ℕ} {V : Type} [DecidableEq V] (prm : Params n)

/-- A node state in which nothing can happen without new messages. -/
def Quiet (p : Fin n) (s : St n V) : Prop :=
  maxVC s.rcv (prm.f + 1) s.vcSent = none ∧ maxVC s.rcv (n - prm.f) s.view = none ∧
  prm.timeout ≤ s.clock ∧ p ≠ prm.leader s.view ∧
  firstFrom s.rcv (prm.leader s.view) (getProposal s.view) = none ∧
  quorumVal prm.f s.rcv 1 s.view = none ∧ quorumVal prm.f s.rcv 2 s.view = none ∧
  quorumVal prm.f s.rcv 3 s.view = none ∧ quorumVal prm.f s.rcv 4 s.view = none

instance (p : Fin n) (s : St n V) : Decidable (Quiet prm p s) := by
  unfold Quiet; infer_instance

/-- Advance the timer by `k` ticks. -/
def St.shift (s : St n V) (k : ℕ) : St n V := { s with clock := s.clock + k }

theorem step_quiet (hfix : prm.fixEcho = false) {p : Fin n} {s : St n V} (h : Quiet prm p s)
    (hout : s.out = []) :
    step prm p s (fun _ => []) = s.shift 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hrecv : recvSt s (fun _ : Fin n => ([] : List (Msg V))) = s := by
    cases s; simp_all [recvSt]
  have hecho : echoSt prm s = s := by simp [echoSt, hfix, h1]
  have hview : viewSt prm s = s.shift 1 := by
    simp only [viewSt, h2, show s.clock + 1 ≠ prm.timeout by omega, ite_false]; rfl
  have hprop : proposeSt prm p (s.shift 1) = s.shift 1 := by
    simp [proposeSt, St.shift, h4]
  have hv1 : vote1St prm (s.shift 1) = s.shift 1 := by
    simp only [vote1St, St.shift, h5]; split <;> rfl
  have hvk : ∀ k, quorumVal prm.f s.rcv (k - 1) s.view = none →
      voteKSt prm k (s.shift 1) = s.shift 1 := by
    intro k hk
    simp only [voteKSt, St.shift, hk]; split <;> rfl
  have hdec : decideSt prm (s.shift 1) = s.shift 1 := by
    simp only [decideSt, St.shift, h9]; split <;> rfl
  simp only [step, hrecv, hecho, hview, hprop, hv1, hvk 2 h6, hvk 3 h7, hvk 4 h8, hdec]

theorem Quiet.shift {p : Fin n} {s : St n V} (h : Quiet prm p s) (k : ℕ) :
    Quiet prm p (s.shift k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, by simp [St.shift]; omega, h4, h5, h6, h7, h8, h9⟩

omit [DecidableEq V] in
theorem St.shift_add (s : St n V) (k l : ℕ) : (s.shift k).shift l = s.shift (k + l) := by
  simp [St.shift, Nat.add_assoc]

omit [DecidableEq V] in
theorem St.shift_zero (s : St n V) : s.shift 0 = s := by
  cases s; rfl

variable {prm} (R : Run (Fin n) (Msg V) V) (T : ℕ)

/-- **Quiescence.** If from time `T` on no message sent before `T` is delivered, faulty nodes are
silent, and every correct node is quiet with an empty outbox at time `T`, then the correct nodes
only count ticks forever. -/
theorem st_tail_of_quiet (hfix : prm.fixEcho = false) (hdl : ∀ q τ' p τ, T ≤ τ → R.dl q τ' p = τ → τ' = τ)
    (hbyz : ∀ q ∈ R.faulty, ∀ τ p, T ≤ τ → R.byz q τ p = [])
    (hq : ∀ p ∉ R.faulty, Quiet prm p (R.st (tetra prm) T p) ∧ (R.st (tetra prm) T p).out = [])
    (k : ℕ) : ∀ p ∉ R.faulty, R.st (tetra prm) (T + k) p = (R.st (tetra prm) T p).shift k := by
  induction k with
  | zero => intro p _; rw [St.shift_zero]; rfl
  | succ k ih =>
    intro p hp
    have hib : R.inbox (tetra prm) p (T + k) = fun _ => [] := by
      funext q
      rw [Run.inbox_eq_flatMap, List.flatMap_eq_nil_iff]
      intro τ' _
      simp only [Run.dlv]
      split_ifs with hd
      · have hτ' := hdl q τ' p (T + k) (by omega) hd
        subst hτ'
        by_cases hqF : q ∈ R.faulty
        · rw [Run.out_of_faulty _ _ hqF]; exact hbyz q hqF _ p (by omega)
        · rw [Run.out_of_correct _ _ hqF, ih q hqF]
          simpa [tetra, St.shift] using (hq q hqF).2
      · rfl
    rw [show T + (k + 1) = (T + k) + 1 by omega, st_succ', hib, ih p hp]
    rw [step_quiet prm hfix (((hq p hp).1).shift prm k) (by simpa [St.shift] using (hq p hp).2),
      St.shift_add]

/-- Under the quiescence hypotheses, a correct node that has not decided by time `T` never
decides. -/
theorem no_decision_of_quiet (hfix : prm.fixEcho = false) (hdl : ∀ q τ' p τ, T ≤ τ → R.dl q τ' p = τ → τ' = τ)
    (hbyz : ∀ q ∈ R.faulty, ∀ τ p, T ≤ τ → R.byz q τ p = [])
    (hq : ∀ p ∉ R.faulty, Quiet prm p (R.st (tetra prm) T p) ∧ (R.st (tetra prm) T p).out = [])
    (hdec : ∀ p ∉ R.faulty, (R.st (tetra prm) T p).dec = none) :
    ∀ p ∉ R.faulty, ∀ v, ¬ R.Decides (tetra prm) p v := by
  intro p hp v ⟨τ, hτ⟩
  change Option.map Prod.fst (R.st (tetra prm) τ p).dec = some v at hτ
  rw [Option.map_eq_some_iff] at hτ
  obtain ⟨d, hd, -⟩ := hτ
  rcases le_total τ T with hle | hle
  · have := st_dec_mono (prm := prm) R hle p hd
    rw [hdec p hp] at this; simp at this
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [st_tail_of_quiet R T hfix hdl hbyz hq k p hp] at hd
    simp [St.shift, hdec p hp] at hd

end Quiet

namespace Deadlock

/-- `n = 7`, `f = 2`, round-robin leaders, timeout `9Δ` with `Δ = 1`. -/
def prm : Params 7 where
  f := 2
  leader v := ⟨v % 7, Nat.mod_lt _ (by omega)⟩
  timeout := 9

/-- The Byzantine nodes `0, 1` only send a few view-change messages to nodes 5 and 6. -/
def byzMsgs (q : Fin 7) (τ : ℕ) (p : Fin 7) : List (Msg Bool) :=
  if q = 0 ∧ τ = 19 ∧ p = 5 then [.viewChange 2]
  else if q = 0 ∧ τ = 29 ∧ p = 6 then [.viewChange 3]
  else if q = 0 ∧ τ = 30 ∧ p = 6 then [.viewChange 2]
  else if q = 1 ∧ τ = 29 ∧ p = 6 then [.viewChange 3]
  else []

/-- Messages from nodes 2–5 to node 6 sent before time 29 are delayed (until GST + Δ = 31; the
view-2 messages of time 19 until 30); all other messages are delivered immediately. -/
def delay (q : Fin 7) (τ : ℕ) (p : Fin 7) : ℕ :=
  if p = 6 ∧ 2 ≤ q.val ∧ q.val ≤ 5 then (if τ = 19 then 30 else if τ < 29 then 31 else τ) else τ

/-- The run: nodes `0, 1` Byzantine, all inputs `true`, `GST = 30`. -/
def R : Run (Fin 7) (Msg Bool) Bool where
  faulty := {0, 1}
  inp _ := true
  gst := 30
  byz := byzMsgs
  dl := delay

theorem R_valid : R.Valid prm.f 1 where
  card_faulty := by decide
  dl_ge q τ p _ _ := by simp only [R, delay]; split_ifs <;> omega
  dl_le q τ p _ _ := by simp only [R, delay]; split_ifs <;> omega

def bad (q : Fin 7) : Bool := q.val < 2

theorem bad_iff (q : Fin 7) : bad q = true ↔ q ∈ R.faulty := by
  revert q; decide

/-- Dummy state. -/
def d0 : St 7 Bool := { inp := true }

/-- The memoised history up to time 41. -/
noncomputable def H : List (List (St 7 Bool)) := simHist (tetra prm) R.inp bad R.byz R.dl d0 41

/-- **Checked by evaluation:** at time 41 every correct node is quiet, has an empty outbox and
has not decided; nodes 2, 3, 4 are in view 1 and nodes 5, 6 in view 2. -/
theorem facts41 : ∀ p : Fin 7, bad p = false →
    Quiet prm p ((H.getD 41 []).getD p d0) ∧ ((H.getD 41 []).getD p d0).out = [] ∧
    ((H.getD 41 []).getD p d0).dec = none ∧
    ((H.getD 41 []).getD p d0).view = (if p.val ≤ 4 then 1 else 2) := by
  decide +kernel

local notation "A" => tetra (V := Bool) prm

theorem st41 (p : Fin 7) : R.st A 41 p = (H.getD 41 []).getD p d0 :=
  Run.st_eq_simHist _ R bad_iff d0 41 p

theorem delay_eq (q : Fin 7) (τ' : ℕ) (p : Fin 7) (τ : ℕ) (hτ : 41 ≤ τ) (h : R.dl q τ' p = τ) : τ' = τ := by
  simp only [R, delay] at h; split_ifs at h <;> (try omega)

theorem byz_nil (q : Fin 7) (_ : q ∈ R.faulty) (τ : ℕ) (p : Fin 7) (hτ : 41 ≤ τ) :
    R.byz q τ p = [] := by
  simp only [R, byzMsgs]; split_ifs <;> (try rfl) <;> (try omega)

theorem bad_false {p : Fin 7} (hp : p ∉ R.faulty) : bad p = false := by
  cases h : bad p
  · rfl
  · exact absurd ((bad_iff p).1 h) hp

/-- In this run no correct node ever decides. -/
theorem no_decision : ∀ p ∉ R.faulty, ∀ v, ¬ R.Decides A p v :=
  no_decision_of_quiet R 41 rfl delay_eq byz_nil
    (fun p hp => by
      have := facts41 p (bad_false hp)
      rw [← st41] at this
      exact ⟨this.1, this.2.1⟩)
    (fun p hp => by
      have := (facts41 p (bad_false hp)).2.2.1
      rwa [← st41] at this)

/-- The views are stuck forever: nodes 2, 3, 4 in view 1 and nodes 5, 6 in view 2. -/
theorem views_stuck (τ : ℕ) (hτ : 41 ≤ τ) (p : Fin 7) (hp : p ∉ R.faulty) :
    (R.st A τ p).view = if p.val ≤ 4 then 1 else 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hτ
  have hq : ∀ p ∉ R.faulty, Quiet prm p (R.st A 41 p) ∧ (R.st A 41 p).out = [] := fun p hp => by
    have := facts41 p (bad_false hp)
    rw [← st41] at this
    exact ⟨this.1, this.2.1⟩
  rw [st_tail_of_quiet R 41 rfl delay_eq byz_nil hq k p hp]
  have := (facts41 p (bad_false hp)).2.2.2
  rw [← st41] at this
  simpa [St.shift] using this

/-- **Termination fails** (Theorem 1): there is a valid run (`n = 7 > 3f`, `f = 2`, reliable
channels, GST = 30, Δ = 1) in which no correct node ever decides. -/
theorem termination_fails : ∃ R : Run (Fin 7) (Msg Bool) Bool, R.Valid prm.f 1 ∧
    ∀ p ∉ R.faulty, ∀ v, ¬ R.Decides (tetra prm) p v :=
  ⟨R, R_valid, no_decision⟩

/-- Hence single-shot TetraBFT does not solve consensus for `n = 7`, `f = 2`, whatever the
validity property. -/
theorem not_solvesConsensus (val : ValidityProperty (Fin 7) Bool Bool) :
    ¬ SolvesConsensus prm.f 1 (tetra prm) val := by
  intro h
  have h2 : (2 : Fin 7) ∉ R.faulty := by decide
  obtain ⟨v, hv⟩ := h.termination R R_valid 2 h2
  exact no_decision 2 h2 v hv

end Deadlock

/-! ### The same deadlock with timeout 17 = 8δ + 9

The bound under which the *repaired* protocol terminates (`fixed_solvesConsensus`,
`ViewSync.lean`); with the paper's echo rule the same schedule (all times rescaled) deadlocks. -/

namespace Deadlock17

/-- `n = 7`, `f = 2`, round-robin leaders, timeout `17 = 8Δ + 9` with `Δ = 1`. -/
def prm : Params 7 where
  f := 2
  leader v := ⟨v % 7, Nat.mod_lt _ (by omega)⟩
  timeout := 17

/-- The Byzantine nodes `0, 1` only send a few view-change messages to nodes 5 and 6. -/
def byzMsgs (q : Fin 7) (τ : ℕ) (p : Fin 7) : List (Msg Bool) :=
  if q = 0 ∧ τ = 35 ∧ p = 5 then [.viewChange 2]
  else if q = 0 ∧ τ = 53 ∧ p = 6 then [.viewChange 3]
  else if q = 0 ∧ τ = 54 ∧ p = 6 then [.viewChange 2]
  else if q = 1 ∧ τ = 53 ∧ p = 6 then [.viewChange 3]
  else []

/-- Messages from nodes 2–5 to node 6 sent before time 53 are delayed (until GST + Δ = 55; the
view-2 messages of time 35 until 54); all other messages are delivered immediately. -/
def delay (q : Fin 7) (τ : ℕ) (p : Fin 7) : ℕ :=
  if p = 6 ∧ 2 ≤ q.val ∧ q.val ≤ 5 then (if τ = 35 then 54 else if τ < 53 then 55 else τ) else τ

/-- The run: nodes `0, 1` Byzantine, all inputs `true`, `GST = 54`. -/
def R : Run (Fin 7) (Msg Bool) Bool where
  faulty := {0, 1}
  inp _ := true
  gst := 54
  byz := byzMsgs
  dl := delay

theorem R_valid : R.Valid prm.f 1 where
  card_faulty := by decide
  dl_ge q τ p _ _ := by simp only [R, delay]; split_ifs <;> omega
  dl_le q τ p _ _ := by simp only [R, delay]; split_ifs <;> omega

def bad (q : Fin 7) : Bool := q.val < 2

theorem bad_iff (q : Fin 7) : bad q = true ↔ q ∈ R.faulty := by
  revert q; decide

/-- Dummy state. -/
def d0 : St 7 Bool := { inp := true }

/-- The memoised history up to time 75. -/
noncomputable def H : List (List (St 7 Bool)) := simHist (tetra prm) R.inp bad R.byz R.dl d0 75

/-- **Checked by evaluation:** at time 75 every correct node is quiet, has an empty outbox and
has not decided; nodes 2, 3, 4 are in view 1 and nodes 5, 6 in view 2. -/
theorem facts75 : ∀ p : Fin 7, bad p = false →
    Quiet prm p ((H.getD 75 []).getD p d0) ∧ ((H.getD 75 []).getD p d0).out = [] ∧
    ((H.getD 75 []).getD p d0).dec = none ∧
    ((H.getD 75 []).getD p d0).view = (if p.val ≤ 4 then 1 else 2) := by
  decide +kernel

local notation "A" => tetra (V := Bool) prm

theorem st75 (p : Fin 7) : R.st A 75 p = (H.getD 75 []).getD p d0 :=
  Run.st_eq_simHist _ R bad_iff d0 75 p

theorem delay_eq (q : Fin 7) (τ' : ℕ) (p : Fin 7) (τ : ℕ) (hτ : 75 ≤ τ) (h : R.dl q τ' p = τ) : τ' = τ := by
  simp only [R, delay] at h; split_ifs at h <;> (try omega)

theorem byz_nil (q : Fin 7) (_ : q ∈ R.faulty) (τ : ℕ) (p : Fin 7) (hτ : 75 ≤ τ) :
    R.byz q τ p = [] := by
  simp only [R, byzMsgs]; split_ifs <;> (try rfl) <;> (try omega)

theorem bad_false {p : Fin 7} (hp : p ∉ R.faulty) : bad p = false := by
  cases h : bad p
  · rfl
  · exact absurd ((bad_iff p).1 h) hp

/-- In this run no correct node ever decides. -/
theorem no_decision : ∀ p ∉ R.faulty, ∀ v, ¬ R.Decides A p v :=
  no_decision_of_quiet R 75 rfl delay_eq byz_nil
    (fun p hp => by
      have := facts75 p (bad_false hp)
      rw [← st75] at this
      exact ⟨this.1, this.2.1⟩)
    (fun p hp => by
      have := (facts75 p (bad_false hp)).2.2.1
      rwa [← st75] at this)

/-- The views are stuck forever: nodes 2, 3, 4 in view 1 and nodes 5, 6 in view 2. -/
theorem views_stuck (τ : ℕ) (hτ : 75 ≤ τ) (p : Fin 7) (hp : p ∉ R.faulty) :
    (R.st A τ p).view = if p.val ≤ 4 then 1 else 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hτ
  have hq : ∀ p ∉ R.faulty, Quiet prm p (R.st A 75 p) ∧ (R.st A 75 p).out = [] := fun p hp => by
    have := facts75 p (bad_false hp)
    rw [← st75] at this
    exact ⟨this.1, this.2.1⟩
  rw [st_tail_of_quiet R 75 rfl delay_eq byz_nil hq k p hp]
  have := (facts75 p (bad_false hp)).2.2.2
  rw [← st75] at this
  simpa [St.shift] using this

/-- **Termination fails** (Theorem 1): there is a valid run (`n = 7 > 3f`, `f = 2`, reliable
channels, GST = 54, Δ = 1, timeout 17) in which no correct node ever decides. -/
theorem termination_fails : ∃ R : Run (Fin 7) (Msg Bool) Bool, R.Valid prm.f 1 ∧
    ∀ p ∉ R.faulty, ∀ v, ¬ R.Decides (tetra prm) p v :=
  ⟨R, R_valid, no_decision⟩

/-- Hence single-shot TetraBFT does not solve consensus for `n = 7`, `f = 2`, whatever the
validity property. -/
theorem not_solvesConsensus (val : ValidityProperty (Fin 7) Bool Bool) :
    ¬ SolvesConsensus prm.f 1 (tetra prm) val := by
  intro h
  have h2 : (2 : Fin 7) ∉ R.faulty := by decide
  obtain ⟨v, hv⟩ := h.termination R R_valid 2 h2
  exact no_decision 2 h2 v hv

end Deadlock17

/-! ### With message loss before GST (the paper's model), already `n = 4`, `f = 1` deadlocks -/

/-- The network model of Section 2 of the paper: before GST messages may be lost (a batch with
delivery time before its send time is never delivered) or arbitrarily delayed; messages between
correct nodes sent at or after GST are delivered within `δ`. -/
structure LossyValid {P M VI : Type*} (t δ : ℕ) (R : Run P M VI) : Prop where
  card_faulty : R.faulty.card ≤ t
  dl_ge : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → R.gst ≤ τ → τ ≤ R.dl q τ p
  dl_le : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → R.gst ≤ τ → R.dl q τ p ≤ τ + δ

namespace Lossy

/-- `n = 4`, `f = 1`, round-robin leaders, timeout 9. -/
def prm : Params 4 where
  f := 1
  leader v := ⟨v % 4, Nat.mod_lt _ (by omega)⟩
  timeout := 9

/-- Before GST = 12, all messages to nodes 1 and 3 from other nodes are lost. -/
def delay (q : Fin 4) (τ : ℕ) (p : Fin 4) : ℕ :=
  if 1 ≤ τ ∧ τ < 12 ∧ q ≠ p ∧ p ≠ 2 then 0 else τ

/-- Node 0 is Byzantine and silent. -/
def R : Run (Fin 4) (Msg Bool) Bool where
  faulty := {0}
  inp _ := true
  gst := 12
  byz _ _ _ := []
  dl := delay

theorem R_valid : LossyValid prm.f 1 R where
  card_faulty := by decide
  dl_ge q τ p _ _ h := by simp only [R, delay] at h ⊢; split_ifs <;> omega
  dl_le q τ p _ _ h := by simp only [R, delay] at h ⊢; split_ifs <;> omega

def bad (q : Fin 4) : Bool := q.val < 1

theorem bad_iff (q : Fin 4) : bad q = true ↔ q ∈ R.faulty := by
  revert q; decide

def d0 : St 4 Bool := { inp := true }

noncomputable def H : List (List (St 4 Bool)) := simHist (tetra prm) R.inp bad R.byz R.dl d0 21

/-- Checked by evaluation: at time 21 the correct nodes are quiet, undecided, node 2 in view 1
and nodes 1, 3 in view 0. -/
theorem facts21 : ∀ p : Fin 4, bad p = false →
    Quiet prm p ((H.getD 21 []).getD p d0) ∧ ((H.getD 21 []).getD p d0).out = [] ∧
    ((H.getD 21 []).getD p d0).dec = none ∧
    ((H.getD 21 []).getD p d0).view = (if p.val = 2 then 1 else 0) := by
  decide +kernel

theorem st21 (p : Fin 4) : R.st (tetra prm) 21 p = (H.getD 21 []).getD p d0 :=
  Run.st_eq_simHist _ R bad_iff d0 21 p

theorem bad_false {p : Fin 4} (hp : p ∉ R.faulty) : bad p = false := by
  cases h : bad p
  · rfl
  · exact absurd ((bad_iff p).1 h) hp

/-- **Termination fails in the paper's own network model**, for `n = 4`, `f = 1`. -/
theorem termination_fails_lossy : ∃ R : Run (Fin 4) (Msg Bool) Bool, LossyValid prm.f 1 R ∧
    ∀ p ∉ R.faulty, ∀ v, ¬ R.Decides (tetra prm) p v :=
  ⟨R, R_valid, no_decision_of_quiet R 21 rfl
    (fun q τ' p τ hτ h => by simp only [R, delay] at h; split_ifs at h <;> omega)
    (fun _ _ _ _ _ => rfl)
    (fun p hp => by
      have := facts21 p (bad_false hp)
      rw [← st21] at this
      exact ⟨this.1, this.2.1⟩)
    (fun p hp => by
      have := (facts21 p (bad_false hp)).2.2.1
      rwa [← st21] at this)⟩

end Lossy

/-! ### The proof of Lemma 7 claims too much -/

namespace Lemma7

/-- `n = 4`, `f = 1`, round-robin leaders (view 0 is led by the Byzantine node 0). -/
def prm : Params 4 where
  f := 1
  leader v := ⟨v % 4, Nat.mod_lt _ (by omega)⟩
  timeout := 9

/-- The Byzantine leader proposes `true` to nodes 1, 2 and `false` to node 3, and supports
`true` with its own votes. -/
def byzMsgs (q : Fin 4) (τ : ℕ) (p : Fin 4) : List (Msg Bool) :=
  if q = 0 ∧ τ = 1 then
    (if p = 3 then [.proposal 0 false]
     else [.proposal 0 true, .vote 1 0 true, .vote 2 0 true, .vote 3 0 true, .vote 4 0 true])
  else []

/-- Synchronous run (`GST = 0`), all messages delivered immediately. -/
def R : Run (Fin 4) (Msg Bool) Bool where
  faulty := {0}
  inp _ := true
  gst := 0
  byz := byzMsgs
  dl _ τ _ := τ

theorem R_valid : R.Valid prm.f 1 where
  card_faulty := by decide
  dl_ge _ _ _ _ _ := le_rfl
  dl_le _ τ _ _ _ := by simp [R]

def bad (q : Fin 4) : Bool := q.val < 1

theorem bad_iff (q : Fin 4) : bad q = true ↔ q ∈ R.faulty := by
  revert q; decide

def d0 : St 4 Bool := { inp := true }

noncomputable def H : List (List (St 4 Bool)) := simHist (tetra prm) R.inp bad R.byz R.dl d0 8

theorem facts8 : ((H.getD 8 []).getD 1 d0).dec = some (true, 0) ∧
    (⟨1, 0, false⟩ : Vote Bool) ∈ ((H.getD 8 []).getD 3 d0).votes := by
  decide +kernel

/-- In the proof of Lemma 7 the paper claims that if a correct node decides `val` in view `v`,
then "every well-behaved node that sends a vote-1 message [in view `v`] does so with value
`val`". This is false: with a Byzantine leader, correct node 1 decides `true` in view 0 while
correct node 3 sends a vote-1 for `false` in view 0 (synchronous run, `n = 4`, `f = 1`). The
statement of Lemma 7 itself is true (`Execution.lemma7`). -/
theorem lemma7_proof_claim_false : ∃ R : Run (Fin 4) (Msg Bool) Bool, R.Valid prm.f 1 ∧
    (1 : Fin 4) ∉ R.faulty ∧ (3 : Fin 4) ∉ R.faulty ∧
    (∃ τ, (R.st (tetra prm) τ 1).dec = some (true, 0)) ∧
    (∃ τ, (⟨1, 0, false⟩ : Vote Bool) ∈ (R.st (tetra prm) τ 3).votes) := by
  refine ⟨R, R_valid, by decide, by decide, ⟨8, ?_⟩, ⟨8, ?_⟩⟩
  · rw [Run.st_eq_simHist _ R bad_iff d0]; exact facts8.1
  · rw [Run.st_eq_simHist _ R bad_iff d0]; exact facts8.2

end Lemma7

end TetraBFT
