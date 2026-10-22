import Papers.PODC2015.MinimalSynchronyBC.Machine
import Cslib.Computability.Distributed.Byzantine.PartialSync.Sim
import Podc.Computability.Distributed.Byzantine.PartialSync.Timeliness
import Podc.Computability.Distributed.Byzantine.PartialSync.Quiescence

/-!
# Lemma 2, Theorem 3 and the termination part of Theorem 4 are false

A correct process that returns at line 4 of Figure 3 never sets `timer[r]` (line 5), so it
broadcasts `EA_RELAY[r]` only if it receives `EA_COORD[r]` from the coordinator (lines 15–19).
If the coordinator of round `r` is faulty and silent, these processes never relay, and the
processes that did not return at line 4 may wait forever at line 6 for `n − t` relays.

The run (`n = 7`, `t = 2`, so `m = ⌊(n − (t+1))/t⌋ = 2` values are allowed):

* process `0` (the paper's `p₁ = coord(1)`) is faulty and **sends nothing** (it crashed initially);
* processes `1, 2, 3` propose `true`, processes `4, 5, 6` propose `false`;
* the run is **synchronous** (`gst = 0`, every message delivered within `δ = 1` tick), so every
  correct process is an eventual `⟨t+1⟩bisource`;
* `CB[0]` gives `est = true` to `1, 2, 3` and `false` to `4, 5, 6`; `CB[1]` (EA round 1) gives
  `aux = true` to `1, …, 5` and `aux = false` to `6`;
* processes `1, 2` receive `EA_PROP2[1](true)` from `1, …, 5` first and return `true` at line 4;
  processes `3, …, 6` receive the messages of `1, 2, 3, 4, 6` first (mixed values), set their
  timers and, when they expire, relay `⊥`;
* only `4 < n − t = 5` relays are ever sent: processes `3, …, 6` wait at line 6 of round 1
  forever, processes `1, 2` wait forever in the CB of `AC_OBJECT[1]` (two `AC_PROP` messages,
  fewer than `t + 1 = 3`), and nobody decides.

Every "pick any" choice of the algorithm is forced in this run (at every return there is a single
candidate value / exactly `n − t` qualifying messages).
-/

namespace MinimalSynchronyBC

open Cslib.Byzantine.PartialSync

/-- The paper's coordinator `coord(r) = ((r − 1) mod n) + 1`, i.e. index `(r − 1) mod n`. -/
def paperCoord (n : ℕ) [NeZero n] (r : ℕ) : Fin n := ⟨(r - 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- The paper's `F(r) = F_{index(r)}`, `index(r) = ((⌈r/n⌉ − 1) mod α) + 1`, where
`F₁, …, F_α` enumerate the `(n − t)`-subsets of the processes (here in the order of
`List.sublistsLen`). -/
def paperF (n t : ℕ) (r : ℕ) : Finset (Fin n) :=
  let L := List.sublistsLen (n - t) (List.finRange n)
  (L.getD (((r + n - 1) / n - 1) % L.length) []).toFinset

/-- The paper's parameters (timer of round `r` set to `r` ticks). -/
def paperParams (n t : ℕ) [NeZero n] : Params n where
  t := t
  coord := paperCoord n
  F := paperF n t

namespace Blocking

/-- `n = 7`, `t = 2`. -/
abbrev prm : Params 7 := paperParams 7 2

local notation "A" => alg (V := Bool) prm

/-- Proposals: `1, 2, 3` propose `true`, `4, 5, 6` propose `false`. -/
def inp (p : Fin 7) : Bool := decide (p.val ≤ 3)

/-- Delivery times (all delays `≤ 1`). -/
def delay (q : Fin 7) (τ : ℕ) (p : Fin 7) : ℕ :=
  if τ = 0 then
    (if (4 ≤ q.val ∧ 1 ≤ p.val ∧ p.val ≤ 3) ∨ (1 ≤ q.val ∧ q.val ≤ 3 ∧ 4 ≤ p.val) then 1 else 0)
  else if τ = 1 then
    (if (4 ≤ q.val ∧ 1 ≤ p.val ∧ p.val ≤ 5) ∨ (1 ≤ q.val ∧ q.val ≤ 3 ∧ p.val = 6) then 2 else 1)
  else if τ = 2 then
    (if (q.val = 6 ∧ 1 ≤ p.val ∧ p.val ≤ 2) ∨ (q.val = 5 ∧ 3 ≤ p.val) then 3 else 2)
  else τ

/-- The run: process `0` faulty and silent, synchronous (`gst = 0`). -/
def R : Run (Fin 7) (Msg Bool) Bool where
  faulty := {0}
  inp := inp
  gst := 0
  byz _ _ _ := []
  dl := delay

theorem R_syncValid : R.SyncValid prm.t 1 := by
  refine ⟨⟨by decide, fun q τ p _ _ => ?_, fun q τ p _ _ => ?_⟩, rfl⟩ <;>
  · simp only [R, delay]; split_ifs <;> omega

def bad (q : Fin 7) : Bool := q.val = 0

theorem bad_iff (q : Fin 7) : bad q = true ↔ q ∈ R.faulty := by
  revert q; decide

theorem bad_false {p : Fin 7} (hp : p ∉ R.faulty) : bad p = false := by
  cases h : bad p
  · rfl
  · exact absurd ((bad_iff p).1 h) hp

/-- Dummy state. -/
def d0 : St 7 Bool := init prm true

/-- The memoised history up to time 6. -/
def H : List (List (St 7 Bool)) := simHist A R.inp bad R.byz R.dl d0 6

theorem st_eq (τ : ℕ) (hτ : τ ≤ 6) (p : Fin 7) : R.st A τ p = (H.getD τ []).getD p d0 := by
  rw [Run.st_eq_simHist _ R bad_iff d0 τ p, H, simHist_getD_of_le _ _ _ _ _ _ hτ]

/-- **Checked by evaluation.** At time 6 every correct process is at a fixed point of its step on
an empty inbox and sends nothing; processes `1, 2` returned `true` from the EA object in round 1
and wait in the CB of `AC_OBJECT[1]`, processes `3, …, 6` wait at line 6 of round 1. Moreover, at
every time `≤ 6` nobody has decided and processes `3, …, 6` have not returned from the EA object;
at time 1 every correct process has started round 1 (`EA_propose(1, est)`). -/
theorem facts : ∀ p : Fin 7, bad p = false →
    step prm p ((H.getD 6 []).getD p d0) (fun _ => []) = (H.getD 6 []).getD p d0 ∧
    ((H.getD 6 []).getD p d0).out = [] ∧
    ((H.getD 6 []).getD p d0).pc = (if p.val ≤ 2 then .acCB 1 else .eaW6 1) ∧
    ((H.getD 1 []).getD p d0).pc = .eaCB 1 ∧
    (∀ τ ≤ 6, ((H.getD τ []).getD p d0).dec = none) ∧
    (∀ τ ≤ 6, 3 ≤ p.val → ((H.getD τ []).getD p d0).eaRet = []) := by
  decide +kernel

theorem dl_ne (q : Fin 7) (τ' : ℕ) (p : Fin 7) (τ : ℕ) (h1 : τ' < 6) (h2 : 6 ≤ τ) :
    R.dl q τ' p ≠ τ := by
  simp only [R, delay]; split_ifs <;> omega

/-- From time 6 on the states of correct processes never change. -/
theorem st_stuck (k : ℕ) (p : Fin 7) (hp : p ∉ R.faulty) : R.st A (6 + k) p = R.st A 6 p :=
  Run.st_eq_of_quiescent A R 6
    (fun p hp => by rw [st_eq 6 le_rfl]; exact (facts p (bad_false hp)).1)
    (fun p hp _ => by rw [st_eq 6 le_rfl]; exact (facts p (bad_false hp)).2.1)
    dl_ne (fun _ _ _ _ _ => rfl) k p hp

theorem dec_none (τ : ℕ) (p : Fin 7) (hp : p ∉ R.faulty) : (R.st A τ p).dec = none := by
  rcases le_total τ 6 with h | h
  · rw [st_eq τ h]; exact (facts p (bad_false hp)).2.2.2.2.1 τ h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [st_stuck k p hp, st_eq 6 le_rfl]; exact (facts p (bad_false hp)).2.2.2.2.1 6 le_rfl

theorem eaRet_nil (τ : ℕ) (p : Fin 7) (hp : p ∉ R.faulty) (h3 : 3 ≤ p.val) :
    (R.st A τ p).eaRet = [] := by
  rcases le_total τ 6 with h | h
  · rw [st_eq τ h]; exact (facts p (bad_false hp)).2.2.2.2.2 τ h h3
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [st_stuck k p hp, st_eq 6 le_rfl]; exact (facts p (bad_false hp)).2.2.2.2.2 6 le_rfl h3

end Blocking

open Blocking in
/-- **Lemma 2 (EA-Termination) is false**, hence Figure 3 does not implement an EA object
(**Theorem 3 is false**): in a synchronous run of Figure 4 with `n = 7`, `t = 2`, one faulty
process that sends nothing, and correct proposals from `m = 2` values, every correct process
invokes `EA_propose(1, -)` (at time 1), but four of them never return from it. -/
theorem lemma2_false :
    ∃ R : Run (Fin 7) (Msg Bool) Bool, R.SyncValid 2 1 ∧ R.faulty.card = 1 ∧ R.Canonical ∧
      (∀ p ∉ R.faulty, (R.st (alg (paperParams 7 2)) 1 p).pc = .eaCB 1) ∧
      ∃ p ∉ R.faulty, ∀ τ v, ¬ EAReturns (paperParams 7 2) R p 1 v τ := by
  refine ⟨R, R_syncValid, rfl, fun _ _ _ _ => rfl, fun p hp => ?_, 3, by decide,
    fun τ v h => ?_⟩
  · rw [st_eq 1 (by omega)]; exact (facts p (bad_false hp)).2.2.2.1
  · have := eaRet_nil τ 3 (by decide) (by decide)
    simp only [EAReturns] at h
    rw [this] at h
    simp at h

open Blocking in
/-- **The termination part of Theorem 4 is false**: there is a run with `n = 7 > 3t`, `t = 2`, in
which the correct processes propose at most `m = ⌊(n − (t+1))/t⌋ = 2` different values, which is
synchronous (`gst = 0`, delays `≤ 1`; in particular every correct process is an eventual
`⟨t+1⟩bisource`, `Run.SyncValid.bisourceValid`), where the only faulty process crashes
initially (sends nothing), and in which **no correct process ever decides**. -/
theorem theorem4_termination_false :
    ∃ R : Run (Fin 7) (Msg Bool) Bool, R.SyncValid 2 1 ∧ R.BisourceValid 2 3 ∧
      R.faulty.card = 1 ∧ R.Canonical ∧ (7 - (2 + 1)) / 2 = 2 ∧
      ∀ p ∉ R.faulty, ∀ v, ¬ R.Decides (alg (paperParams 7 2)) p v := by
  refine ⟨R, R_syncValid, R_syncValid.bisourceValid (ℓ := 1) (by decide) (by omega) (by decide),
    rfl, fun _ _ _ _ => rfl, rfl, fun p hp v ⟨τ, hτ⟩ => ?_⟩
  have := dec_none τ p hp
  change (R.st (alg (V := Bool) prm) τ p).dec = some v at hτ
  rw [this] at hτ
  simp at hτ

/-! ### Lemma 3: the "good" round of the proof need not be good

The proof of Lemma 3 picks a round `r > 2δ` coordinated by the bisource `p_ℓ` with
`F(r) ⊆ C` (and `X⁺ ⊆ F(r)`), and concludes that every correct process returns the coordinator's
value `w` "after executing lines 7–10". It forgets the processes that return at **line 4**.
Here `n = 4`, `t = 1`, process `3` is Byzantine, and round `r = 15` has `coord(15) = 2`,
`F(15) = {0, 1, 2}` = the correct processes; the run is synchronous (`δ = 1`), so `2` is a
`⟨t+1⟩bisource` with `X⁻ = X⁺ = {0, 1, 2} ⊆ F(15)`. Processes `0, 1` ea-propose `true`, `2`
proposes `false`; the Byzantine process RB-broadcasts `EA_PROP1(false)` (consistently, to all) and
sends `EA_PROP2[15](true)`. Process `0` sees three `true` messages and returns `true` at line 4;
the coordinator champions its own `false`, which processes `1, 2` return. -/

namespace GoodRound

/-- The EA object alone, round 15, `n = 4`, `t = 1`, the paper's coordinators and sets `F(r)`. -/
abbrev prm : Params 4 := { paperParams 4 1 with eaRound := some 15 }

local notation "A" => alg (V := Bool) prm

/-- The Byzantine process `3`: RB-broadcasts `EA_PROP1(false)` at time 0, sends
`EA_PROP2[15](true)` at time 1. -/
def byz (_ : Fin 4) (τ : ℕ) (_ : Fin 4) : List (Msg Bool) :=
  if τ = 0 then [.rb (.eaProp1 15) false] else if τ = 1 then [.prop2 15 true] else []

/-- Delivery times (delays `≤ 1`). -/
def delay (q : Fin 4) (τ : ℕ) (p : Fin 4) : ℕ :=
  if τ = 0 then
    (if (2 ≤ q.val ∧ p.val ≤ 1) ∨ (q.val ≤ 1 ∧ p.val = 2) then 1 else 0)
  else if τ = 1 then
    (if (q.val = 2 ∧ p.val = 0) ∨ (q.val ≤ 1 ∧ p.val = 2) ∨ (q.val = 3 ∧ 1 ≤ p.val) then 2 else 1)
  else τ

def R : Run (Fin 4) (Msg Bool) Bool where
  faulty := {3}
  inp p := decide (p.val ≤ 1)
  gst := 0
  byz := byz
  dl := delay

theorem R_syncValid : R.SyncValid 1 1 := by
  refine ⟨⟨by decide, fun q τ p _ _ => ?_, fun q τ p _ _ => ?_⟩, rfl⟩ <;>
  · simp only [R, delay]; split_ifs <;> omega

theorem rb_mem {q : Fin 4} {τ : ℕ} {p : Fin 4} {k : Key} {v : Bool}
    (h : Msg.rb k v ∈ R.byz q τ p) : τ = 0 ∧ k = .eaProp1 15 ∧ v = false := by
  simp only [R, byz] at h
  split_ifs at h with h0 h1 <;> simp_all

theorem R_rbAdmissible : RBAdmissible R := by
  intro q _ k v τ p _ h
  obtain ⟨rfl, rfl, rfl⟩ := rb_mem h
  refine ⟨fun τ' p' v' _ h' => (rb_mem h').2.2, fun p' _ => ⟨by simp [R, byz], Nat.zero_le _⟩⟩

def bad (q : Fin 4) : Bool := q.val = 3

theorem bad_iff (q : Fin 4) : bad q = true ↔ q ∈ R.faulty := by
  revert q; decide

theorem bad_false {p : Fin 4} (hp : p ∉ R.faulty) : bad p = false := by
  cases h : bad p
  · rfl
  · exact absurd ((bad_iff p).1 h) hp

def d0 : St 4 Bool := init prm true

def H : List (List (St 4 Bool)) := simHist A R.inp bad R.byz R.dl d0 4

theorem st_eq (τ : ℕ) (hτ : τ ≤ 4) (p : Fin 4) : R.st A τ p = (H.getD τ []).getD p d0 := by
  rw [Run.st_eq_simHist _ R bad_iff d0 τ p, H, simHist_getD_of_le _ _ _ _ _ _ hτ]

/-- **Checked by evaluation.** At time 4, process `0` has returned `true` and processes `1, 2`
have returned `false` from `EA_propose(15, -)`. -/
theorem facts : ((H.getD 4 []).getD 0 d0).eaRet = [(15, true)] ∧
    ((H.getD 4 []).getD 1 d0).eaRet = [(15, false)] ∧
    ((H.getD 4 []).getD 2 d0).eaRet = [(15, false)] := by
  decide +kernel

end GoodRound

open GoodRound in
/-- **The proof of Lemma 3 is wrong.** In a synchronous run (`n = 4`, `t = 1`, `δ = 1`, faulty
reliable broadcasts consistent) of the EA object, round `r = 15 > 2δ` is coordinated by the
correct process `2`, a `⟨t+1⟩bisource` with `X⁻ = X⁺ ⊆ F(15) = ` the correct processes — a round
of the kind chosen in the proof — yet correct processes return different values from
`EA_propose(15, -)`: process `0` returns `true` (line 4), process `1` returns `false`
(line 8). (This refutes the proof, not the statement of Lemma 3, which needs infinitely many
rounds.) -/
theorem lemma3_proof_fails :
    ∃ R : Run (Fin 4) (Msg Bool) Bool, R.SyncValid 1 1 ∧ RBAdmissible R ∧
      paperCoord 4 15 ∉ R.faulty ∧ R.IsBisource 2 (paperCoord 4 15) ∧
      paperF 4 1 15 = Finset.univ \ R.faulty ∧ 2 * 1 < 15 ∧
      EAReturns prm R 0 15 true 4 ∧ EAReturns prm R 1 15 false 4 := by
  refine ⟨R, R_syncValid, R_rbAdmissible, by decide,
    R_syncValid.isBisource (by decide) (by omega) (by decide), by decide, by omega, ?_, ?_⟩
  · unfold EAReturns; rw [st_eq 4 le_rfl 0]
    show (15, true) ∈ ((H.getD 4 []).getD 0 d0).eaRet
    rw [facts.1]; simp
  · unfold EAReturns; rw [st_eq 4 le_rfl 1]
    show (15, false) ∈ ((H.getD 4 []).getD 1 d0).eaRet
    rw [facts.2.1]; simp

end MinimalSynchronyBC
