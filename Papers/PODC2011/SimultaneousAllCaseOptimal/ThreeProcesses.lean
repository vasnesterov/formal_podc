import Papers.PODC2011.SimultaneousAllCaseOptimal.Flood
import Papers.PODC2011.SimultaneousAllCaseOptimal.Chain
import Papers.PODC2011.SimultaneousAllCaseOptimal.Lemma5False

/-!
# Theorem 6 and Corollary 9 fail for `n = 3`, `t = 2` (`t = n − 1`)

Consensus with `n = 3` processes, `t = 2` crashes, on a set with two distinct values:
* `2` is a worst-case lower bound (`consensus_lb_two`) and FloodSet solves consensus in `2` rounds
  (`floodSet_solvesWithin`), so the hypotheses of Theorem 6 hold with `k̂ = 2`, `A = floodSet 2`
  (the input set is complete).
* The protocol `loneSurvivor` solves simultaneous consensus and decides at time `1` in the run
  `r⋆` in which two processes crash in round 1 without sending anything: the survivor sees that it
  is alone and decides its own input (`loneSurvivor_solvesSim`, `loneSurvivor_decides`).
* In `r⋆`, `W = 1`, so `min{k̂, t + 1 − W} = 2` (`waste_loneRun`).

Hence no protocol can have both the timing of Theorem 3 (decide at `min{k̂, t + 1 − W(F)}`) and
the all-case optimality of Theorem 6 (`thm3_thm6_incompatible`); in particular, for every protocol
`C` with the ConCon properties of §2.3, `Opt(floodSet 2, 2)` is not all-case optimal
(`theorem6_fails`).

Corollary 9 (with `k = 1`) claims that `Opt(sa, ⌊t/k⌋ + 1) = Opt(sa, 3)` is all-case optimal and
halts at `min{3, 3 − W}`, i.e. at time `3` in failure-free runs; but `floodSet 2` decides at time
`2` in every run (`corollary9_false`). The cited bound `⌊t/k⌋ + 1` of [CHLT00] needs
`n ≥ t + k + 1`; here `3` is not a lower bound (`not_lb_three`).
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I : Type} [Fintype P] [DecidableEq P] [DecidableEq I] [LinearOrder I]

/-- `floodSet R` solves consensus within `R` rounds when `t < R` or `n ≤ R + 1`. -/
lemma floodSet_solvesWithin [Nonempty P] {t R : ℕ} (hR : t < R ∨ Fintype.card P ≤ R + 1) :
    SolvesWithin (floodSet (P := P) (I := I) R) (consensus P I) t R :=
  { toSolves := (floodSet_solvesSim hR).toSolves
    within := fun _ _ p hp => ⟨R, le_rfl, _, floodSet_decides (Run.alive_of_not_faulty hp R)⟩ }

/-! ### The lone-survivor protocol -/

open Classical in
/-- Flood the known pairs; a process that received no message at all in round 1 decides its own
input at time 1 (all other processes have crashed); otherwise decide as `floodSet 2`. -/
noncomputable def loneSurvivor : Protocol P I (FloodMsg P I) I where
  send p x h _ := some (known p x h)
  decide p x h := if 1 ≤ h.length ∧ ∀ s, rcv h 0 s = none then some x
    else (floodSet 2).decide p x h

lemma hist_loneSurvivor (r : Run P I) (m : ℕ) (p : P) :
    hist (loneSurvivor (P := P) (I := I)) r m p = hist (floodSet 0) r m p :=
  hist_eq_of_send (A := loneSurvivor) (B := floodSet 0) rfl r m p

/-- `p` received no message in round 1. -/
def SilentInbox (r : Run P I) (p : P) : Prop :=
  ∀ s, msg (floodSet (P := P) (I := I) 0) r s p 0 = none

open Classical in
lemma raw_loneSurvivor {r : Run P I} {p : P} {m : ℕ} :
    raw loneSurvivor r p m =
      if 1 ≤ m ∧ SilentInbox r p then some (r.input p) else raw (floodSet 2) r p m := by
  classical
  have e : ∀ s, 1 ≤ m → rcv (hist (floodSet (P := P) (I := I) 0) r m p) 0 s =
      msg (floodSet 0) r s p 0 := fun s hm => rcv_hist r p s (by omega)
  have hd : ∀ x h, (loneSurvivor (P := P) (I := I)).decide p x h =
      if 1 ≤ h.length ∧ ∀ s, rcv h 0 s = none then some x else (floodSet 2).decide p x h :=
    fun _ _ => rfl
  have h2 : raw (floodSet 2) r p m = (floodSet 2).decide p (r.input p) (hist (floodSet 0) r m p) := by
    rw [raw, hist_floodSet 2 0]
  rw [raw, hd, hist_loneSurvivor, Cslib.SyncCrash.length_hist, h2]
  by_cases hm : 1 ≤ m
  · have : (∀ s, rcv (hist (floodSet (P := P) (I := I) 0) r m p) 0 s = none) ↔ SilentInbox r p := by
      simp only [SilentInbox, e _ hm]
    by_cases hs : SilentInbox r p
    · rw [if_pos ⟨hm, this.2 hs⟩, if_pos ⟨hm, hs⟩]
    · rw [if_neg (fun h => hs (this.1 h.2)), if_neg (fun h => hs h.2)]
  · rw [if_neg (fun h => hm h.1), if_neg (fun h => hm h.1)]

lemma raw_floodSet_lt {R : ℕ} {r : Run P I} {p : P} {m : ℕ} (hm : m < R) :
    raw (floodSet R) r p m = none := by
  simp [raw, floodSet, Cslib.SyncCrash.length_hist, hm]

lemma loneSurvivor_decides_silent {r : Run P I} {p : P} (ha : r.Alive p 1) (hs : SilentInbox r p) :
    Decides loneSurvivor r p 1 (r.input p) := by
  refine decides_iff.2 ⟨ha, by rw [raw_loneSurvivor, if_pos ⟨le_rfl, hs⟩], fun m' hm' => ?_⟩
  rw [raw_loneSurvivor, if_neg (by omega), raw_floodSet_lt (by omega)]

lemma decides_loneSurvivor_iff_of_not_silent {r : Run P I} {p : P} (hs : ¬ SilentInbox r p)
    {m : ℕ} {d : I} : Decides loneSurvivor r p m d ↔ Decides (floodSet 2) r p m d := by
  have : ∀ m', raw loneSurvivor r p m' = raw (floodSet 2) r p m' := fun m' => by
    rw [raw_loneSurvivor, if_neg (fun h => hs h.2)]
  simp only [decides_iff, this]

lemma Decides.one_le_loneSurvivor {r : Run P I} {p : P} {m : ℕ} {d : I}
    (h : Decides loneSurvivor r p m d) : 1 ≤ m := by
  by_contra h0
  have := h.raw_eq
  rw [raw_loneSurvivor, if_neg (by omega), raw_floodSet_lt (by omega)] at this
  simp at this

/-- A process alive at time 1 with an empty round-1 inbox is the only process alive at time 1. -/
lemma SilentInbox.not_alive {t : ℕ} {r : Run P I} (hr : r.Admissible t) {p : P}
    (hs : SilentInbox r p) {q : P} (hq : q ≠ p) : ¬ r.Alive q 1 := by
  intro ha
  have hd : r.Deliv q p 0 := ⟨hr.alive_zero q, fun hc => by have := ha 1 hc.1; omega⟩
  have := hs q
  rw [msg_eq_deliv, if_pos ⟨hq, hd⟩] at this
  simp [floodSet] at this

/-- `loneSurvivor` solves simultaneous consensus for `n = 3`, `t = 2`. -/
theorem loneSurvivor_solvesSim (hn : Fintype.card P = 3) :
    SolvesSim (loneSurvivor (P := P) (I := I)) (consensus P I) 2 := by
  haveI : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  have hF := floodSet_solvesSim (P := P) (I := I) (t := 2) (R := 2) (Or.inr (by omega))
  refine { complete := ?_, correct := ?_, simultaneous := ?_ }
  · intro r hr p hp
    by_cases hs : SilentInbox r p
    · exact ⟨1, _, loneSurvivor_decides_silent (Run.alive_of_not_faulty hp 1) hs⟩
    · exact ⟨2, _, (decides_loneSurvivor_iff_of_not_silent hs).2
        (floodSet_decides (Run.alive_of_not_faulty hp 2))⟩
  · intro r hr
    by_cases hex : ∃ p, r.Alive p 1 ∧ SilentInbox r p
    · obtain ⟨p, hpa, hps⟩ := hex
      refine consensus_correct_of ⟨p, rfl⟩ fun q m d hq => ?_
      have hq1 : r.Alive q 1 := hq.alive.mono hq.one_le_loneSurvivor
      have hqp : q = p := by
        by_contra hne; exact hps.not_alive hr.1 hne hq1
      subst hqp
      exact (Decides.unique hq (loneSurvivor_decides_silent hpa hps)).2
    · push Not at hex
      obtain ⟨o, ho, hdec⟩ := hF.correct r hr
      refine ⟨o, ho, fun q m d hq => hdec q m d ?_⟩
      exact (decides_loneSurvivor_iff_of_not_silent
        (hex q (hq.alive.mono hq.one_le_loneSurvivor))).1 hq
  · intro r hr p q m m' d d' hp hq
    have hp1 := hp.alive.mono hp.one_le_loneSurvivor
    have hq1 := hq.alive.mono hq.one_le_loneSurvivor
    by_cases hps : SilentInbox r p
    · have hqp : q = p := by
        by_contra hne; exact hps.not_alive hr.1 hne hq1
      subst hqp; exact (Decides.unique hp hq).1
    · by_cases hqs : SilentInbox r q
      · have hpq : p = q := by
          by_contra hne; exact hqs.not_alive hr.1 hne hp1
        subst hpq; exact (Decides.unique hp hq).1
      · exact hF.simultaneous r hr p q m m' d d'
          ((decides_loneSurvivor_iff_of_not_silent hps).1 hp)
          ((decides_loneSurvivor_iff_of_not_silent hqs).1 hq)

/-! ### The run `r⋆` -/

lemma loneRun_isRun (hn : Fintype.card P = 3) (p₀ : P) (ι : P → I) :
    (consensus P I).IsRun 2 (loneRun p₀ ι) := by
  have := (lemma5_false (O := I) (T := consensus P I) (by omega) rfl ι p₀).2.1
  rwa [hn] at this

lemma loneInv_loneRun (p₀ : P) (ι : P → I) : LoneInv p₀ (loneRun p₀ ι) := by
  refine ⟨fun c hc => by simp [loneRun] at hc, fun q hq hd => ?_⟩
  exact hd.2 ⟨by simp [loneRun, hq], by simp [loneRun]⟩

lemma silentInbox_loneRun (p₀ : P) (ι : P → I) : SilentInbox (loneRun p₀ ι) p₀ := by
  intro s
  rw [msg_eq_deliv, if_neg]
  rintro ⟨hs, hd⟩
  exact (loneInv_loneRun p₀ ι).2 s hs hd

lemma faulty_loneRun {p₀ q : P} {ι : P → I} (h : ¬ (loneRun p₀ ι).Faulty q) : q = p₀ := by
  by_contra hne
  apply h
  simp [Run.Faulty, loneRun, hne]

/-- In `r⋆`, the waste is `1` (two failures exposed in round 1), so `t + 1 − W = 2`. -/
lemma waste_loneRun (hn : Fintype.card P = 3) (p₀ : P) (ι : P → I) :
    (loneRun p₀ ι).waste = 1 := by
  classical
  have hr := loneRun_isRun hn p₀ ι
  have hlt := waste_lt hr.1 (by norm_num)
  have hexp : 2 ≤ (loneRun p₀ ι).exposed 1 := by
    refine le_trans ?_ (card_le_exposed (Finset.univ.erase p₀) fun q hq => ?_)
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hn]
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq
      exact ⟨1, le_rfl, le_rfl, p₀, (loneInv_loneRun p₀ ι).1,
        (loneInv_loneRun p₀ ι).2 q hq⟩
  have := le_waste (loneRun p₀ ι) (k := 1) (by omega)
  omega

/-- `loneSurvivor` decides at time 1 in `r⋆`. -/
lemma loneSurvivor_decides (hn : Fintype.card P = 3) (p₀ : P) (ι : P → I) :
    DecideAll loneSurvivor (loneRun p₀ ι) 1 := by
  intro p hp
  have := faulty_loneRun hp
  subst this
  exact ⟨_, loneSurvivor_decides_silent (loneInv_loneRun p ι).1 (silentInbox_loneRun p ι)⟩

/-- The timing claimed by Theorem 3 for `Opt(A, k̂)`: every process alive at time
`min{k̂, t + 1 − W(F)}` decides at that time. -/
def Thm3Timing {MX : Type} (X : Protocol P I MX I) (t k : ℕ) : Prop :=
  ∀ r, (consensus P I).IsRun t r → ∀ p, r.Alive p (min k (t + 1 - r.waste)) →
    ∃ d, Decides X r p (min k (t + 1 - r.waste)) d

/-- **Theorems 3 and 6 contradict each other for `n = 3`, `t = 2`, consensus, `k̂ = 2`.**
No protocol both decides at `min{k̂, t + 1 − W(F)}` (Theorem 3) and is all-case optimal
(Theorem 6), although all hypotheses of Theorem 6 except Lemma 5 hold (`theorem6_hypotheses`). -/
theorem thm3_thm6_incompatible (hn : Fintype.card P = 3) [Nonempty I] {MX : Type}
    (X : Protocol P I MX I) : ¬ (AllCaseOptimal X (consensus P I) 2 ∧ Thm3Timing X 2 2) := by
  rintro ⟨hopt, htime⟩
  have p₀ : P := Classical.choice (Fintype.card_pos_iff.1 (by omega))
  let ι : P → I := fun _ => Classical.arbitrary I
  have hr := loneRun_isRun hn p₀ ι
  obtain ⟨k', hk', hX⟩ := hopt.2 _ loneSurvivor (loneSurvivor_solvesSim hn) _ hr 1
    (loneSurvivor_decides hn p₀ ι)
  have hp₀ : ¬ (loneRun p₀ ι).Faulty p₀ := by simp [Run.Faulty, loneRun]
  obtain ⟨d, hd⟩ := hX p₀ hp₀
  have hw := waste_loneRun hn p₀ ι
  obtain ⟨d', hd'⟩ := htime _ hr p₀ (Run.alive_of_not_faulty hp₀ _)
  rw [hw] at hd'
  have := (Decides.unique hd hd').1
  norm_num at this
  omega

/-- The hypotheses of Theorem 6 (other than Lemma 5) hold for `n = 3`, `t = 2`, consensus,
`k̂ = 2`, `A = floodSet 2`: the input set is complete, `2` is a worst-case lower bound, and
`floodSet 2` solves consensus within 2 rounds. -/
theorem theorem6_hypotheses (hn : Fintype.card P = 3) {a b : I} (hab : a ≠ b) :
    (consensus P I).inputs = Set.univ ∧ WorstCaseLB (consensus P I) 2 2 ∧
      SolvesWithin (floodSet (P := P) (I := I) 2) (consensus P I) 2 2 :=
  haveI : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  ⟨rfl, consensus_lb_two (by omega) (by norm_num) (by omega) hab,
    floodSet_solvesWithin (Or.inr (by omega))⟩

/-- **Theorem 6 fails for `n = 3`, `t = 2`**: for every protocol `C` with the ConCon properties
of §2.3, `Opt(floodSet 2, 2) = Delay(floodSet 2, 2) else ConCon(floodSet 2)` is not all-case
optimal, although its hypotheses (`theorem6_hypotheses`) hold. -/
theorem theorem6_fails (hn : Fintype.card P = 3) [Nonempty I] {MC : Type}
    {C : CCProtocol P I MC} (hC : IsConCon C (consensus P I) 2) :
    ¬ AllCaseOptimal (Opt C (floodSet 2) (consensus P I) 2) (consensus P I) 2 := fun h =>
  haveI : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  thm3_thm6_incompatible hn _
    ⟨h, (theorem3 hC (floodSet_solvesWithin (P := P) (I := I) (Or.inr (by omega)))).2⟩

/-! ### Corollary 9 -/

lemma waste_ffRun (ι : P → I) : (ffRun ι).waste = 0 := by
  have h0 : ∀ k, (ffRun ι).exposed k = 0 := fun k => by
    have := exposed_le_faulty (ffRun ι) k
    have h0 : (ffRun ι).faulty = ∅ := by ext p; simp [Run.Faulty, ffRun]
    rw [h0, Finset.card_empty] at this
    omega
  unfold Run.waste
  simp [h0]

/-- `3 = ⌊t/1⌋ + 1` is not a worst-case lower bound for consensus with `n = 3`, `t = 2`. -/
theorem not_lb_three (hn : Fintype.card P = 3) :
    ¬ WorstCaseLB (consensus P I) 2 3 := fun h => by
  haveI : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  have := h _ _ _ (floodSet_solvesWithin (P := P) (I := I) (t := 2) (R := 2) (Or.inr (by omega)))
  omega

/-- **Corollary 9 is false for `k = 1`, `n = 3`, `t = 2`**: no protocol is both all-case optimal
for simultaneous consensus and halts at `min{⌊t/k⌋ + 1, t + 1 − W} = min{3, 3 − W}` (as claimed
for `Opt(sa, ⌊t/k⌋ + 1)`), since `floodSet 2` decides at time 2 in the failure-free run. -/
theorem corollary9_false (hn : Fintype.card P = 3) [Nonempty I] {MX : Type}
    (X : Protocol P I MX I) : ¬ (AllCaseOptimal X (consensus P I) 2 ∧ Thm3Timing X 2 3) := by
  rintro ⟨hopt, htime⟩
  have p₀ : P := Classical.choice (Fintype.card_pos_iff.1 (by omega))
  let ι : P → I := fun _ => Classical.arbitrary I
  have hr : (consensus P I).IsRun 2 (ffRun ι) := ffRun_isRun 2 trivial
  haveI : Nonempty P := ⟨p₀⟩
  have hF := floodSet_solvesSim (P := P) (I := I) (t := 2) (R := 2) (Or.inr (by omega))
  obtain ⟨k', hk', hX⟩ := hopt.2 _ (floodSet 2) hF _ hr 2
    (fun p _ => ⟨_, floodSet_decides (Run.alive_of_not_faulty (ffRun_not_faulty p) 2)⟩)
  obtain ⟨d, hd⟩ := hX p₀ (ffRun_not_faulty p₀)
  obtain ⟨d', hd'⟩ := htime _ hr p₀ (Run.alive_of_not_faulty (ffRun_not_faulty p₀) _)
  rw [waste_ffRun] at hd'
  have := (Decides.unique hd hd').1
  norm_num at this
  omega

end Podc.SimultaneousAllCaseOptimal
