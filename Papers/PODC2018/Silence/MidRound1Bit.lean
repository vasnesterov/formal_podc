import Papers.PODC2018.Silence.MidRound15D

/-!
# A 1-bit decoding of `huh?` under which 1.5D is incorrect

Appendix D of Goren–Moses says that, as in STEALTH, all messages of the 1.5D protocol (Figure 5)
can be single bits: "The only non-trivial one is `huh?`, implemented in 1-bit by: quiet to
`{i+1, …, i+f} % n`; `1` to the rest." So in round 2 a process that is not `ok` sends `1` only to
the processes outside its successor set `nb i`. The paper does not say how receivers decode this.

This file takes the decoding where a round-2 `1` from `j` counts as `all[1]` if the receiver is in
`nb j`, and as `huh?` otherwise; silence from a predecessor `j` (receiver in `nb j`) is ignored.
Under this decoding the protocol violates Agreement (`oneBit_not_solvesACMid`): `n = 5`, `f = 2`,
`nb i = {i+1, i+2}`, all values `1`; process `4` crashes in round 1 reaching only `1, 2`; process `3`
crashes in round 2 sending nothing. Processes `1, 2` are `ok` and commit in mid-round 2. Process `0`
is not `ok`; its `huh?` goes only to `3, 4` (crashed), so `1` and `2` hear no `huh?` and halt.
Process `0` received no `all[1]` (`0 ∈ nb j` only for `j ∈ {3, 4}`), so it runs the consensus alone
with value `0` and aborts at time `f + 2 = 4`.

The counterexample covers only this decoding. If silence from a predecessor is also read as `huh?`
(an `ok` predecessor would have sent `all[1]`), the 1-bit protocol is correct:
`Papers.PODC2018.Silence.MidRound.OneBitFixed.solvesACMid` (`MidRound1BitFixed.lean`). The
protocol of `MidRound15D.lean`, where `huh?` is a separate message sent to all, is correct too.
-/

namespace Papers.PODC2018.Silence.MidRound.OneBit

open Cslib.SyncCrash Classical
open Papers.PODC2018.Silence.MidRound.OnePointFive (ok H)

variable {P : Type*}

/-- Received a round-2 `1` from some `j` with `p ∉ nb j` (decoded as `huh?`). -/
def huh1 (nb : P → Finset P) (p : P) (h : H P) : Prop := ∃ j, rcv h 1 j ≠ none ∧ p ∉ nb j

/-- Received a round-2 `1` from some `j` with `p ∈ nb j` (decoded as `all[1]`). -/
def all11 (nb : P → Finset P) (p : P) (h : H P) : Prop := ∃ j, rcv h 1 j ≠ none ∧ p ∈ nb j

def part1 (nb : P → Finset P) (p : P) (x : Bool) (h : H P) : Prop := ¬ ok p x h ∨ huh1 nb p h

def val1 (nb : P → Finset P) (p : P) (x : Bool) (h : H P) : Prop :=
  (ok p x h ∨ all11 nb p h) ∨ ∃ t', 2 ≤ t' ∧ t' < h.length ∧ ∃ j, rcv h t' j ≠ none

/-- 1.5D with the 1-bit encoding of `huh?` (all messages are the bit `true`). -/
noncomputable def alg1 (f : ℕ) (nb : P → Finset P) : ACProtocol P Bool where
  send p x h q :=
    if h.length = 0 then (if x = true then some true else none)
    else if h.length = 1 then
      (if ok p x h then (if q ∈ nb p then some true else none)
       else (if q ∉ nb p then some true else none))
    else if h.length < f + 2 then (if part1 nb p x h ∧ val1 nb p x h then some true else none)
    else none
  decide p x h :=
    if h.length = 1 ∧ ok p x h then some .commit
    else if h.length = f + 2 ∧ ¬ ok p x h then
      (if val1 nb p x h then some .commit else some .abort)
    else none

/-- Successors `{i + 1, i + 2}` on `Fin 5`. -/
def nb5 (i : Fin 5) : Finset (Fin 5) := {i + 1, i + 2}

/-- `nb5` satisfies the hypotheses of the 1.5D protocol for `f = 2`. -/
lemma nb5_spec : (∀ i, i ∉ nb5 i) ∧ ∀ i, (nb5 i).card = 2 := by
  constructor <;> decide

/-- The run of the counterexample. -/
def cex : Run (Fin 5) Bool where
  input _ := true
  crash z := if z = 4 then some 1 else if z = 3 then some 2 else none
  reach z := if z = 4 then {1, 2} else ∅

noncomputable abbrev A := alg1 (P := Fin 5) 2 nb5

lemma send_def1 (f : ℕ) (nb : P → Finset P) (p : P) (x : Bool) (h : H P) (q : P) :
    (alg1 f nb).send p x h q =
    if h.length = 0 then (if x = true then some true else none)
    else if h.length = 1 then
      (if ok p x h then (if q ∈ nb p then some true else none)
       else (if q ∉ nb p then some true else none))
    else if h.length < f + 2 then (if part1 nb p x h ∧ val1 nb p x h then some true else none)
    else none := rfl

lemma decide_def1 (f : ℕ) (nb : P → Finset P) (p : P) (x : Bool) (h : H P) :
    (alg1 f nb).decide p x h =
    if h.length = 1 ∧ ok p x h then some .commit
    else if h.length = f + 2 ∧ ¬ ok p x h then
      (if val1 nb p x h then some .commit else some .abort)
    else none := rfl

lemma deliv_iff (k j : Fin 5) (t : ℕ) : cex.Deliv k j t ↔
    (k = 4 → t = 0 ∧ (j = 1 ∨ j = 2)) ∧ (k = 3 → t = 0) := by
  simp only [Run.Deliv, Run.Alive, cex]
  fin_cases k <;> simp <;> omega

lemma sent0 (k j : Fin 5) : Sent A cex k j 0 ↔ k ≠ j ∧ (k = 4 → j = 1 ∨ j = 2) := by
  rw [sent_iff_deliv, send_def1, deliv_iff]
  simp only [length_hist, ite_true, cex]
  simp

lemma ok_iff (p : Fin 5) {m : ℕ} (hm : 1 ≤ m) :
    ok p (cex.input p) (hist A cex m p) ↔ p ≠ 0 ∧ p ≠ 3 := by
  show (cex.input p = true ∧ ∀ j, j ≠ p → rcv (hist A cex m p) 0 j ≠ none) ↔ _
  simp only [rcv_hist cex p _ (show 0 < m by omega)]
  have e : ∀ j, (msg A cex j p 0 ≠ none) = Sent A cex j p 0 := fun _ => rfl
  simp only [e, sent0, show cex.input p = true from rfl, true_and]
  fin_cases p <;> decide

lemma msg1_ne (k j : Fin 5) : msg A cex k j 1 ≠ none ↔
    k ≠ j ∧ k ≠ 4 ∧ k ≠ 3 ∧ (k ≠ 0 → j ∈ nb5 k) ∧ (k = 0 → j ∉ nb5 k) := by
  have := sent_iff_deliv (alg := A) cex k j 1
  unfold Sent at this
  rw [this, send_def1, deliv_iff, length_hist]
  simp only [one_ne_zero, ite_false, ite_true]
  by_cases hk : k = 0
  · subst hk
    rw [if_neg (by rw [ok_iff 0 le_rfl]; simp)]
    fin_cases j <;> simp [nb5]
  · by_cases hk3 : k = 3
    · subst hk3; simp
    · by_cases hk4 : k = 4
      · subst hk4; simp
      · rw [if_pos (by rw [ok_iff k le_rfl]; exact ⟨hk, hk3⟩)]
        by_cases hj : j ∈ nb5 k
        · simp only [hj, ite_true]
          have : k ≠ j := by
            intro h; subst h; exact nb5_spec.1 k hj
          simp [hk, hk3, hk4, this]
        · simp [hj, hk]

lemma part1_false (y : Fin 5) (hy : y = 1 ∨ y = 2) {m : ℕ} (hm : 2 ≤ m) :
    ¬ part1 nb5 y (cex.input y) (hist A cex m y) := by
  rintro (h | ⟨k, hk, hny⟩)
  · exact h ((ok_iff y (by omega)).2 (by rcases hy with rfl | rfl <;> decide))
  · rw [rcv_hist cex y _ (show 1 < m by omega), msg1_ne] at hk
    rcases hy with rfl | rfl <;> fin_cases k <;> simp_all [nb5]

lemma no_cons_msg (y : Fin 5) {t : ℕ} (h2 : 2 ≤ t) (h4 : t < 4) : ¬ Sent A cex y 0 t := by
  intro hs
  have hd := hs.deliv
  rw [deliv_iff] at hd
  obtain ⟨hd4, hd3⟩ := hd
  have hne := hs.ne
  have hsend := hs.send_ne_none
  rw [send_def1, length_hist, if_neg (by omega), if_neg (by omega), if_pos (by omega)] at hsend
  have hp : part1 nb5 y (cex.input y) (hist A cex t y) := by
    by_contra hc; rw [if_neg (fun h => hc h.1)] at hsend; exact hsend rfl
  fin_cases y
  · exact hne rfl
  · exact part1_false 1 (Or.inl rfl) h2 hp
  · exact part1_false 2 (Or.inr rfl) h2 hp
  · exact absurd (hd3 (by decide)) (by omega)
  · exact absurd (hd4 (by decide)).1 (by omega)

lemma cex_admissible : cex.Admissible 2 := by
  refine ⟨?_, ?_⟩
  · have : cex.faulty ⊆ {3, 4} := by
      intro z hz
      simp only [Run.mem_faulty, Run.Faulty, cex] at hz
      fin_cases z <;> simp_all
    exact (Finset.card_le_card this).trans (by decide)
  · intro z c hc
    simp only [cex] at hc
    split_ifs at hc <;> (simp at hc; omega)

/-- **The 1-bit 1.5D protocol does not solve AC in `γ̃_2`** (`n = 5`): in `cex`, process `1` commits
in mid-round 2 and process `0` (correct) aborts at time `4`. -/
theorem oneBit_not_solvesACMid : ¬ SolvesACMid (alg1 (P := Fin 5) 2 nb5) 2 := by
  intro hAC
  have h1 : DecidesMid A cex 1 1 .commit := by
    refine ⟨fun c hc => by simp [cex] at hc, fun q _ _ => ?_, ?_⟩
    · rw [deliv_iff]; simp
    · rw [decide_def1, length_hist, if_pos ⟨rfl, (ok_iff 1 le_rfl).2 (by decide)⟩]
  have h0 : DecidesMid A cex 0 4 .abort := by
    refine ⟨fun c hc => by simp [cex] at hc, fun q _ hs => ?_, ?_⟩
    · rw [send_def1, length_hist] at hs; simp at hs
    · have hnok : ¬ ok 0 (cex.input 0) (hist A cex 4 0) := fun h =>
        ((ok_iff 0 (by omega)).1 h).1 rfl
      rw [decide_def1, length_hist, if_neg (by omega), if_pos ⟨rfl, hnok⟩, if_neg]
      rintro ((h | ⟨k, hk, hk0⟩) | ⟨t', h2, h4, j, hj⟩)
      · exact hnok h
      · rw [rcv_hist cex 0 _ (show 1 < 4 by omega), msg1_ne] at hk
        fin_cases k <;> simp_all [nb5]
      · rw [length_hist] at h4
        rw [rcv_hist cex 0 _ h4] at hj
        exact no_cons_msg j h2 h4 hj
  exact absurd ((hAC cex cex_admissible).agreement _ _ _ _ _ _ h1 h0) (by decide)

end Papers.PODC2018.Silence.MidRound.OneBit
