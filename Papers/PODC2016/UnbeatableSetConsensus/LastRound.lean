import Papers.PODC2016.UnbeatableSetConsensus.Runs

/-!
# Adjusting the messages received in the last round (the "changes" in the proof of Lemma 1)

Setting: a base run `r₀`, a process `x` alive at time `M + 1` and high at `M`, `k` distinct
processes `j b` high at `M` whose time-`M` nodes are seen by `⟨x, M + 1⟩`, and for every low value
`w < k` a process `iw w`, alive at `M`, whose only low value at `M` is `w`. Every process that is
alive and low at `M` crashes in round `M + 1` (`hD`).

`lastRun σ W` makes `x`, the `j b` and the processes `iw w` (`w ∈ W`) correct, and lets every low
crashing process `y` reach `j b` in round `M + 1` iff `y = iw w` for some `w ∈ σ b` (and reach the
other processes as in `r₀`). Then:

* nothing changes up to time `M` (`lastRun_sameView_le`);
* `Lows⟨j b, M + 1⟩ = σ b` (`lastRun_lows`) and the view of `⟨j b, M + 1⟩` depends only on `σ b`
  (`lastRun_sameView_j`);
* for `W = ∅`, `x` has the same view at `M + 1` as in `r₀` (`lastRun_sameView_x`).
-/

namespace Podc.UnbeatableSetConsensus

open Cslib Finset

variable {P : Type*} [Fintype P] {k : ℕ}

section LastRound

variable (k) (r₀ : Run P) (x : P) (M : ℕ) (j : Fin k → P) (iw : ℕ → P)

open Classical in
/-- The new reach sets of round `M + 1`. -/
noncomputable def lastReach (σ : Fin k → Finset ℕ) (y : P) : Set P :=
  if Low k r₀ y M then {p | (p ∈ r₀.reach y ∧ p ∉ Set.range j) ∨ ∃ b, p = j b ∧ ∃ w ∈ σ b, iw w = y}
  else r₀.reach y

/-- The processes made correct. -/
def lastCorrect (W : Finset ℕ) : Set P := insert x (Set.range j) ∪ iw '' ↑W

/-- The run with adjusted last round. -/
noncomputable def lastRun (σ : Fin k → Finset ℕ) (W : Finset ℕ) : Run P :=
  modify r₀ (lastCorrect k x j iw W) (lastReach k r₀ M j iw σ) M

/-- The hypotheses of the setting. -/
structure LastHyp : Prop where
  alive_x : r₀.Alive x (M + 1)
  high_x : ¬ Low k r₀ x M
  seen_j : ∀ b, Seen r₀ (j b) M x (M + 1)
  high_j : ∀ b, ¬ Low k r₀ (j b) M
  inj_j : Function.Injective j
  j_ne_x : ∀ b, j b ≠ x
  alive_iw : ∀ w < k, r₀.Alive (iw w) M
  lows_iw : ∀ w < k, lows k r₀ (iw w) M = {w}
  crash_low : ∀ y, r₀.Alive y M → Low k r₀ y M → r₀.crash y = some (M + 1)

variable {k r₀ x M j iw}
variable (H : LastHyp k r₀ x M j iw)
include H

lemma LastHyp.low_iw {w : ℕ} (hw : w < k) : Low k r₀ (iw w) M :=
  low_iff_lows_nonempty.2 (by rw [H.lows_iw w hw]; exact singleton_nonempty w)

lemma LastHyp.alive_j (b : Fin k) : r₀.Alive (j b) M := (H.seen_j b).alive H.alive_x

lemma LastHyp.alive_correct {W : Finset ℕ} (hW : W ⊆ range k) :
    ∀ p ∈ lastCorrect k x j iw W, r₀.Alive p M := by
  rintro p ((rfl | ⟨b, rfl⟩) | ⟨w, hw, rfl⟩)
  · exact H.alive_x.mono (Nat.le_succ M)
  · exact H.alive_j b
  · exact H.alive_iw w (mem_range.1 (hW hw))

omit H in
lemma LastHyp.adm {t : ℕ} {D : Set ℕ} (hr : Adm t D r₀) (σ : Fin k → Finset ℕ) (W : Finset ℕ) :
    Adm t D (lastRun k r₀ x M j iw σ W) := modify_admissible hr

omit H in
lemma LastHyp.correct {σ : Fin k → Finset ℕ} {W : Finset ℕ} {p : P}
    (hp : p ∈ lastCorrect k x j iw W) : ¬ (lastRun k r₀ x M j iw σ W).Faulty p :=
  modify_not_faulty hp

lemma LastHyp.sameView_le {σ : Fin k → Finset ℕ} {W : Finset ℕ} (hW : W ⊆ range k) {s : ℕ}
    (hs : s ≤ M) (p : P) : SameView r₀ (lastRun k r₀ x M j iw σ W) p s :=
  modify_sameView (H.alive_correct hW) hs p

/-- The view of `x` at `M + 1` is unchanged when no low process is made correct. -/
lemma LastHyp.sameView_x (σ : Fin k → Finset ℕ) :
    SameView r₀ (lastRun k r₀ x M j iw σ ∅) x (M + 1) := by
  classical
  refine modify_sameView_last (H.alive_correct (empty_subset _)) ?_ ?_
  · rintro p ((rfl | ⟨b, rfl⟩) | ⟨w, hw, rfl⟩) hpx
    · exact absurd rfl hpx
    · exact (H.seen_j b).deliv_of_succ hpx
    · simp at hw
  · intro q _
    simp only [lastReach]
    split_ifs
    · simp only [Set.mem_ofPred_eq, Set.mem_range, not_exists]
      constructor
      · rintro (⟨h, -⟩ | ⟨b, hb, -⟩)
        · exact h
        · exact absurd hb.symm (H.j_ne_x b)
      · intro h; exact Or.inl ⟨h, fun b hb => H.j_ne_x b hb⟩
    · exact Iff.rfl

/-- Who reaches `j b` in round `M + 1`. -/
lemma LastHyp.deliv_j {σ : Fin k → Finset ℕ} {W : Finset ℕ} (hW : W ⊆ range k)
    (hWσ : ∀ b, W ⊆ σ b) (b : Fin k) (q : P) :
    (lastRun k r₀ x M j iw σ W).Deliv q (j b) M ↔
      q ∈ insert x (Set.range j) ∨
      (r₀.Alive q M ∧ (Low k r₀ q M → ∃ w ∈ σ b, iw w = q) ∧
        (¬ Low k r₀ q M → ¬ (r₀.crash q = some (M + 1) ∧ j b ∉ r₀.reach q))) := by
  classical
  rw [lastRun, modify_deliv_last]
  have hreach : ∀ hl : Low k r₀ q M, j b ∈ lastReach k r₀ M j iw σ q ↔ ∃ w ∈ σ b, iw w = q := by
    intro hl
    simp only [lastReach, hl, ite_true, Set.mem_ofPred_eq, Set.mem_range, exists_apply_eq_apply,
      not_true_eq_false, and_false, false_or]
    constructor
    · rintro ⟨b', hb', hw⟩; rw [← H.inj_j hb'] at hw; exact hw
    · intro h; exact ⟨b, rfl, h⟩
  constructor
  · rintro (hK | ⟨ha, hn⟩)
    · rcases hK with hK | ⟨w, hw, rfl⟩
      · exact Or.inl hK
      · refine Or.inr ⟨H.alive_iw w (mem_range.1 (hW hw)), fun _ => ⟨w, hWσ b hw, rfl⟩,
          fun hl => absurd (H.low_iw (mem_range.1 (hW hw))) hl⟩
    · by_cases hq : q ∈ insert x (Set.range j)
      · exact Or.inl hq
      refine Or.inr ⟨ha, fun hl => ?_, fun hl hc => hn ⟨hc.1, ?_⟩⟩
      · rw [← hreach hl]
        by_contra hj
        exact hn ⟨H.crash_low q ha hl, hj⟩
      · simp only [lastReach, hl, ite_false]; exact hc.2
  · rintro (hq | ⟨ha, hl1, hl2⟩)
    · exact Or.inl (Or.inl hq)
    · refine Or.inr ⟨ha, fun ⟨hc, hj⟩ => ?_⟩
      by_cases hl : Low k r₀ q M
      · exact hj ((hreach hl).2 (hl1 hl))
      · simp only [lastReach, hl, ite_false] at hj
        exact hl2 hl ⟨hc, hj⟩

/-- The view of `⟨j b, M + 1⟩` depends only on `σ b`. -/
lemma LastHyp.sameView_j {σ σ' : Fin k → Finset ℕ} {W W' : Finset ℕ} (hW : W ⊆ range k)
    (hWσ : ∀ b, W ⊆ σ b) (hW' : W' ⊆ range k) (hWσ' : ∀ b, W' ⊆ σ' b) (b : Fin k)
    (hσ : σ b = σ' b) :
    SameView (lastRun k r₀ x M j iw σ W) (lastRun k r₀ x M j iw σ' W') (j b) (M + 1) := by
  refine sameView_of_agree (fun _ _ => rfl) (fun h s hs q hq => ?_)
  have hsM : s + 1 ≤ M + 1 := hs.le
  rcases Nat.lt_or_eq_of_le hsM with hlt | heq
  · rw [lastRun, lastRun, modify_deliv_lt (H.alive_correct hW) (by omega),
      modify_deliv_lt (H.alive_correct hW') (by omega)]
  · obtain rfl : s = M := by omega
    obtain rfl : h = j b := seen_same_time hs
    rw [H.deliv_j hW hWσ b, H.deliv_j hW' hWσ' b, hσ]

/-- `Lows⟨j b, M + 1⟩ = σ b`. -/
lemma LastHyp.lows_j {σ : Fin k → Finset ℕ} {W : Finset ℕ} (hW : W ⊆ range k)
    (hWσ : ∀ b, W ⊆ σ b) (hσ : ∀ b, σ b ⊆ range k) (b : Fin k) :
    lows k (lastRun k r₀ x M j iw σ W) (j b) (M + 1) = σ b := by
  set T := lastRun k r₀ x M j iw σ W
  have hsv : ∀ p, SameView r₀ T p M := H.sameView_le hW le_rfl
  ext v
  rw [mem_lows]
  constructor
  · rintro ⟨hv, hvk⟩
    rcases mem_vals_succ.1 hv with hv | ⟨q, hq, hv⟩
    · rw [← (hsv (j b)).vals_eq] at hv
      exact absurd ⟨v, hv, hvk⟩ (H.high_j b)
    · rw [← (hsv q).vals_eq] at hv
      have hl : Low k r₀ q M := ⟨v, hv, hvk⟩
      rcases (H.deliv_j hW hWσ b q).1 hq.2 with hq' | ⟨ha, h1, -⟩
      · rcases hq' with rfl | ⟨b', rfl⟩
        · exact absurd hl H.high_x
        · exact absurd hl (H.high_j b')
      · obtain ⟨w, hw, rfl⟩ := h1 hl
        have hwk := mem_range.1 (hσ b hw)
        have : v ∈ lows k r₀ (iw w) M := mem_lows.2 ⟨hv, hvk⟩
        rw [H.lows_iw w hwk, mem_singleton] at this
        rw [this]; exact hw
  · intro hv
    have hwk := mem_range.1 (hσ b hv)
    refine ⟨?_, hwk⟩
    have hlow := H.lows_iw v hwk
    have hmem : v ∈ vals r₀ (iw v) M := (mem_lows.1 (hlow ▸ mem_singleton_self v)).1
    have hne : iw v ≠ j b := fun he => H.high_j b (he ▸ H.low_iw hwk)
    refine vals_subset_succ_of_comm ⟨hne, ?_⟩ (((hsv (iw v)).vals_eq) ▸ hmem)
    rw [H.deliv_j hW hWσ b]
    exact Or.inr ⟨H.alive_iw v hwk, fun _ => ⟨v, hv, rfl⟩,
      fun hl => absurd (H.low_iw hwk) hl⟩

end LastRound

end Podc.UnbeatableSetConsensus
