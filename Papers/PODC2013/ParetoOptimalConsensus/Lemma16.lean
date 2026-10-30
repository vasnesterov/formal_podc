import Papers.PODC2013.ParetoOptimalConsensus.Lemma15

/-!
# Lemma 16 (no earlier decisions when `K_i ∃0`, Appendix C)

Let `Q ⪰ U-P0` solve uniform consensus, `0 < t < n`. If `K_i ∃0` but `¬K_i ∃correct(0)` at `m`,
then `i` does not decide at `m`. Proof as in the paper: `m = 0` is Lemma 13; for `m > 0`, by
Lemma 6, `i` learnt `∃0` at `m` from fewer than `t - F⟨i, m⟩` carriers, so `F⟨i, m⟩ < t - 1`; in the
run where every process not known by `⟨i, m⟩` to have crashed is correct, Lemma 15 (Part 2) makes
`i` decide `0` at `m + 1`.
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

/-- **Lemma 16.** -/
theorem lemma16 (ht0 : 0 < t) (ht : t < Fintype.card P) {Q : Protocol P}
    (hQ : SolvesUniformSetConsensus 1 t bin Q) (hdom : Dominates t bin Q (uP0 t)) {r : Run P}
    (hr : Adm t bin r) {i : P} {m : ℕ} (h0 : 0 ∈ vals r i m) (hnk : ¬ KCorrect t r i m 0)
    (v : ℕ) : ¬ DecidesAt Q r i m v := by
  classical
  intro hd
  rcases m with _ | M
  · exact lemma13 ht0 ht hQ hr i v hd
  have hal := hd.1
  -- Lemma 6: `i` did not know `∃0` at `M`, and knows of at most `t - 2` failures
  have h6 := (lemma6 ht hr hal zero_mem_bin).not.1 hnk
  simp only [h0, true_and, not_or, Nat.add_sub_cancel] at h6
  obtain ⟨ha, hb⟩ := h6
  have hn0 : 0 ∉ vals r i M := fun h => ha ⟨Nat.succ_pos M, h⟩
  have hcar : 1 ≤ carriers r i (M + 1) 0 := by
    obtain hv | ⟨q, hq, hqv⟩ := mem_vals_succ.1 h0
    · exact absurd hv hn0
    rw [carriers_eq_card]
    exact card_pos.2 ⟨q, mem_carrierSet.2 ⟨Nat.succ_pos M, by simpa using seen_of_comm hq,
      by simpa using hqv⟩⟩
  have hK : known r i (M + 1) + 2 ≤ t := by omega
  -- the run in which all processes not known to have crashed are correct
  set K : Set P := {p | p ∉ knownSet r i (M + 1)}
  have hKd : ∀ p ∈ K, p ≠ i → r.Deliv p i M := by
    intro p hp hpi
    by_contra hnd
    exact hp (mem_knownSet.2 ⟨i, M, Nat.lt_succ_self M, seen_self le_rfl, Ne.symm hpi, hnd⟩)
  have hKa : ∀ p ∈ K, r.Alive p M := by
    intro p hp
    by_cases hpi : p = i
    · rw [hpi]; exact hal.mono (Nat.le_succ M)
    · exact (hKd p hp hpi).1
  set r' := modify r K r.reach M
  have hr' : Adm t bin r' := modify_admissible hr
  have hsv : SameView r r' i (M + 1) :=
    modify_sameView_last hKa (fun p hp hpi => hKd p hp hpi) (fun _ _ => Iff.rfl)
  have hiK : i ∈ K := fun h => not_guarCrashed_of_alive hal (mem_knownSet.1 h)
  have hic : ¬ r'.Faulty i := modify_not_faulty hiK
  have hal' : r'.Alive i (M + 2) := SyncCrash.Run.alive_of_not_faulty hic _
  -- `i` knows of no new failure at `M + 2`
  have hK' : known r' i (M + 2) + 2 ≤ t := by
    have hsub : knownSet r' i (M + 2) ⊆ knownSet r i (M + 1) := by
      intro p hp
      by_contra hpK
      have hpK' : p ∈ K := hpK
      have := modify_not_faulty (r := r) (R := r.reach) (M := M) hpK'
      exact not_guarCrashed_of_alive (SyncCrash.Run.alive_of_not_faulty this _)
        (mem_knownSet.1 hp)
    have := card_le_card hsub
    rw [← known_eq_card, ← known_eq_card] at this
    omega
  have hf : FirstKnows r i (M + 1) 0 := ⟨h0, fun M' hM' => by
    obtain rfl : M = M' := by omega
    exact hn0⟩
  have hd2 : DecidesAt Q r' i (M + 2) 0 :=
    g15_all ht hQ hdom (M + 1) r' hr' i hal' ((SameView.firstKnows_iff hsv).1 hf)
      (fun hk => hnk ((kCorrect_iff_of_sameView hsv).2 hk)) hK'
  have hd' : DecidesAt Q r' i (M + 1) v :=
    (hsv.decidesAt_iff Q le_rfl ⟨fun _ => hal'.mono (Nat.le_succ _), fun _ => hal⟩).1 hd
  have := (hd'.unique hd2).1
  omega

end Podc.ParetoOptimalConsensus
