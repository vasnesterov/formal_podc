import Papers.PODC2019.SmallBuffersAQT.RoundMain

/-!
# Lemma 4.8 (repaired): badness strictly decreases during a phase

A phase processes the levels in *decreasing* order `ℓ-1, ℓ-2, …, 0` (as the proof of
Lemma 4.8 in the paper assumes: "levels are activated in decreasing order over the course of a
phase"; Algorithm 3 as printed uses `λ = t mod ℓ`, i.e. increasing order, for which the lemma is
false, see `Counterexample.lean`).
-/

namespace Podc.SmallBuffersAQT

open Finset

variable {m ℓ : ℕ}

lemma Bad_union (c : Config) {L1 L2 : Finset ℕ} (h : Disjoint L1 L2) (i : ℕ) :
    Bad m ℓ c (L1 ∪ L2) i = Bad m ℓ c L1 i + Bad m ℓ c L2 i := by
  unfold Bad
  rw [← sum_union]
  · congr 1
    ext q
    simp only [mem_filter, mem_union]
    tauto
  · rw [disjoint_filter]
    rintro q - ⟨h1, -⟩ ⟨h2, -⟩
    exact disjoint_left.1 h h1 h2

lemma badness_split (c : Config) {lam : ℕ} (hlam : lam < ℓ) (i : ℕ) :
    badness m ℓ c i = Bad m ℓ c (range lam) i + Bad m ℓ c {lam} i + Bad m ℓ c (Ico (lam + 1) ℓ) i := by
  unfold badness
  have h1 : range ℓ = (range lam ∪ {lam}) ∪ Ico (lam + 1) ℓ := by
    ext j; simp only [mem_range, mem_union, mem_singleton, mem_Ico]; omega
  rw [h1, Bad_union, Bad_union]
  · rw [disjoint_left]; intro j hj; simp at hj ⊢; omega
  · rw [disjoint_left]; intro j hj; simp at hj ⊢; omega

lemma Bad_range_succ (c : Config) (lam i : ℕ) :
    Bad m ℓ c (range (lam + 1)) i = Bad m ℓ c (range lam) i + Bad m ℓ c {lam} i := by
  rw [range_add_one, insert_eq, union_comm, Bad_union]
  rw [disjoint_left]; intro j hj; simp at hj ⊢; omega

/-- One round at level `lam`: the badness does not increase, and if the badness at levels
`≤ lam` is positive then either the badness decreases or positive badness remains at levels
`< lam`. -/
lemma round_main {c : Config} {sel : ℕ → Key → ℕ} (hsel : ValidSel m ℓ c sel) {lam : ℕ}
    (hlam : lam < ℓ) (i : ℕ) :
    badness m ℓ (hptsStep m ℓ lam c sel) i ≤ badness m ℓ c i ∧
      (0 < Bad m ℓ c (range (lam + 1)) i →
        badness m ℓ (hptsStep m ℓ lam c sel) i < badness m ℓ c i ∨
          0 < Bad m ℓ (hptsStep m ℓ lam c sel) (range lam) i) := by
  have hH := Bad_high_eq (lam := lam) hsel (L := Ico (lam + 1) ℓ)
    (fun j hj => by simp at hj; omega) i
  have hL := Bad_lam_le hsel hlam i
  have hLo := Bad_low_le hsel (lam := lam) i
  have hpos := fpAct_of_Bad_lam_pos (m := m) (ℓ := ℓ) (c := c) (lam := lam) (i := i)
  rw [badness_split _ hlam, badness_split _ hlam, Bad_range_succ]
  constructor
  · split_ifs at hL hLo <;> omega
  · intro h
    by_cases h0 : 0 < Bad m ℓ c {lam} i
    · have := hpos h0
      rw [ite_eq_left this] at hL hLo
      omega
    · rw [Nat.not_lt, Nat.le_zero] at h0
      split_ifs at hL hLo with hfp <;> omega

/-- Lemma 4.8 (repaired, levels in decreasing order): along rounds at levels
`lam, lam-1, …, 0` the badness of every node never increases, and it strictly decreases if the
badness at levels `≤ lam` is positive at the start. -/
theorem phase_decreasing (i : ℕ) :
    ∀ lam, lam < ℓ → ∀ d : ℕ → Config,
      (∀ k ≤ lam, ∃ sel, ValidSel m ℓ (d k) sel ∧ d (k + 1) = hptsStep m ℓ (lam - k) (d k) sel) →
      (∀ k ≤ lam + 1, badness m ℓ (d k) i ≤ badness m ℓ (d 0) i) ∧
        (0 < Bad m ℓ (d 0) (range (lam + 1)) i → badness m ℓ (d (lam + 1)) i < badness m ℓ (d 0) i) := by
  intro lam
  induction lam with
  | zero =>
    intro hl d hd
    obtain ⟨sel, hsel, h1⟩ := hd 0 le_rfl
    have hr := round_main hsel hl i
    rw [← h1] at hr
    refine ⟨fun k hk => ?_, fun h => ?_⟩
    · interval_cases k
      · exact le_rfl
      · exact hr.1
    · rcases hr.2 h with h' | h'
      · exact h'
      · simp [Bad] at h'
  | succ lam ih =>
    intro hl d hd
    obtain ⟨sel, hsel, h1⟩ := hd 0 (Nat.zero_le _)
    have hr := round_main hsel hl i
    simp only [Nat.sub_zero, zero_add] at h1
    rw [← h1] at hr
    have hd' : ∀ k ≤ lam, ∃ sel, ValidSel m ℓ (d (k + 1)) sel ∧
        d (k + 1 + 1) = hptsStep m ℓ (lam - k) (d (k + 1)) sel := by
      intro k hk
      obtain ⟨s, hs, he⟩ := hd (k + 1) (by omega)
      exact ⟨s, hs, by rw [he]; congr 1; omega⟩
    obtain ⟨ihle, ihlt⟩ := ih (by omega) (fun k => d (k + 1)) hd'
    refine ⟨fun k hk => ?_, fun h => ?_⟩
    · rcases k with _ | k
      · exact le_rfl
      · exact (ihle k (by omega)).trans hr.1
    · rcases hr.2 h with h' | h'
      · exact (ihle (lam + 1) le_rfl).trans_lt h'
      · exact (ihlt h').trans_le hr.1

end Podc.SmallBuffersAQT
