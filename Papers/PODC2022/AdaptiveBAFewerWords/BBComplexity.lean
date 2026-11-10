import Papers.PODC2022.AdaptiveBAFewerWords.BBCorrect

/-!
# Section 5.1 of [CKS22]: the vetting part costs `O(n(f + 1))` words

With the repaired relay rule, `n ≥ 2t + 1` and `|F| = f ≤ t`, the correct processes send at most
`n (f + 4)` messages (= words, thanks to threshold signatures) in round 1 and the `n` phases of
Algorithm 1 (messages to oneself included):

* round 1: at most `n` (the sender's broadcast);
* a phase with a Byzantine leader: at most `n` (one answer per correct process);
* a silent phase (correct leader holding a value): `0`;
* a non-silent phase: at most `3n`, and (`nonSilent_unique`, the key fact of Section 5.1) after the
  first non-silent phase every later phase with a correct leader is silent.

No assumption on the adversary (unforgeability) is needed.
-/

set_option linter.unusedSectionVars false

namespace Podc.AdaptiveBAFewerWords.BB

open Finset

variable {n : ℕ} {V : Type} [DecidableEq V] [NeZero n] (t : ℕ) (rule : Rule) (sc : Scenario n V)

/-- **Section 5.1 of [CKS22]** (key fact; repaired rule): after a non-silent phase `j`, every later
phase `j'` with a correct leader is silent. -/
theorem silent_after (hn : 2 * t < n) (hF : sc.F.card ≤ t) {j j' : ℕ} (hj1 : 1 ≤ j)
    (hj : NonSilent t .fixed sc j) (hjj' : j < j') (hl : ldr (n := n) j' ∉ sc.F) :
    ¬ NonSilent t .fixed sc j' := by
  rintro ⟨-, hv⟩
  obtain ⟨x, hx, -⟩ := lemma9 t sc hn hF j hj (ldr j') hl
  have hj' : vPh t .fixed sc j (ldr j') ≠ none := by
    have : j = (j - 1) + 1 := by omega
    rw [this, vPh_succ, step, ← this, hx]
    simp
  exact vPh_mono t _ sc (by omega) _ hj' hv

/-- At most one phase in `[1, n]` is non-silent. -/
theorem nonSilent_unique (hn : 2 * t < n) (hF : sc.F.card ≤ t) :
    ((Icc 1 n).filter (NonSilent t .fixed sc)).card ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_Icc] at ha hb
  by_contra hab
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact silent_after t sc hn hF ha.1.1 ha.2 h hb.2.1 hb.2
  · exact silent_after t sc hn hF hb.1.1 hb.2 h ha.2.1 ha.2

lemma sum_ite_eq_left (ℓ : Fin n) :
    ∑ u : Fin n, ∑ _w : Fin n, (if u = ℓ then 1 else 0) = n := by
  simp [sum_ite_eq']

lemma sum_ite_eq_right (ℓ : Fin n) :
    ∑ _u : Fin n, ∑ w : Fin n, (if w = ℓ then 1 else 0) = n := by
  simp [sum_ite_eq']

/-- Words sent by correct processes in phase `j`. -/
theorem phaseWords_le (j : ℕ) :
    phaseWords t rule sc j ≤
      if ldr (n := n) j ∈ sc.F then n else if NonSilent t rule sc j then 3 * n else 0 := by
  unfold phaseWords
  split_ifs with hl hns
  · calc _ ≤ ∑ u ∈ univ.filter (· ∉ sc.F), ∑ w : Fin n, (if w = ldr (n := n) j then 1 else 0) := by
          apply sum_le_sum; intro u hu; apply sum_le_sum; intro w _
          simp only [mem_filter, mem_univ, true_and] at hu
          have hu' : u ≠ ldr j := fun h => hu (h ▸ hl)
          simp only [reqH, relH, hu', false_and, ite_false, List.length_nil, zero_add, repH]
          split_ifs <;> simp_all
      _ ≤ ∑ u : Fin n, ∑ w : Fin n, (if w = ldr (n := n) j then 1 else 0) :=
          sum_le_sum_of_subset (filter_subset _ _)
      _ = n := sum_ite_eq_right _
  · calc _ ≤ ∑ u ∈ univ.filter (· ∉ sc.F), ∑ w : Fin n,
          ((if u = ldr (n := n) j then 1 else 0) + (if w = ldr (n := n) j then 1 else 0) +
            (if u = ldr (n := n) j then 1 else 0)) := by
          apply sum_le_sum; intro u _; apply sum_le_sum; intro w _
          gcongr
          · simp only [reqH]; split_ifs <;> simp_all
          · simp only [repH]; split_ifs <;> simp_all
          · simp only [relH]; split_ifs with h1 h2
            · cases pick t rule sc.sender j (inboxRep sc j (vPh t rule sc (j - 1))) <;> simp
            · exact absurd h1.1 h2
            · simp
            · simp
      _ ≤ ∑ u : Fin n, ∑ w : Fin n,
          ((if u = ldr (n := n) j then 1 else 0) + (if w = ldr (n := n) j then 1 else 0) +
            (if u = ldr (n := n) j then 1 else 0)) := sum_le_sum_of_subset (filter_subset _ _)
      _ = 3 * n := by
          simp only [sum_add_distrib, sum_ite_eq_left, sum_ite_eq_right]; ring
  · apply le_of_eq
    apply sum_eq_zero; intro u _; apply sum_eq_zero; intro w _
    have hv : vPh t rule sc (j - 1) (ldr j) ≠ none := fun h => hns ⟨hl, h⟩
    have hr : reqOut sc j (vPh t rule sc (j - 1)) (ldr j) u = [] := by
      simp [reqOut, hl, reqH, hv]
    have hu : ¬ (u = ldr j ∧ vPh t rule sc (j - 1) u = none) := by
      rintro ⟨rfl, h⟩; exact hv h
    simp only [reqH, repH, relH, hr, hu, ite_false]
    simp

/-- **Section 5.1 of [CKS22]** (repaired rule, `n ≥ 2t + 1`, `|F| ≤ t`): the correct processes send
at most `n (f + 4) ≤ 4 n (f + 1)` words in lines 1-8 of Algorithm 1, where `f = |F|`. -/
theorem words_le (hn : 2 * t < n) (hF : sc.F.card ≤ t) :
    words t .fixed sc ≤ n * (sc.F.card + 4) := by
  unfold words
  have h0 : ∑ u ∈ univ.filter (· ∉ sc.F), ∑ w : Fin n, (initH sc u w).length ≤ n := by
    calc _ ≤ ∑ u : Fin n, ∑ w : Fin n, (if u = sc.sender then 1 else 0) := by
          refine (sum_le_sum_of_subset (filter_subset _ _)).trans (sum_le_sum fun u _ => ?_)
          apply sum_le_sum; intro w _
          simp only [initH]; split_ifs <;> simp
      _ = n := sum_ite_eq_left _
  have hph : ∑ j ∈ Icc 1 n, phaseWords t .fixed sc j ≤
      ∑ j ∈ Icc 1 n, ((if ldr (n := n) j ∈ sc.F then n else 0) +
        (if NonSilent t .fixed sc j then 3 * n else 0)) := by
    apply sum_le_sum; intro j _
    refine (phaseWords_le t .fixed sc j).trans ?_
    split_ifs <;> omega
  rw [sum_add_distrib, sum_ite, sum_ite, sum_const_zero, sum_const_zero, sum_const, sum_const,
    smul_eq_mul, smul_eq_mul] at hph
  have hB : ((Icc 1 n).filter fun j => ldr (n := n) j ∈ sc.F).card ≤ sc.F.card := by
    apply card_le_card_of_injOn ldr
    · intro j hj; exact (mem_filter.mp hj).2
    · intro a ha b hb hab
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha hb
      have h := congrArg Fin.val hab
      simp only [ldr] at h
      have hn0 := NeZero.pos n
      rcases Nat.lt_or_ge a n with ha' | ha' <;> rcases Nat.lt_or_ge b n with hb' | hb'
      · rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h
      · have : b = n := by omega
        subst this; rw [Nat.mod_eq_of_lt ha', Nat.mod_self] at h; omega
      · have : a = n := by omega
        subst this; rw [Nat.mod_eq_of_lt hb', Nat.mod_self] at h; omega
      · omega
  have hN := nonSilent_unique t sc hn hF
  have h1 := Nat.mul_le_mul_right n hB
  have h2 := Nat.mul_le_mul_right (3 * n) hN
  nlinarith

end Podc.AdaptiveBAFewerWords.BB
