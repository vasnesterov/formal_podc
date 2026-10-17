import Papers.PODC2026.ContentObliviousCounting.AnonCountingMain

/-!
# Anonymous counting: pulse complexity (Theorem 13), number of phases, and the distance formula

* `totalPulses_le` (**Theorem 13**): `totalPulses n ≤ 6 n ⌊√(2n)⌋ + 8n`, hence `O(n^1.5)`
  (`totalPulses_le_sqrt`: `≤ 12 n ⌊√n⌋ + 14 n`); `totalPulses_small`: the exact values for
  `n = 1, …, 9` (they agree with exhaustive model checking).
* `lastPhase_spec`: the number of phases `i` satisfies `i(i-1)/2 < n ≤ i(i+1)/2`, i.e.
  `i ≈ √(2n)`, not `⌈√n⌉` as stated in Lemmas 11–12 (`lastPhase_forty`: `n = 40` has 9 phases,
  while `⌈√40⌉ = 7`).
* `paperResult_off_by_one`, `paperResult_two`: the distance formula of the paper (p. 9) is off by
  one for every node probed in a completed phase (including the last leader when it is not the
  original leader), e.g. on the ring of size 2 the node at distance 1 computes 0; it is undefined
  at the original leader (`paperResult_leader`).
-/

namespace Podc.ContentOblivious.AnonCounting

open Cslib.ContentOblivious Finset

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! ## Number of phases -/

/-- The last phase `i` is the unique `i` with `i(i-1)/2 < n ≤ i(i+1)/2`. -/
theorem lastPhase_spec {n : ℕ} (hn : 0 < n) :
    (lastPhase n) * (lastPhase n - 1) / 2 < n ∧ n ≤ lastPhase n * (lastPhase n + 1) / 2 := by
  rw [← tri_eq, ← tri_succ_eq]
  exact ⟨tri_lastPhase_lt hn, lt_tri_lastPhase_succ⟩

/-- Lemmas 11–12 of the paper say that there are `⌈√n⌉` phases; for `n = 40` there are 9 phases,
while `⌈√40⌉ = 7`. -/
theorem lastPhase_forty : lastPhase 40 = 9 ∧ Nat.sqrt 40 = 6 := by
  exact ⟨lastPhase_eq (by decide) (by decide), (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm⟩

/-! ## Pulse complexity -/

lemma phasesCost_le {n I : ℕ} (hI : I * (I - 1) ≤ 2 * n) :
    ∀ j ≤ I, phasesCost n j ≤ (j - 1) * (4 * n) := by
  intro j
  induction j with
  | zero => intro _; simp [phasesCost]
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    simp only [phasesCost]
    split_ifs with h0
    · subst h0; simp [phasesCost]
    · have : j * (j + 1) ≤ I * (I - 1) := by
        have := Nat.mul_le_mul (show j ≤ I - 1 by omega) (show j + 1 ≤ I by omega)
        rw [mul_comm I]; exact this
      have e : (j + 1 - 1) * (4 * n) = (j - 1) * (4 * n) + 4 * n := by
        rw [show j + 1 - 1 = (j - 1) + 1 by omega, add_mul, one_mul]
      omega

/-- **Theorem 13** (pulse complexity `O(n^1.5)`): every execution of the counting algorithm sends
at most `6 n ⌊√(2n)⌋ + 8 n` pulses. -/
theorem totalPulses_le {n : ℕ} (hn : 0 < n) :
    totalPulses n ≤ 6 * n * Nat.sqrt (2 * n) + 8 * n := by
  set I := lastPhase n with hIdef
  have h1 := tri_lastPhase_lt hn
  have h2 := @lt_tri_lastPhase_succ n
  have hI1 := one_le_lastPhase hn
  rw [← hIdef] at h1 h2 hI1
  simp only [tri_succ] at h2
  have h3 := two_mul_tri I
  have hII : I * (I - 1) ≤ 2 * n := by omega
  have hP := phasesCost_le hII I le_rfl
  have hC : lastCount n ≤ I - 1 := by
    show n - 1 - tri (lastPhase n) ≤ _; rw [← hIdef]; omega
  have hCC : lastCount n * (lastCount n + 1) ≤ 2 * n := by
    have := Nat.mul_le_mul hC (show lastCount n + 1 ≤ I by omega)
    rw [mul_comm (I - 1)] at this; omega
  have hlen : (Nat.digits 2 (lastCount n)).length ≤ I - 1 :=
    ((Nat.digits_length_le_iff (by norm_num) _).2 (Nat.lt_two_pow_self)).trans hC
  have hsq : I - 1 ≤ Nat.sqrt (2 * n) := by
    rw [Nat.le_sqrt]
    have := Nat.mul_le_mul_left (I - 1) (show I - 1 ≤ I by omega)
    rw [mul_comm (I - 1) I] at this; omega
  unfold totalPulses
  rw [← hIdef]
  have e1 : 2 * n * (Nat.digits 2 (lastCount n)).length ≤ 2 * n * (I - 1) :=
    Nat.mul_le_mul_left _ hlen
  have e2 : 6 * n * (I - 1) ≤ 6 * n * Nat.sqrt (2 * n) := Nat.mul_le_mul_left _ hsq
  nlinarith

lemma sqrt_two_mul_le (n : ℕ) : Nat.sqrt (2 * n) ≤ 2 * Nat.sqrt n + 1 := by
  have h := Nat.lt_succ_sqrt n
  have : Nat.sqrt (2 * n) < 2 * Nat.sqrt n + 2 := by
    rw [Nat.sqrt_lt]; nlinarith
  omega

/-- **Theorem 13**, in the form `O(n^1.5)`. -/
theorem totalPulses_le_sqrt {n : ℕ} (hn : 0 < n) :
    totalPulses n ≤ 12 * n * Nat.sqrt n + 14 * n := by
  have h1 := totalPulses_le hn
  have h2 := Nat.mul_le_mul_left (6 * n) (sqrt_two_mul_le n)
  nlinarith

lemma totalPulses_of {n i : ℕ} (h1 : tri i < n) (h2 : n ≤ tri (i + 1)) :
    totalPulses n = phasesCost n i + (n - 1 - tri i) * (n - 1 - tri i + 1) + 4 * n +
      2 * n * (Nat.digits 2 (n - 1 - tri i)).length + 2 * n := by
  simp only [totalPulses, lastCount, lastPhase_eq h1 h2]

/-- The exact pulse counts for `n = 1, …, 9` (they coincide with the totals found by exhaustive
model checking of the pseudo-code: 6, 18, 34, 48, 70, 98, 104, 134, 170). -/
theorem totalPulses_small :
    totalPulses 1 = 6 ∧ totalPulses 2 = 18 ∧ totalPulses 3 = 34 ∧ totalPulses 4 = 48 ∧
    totalPulses 5 = 70 ∧ totalPulses 6 = 98 ∧ totalPulses 7 = 104 ∧ totalPulses 8 = 134 ∧
    totalPulses 9 = 170 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [totalPulses_of (i := 1) (by decide) (by decide)]; norm_num [phasesCost, tri]
  · rw [totalPulses_of (i := 2) (by decide) (by decide)]; norm_num [phasesCost, tri]
  · rw [totalPulses_of (i := 2) (by decide) (by decide)]; norm_num [phasesCost, tri]
  · rw [totalPulses_of (i := 3) (by decide) (by decide)]; norm_num [phasesCost, tri]
  · rw [totalPulses_of (i := 3) (by decide) (by decide)]; norm_num [phasesCost, tri]
  · rw [totalPulses_of (i := 3) (by decide) (by decide)]; norm_num [phasesCost, tri]
  · rw [totalPulses_of (i := 4) (by decide) (by decide)]; norm_num [phasesCost, tri]
  · rw [totalPulses_of (i := 4) (by decide) (by decide)]; norm_num [phasesCost, tri]
  · rw [totalPulses_of (i := 4) (by decide) (by decide)]; norm_num [phasesCost, tri]

/-! ## The distance formula of the paper -/

lemma paperDist_eq {i N m k : ℕ} (hm : m < i) :
    paperDist i N (some m) k = some (corrDist i N (some m) k - 1) := by
  simp [paperDist, corrDist, hm, Nat.sub_sub]

lemma final_st {n : ℕ} [NeZero n] {ℓ : ZMod n} {c : Cfg n}
    (hc : anonCount.Reach (oriented n) (leaderInput ℓ) c) (hf : anonCount.Final (oriented n) c)
    (v : ZMod n) :
    terminated (c.st v) = true ∧ (c.st v).phase = lastPhase n ∧
      (c.st v).myPhase = mphF (lastPhase n) (n - 1) (pos ℓ v) := by
  rw [(final_matches hc hf).1 v]
  simp only [absFinal]
  split_ifs with h <;> simp [h, gst, fst, lst, nst, terminated]

/-- The paper's distance formula (p. 9) is off by one at every node that was probed in a completed
phase (`myPhase < i`): it yields the clockwise distance minus one. -/
theorem paperResult_off_by_one {n : ℕ} [NeZero n] (ℓ : ZMod n) (c : Cfg n)
    (hc : anonCount.Reach (oriented n) (leaderInput ℓ) c) (hf : anonCount.Final (oriented n) c)
    (v : ZMod n) {m : ℕ} (hm : (c.st v).myPhase = some m) (hmI : m < lastPhase n) :
    paperResult (c.st v) = some ((v - ℓ).val - 1) := by
  obtain ⟨hterm, hph, -⟩ := final_st hc hf v
  have hres := (anonCount_final ℓ c hc hf).2.1 v
  change result (c.st v) = _ at hres
  simp only [result, hterm, hph, hm, ite_true, Option.some.injEq, Prod.mk.injEq] at hres
  simp only [paperResult, hterm, hph, hm, ite_true, paperDist_eq hmI, hres.2]

/-- At the original leader the paper's formula is undefined (`myPhase` was never written). -/
theorem paperResult_leader {n : ℕ} [NeZero n] (ℓ : ZMod n) (c : Cfg n)
    (hc : anonCount.Reach (oriented n) (leaderInput ℓ) c) (hf : anonCount.Final (oriented n) c) :
    (c.st ℓ).myPhase = none ∧ paperResult (c.st ℓ) = none := by
  obtain ⟨hterm, hph, hmp⟩ := final_st hc hf ℓ
  rw [pos_self, mphF_zero' rfl] at hmp
  exact ⟨hmp, by simp [paperResult, hterm, hmp, paperDist]⟩

/-- **Counterexample to the distance formula of the paper**: on every ring of size `n ≥ 2`, in
every final configuration, the clockwise neighbour of the leader (at distance 1) computes the
distance 0 with the paper's formula. -/
theorem paperResult_wrong {n : ℕ} [NeZero n] (hn : 2 ≤ n) (ℓ : ZMod n) (c : Cfg n)
    (hc : anonCount.Reach (oriented n) (leaderInput ℓ) c) (hf : anonCount.Final (oriented n) c) :
    paperResult (c.st (ℓ + 1)) = some 0 ∧ (ℓ + 1 - ℓ).val = 1 := by
  have hp1 : pos ℓ (ℓ + 1) = 1 := by
    have := pos_natCast ℓ (p := 1) (by omega); simpa using this
  have hpos1 : (ℓ + 1 - ℓ).val = 1 := hp1
  have hI : 2 ≤ lastPhase n := by
    have h1 := @lt_tri_lastPhase_succ n
    have h2 := one_le_lastPhase (n := n) (by omega)
    by_contra h
    have h3 : lastPhase n = 1 := by omega
    rw [h3] at h1; simp [tri] at h1; omega
  have hmp : (c.st (ℓ + 1)).myPhase = some 1 := by
    rw [(final_st hc hf _).2.2, hp1, mphF_le le_rfl]
    · rw [phaseOf_eq (k := 1) (by simp [tri]) (by simp [tri])]
    · have := tri_mono hI; simp [tri] at this ⊢; omega
  refine ⟨?_, hpos1⟩
  rw [paperResult_off_by_one ℓ c hc hf _ hmp (by omega), hpos1]

/-- The counterexample on the ring of size 2: the node `1` (at distance 1 from the leader `0`)
computes the distance `0` with the paper's formula, in every final configuration; final
configurations exist. -/
theorem paperResult_two (c : Cfg 2)
    (hc : anonCount.Reach (oriented 2) (leaderInput 0) c) (hf : anonCount.Final (oriented 2) c) :
    paperResult (c.st 1) = some 0 ∧ anonCount.result (c.st 1) = some (2, 1) := by
  have h := paperResult_wrong le_rfl (0 : ZMod 2) c hc hf
  simp only [zero_add] at h
  refine ⟨h.1, ?_⟩
  have := (anonCount_final (0 : ZMod 2) c hc hf).2.1 1
  have e : (1 - 0 : ZMod 2).val = 1 := rfl
  rw [e] at this; exact this

/-! ## Lemma 10 (4)–(5), read off in the final configuration -/

/-- The variables `myPhase` and `relayed` in every final configuration (the content of
Lemma 10 (4)–(5) for all phases; `relayed` is one more than in Lemma 10 because the completion probe
of the last phase is relayed by every node except the last leader). Positions are clockwise
distances from the leader; the last leader sits at position `tri i = i(i-1)/2`. -/
theorem final_data {n : ℕ} [NeZero n] (ℓ : ZMod n) (c : Cfg n)
    (hc : anonCount.Reach (oriented n) (leaderInput ℓ) c) (hf : anonCount.Final (oriented n) c)
    (v : ZMod n) :
    (c.st v).phase = lastPhase n ∧ (c.st v).counted = true ∧
    ((v - ℓ).val = 0 → (c.st v).myPhase = none) ∧
    ((v - ℓ).val ≠ 0 → (v - ℓ).val = tri (lastPhase n) →
      (c.st v).myPhase = some (lastPhase n - 1) ∧ (c.st v).relayed = 0) ∧
    ((v - ℓ).val ≠ 0 → (v - ℓ).val < tri (lastPhase n) →
      (c.st v).myPhase = some (phaseOf (v - ℓ).val) ∧
        (c.st v).relayed = tri (phaseOf (v - ℓ).val + 1) - (v - ℓ).val + 1) ∧
    (tri (lastPhase n) < (v - ℓ).val →
      (c.st v).myPhase = some (lastPhase n) ∧ (c.st v).relayed = n - (v - ℓ).val) := by
  change _ ∧ _ ∧ (pos ℓ v = 0 → _) ∧ (pos ℓ v ≠ 0 → pos ℓ v = _ → _) ∧
    (pos ℓ v ≠ 0 → pos ℓ v < _ → (c.st v).myPhase = some (phaseOf (pos ℓ v)) ∧
      (c.st v).relayed = tri (phaseOf (pos ℓ v) + 1) - pos ℓ v + 1) ∧
    (_ < pos ℓ v → _ ∧ (c.st v).relayed = n - pos ℓ v)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hp : pos ℓ v < n := pos_lt ℓ v
  have htri := tri_lastPhase_lt hn
  have hI1 := one_le_lastPhase hn
  rw [(final_matches hc hf).1 v]
  have ePh : ((absFinal n).st (pos ℓ v)).phase = lastPhase n := by
    simp only [absFinal]; split_ifs <;> rfl
  have eCo : ((absFinal n).st (pos ℓ v)).counted = true := by
    simp only [absFinal]; split_ifs <;> simp [gst, fst, lst, nst, lead] <;>
      first | omega | exact decide_eq_true (by omega)
  have eMp : ((absFinal n).st (pos ℓ v)).myPhase = mphF (lastPhase n) (n - 1) (pos ℓ v) := by
    simp only [absFinal]; split_ifs with h <;> simp [gst, fst, lst, nst, h]
  have eRe : ((absFinal n).st (pos ℓ v)).relayed =
      relF (lastPhase n) (n - 1) (pos ℓ v) + if pos ℓ v = tri (lastPhase n) then 0 else 1 := by
    simp only [absFinal]; split_ifs with h h' h' <;> simp [gst, fst, lst, nst, h] <;> simp_all [lead]
  rw [ePh, eCo, eMp, eRe]
  refine ⟨rfl, rfl, fun h0 => mphF_zero' h0, fun h0 hL => ?_, fun h0 h => ?_, fun h => ?_⟩
  · have hI2 : 2 ≤ lastPhase n := by
      by_contra hc'; obtain h | h : lastPhase n = 0 ∨ lastPhase n = 1 := by omega
      · rw [h] at hL; simp [tri] at hL; exact h0 hL
      · rw [h] at hL; simp [tri] at hL; exact h0 hL
    rw [hL, mphF_le (by omega) le_rfl, phaseOf_eq (k := lastPhase n - 1), relF_lead]
    · simp
    · exact tri_lt_tri (by omega) (by omega)
    · rw [show lastPhase n - 1 + 1 = lastPhase n by omega]
  · rw [mphF_le (by omega) h.le, relF_le (by omega) h.le, if_neg (by omega)]
    exact ⟨rfl, rfl⟩
  · rw [mphF_mid h (by omega), relF_mid h (by omega), if_neg (by omega)]
    exact ⟨rfl, by omega⟩

end Podc.ContentOblivious.AnonCounting
