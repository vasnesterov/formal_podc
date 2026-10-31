import Papers.PODC2020.NullMessagesByzantine.Consensus

/-!
# Theorem 2.1 (1)–(3): failure-free behaviour and communication

* `ff_status_three`, `ff_decides_maj`: in failure-free runs every process decides at time 3
  (and not before) on the majority value `MAJ(inputs)` (Theorem 2.1 (1) time, (3));
* `ff_msgsAt_eq_zero`: in failure-free runs nothing is sent from round 3 on, in particular the
  base protocol never sends a message;
* `ff_bits_le`: in failure-free runs at most `n (t + 1.5)` bits are sent in total
  (Theorem 2.1 (1));
* `layer_bits_le`: in every run, correct processes send at most `n (t + 1.5) + 2 n²` bits during
  the four layer rounds (Theorem 2.1 (2)); the base protocol starts at time 4 (`status_base`).

Every layer message is a single bit (`Bool`), so the number of layer bits is the number of layer
messages. Messages a process "sends to itself" are not counted (there are none in the model).
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} {M₂ : Type*} (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool)
  (s : Scenario (Fin n) Bool (Msg M₂))

-- CSLib candidate: message counting for `LockStep` protocols on the complete graph.
/-- Number of messages correct processes send in round `r` (round `r + 1` of the paper). -/
noncomputable def msgsAt {I M O : Type*} (alg : Protocol (Fin n) I M O) (s : Scenario (Fin n) I M)
    (r : ℕ) : ℕ :=
  ∑ p ∈ s.honestFinset,
    (univ.filter fun q => q ≠ p ∧ (alg.send p (s.input p) (hist ⊤ alg s r p) q).isSome).card

/-- Nothing is received from oneself. -/
lemma lmsg_self (sr : Bool) {k r : ℕ} (hk : k < r) (p : Fin n) :
    lmsg (H sr t B s r p) k p = none := by
  rw [lmsg_hist sr t B s hk]; simp [deliver]

/-! ### Failure-free runs -/

section FailureFree

variable (hrel : s.Reliable) (hff : s.byz = ∅)
include hrel hff

/-- In a failure-free run every council member recommends `MAJ(inputs)`. -/
lemma ff_recOf {j : Fin n} (hj : council t j) :
    recOf j (s.input j) (H true t B s 1 j) = maj s.input := by
  unfold recOf; congr 1; funext i
  exact values_honest true t B s hrel (by norm_num) hj (by simp [hff])

/-- In a failure-free run every process receives the unanimous recommendation `MAJ(inputs)`. -/
lemma ff_unanimous {r : ℕ} (hr : 1 < r) (p : Fin n) :
    Unanimous t p (s.input p) (H true t B s r p) (maj s.input) := by
  intro j hj
  rw [recFrom_honest true t B s hrel hr (by simp [hff]) hj (by simp [hff]),
    ff_recOf t B s hrel hff hj]

lemma ff_not_err {r : ℕ} (hr : 1 < r) (p : Fin n) : ¬ Err t p (s.input p) (H true t B s r p) := by
  intro he
  cases hm : maj s.input
  · exact he.2 (hm ▸ ff_unanimous t B s hrel hff hr p)
  · exact he.1 (hm ▸ ff_unanimous t B s hrel hff hr p)

lemma ff_est {r : ℕ} (hr : 1 < r) (p : Fin n) :
    est t p (s.input p) (H true t B s r p) = maj s.input :=
  est_of_unanimous t (ff_unanimous t B s hrel hff hr p)

lemma ff_not_gotErr {r : ℕ} (hr : 2 < r) (p : Fin n) :
    ¬ GotErr true t p (s.input p) (H true t B s r p) := by
  rintro (⟨-, he⟩ | ⟨q, hq⟩)
  · exact ff_not_err t B s hrel hff (by omega) p he
  · by_cases hqp : q = p
    · subst hqp; rw [lmsg_self t B s true (by omega)] at hq; simp at hq
    · rw [lmsg2_honest true t B s hrel hr (by simp [hff]) hqp,
        ite_eq_right (ff_not_err t B s hrel hff (by norm_num) q)] at hq
      simp at hq

lemma ff_not_participates {r : ℕ} (hr : 3 < r) (p : Fin n) :
    ¬ Participates true t p (s.input p) (H true t B s r p) := by
  rintro (⟨-, he⟩ | ⟨q, hq⟩)
  · exact ff_not_gotErr t B s hrel hff (by omega) p he
  · by_cases hqp : q = p
    · subst hqp; rw [lmsg_self t B s true (by omega)] at hq; simp at hq
    · rw [lmsg3_honest true t B s hrel hr (by simp [hff]) hqp,
        ite_eq_right (ff_not_gotErr t B s hrel hff (by norm_num) q)] at hq
      simp at hq

/-- **Theorem 2.1 (1), time.** In failure-free runs every process decides at time 3 … -/
lemma ff_status_three (p : Fin n) :
    status ⊤ (smallCouncil t B) s 3 p = some (maj s.input) ∧
      ∀ r < 3, status ⊤ (smallCouncil t B) s r p = none := by
  refine ⟨?_, fun r hr => status_lt true t B s hr p⟩
  rw [status_three true t B s (ff_not_gotErr t B s hrel hff (by norm_num) p),
    ff_est t B s hrel hff (by norm_num) p]

/-- **Theorem 2.1 (3).** … on the majority value of the inputs. -/
theorem ff_decides_maj (p : Fin n) : Decides ⊤ (smallCouncil t B) s p (maj s.input) := by
  have h := decides_of_not_gotErr true t B s (ff_not_gotErr t B s hrel hff (by norm_num) p)
  rwa [ff_est t B s hrel hff (by norm_num) p] at h

/-- In failure-free runs nothing is sent from round 2 on (rounds 3, 4, … of the paper): the
validation rounds are silent and the base protocol is never started. -/
theorem ff_msgsAt_eq_zero {r : ℕ} (hr : 2 ≤ r) : msgsAt (smallCouncil t B) s r = 0 := by
  unfold msgsAt
  apply sum_eq_zero
  intro p _
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro q - ⟨-, hq⟩
  have hl : (hist ⊤ (smallCouncil t B) s r p).length = r := length_hist _ _ _ _ _
  rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | h4
  · rw [send_round2 _ _ _ hl, ite_eq_right (ff_not_err t B s hrel hff (by norm_num) p)] at hq
    simp at hq
  · rw [send_round3 _ _ _ hl, ite_eq_right (ff_not_gotErr t B s hrel hff (by norm_num) p)] at hq
    simp at hq
  · rw [send_round4 _ _ _ (by omega),
      ite_eq_right (ff_not_participates t B s hrel hff (by omega) p)] at hq
    simp at hq

end FailureFree

/-! ### Counting messages per round -/

lemma card_round0_le (sr : Bool) (p : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂))
    (hl : h.length = 0) :
    2 * (univ.filter fun q => q ≠ p ∧ ((smallCouncilGen sr t B).send p x h q).isSome).card
      ≤ t + 2 := by
  refine le_trans (Nat.mul_le_mul_left 2 (card_le_card ?_)) (two_mul_card_council_par_le t (!x))
  intro q hq
  simp only [mem_filter, mem_univ, true_and] at hq ⊢
  rw [send_round0 _ _ _ hl] at hq
  have := hq.2
  simp only [send0, Option.isSome_map] at this
  split_ifs at this with hc
  · refine ⟨hc.1, ?_⟩
    cases h1 : par q <;> cases x <;> simp_all
  · simp at this

lemma card_round1_le (sr : Bool) (p : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂))
    (hl : h.length = 1) :
    2 * (univ.filter fun q => q ≠ p ∧ ((smallCouncilGen sr t B).send p x h q).isSome).card
      ≤ if council t p then n else 0 := by
  split_ifs with hc
  · refine le_trans (Nat.mul_le_mul_left 2 (card_le_card ?_))
      (two_mul_card_ne_maj_le (values p x h))
    intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq ⊢
    rw [send_round1 _ _ _ hl] at hq
    have := hq.2
    simp only [send1, Option.isSome_map] at this
    split_ifs at this with hc'
    · exact hc'.2
    · simp at this
  · simp only [nonpos_iff_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, card_eq_zero,
      filter_eq_empty_iff, mem_univ, not_and, true_implies]
    intro q _ hq
    rw [send_round1 _ _ _ hl] at hq
    simp [send1, hc] at hq

lemma card_filter_le_n (P : Fin n → Prop) [DecidablePred P] :
    (univ.filter P).card ≤ n := by
  simpa using card_filter_le (univ : Finset (Fin n)) P

lemma two_mul_msgsAt0_le (sr : Bool) :
    2 * msgsAt (smallCouncilGen sr t B) s 0 ≤ n * (t + 2) := by
  have hH : s.honestFinset.card ≤ n := by simpa using card_le_univ s.honestFinset
  unfold msgsAt; rw [mul_sum]
  calc _ ≤ ∑ _p ∈ s.honestFinset, (t + 2) :=
        sum_le_sum fun p _ => card_round0_le t B sr p _ _ (length_hist _ _ _ _ _)
    _ ≤ n * (t + 2) := by rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hH

lemma two_mul_msgsAt1_le (sr : Bool) :
    2 * msgsAt (smallCouncilGen sr t B) s 1 ≤ n * (t + 1) := by
  unfold msgsAt; rw [mul_sum]
  calc _ ≤ ∑ p ∈ s.honestFinset, (if council t p then n else 0) :=
        sum_le_sum fun p _ => card_round1_le t B sr p _ _ (length_hist _ _ _ _ _)
    _ ≤ ∑ p ∈ (univ : Finset (Fin n)), (if council t p then n else 0) :=
        sum_le_sum_of_subset (subset_univ _)
    _ = n * (univ.filter fun j : Fin n => council t j).card := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_comm]
    _ ≤ n * (t + 1) := Nat.mul_le_mul_left _ (card_council_le t)

/-- **Theorem 2.1 (2), communication.** In every run, correct processes send at most
`n (t + 1.5) + 2 n²` bits during the four rounds of the layer (one bit per message). -/
theorem layer_bits_le (sr : Bool) :
    2 * ∑ r ∈ range 4, msgsAt (smallCouncilGen sr t B) s r ≤ n * (2 * t + 3) + 4 * n ^ 2 := by
  have hH : s.honestFinset.card ≤ n := by simpa using card_le_univ s.honestFinset
  have h0 := two_mul_msgsAt0_le t B s sr
  have h1 := two_mul_msgsAt1_le t B s sr
  have hk : ∀ r, msgsAt (smallCouncilGen sr t B) s r ≤ n ^ 2 := by
    intro r
    unfold msgsAt
    calc _ ≤ ∑ _p ∈ s.honestFinset, n := sum_le_sum fun _ _ => card_filter_le_n _
      _ ≤ n ^ 2 := by rw [sum_const, smul_eq_mul, sq]; exact Nat.mul_le_mul_right _ hH
  simp only [sum_range_succ, sum_range_zero, zero_add]
  have := hk 2
  have := hk 3
  nlinarith

/-- **Theorem 2.1 (1), communication.** In failure-free runs at most `n (t + 1.5)` bits are sent
in the whole run (all of them in the first two rounds). -/
theorem ff_bits_le (hrel : s.Reliable) (hff : s.byz = ∅) (R : ℕ) :
    2 * ∑ r ∈ range R, msgsAt (smallCouncil t B) s r ≤ n * (2 * t + 3) := by
  have key : ∀ R, ∑ r ∈ range R, msgsAt (smallCouncil t B) s r ≤
      msgsAt (smallCouncil t B) s 0 + msgsAt (smallCouncil t B) s 1 := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
      rw [sum_range_succ]
      rcases (show R = 0 ∨ R = 1 ∨ 2 ≤ R by omega) with rfl | rfl | h
      · simp
      · simp
      · rw [ff_msgsAt_eq_zero t B s hrel hff h]; omega
  have h0 := two_mul_msgsAt0_le t B s true
  have h1 := two_mul_msgsAt1_le t B s true
  have := key R
  nlinarith

end Podc.NullMessagesByzantine
