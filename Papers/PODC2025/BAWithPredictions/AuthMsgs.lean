import Papers.PODC2025.BAWithPredictions.AuthBA

/-!
# Authenticated BA with classification — message complexity (Theorem 6) and non-vacuity

The paper counts every chain broadcast in an instance of Algorithm 6 as one message; our
algorithm bundles the chains of all instances sent to one receiver in one round into one
`Msg.chains` message. `msgCost` restores the paper's count (a `chains` message costs the number
of its chains, every other message costs `1`), and `sentCost E p N` is the cost of all messages
sent by `p` (to all processes, itself included) in rounds `< N`.

* `theorem6_messages_per_process`: in every execution (no hypothesis on the classification),
  every process sends at most `2k + 1 + n + 2n²` messages (paper: `2k + 1 + n + 2n|C| ∈ O(n²)`).
* `theorem6_messages`: under the hypotheses of Theorem 6, the honest processes send at most
  `n(2k + 1) + (3k + 1) n (6k + 3)` messages in total (`O(nk²)`); the same bound holds for
  `roundMsgs` (bundled messages, `roundMsgs_le`).
* `exists_run`: non-vacuity — for all inputs there is a synchronous authenticated execution
  (all processes honest); with correct classifications, `k = t = 0` satisfies all hypotheses.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions.AuthBA

open Finset Cslib.Byzantine.PartialSync

variable {P V : Type*} [Fintype P] [LinearOrder P] [LinearOrder V]

/-- The paper's message count of a (possibly absent) message. -/
def msgCost : Option (Msg P V) → ℕ
  | some (.chains S) => S.card
  | some _ => 1
  | none => 0

section Cost

variable {k t : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}
  (E : RoundRun (alg (P := P) (V := V) k t) F inp)

/-- The cost of the messages sent by `p` in rounds `< N`. -/
noncomputable def sentCost (p : P) (N : ℕ) : ℕ :=
  ∑ r ∈ range N, ∑ q, msgCost ((alg k t).send r p (E.s r p) q)

/-- The cost of the messages sent by `p` in round `r`. -/
noncomputable def roundCost (r : ℕ) (p : P) : ℕ := ∑ q, msgCost ((alg k t).send r p (E.s r p) q)

theorem one_le_msgCost {r : ℕ} {p q : P} {st : St P V}
    (h : (alg k t).send r p st q ≠ none) : 1 ≤ msgCost ((alg k t).send r p st q) := by
  rw [send_eq] at h ⊢
  split_ifs at h ⊢
  · simp [msgCost]
  · exact absurd rfl h
  · simp only [msgCost]; exact card_pos.mpr ‹_›
  · exact absurd rfl h
  · cases hc : st.cc with
    | none => rw [hc] at h; simp at h
    | some _ => simp [msgCost]
  · exact absurd rfl h

theorem roundCost_zero (p : P) : roundCost E 0 p ≤ 2 * k + 1 := by
  unfold roundCost
  have : ∀ q, msgCost ((alg k t).send 0 p (E.s 0 p) q) =
      if pos (inp p).2 q ≤ 2 * k + 1 then 1 else 0 := by
    intro q; rw [send_eq, ifp rfl, c_eq]; split_ifs <;> rfl
  simp only [this, sum_boole, Nat.cast_id]
  have h := card_le_card_of_injOn (pos (inp p).2) (t := Icc 1 (2 * k + 1))
    (s := univ.filter fun q => pos (inp p).2 q ≤ 2 * k + 1)
    (fun q hq => mem_Icc.mpr ⟨one_le_pos _ _, (mem_filter.mp hq).2⟩)
    ((pos_injective _).injOn)
  simpa using h

theorem roundCost_bb {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ k + 1) (p : P) :
    roundCost E r p = Fintype.card P * (E.s r p).out.card := by
  unfold roundCost
  have : ∀ q, msgCost ((alg k t).send r p (E.s r p) q) = (E.s r p).out.card := by
    intro q
    rw [send_eq, ifn (by omega), ifp h2]
    split_ifs with h
    · rfl
    · simp [msgCost, not_nonempty_iff_eq_empty.mp h]
  simp [this]

theorem roundCost_plur (p : P) :
    roundCost E (k + 2) p ≤ if (cert E p).isSome then Fintype.card P else 0 := by
  unfold roundCost
  have : ∀ q, msgCost ((alg k t).send (k + 2) p (E.s (k + 2) p) q) =
      if (cert E p).isSome then 1 else 0 := by
    intro q
    rw [send_eq, ifn (by omega), ifn (by omega), ifp rfl, cc_eq E (by omega)]
    cases cert E p <;> rfl
  simp only [this]
  split_ifs <;> simp

theorem roundCost_late {r : ℕ} (h : k + 2 < r) (p : P) : roundCost E r p = 0 := by
  unfold roundCost
  apply sum_eq_zero
  intro q _
  rw [send_eq, ifn (by omega), ifn (by omega), ifn (by omega)]
  rfl

/-- The chains sent in round `r + 1` correspond to values newly added to the sets `X_p[s]` at the
end of round `r` (and only processes with a certificate send chains). -/
theorem card_out_succ {r : ℕ} (hr : r ≤ k + 1) (p : P) :
    (E.s (r + 1) p).out.card ≤
      if (cert E p).isSome then ∑ s, ((E.s (r + 1) p).X s \ (E.s r p).X s).card else 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · rw [out_one]
    cases hc : cert E p with
    | none => simp
    | some S =>
      simp only [card_singleton, Option.isSome_some, ↓reduceIte]
      refine le_trans ?_ (single_le_sum (f := fun s => ((E.s (0 + 1) p).X s \ (E.s 0 p).X s).card)
        (fun _ _ => Nat.zero_le _) (mem_univ p))
      simp [X_one, X_zero, hc]
  · rw [out_succ_bb E h0 hr]
    cases hc : cert E p with
    | none => simp
    | some cc =>
      simp only [Option.isSome_some, ↓reduceIte]
      unfold relayOut
      refine card_biUnion_le.trans (sum_le_sum fun s _ => ?_)
      rw [X_succ_bb E h0 hr]
      exact card_image_le

theorem sum_card_sdiff (p s : P) (m : ℕ) :
    ∑ r ∈ range m, ((E.s (r + 1) p).X s \ (E.s r p).X s).card = ((E.s m p).X s).card := by
  induction m with
  | zero => simp [X_zero]
  | succ m ih =>
    rw [sum_range_succ, ih, card_sdiff_of_subset (X_mono_succ E m p s)]
    have := card_le_card (X_mono_succ E m p s)
    omega

/-- Chains of instance `s` sent in round `r + 1` correspond to values newly added to `X_p[s]`. -/
theorem card_out_inst_succ {r : ℕ} (hr : r ≤ k + 1) (p s : P) :
    ((E.s (r + 1) p).out.filter (·.s = s)).card ≤
      if (cert E p).isSome then ((E.s (r + 1) p).X s \ (E.s r p).X s).card else 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · rw [out_one]
    cases hc : cert E p with
    | none => simp
    | some S =>
      rw [X_zero, sdiff_empty, X_one, hc]
      by_cases hps : s = p
      · subst hps; simp only [Option.isSome_some, and_self, ↓reduceIte, card_singleton]
        exact (card_filter_le _ _).trans (card_singleton _).le
      · rw [filter_singleton, ifn (Ne.symm hps)]; simp
  · rw [out_succ_bb E h0 hr]
    cases hc : cert E p with
    | none => simp
    | some cc =>
      simp only [Option.isSome_some, ↓reduceIte]
      rw [X_succ_bb E h0 hr]
      have : ((relayOut t r p (E.rcv r p) (E.s r p).X
          (fun s => step (accSet t r p (E.rcv r p) s) ((E.s r p).X s)) cc).filter (·.s = s)) ⊆
          ((step (accSet t r p (E.rcv r p) s) ((E.s r p).X s)) \ (E.s r p).X s).image
            (fun x => (⟨s, x, relayLinks t r p (E.rcv r p) s x ++ [(p, cc)]⟩ : Chain P V)) := by
        intro ch hch
        obtain ⟨hch, hs⟩ := mem_filter.mp hch
        obtain ⟨s', v, hv, hv', rfl⟩ := mem_relayOut.mp hch
        cases hs
        exact mem_image.mpr ⟨v, mem_sdiff.mpr ⟨hv, hv'⟩, rfl⟩
      exact (card_le_card this).trans card_image_le

/-- **Observation 3** (counting). In the broadcast instance with sender `p_s`, a process broadcasts
at most `|X_p[s]| ≤ 2` chains in total over rounds `1 … k+1` (one per value added to `X_p[s]`),
and none if it has no committee certificate. -/
theorem observation3 (p s : P) :
    ∑ r ∈ range (k + 1), ((E.s (r + 1) p).out.filter (·.s = s)).card ≤
      if (cert E p).isSome then (Xf E p s).card else 0 := by
  refine (sum_le_sum fun r hr => card_out_inst_succ E (by simp at hr; omega) p s).trans ?_
  split_ifs
  · rw [sum_card_sdiff]; exact card_le_card (X_mono E (by omega) p s)
  · simp

theorem observation3_le_two (p s : P) :
    ∑ r ∈ range (k + 1), ((E.s (r + 1) p).out.filter (·.s = s)).card ≤ 2 := by
  refine (observation3 E p s).trans ?_
  split_ifs
  · exact X_card E _ _ _
  · omega

/-- **Observation 3** (no sender certificate). If no committee certificate for `p_s` can exist
(`s ∉ Csup`), or `p_s` is honest without a certificate, no honest process sends any chain of
instance `s`. -/
theorem observation3_noCert (hF : F.card ≤ t) (hA : E.AuthValid auth) {p s : P} (hp : p ∉ F)
    (hs : s ∉ Csup k F inp ∨ (s ∉ F ∧ cert E s = none)) :
    ∑ r ∈ range (k + 1), ((E.s (r + 1) p).out.filter (·.s = s)).card = 0 := by
  have hX : Xf E p s = ∅ := by
    rcases hs with hs | ⟨hs, hc⟩
    · exact Xf_empty_of_notMem_Csup E hF hA hs hp
    · exact Xf_empty_honest E hA hs hc hp
  have := observation3 E p s
  rw [hX, card_empty] at this
  split_ifs at this <;> omega

/-- The cost of `p`'s messages: at most `2k + 1` votes, and, if `p` has a certificate, one chain
per value it ever adds to some `X_p[s]`, sent to all `n` processes, plus `n` plurality
messages. -/
theorem sentCost_le (p : P) (N : ℕ) :
    sentCost E p N ≤ 2 * k + 1 +
      if (cert E p).isSome then Fintype.card P * ∑ s, (Xf E p s).card + Fintype.card P else 0 := by
  have hN : sentCost E p N ≤ ∑ r ∈ range (k + 3), roundCost E r p := by
    unfold sentCost
    rw [← sum_filter_of_ne (p := fun r => r < k + 3) (fun r _ h => by
      by_contra h'; exact h (roundCost_late E (by omega) p))]
    exact sum_le_sum_of_subset (fun r hr => mem_range.mpr (mem_filter.mp hr).2)
  refine hN.trans ?_
  rw [show k + 3 = (k + 1) + 1 + 1 by omega, sum_range_succ, sum_range_succ']
  have hbb : ∑ r ∈ range (k + 1), roundCost E (r + 1) p ≤
      if (cert E p).isSome then Fintype.card P * ∑ s, (Xf E p s).card else 0 := by
    rw [sum_congr rfl fun r hr => roundCost_bb E (by omega) (by simp at hr; omega) p,
      ← mul_sum]
    have hsum : ∑ r ∈ range (k + 1), (E.s (r + 1) p).out.card ≤
        if (cert E p).isSome then ∑ s, (Xf E p s).card else 0 := by
      refine (sum_le_sum fun r hr => card_out_succ E (by simp at hr; omega) p).trans ?_
      split_ifs
      · rw [sum_comm]
        refine sum_le_sum fun s _ => ?_
        rw [sum_card_sdiff]
        exact card_le_card (X_mono E (by omega) p s)
      · simp
    split_ifs at hsum ⊢
    · exact Nat.mul_le_mul_left _ hsum
    · simp at hsum; simp; exact Or.inr hsum
  have h0 := roundCost_zero E p
  have hp := roundCost_plur E p
  rw [show (k + 1) + 1 = k + 2 by omega]
  split_ifs at hbb hp ⊢ <;> omega

/-- **Theorem 6**, per-process message bound (no hypothesis on the classification): every
process sends at most `2k + 1 + n + 2n²` messages (`O(n²)`). -/
theorem theorem6_messages_per_process (p : P) (N : ℕ) :
    sentCost E p N ≤ 2 * k + 1 + Fintype.card P + 2 * Fintype.card P ^ 2 := by
  refine (sentCost_le E p N).trans ?_
  have : ∑ s, (Xf E p s).card ≤ 2 * Fintype.card P := by
    calc ∑ s, (Xf E p s).card ≤ ∑ _s : P, 2 := sum_le_sum fun s _ => X_card E _ _ _
      _ = 2 * Fintype.card P := by simp [mul_comm]
  have := Nat.mul_le_mul_left (Fintype.card P) this
  split_ifs
  · nlinarith
  · omega

/-- Bundled messages (`roundMsgs`) are bounded by the paper's count. -/
theorem roundMsgs_le (N : ℕ) : roundMsgs E N ≤ ∑ p ∈ univ.filter (· ∉ F), sentCost E p N := by
  unfold roundMsgs RoundRun.msgsUpTo sentCost
  rw [sum_comm]
  refine sum_le_sum fun p _ => sum_le_sum fun r _ => ?_
  calc (univ.filter fun q => q ≠ p ∧ (alg k t).send r p (E.s r p) q ≠ none).card
      ≤ (univ.filter fun q => (alg k t).send r p (E.s r p) q ≠ none).card :=
        card_le_card fun q hq => by simp only [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.2⟩
    _ = ∑ q, if (alg k t).send r p (E.s r p) q ≠ none then 1 else 0 := by
        rw [sum_boole]; simp
    _ ≤ ∑ q, msgCost ((alg k t).send r p (E.s r p) q) := sum_le_sum fun q _ => by
        split_ifs with h
        · exact one_le_msgCost h
        · exact Nat.zero_le _

variable (hF : F.card ≤ t) (hsync : E.SyncFrom 0) (hA : E.AuthValid auth)
  (htn : 2 * t < Fintype.card P) (hn : 2 * k + 1 ≤ Fintype.card P - t - k)
  (hk : (mis F fun i => (inp i).2).card ≤ k)

include hF hA hn hk in
/-- **Theorem 6**, total message bound: under the hypotheses, the honest processes send at most
`n(2k + 1) + (3k + 1) · n · (6k + 3)` messages in total (`O(nk²)`). -/
theorem theorem6_messages (N : ℕ) :
    ∑ p ∈ univ.filter (· ∉ F), sentCost E p N ≤
      Fintype.card P * (2 * k + 1) + (3 * k + 1) * (Fintype.card P * (6 * k + 3)) := by
  set n := Fintype.card P
  have hC := lemma24_card' hF hn hk
  have hper : ∀ p ∈ univ.filter (· ∉ F), sentCost E p N ≤
      (2 * k + 1) + n * (6 * k + 3) * (if p ∈ CH E then 1 else 0) := by
    intro p hp
    have hpF := (mem_filter.mp hp).2
    refine (sentCost_le E p N).trans ?_
    split_ifs with hc hc'
    · have hsum : ∑ s, (Xf E p s).card ≤ 2 * (3 * k + 1) := by
        calc ∑ s, (Xf E p s).card = ∑ s ∈ Csup k F inp, (Xf E p s).card := by
              refine (sum_subset (subset_univ _) fun s _ hs => ?_).symm
              rw [Xf_empty_of_notMem_Csup E hF hA hs hpF, card_empty]
          _ ≤ ∑ _s ∈ Csup k F inp, 2 := sum_le_sum fun s _ => X_card E _ _ _
          _ = 2 * (Csup k F inp).card := by rw [sum_const, smul_eq_mul, mul_comm]
          _ ≤ 2 * (3 * k + 1) := by omega
      have := Nat.mul_le_mul_left n hsum
      nlinarith
    · exact absurd (by simp [CH, hpF, hc]) hc'
    · omega
    · omega
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum, sum_boole]
  have h1 : (univ.filter fun p : P => p ∉ F).card ≤ n := card_le_univ _
  have h2 : ((univ.filter fun p : P => p ∉ F).filter fun p => p ∈ CH E).card ≤ 3 * k + 1 := by
    refine (card_le_card fun p hp => ?_).trans hC
    obtain ⟨-, hpCH⟩ := mem_filter.mp hp
    obtain ⟨hpF, hpc⟩ := by simpa [CH] using hpCH
    exact cert_mem_Csup E hF hA hpF hpc
  simp only [Nat.cast_id]
  have := Nat.mul_le_mul_left (n * (6 * k + 3)) h2
  nlinarith

end Cost

/-! ### Non-vacuity -/

section NonVacuity

variable {Msg' S VI VO : Type*} [DecidableEq P]

/-- **Non-vacuity of Theorem 6.** For every input there is a synchronous authenticated execution
of `alg k t` (with no faulty process); with correct classification vectors, `k = t = 0` satisfies
all hypotheses of Theorem 6 (for `n ≥ 1`). -/
theorem exists_run (k t : ℕ) (inp : P → V × (P → Bool)) :
    ∃ E : RoundRun (alg (P := P) (V := V) k t) ∅ inp, E.SyncFrom 0 ∧ E.AuthValid auth :=
  ⟨RoundRun.sync _ ∅ inp fun _ _ _ _ => none, RoundRun.sync_syncFrom _ _ _ _,
    RoundRun.sync_empty_authValid _ _ _ _⟩

theorem hypotheses_satisfiable [Nonempty P] (inp : P → V × (P → Bool))
    (hc : ∀ i, (inp i).2 = correctPred ∅) :
    (∅ : Finset P).card ≤ 0 ∧ 2 * 0 < Fintype.card P ∧ 2 * 0 + 1 ≤ Fintype.card P - 0 - 0 ∧
      (mis ∅ fun i => (inp i).2).card ≤ 0 := by
  have hn := Fintype.card_pos (α := P)
  refine ⟨by simp, by omega, by omega, ?_⟩
  simp [mis, hc]

end NonVacuity

end BAWithPredictions.AuthBA
