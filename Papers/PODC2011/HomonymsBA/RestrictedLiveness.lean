import Papers.PODC2011.HomonymsBA.RestrictedSafety

/-!
# Proposition 18: termination of the consensus algorithm (Figure 7)

Lemmas 36, 37 and Proposition 40, and the main theorem `prop18`.
-/

namespace Podc.HomonymsBA.Restricted

open Finset Classical

variable {n t ℓ : ℕ} {hℓ : 0 < ℓ} {V : Type} {P : Type} [Fintype P]

set_option linter.unusedSectionVars false

variable (R : Run P ℓ V (Msg ℓ V))

local notation "A" => alg n t hℓ V

/-! ### Proper sets -/

lemma proper_mono {r r' : ℕ} (h : r ≤ r') (q : P) :
    (R.st A r q).proper ⊆ (R.st A r' q).proper := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ r' _ ih =>
    refine ih.trans ?_
    rw [proper_succ]
    unfold newProper
    exact Set.subset_union_left.trans Set.subset_union_left

/-- After `gst`, a value in the proper sets of `t + 1` correct processes spreads to all correct
processes. -/
lemma proper_spread (hR : R.Admissible t .psync .restricted) {r : ℕ} (hr : R.gst ≤ r) {v : V}
    (h : t + 1 ≤ ((cor R).filter (fun q => v ∈ (R.st A r q).proper)).card) {p : P}
    (hp : p ∉ R.byz) : v ∈ (R.st A (r + 1) p).proper := by
  rw [proper_succ]
  unfold newProper
  refine Or.inl (Or.inr ?_)
  exact h.trans (countP_inbox_ge R hR.1 hr hp (fun x => v ∈ x.2.proper))

/-- After `gst`, all correct processes have a common proper value (the existential reading of
the "`2t+1` messages and no value `t+1` times" rule). -/
lemma common_proper (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {r : ℕ} (hr : R.gst ≤ r) (v₀ : V) :
    ∃ v, ∀ p, p ∉ R.byz → v ∈ (R.st A (r + 1) p).proper := by
  by_cases h : ∃ v, t + 1 ≤ ((cor R).filter (fun q => v ∈ (R.st A r q).proper)).card
  · obtain ⟨v, hv⟩ := h
    exact ⟨v, fun p hp => proper_spread R hR hr hv hp⟩
  push Not at h
  refine ⟨v₀, fun p hp => ?_⟩
  rw [proper_succ]
  unfold newProper
  refine Or.inr ?_
  have hf := hR.1.card_byz
  have hc := card_cor R hP
  obtain ⟨Q, hQ, hQc⟩ := Finset.exists_subset_card_eq (show 2 * t + 1 ≤ (cor R).card by omega)
  refine ⟨Q.val.map (fun q => (R.id q, out n t hℓ (R.st A r q))), ?_, ?_, fun w => ?_⟩
  · rw [inbox_alg, snd_eq_cor R hR.1 hr hp]
    exact (Multiset.map_le_map (Finset.val_le_iff.2 hQ)).trans (Multiset.le_add_right _ _)
  · simpa using hQc
  · rw [Multiset.countP_map]
    have := h w
    have h2 : (Q.filter (fun q => w ∈ (R.st A r q).proper)).card ≤
        ((cor R).filter (fun q => w ∈ (R.st A r q).proper)).card :=
      card_le_card (filter_subset_filter _ hQ)
    change (Q.filter (fun q => w ∈ (R.st A r q).proper)).card ≤ t
    omega

/-! ### Lemma 36 -/

/-- **Lemma 36.** At the end of a phase `e` with `gst ≤ 8e + 6`, all locks of correct processes
carry the same value. -/
theorem lemma36 (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {e : ℕ} (he : R.gst ≤ 8 * e + 6) {p₁ p₂ : P}
    (hp₁ : p₁ ∉ R.byz) (hp₂ : p₂ ∉ R.byz) {x₁ x₂ : V × ℕ}
    (h₁ : x₁ ∈ (R.st A (8 * e + 8) p₁).locks) (h₂ : x₂ ∈ (R.st A (8 * e + 8) p₂).locks) :
    x₁.1 = x₂.1 := by
  wlog hle : x₁.2 ≤ x₂.2 generalizing p₁ p₂ x₁ x₂
  · exact (this hp₂ hp₁ h₂ h₁ (by omega)).symm
  obtain ⟨hr₁, hw₁⟩ := lock_spec R _ _ _ h₁
  obtain ⟨hr₂, hw₂⟩ := lock_spec R _ _ _ h₂
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · rw [heq] at hw₁
    obtain ⟨q, -, hq1, hq2⟩ := lemma31 R hn hP hR hw₁ hw₂
    exact vote_unique R hq1 hq2
  · by_contra hne
    have hw := (witnesses_relay R hP hR (r := 8 * x₂.2 + 5) (s := 8 * e + 6) (by omega) he
      hp₁ (.vote x₂.1) (4 * x₂.2 + 2)).trans' hw₂
    rw [show 8 * e + 8 = 8 * e + 7 + 1 by ring, locks_succ] at h₁
    unfold newLocks at h₁
    rw [rnd_st, ite_eq_right (by omega), ite_eq_left (by omega)] at h₁
    exact h₁.2 ⟨x₂.1, x₂.2, Ne.symm hne, hlt, hw⟩

/-- A locked value of a correct process is, after `gst`, in the proper set of every correct
process (Case 1 of Lemma 37). -/
theorem lock_proper (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {e : ℕ} (he : R.gst ≤ 8 * e + 6) {q : P}
    {x : V × ℕ} (hx : x ∈ (R.st A (8 * e + 8) q).locks) {p : P} (hp : p ∉ R.byz) :
    x.1 ∈ (R.st A (8 * e + 8) p).proper := by
  have hf := hR.1.card_byz
  obtain ⟨hr, hw⟩ := lock_spec R _ _ _ hx
  obtain ⟨h, hh, hhv⟩ := exists_of_cc R hn hR (lemma30 R hn hR hw).2
  have hB := (lemma30 R hn hR (vote_spec R hhv)).2
  unfold cc at hB
  have hsp : t + 1 ≤ ((cor R).filter (fun q => x.1 ∈ (R.st A (8 * e + 6) q).proper)).card := by
    refine le_trans (by omega) (hB.trans (card_le_card fun q hq => ?_))
    simp only [mem_filter] at hq ⊢
    exact ⟨hq.1, proper_mono R (by omega) q (mem_initOut_propose.1 hq.2).2.1⟩
  exact proper_mono R (by omega) p (proper_spread R hR he hsp hp)

/-- **Lemma 37** (core): in a phase `e + 1` with `gst ≤ 8e + 6`, all correct processes propose a
common value. -/
theorem common_propose (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {e : ℕ} (he : R.gst ≤ 8 * e + 6) (v₀ : V) :
    ∃ v, ∀ q, q ∉ R.byz → CM.propose v ∈ initOut n t (R.st A (8 * (e + 1)) q) := by
  have e8 : 8 * (e + 1) = 8 * e + 8 := by ring
  rw [e8]
  by_cases hl : ∃ q, q ∉ R.byz ∧ ∃ x, x ∈ (R.st A (8 * e + 8) q).locks
  · obtain ⟨q, hq, x, hx⟩ := hl
    refine ⟨x.1, fun q' hq' => mem_initOut_propose.2 ⟨by rw [rnd_st]; omega, ?_, ?_⟩⟩
    · exact lock_proper R hn hP hR he hx hq'
    · intro y hy
      exact lemma36 R hn hP hR he hq' hq hy hx
  · push Not at hl
    obtain ⟨v, hv⟩ := common_proper R hn hP hR (r := 8 * e + 7) (by omega) v₀
    refine ⟨v, fun q hq => mem_initOut_propose.2 ⟨by rw [rnd_st]; omega, hv q hq, ?_⟩⟩
    intro y hy
    exact absurd hy (hl q hq y)

/-! ### Proposition 40: termination -/

/-- **Proposition 40 (termination)**, for a phase `ph` whose leader identifier `k` has no
Byzantine process and with `gst ≤ 8ph - 2`: every correct process has decided by the end of
round `8ph + 6`. -/
theorem decides_in_phase (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {e : ℕ} (he : R.gst ≤ 8 * e + 6)
    (hk : ∀ b ∈ R.byz, R.id b ≠ leader hℓ (e + 1)) (v₀ : V) {p : P} (hp : p ∉ R.byz) :
    ∃ v, (R.st A (8 * (e + 1) + 7) p).decided = some v := by
  set ph := e + 1 with hph
  have hf := hR.1.card_byz
  have hc := card_cor R hP
  have hg : R.gst ≤ 8 * ph := by omega
  -- T4: everybody has `n - t` witnesses for a common proposal
  obtain ⟨v, hv⟩ := common_propose R hn hP hR he v₀
  have hW1 : ∀ q, q ∉ R.byz →
      n - t ≤ witnesses n t (R.inbox A (8 * ph + 1) q) (.propose v) (4 * ph) := by
    intro q hq
    have h := cc_le_witnesses (hℓ := hℓ) R hP hR (k := 4 * ph) (by omega) hq (.propose v)
    rw [show 2 * (4 * ph) + 1 = 8 * ph + 1 by ring] at h
    refine le_trans ?_ h
    unfold cc
    rw [filter_true_of_mem]
    · omega
    · intro q' hq'
      rw [show 2 * (4 * ph) = 8 * ph by ring]
      exact hv q' (by simpa [cor] using hq')
  -- T5: the leaders send lock requests
  have hL5 : ∀ q, q ∉ R.byz → R.id q = leader hℓ ph → ∃ w,
      lockOut n t hℓ (R.st A (8 * ph + 2) q) = some w ∧
        n - t ≤ witnesses n t (R.inbox A (8 * ph + 1) q) (.propose w) (4 * ph) := by
    intro q hq hid
    have hcand : (lockCand n t (R.st A (8 * ph + 2) q)).Nonempty := by
      refine ⟨v, ?_⟩
      simp only [lockCand, Set.mem_ofPred_eq, rnd_st,
        show (8 * ph + 2) / 8 = ph by omega]
      rw [wit_phase R ph 1 rfl q]
      exact hW1 q hq
    obtain ⟨w, hw⟩ := pick_isSome hcand
    have hlo : lockOut n t hℓ (R.st A (8 * ph + 2) q) = some w := by
      unfold lockOut
      rw [rnd_st, id_st, show (8 * ph + 2) / 8 = ph by omega, ite_eq_left ⟨by omega, hid⟩]
      exact hw
    refine ⟨w, hlo, ?_⟩
    have hm := pick_mem hw
    simp only [lockCand, Set.mem_ofPred_eq, rnd_st,
      show (8 * ph + 2) / 8 = ph by omega] at hm
    rwa [wit_phase R ph 1 rfl q] at hm
  -- T6: every correct process receives the same set of lock requests
  set L : Set V := {w | ∃ q, q ∉ R.byz ∧ R.id q = leader hℓ ph ∧
    lockOut n t hℓ (R.st A (8 * ph + 2) q) = some w} with hLdef
  have hL6 : ∀ p, p ∉ R.byz → (R.st A (8 * ph + 4) p).lockRcv = L := by
    intro p hp
    rw [show 8 * ph + 4 = 8 * ph + 3 + 1 by ring, lockRcv_succ, ite_eq_right (by omega),
      lockRcv_succ, ite_eq_left (by omega), show (8 * ph + 2) / 8 = ph by omega]
    ext w
    simp only [Set.mem_ofPred_eq, hLdef]
    constructor
    · rintro ⟨x, hx, hx1, hx2⟩
      rw [inbox_alg, Multiset.mem_add] at hx
      rcases hx with hx | hx
      · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
        have hq' := snd_subset R _ _ (Finset.mem_def.2 hq)
        exact ⟨q, by simpa [cor] using hq', hx1, hx2⟩
      · obtain ⟨b, hb, hbid⟩ := hR.1.adv_id _ _ x hx
        exact absurd (hbid.trans hx1) (hk b hb)
    · rintro ⟨q, hq, hid, hlo⟩
      refine ⟨(R.id q, out n t hℓ (R.st A (8 * ph + 2) q)), ?_, hid, hlo⟩
      rw [inbox_alg, snd_eq_cor R hR.1 (by omega) hp]
      exact Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2
        ⟨q, Finset.mem_def.1 (by simp [cor, hq]), rfl⟩))
  -- T7: relay of the leaders' proposals
  have hL7 : ∀ w ∈ L, ∀ p, p ∉ R.byz → ∀ s, 8 * ph + 2 ≤ s →
      n - t ≤ witnesses n t (R.inbox A (s + 1) p) (.propose w) (4 * ph) := by
    rintro w ⟨q, hq, hid, hlo⟩ p hp s hs
    obtain ⟨w', hw', hW⟩ := hL5 q hq hid
    rw [hlo] at hw'
    cases hw'
    exact hW.trans (witnesses_relay R hP hR (by omega) (by omega) hp _ _)
  -- L is nonempty
  obtain ⟨q₀, hq₀⟩ := hR.1.surj (leader hℓ ph)
  have hq₀c : q₀ ∉ R.byz := fun hb => hk q₀ hb hq₀
  have hLne : L.Nonempty := by
    obtain ⟨w, hw, -⟩ := hL5 q₀ hq₀c hq₀
    exact ⟨w, q₀, hq₀c, hq₀, hw⟩
  obtain ⟨u, hu⟩ := pick_isSome hLne
  -- T8: all correct processes vote `u`
  have hvote : ∀ q, q ∉ R.byz → CM.vote u ∈ initOut n t (R.st A (8 * ph + 4) q) := by
    intro q hq
    have : voteCand n t (R.st A (8 * ph + 4) q) = L := by
      ext w
      simp only [voteCand, Set.mem_ofPred_eq, rnd_st, hL6 q hq,
        show (8 * ph + 4) / 8 = ph by omega]
      rw [wit_phase R ph 3 rfl q]
      exact ⟨fun h => h.1, fun h => ⟨h, hL7 w h q hq (8 * ph + 2) le_rfl⟩⟩
    rw [mem_initOut_vote, rnd_st, this]
    exact ⟨by omega, hu⟩
  -- T9: all correct processes acknowledge `u`
  have hack : ∀ q, q ∉ R.byz → (R.st A (8 * ph + 6) q).ackVal = some u := by
    intro q hq
    have hWv : n - t ≤ witnesses n t (R.inbox A (8 * ph + 5) q) (.vote u) (4 * ph + 2) := by
      have h := cc_le_witnesses (hℓ := hℓ) R hP hR (k := 4 * ph + 2) (by omega) hq (.vote u)
      rw [show 2 * (4 * ph + 2) + 1 = 8 * ph + 5 by ring] at h
      refine le_trans ?_ h
      unfold cc
      rw [filter_true_of_mem]
      · omega
      · intro q' hq'
        rw [show 2 * (4 * ph + 2) = 8 * ph + 4 by ring]
        exact hvote q' (by simpa [cor] using hq')
    have hne : (ackCand n t (R.st A (8 * ph + 5) q) (R.inbox A (8 * ph + 5) q)).Nonempty := by
      refine ⟨u, ?_⟩
      simp only [ackCand, Set.mem_ofPred_eq, rnd_st, show (8 * ph + 5) / 8 = ph by omega]
      exact hWv
    obtain ⟨u', hu'⟩ := pick_isSome hne
    rw [show 8 * ph + 6 = 8 * ph + 5 + 1 by ring, ackVal_succ, ite_eq_left (by omega), hu']
    have hm := pick_mem hu'
    simp only [ackCand, Set.mem_ofPred_eq, rnd_st, show (8 * ph + 5) / 8 = ph by omega] at hm
    obtain ⟨h, -, h1, h2⟩ := lemma31 R hn hP hR hm hWv
    rw [vote_unique R h1 h2]
  -- T10: decision
  have hdc : (decCand n t (R.st A (8 * ph + 6) p) (R.inbox A (8 * ph + 6) p)).Nonempty := by
    refine ⟨u, ?_, ?_⟩
    · simp only [rnd_st, show (8 * ph + 6) / 8 = ph by omega]
      rw [wit_phase R ph 5 rfl p]
      exact hL7 u (pick_mem hu) p hp (8 * ph + 4) (by omega)
    · refine le_trans ?_ (countP_inbox_ge R hR.1 (by omega) hp (fun x => x.2.ack = some u))
      rw [filter_true_of_mem]
      · omega
      · intro q hq; exact hack q (by simpa [cor] using hq)
  obtain ⟨d, hd⟩ := pick_isSome hdc
  rw [show 8 * ph + 7 = 8 * ph + 6 + 1 by ring, decided_succ, ite_eq_left (by omega), hd]
  cases (R.st A (8 * ph + 6) p).decided with
  | none => exact ⟨d, rfl⟩
  | some w => exact ⟨w, rfl⟩

end Podc.HomonymsBA.Restricted
