import Papers.PODC2011.HomonymsBA.RestrictedBroadcast

/-!
# Proposition 18: safety of the consensus algorithm (Figure 7)

Lemmas 32, 33, 35 and Propositions 38 (validity), 39 (agreement).
-/

namespace Podc.HomonymsBA.Restricted

open Finset Classical

variable {n t ℓ : ℕ} {hℓ : 0 < ℓ} {V : Type} {P : Type} [Fintype P]

set_option linter.unusedSectionVars false

/-! ### Shape of the broadcasts -/

lemma mem_initOut_propose {s : St ℓ V} {v : V} :
    CM.propose v ∈ initOut n t s ↔ s.rnd % 8 = 0 ∧ v ∈ propVals s := by
  unfold initOut
  split_ifs with h0 h4 <;> simp [*]

lemma mem_initOut_vote {s : St ℓ V} {v : V} :
    CM.vote v ∈ initOut n t s ↔ s.rnd % 8 = 4 ∧ pick (voteCand n t s) = some v := by
  unfold initOut
  split_ifs with h0 h4 <;> simp [*]

variable (R : Run P ℓ V (Msg ℓ V))

local notation "A" => alg n t hℓ V
local notation "CC" => cc (n := n) (t := t) (hℓ := hℓ)

lemma wit_of_odd {r : ℕ} (hr : r % 2 = 1) (q : P) :
    (R.st A (r + 1) q).wit = witnesses n t (R.inbox A r q) := by
  rw [wit_succ, ite_eq_left hr]

/-- The witnesses a correct process holds in round `8ph + j + 1` (`j` odd) are those of round
`8ph + j`. -/
lemma wit_phase (ph j : ℕ) (hj : j % 2 = 1) (q : P) :
    (R.st A (8 * ph + j + 1) q).wit = witnesses n t (R.inbox A (8 * ph + j) q) :=
  wit_of_odd R (by omega) q

/-- A correct broadcaster exists if `n - t - f ≥ 1` of them do. -/
lemma exists_of_cc (hn : 3 * t < n) (hR : R.Admissible t .psync .restricted) {m : CM V} {k : ℕ}
    (h : n - t - R.byz.card ≤ CC R m k) :
    ∃ q, q ∉ R.byz ∧ m ∈ initOut n t (R.st A (2 * k) q) := by
  have := hR.1.card_byz
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (show 0 < ((cor R).filter
    (fun q => m ∈ initOut n t (R.st A (2 * k) q))).card by unfold cc at h; omega)
  simp only [mem_filter, cor, mem_univ, true_and] at hq
  exact ⟨q, hq⟩

/-- A vote is only broadcast for a value with `n - t` witnesses for its proposal in the previous
round (lines 12–14 of Figure 7). -/
lemma vote_spec {ph : ℕ} {q : P} {v : V}
    (h : CM.vote v ∈ initOut n t (R.st A (2 * (4 * ph + 2)) q)) :
    n - t ≤ witnesses n t (R.inbox A (8 * ph + 3) q) (.propose v) (4 * ph) := by
  rw [mem_initOut_vote] at h
  have h2 := pick_mem h.2
  have e : 2 * (4 * ph + 2) = 8 * ph + 3 + 1 := by ring
  rw [e] at h2
  have e2 : (8 * ph + 3 + 1) / 8 = ph := by omega
  simp only [voteCand, Set.mem_ofPred_eq, rnd_st, e2] at h2
  rw [wit_phase R ph 3 rfl q] at h2
  exact h2.2

/-- A correct process votes for at most one value per phase. -/
lemma vote_unique {r : ℕ} {q : P} {v w : V} (hv : CM.vote v ∈ initOut n t (R.st A r q))
    (hw : CM.vote w ∈ initOut n t (R.st A r q)) : v = w := by
  rw [mem_initOut_vote] at hv hw
  rw [hv.2] at hw
  exact Option.some_injective _ hw.2

/-! ### Locks -/

/-- A lock `(v, ph)` of a correct process was added at the end of round `8ph + 5`, with `n - t`
witnesses for `vote v` of phase `ph`. -/
theorem lock_spec (r : ℕ) (q : P) (x : V × ℕ) (hx : x ∈ (R.st A r q).locks) :
    8 * x.2 + 6 ≤ r ∧ n - t ≤ witnesses n t (R.inbox A (8 * x.2 + 5) q) (.vote x.1) (4 * x.2 + 2) := by
  induction r generalizing x with
  | zero => simp [Run.st, alg] at hx
  | succ r ih =>
    rw [locks_succ] at hx
    unfold newLocks at hx
    rw [rnd_st] at hx
    split_ifs at hx with h5 h7
    · rcases hpk : pick (ackCand n t (R.st A r q) (R.inbox A r q)) with _ | v
      · rw [hpk] at hx
        exact ⟨(ih x hx).1.trans (by omega), (ih x hx).2⟩
      · rw [hpk] at hx
        rcases hx with rfl | ⟨hx, -⟩
        · have hm := pick_mem hpk
          simp only [ackCand, Set.mem_ofPred_eq, rnd_st] at hm
          have e : 8 * (r / 8) + 5 = r := by omega
          refine ⟨by simp only; omega, ?_⟩
          simp only [e]
          exact hm
        · exact ⟨(ih x hx).1.trans (by omega), (ih x hx).2⟩
    · exact ⟨(ih x hx.1).1.trans (by omega), (ih x hx.1).2⟩
    · exact ⟨(ih x hx).1.trans (by omega), (ih x hx).2⟩

/-- Sending `ack v` in phase `ph` (line 19): `n - t` witnesses for `vote v` and the lock
`(v, ph)`. -/
theorem ack_spec (ph : ℕ) (q : P) (v : V) (h : (R.st A (8 * ph + 6) q).ackVal = some v) :
    n - t ≤ witnesses n t (R.inbox A (8 * ph + 5) q) (.vote v) (4 * ph + 2) ∧
      (v, ph) ∈ (R.st A (8 * ph + 6) q).locks := by
  rw [show 8 * ph + 6 = 8 * ph + 5 + 1 by ring, ackVal_succ, ite_eq_left (by omega)] at h
  have hm := pick_mem h
  have e : (8 * ph + 5) / 8 = ph := by omega
  simp only [ackCand, Set.mem_ofPred_eq, rnd_st, e] at hm
  refine ⟨hm, ?_⟩
  rw [show 8 * ph + 6 = 8 * ph + 5 + 1 by ring, locks_succ]
  unfold newLocks
  rw [rnd_st, ite_eq_left (by omega : (8 * ph + 5) % 8 = 5), h, e]
  exact Set.mem_insert _ _

/-! ### Decisions -/

/-- The decision condition of lines 20–23 in phase `ph`. -/
def DecAt (q : P) (ph : ℕ) (v : V) : Prop :=
  n - t ≤ witnesses n t (R.inbox A (8 * ph + 5) q) (.propose v) (4 * ph) ∧
    n - t ≤ (R.inbox A (8 * ph + 6) q).countP (fun x => x.2.ack = some v)

/-- Every decision comes from the decision condition in some phase. -/
theorem decided_spec (r : ℕ) (q : P) (v : V) (h : (R.st A r q).decided = some v) :
    ∃ ph, 8 * ph + 6 < r ∧ DecAt (n := n) (t := t) (hℓ := hℓ) R q ph v := by
  induction r with
  | zero => simp [Run.st, alg] at h
  | succ r ih =>
    rw [decided_succ] at h
    rcases hd : (R.st A r q).decided with _ | w
    · rw [hd, Option.none_or] at h
      split_ifs at h with h6
      have hm := pick_mem h
      refine ⟨r / 8, by omega, ?_⟩
      have e : 8 * (r / 8) + 6 = r := by omega
      simp only [decCand, Set.mem_ofPred_eq, rnd_st] at hm
      unfold DecAt
      rw [e]
      refine ⟨?_, hm.2⟩
      have := hm.1
      rw [← e, wit_phase R (r / 8) 5 rfl q] at this
      simpa [e] using this
    · rw [hd, Option.some_or] at h
      cases h
      obtain ⟨ph, h1, h2⟩ := ih hd
      exact ⟨ph, by omega, h2⟩

/-! ### Agreement -/

/-- **Lemma 32.** Correct processes acknowledge the same value in a phase. -/
theorem lemma32 (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {ph : ℕ} {q q' : P} {v v' : V}
    (h : (R.st A (8 * ph + 6) q).ackVal = some v) (h' : (R.st A (8 * ph + 6) q').ackVal = some v') :
    v = v' := by
  obtain ⟨h1, -⟩ := ack_spec R ph q v h
  obtain ⟨h2, -⟩ := ack_spec R ph q' v' h'
  obtain ⟨r, -, hr1, hr2⟩ := lemma31 R hn hP hR h1 h2
  exact vote_unique R hr1 hr2

/-- `n - t` received `ack v` messages come from at least `n - t - f` correct processes. -/
lemma ack_senders (hR : R.Admissible t .psync .restricted) {ph : ℕ} {p : P} {v : V}
    (h : n - t ≤ (R.inbox A (8 * ph + 6) p).countP (fun x => x.2.ack = some v)) :
    n - t - R.byz.card ≤
      ((cor R).filter (fun q => (R.st A (8 * ph + 6) q).ackVal = some v)).card := by
  have := countP_inbox_le (n := n) (t := t) (hℓ := hℓ) R (hR.2.2 rfl) (fun x => x.2.ack = some v) (8 * ph + 6) p
  have e : ((cor R).filter (fun q => (R.id q, out n t hℓ (R.st A (8 * ph + 6) q)).2.ack = some v))
      = (cor R).filter (fun q => (R.st A (8 * ph + 6) q).ackVal = some v) := rfl
  rw [e] at this
  omega

/-- **Lemma 33.** Decisions in the same phase agree. -/
theorem lemma33 (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {ph : ℕ} {q q' : P} {v v' : V}
    (h : DecAt (n := n) (t := t) (hℓ := hℓ) R q ph v)
    (h' : DecAt (n := n) (t := t) (hℓ := hℓ) R q' ph v') : v = v' := by
  have hf := hR.1.card_byz
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (show 0 < ((cor R).filter
    (fun q => (R.st A (8 * ph + 6) q).ackVal = some v)).card by
      have := ack_senders R hR h.2; omega)
  obtain ⟨b, hb⟩ := Finset.card_pos.1 (show 0 < ((cor R).filter
    (fun q => (R.st A (8 * ph + 6) q).ackVal = some v')).card by
      have := ack_senders R hR h'.2; omega)
  exact lemma32 R hn hP hR (mem_filter.1 ha).2 (mem_filter.1 hb).2

/-- **Lemma 35.** If some correct process receives `n - t` messages `ack v` in phase `ph`, then
every correct process that sent `ack v` in phase `ph` keeps a lock `(v, ph')` with `ph' ≥ ph`
forever. -/
theorem lemma35 (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {ph : ℕ} {p : P} {v : V}
    (hack : n - t ≤ (R.inbox A (8 * ph + 6) p).countP (fun x => x.2.ack = some v)) :
    ∀ r, 8 * ph + 6 ≤ r → ∀ q, q ∉ R.byz → (R.st A (8 * ph + 6) q).ackVal = some v →
      ∃ ph', ph ≤ ph' ∧ (v, ph') ∈ (R.st A r q).locks := by
  have hf := hR.1.card_byz
  have hc := card_cor R hP
  have hA := ack_senders R hR hack
  set Aset := (cor R).filter (fun q => (R.st A (8 * ph + 6) q).ackVal = some v)
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro hr q hq hqv
  rcases Nat.eq_or_lt_of_le hr with rfl | hlt
  · exact ⟨ph, le_rfl, (ack_spec R ph q v hqv).2⟩
  obtain ⟨r0, rfl⟩ : ∃ r0, r = r0 + 1 := ⟨r - 1, by omega⟩
  obtain ⟨ph0, hph0, hl0⟩ := ih r0 (by omega) (by omega) q hq hqv
  rw [locks_succ]
  unfold newLocks
  rw [rnd_st]
  split_ifs with h5 h7
  · rcases hpk : pick (ackCand n t (R.st A r0 q) (R.inbox A r0 q)) with _ | w
    · exact ⟨ph0, hph0, hl0⟩
    · by_cases hw : w = v
      · subst hw
        exact ⟨r0 / 8, by omega, Set.mem_insert _ _⟩
      · exact ⟨ph0, hph0, Set.mem_insert_of_mem _ ⟨hl0, Ne.symm hw⟩⟩
  · refine ⟨ph0, hph0, hl0, ?_⟩
    rintro ⟨v₂, ph₂, hne, hlt2, hw⟩
    -- some correct process voted `v₂` in phase `ph₂`
    obtain ⟨hk, hcc⟩ := lemma30 R hn hR hw
    obtain ⟨h0, h0c, h0v⟩ := exists_of_cc R hn hR hcc
    have hB := (lemma30 R hn hR (vote_spec R h0v)).2
    unfold cc at hB
    set B := (cor R).filter (fun q => CM.propose v₂ ∈ initOut n t (R.st A (2 * (4 * ph₂)) q))
    have hU : (Aset ∪ B).card ≤ (cor R).card :=
      card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    have := card_union_add_card_inter Aset B
    obtain ⟨h, hh⟩ := Finset.card_pos.1 (show 0 < (Aset ∩ B).card by omega)
    simp only [Aset, B, mem_inter, mem_filter, cor, mem_univ, true_and] at hh
    obtain ⟨phh, -, hlh⟩ := ih (2 * (4 * ph₂)) (by omega) (by omega) h hh.1.1 hh.1.2
    have := (mem_initOut_propose.1 hh.2.2).2.2 _ hlh
    exact hne this.symm
  · exact ⟨ph0, hph0, hl0⟩

/-- **Proposition 39 (agreement)**, for decision events. -/
theorem decAt_agree (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {q q' : P} {ph ph' : ℕ} {v v' : V}
    (h : DecAt (n := n) (t := t) (hℓ := hℓ) R q ph v)
    (h' : DecAt (n := n) (t := t) (hℓ := hℓ) R q' ph' v') : v = v' := by
  -- reduce to `ph ≤ ph'`
  wlog hle : ph ≤ ph' generalizing q q' ph ph' v v'
  · exact (this h' h (by omega)).symm
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact lemma33 R hn hP hR h h'
  have hf := hR.1.card_byz
  have hc := card_cor R hP
  have hA := ack_senders R hR h.2
  have hB := (lemma30 R hn hR h'.1).2
  unfold cc at hB
  set Aset := (cor R).filter (fun q => (R.st A (8 * ph + 6) q).ackVal = some v)
  set B := (cor R).filter (fun q => CM.propose v' ∈ initOut n t (R.st A (2 * (4 * ph')) q))
  have hU : (Aset ∪ B).card ≤ (cor R).card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have := card_union_add_card_inter Aset B
  obtain ⟨h0, hh⟩ := Finset.card_pos.1 (show 0 < (Aset ∩ B).card by omega)
  simp only [Aset, B, mem_inter, mem_filter, cor, mem_univ, true_and] at hh
  obtain ⟨ph'', -, hl⟩ := lemma35 R hn hP hR h.2 (2 * (4 * ph')) (by omega) h0 hh.1.1 hh.1.2
  exact (mem_initOut_propose.1 hh.2.2).2.2 _ hl

/-! ### Validity -/

/-- If all correct processes have input `v₀`, their proper sets stay `{v₀}`. -/
theorem proper_eq_of_unanimous (hR : R.Admissible t .psync .restricted) {v₀ : V}
    (hv : ∀ p, p ∉ R.byz → R.inp p = v₀) (r : ℕ) : ∀ q, q ∉ R.byz → (R.st A r q).proper = {v₀} := by
  have hf := hR.1.card_byz
  have hres : R.Restricted := hR.2.2 rfl
  induction r with
  | zero => intro q hq; simp [Run.st, alg, hv q hq]
  | succ r ih =>
    intro q hq
    rw [proper_succ]
    unfold newProper
    rw [ih q hq]
    ext v
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ((h | h) | ⟨J, hJ, hJc, hJt⟩)
      · exact h
      · obtain ⟨q', hq', hv'⟩ := exists_cor_of_countP R hres h (by omega)
        change v ∈ (R.st A r q').proper at hv'
        rw [ih q' hq'] at hv'
        exact hv'
      · exfalso
        have h1 := hJt v₀
        have h2 : J.countP (fun x => v₀ ∉ x.2.proper) ≤ t := by
          refine (Multiset.countP_le_of_le _ hJ).trans ?_
          refine (countP_inbox_le R hres _ r q).trans ?_
          rw [filter_false_of_mem]
          · simpa using hf
          · intro q' hq'
            change ¬ v₀ ∉ (R.st A r q').proper
            rw [ih q' (by simpa [cor] using hq')]
            simp
        have := Multiset.card_eq_countP_add_countP (fun x => v₀ ∈ x.2.proper) J
        omega
    · intro h; exact Or.inl (Or.inl h)

/-- **Proposition 38 (validity)**, for decision events. -/
theorem decAt_valid (hn : 3 * t < n) (hR : R.Admissible t .psync .restricted) {v₀ : V}
    (hv : ∀ p, p ∉ R.byz → R.inp p = v₀) {q : P} {ph : ℕ} {v : V}
    (h : DecAt (n := n) (t := t) (hℓ := hℓ) R q ph v) : v = v₀ := by
  obtain ⟨h0, h0c, h0v⟩ := exists_of_cc R hn hR (lemma30 R hn hR h.1).2
  have := (mem_initOut_propose.1 h0v).2.1
  rwa [proper_eq_of_unanimous R hR hv _ h0 h0c] at this

end Podc.HomonymsBA.Restricted
