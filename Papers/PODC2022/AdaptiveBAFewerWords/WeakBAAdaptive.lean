import Papers.PODC2022.AdaptiveBAFewerWords.WeakBAModel

/-!
# Adaptivity of Algorithm 3 of [CKS22]: Lemma 16, Lemma 14, Lemma 6 and Section 6.1

In the model of `WeakBAModel.lean`:

* `lemma16`: if the leader of phase `j` is correct and undecided, its input is valid and the
  correct processes form a quorum (`q + f ≤ n`, implied by the paper's `f < (n − t − 1)/2`), then
  every correct process receives the same finalize certificate in phase `j` and has decided after it.
  No unforgeability is needed: the leader relays the commit of maximal level it received, and every
  correct process sent it its own commit.
* `lemma14`: every decision taken in the phases by a correct process is a valid value.
* `lemma6`: with the text's `K = n` phases and `f < (n − t − 1)/2`, all correct processes decide in
  the phases and no correct process runs the fallback.
* `phaseWords_le`: with the guard reading (a correct leader that does not propose stays silent), the
  phases cost at most `5n + 2nf` words, and the help answers at most `nf` (Section 6.1).
-/

namespace Podc.AdaptiveBAFewerWords.WeakBA

open Finset

variable {n : ℕ} {V : Type} [DecidableEq V]

lemma count_filterMap_finRange (f : Fin n → Option V) (v : V) :
    ((List.finRange n).filterMap f).count v = (univ.filter fun p => f p = some v).card := by
  rw [List.count, List.countP_filterMap, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1; ext i; cases h : f i <;> simp [h]

omit [DecidableEq V] in
lemma maxCert_eq_none {l : List (Cert V)} : maxCert l = none → l = [] := by
  cases l with
  | nil => intro; rfl
  | cons c cs =>
    simp only [maxCert]
    cases maxCert cs with
    | none => simp
    | some d => simp only; split <;> simp

omit [DecidableEq V] in
lemma maxCert_spec : ∀ {l : List (Cert V)} {c : Cert V}, maxCert l = some c →
    c ∈ l ∧ ∀ d ∈ l, d.lvl ≤ c.lvl
  | [], c, h => by simp [maxCert] at h
  | c' :: cs, c, h => by
    simp only [maxCert] at h
    rcases hm : maxCert cs with _ | d
    · rw [hm] at h; cases h
      have := maxCert_eq_none hm; subst this; simp
    · rw [hm] at h
      obtain ⟨hd, hdmax⟩ := maxCert_spec hm
      simp only at h
      split at h
      · cases h
        refine ⟨by simp, ?_⟩
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact le_rfl
        · exact (hdmax e he).trans (by omega)
      · cases h
        refine ⟨List.mem_cons_of_mem _ hd, ?_⟩
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · omega
        · exact hdmax e he

/-- The correct processes number `n - |F|`. -/
lemma card_correct (F : Finset (Fin n)) : (univ.filter fun p => p ∉ F).card = n - F.card := by
  rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff]
  simp

/-- If every correct process satisfies `f p = some v`, then `v` occurs at least `n - |F|` times. -/
lemma le_count_of_correct (F : Finset (Fin n)) (f : Fin n → Option V) (v : V)
    (h : ∀ p, p ∉ F → f p = some v) : n - F.card ≤ ((List.finRange n).filterMap f).count v := by
  rw [count_filterMap_finRange, ← card_correct F]
  exact card_le_card fun p hp => by simp only [mem_filter, mem_univ, true_and] at hp ⊢; exact h p hp

variable (P : Params V) (A : Adv n V) [NeZero n]

/-- **Lemma 16 of [CKS22]** (model form; per-phase reading of "for the first time" at line 33,
`voteOnce = false`, as in the paper's proof). If the leader of phase `j` is correct, has not decided
(the phase is non-silent), its input is valid, and the correct processes form a quorum
(`q + f ≤ n`), then all correct processes receive the same finalize certificate in phase `j`. -/
theorem lemma16 (hvo : P.voteOnce = false) (j : ℕ) (s : Fin n → St V) (hL : leader n j ∉ A.F)
    (hprop : proposes j s = true) (hvalid : P.valid (s (leader n j)).inp = true)
    (hq : quorum n P.t + A.F.card ≤ n) :
    ∃ w, ∀ q, q ∉ A.F → finRcv P A j s q = some w := by
  have hq1 : 1 ≤ quorum n P.t := by unfold quorum; omega
  set x := (s (leader n j)).inp with hx
  have hpr : ∀ q, propRcv A j s q = some x := fun q => by
    simp [propRcv, hL, hprop, hx]
  -- the commit certificate of round 3
  have hcert : ∃ c, leaderCert P A j s = some c ∧ ∀ q, q ∉ A.F → (s q).level ≤ c.lvl := by
    have hrep : ∀ q, q ∉ A.F → replyRcv P A j s q = replyOf P A j s q := fun q hq => by
      simp [replyRcv, hq]
    unfold leaderCert
    simp only [hprop, Bool.true_eq_false, and_false, ite_false]
    rcases hm : maxCert (commitsRcv P A j s) with _ | c
    · -- no commit received: every correct process votes for `x`
      have hnil := maxCert_eq_none hm
      have hcom : ∀ q, q ∉ A.F → (s q).commit = none := by
        intro q hq
        rcases hc : (s q).commit with _ | cq
        · rfl
        · exfalso
          have : cq ∈ commitsRcv P A j s := by
            simp only [commitsRcv, List.mem_filterMap, List.mem_finRange, true_and]
            exact ⟨q, by rw [hrep q hq]; simp [replyOf, hpr q, hc]⟩
          rw [hnil] at this; simp at this
      have hvote : ∀ q, q ∉ A.F →
          (fun p => match replyRcv P A j s p with
            | some (.vote v) => some v
            | _ => none) q = some x := by
        intro q hq
        simp [hrep q hq, replyOf, hpr q, hcom q hq, hvalid, hvo]
      have hcount : n - A.F.card ≤ (votesRcv P A j s).count x := le_count_of_correct A.F _ x hvote
      have hsome : ((votesRcv P A j s).find?
          fun v => decide (quorum n P.t ≤ (votesRcv P A j s).count v)).isSome := by
        rw [List.find?_isSome]
        refine ⟨x, ?_, ?_⟩
        · rw [← List.count_pos_iff]; omega
        · simp only [decide_eq_true_eq]; omega
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
      refine ⟨⟨v, j⟩, by simp [hv], fun q hq => ?_⟩
      simp [St.level, hcom q hq]
    · obtain ⟨-, hmax⟩ := maxCert_spec hm
      refine ⟨c, rfl, fun q hq => ?_⟩
      rcases hc : (s q).commit with _ | cq
      · simp [St.level, hc]
      · have : cq ∈ commitsRcv P A j s := by
          simp only [commitsRcv, List.mem_filterMap, List.mem_finRange, true_and]
          exact ⟨q, by rw [hrep q hq]; simp [replyOf, hpr q, hc]⟩
        simpa [St.level, hc] using hmax cq this
  obtain ⟨c, hc, hlev⟩ := hcert
  have hdec : ∀ q, q ∉ A.F → decRcv P A j s q = some c.val := fun q hq => by
    simp [decRcv, hq, decOf, comRcv, hL, hc, hlev q hq]
  have hcount : n - A.F.card ≤ (decsRcv P A j s).count c.val := le_count_of_correct A.F _ c.val hdec
  have hsome : ((decsRcv P A j s).find?
      fun v => decide (quorum n P.t ≤ (decsRcv P A j s).count v)).isSome := by
    rw [List.find?_isSome]
    refine ⟨c.val, ?_, ?_⟩
    · rw [← List.count_pos_iff]; omega
    · simp only [decide_eq_true_eq]; omega
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hsome
  refine ⟨w, fun q _ => ?_⟩
  simp [finRcv, hL, leaderFin, hprop, hw]

/-! ### Monotonicity of decisions -/

lemma inp_stateAt : ∀ j q, (stateAt P A j q).inp = A.inp q
  | 0, _ => rfl
  | j + 1, q => by simp only [stateAt, step]; exact inp_stateAt j q

lemma decided_step (j : ℕ) (s : Fin n → St V) (q : Fin n) (h : (s q).decision.isSome) :
    (step P A j s q).decision.isSome := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  simp [step, hv]

lemma decided_step_of_fin (j : ℕ) (s : Fin n → St V) (q : Fin n) (w : V)
    (h : finRcv P A j s q = some w) : (step P A j s q).decision.isSome := by
  simp only [step]
  split <;> simp_all

lemma decided_mono {j k : ℕ} (hjk : j ≤ k) (q : Fin n) (h : (stateAt P A j q).decision.isSome) :
    (stateAt P A k q).decision.isSome := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact decided_step P A _ _ q ih

/-- The phase in `[1, n]` led by `q`. -/
def ownPhase (q : Fin n) : ℕ := if q.val = 0 then n else q.val

omit [DecidableEq V] in
lemma ownPhase_spec (q : Fin n) : leader n (ownPhase q) = q ∧ 1 ≤ ownPhase q ∧ ownPhase q ≤ n := by
  have hn := NeZero.pos n
  unfold ownPhase leader
  split_ifs with h
  · exact ⟨Fin.ext (by simp [h]), by omega, le_rfl⟩
  · exact ⟨Fin.ext (Nat.mod_eq_of_lt q.isLt), by omega, q.isLt.le⟩

/-- In a non-silent phase `j` with a correct leader, all correct processes decide (Lemma 16 with
the monotonicity of decisions). -/
lemma all_decided_after (hvo : P.voteOnce = false) (j : ℕ) (hj : 1 ≤ j) (hL : leader n j ∉ A.F)
    (hprop : proposes j (stateAt P A (j - 1)) = true)
    (hvalid : ∀ q, q ∉ A.F → P.valid (A.inp q) = true) (hq : quorum n P.t + A.F.card ≤ n) :
    ∀ q, q ∉ A.F → (stateAt P A j q).decision.isSome := by
  obtain ⟨w, hw⟩ := lemma16 P A hvo j (stateAt P A (j - 1)) hL hprop
    (by rw [inp_stateAt]; exact hvalid _ hL) hq
  intro q hq'
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact decided_step_of_fin P A _ _ q w (hw q hq')

/-- With `K = n` phases and `q + f ≤ n`, every correct process decides in the phases. -/
theorem all_decide (hvo : P.voteOnce = false) (hK : P.K = n) (hvalid : ∀ q, q ∉ A.F → P.valid (A.inp q) = true)
    (hq : quorum n P.t + A.F.card ≤ n) : ∀ q, q ∉ A.F → (dAfter P A q).isSome := by
  intro q hqF
  obtain ⟨hl, h1, h2⟩ := ownPhase_spec q
  unfold dAfter phases
  rw [hK]
  by_cases hd : (stateAt P A (ownPhase q - 1) q).decision.isSome
  · exact decided_mono P A (by omega) q hd
  · have hprop : proposes (ownPhase q) (stateAt P A (ownPhase q - 1)) = true := by
      simp only [proposes, hl]; simpa using hd
    exact decided_mono P A h2 q
      (all_decided_after P A hvo _ h1 (by rw [hl]; exact hqF) hprop hvalid hq q hqF)

/-- **Lemma 6 of [CKS22]** (with the text's `n` phases and the per-phase reading of line 33). If `n = 2t + 1` and
`f < (n − t − 1)/2`, all correct processes decide in the phases and no correct process ever runs
the fallback algorithm. -/
theorem lemma6 (hvo : P.voteOnce = false) (hn : n = 2 * P.t + 1) (hK : P.K = n) (hV : AdvValid P A)
    (hf : 2 * A.F.card < n - P.t - 1) (hvalid : ∀ q, q ∉ A.F → P.valid (A.inp q) = true) :
    (∀ q, q ∉ A.F → (dAfter P A q).isSome) ∧ ¬ FbRuns P A := by
  have hq : quorum n P.t + A.F.card ≤ n := by
    have := quorum_le_correct (n := n) (t := P.t) hf (by omega)
    have := hV.card_F; omega
  have hdec := all_decide P A hvo hK hvalid hq
  have hsub : (univ.filter fun p => p ∈ A.F ∨ (dAfter P A p).isNone) ⊆ A.F := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    rcases hp with hp | hp
    · exact hp
    · by_contra hpF; have := hdec p hpF; simp_all
  refine ⟨hdec, ?_⟩
  rintro (⟨q, _, hfq⟩ | ⟨b, _, q, _, hm⟩)
  · unfold Former at hfq
    have : (univ.filter fun p => helpReqFrom P A p q = true) ⊆ A.F := by
      intro p hp
      by_contra hpF
      have := hdec p hpF
      simp [helpReqFrom, hpF, dAfter] at hp this
      simp_all
    have := card_le_card this; have := hV.card_F; omega
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hm
    have hc := hV.fbMsg b q m hm
    unfold FbCertAvail at hc
    have := card_le_card hsub; have := hV.card_F; omega

/-! ### Word complexity (Section 6.1) -/

/-- Words sent by correct processes in phase `j` started in states `s` (one word per message,
messages to oneself included): the three broadcasts of a correct leader (`n` words each) and the
round-2 and round-4 messages of correct processes to the leader. -/
def phaseWords (j : ℕ) (s : Fin n → St V) : ℕ :=
  (if leader n j ∈ A.F then 0 else
    (if proposes j s then n else 0) + (if (leaderCert P A j s).isSome then n else 0) +
      (if (leaderFin P A j s).isSome then n else 0)) +
  (univ.filter fun q => q ∉ A.F ∧ (replyOf P A j s q).isSome).card +
  (univ.filter fun q => q ∉ A.F ∧ (decOf P A j s q).isSome).card

/-- Words sent by correct processes in the `K` phases. -/
def phasesWords : ℕ := ∑ j ∈ Finset.Icc 1 P.K, phaseWords P A j (stateAt P A (j - 1))

/-- Words sent by correct processes in rounds H1–H2: `help_req` broadcasts of undecided processes
and `help` answers of decided processes (line 8). -/
def helpWords : ℕ :=
  ∑ p ∈ univ.filter (· ∉ A.F),
    if (dAfter P A p).isNone then n else (univ.filter fun b => helpReqFrom P A b p).card

omit [NeZero n] in
lemma card_filter_le_n (p : Fin n → Prop) [DecidablePred p] : (univ.filter p).card ≤ n := by
  simpa using card_filter_le univ p

lemma phaseWords_le (j : ℕ) (s : Fin n → St V) :
    phaseWords P A j s ≤
      if leader n j ∈ A.F then 2 * n else if proposes j s then 5 * n else
        if P.guard then 0 else 4 * n := by
  have h1 := card_filter_le_n fun q => q ∉ A.F ∧ (replyOf P A j s q).isSome
  have h2 := card_filter_le_n fun q => q ∉ A.F ∧ (decOf P A j s q).isSome
  by_cases hL : leader n j ∈ A.F
  · simp only [phaseWords, hL, ite_true]; omega
  by_cases hp : proposes j s = true
  · simp only [phaseWords, hL, hp, ite_false, ite_true]; split_ifs <;> omega
  have hp' : proposes j s = false := by simpa using hp
  by_cases hg : P.guard = true
  · -- a silent phase of a correct leader under the guard reading costs nothing
    have hlc : leaderCert P A j s = none := by simp [leaderCert, hg, hp']
    have hlf : leaderFin P A j s = none := by simp [leaderFin, hg, hp']
    have hr : ∀ q, replyOf P A j s q = none := fun q => by simp [replyOf, propRcv, hL, hp']
    have hd : ∀ q, decOf P A j s q = none := fun q => by simp [decOf, comRcv, hL, hlc]
    simp [phaseWords, hL, hp', hg, hlc, hlf, hr, hd]
  · simp only [phaseWords, hL, hp', hg, ite_false, Bool.false_eq_true]; split_ifs <;> omega

/-- **Section 6.1 of [CKS22]** (phases). With `K = n` phases, `n = 2t + 1`,
`f < (n − t − 1)/2`, valid inputs and the guard reading, correct processes send at most
`5n + 2nf` words in the phases and at most `nf` words in rounds H1–H2; the fallback never runs
(Lemma 6). So Algorithm 3 sends `O(n(f + 1))` words in this regime. -/
theorem words_le (hvo : P.voteOnce = false) (hn : n = 2 * P.t + 1) (hK : P.K = n) (hg : P.guard = true) (hV : AdvValid P A)
    (hf : 2 * A.F.card < n - P.t - 1) (hvalid : ∀ q, q ∉ A.F → P.valid (A.inp q) = true) :
    phasesWords P A ≤ 5 * n + 2 * n * A.F.card ∧ helpWords P A ≤ n * A.F.card ∧
      ¬ FbRuns P A := by
  have hq : quorum n P.t + A.F.card ≤ n := by
    have := quorum_le_correct (n := n) (t := P.t) hf (by omega)
    have := hV.card_F; omega
  obtain ⟨hdec, hfb⟩ := lemma6 P A hvo hn hK hV hf hvalid
  refine ⟨?_, ?_, hfb⟩
  · -- phases
    set B := (Icc 1 P.K).filter fun j => leader n j ∈ A.F
    set S := (Icc 1 P.K).filter fun j => leader n j ∉ A.F ∧ proposes j (stateAt P A (j - 1))
    have hB : B.card ≤ A.F.card := by
      refine card_le_card_of_injOn (leader n) (fun j hj => (mem_filter.1 hj).2) ?_
      intro a ha b hb hab
      simp only [B, coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha hb
      have := congrArg Fin.val hab
      simp only [leader] at this
      rcases Nat.lt_or_ge a n with ha' | ha' <;> rcases Nat.lt_or_ge b n with hb' | hb'
      · rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
      · have : b = n := by omega
        subst this; rw [Nat.mod_eq_of_lt ha', Nat.mod_self] at *; omega
      · have : a = n := by omega
        subst this; rw [Nat.mod_eq_of_lt hb', Nat.mod_self] at *; omega
      · omega
    have hS : S.card ≤ 1 := by
      rw [Finset.card_le_one]
      have key : ∀ a ∈ S, ∀ b ∈ S, a < b → False := by
        intro a ha b hb hab
        simp only [S, mem_filter, mem_Icc] at ha hb
        have hall := all_decided_after P A hvo a ha.1.1 ha.2.1 ha.2.2 hvalid hq
        have := decided_mono P A (show a ≤ b - 1 by omega) _ (hall _ hb.2.1)
        simp only [proposes, Option.isNone_iff_eq_none] at hb
        rw [hb.2.2] at this; simp at this
      intro a ha b hb
      rcases lt_trichotomy a b with h | h | h
      · exact (key a ha b hb h).elim
      · exact h
      · exact (key b hb a ha h).elim
    calc phasesWords P A
        ≤ ∑ j ∈ Icc 1 P.K, ((if leader n j ∈ A.F then 2 * n else 0) +
            (if leader n j ∉ A.F ∧ proposes j (stateAt P A (j - 1)) then 5 * n else 0)) := by
          apply sum_le_sum
          intro j _
          refine (phaseWords_le P A j _).trans ?_
          split_ifs <;> simp_all
      _ = B.card * (2 * n) + S.card * (5 * n) := by
          rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const, smul_eq_mul,
            smul_eq_mul]
      _ ≤ A.F.card * (2 * n) + 1 * (5 * n) := by gcongr
      _ = 5 * n + 2 * n * A.F.card := by ring
  · -- help answers: only Byzantine processes ask for help
    unfold helpWords
    calc _ ≤ ∑ p ∈ univ.filter (· ∉ A.F), A.F.card := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter, mem_univ, true_and] at hp
          have hd := hdec p hp
          simp only [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none.1 hd, ite_false]
          refine card_le_card fun b hb => ?_
          simp only [helpReqFrom] at hb
          by_contra hbF
          have := hdec b hbF
          simp_all [dAfter]
      _ ≤ n * A.F.card := by
          rw [sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (card_filter_le_n _)

end Podc.AdaptiveBAFewerWords.WeakBA
