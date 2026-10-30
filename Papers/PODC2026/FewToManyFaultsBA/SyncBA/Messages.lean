import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Correct

/-!
# Message complexity of `SyncBA` (Lemmas B.9–B.11, Theorem B.13)

`honestMsgs alg s T`: the number of messages honest parties send (to other parties) in the first
`T` rounds. We bound, round by round, the messages of stage A (`cA`), and those of stage B by the
per-party budget of the fallback.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {Mf Sf : Type}
  {Afb : Protocol (Fin n) Bool Mf Bool} {Af : Auth (Fin n) Mf Sf}

/-- Messages sent by honest parties in the first `T` rounds. -/
noncomputable def honestMsgs {I M O : Type} (alg : Protocol (Fin n) I M O)
    (s : Scenario (Fin n) I M) (T : ℕ) : ℕ :=
  ∑ r ∈ range T, ∑ p ∈ s.honestFinset, sendsAt alg s r p

/-- Messages of `p` in round `r` of stage A. -/
noncomputable def cA (π : Params n) (s : Scenario (Fin n) Bool (Msg n)) (r : ℕ) (p : Fin n) : ℕ :=
  (univ.filter fun q => q ≠ p ∧ (out π p (S π s r p) r q).isSome).card

variable {sc : Scenario (Fin n) Bool (Msg n ⊕ Mf)}

lemma sendsAt_lt {r : ℕ} (hr : r < R0 n) (p : Fin n) :
    sendsAt (syncBA π Afb) sc r p = cA π (scA sc) r p := by
  unfold sendsAt cA
  congr 1
  apply filter_congr
  intro q _
  have hlen : (hist (G n) (seqP π Afb) sc r p).length < R0 n := by simpa using hr
  have h1 : (syncBA π Afb).send p (sc.input p) (hist ⊤ (syncBA π Afb) sc r p) q =
      ((stageA π).send p (sc.input p) (hist (G n) (stageA π) (scA sc) r p) q).map Sum.inl := by
    show (seqP π Afb).send p (sc.input p) (hist (G n) (syncBA π Afb) sc r p) q = _
    rw [hist_syncBA, seq_send_lt _ _ _ _ hlen,
      histL_hist_seq (G n) (stageA π) (R0 n) toB (stageB Afb) sc r hr.le p]
  rw [h1]
  simp only [stageA, length_hist, hr, ite_true, Option.isSome_map]
  rfl

lemma sendsAt_ge (j : ℕ) (p : Fin n) :
    sendsAt (syncBA π Afb) sc (R0 n + j) p = sendsAt (stageB Afb) (scB (π := π) sc) j p := by
  unfold sendsAt
  congr 1
  apply filter_congr
  intro q _
  have hlen : R0 n ≤ (hist (G n) (seqP π Afb) sc (R0 n + j) p).length := by simp
  have h1 : (syncBA π Afb).send p (sc.input p) (hist ⊤ (syncBA π Afb) sc (R0 n + j) p) q =
      ((stageB Afb).send p ((scB (π := π) sc).input p)
        (hist (G n) (stageB Afb) (scB (π := π) sc) j p) q).map Sum.inr := by
    show (seqP π Afb).send p (sc.input p) (hist (G n) (syncBA π Afb) sc (R0 n + j) p) q = _
    rw [hist_syncBA, seq_send_ge _ _ _ _ hlen, seqInput_hist, histR_hist_seq]
    rfl
  rw [h1, Option.isSome_map]

lemma sendsAt_stageB_none {s₂ : Scenario (Fin n) (Option Bool) Mf} {p : Fin n}
    (h : s₂.input p = none) (j : ℕ) : sendsAt (stageB Afb) s₂ j p = 0 := by
  unfold sendsAt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro q _
  simp [h, stageB]

lemma sendsAt_stageB_bScen {s₂ : Scenario (Fin n) (Option Bool) Mf} {p : Fin n}
    (hp : p ∉ (bScen s₂).byz) (j : ℕ) :
    sendsAt (stageB Afb) s₂ j p = sendsAt Afb (bScen s₂) j p := by
  obtain ⟨-, v, hv⟩ := mem_bScen_byz.1 hp
  unfold sendsAt
  rw [hist_bScen ⊤ s₂ j p hp]
  simp [stageB, hv, bScen]

/-! ### Per-round bounds in stage A -/

lemma cA_le (π : Params n) (s : Scenario (Fin n) Bool (Msg n)) (r : ℕ) (p : Fin n) :
    cA π s r p ≤ n := by
  unfold cA
  calc _ ≤ (univ : Finset (Fin n)).card := card_le_card (filter_subset _ _)
    _ = n := by simp

lemma cA_view_nonleader (π : Params n) (s : Scenario (Fin n) Bool (Msg n)) {v j : ℕ} (hv : v < n)
    (hj : j < 11) {p : Fin n} (hp : p ≠ leader v) : cA π s (11 * v + j) p ≤ 1 := by
  unfold cA
  calc _ ≤ ({leader v} : Finset (Fin n)).card := by
        apply card_le_card
        intro q hq
        obtain ⟨-, hne, hs⟩ := mem_filter.1 hq
        by_contra hql
        rw [mem_singleton] at hql
        rw [out_none hv hj hp hql] at hs; simp at hs
    _ = 1 := card_singleton _

lemma cA_eq_zero {π : Params n} {s : Scenario (Fin n) Bool (Msg n)} {r : ℕ} {p : Fin n}
    (h : ∀ q, q ≠ p → out π p (S π s r p) r q = none) : cA π s r p = 0 := by
  unfold cA
  rw [card_eq_zero, filter_eq_empty_iff]
  intro q _ ⟨hq, hs⟩
  rw [h q hq] at hs; simp at hs

/-- A generic view round: the leader sends to everybody, the others only to the leader. -/
lemma sum_cA_view (π : Params n) (s : Scenario (Fin n) Bool (Msg n)) {v j : ℕ} (hv : v < n)
    (hj : j < 11) (P : Finset (Fin n)) : ∑ p ∈ P, cA π s (11 * v + j) p ≤ 2 * n := by
  classical
  calc ∑ p ∈ P, cA π s (11 * v + j) p
      ≤ ∑ p ∈ P, (if p = leader v then n else 1) := by
        apply sum_le_sum; intro p _
        split_ifs with h
        · exact cA_le π s _ p
        · exact cA_view_nonleader π s hv hj h
    _ ≤ ∑ p : Fin n, (if p = leader v then n else 1) := sum_le_sum_of_subset (subset_univ _)
    _ = n + (n - 1) := by
        rw [sum_ite, sum_const, sum_const]
        simp only [filter_eq', mem_univ, ite_true, card_singleton, smul_eq_mul, one_mul,
          mul_one]
        rw [filter_ne' univ (leader v), card_erase_of_mem (mem_univ _), card_univ,
          Fintype.card_fin]
    _ ≤ 2 * n := by omega

/-! ### Rounds after every honest party has decided -/

lemma plan_idle {s : Scenario (Fin n) Bool (Msg n)} {v : ℕ} (hv : v < n) {p : Fin n}
    (hl : (S π s (11 * v + 1) p).lead = false) :
    ∀ j, 2 ≤ j → j ≤ 11 → (S π s (11 * v + j) p).plan = .idle := by
  intro j hj1 hj2
  induction j, hj1 using Nat.le_induction with
  | base => rw [S_plan2 hv, hl]; rfl
  | succ j hj ih =>
    have hlj : (S π s (11 * v + j) p).lead = false := by
      rw [S_lead hv (by omega) (by omega)]; exact hl
    rw [show 11 * v + (j + 1) = 11 * v + j + 1 by omega, S_plan_succ hv (by omega)]
    have hpl := ih (by omega)
    have hj11 : j < 11 := by omega
    interval_cases j
    · simp [viewTrans, hpl]
    · simp [viewTrans, ph3, hlj, hpl]
    · simp [viewTrans, ph4, hpl]
    · simp [viewTrans, phAgg, hpl]
    · simp only [viewTrans, ph6]; split <;> (try split_ifs) <;> exact hpl
    · simp [viewTrans, phAgg, hpl]
    · simp only [viewTrans, ph8]; split <;> (try split_ifs) <;> exact hpl
    · simp [viewTrans, phAgg, hpl]
    · simp [viewTrans, hpl]

variable {s : Scenario (Fin n) Bool (Msg n)} (hg : Good π s)
include hg

open Classical in
/-- In a view where every honest party already has a commit, honest parties only send messages in
phase 1: suggestions to a Byzantine leader, or an honest leader's answers to Byzantine complaints. -/
lemma sum_cA_decided {v j : ℕ} (hv : v < n) (hj : j < 11)
    (hall : ∀ q, q ∉ s.byz → (S π s (11 * v) q).commit.isSome) :
    ∑ p ∈ s.honestFinset, cA π s (11 * v + j) p ≤
      if j = 1 then (if leader v ∈ s.byz then n else (byzF s).card) else 0 := by
  classical
  have hcom : ∀ q, q ∉ s.byz → ∀ j', (S π s (11 * v + j') q).commit.isSome := fun q hq j' =>
    commit_mono_isSome hg (by omega) (hall q hq)
  have hlead : ∀ q, q ∉ s.byz → (S π s (11 * v + 1) q).lead = false := fun q hq => by
    rw [S_lead1 hv]
    have := hall q hq
    cases h : (S π s (11 * v) q).commit <;> simp_all
  have hact : ∀ q, q ∉ s.byz → ∀ j', 2 ≤ j' → j' ≤ 11 → (S π s (11 * v + j') q).active = false :=
    fun q hq j' h1 h2 => by
      rw [S_active hv h1 h2]
      have := hcom q hq 1
      cases h : (S π s (11 * v + 1) q).commit <;> simp_all
  -- party-role messages vanish except possibly the suggestion of phase 1
  have hpo : ∀ q, q ∉ s.byz → j ≠ 1 → partyOut q (S π s (11 * v + j) q) v j = none := by
    intro q hq hj1
    have hc := hcom q hq j
    unfold partyOut
    by_cases h0 : j = 0
    · subst h0
      simp only [Nat.add_zero] at hc ⊢
      cases h : (S π s (11 * v) q).commit <;> simp_all
    have h2 : 2 ≤ j := by omega
    simp only [h0, hj1, ite_false, hact q hq j h2 (by omega), Bool.false_eq_true, false_and,
      ite_false]
    split_ifs <;> (try rfl)
    split <;> simp
  -- an honest leader's messages vanish except the answers of phase 1
  have hlo : leader v ∉ s.byz → j ≠ 1 → ∀ q, leaderOut (S π s (11 * v + j) (leader v)) j q = none := by
    intro hL hj1 q
    have hc := hcom _ hL j
    unfold leaderOut
    by_cases h0 : j = 0
    · subst h0
      simp only [Nat.add_zero] at hc ⊢
      cases h : (S π s (11 * v) (leader v)).commit <;> simp_all
    have hpl := plan_idle hv (hlead _ hL) j (by omega) (by omega)
    simp only [h0, hj1, ite_false, hpl]
    split_ifs <;> rfl
  by_cases hj1 : j = 1
  swap
  · simp only [hj1, ite_false, nonpos_iff_eq_zero]
    apply sum_eq_zero
    intro p hp
    have hp' := (Scenario.mem_honestFinset _).1 hp
    apply cA_eq_zero
    intro q _
    rw [out_view hv hj]
    have h1 : (if q = leader v then partyOut p (S π s (11 * v + j) p) v j else none) = none := by
      split_ifs <;> simp [hpo p hp' hj1]
    have h2 : (if p = leader v then leaderOut (S π s (11 * v + j) p) j q else none) = none := by
      split_ifs with h
      · subst h; exact hlo hp' hj1 q
      · rfl
    simp [h1, h2]
  subst hj1
  simp only [ite_true]
  split_ifs with hL
  · -- Byzantine leader: every honest party sends at most its suggestion
    calc ∑ p ∈ s.honestFinset, cA π s (11 * v + 1) p
        ≤ ∑ p ∈ s.honestFinset, 1 := by
          apply sum_le_sum; intro p hp
          have hp' := (Scenario.mem_honestFinset _).1 hp
          exact cA_view_nonleader π s hv (by norm_num) (fun h => hp' (h ▸ hL))
      _ ≤ n := by
          rw [sum_const, smul_eq_mul, mul_one]
          exact (card_le_univ _).trans (by simp)
  · -- honest leader: no suggestions are requested; it answers Byzantine complaints only
    have h0 : 11 * v < R0 n := by simpa using view_lt_R0 (n := n) hv (by norm_num : 0 < 11)
    have hreq : ∀ p, p ∉ s.byz → isReqSugg ((S π s (11 * v + 1) p).last (leader v)) = false := by
      intro p hp
      rw [S_last, aib_honest hg.rel h0 p hL]
      have hc := hall _ hL
      have hout := out_view (π := π) (p := leader v) (st := S π s (11 * v) (leader v)) hv
        (j := 0) (by norm_num) p
      simp only [Nat.add_zero] at hout
      rw [hout]
      have hlo0 : leaderOut (S π s (11 * v) (leader v)) 0 p = none := by
        cases h : (S π s (11 * v) (leader v)).commit <;> simp_all [leaderOut]
      have hpo0 : partyOut (leader v) (S π s (11 * v) (leader v)) v 0 = none := by
        cases h : (S π s (11 * v) (leader v)).commit <;> simp_all [partyOut]
      split_ifs <;> simp_all [isReqSugg]
    have hpo1 : ∀ p, p ∉ s.byz → partyOut p (S π s (11 * v + 1) p) v 1 = none := by
      intro p hp
      simp [partyOut, hreq p hp]
    rw [← add_sum_erase _ _ ((Scenario.mem_honestFinset _).2 hL)]
    have hrest : ∑ p ∈ s.honestFinset.erase (leader v), cA π s (11 * v + 1) p = 0 := by
      apply sum_eq_zero
      intro p hp
      obtain ⟨hpL, hp⟩ := mem_erase.1 hp
      have hp' := (Scenario.mem_honestFinset _).1 hp
      apply cA_eq_zero
      intro q _
      rw [out_view hv (by norm_num)]
      simp [hpL, hpo1 p hp']
    rw [hrest, add_zero]
    unfold cA
    calc _ ≤ (byzF s).card := by
          apply card_le_card
          intro q hq
          obtain ⟨-, hqL, hs⟩ := mem_filter.1 hq
          rw [mem_byzF]
          by_contra hqb
          rw [out_view hv (by norm_num)] at hs
          have hcompl : isComplain ((S π s (11 * v + 1) (leader v)).last q) = false := by
            rw [S_last, aib_honest hg.rel h0 (leader v) hqb]
            have hov := out_view (π := π) (p := q) (st := S π s (11 * v) q) hv (j := 0)
              (by norm_num) (leader v)
            simp only [Nat.add_zero] at hov
            rw [hov]
            have hpo0 : partyOut q (S π s (11 * v) q) v 0 = none := by
              have := hall q hqb
              cases h : (S π s (11 * v) q).commit <;> simp_all [partyOut]
            simp [hqL, hpo0, isComplain]
          have hc1 := hcom _ hL 1
          have hlo1 : leaderOut (S π s (11 * v + 1) (leader v)) 1 q = none := by
            unfold leaderOut
            simp only [one_ne_zero, ite_false, ite_true]
            split <;> simp_all
          simp [hqL, hlo1] at hs
      _ ≤ _ := le_rfl

end Podc.FewToManyFaultsBA.Sync

/-! ### The rounds after the views and stage B -/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {Mf Sf : Type}
  {Afb : Protocol (Fin n) Bool Mf Bool} {Af : Auth (Fin n) Mf Sf}

lemma cA_ge_R0 (π : Params n) (s : Scenario (Fin n) Bool (Msg n)) {r : ℕ} (hr : R0 n ≤ r)
    (p : Fin n) : cA π s r p = 0 :=
  cA_eq_zero fun q _ => out_none_ge hr q

section Decided

variable {s : Scenario (Fin n) Bool (Msg n)} (hg : Good π s)
  (hall : ∀ q, q ∉ s.byz → (S π s (Rh n) q).commit.isSome)
include hg hall

lemma cA_Rh_decided {p : Fin n} (hp : p ∉ s.byz) : cA π s (Rh n) p = 0 := by
  apply cA_eq_zero
  intro q _
  rw [out_Rh]
  have := hall p hp
  cases h : (S π s (Rh n) p).commit <;> simp_all

lemma cA_Rh1_decided {p : Fin n} (hp : p ∉ s.byz) : cA π s (Rh n + 1) p ≤ (byzF s).card := by
  have hfb := no_fb_of_commit hg hall (Rh n + 2) p hp
  rw [S_fb_Rh1] at hfb
  have hown : ownFb π.t (S π s (Rh n + 1) p).last = none := by
    cases h : ownFb π.t (S π s (Rh n + 1) p).last <;> simp_all
  unfold cA
  apply card_le_card
  intro q hq
  obtain ⟨-, hqp, hs⟩ := mem_filter.1 hq
  rw [mem_byzF]
  by_contra hqb
  have hhelp : isHelp ((S π s (Rh n + 1) p).last q) = false := by
    rw [S_last, aib_honest hg.rel Rh_lt_R0 p hqb, out_Rh]
    have := hall q hqb
    cases h : (S π s (Rh n) q).commit <;> simp_all [isHelp]
  rw [out_Rh1] at hs
  simp [hhelp, hown] at hs

lemma cA_Rh2_decided {p : Fin n} (hp : p ∉ s.byz) : cA π s (Rh n + 2) p = 0 :=
  cA_eq_zero fun q _ => out_Rh2_none p q (no_fb_of_commit hg hall _ p hp)

end Decided

lemma sum_range_mul11 (f : ℕ → ℕ) (m : ℕ) :
    ∑ r ∈ range (11 * m), f r = ∑ v ∈ range m, ∑ j ∈ range 11, f (11 * v + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 11 * (m + 1) = 11 * m + 11 by ring, sum_range_add, ih,
      sum_range_succ (fun v => ∑ j ∈ range 11, f (11 * v + j)) m]

open Classical in
lemma card_byz_views (s : Scenario (Fin n) Bool (Msg n)) :
    ((range n).filter fun v => leader (n := n) v ∈ s.byz).card ≤ (byzF s).card := by
  classical
  have : ((range n).filter fun v => leader (n := n) v ∈ s.byz).image (leader (n := n)) ⊆ byzF s := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hq
    exact mem_byzF.2 (mem_filter.1 hw).2
  rw [← card_image_of_injOn (f := leader (n := n)) (fun a ha b hb h => leader_injOn
    (mem_range.1 (mem_filter.1 ha).1) (mem_range.1 (mem_filter.1 hb).1) h)]
  exact card_le_card this

/-- The message bound of `SyncBA`. -/
def msgBound (π : Params n) (f mfb : ℕ) : ℕ :=
  if f + π.k ≤ n then 22 * n * (2 * f + 1) + 3 * n * f else 25 * n * n + n * mfb

/-- **Message complexity of `SyncBA`** (Lemma B.11, Theorem B.13): honest parties send at most
`22n(2f+1) + 3nf` messages if `f + k ≤ n`, and at most `25n² + n·mfb` otherwise (`mfb` = per-party
budget of the fallback). -/
theorem syncBA_msgs {Rfb mfb : ℕ} (hres : 2 * π.t < n) (hfb : Fallback Afb Af π.t Rfb mfb)
    (sc : Scenario (Fin n) Bool (Msg n ⊕ Mf)) (hZ : sc.byz.ncard ≤ π.t) (hrel : sc.Reliable)
    (hV : sc.AuthValid (G n) (syncBA π Afb) (Auth.seq auth Af)) (T : ℕ) :
    honestMsgs (syncBA π Afb) sc T ≤ msgBound π sc.byz.ncard mfb := by
  classical
  have hg := good_scA hres hZ hrel hV
  set s₁ := scA sc
  set f := sc.byz.ncard with hfdef
  have hfeq : (byzF s₁).card = f := card_byzF s₁
  have hHon : sc.honestFinset.card ≤ n := (card_le_univ _).trans (by simp)
  have hHon₁ : s₁.honestFinset.card ≤ n := (card_le_univ _).trans (by simp)
  -- reduce to `R0 + T` rounds and split
  have hmono : honestMsgs (syncBA π Afb) sc T ≤ honestMsgs (syncBA π Afb) sc (R0 n + T) :=
    sum_le_sum_of_subset (range_mono (by omega))
  refine hmono.trans ?_
  unfold honestMsgs
  rw [show R0 n + T = 11 * n + (3 + T) by unfold R0; omega, sum_range_add, sum_range_add,
    sum_range_mul11]
  -- stage-A rounds as `cA`
  have hA : ∀ r, r < R0 n → ∑ p ∈ sc.honestFinset, sendsAt (syncBA π Afb) sc r p =
      ∑ p ∈ s₁.honestFinset, cA π s₁ r p := fun r hr => sum_congr rfl fun p _ => sendsAt_lt hr p
  have hB : ∀ j, ∑ p ∈ sc.honestFinset, sendsAt (syncBA π Afb) sc (11 * n + 3 + j) p =
      ∑ p ∈ sc.honestFinset, sendsAt (stageB Afb) (scB (π := π) sc) j p := fun j =>
    sum_congr rfl fun p _ => by rw [show 11 * n + 3 + j = R0 n + j by unfold R0; omega,
      sendsAt_ge]
  have hv : ∀ v ∈ range n, ∀ j ∈ range 11, 11 * v + j < R0 n := fun v hv j hj => by
    have := mem_range.1 hv; have := mem_range.1 hj; unfold R0; omega
  rw [sum_congr rfl fun v hv' => sum_congr rfl fun j hj => hA _ (hv v hv' j hj)]
  rw [sum_range_succ, sum_range_succ, sum_range_one, hA _ (by unfold R0; omega),
    hA _ (by unfold R0; omega), hA _ (by unfold R0; omega)]
  simp only [show 11 * n + 0 = Rh n by rfl, show 11 * n + 1 = Rh n + 1 by rfl,
    show 11 * n + 2 = Rh n + 2 by rfl, ← add_assoc]
  simp only [show ∀ j, 11 * n + 3 + j = 11 * n + 3 + j from fun _ => rfl, hB]
  -- stage B: per-party budgets
  have hBsum : ∑ j ∈ range T, ∑ p ∈ sc.honestFinset, sendsAt (stageB Afb) (scB (π := π) sc) j p ≤
      ∑ p ∈ sc.honestFinset, (if (S π s₁ (R0 n) p).fb.isSome then mfb else 0) := by
    rw [sum_comm]
    apply sum_le_sum
    intro p hp
    have hp' := (Scenario.mem_honestFinset _).1 hp
    split_ifs with hfbp
    · have hpb : p ∉ (bScen (scB (π := π) sc)).byz := mem_bScen_byz.2 ⟨hp', _, by
        show seqInputs (G n) (stageA π) (R0 n) toB sc p = _
        rw [seqInputs_val, if_pos hfbp]⟩
      rw [sum_congr rfl fun j _ => sendsAt_stageB_bScen hpb j]
      exact hfb.msgs _ p hpb T
    · rw [sum_eq_zero fun j _ => sendsAt_stageB_none (by
        show seqInputs (G n) (stageA π) (R0 n) toB sc p = _
        rw [seqInputs_val, if_neg hfbp]) j]
  unfold msgBound
  split_ifs with hfk
  · -- few faults: everybody has decided after `2f+1` views
    have hdec := all_commit hg (by rw [hfeq]; exact hfk)
    rw [hfeq] at hdec
    have hfn : 2 * f + 1 ≤ n := by have := hg.res; have := hg.faults; omega
    have hallv : ∀ v, 2 * f + 1 ≤ v → ∀ q, q ∉ s₁.byz → (S π s₁ (11 * v) q).commit.isSome :=
      fun v hv q hq => commit_mono_isSome hg (by omega) (hdec q hq)
    have hallRh : ∀ q, q ∉ s₁.byz → (S π s₁ (Rh n) q).commit.isSome :=
      fun q hq => commit_mono_isSome hg (by unfold Rh; omega) (hdec q hq)
    have hviews : ∑ v ∈ range n, ∑ j ∈ range 11, ∑ p ∈ s₁.honestFinset, cA π s₁ (11 * v + j) p ≤
        ∑ v ∈ range n, ((if v < 2 * f + 1 then 22 * n else 0) +
          (if leader (n := n) v ∈ s₁.byz then n else 0) + f) := by
      apply sum_le_sum
      intro v hv'
      have hvn := mem_range.1 hv'
      by_cases h1 : v < 2 * f + 1
      · simp only [h1, ite_true]
        calc _ ≤ ∑ j ∈ range 11, 2 * n := sum_le_sum fun j hj =>
              sum_cA_view π s₁ hvn (mem_range.1 hj) _
          _ = 22 * n := by simp; ring
          _ ≤ _ := by omega
      simp only [h1, ite_false, zero_add]
      by_cases h2 : leader (n := n) v ∈ s₁.byz
      · simp only [h2, ite_true]
        calc _ ≤ ∑ j ∈ range 11, (if j = 1 then n else 0) := sum_le_sum fun j hj => by
              have := sum_cA_decided hg hvn (mem_range.1 hj) (hallv v (by omega))
              simp only [h2, ite_true] at this; exact this
          _ = n := by simp [sum_ite_eq']
          _ ≤ _ := by omega
      · simp only [h2, ite_false, zero_add]
        calc _ ≤ ∑ j ∈ range 11, (if j = 1 then f else 0) := sum_le_sum fun j hj => by
              have := sum_cA_decided hg hvn (mem_range.1 hj) (hallv v (by omega))
              simp only [h2, ite_false, hfeq] at this; exact this
          _ = f := by simp [sum_ite_eq']
    have hsum : ∑ v ∈ range n, ((if v < 2 * f + 1 then 22 * n else 0) +
        (if leader (n := n) v ∈ s₁.byz then n else 0) + f) ≤ 22 * n * (2 * f + 1) + 2 * n * f := by
      rw [sum_add_distrib, sum_add_distrib]
      have e1 : ∑ v ∈ range n, (if v < 2 * f + 1 then 22 * n else 0) =
          ((range n).filter fun v => v < 2 * f + 1).card * (22 * n) := by
        rw [sum_ite, sum_const, sum_const_zero, smul_eq_mul, add_zero]
      have e2 : ∑ v ∈ range n, (if leader (n := n) v ∈ s₁.byz then n else 0) =
          ((range n).filter fun v => leader (n := n) v ∈ s₁.byz).card * n := by
        rw [sum_ite, sum_const, sum_const_zero, smul_eq_mul, add_zero]
      have e3 : ∑ v ∈ range n, f = n * f := by rw [sum_const, card_range, smul_eq_mul]
      rw [e1, e2, e3]
      have h1 : ((range n).filter fun v => v < 2 * f + 1).card ≤ 2 * f + 1 := by
        calc _ ≤ (range (2 * f + 1)).card := card_le_card (fun v hv => by
              rw [mem_filter] at hv; exact mem_range.2 hv.2)
          _ = _ := card_range _
      have h2 := card_byz_views s₁
      rw [hfeq] at h2
      nlinarith
    have hRh : ∑ p ∈ s₁.honestFinset, cA π s₁ (Rh n) p = 0 :=
      sum_eq_zero fun p hp => cA_Rh_decided hg hallRh ((Scenario.mem_honestFinset _).1 hp)
    have hRh1 : ∑ p ∈ s₁.honestFinset, cA π s₁ (Rh n + 1) p ≤ n * f := by
      calc _ ≤ ∑ p ∈ s₁.honestFinset, f := sum_le_sum fun p hp => by
            rw [← hfeq]; exact cA_Rh1_decided hg hallRh ((Scenario.mem_honestFinset _).1 hp)
        _ ≤ n * f := by rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hHon₁
    have hRh2 : ∑ p ∈ s₁.honestFinset, cA π s₁ (Rh n + 2) p = 0 :=
      sum_eq_zero fun p hp => cA_Rh2_decided hg hallRh ((Scenario.mem_honestFinset _).1 hp)
    have hBz : ∑ p ∈ sc.honestFinset, (if (S π s₁ (R0 n) p).fb.isSome then mfb else 0) = 0 :=
      sum_eq_zero fun p hp => by
        rw [no_fb_of_commit hg hallRh _ p ((Scenario.mem_honestFinset _).1 hp)]; rfl
    have : 3 * n * f = 2 * n * f + n * f := by ring
    linarith
  · -- many faults: generic bounds
    have hviews : ∑ v ∈ range n, ∑ j ∈ range 11, ∑ p ∈ s₁.honestFinset, cA π s₁ (11 * v + j) p ≤
        22 * n * n := by
      calc _ ≤ ∑ v ∈ range n, ∑ j ∈ range 11, 2 * n := sum_le_sum fun v hv => sum_le_sum
            fun j hj => sum_cA_view π s₁ (mem_range.1 hv) (mem_range.1 hj) _
        _ = 22 * n * n := by simp; ring
    have hgen : ∀ r, ∑ p ∈ s₁.honestFinset, cA π s₁ r p ≤ n * n := fun r =>
      calc _ ≤ ∑ p ∈ s₁.honestFinset, n := sum_le_sum fun p _ => cA_le π s₁ r p
        _ ≤ n * n := by rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hHon₁
    have hBn : ∑ p ∈ sc.honestFinset, (if (S π s₁ (R0 n) p).fb.isSome then mfb else 0) ≤ n * mfb :=
      calc _ ≤ ∑ p ∈ sc.honestFinset, mfb := sum_le_sum fun p _ => by split_ifs <;> omega
        _ ≤ n * mfb := by rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hHon
    have h1 := hgen (Rh n); have h2 := hgen (Rh n + 1); have h3 := hgen (Rh n + 2)
    linarith

end Podc.FewToManyFaultsBA.Sync
