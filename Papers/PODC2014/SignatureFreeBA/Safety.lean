import Papers.PODC2014.SignatureFreeBA.Model

/-!
# Safety: Lemmas 1–4 and the safety half of Theorem 2

Mostéfaoui, Moumen, Raynal, PODC 2014, Section 4.3.

All statements hold in every reachable state of the asynchronous system, for every coin
sequence, against an adaptive Byzantine adversary that corrupts at most `t` processes, if
`3t < n`. "Correct" processes are those of a set `H` that contains every corrupted process'
complement (`σ.bad ⊆ Hᶜ`, `|Hᶜ| ≤ t`); in the paper's static model `H` is the set of correct
processes.

* `est_just`, `aux_just`, `aux_unique`, `est_unique`: what the guards guarantee.
* `lemma_2`: two processes whose `values` in round `r` are singletons have the same value.
* `est_coin_of_single`: if a process decides `v` in round `r` (singleton `values = {v}` and
  coin `v`), every process starts round `r + 1` with estimate `v` (proof of Lemma 4).
* `lemma_1`: once all correct processes start a round with estimate `v`, no correct process
  ever broadcasts `B_VAL[r'](¬v)` or `AUX[r'](¬v)` in a later round, so all keep `v`.
* `lemma_3` (BC-Validity) and `lemma_4` (BC-Agreement); `theorem_2_safety`.
-/

namespace Podc.SignatureFreeBA

open Cslib.Byzantine.AsyncBroadcast

variable {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {coin : ℕ → Bool} {x : P → Bool}
  {k : FaultKind} {σ : State P Msg Bool}

/-! ### Justifications of broadcasts and decisions -/

/-- The own estimate of round `r + 2` is computed from a quorum of round `r + 1`
(lines 05–11). -/
theorem est_just (h : Reachable (mmr t coin) x k t σ) {p : P} {r : ℕ} {v d : Bool}
    (hm : (p, .bval (r + 2) v (some d)) ∈ σ.sent) :
    ∃ V, AuxQuorum t (σ.inbox p) (r + 1) V ∧ nextEst V (coin (r + 1)) = (v, d) := by
  refine h.sent_just (J := fun _ m ib _ => ∀ r v d, m = .bval (r + 2) v (some d) →
    ∃ V, AuxQuorum t ib (r + 1) V ∧ nextEst V (coin (r + 1)) = (v, d)) ?_ ?_ hm r v d rfl
  · intro p m ib ib' out out' hib _ hj r v d hv
    obtain ⟨V, hV, he⟩ := hj r v d hv
    exact ⟨V, hV.mono hib, he⟩
  · intro p ib out m hs r v d hv
    subst hv
    exact hs.2.2

/-- The own estimate of round 1 is the input, with tag `false`. -/
theorem est1_just (h : Reachable (mmr t coin) x k t σ) {p : P} {v d : Bool}
    (hm : (p, .bval 1 v (some d)) ∈ σ.sent) : v = x p ∧ d = false := by
  refine h.sent_just (J := fun p m _ _ => ∀ v d : Bool, m = .bval 1 v (some d) →
    v = x p ∧ d = false) (by intro _ _ _ _ _ _ _ _ hj; exact hj) ?_ hm v d rfl
  intro p ib out m hs v d hv
  subst hv
  exact ⟨hs.1, hs.2.1⟩

/-- No own estimate for round 0. -/
theorem est0_not (h : Reachable (mmr t coin) x k t σ) {p : P} {v d : Bool} :
    (p, .bval 0 v (some d)) ∉ σ.sent := fun hm => by
  have := h.sent_just (J := fun _ m _ _ => ∀ v d : Bool, m ≠ .bval 0 v (some d))
    (by intro _ _ _ _ _ _ _ _ hj; exact hj) (by
      intro p ib out m hs v d hv
      subst hv
      exact hs) hm v d
  exact this rfl

/-- `AUX[r](w)` is broadcast only with `w ∈ bin_values[r]` (line 04). -/
theorem aux_just (h : Reachable (mmr t coin) x k t σ) {p : P} {r : ℕ} {w : Bool}
    (hm : (p, .aux r w) ∈ σ.sent) : BinVal t (σ.inbox p) r w := by
  refine h.sent_just (J := fun _ m ib _ => ∀ r w, m = .aux r w → BinVal t ib r w) ?_ ?_ hm r w rfl
  · intro p m ib ib' out out' hib _ hj r w hv
    exact (hj r w hv).mono hib
  · intro p ib out m hs r w hv
    subst hv
    exact hs.2.1

/-- An echo `B_VAL[r](v)` is broadcast only after receiving it from `t + 1` processes. -/
theorem echo_just (h : Reachable (mmr t coin) x k t σ) {p : P} {r : ℕ} {v : Bool}
    (hm : (p, .bval r v none) ∈ σ.sent) : t + 1 ≤ bvCnt (σ.inbox p) r v := by
  refine h.sent_just (J := fun _ m ib _ => ∀ r v, m = .bval r v none → t + 1 ≤ bvCnt ib r v)
    ?_ ?_ hm r v rfl
  · intro p m ib ib' out out' hib _ hj r v hv
    exact (hj r v hv).trans (cntP_mono hib _)
  · intro p ib out m hs r v hv
    subst hv
    exact hs.1

/-- Every process broadcasts at most one `AUX[r](·)` (line 04 is executed once per round). -/
theorem aux_unique (h : Reachable (mmr t coin) x k t σ) {p : P} {r : ℕ} {v w : Bool}
    (hv : (p, .aux r v) ∈ σ.sent) (hw : (p, .aux r w) ∈ σ.sent) : v = w := by
  have := h.sent_excl (IsAux r) ?_ hv hw ⟨v, rfl⟩ ⟨w, rfl⟩
  · simpa using this
  · intro p ib out m hs hm m' hm' h2
    obtain ⟨u, rfl⟩ := hm
    exact hs.2.2 m' hm' h2

/-- Every process has at most one estimate per round. -/
theorem est_unique (h : Reachable (mmr t coin) x k t σ) {p : P} {r : ℕ} {v w : Bool}
    {d e : Bool} (hv : (p, .bval r v (some d)) ∈ σ.sent) (hw : (p, .bval r w (some e)) ∈ σ.sent) :
    v = w ∧ d = e := by
  have := h.sent_excl (IsEst r) ?_ hv hw ⟨v, d, rfl⟩ ⟨w, e, rfl⟩
  · simpa using this
  · intro p ib out m hs hm m' hm' h2
    obtain ⟨u, d, rfl⟩ := hm
    match r, hs with
    | 0, hs => exact hs.elim
    | 1, hs => exact hs.2.2 m' hm' h2
    | r + 2, hs => exact hs.2.1 m' hm' h2

/-- Decisions are justified by the decide guard. -/
theorem dec_just (h : Reachable (mmr t coin) x k t σ) {p : P} {o : Bool}
    (ho : σ.dec p = some o) : ∃ r, (p, .bval (r + 1) o (some true)) ∈ σ.sent ∧ coin r = o := by
  refine h.dec_just (J := fun _ o _ out => ∃ r, Msg.bval (r + 1) o (some true) ∈ out ∧ coin r = o)
    ?_ ?_ ho
  · intro p o ib ib' out out' _ hout ⟨r, hr, hc⟩
    exact ⟨r, hout hr, hc⟩
  · intro p ib out o hd
    exact hd

/-! ### Counting -/

omit [DecidableEq P] in
/-- If more than `|Hᶜ|` processes sent `B_VAL[r](v)` to `q`, one of them is in `H`. -/
theorem exists_bval_sender_mem {H : Set P} {ib : P → Set Msg} {r : ℕ} {v : Bool} {c : ℕ}
    (hH : Hᶜ.ncard ≤ c) (hc : c + 1 ≤ bvCnt ib r v) : ∃ s ∈ H, ∃ d, Msg.bval r v d ∈ ib s := by
  have hlt : Hᶜ.ncard < {s | ∃ m ∈ ib s, IsBval r v m}.ncard := by
    unfold bvCnt cntP at hc; omega
  obtain ⟨s, ⟨m, hm, d, rfl⟩, hs⟩ := exists_mem_not_mem_of_ncard_lt hlt
  exact ⟨s, by simpa using hs, d, hm⟩

/-- **Lemma 2.** If the sets `values` of round `r` of two processes are singletons `{v}` and
`{w}` (witnessed by their `n − t` `AUX` messages), then `v = w`. -/
theorem lemma_2 (ht : 3 * t < Fintype.card P) (h : Reachable (mmr t coin) x k t σ) {p q : P}
    {r : ℕ} {V W : Finset Bool} {v w : Bool} (hV : AuxQuorum t (σ.inbox p) r V)
    (hW : AuxQuorum t (σ.inbox q) r W) (hv : ∀ u ∈ V, u = v) (hw : ∀ u ∈ W, u = w) : v = w := by
  obtain ⟨S, f, hS, hf, rfl⟩ := hV
  obtain ⟨S', f', hS', hf', rfl⟩ := hW
  have hb := h.bad_ncard_le
  obtain ⟨s, hs, hs', hsb⟩ := exists_mem_inter_not_mem (S₁ := (S : Set P)) (S₂ := (S' : Set P))
    (B := σ.bad) (by simp only [Set.ncard_coe_finset]; omega)
  have h1 := h.genuine (hf s hs).1 hsb
  have h2 := h.genuine (hf' s hs').1 hsb
  rw [← hv (f s) (Finset.mem_image_of_mem f hs), ← hw (f' s) (Finset.mem_image_of_mem f' hs')]
  exact aux_unique h h1 h2

/-- Proof of Lemma 4, first part: if some process has `values = {v}` in round `r + 1` and the
coin of round `r + 1` is `v`, then every process starts round `r + 2` with estimate `v`. -/
theorem est_coin_of_single (ht : 3 * t < Fintype.card P) (h : Reachable (mmr t coin) x k t σ)
    {p q : P} {r : ℕ} {v w : Bool} {e : Bool}
    (hp : (p, .bval (r + 2) v (some true)) ∈ σ.sent) (hc : coin (r + 1) = v)
    (hq : (q, .bval (r + 2) w (some e)) ∈ σ.sent) : w = v := by
  obtain ⟨V, hV, hVe⟩ := est_just h hp
  obtain ⟨W, hW, hWe⟩ := est_just h hq
  cases e
  · rw [nextEst_false hWe, hc]
  · exact (lemma_2 ht h hV hW (nextEst_true hVe) (nextEst_true hWe)).symm

/-- **Lemma 1** (in invariant form). Let `r₀ ≥ 1` and suppose every process of `H` that starts
round `r₀` does so with estimate `v`. Then no process of `H` ever broadcasts `B_VAL[r](¬v)`
or `AUX[r](¬v)` for `r ≥ r₀`; in particular all of them keep the estimate `v` in all later
rounds. -/
theorem lemma_1 (h : Reachable (mmr t coin) x k t σ) {H : Set P} (hbad : σ.bad ⊆ Hᶜ)
    (hH : Hᶜ.ncard ≤ t) (ht : t < Fintype.card P) {r₀ : ℕ} (hr₀ : 1 ≤ r₀) {v : Bool}
    (hbase : ∀ p ∈ H, ∀ w d, (p, .bval r₀ w (some d)) ∈ σ.sent → w = v) :
    ∀ p ∈ H, ∀ r, r₀ ≤ r → (∀ d, (p, .bval r (!v) d) ∉ σ.sent) ∧ (p, .aux r (!v)) ∉ σ.sent := by
  revert hbad hbase
  refine Reachable.induction (Inv := fun σ => σ.bad ⊆ Hᶜ →
    (∀ p ∈ H, ∀ w d, (p, .bval r₀ w (some d)) ∈ σ.sent → w = v) →
    ∀ p ∈ H, ∀ r, r₀ ≤ r → (∀ d, (p, .bval r (!v) d) ∉ σ.sent) ∧ (p, .aux r (!v)) ∉ σ.sent)
    (by simp [State.init]) ?_ h
  intro σ σ' hr ih hst hbad' hbase'
  have hbad : σ.bad ⊆ Hᶜ := hst.bad_subset.trans hbad'
  have ih := ih hbad fun p hp w d hm => hbase' p hp w d (hst.sent_subset hm)
  -- no `¬v` is in `bin_values` (nor echoed) at any process, in rounds `≥ r₀`
  have hcnt : ∀ q r c, r₀ ≤ r → Hᶜ.ncard ≤ c → ¬ c + 1 ≤ bvCnt (σ.inbox q) r (!v) := by
    intro q r c hrr hc hcnt
    obtain ⟨s, hs, d, hm⟩ := exists_bval_sender_mem hc hcnt
    exact (ih s hs r hrr).1 d (hr.genuine hm fun hb => hbad hb hs)
  have hbin : ∀ q r, r₀ ≤ r → ¬ BinVal t (σ.inbox q) r (!v) := fun q r hr hb =>
    hcnt q r (2 * t) hr (by omega) hb
  cases hst with
  | send p' m hb hg =>
    intro p hp r hr
    refine ⟨fun d hm => ?_, fun hm => ?_⟩
    · rcases Set.mem_insert_iff.1 hm with he | hm
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        match r, d, hg with
        | r, none, hg => exact hcnt p r t hr hH hg.1
        | 0, some d, hg => exact hg
        | 1, some d, hg =>
          have : r₀ = 1 := by omega
          subst this
          have := hbase' p hp (!v) d (Set.mem_insert _ _)
          cases v <;> simp at this
        | r + 2, some d, hg =>
          obtain ⟨-, -, V, hV, hVe⟩ := hg
          by_cases hr' : r + 2 = r₀
          · have := hbase' p hp (!v) d (by rw [hr']; exact Set.mem_insert _ _)
            cases v <;> simp at this
          · have hV1 : ∀ u ∈ V, u = v := by
              obtain ⟨S, f, -, hf, rfl⟩ := hV
              intro u hu
              obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
              by_contra hne
              have : f s = !v := by cases v <;> cases hfs : f s <;> simp_all
              exact hbin p (r + 1) (by omega) (this ▸ (hf s hs).2)
            rw [nextEst_of_subset (hV.nonempty ht) hV1] at hVe
            simp only [Prod.mk.injEq] at hVe
            cases v <;> simp at hVe
      · exact (ih p hp r hr).1 d hm
    · rcases Set.mem_insert_iff.1 hm with he | hm
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hbin p r hr hg.2.1
      · exact (ih p hp r hr).2 hm
  | _ => exact ih

/-- **Lemma 3** (BC-Validity). If all processes of `H` propose `v`, no process of `H` ever
decides `¬v` (for binary values: a decided value was proposed by a correct process). -/
theorem lemma_3 (ht : 3 * t < Fintype.card P) (h : Reachable (mmr t coin) x k t σ) {H : Set P}
    (hbad : σ.bad ⊆ Hᶜ) (hH : Hᶜ.ncard ≤ t) {v : Bool} (hx : ∀ p ∈ H, x p = v) {p : P}
    (hp : p ∈ H) {o : Bool} (ho : σ.dec p = some o) : o = v := by
  obtain ⟨r, hm, -⟩ := dec_just h ho
  have := lemma_1 h hbad hH (by omega) le_rfl (v := v)
    (fun p hp w d hm => (est1_just h hm).1 ▸ hx p hp) p hp (r + 1) (by omega)
  by_contra hne
  have : o = !v := by cases o <;> cases v <;> simp_all
  subst this
  exact this.1 _ hm

/-- **Lemma 4** (BC-Agreement). Two processes of `H` never decide different values. -/
theorem lemma_4 (ht : 3 * t < Fintype.card P) (h : Reachable (mmr t coin) x k t σ) {H : Set P}
    (hbad : σ.bad ⊆ Hᶜ) (hH : Hᶜ.ncard ≤ t) {p q : P} (hp : p ∈ H) (hq : q ∈ H) {u w : Bool}
    (hu : σ.dec p = some u) (hw : σ.dec q = some w) : u = w := by
  -- the decision of the earlier round fixes all later estimates
  have key : ∀ {p q : P} {u w : Bool} {r r' : ℕ}, p ∈ H → q ∈ H → r ≤ r' →
      (p, .bval (r + 1) u (some true)) ∈ σ.sent → coin r = u →
      (q, .bval (r' + 1) w (some true)) ∈ σ.sent → u = w := by
    intro p q u w r r' hp hq hrr hpm hc hqm
    match r, hpm, hc with
    | 0, hpm, _ => exact absurd (est1_just h hpm).2 (by simp)
    | r + 1, hpm, hc =>
      have := lemma_1 h hbad hH (by omega) (r₀ := r + 2) (by omega) (v := u)
        (fun p' _ w' d' hm' => est_coin_of_single ht h hpm hc hm') q hq (r' + 1) (by omega)
      by_contra hne
      have : w = !u := by cases w <;> cases u <;> simp_all
      subst this
      exact this.1 _ hqm
  obtain ⟨r, hpm, hpc⟩ := dec_just h hu
  obtain ⟨r', hqm, hqc⟩ := dec_just h hw
  rcases le_total r r' with hrr | hrr
  · exact key hp hq hrr hpm hpc hqm
  · exact (key hq hp hrr hqm hqc hpm).symm

/-- **Theorem 2**, safety part: BC-Validity, BC-Agreement and BC-One-shot (decisions are
recorded once and never change) hold in every reachable state, for every coin sequence. -/
theorem theorem_2_safety (ht : 3 * t < Fintype.card P) (h : Reachable (mmr t coin) x k t σ)
    {H : Set P} (hbad : σ.bad ⊆ Hᶜ) (hH : Hᶜ.ncard ≤ t) :
    (∀ v, (∀ p ∈ H, x p = v) → ∀ p ∈ H, ∀ o, σ.dec p = some o → o = v) ∧
    (∀ p ∈ H, ∀ q ∈ H, ∀ u w, σ.dec p = some u → σ.dec q = some w → u = w) ∧
    (∀ σ', Reach (mmr t coin) x k t σ σ' → ∀ p o, σ.dec p = some o → σ'.dec p = some o) :=
  ⟨fun _ hx _ hp _ ho => lemma_3 ht h hbad hH hx hp ho,
    fun _ hp _ hq _ _ hu hw => lemma_4 ht h hbad hH hp hq hu hw,
    fun _ h' _ _ ho => h'.dec_mono ho⟩

end Podc.SignatureFreeBA
