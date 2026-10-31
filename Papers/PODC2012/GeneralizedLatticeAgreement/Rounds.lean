import Papers.PODC2012.GeneralizedLatticeAgreement.InitInv

/-!
# Rounds: Lemmas 5.7–5.11 of [paper]

The paper partitions an execution into rounds using the chain `v₁ ⊏ ⋯ ⊏ v_k` of all values chosen
in the (finite) execution: a value `v` is in round `r` iff `v ⊑ v_r` and `v ⋢ v_{r-1}` (round
`k + 1` if `v ⋢ v_k`). Since the chosen values form a chain (Lemma 5.5), two values are in the same
round iff they lie below exactly the same chosen values; this is our `SameRound s u v`, stated
for the chosen values of the current state `s` (the end of a finite execution). It needs no
indexing of the chosen chain. (The paper's dummy round 0 for `v = ⊥` plays no role: proposed
values are never `⊥`.)

* Lemma 5.7: `lemma_5_7` (proposals of a proposer strictly increase).
* Lemma 5.8 holds by definition (`lemma_5_8`).
* Lemma 5.9: at most one `Propose` per proposer per round (`lemma_5_9_propose`). Its second
  half, "at most one `Decide` per round", is false for the pseudocode as written
  (`Cex59.lemma_5_9_decide_false`); it holds for decisions taken with `nackCount = 0`
  (`lemma_5_9_decide_clean`).
* Lemma 5.10: `lemma_5_10` (in the stronger form: for every chosen `c` with `w₁ ⋢ c`, `c ⊑ w₂`).
* Lemma 5.11: a proposer makes at most `N_p + 1` proposals in a round (`lemma_5_11`).
-/

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}
variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

/-- `u` and `v` belong to the same round (w.r.t. the values chosen in `s`): they are below the
same chosen values. -/
def SameRound (s : State P A Ln L) (u v : L) : Prop := ∀ c, Chosen s c → (u ≤ c ↔ v ≤ c)

variable {s : State P A Ln L}

lemma SameRound.symm {u v : L} (h : SameRound s u v) : SameRound s v u :=
  fun c hc => (h c hc).symm

namespace Inv

variable (h : Inv s)
include h

lemma prop_le_of_le {p : P} {n n' : ℕ} {v v' : L} (hv : Msg.proposal p n v ∈ s.sent)
    (hv' : Msg.proposal p n' v' ∈ s.sent) (hle : n ≤ n') : v ≤ v' := by
  induction n', hle using Nat.le_induction generalizing v' with
  | base => exact (h.prop_unique hv hv').le
  | succ k hk ih =>
    have h1 := (h.prop_range hv).1
    have h2 := (h.prop_range hv').2
    obtain ⟨w, hw⟩ := h.prop_exists (p := p) (n := k) (by omega) (by omega)
    exact (ih hw).trans (h.prop_succ hw hv').le

lemma prop_lt_of_lt {p : P} {n n' : ℕ} {v v' : L} (hv : Msg.proposal p n v ∈ s.sent)
    (hv' : Msg.proposal p n' v' ∈ s.sent) (hlt : n < n') : v < v' := by
  have h1 := (h.prop_range hv).1
  have h2 := (h.prop_range hv').2
  obtain ⟨w, hw⟩ := h.prop_exists (p := p) (n := n' - 1) (by omega) (by omega)
  have := h.prop_succ hw (by rwa [Nat.sub_add_cancel (by omega)])
  exact lt_of_le_of_lt (h.prop_le_of_le hv hw (by omega)) this

/-- The chosen values are closed under binary joins (they form a chain). -/
lemma chosen_sup_mem {u v : L} (hu : Chosen s u) (hv : Chosen s v) : Chosen s (u ⊔ v) := by
  rcases h.chosen_comparable hu hv with huv | hvu
  · rwa [sup_eq_right.2 huv]
  · rwa [sup_eq_left.2 hvu]

end Inv

variable {b : P → L}

/-- Lemma 5.7 of [paper]: values proposed by a single proposer strictly increase: if `v` is the
value of proposal number `i` and `v'` the value of proposal number `i + 1` of `p`, then `v ⊏ v'`. -/
theorem lemma_5_7 (hs : Reachable b s) {p : P} {i : ℕ} {v v' : L}
    (hv : Msg.proposal p i v ∈ s.sent) (hv' : Msg.proposal p (i + 1) v' ∈ s.sent) : v < v' :=
  hs.inv.prop_succ hv hv'

/-- Lemma 5.8 of [paper] (by definition of rounds): if `v` is in the same round as a chosen
value `c` (the value chosen in that round), then `v ⊑ c`. -/
theorem lemma_5_8 {v c : L} (hc : Chosen s c) (hround : SameRound s v c) : v ≤ c :=
  (hround c hc).2 le_rfl

/-- Lemma 5.9 of [paper], first half: a proposer executes at most one `Propose` step in a round:
two initiated proposals of the same proposer are in different rounds. -/
theorem lemma_5_9_propose (hs : Reachable b s) {q : P} {m₁ m₂ : ℕ} {u₁ u₂ : L}
    (hi₁ : (q, m₁) ∈ s.initiated) (hi₂ : (q, m₂) ∈ s.initiated)
    (hu₁ : Msg.proposal q m₁ u₁ ∈ s.sent) (hu₂ : Msg.proposal q m₂ u₂ ∈ s.sent)
    (hlt : m₁ < m₂) : ¬ SameRound s u₁ u₂ := by
  have h := hs.inv
  have h1 := (h.prop_range hu₁).1
  have h2 := (h.prop_range hu₂).2
  obtain ⟨w, hw⟩ := h.prop_exists (p := q) (n := m₂ - 1) (by omega) (by omega)
  have hq := h.init_quorum hi₂ (by omega)
  have hc : Chosen s w := h.chosen_of_quorum hw hq
  have hle : u₁ ≤ w := h.prop_le_of_le hu₁ hw (by omega)
  have hlt' : w < u₂ := h.prop_succ hw (by rwa [Nat.sub_add_cancel (by omega)])
  intro hr
  exact absurd ((hr w hc).1 hle) (not_le_of_gt hlt')

/-- Lemma 5.9 of [paper], second half, for decisions taken with `nackCount = 0` (the repaired
`Decide`): such decisions of one proposer are in different rounds. -/
theorem lemma_5_9_decide_clean (hs : Reachable b s) {q : P} {n n' : ℕ} {d d' : L}
    (hd : (q, n, d, true) ∈ s.decisions) (hd' : (q, n', d', true) ∈ s.decisions) (hlt : n < n') :
    ¬ SameRound s d d' := by
  have h := hs.inv
  have hdp := h.dec_clean hd
  have hdp' := h.dec_clean hd'
  have hc : Chosen s d := h.chosen_of_quorum hdp (h.dec_quorum hd).2.2
  have hlt' := h.prop_lt_of_lt hdp hdp' hlt
  intro hr
  exact absurd ((hr d hc).1 le_rfl) (not_le_of_gt hlt')

/-- Lemma 5.10 of [paper]: if `w₁` and `w₂` are consecutive proposals of a proposer, then every
chosen value `c` with `w₁ ⋢ c` satisfies `c ⊑ w₂`. (The paper's statement is the case
`c = v_{r-1}` with `w₁` in round `r`, i.e. `w₁ ⋢ v_{r-1}`.) -/
theorem lemma_5_10 (hs : Reachable b s) {p : P} {n : ℕ} {w₁ w₂ c : L}
    (hw₁ : Msg.proposal p n w₁ ∈ s.sent) (hw₂ : Msg.proposal p (n + 1) w₂ ∈ s.sent)
    (hc : Chosen s c) (hnot : ¬ w₁ ≤ c) : c ≤ w₂ := by
  have h := hs.inv
  obtain ⟨R, hR, hR'⟩ := h.prev_quorum (h.prop_range hw₁).1 hw₂
  obtain ⟨p', n', hc⟩ := hc
  obtain ⟨a, ha⟩ := quorum_inter hR hc
  simp only [Finset.mem_inter, ackers, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨ρ, hρ, hρle⟩ := hR' a ha.1
  have hw₁ρ : w₁ ≤ ρ := by
    rcases hρ with hρ | hρ
    · exact (h.prop_unique hw₁ (h.ack_prop hρ)).le
    · obtain ⟨v, hv, hlt⟩ := h.nack_prop hρ
      exact (h.prop_unique hw₁ hv).le.trans hlt.le
  have hmem : ρ ∈ respVals s a := ⟨p, n, hρ⟩
  rcases h.resp_chain hmem ⟨p', n', Or.inl ha.2⟩ with h1 | h1
  · exact absurd (hw₁ρ.trans h1) hnot
  · exact h1.trans hρle

/-- Lemma 5.11 of [paper]: a proposer makes at most `N_p + 1` proposals in a single round. Here
`N` is any set of proposal numbers of `p` whose values are pairwise in the same round. -/
theorem lemma_5_11 (hs : Reachable b s) (p : P) (N : Finset ℕ) (w : ℕ → L)
    (hw : ∀ n ∈ N, Msg.proposal p n (w n) ∈ s.sent)
    (hround : ∀ n ∈ N, ∀ n' ∈ N, SameRound s (w n) (w n')) :
    N.card ≤ Fintype.card P + 1 := by
  classical
  have h := hs.inv
  have hi := hs.initInv
  rcases N.eq_empty_or_nonempty with hN | hN
  · simp [hN]
  set n₁ := N.min' hN with hn₁
  have hn₁N : n₁ ∈ N := N.min'_mem hN
  set I := initVals s
  -- `w n` is the join of the initiated values below it
  have hjoin : ∀ n ∈ N, w n = (I.filter (· ≤ w n)).sup id := fun n hn =>
    IsJoinOf.eq_sup_filter (hi.prop (hw n hn)).1
  set cov : ℕ → Finset L := fun n => I.filter (· ≤ w n)
  -- previous rounds and the current round
  set Prev := I.filter fun u => ∃ c, Chosen s c ∧ u ≤ c ∧ ¬ w n₁ ≤ c
  set Curr := I.filter fun u => SameRound s u (w n₁)
  have hcov_sub : ∀ n ∈ N, cov n ⊆ Prev ∪ Curr := by
    intro n hn u hu
    simp only [cov, Finset.mem_filter] at hu
    by_cases hp : ∃ c, Chosen s c ∧ u ≤ c ∧ ¬ w n₁ ≤ c
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hu.1, hp⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hu.1, fun c hc => ⟨?_, ?_⟩⟩)
      · intro huc; by_contra hn'; exact hp ⟨c, hc, huc, hn'⟩
      · intro h1; exact hu.2.trans (((hround n₁ hn₁N n hn) c hc).1 h1)
  -- the proposals of `p` with numbers in `N` strictly increase
  have hmono : ∀ n ∈ N, ∀ n' ∈ N, n < n' → w n < w n' := fun n hn n' hn' hlt =>
    h.prop_lt_of_lt (hw n hn) (hw n' hn') hlt
  have hcov_lt : ∀ n ∈ N, ∀ n' ∈ N, n < n' → (cov n).card < (cov n').card := by
    intro n hn n' hn' hlt
    apply Finset.card_lt_card
    refine ⟨fun u hu => ?_, fun hsub => ?_⟩
    · simp only [cov, Finset.mem_filter] at hu ⊢
      exact ⟨hu.1, hu.2.trans (hmono n hn n' hn' hlt).le⟩
    · have : w n' ≤ w n := by
        rw [hjoin n' hn']
        refine Finset.sup_le fun u hu => ?_
        exact (Finset.mem_filter.1 (hsub hu)).2
      exact absurd (hmono n hn n' hn' hlt) (not_lt_of_ge this)
  -- some value of the current round is below `w n₁`
  have hu₀ : ∃ u₀ ∈ cov n₁, u₀ ∈ Curr := by
    by_contra hcon
    push_neg at hcon
    have hprev : ∀ u ∈ cov n₁, ∃ c, Chosen s c ∧ u ≤ c ∧ ¬ w n₁ ≤ c := by
      intro u hu
      rcases Finset.mem_union.1 (hcov_sub n₁ hn₁N hu) with h1 | h1
      · exact (Finset.mem_filter.1 h1).2
      · exact absurd h1 (hcon u hu)
    have hne : (cov n₁).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have h0 := hjoin n₁ hn₁N
      have : (I.filter (· ≤ w n₁)) = cov n₁ := rfl
      rw [this, he, Finset.sup_empty] at h0
      exact absurd h0 (hi.prop (hw n₁ hn₁N)).2.ne'
    choose! cf hcf using hprev
    set M := (cov n₁).sup' hne cf
    have hM : Chosen s M ∧ ¬ w n₁ ≤ M := by
      refine Finset.sup'_mem {c | Chosen s c ∧ ¬ w n₁ ≤ c} ?_ (cov n₁) hne cf
        (fun u hu => ⟨(hcf u hu).1, (hcf u hu).2.2⟩)
      intro x hx y hy
      rcases h.chosen_comparable hx.1 hy.1 with hxy | hxy
      · rwa [sup_eq_right.2 hxy]
      · rwa [sup_eq_left.2 hxy]
    apply hM.2
    rw [hjoin n₁ hn₁N]
    refine Finset.sup_le fun u hu => ?_
    exact (hcf u hu).2.1.trans (Finset.le_sup' cf hu)
  obtain ⟨u₀, hu₀c, hu₀C⟩ := hu₀
  -- the current round has at most one initiated value per proposer (Lemma 5.9)
  have hCurr : Curr.card ≤ Fintype.card P := by
    have hex : ∀ u ∈ Curr, ∃ q m, (q, m) ∈ s.initiated ∧ Msg.proposal q m u ∈ s.sent :=
      fun u hu => mem_initVals.1 (Finset.mem_filter.1 hu).1
    haveI : Nonempty P := by
      obtain ⟨q, -, -⟩ := hex u₀ hu₀C
      exact ⟨q⟩
    haveI : Inhabited P := Classical.inhabited_of_nonempty'
    choose! fq fm hfqm using hex
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn fq (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
    intro u hu u' hu' heq
    have hu1 := hfqm u hu
    have hu2 := hfqm u' hu'
    rw [heq] at hu1
    have hr : SameRound s u u' := fun c hc =>
      ((Finset.mem_filter.1 hu).2 c hc).trans ((Finset.mem_filter.1 hu').2 c hc).symm
    rcases lt_trichotomy (fm u) (fm u') with hlt | heq' | hlt
    · exact absurd hr (lemma_5_9_propose hs hu1.1 hu2.1 hu1.2 hu2.2 hlt)
    · rw [heq'] at hu1; exact h.prop_unique hu1.2 hu2.2
    · exact absurd hr.symm (lemma_5_9_propose hs hu2.1 hu1.1 hu2.2 hu1.2 hlt)
  -- every later proposal covers all values of previous rounds (Lemma 5.10)
  have hn₁' : ∀ n ∈ N, n ≠ n₁ → n₁ < n := fun n hn hne =>
    lt_of_le_of_ne (N.min'_le n hn) (Ne.symm hne)
  have hPrev : ∀ n ∈ N, n ≠ n₁ → Prev ⊆ cov n := by
    intro n hn hne u hu
    obtain ⟨hI, c, hc, huc, hnc⟩ := Finset.mem_filter.1 hu
    have hlt := hn₁' n hn hne
    obtain ⟨w₂, hw₂⟩ := h.prop_exists (p := p) (n := n₁ + 1) (by omega)
      (by have := (h.prop_range (hw n hn)).2; omega)
    have hcw₂ := lemma_5_10 hs (hw n₁ hn₁N) hw₂ hc hnc
    simp only [cov, Finset.mem_filter]
    exact ⟨hI, huc.trans (hcw₂.trans (h.prop_le_of_le hw₂ (hw n hn) (by omega)))⟩
  -- counting
  set B := insert u₀ Prev
  have hB : ∀ n ∈ N, n ≠ n₁ → B ⊆ cov n := by
    intro n hn hne
    refine Finset.insert_subset ?_ (hPrev n hn hne)
    simp only [cov, Finset.mem_filter] at hu₀c ⊢
    exact ⟨hu₀c.1, hu₀c.2.trans (hmono n₁ hn₁N n hn (hn₁' n hn hne)).le⟩
  have hu₀P : u₀ ∉ Prev := by
    intro hu
    obtain ⟨-, c, hc, huc, hnc⟩ := Finset.mem_filter.1 hu
    exact hnc (((Finset.mem_filter.1 hu₀C).2 c hc).1 huc)
  have hBcard : B.card = Prev.card + 1 := Finset.card_insert_of_notMem hu₀P
  have hUcard : (Prev ∪ Curr).card ≤ Prev.card + Curr.card := Finset.card_union_le _ _
  -- the map `n ↦ (cov n).card` is injective on `N.erase n₁` with values in an interval
  have hmaps : ∀ n ∈ N.erase n₁, (cov n).card ∈ Finset.Icc B.card (Prev ∪ Curr).card := by
    intro n hn
    obtain ⟨hne, hn⟩ := Finset.mem_erase.1 hn
    exact Finset.mem_Icc.2 ⟨Finset.card_le_card (hB n hn hne),
      Finset.card_le_card (hcov_sub n hn)⟩
  have hinj : Set.InjOn (fun n => (cov n).card) ↑(N.erase n₁) := by
    intro n hn n' hn' heq
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe] at hn hn'
    rcases lt_trichotomy n n' with hlt | heq' | hlt
    · exact absurd heq (hcov_lt n hn.1 n' hn'.1 hlt).ne
    · exact heq'
    · exact absurd heq.symm (hcov_lt n' hn'.1 n hn.1 hlt).ne
  have hcard := Finset.card_le_card_of_injOn _ (fun n hn => hmaps n hn) hinj
  rw [Nat.card_Icc] at hcard
  have hNcard := Finset.card_erase_of_mem hn₁N
  have hC1 : 1 ≤ Curr.card := Finset.card_pos.2 ⟨u₀, hu₀C⟩
  omega

end Podc.GeneralizedLatticeAgreement
