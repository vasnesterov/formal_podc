import Papers.PODC2016.UnbeatableSetConsensus.LastRound

/-!
# Lemma 1 (corrected)

**Lemma 1** of the paper: let `P` solve nonuniform `k`-set consensus and let every process that is
low at time `m` decide by time `m`. If at `⟨i, m⟩`

1. `i` is low at `m` for the first time,
2. `i` has seen a single low value `v`,
3. `HC⟨i, m⟩ ≥ k - 1`,
4. there are `k` distinct processes `j_b` with `⟨j_b, m - 1⟩` high and `⟨j_b, m⟩` hidden from
   `⟨i, m⟩`,

then `i` decides `v` at time `m`.

**As stated, Lemma 1 is false** (`Counterexample.lean`): the "changes" of its proof make a process
`j_b` receive no message carrying `v` in round `m`; this is impossible when the low value `v`
reached `i` from processes that do not crash in round `m` (it would need more than `t` crashes).
We prove it under the additional hypothesis

5. every process that is alive and low at time `m - 1` crashes in round `m`

(`Lemma1Hyp.lowCrash`), which holds wherever the paper uses the lemma (in the proof of Lemma 3,
and in the induction step itself), see `lemma1`.

The proof follows the paper's combinatorial proof: the run `r'` of Lemma 2 for the `k - 1` low
values other than `v` (`chainRun`), the induction hypothesis for the `k` processes `i_w` that
carry the low values at `m - 1` (`step_setup`), and the "changes" `k, …, 1` of the messages that
`j_1, …, j_k` receive in round `m` (`step_final`, using `lastRun`).
-/

namespace Podc.UnbeatableSetConsensus

open Cslib Finset

variable {P : Type*} [Fintype P] {k t : ℕ} {D : Set ℕ} {Q : Protocol P}

/-- In `Q`, every process that is low at time `m` has decided by time `m`. -/
def LowDecides (k t : ℕ) (D : Set ℕ) (Q : Protocol P) : Prop :=
  ∀ r, Adm t D r → ∀ i m, r.Alive i m → Low k r i m → DecidesBy Q r i m

/-- The hypotheses 1–4 of Lemma 1, as stated in the paper (for a live process `x`). -/
structure Lemma1HypPaper (k : ℕ) (r : Run P) (x : P) (m v : ℕ) : Prop where
  alive : r.Alive x m
  /-- 1. `x` is low at `m` for the first time. -/
  first : ∀ M, m = M + 1 → ¬ Low k r x M
  /-- 1–2. `x` is low at `m` and `v` is the only low value it has seen. -/
  lows_eq : lows k r x m = {v}
  /-- 3. `HC⟨x, m⟩ ≥ k - 1`. -/
  hc_ge : k - 1 ≤ hc r x m
  /-- 4. `k` distinct processes, high at `m - 1`, hidden from `⟨x, m⟩` at `m`. -/
  others : ∃ j : Fin k → P, Function.Injective j ∧
    ∀ b, (∀ M, m = M + 1 → ¬ Low k r (j b) M) ∧ Hidden r x m (j b) m

/-- The hypotheses of the corrected Lemma 1: those of the paper and hypothesis 5. -/
structure Lemma1Hyp (k : ℕ) (r : Run P) (x : P) (m v : ℕ) : Prop
    extends Lemma1HypPaper k r x m v where
  /-- 5. (added) every process alive and low at `m - 1` crashes in round `m`. -/
  lowCrash : ∀ M, m = M + 1 → ∀ y, r.Alive y M → Low k r y M → r.crash y = some m

section Common

variable (hk : 1 ≤ k) (hD : ∀ v ≤ k, v ∈ D) (hQ : SolvesSetConsensus k t D Q)
include hk hD hQ

/-- Validity + knowledge of preconditions: decided values have been seen. -/
lemma dec_mem_vals {r : Run P} (hr : Adm t D r) {i : P} {m u : ℕ} (hd : DecidesAt Q r i m u) :
    u ∈ vals r i m :=
  decided_mem_vals hQ (hD 0 (Nat.zero_le k)) (hD 1 hk) zero_ne_one hr hd

omit hk hD in
/-- If all `k` low values are decided by correct processes, no correct process decides a high
value. -/
lemma not_high_of_all_low {r : Run P} (hr : Adm t D r)
    (hall : ∀ u < k, ∃ i m, ¬ r.Faulty i ∧ DecidesAt Q r i m u) {i : P} {m u : ℕ}
    (hi : ¬ r.Faulty i) (hd : DecidesAt Q r i m u) : u < k := by
  by_contra hku
  push Not at hku
  have hsub : (↑(insert u (range k)) : Set ℕ) ⊆
      {v | ∃ i m, ¬ r.Faulty i ∧ DecidesAt Q r i m v} := by
    intro v hv
    rcases mem_insert.1 hv with rfl | hv
    · exact ⟨i, m, hi, hd⟩
    · exact hall v (mem_range.1 hv)
  have h1 := (Set.encard_le_encard hsub).trans (hQ.agreement r hr)
  rw [Set.encard_coe_eq_coe_finsetCard, card_insert_of_notMem (by simpa using hku),
    card_range] at h1
  norm_cast at h1
  omega

end Common

/-! ### The final step: the "changes" of the messages received by `j_1, …, j_k` -/

section Final

variable {r₀ : Run P} {x : P} {M : ℕ} {j : Fin k → P} {iw : ℕ → P}

/-- The decision value of `j b` in the last-round run where `j b` receives the low values `S`. -/
noncomputable def dval (k : ℕ) (Q : Protocol P) (r₀ : Run P) (x : P) (M : ℕ) (j : Fin k → P)
    (iw : ℕ → P) (b : Fin k) (S : Finset ℕ) : ℕ :=
  Classical.epsilon fun u => ∃ m' ≤ M + 1,
    DecidesAt Q (lastRun k r₀ x M j iw (fun _ => S) ∅) (j b) m' u

variable (hk : 1 ≤ k) (hD : ∀ v ≤ k, v ∈ D) (hQ : SolvesSetConsensus k t D Q)
  (hlow : LowDecides k t D Q) (hr₀ : Adm t D r₀) (LH : LastHyp k r₀ x M j iw)
include hk hD hQ hlow hr₀ LH

omit hk hD hQ in
/-- `j b` decides `dval b (σ b)` by time `M + 1` in every last-round run. -/
lemma LastHyp.decides_dval {σ : Fin k → Finset ℕ} {W : Finset ℕ} (hW : W ⊆ range k)
    (hWσ : ∀ b, W ⊆ σ b) (hσ : ∀ b, σ b ⊆ range k) (b : Fin k) (hne : (σ b).Nonempty) :
    ∃ m' ≤ M + 1, DecidesAt Q (lastRun k r₀ x M j iw σ W) (j b) m' (dval k Q r₀ x M j iw b (σ b)) := by
  set S := σ b
  set T₀ := lastRun k r₀ x M j iw (fun _ => S) ∅
  have hcor₀ : ¬ T₀.Faulty (j b) := LastHyp.correct (Or.inl (Or.inr ⟨b, rfl⟩))
  have hlowT₀ : Low k T₀ (j b) (M + 1) := by
    rw [low_iff_lows_nonempty, LH.lows_j (empty_subset _) (fun _ => empty_subset _)
      (fun _ => hσ b) b]
    exact hne
  obtain ⟨m', hm', u, hu⟩ := hlow T₀ (LastHyp.adm hr₀ _ _) (j b) (M + 1)
    (SyncCrash.Run.alive_of_not_faulty hcor₀ _) hlowT₀
  obtain ⟨m'', hm'', hd⟩ := Classical.epsilon_spec (p := fun u => ∃ m' ≤ M + 1,
    DecidesAt Q T₀ (j b) m' u) ⟨u, m', hm', hu⟩
  refine ⟨m'', hm'', ?_⟩
  have hsv := LH.sameView_j (empty_subset _) (fun _ => empty_subset _) hW hWσ b
    (σ := fun _ => S) (σ' := σ) rfl
  have hcor : ¬ (lastRun k r₀ x M j iw σ W).Faulty (j b) :=
    LastHyp.correct (Or.inl (Or.inr ⟨b, rfl⟩))
  exact (hsv.decidesAt_iff Q hm'' ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hcor _,
    fun _ => SyncCrash.Run.alive_of_not_faulty hcor₀ _⟩).1 hd

/-- The values used by `j_0, …, j_{n-1}` (the changes are processed in the order `b = 0, 1, …`). -/
noncomputable def usedVals (k : ℕ) (Q : Protocol P) (r₀ : Run P) (x : P) (M : ℕ) (j : Fin k → P)
    (iw : ℕ → P) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => if h : n < k then
      insert (dval k Q r₀ x M j iw ⟨n, h⟩ (range k \ usedVals k Q r₀ x M j iw n))
        (usedVals k Q r₀ x M j iw n)
    else usedVals k Q r₀ x M j iw n

omit hk hD hQ hlow hr₀ LH in
lemma usedVals_mono {a b : ℕ} (hab : a ≤ b) :
    usedVals k Q r₀ x M j iw a ⊆ usedVals k Q r₀ x M j iw b := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            exact subset_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact subset_rfl
    · refine (ih (by omega)).trans ?_
      simp only [usedVals]; split_ifs
      · exact subset_insert _ _
      · exact subset_rfl

omit hk hD hQ hlow hr₀ LH in
lemma card_usedVals_le (n : ℕ) : (usedVals k Q r₀ x M j iw n).card ≤ n := by
  induction n with
  | zero => simp [usedVals]
  | succ n ih =>
    simp only [usedVals]; split_ifs
    · exact (card_insert_le _ _).trans (by omega)
    · omega

omit hk hD hQ hlow hr₀ LH in
lemma sdiff_usedVals_nonempty {n : ℕ} (hn : n < k) :
    (range k \ usedVals k Q r₀ x M j iw n).Nonempty := by
  rw [← card_pos]
  have := le_card_sdiff (usedVals k Q r₀ x M j iw n) (range k)
  have := card_usedVals_le (k := k) (Q := Q) (r₀ := r₀) (x := x) (M := M) (j := j) (iw := iw) n
  rw [card_range] at *
  omega

/-- The sequence of changes: after `n` changes, `n` distinct low values are used, and each is
decided by the corresponding `j_b`. -/
lemma LastHyp.usedVals_spec
    (hiw : ∀ u < k, ∃ t₀ ≤ M, DecidesAt Q r₀ (iw u) t₀ u) :
    ∀ n ≤ k, usedVals k Q r₀ x M j iw n ⊆ range k ∧ (usedVals k Q r₀ x M j iw n).card = n ∧
      ∀ u ∈ usedVals k Q r₀ x M j iw n, ∃ b : Fin k, b.1 < n ∧
        u = dval k Q r₀ x M j iw b (range k \ usedVals k Q r₀ x M j iw b.1) := by
  classical
  intro n
  induction n with
  | zero => intro _; simp [usedVals]
  | succ n ih =>
    intro hn
    obtain ⟨hsub, hcard, hval⟩ := ih (by omega)
    have hnk : n < k := by omega
    set U := usedVals k Q r₀ x M j iw
    -- the run `s_n`
    set σ : Fin k → Finset ℕ := fun b => if b.1 < n then range k \ U b.1 else range k \ U n
    set W := range k \ U n
    have hW : W ⊆ range k := sdiff_subset
    have hWσ : ∀ b, W ⊆ σ b := by
      intro b; simp only [σ]; split_ifs with hb
      · exact sdiff_subset_sdiff subset_rfl (usedVals_mono hb.le)
      · exact subset_rfl
    have hσ : ∀ b, σ b ⊆ range k := by
      intro b; simp only [σ]; split_ifs <;> exact sdiff_subset
    set s := lastRun k r₀ x M j iw σ W
    have hs : Adm t D s := LastHyp.adm hr₀ _ _
    -- all low values are decided by correct processes in `s`
    have hall : ∀ u < k, ∃ i m, ¬ s.Faulty i ∧ DecidesAt Q s i m u := by
      intro u hu
      by_cases huU : u ∈ U n
      · obtain ⟨b, hb, rfl⟩ := hval u huU
        have hσb : σ b = range k \ U b.1 := by simp [σ, hb]
        obtain ⟨m', -, hd⟩ := LH.decides_dval hlow hr₀ hW hWσ hσ b
          (hσb ▸ sdiff_usedVals_nonempty b.2)
        rw [hσb] at hd
        exact ⟨j b, m', LastHyp.correct (Or.inl (Or.inr ⟨b, rfl⟩)), hd⟩
      · have huW : u ∈ W := mem_sdiff.2 ⟨mem_range.2 hu, huU⟩
        obtain ⟨t₀, ht₀, hd⟩ := hiw u hu
        have hcor : ¬ s.Faulty (iw u) := LastHyp.correct (Or.inr ⟨u, huW, rfl⟩)
        refine ⟨iw u, t₀, hcor, ?_⟩
        exact ((LH.sameView_le hW le_rfl (iw u)).decidesAt_iff Q ht₀
          ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hcor _, fun _ => hd.1⟩).1 hd
    -- `j_n` decides a new low value
    set b : Fin k := ⟨n, hnk⟩
    have hσb : σ b = range k \ U n := by simp [σ, b]
    obtain ⟨m', hm', hd⟩ := LH.decides_dval hlow hr₀ hW hWσ hσ b
      (hσb ▸ sdiff_usedVals_nonempty hnk)
    rw [hσb] at hd
    set d := dval k Q r₀ x M j iw b (range k \ U n)
    have hcor : ¬ s.Faulty (j b) := LastHyp.correct (Or.inl (Or.inr ⟨b, rfl⟩))
    have hdk : d < k := not_high_of_all_low hQ hs hall hcor hd
    have hdσ : d ∈ σ b := by
      rw [← LH.lows_j hW hWσ hσ b, mem_lows]
      exact ⟨vals_mono hm' (dec_mem_vals hk hD hQ hs hd), hdk⟩
    rw [hσb] at hdσ
    have hdU : d ∉ U n := (mem_sdiff.1 hdσ).2
    have hUs : U (n + 1) = insert d (U n) := by simp [U, usedVals, hnk, d, b]
    refine ⟨?_, ?_, ?_⟩
    · rw [hUs]; exact insert_subset (mem_range.2 hdk) hsub
    · rw [hUs, card_insert_of_notMem hdU, hcard]
    · intro u hu
      rw [hUs] at hu
      rcases mem_insert.1 hu with rfl | hu
      · exact ⟨b, Nat.lt_succ_self n, rfl⟩
      · obtain ⟨b', hb', h⟩ := hval u hu
        exact ⟨b', by omega, h⟩

/-- **The final step of Lemma 1**: in the setting of `LastHyp`, if each `iw u` decides `u` by time
`M` and `x` has seen the single low value `v` at `M + 1`, then `x` decides `v` at `M + 1`. -/
theorem step_final (hiw : ∀ u < k, ∃ t₀ ≤ M, DecidesAt Q r₀ (iw u) t₀ u) {v : ℕ}
    (hxv : lows k r₀ x (M + 1) = {v}) : DecidesAt Q r₀ x (M + 1) v := by
  classical
  set U := usedVals k Q r₀ x M j iw
  obtain ⟨hsub, hcard, hval⟩ := LH.usedVals_spec hk hD hQ hlow hr₀ hiw k le_rfl
  have hUk : U k = range k := eq_of_subset_of_card_le hsub (by rw [hcard, card_range])
  set σ : Fin k → Finset ℕ := fun b => range k \ U b.1
  have hσ : ∀ b, σ b ⊆ range k := fun _ => sdiff_subset
  set F := lastRun k r₀ x M j iw σ ∅
  have hF : Adm t D F := LastHyp.adm hr₀ _ _
  have hall : ∀ u < k, ∃ i m, ¬ F.Faulty i ∧ DecidesAt Q F i m u := by
    intro u hu
    obtain ⟨b, -, rfl⟩ := hval u (by rw [show usedVals k Q r₀ x M j iw k = range k from hUk]; exact mem_range.2 hu)
    obtain ⟨m', -, hd⟩ := LH.decides_dval hlow hr₀ (empty_subset _) (fun _ => empty_subset _) hσ
      b (sdiff_usedVals_nonempty b.2)
    exact ⟨j b, m', LastHyp.correct (Or.inl (Or.inr ⟨b, rfl⟩)), hd⟩
  have hsv : SameView r₀ F x (M + 1) := LH.sameView_x σ
  have hcor : ¬ F.Faulty x := LastHyp.correct (Or.inl (Or.inl rfl))
  have hlowF : Low k F x (M + 1) := by
    rw [← hsv.low_iff, low_iff_lows_nonempty, hxv]; exact singleton_nonempty v
  obtain ⟨m', hm', u, hd⟩ := hlow F hF x (M + 1) (SyncCrash.Run.alive_of_not_faulty hcor _) hlowF
  have huk : u < k := not_high_of_all_low hQ hF hall hcor hd
  have hu : u ∈ vals F x m' := dec_mem_vals hk hD hQ hF hd
  have hm'M : m' = M + 1 := by
    by_contra hne
    have hle : m' ≤ M := by omega
    have : u ∈ vals r₀ x M := by
      rw [(hsv.mono (Nat.le_succ M)).vals_eq]; exact vals_mono hle hu
    exact LH.high_x ⟨u, this, huk⟩
  subst hm'M
  have huv : u = v := by
    have : u ∈ lows k r₀ x (M + 1) := by rw [hsv.lows_eq]; exact mem_lows.2 ⟨hu, huk⟩
    rw [hxv] at this; exact mem_singleton.1 this
  subst huv
  exact (hsv.decidesAt_iff Q le_rfl ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hcor _,
    fun _ => LH.alive_x⟩).2 hd

end Final

/-! ### The induction -/

section Induction

variable (hk : 1 ≤ k) (hD : ∀ v ≤ k, v ∈ D) (hQ : SolvesSetConsensus k t D Q)
  (hlow : LowDecides k t D Q)
include hk hD hQ hlow

/-- **The induction step of Lemma 1** (time `M + 1`). -/
theorem lemma1_step {M : ℕ}
    (ih : ∀ m < M + 1, ∀ (r : Run P) x v, Adm t D r → Lemma1Hyp k r x m v → DecidesAt Q r x m v)
    {r : Run P} {x : P} {v : ℕ} (hr : Adm t D r) (h : Lemma1Hyp k r x (M + 1) v) :
    DecidesAt Q r x (M + 1) v := by
  classical
  have hxhigh : ¬ Low k r x M := h.first M rfl
  have hv : v ∈ lows k r x (M + 1) := h.lows_eq ▸ mem_singleton_self v
  have hvk : v < k := (mem_lows.1 hv).2
  obtain ⟨j, hjinj, hj⟩ := h.others
  -- the witnesses of `HC⟨x, M + 1⟩ ≥ k - 1`, indexed by the low values other than `v`
  set E := (range k).erase v
  have hcardE : Fintype.card E = k - 1 := by
    rw [Fintype.card_coe, card_erase_of_mem (mem_range.2 hvk), card_range]
  obtain ⟨w, hw⟩ := exists_witnesses (r := r) (i := x) (m := M + 1) (ι := E)
    (hcardE ▸ h.hc_ge)
  have H : ChainHyp r x (M + 1) M w :=
    ⟨Nat.le_succ M, fun ℓ hℓ => (hw ℓ (by omega)).1, fun ℓ hℓ => (hw ℓ (by omega)).2⟩
  -- the run `r'` of Lemma 2
  set r₀ := chainRun r x M w (fun b => b.1)
  have hsv : SameView r r₀ x (M + 1) := H.sameView
  have hr₀ : Adm t D r₀ :=
    H.adm hr (fun b => hD _ (mem_range.1 (mem_erase.1 b.2).2).le) (Nat.lt_succ_self M)
  have hxs : Seen r x M x (M + 1) := seen_self (Nat.le_succ M)
  have halive_x : r₀.Alive x (M + 1) := (H.alive_iff_of_seen hxs le_rfl).2 h.alive
  -- the process `i_v` from which `x` learned `v`
  obtain ⟨iv, hiv, hviv⟩ : ∃ q, comm r M q x ∧ v ∈ vals r q M := by
    rcases mem_vals_succ.1 (mem_lows.1 hv).1 with h' | h'
    · exact absurd ⟨v, h', hvk⟩ hxhigh
    · exact h'
  have hivs : Seen r iv M x (M + 1) := seen_of_comm hiv
  have halive_iv : r₀.Alive iv M := (H.alive_iff_of_seen hivs le_rfl).2 hiv.2.1
  have hviv₀ : v ∈ vals r₀ iv M := by rw [← (hsv.of_seen hivs).vals_eq]; exact hviv
  -- the processes `i_w`
  set iw : ℕ → P := fun u => if hu : u ∈ E then w M ⟨u, hu⟩ else iv
  have hiw_v : iw v = iv := by simp [iw, E]
  have hiw_E : ∀ u (hu : u ∈ E), iw u = w M ⟨u, hu⟩ := fun u hu => by simp [iw, hu]
  have hE : ∀ u < k, u ≠ v → u ∈ E := fun u hu huv => mem_erase.2 ⟨huv, mem_range.2 hu⟩
  have hlows_iw : ∀ u < k, lows k r₀ (iw u) M = {u} := by
    intro u hu
    by_cases huv : u = v
    · subst huv
      rw [hiw_v]
      refine Subset.antisymm ?_ (singleton_subset_iff.2 (mem_lows.2 ⟨hviv₀, hu⟩))
      rw [← (hsv.of_seen hivs).lows_eq, ← h.lows_eq]
      exact lows_subset_of_seen hivs
    · rw [hiw_E u (hE u hu huv)]
      refine Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2
        (mem_lows.2 ⟨H.mem_vals le_rfl _, hu⟩))
      obtain ⟨hy1, hy2⟩ := mem_lows.1 hy
      rcases mem_insert.1 (H.vals_subset le_rfl ⟨u, hE u hu huv⟩ hy1) with h' | h'
      · exact mem_singleton.2 h'
      · exact absurd ⟨y, h', hy2⟩ hxhigh
  have hhigh_j : ∀ b, ¬ Low k r₀ (j b) M := fun b => by
    rw [← (hsv.of_seen ((hj b).2.seen_pred le_rfl)).low_iff]; exact (hj b).1 M rfl
  have LH : LastHyp k r₀ x M j iw := by
    refine ⟨halive_x, ?_, fun b => hsv.seen ((hj b).2.seen_pred le_rfl), hhigh_j, hjinj,
      fun b => (hj b).2.ne le_rfl, fun u hu => ?_, hlows_iw, fun y hy hl => ?_⟩
    · rw [← (hsv.mono (Nat.le_succ M)).low_iff]; exact hxhigh
    · by_cases huv : u = v
      · rw [huv, hiw_v]; exact halive_iv
      · rw [hiw_E u (hE u hu huv)]; exact H.alive_w le_rfl _
    · by_cases hs : Seen r₀ y M x (M + 1)
      · have hs' : Seen r y M x (M + 1) := hsv.symm.seen hs
        rw [H.crash_of_seen hs' le_rfl]
        refine h.lowCrash M rfl y (hs'.alive h.alive) ?_
        rw [(hsv.of_seen hs').low_iff]; exact hl
      · by_contra hc
        have hyx : y ≠ x := by rintro rfl; exact hs (seen_self (Nat.le_succ M))
        exact hs (seen_of_deliv hyx (deliv_of_alive_of_ne hy hc x))
  -- the hidden capacity of the processes `i_w`
  have hhc_iw : ∀ u < k, k - 1 ≤ hc r₀ (iw u) M := by
    intro u hu
    rw [le_hc_iff]
    intro ℓ hℓ
    by_cases huv : u = v
    · subst huv
      rw [hiw_v, ← hcardE, ← card_univ, ← card_image_of_injective _ ((hw ℓ (by omega)).1)]
      refine card_le_card fun p hp => ?_
      obtain ⟨b, -, rfl⟩ := mem_image.1 hp
      refine mem_hiddenAt.2 (H.hidden_of_not_w le_rfl hℓ fun s hs he => ?_)
      exact H.not_w_of_seen (hivs.mono_left hs) hs b he.symm
    · have huE := hE u hu huv
      rw [hiw_E u huE]
      set bu : E := ⟨u, huE⟩
      obtain ⟨q, hq, hvq⟩ := exists_seen_of_mem_vals hviv₀ hℓ
      have hqx : Seen r q ℓ x (M + 1) := hsv.symm.seen (hq.trans (hsv.seen hivs))
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_gt_of_ne huv with h1 | h1 <;> omega
      have hqS : q ∉ (univ.erase bu).image (w ℓ) := by
        intro hqi
        obtain ⟨b, -, rfl⟩ := mem_image.1 hqi
        exact H.not_w_of_seen hqx hℓ b rfl
      have hcard : k - 1 ≤ (insert q ((univ.erase bu).image (w ℓ))).card := by
        rw [card_insert_of_notMem hqS, card_image_of_injective _ ((hw ℓ (by omega)).1),
          card_erase_of_mem (mem_univ _), card_univ, hcardE]
        omega
      refine hcard.trans (card_le_card fun p hp => ?_)
      rcases mem_insert.1 hp with rfl | hp
      · refine mem_hiddenAt.2 (hidden_of_alive (hq.alive halive_iv) fun hs => huv ?_)
        have : v ∈ lows k r₀ (w M bu) M :=
          mem_lows.2 ⟨vals_subset_of_seen hs hvq, hvk⟩
        rw [← hiw_E u huE, hlows_iw u hu] at this
        exact (mem_singleton.1 this).symm
      · obtain ⟨b, hb, rfl⟩ := mem_image.1 hp
        exact mem_hiddenAt.2 (H.hidden_col le_rfl hℓ (Ne.symm (ne_of_mem_erase hb)))
  -- the induction hypothesis: each `i_w` decides `w` by time `M`
  have hiw : ∀ u < k, ∃ t₀ ≤ M, DecidesAt Q r₀ (iw u) t₀ u := by
    intro u hu
    have hlM : Low k r₀ (iw u) M := LH.low_iw hu
    have hex : ∃ s, Low k r₀ (iw u) s := ⟨M, hlM⟩
    set t₀ := Nat.find hex
    have ht₀ : t₀ ≤ M := Nat.find_min' hex hlM
    have hlt₀ : Low k r₀ (iw u) t₀ := Nat.find_spec hex
    have hyp : Lemma1Hyp k r₀ (iw u) t₀ u := by
      refine ⟨⟨(LH.alive_iw u hu).mono ht₀, fun M' hM' hl => Nat.find_min hex (by omega) hl,
        ?_, (hhc_iw u hu).trans (hc_mono ht₀), ⟨j, hjinj, fun b => ⟨fun M' _ hl =>
          hhigh_j b (hl.mono (by omega)), hidden_now_of_alive ((LH.alive_j b).mono ht₀) ?_⟩⟩⟩,
        fun M' hM' y hy hl => ?_⟩
      · have hsub : lows k r₀ (iw u) t₀ ⊆ {u} := hlows_iw u hu ▸ lows_mono ht₀
        exact (Nonempty.subset_singleton_iff (low_iff_lows_nonempty.1 hlt₀)).1 hsub
      · intro he; exact hhigh_j b (he ▸ hlM)
      · rw [hM']
        refine crash_eq_of_low_of_high (z := x) (fun hlx => LH.high_x (hlx.mono ?_)) hy hl
        omega
    exact ⟨t₀, ht₀, ih t₀ (by omega) r₀ (iw u) u hr₀ hyp⟩
  -- the changes, and the conclusion in `r'`, transferred to `r`
  have hd := step_final hk hD hQ hlow hr₀ LH hiw (v := v) (by rw [← hsv.lows_eq]; exact h.lows_eq)
  exact (hsv.decidesAt_iff Q le_rfl ⟨fun _ => halive_x, fun _ => h.alive⟩).2 hd

/-- **Lemma 1** (corrected: with the additional hypothesis 5, `Lemma1Hyp.lowCrash`). Let `Q` solve
nonuniform `k`-set consensus and let every low process decide by the time it is low. If the
hypotheses hold at `⟨x, m⟩`, then `x` decides its unique low value `v` at time `m`. -/
theorem lemma1 : ∀ m (r : Run P) (x : P) (v : ℕ), Adm t D r → Lemma1Hyp k r x m v →
    DecidesAt Q r x m v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro r x v hr h
    cases m with
    | zero =>
      have hv : v ∈ lows k r x 0 := h.lows_eq ▸ mem_singleton_self v
      obtain ⟨hv1, hvk⟩ := mem_lows.1 hv
      rw [vals_zero, mem_singleton] at hv1
      obtain ⟨m', hm', u, hd⟩ := hlow r hr x 0 h.alive ⟨v, by rw [vals_zero, hv1]; simp, hvk⟩
      obtain rfl : m' = 0 := by omega
      have hu := dec_mem_vals hk hD hQ hr hd
      rw [vals_zero, mem_singleton, ← hv1] at hu
      exact hu ▸ hd
    | succ M => exact lemma1_step hk hD hQ hlow ih hr h

end Induction

end Podc.UnbeatableSetConsensus
