import Papers.PODC2016.UnbeatableSetConsensus.Optmin
import Papers.PODC2016.UnbeatableSetConsensus.Runs

/-!
# The uniform protocol `u-Pmin[k]` (§5, Theorem 3)

**Definition 3.** Let `i` know of `d` failures at time `m` (the processes `p` such that `⟨p, m⟩` is
guaranteed crashed at `⟨i, m⟩`). `i` *knows that `v` will persist* at time `m` if `m > 0` and `i`
has seen `v` by time `m - 1`, or `⟨i, m⟩` sees at least `t - d` distinct nodes `⟨j, m - 1⟩` that
have seen `v` (`KnowsPersist`).

**Protocol `u-Pmin[k]`** (for an undecided process `i` at time `m`):

  if (`i` is low or `HC⟨i, m⟩ < k`) and `i` knows that `Min⟨i, m⟩` will persist
                                                          then decide(`Min⟨i, m⟩`)
  elseif `m > 0` and (`⟨i, m - 1⟩` was low or `HC⟨i, m - 1⟩ < k`)   then decide(`Min⟨i, m - 1⟩`)
  elseif `m = ⌊t/k⌋ + 1`                                  then decide(`Min⟨i, m⟩`)

**Theorem 3.** `u-Pmin[k]` solves *uniform* `k`-set consensus, and every process decides by time
`min(⌊t/k⌋ + 1, ⌊f/k⌋ + 2)` (`theorem3`). The key fact about persistence (`persist`): if `j`,
alive at `m`, knows that `w` (seen by `j` at `m`) will persist, then every process alive at `m + 1`
has seen `w` by then.
-/

namespace Podc.UnbeatableSetConsensus

open Cslib Finset

variable {P : Type*} [Fintype P] {k t : ℕ} {D : Set ℕ}

/-- The number of failures `i` knows of at time `m`. -/
noncomputable def known (r : Run P) (i : P) (m : ℕ) : ℕ := by
  classical exact (univ.filter fun p => GuarCrashed r i m p m).card

/-- The number of nodes `⟨j, m - 1⟩` seen by `⟨i, m⟩` that have seen `v` (`0` for `m = 0`). -/
noncomputable def carriers (r : Run P) (i : P) (m v : ℕ) : ℕ := by
  classical exact
    (univ.filter fun p => 0 < m ∧ Seen r p (m - 1) i m ∧ v ∈ vals r p (m - 1)).card

/-- **Definition 3**: `i` knows at time `m` that `v` will persist. -/
def KnowsPersist (t : ℕ) (r : Run P) (i : P) (m v : ℕ) : Prop :=
  (0 < m ∧ v ∈ vals r i (m - 1)) ∨ t - known r i m ≤ carriers r i m v

omit [Fintype P] in
lemma SameView.guarCrashed_iff {r r' : Run P} {i j : P} {m ℓ : ℕ} (h : SameView r r' i m) :
    GuarCrashed r i m j ℓ ↔ GuarCrashed r' i m j ℓ :=
  ⟨h.guarCrashed, h.symm.guarCrashed⟩

lemma SameView.knowsPersist_iff {r r' : Run P} {i : P} {m v : ℕ} (h : SameView r r' i m) :
    KnowsPersist t r i m v ↔ KnowsPersist t r' i m v := by
  classical
  have hk : known r i m = known r' i m := by
    unfold known; congr 1; ext p; simp [h.guarCrashed_iff]
  have hc : carriers r i m v = carriers r' i m v := by
    unfold carriers; congr 1; ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h0, hs, hv⟩; exact ⟨h0, h.seen hs, (h.of_seen hs).vals_eq ▸ hv⟩
    · rintro ⟨h0, hs, hv⟩
      exact ⟨h0, h.symm.seen hs, (h.symm.of_seen hs).vals_eq ▸ hv⟩
  unfold KnowsPersist
  rw [hk, hc, (h.mono (Nat.sub_le m 1)).vals_eq]

open Classical in
/-- **Protocol `u-Pmin[k]`** (§5). -/
noncomputable def uPmin (k t : ℕ) : Protocol P where
  dec r i m :=
    if (Low k r i m ∨ hc r i m < k) ∧ KnowsPersist t r i m (minVal r i m) then some (minVal r i m)
    else if 0 < m ∧ (Low k r i (m - 1) ∨ hc r i (m - 1) < k) then some (minVal r i (m - 1))
    else if m = t / k + 1 then some (minVal r i m) else none
  dec_congr r r' i m h := by
    have h1 := h.mono (Nat.sub_le m 1)
    simp only [h.low_iff, h.hc_eq, h.minVal_eq, h.knowsPersist_iff, h1.low_iff, h1.hc_eq,
      h1.minVal_eq]

/-- **Uniform `k`-set consensus**: Decision and Validity as before; Uniform `k`-Agreement: at most
`k` values are decided (by correct or faulty processes). -/
structure SolvesUniformSetConsensus (k t : ℕ) (D : Set ℕ) (Q : Protocol P) : Prop where
  decision : ∀ r, Adm t D r → ∀ i, ¬ r.Faulty i → ∃ m v, DecidesAt Q r i m v
  validity : ∀ r, Adm t D r → ∀ i m v, DecidesAt Q r i m v → ∃ j, r.input j = v
  agreement : ∀ r, Adm t D r → {v | ∃ i m, DecidesAt Q r i m v}.encard ≤ k

variable {r : Run P} {i j : P} {m v w : ℕ}

/-! ### Decision times -/

lemma uPmin_dec_ne_none_T : (uPmin k t).dec r i (t / k + 1) ≠ none := by
  simp only [uPmin]; split_ifs <;> simp_all

/-- Every process alive at `⌊t/k⌋ + 1` has decided by then. -/
lemma uPmin_decidesBy_T (ha : r.Alive i (t / k + 1)) : DecidesBy (uPmin k t) r i (t / k + 1) :=
  decidesBy_of_dec ha uPmin_dec_ne_none_T

/-- Every process alive at `⌊f/k⌋ + 2` has decided by then. -/
lemma uPmin_decidesBy_f (hk : 0 < k) (ha : r.Alive i (r.faulty.card / k + 2)) :
    DecidesBy (uPmin k t) r i (r.faulty.card / k + 2) := by
  refine decidesBy_of_dec ha ?_
  have h2 : Low k r i (r.faulty.card / k + 1) ∨ hc r i (r.faulty.card / k + 1) < k := by
    by_contra hn
    push Not at hn
    have := mul_le_card_faulty hn.2
    have := Nat.lt_mul_div_succ r.faulty.card hk
    omega
  simp only [uPmin]
  split_ifs <;> simp_all

lemma DecidesAt.le_T (h : DecidesAt (uPmin k t) r i m v) : m ≤ t / k + 1 := by
  by_contra hlt
  exact uPmin_dec_ne_none_T (h.2.2 _ (by omega))

/-- What a decision of `u-Pmin[k]` looks like: `v = Min⟨i, m'⟩` for `m' ∈ {m - 1, m}` with
`⟨i, m'⟩` low or of hidden capacity `< k`, and if `m' = m` then `i` knows that `v` persists or
`m = ⌊t/k⌋ + 1`. -/
lemma DecidesAt.uPmin_cases (hr : Adm t D r) (hk : 0 < k) (h : DecidesAt (uPmin k t) r i m v) :
    ∃ m', m' ≤ m ∧ v = minVal r i m' ∧ (Low k r i m' ∨ hc r i m' < k) ∧
      ((m' = m ∧ (KnowsPersist t r i m v ∨ m = t / k + 1)) ∨ m = m' + 1) := by
  have h2 := h.2.1
  simp only [uPmin] at h2
  split_ifs at h2 with h3 h4 h5
  · cases h2; exact ⟨m, le_rfl, rfl, h3.1, Or.inl ⟨rfl, Or.inl h3.2⟩⟩
  · cases h2; exact ⟨m - 1, Nat.sub_le m 1, rfl, h4.2, Or.inr (by omega)⟩
  · cases h2
    refine ⟨m, le_rfl, rfl, ?_, Or.inl ⟨rfl, Or.inr h5⟩⟩
    by_contra hn
    push Not at hn
    have h6 := mul_le_card_faulty hn.2
    have h7 := Nat.lt_mul_div_succ t hk
    have h8 := hr.1.1
    rw [h5] at h6
    omega

/-! ### Persistence -/

omit [Fintype P] in
lemma not_guarCrashed_of_seen_pred {p : P} {M : ℕ} (ha : r.Alive p M)
    (hs : Seen r p M i (M + 1)) : ¬ GuarCrashed r i (M + 1) p (M + 1) := by
  rintro ⟨h, s, hs', hseen, hne, hd⟩
  rcases Nat.lt_or_ge s M with hlt | hge
  · exact hd (deliv_of_alive_succ (ha.mono hlt) h)
  · obtain rfl : s = M := by omega
    obtain rfl := seen_same_time hseen
    exact hd (Seen.deliv_of_succ hs (Ne.symm hne))

omit [Fintype P] in
lemma faulty_of_not_deliv' {q p : P} {s : ℕ} (h : ¬ r.Deliv q p s) : r.Faulty q := by
  intro hc; exact h (deliv_of_crash_none (by simpa [SyncCrash.Run.Faulty] using hc) p s)

/-- **Persistence** (§5, after Definition 3): if `j` is alive at `m`, has seen `w`, and knows that
`w` will persist, then every process alive at `m + 1` has seen `w` by then. -/
theorem persist (hr : Adm t D r) (hj : r.Alive j m) (hw : w ∈ vals r j m)
    (hkp : KnowsPersist t r j m w) (i : P) : w ∈ vals r i (m + 1) := by
  classical
  by_contra hwi
  have hij : i ≠ j := by rintro rfl; exact hwi (vals_mono (Nat.le_succ m) hw)
  have hdj : ¬ r.Deliv j i m := fun hd => hwi (vals_subset_succ_of_comm ⟨hij.symm, hd⟩ hw)
  rcases hkp with ⟨hm, hw'⟩ | hcount
  · -- `j` sent `w` to everybody in round `m`
    obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
    have hd := deliv_of_alive_succ hj i
    exact hwi (vals_mono (Nat.le_succ _) (vals_subset_succ_of_comm ⟨hij.symm, hd⟩ hw'))
  · -- otherwise more than `t` processes crash
    set Dset := univ.filter fun p => GuarCrashed r j m p m
    set J := univ.filter fun p => 0 < m ∧ Seen r p (m - 1) j m ∧ w ∈ vals r p (m - 1)
    have hJ : ∀ p ∈ J, r.Faulty p ∧ p ≠ j ∧ p ∉ Dset := by
      intro p hp
      obtain ⟨hm, hs, hwp⟩ := by simpa [J] using hp
      obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hs hwp
      have hpi : p ≠ i := by rintro rfl; exact hwi (vals_mono (by omega) hwp)
      have hdp : ¬ r.Deliv p i M := fun hd =>
        hwi (vals_mono (Nat.le_succ _) (vals_subset_succ_of_comm ⟨hpi, hd⟩ hwp))
      refine ⟨faulty_of_not_deliv' hdp, fun hpj => hdp (hpj ▸ deliv_of_alive_succ hj i), ?_⟩
      simp only [Dset, mem_filter, mem_univ, true_and]
      exact not_guarCrashed_of_seen_pred (hs.alive hj) hs
    have hD : ∀ p ∈ Dset, r.Faulty p := by
      intro p hp
      have hg : GuarCrashed r j m p m := by simpa [Dset] using hp
      by_contra hpf
      exact not_guarCrashed_of_alive (SyncCrash.Run.alive_of_not_faulty hpf m) hg
    have hjD : j ∉ Dset := by
      simp only [Dset, mem_filter, mem_univ, true_and]; exact not_guarCrashed_of_alive hj
    have hsub : insert j (Dset ∪ J) ⊆ r.faulty := by
      intro p hp
      rw [SyncCrash.Run.mem_faulty]
      rcases mem_insert.1 hp with rfl | hp
      · exact faulty_of_not_deliv' hdj
      · rcases mem_union.1 hp with hp | hp
        · exact hD p hp
        · exact (hJ p hp).1
    have hdisj : Disjoint Dset J := by
      rw [disjoint_left]; intro p hpD hpJ; exact (hJ p hpJ).2.2 hpD
    have hjJ : j ∉ J := fun h => (hJ j h).2.1 rfl
    have hcard := (card_le_card hsub).trans hr.1.1
    rw [card_insert_of_notMem (by simp [hjD, hjJ]), card_union_of_disjoint hdisj] at hcard
    have hDt : Dset.card ≤ t :=
      (card_le_card fun p hp => SyncCrash.Run.mem_faulty.2 (hD p hp)).trans hr.1.1
    have hkn : known r j m = Dset.card := by unfold known; convert rfl
    have : t - known r j m ≤ J.card := hcount
    omega

/-! ### Theorem 3 -/

/-- If `w < v` are decided by `j` and `i`, with `v = Min⟨i, m'_i⟩`, then `m'_i ≤ m'_j`. -/
lemma le_of_decides (hr : Adm t D r) {mi mj mi' mj' : ℕ}
    (hi : DecidesAt (uPmin k t) r i mi v) (hj : DecidesAt (uPmin k t) r j mj w) (hwv : w < v)
    (hvi : v = minVal r i mi') (hmi : mi' ≤ mi) (hwj : w = minVal r j mj')
    (hcase : (mj' = mj ∧ (KnowsPersist t r j mj w ∨ mj = t / k + 1)) ∨ mj = mj' + 1) :
    mi' ≤ mj' := by
  by_contra hlt
  push Not at hlt
  have hne : i ≠ j := by rintro rfl; have := (hi.unique hj).2; omega
  -- `i` has seen `w` by time `mj' + 1 ≤ mi'`
  have hseen : w ∈ vals r i (mj' + 1) := by
    rcases hcase with ⟨hEq, hkp | hT⟩ | hEq
    · subst hEq
      exact persist hr hj.1 (hwj ▸ minVal_mem r j mj') hkp i
    · have := hi.le_T; omega
    · subst hEq
      exact vals_subset_succ_of_comm ⟨hne.symm, deliv_of_alive_succ hj.1 i⟩
        (hwj ▸ minVal_mem r j mj')
  have := minVal_le (vals_mono hlt hseen)
  omega

/-- **Theorem 3, Uniform `k`-Agreement.** -/
theorem uPmin_agreement (hr : Adm t D r) (hk : 0 < k) :
    {v | ∃ i m, DecidesAt (uPmin k t) r i m v}.encard ≤ k := by
  classical
  set A := {v | ∃ i m, DecidesAt (uPmin k t) r i m v} with hA
  have hAfin : A ⊆ ↑(univ.image r.input) := by
    rintro _ ⟨i, m, hv⟩
    obtain ⟨m', -, rfl, -⟩ := hv.uPmin_cases hr hk
    obtain ⟨j, -, hj⟩ := mem_vals.1 (minVal_mem r i m')
    simp [← hj]
  set A' := (univ.image r.input).filter (· ∈ A)
  have hAA' : A = ↑A' := by
    ext v; simp only [A', coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨hAfin h, h⟩, fun h => h.2⟩
  rcases A'.eq_empty_or_nonempty with he | hne
  · rw [hAA', he]; simp
  set v := A'.max' hne
  have hvA : v ∈ A := (mem_filter.1 (A'.max'_mem hne)).2
  obtain ⟨i, mi, hv⟩ := hvA
  obtain ⟨mi', hmi, hvm, hcase, -⟩ := hv.uPmin_cases hr hk
  obtain ⟨F, hF, hFsub⟩ : ∃ F : Finset ℕ, F.card + 1 ≤ k ∧ ∀ w ∈ A, w < v → w ∈ F := by
    rcases hcase with hlow | hhc
    · refine ⟨range v, ?_, fun w _ hw => mem_range.2 hw⟩
      rw [card_range, hvm]; have := low_iff_minVal.1 hlow; omega
    · obtain ⟨ℓ, hℓ, hcard⟩ := hc_lt_iff.1 hhc
      refine ⟨(hiddenAt r i mi' ℓ).image (fun h => minVal r h ℓ),
        (card_image_le.trans_lt hcard), ?_⟩
      rintro w ⟨j, mj, hw⟩ hwv
      obtain ⟨mj', hmj, hwm, -, hjcase⟩ := hw.uPmin_cases hr hk
      have hle := le_of_decides hr hv hw hwv hvm hmi hwm hjcase
      have hnot : w ∉ vals r i mi' := fun h' => absurd (minVal_le h') (by omega)
      obtain ⟨q, hq, hwq⟩ := exists_seen_of_mem_vals (hwm ▸ minVal_mem r j mj') (hℓ.trans hle)
      refine mem_image.2 ⟨q, mem_hiddenAt.2 ⟨fun hs => hnot (vals_subset_of_seen hs hwq),
        not_guarCrashed_of_alive (hq.alive (hw.1.mono hmj))⟩, ?_⟩
      exact le_antisymm (minVal_le hwq) (hwm ▸ minVal_le_of_seen hq)
  have hsub : A ⊆ ↑(insert v F) := by
    intro w hw
    have hwv : w ≤ v := A'.le_max' w (by rw [hAA'] at hw; exact hw)
    rcases Nat.lt_or_eq_of_le hwv with hlt | rfl
    · exact mem_insert_of_mem (hFsub w hw hlt)
    · exact mem_insert_self _ _
  calc A.encard ≤ (↑(insert v F) : Set ℕ).encard := Set.encard_le_encard hsub
    _ = ((insert v F).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ k := by exact_mod_cast (card_insert_le v F).trans hF

/-- **Theorem 3.** `u-Pmin[k]` solves uniform `k`-set consensus, and every process alive at time
`min(⌊t/k⌋ + 1, ⌊f/k⌋ + 2)` has decided by then (`f` = number of crashes). -/
theorem theorem3 (hk : 0 < k) :
    SolvesUniformSetConsensus k t D (uPmin k t : Protocol P) ∧
      ∀ r : Run P, Adm t D r → ∀ i, r.Alive i (min (t / k + 1) (r.faulty.card / k + 2)) →
        DecidesBy (uPmin k t) r i (min (t / k + 1) (r.faulty.card / k + 2)) := by
  refine ⟨⟨fun r _ i hi => ?_, fun r hr i m v hv => ?_, fun r hr => uPmin_agreement hr hk⟩,
    fun r _ i ha => ?_⟩
  · obtain ⟨m, -, v, hv⟩ := uPmin_decidesBy_T (k := k) (t := t)
      (SyncCrash.Run.alive_of_not_faulty hi (t / k + 1))
    exact ⟨m, v, hv⟩
  · obtain ⟨m', -, rfl, -⟩ := hv.uPmin_cases hr hk
    obtain ⟨j, -, hj⟩ := mem_vals.1 (minVal_mem r i m')
    exact ⟨j, hj⟩
  · rcases min_choice (t / k + 1) (r.faulty.card / k + 2) with h | h <;> rw [h] at ha ⊢
    · exact uPmin_decidesBy_T ha
    · exact uPmin_decidesBy_f hk ha

end Podc.UnbeatableSetConsensus
