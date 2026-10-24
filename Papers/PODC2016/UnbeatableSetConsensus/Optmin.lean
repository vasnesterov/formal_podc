import Papers.PODC2016.UnbeatableSetConsensus.Views

/-!
# The protocol `Optmin[k]` and its correctness (Proposition 1)

`Optmin[k]` (§4.1), for an undecided process `i` at time `m`:

  if `i` is low or `HC⟨i, m⟩ < k` then `decide(Min⟨i, m⟩)`.

**Proposition 1.** `Optmin[k]` solves nonuniform `k`-set consensus, and every process decides by
time `⌊f/k⌋ + 1`, where `f` is the number of crashes of the run (`optmin_solves`,
`optmin_decidesBy`). The bound comes from the fact that the witnesses of a hidden capacity `≥ k`
at the times `ℓ < m` are `k · m` distinct faulty processes (`mul_le_card_faulty`).
-/

namespace Podc.UnbeatableSetConsensus

open Cslib Finset

variable {P : Type*} [Fintype P] {k t : ℕ} {D : Set ℕ}

/-- **Protocol `Optmin[k]`** (§4.1). -/
noncomputable def optmin (k : ℕ) : Protocol P where
  dec r i m := if minVal r i m < k ∨ hc r i m < k then some (minVal r i m) else none
  dec_congr r r' i m h := by simp only [h.minVal_eq, h.hc_eq]

variable {r : Run P} {i : P} {m v : ℕ}

lemma optmin_dec_eq_none : (optmin k).dec r i m = none ↔ k ≤ minVal r i m ∧ k ≤ hc r i m := by
  simp only [optmin, ite_eq_right_iff, reduceCtorEq, imp_false, not_or, not_lt]

lemma DecidesAt.optmin (h : DecidesAt (optmin k) r i m v) :
    v = minVal r i m ∧ (minVal r i m < k ∨ hc r i m < k) := by
  have h2 := h.2.1
  simp only [UnbeatableSetConsensus.optmin] at h2
  split_ifs at h2 with hc
  · exact ⟨(Option.some_injective _ h2).symm, hc⟩

/-- A live low process has decided in `Optmin[k]`. -/
lemma optmin_decidesBy_of_low (ha : r.Alive i m) (hl : Low k r i m) :
    DecidesBy (optmin k) r i m := by
  refine decidesBy_of_dec ha ?_
  rw [Ne, optmin_dec_eq_none, not_and_or]
  exact Or.inl (not_le.2 (low_iff_minVal.1 hl))

/-- The witnesses of a hidden capacity `≥ c` at the times `ℓ < m` are `c · m` distinct faulty
processes. -/
lemma mul_le_card_faulty {c : ℕ} (h : c ≤ hc r i m) : c * m ≤ r.faulty.card := by
  classical
  have hdisj : (↑(range m) : Set ℕ).PairwiseDisjoint (fun ℓ => hiddenAt r i m ℓ) := by
    intro ℓ hℓ ℓ' hℓ' hne
    rw [Function.onFun, disjoint_left]
    intro j hj hj'
    rw [mem_hiddenAt] at hj hj'
    simp only [coe_range, Set.mem_Iio] at hℓ hℓ'
    exact hne (hj.time_eq hj' hℓ.le hℓ'.le)
  have hsub : (range m).biUnion (fun ℓ => hiddenAt r i m ℓ) ⊆ r.faulty := by
    intro j hj
    simp only [mem_biUnion, mem_range] at hj
    obtain ⟨ℓ, hℓ, hj⟩ := hj
    exact SyncCrash.Run.mem_faulty.2 ((mem_hiddenAt.1 hj).faulty hℓ)
  calc c * m = ∑ _ℓ ∈ range m, c := by simp [mul_comm]
    _ ≤ ∑ ℓ ∈ range m, (hiddenAt r i m ℓ).card :=
        sum_le_sum fun ℓ hℓ => le_hc_iff.1 h ℓ (by simp at hℓ; omega)
    _ = ((range m).biUnion (fun ℓ => hiddenAt r i m ℓ)).card := (card_biUnion hdisj).symm
    _ ≤ r.faulty.card := card_le_card hsub

/-- **Proposition 1, decision time.** Every process that is alive at time `⌊f/k⌋ + 1` has decided
in `Optmin[k]` by then (`f` = number of crashes in the run). -/
theorem optmin_decidesBy (hk : 0 < k) (r : Run P) (i : P)
    (ha : r.Alive i (r.faulty.card / k + 1)) :
    DecidesBy (optmin k) r i (r.faulty.card / k + 1) := by
  refine decidesBy_of_dec ha fun hn => ?_
  have h := mul_le_card_faulty (optmin_dec_eq_none.1 hn).2
  have := Nat.lt_mul_div_succ r.faulty.card hk
  omega

/-- The key step of `k`-Agreement: if correct `i` decides `v` at `m`, correct `j` decides `w < v`
at `m'`, and `ℓ ≤ m`, then `w = Min⟨h, ℓ⟩` for a node `⟨h, ℓ⟩` hidden from `⟨i, m⟩`. -/
lemma exists_hidden_of_lt {j : P} {m' w ℓ : ℕ} (hi : ¬ r.Faulty i) (hj : ¬ r.Faulty j)
    (hv : DecidesAt (optmin k) r i m v) (hw : DecidesAt (optmin k) r j m' w) (hwv : w < v)
    (hℓ : ℓ ≤ m) : ∃ h, Hidden r i m h ℓ ∧ minVal r h ℓ = w := by
  obtain ⟨rfl, -⟩ := hv.optmin
  obtain ⟨rfl, -⟩ := hw.optmin
  have hnot : minVal r j m' ∉ vals r i m := fun hm => absurd (minVal_le hm) (not_le.2 hwv)
  have hmm : m ≤ m' := by
    by_contra hlt
    push Not at hlt
    apply hnot
    refine vals_subset_of_seen ?_ (minVal_mem r j m')
    by_cases hji : j = i
    · subst hji; exact seen_self hlt.le
    · exact (seen_of_deliv hji (SyncCrash.Run.deliv_of_not_faulty hj i m')).mono_right hlt
  obtain ⟨q, hq, hwq⟩ := exists_seen_of_mem_vals (minVal_mem r j m') (hℓ.trans hmm)
  refine ⟨q, ⟨fun hs => hnot (vals_subset_of_seen hs hwq), ?_⟩, ?_⟩
  · exact not_guarCrashed_of_alive (hq.alive (SyncCrash.Run.alive_of_not_faulty hj m'))
  · exact le_antisymm (minVal_le hwq) (minVal_le_of_seen hq)

/-- **Proposition 1, `k`-Agreement.** -/
theorem optmin_agreement (r : Run P) :
    {v | ∃ i m, ¬ r.Faulty i ∧ DecidesAt (optmin k) r i m v}.encard ≤ k := by
  classical
  set A := {v | ∃ i m, ¬ r.Faulty i ∧ DecidesAt (optmin k) r i m v} with hA
  have hAfin : A ⊆ ↑(univ.image r.input) := by
    rintro _ ⟨i, m, -, hv⟩
    obtain ⟨rfl, -⟩ := hv.optmin
    obtain ⟨j, -, hj⟩ := mem_vals.1 (minVal_mem r i m)
    simp [← hj]
  set A' := (univ.image r.input).filter (· ∈ A)
  have hAA' : A = ↑A' := by
    ext v; simp only [A', coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨hAfin h, h⟩, fun h => h.2⟩
  rcases A'.eq_empty_or_nonempty with he | hne
  · rw [hAA', he]; simp
  set v := A'.max' hne
  have hvA : v ∈ A := (mem_filter.1 (A'.max'_mem hne)).2
  obtain ⟨i, m, hi, hv⟩ := hvA
  obtain ⟨hvm, hcase⟩ := hv.optmin
  -- a finset of size `≤ k - 1` containing the decided values below `v`
  obtain ⟨F, hF, hFsub⟩ : ∃ F : Finset ℕ, F.card + 1 ≤ k ∧ ∀ w ∈ A, w < v → w ∈ F := by
    rcases hcase with hlow | hhc
    · refine ⟨range v, by rw [card_range, hvm]; omega, fun w _ hw => mem_range.2 hw⟩
    · obtain ⟨ℓ, hℓ, hcard⟩ := hc_lt_iff.1 hhc
      refine ⟨(hiddenAt r i m ℓ).image (fun h => minVal r h ℓ),
        (card_image_le.trans_lt hcard), ?_⟩
      rintro w ⟨j, m', hj, hw⟩ hwv
      obtain ⟨h, hh, rfl⟩ := exists_hidden_of_lt hi hj hv hw hwv hℓ
      exact mem_image.2 ⟨h, mem_hiddenAt.2 hh, rfl⟩
  have hsub : A ⊆ ↑(insert v F) := by
    intro w hw
    have hwv : w ≤ v := A'.le_max' w (by rw [hAA'] at hw; exact hw)
    rcases Nat.lt_or_eq_of_le hwv with hlt | rfl
    · exact mem_insert_of_mem (hFsub w hw hlt)
    · exact mem_insert_self _ _
  calc A.encard ≤ (↑(insert v F) : Set ℕ).encard := Set.encard_le_encard hsub
    _ = ((insert v F).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ k := by
        have := card_insert_le v F
        exact_mod_cast this.trans hF

/-- **Proposition 1.** `Optmin[k]` solves nonuniform `k`-set consensus (for every `t` and every
set of inputs `D`). -/
theorem optmin_solves (hk : 0 < k) : SolvesSetConsensus k t D (optmin k : Protocol P) where
  decision r _ i hi := by
    obtain ⟨m', -, v, hv⟩ :=
      optmin_decidesBy hk r i (SyncCrash.Run.alive_of_not_faulty hi _)
    exact ⟨m', v, hv⟩
  validity r _ i m v hv := by
    obtain ⟨rfl, -⟩ := hv.optmin
    obtain ⟨j, -, hj⟩ := mem_vals.1 (minVal_mem r i m)
    exact ⟨j, hj⟩
  agreement r _ := optmin_agreement r

end Podc.UnbeatableSetConsensus
