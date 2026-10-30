import Papers.PODC2013.ParetoOptimalConsensus.UniformDefs

/-!
# The protocols `U-P0` and `U-Opt0`; Theorem 8 and Lemma 18 (§5, Appendix C)

**Protocol `U-P0`** (for an undecided process `i` at time `m`):
  if `K_i ∃correct(0)` then decide(0) elseif `m = t + 1` then decide(1).

**Protocol `U-Opt0`**:
  if `K_i ∃correct(0)` then decide(0)
  elseif no hidden path w.r.t. `⟨i, m⟩` exists and `¬K_i ∃0` then decide(1).

* **Theorem 8** (`theorem8`): `U-Opt0` solves uniform consensus (`t < n`); every process alive at
  `f + 1` has decided by then if `f ≥ t - 1`, and every process alive at `f + 2` has decided by
  then in any case.
* **Lemma 18** (`lemma18`): `U-Opt0 ⪰ U-P0`.
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

open Classical in
/-- **Protocol `U-P0`.** -/
noncomputable def uP0 (t : ℕ) : Protocol P where
  dec r i m := if KCorrect t r i m 0 then some 0 else if m = t + 1 then some 1 else none
  dec_congr r r' i m h := by simp only [kCorrect_iff_of_sameView h]

open Classical in
/-- **Protocol `U-Opt0`.** -/
noncomputable def uOpt0 (t : ℕ) : Protocol P where
  dec r i m := if KCorrect t r i m 0 then some 0
    else if ¬ HiddenPath r i m ∧ 0 ∉ vals r i m then some 1 else none
  dec_congr r r' i m h := by
    simp only [kCorrect_iff_of_sameView h, hiddenPath_iff_of_sameView h, h.vals_eq]

section Basic

variable {r : Run P} {i : P} {m v : ℕ}

lemma uOpt0_dec_eq_none : (uOpt0 t).dec r i m = none ↔
    ¬ KCorrect t r i m 0 ∧ (HiddenPath r i m ∨ 0 ∈ vals r i m) := by
  unfold uOpt0; simp only
  split_ifs with h1 h2 <;> simp_all [or_iff_not_imp_left]

lemma decidesAt_uOpt0 (h : DecidesAt (uOpt0 t) r i m v) :
    (KCorrect t r i m 0 ∧ v = 0) ∨
      (¬ KCorrect t r i m 0 ∧ ¬ HiddenPath r i m ∧ 0 ∉ vals r i m ∧ v = 1) := by
  have h2 := h.2.1
  unfold UnbeatableSetConsensus.Protocol.dec uOpt0 at h2
  simp only at h2
  split_ifs at h2 with h3 h4 <;> cases h2
  · exact Or.inl ⟨h3, rfl⟩
  · exact Or.inr ⟨h3, h4.1, h4.2, rfl⟩

lemma uP0_dec_eq_none : (uP0 t).dec r i m = none ↔ ¬ KCorrect t r i m 0 ∧ m ≠ t + 1 := by
  unfold uP0; simp only
  split_ifs <;> simp_all

lemma decidesAt_uP0 (h : DecidesAt (uP0 t) r i m v) :
    (KCorrect t r i m 0 ∧ v = 0) ∨ (¬ KCorrect t r i m 0 ∧ m = t + 1 ∧ v = 1) := by
  have h2 := h.2.1
  unfold UnbeatableSetConsensus.Protocol.dec uP0 at h2
  simp only at h2
  split_ifs at h2 with h3 h4 <;> cases h2
  · exact Or.inl ⟨h3, rfl⟩
  · exact Or.inr ⟨h3, h4, rfl⟩

/-- Lemma 6 (a): a live process that knew `∃0` one round earlier knows `∃correct(0)`. -/
lemma kCorrect_of_prev (ht : t < Fintype.card P) (hr : Adm t bin r) {M : ℕ}
    (hal : r.Alive i (M + 1)) (h0 : 0 ∈ vals r i M) : KCorrect t r i (M + 1) 0 :=
  (lemma6 ht hr hal zero_mem_bin).2 ⟨vals_mono (Nat.le_succ M) h0, Or.inl ⟨Nat.succ_pos M, h0⟩⟩

/-- Lemma 6 (b) at time `≥ t`: a process learning `∃0` at time `M + 1 ≥ t` knows
`∃correct(0)` (it knows of `M` failures). -/
lemma kCorrect_of_first_late (ht : t < Fintype.card P) (hr : Adm t bin r) {M : ℕ}
    (hal : r.Alive i (M + 1)) (hn : 0 ∉ vals r i M) (hy : 0 ∈ vals r i (M + 1))
    (htM : t ≤ M + 1) : KCorrect t r i (M + 1) 0 := by
  refine (lemma6 ht hr hal zero_mem_bin).2 ⟨hy, Or.inr ?_⟩
  have hk := le_known_of_hiddenPath (hiddenPath_of_first hn hy)
  obtain hv | ⟨q, hq, hqv⟩ := mem_vals_succ.1 hy
  · exact absurd hv hn
  have : 1 ≤ carriers r i (M + 1) 0 := by
    rw [carriers_eq_card]
    exact card_pos.2 ⟨q, mem_carrierSet.2 ⟨Nat.succ_pos M, by simpa using seen_of_comm hq,
      by simpa using hqv⟩⟩
  omega

end Basic

/-! ### Theorem 8 -/

section Theorem8

variable (ht : t < Fintype.card P) {r : Run P} (hr : Adm t bin r) {i : P}
include ht hr

/-- If `f ≥ t - 1`, every process alive at `f + 1` has decided by then. -/
lemma uOpt0_decidesBy_f1 (hf : t ≤ r.faulty.card + 1) (hal : r.Alive i (r.faulty.card + 1)) :
    DecidesBy (uOpt0 t) r i (r.faulty.card + 1) := by
  refine decidesBy_of_dec hal fun hn => ?_
  obtain ⟨hk, hp | h0⟩ := uOpt0_dec_eq_none.1 hn
  · exact not_hiddenPath_faulty hp
  · by_cases h0' : 0 ∈ vals r i r.faulty.card
    · exact hk (kCorrect_of_prev ht hr hal h0')
    · exact hk (kCorrect_of_first_late ht hr hal h0' h0 hf)

/-- Every process alive at `f + 2` has decided by then. -/
lemma uOpt0_decidesBy_f2 (hal : r.Alive i (r.faulty.card + 2)) :
    DecidesBy (uOpt0 t) r i (r.faulty.card + 2) := by
  refine decidesBy_of_dec hal fun hn => ?_
  obtain ⟨hk, hp | h0⟩ := uOpt0_dec_eq_none.1 hn
  · have := le_faulty_of_hiddenPath hp; omega
  · by_cases h0' : 0 ∈ vals r i (r.faulty.card + 1)
    · exact hk (kCorrect_of_prev ht hr hal h0')
    · have := first_le h0' h0; omega

omit hr in
/-- **Theorem 8.** `U-Opt0` solves uniform consensus in `γ_cr` (`t < n`). Moreover, if `f ≥ t - 1`
all decisions are made by time `f + 1`; otherwise by time `f + 2` (for the processes alive at
those times). -/
theorem theorem8 :
    SolvesUniformSetConsensus 1 t bin (uOpt0 t : Protocol P) ∧
      (∀ r : Run P, Adm t bin r → t ≤ r.faulty.card + 1 → ∀ i, r.Alive i (r.faulty.card + 1) →
        DecidesBy (uOpt0 t) r i (r.faulty.card + 1)) ∧
      (∀ r : Run P, Adm t bin r → ∀ i, r.Alive i (r.faulty.card + 2) →
        DecidesBy (uOpt0 t) r i (r.faulty.card + 2)) := by
  refine ⟨⟨fun r hr i hi => ?_, fun r hr i m v hv => ?_, fun r hr => ?_⟩,
    fun r hr hf i hal => uOpt0_decidesBy_f1 ht hr hf hal,
    fun r hr i hal => uOpt0_decidesBy_f2 ht hr hal⟩
  · obtain ⟨m', -, v, hv⟩ := uOpt0_decidesBy_f2 ht hr (SyncCrash.Run.alive_of_not_faulty hi _)
    exact ⟨m', v, hv⟩
  · rcases decidesAt_uOpt0 hv with ⟨hk, rfl⟩ | ⟨-, -, h0, rfl⟩
    · obtain ⟨c, -, hc⟩ := hk.holds hr hv.1
      obtain ⟨j, -, hj⟩ := mem_vals.1 hc; exact ⟨j, hj⟩
    · obtain ⟨j, -, hj⟩ := mem_vals.1 (one_sub_mem_vals hr zero_mem_bin h0); exact ⟨j, hj⟩
  · classical
    rw [Nat.cast_one, Set.encard_le_one_iff]
    rintro v w ⟨i, m, hv⟩ ⟨j, m', hw⟩
    have key : ∀ {i j : P} {m m'}, DecidesAt (uOpt0 t) r i m 1 → DecidesAt (uOpt0 t) r j m' 0 →
        False := by
      intro i j m m' hi hj
      rcases decidesAt_uOpt0 hi with ⟨-, h⟩ | ⟨-, hnp, h0, -⟩
      · exact one_ne_zero h
      rcases decidesAt_uOpt0 hj with ⟨hk, -⟩ | ⟨-, -, -, h⟩
      · obtain ⟨c, hc, hcv⟩ := hk.holds hr hj.1
        obtain ⟨ℓ, hℓ, hnh⟩ := not_hiddenPath_iff.1 hnp
        exact h0 (vals_subset_of_not_hidden hℓ hnh hc m' hcv)
      · exact zero_ne_one h
    have hv01 : v = 0 ∨ v = 1 := by rcases decidesAt_uOpt0 hv with ⟨-, h⟩ | ⟨-, -, -, h⟩ <;> simp [h]
    have hw01 : w = 0 ∨ w = 1 := by rcases decidesAt_uOpt0 hw with ⟨-, h⟩ | ⟨-, -, -, h⟩ <;> simp [h]
    rcases hv01 with rfl | rfl <;> rcases hw01 with rfl | rfl
    · rfl
    · exact (key hw hv).elim
    · exact (key hv hw).elim
    · rfl

end Theorem8

/-- **Lemma 18.** `U-Opt0 ⪰ U-P0`. -/
theorem lemma18 (ht : t < Fintype.card P) : Dominates t bin (uOpt0 t : Protocol P) (uP0 t) := by
  intro r hr i m v hv
  rcases decidesAt_uP0 hv with ⟨hk, -⟩ | ⟨-, rfl, -⟩
  · refine decidesBy_of_dec hv.1 ?_
    rw [Ne, uOpt0_dec_eq_none]; tauto
  · have hf := hr.1.1
    by_cases h : t ≤ r.faulty.card + 1
    · exact DecidesBy.mono' (uOpt0_decidesBy_f1 ht hr h (hv.1.mono (by omega))) (by omega)
    · exact DecidesBy.mono' (uOpt0_decidesBy_f2 ht hr (hv.1.mono (by omega))) (by omega)

end Podc.ParetoOptimalConsensus
