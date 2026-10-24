import Papers.PODC2016.UnbeatableSetConsensus.Lemma1

/-!
# Lemma 1 of the paper, as stated, is false

Take `n = 6`, `k = 2`, `t = 1`, and any set `D ⊇ {0, 1, 2}` of inputs. Process `0` has input
`2`, processes `1` and `2` have input `0`, process `3` crashes in round 1 without sending any
message, processes `4` and `5` have input `2` (`cexRun`). At time `1`, process `0` satisfies
hypotheses 1–4 of Lemma 1 with `v = 0`: it becomes low at time `1`, its only low value is `0`,
`⟨3, 0⟩` and `⟨4, 1⟩` witness `HC⟨0, 1⟩ ≥ 1 = k - 1`, and `j₁ = 4`, `j₂ = 5` are high at time `0`
and hidden from `⟨0, 1⟩` at time `1`.

The protocol `cexProtocol` solves nonuniform 2-set consensus with `t = 1` and makes every low
process decide immediately, yet process `0` decides `2`, not `0`, at time `1`:

* a process with a low input decides it at time `0`;
* at time `1`, a high process that did not hear from some process in round 1 and whose only low
  value is `0` decides its smallest high value; every other high process decides its smallest
  value.

With `t = 1`, a process that misses a message knows the unique faulty process; then all other
processes are correct, so `0` is decided (by its correct holders) and the only other value decided
is the smallest high input of the correct processes. The paper's proof breaks down in its "changes":
`j₁` would have to receive no message carrying `0` in round 1, but both `1` and `2` carry `0` and
cannot both crash (`t = 1`). Hypothesis 5 of our corrected Lemma 1 (`Lemma1Hyp.lowCrash`) fails
here: processes `1` and `2` are low at time `0` and do not crash in round 1.
-/

namespace Podc.UnbeatableSetConsensus

open Cslib Finset

namespace Cex

variable {P : Type*} [Fintype P]

open Classical in
/-- The smallest high value seen at time `1` (`k = 2`). -/
noncomputable def minHigh (r : Run P) (i : P) : ℕ :=
  if h : ((vals r i 1).filter (2 ≤ ·)).Nonempty then ((vals r i 1).filter (2 ≤ ·)).min' h
  else r.input i

/-- The special rule: `i` missed a message of round 1 and its only low value is `0`. -/
def Rule (r : Run P) (i : P) : Prop := (∃ q, q ≠ i ∧ ¬ r.Deliv q i 0) ∧ lows 2 r i 1 = {0}

open Classical in
/-- The decision of a high process at time `1`. -/
noncomputable def g (r : Run P) (i : P) : ℕ := if Rule r i then minHigh r i else minVal r i 1

open Classical in
/-- The value decided by `i`. -/
noncomputable def f (r : Run P) (i : P) : ℕ := if r.input i < 2 then r.input i else g r i

lemma sameView_one {r r' : Run P} {i : P} {m : ℕ} (h : SameView r r' i m) (hm : 1 ≤ m) :
    g r i = g r' i := by
  have h1 := h.mono hm
  have hR : Rule r i ↔ Rule r' i := by
    unfold Rule
    rw [h1.lows_eq]
    constructor
    · rintro ⟨⟨q, hq, hd⟩, hl⟩; exact ⟨⟨q, hq, fun hd' => hd ((h1.deliv_iff hq).2 hd')⟩, hl⟩
    · rintro ⟨⟨q, hq, hd⟩, hl⟩; exact ⟨⟨q, hq, fun hd' => hd ((h1.deliv_iff hq).1 hd')⟩, hl⟩
  have hmh : minHigh r i = minHigh r' i := by
    unfold minHigh; simp only [h1.vals_eq, h1.input_eq]
  unfold g
  by_cases hr : Rule r i
  · rw [ite_eq_left hr, ite_eq_left (hR.1 hr), hmh]
  · rw [ite_eq_right hr, ite_eq_right (fun h => hr (hR.2 h)), h1.minVal_eq]

open Classical in
/-- **The protocol of the counterexample** (`k = 2`). -/
noncomputable def cexProtocol : Protocol P where
  dec r i m := if r.input i < 2 then some (r.input i) else if m = 0 then none else some (g r i)
  dec_congr r r' i m h := by
    simp only [h.input_eq]
    split_ifs with h1 h2
    · rfl
    · rfl
    · rw [sameView_one h (by omega)]

lemma dec_ne_none {r : Run P} {i : P} {m : ℕ} (h : r.input i < 2 ∨ 1 ≤ m) :
    cexProtocol.dec r i m ≠ none := by
  simp only [cexProtocol]
  split_ifs <;> simp_all

lemma decidesAt_val {r : Run P} {i : P} {m v : ℕ} (h : DecidesAt cexProtocol r i m v) :
    v = f r i := by
  have := h.2.1
  simp only [cexProtocol] at this
  unfold f
  split_ifs at this with h1 h2 <;> simp_all

lemma minHigh_mem (r : Run P) (i : P) : minHigh r i ∈ vals r i 1 := by
  unfold minHigh
  split_ifs with h
  · exact (mem_filter.1 (min'_mem _ h)).1
  · exact input_mem_vals r i 1

lemma f_mem_vals (r : Run P) (i : P) : f r i ∈ vals r i 1 := by
  unfold f g
  split_ifs
  · exact input_mem_vals r i 1
  · exact minHigh_mem r i
  · exact minVal_mem r i 1

lemma mem_vals_one {r : Run P} {i : P} {v : ℕ} :
    v ∈ vals r i 1 ↔ r.input i = v ∨ ∃ q, comm r 0 q i ∧ r.input q = v := by
  rw [mem_vals_succ, vals_zero, mem_singleton]
  simp only [vals_zero, mem_singleton]
  constructor
  · rintro (h | ⟨q, hq, h⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨q, hq, h.symm⟩
  · rintro (h | ⟨q, hq, h⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨q, hq, h.symm⟩

variable {D : Set ℕ}

/-- With at most one crash, all faulty processes coincide. -/
lemma faulty_unique {r : Run P} (hr : Adm 1 D r) {q q' : P} (hq : r.Faulty q) (hq' : r.Faulty q') :
    q = q' := by
  classical
  have h1 := hr.1.1
  have : ({q, q'} : Finset P) ⊆ r.faulty := by
    intro p hp; rcases mem_insert.1 hp with rfl | hp
    · simpa using hq
    · rw [mem_singleton] at hp; subst hp; simpa using hq'
  by_contra hne
  have := (card_le_card this).trans h1
  rw [card_pair hne] at this
  omega

omit [Fintype P] in
lemma faulty_of_not_deliv {r : Run P} {q p : P} (h : ¬ r.Deliv q p 0) : r.Faulty q := by
  intro hc; exact h (deliv_of_crash_none (by simpa [SyncCrash.Run.Faulty] using hc) p 0)

/-- Correct processes are heard by everybody in round 1. -/
lemma input_mem_vals_of_correct {r : Run P} {q : P} (hq : ¬ r.Faulty q) (p : P) :
    r.input q ∈ vals r p 1 := by
  by_cases hqp : q = p
  · subst hqp; exact input_mem_vals r q 1
  · exact vals_subset_succ_of_comm ⟨hqp, SyncCrash.Run.deliv_of_not_faulty hq p 0⟩
      (by rw [vals_zero]; exact mem_singleton_self _)

/-- `k`-Agreement of the counterexample protocol, in the form "two values suffice". -/
lemma two_values {r : Run P} (hr : Adm 1 D r) :
    ∃ a b, ∀ i, ¬ r.Faulty i → f r i = a ∨ f r i = b := by
  classical
  by_cases hR : ∃ h, ¬ r.Faulty h ∧ ¬ r.input h < 2 ∧ Rule r h
  · -- case A: some correct process uses the special rule
    obtain ⟨h, hh, hhi, ⟨⟨q, hqh, hdq⟩, hlows⟩⟩ := hR
    have hqF : r.Faulty q := faulty_of_not_deliv hdq
    -- the value `0` comes from a correct process
    have h0 : 0 ∈ vals r h 1 := (mem_lows.1 (hlows ▸ mem_singleton_self 0)).1
    obtain ⟨s, hs, hs0⟩ : ∃ s, ¬ r.Faulty s ∧ r.input s = 0 := by
      rcases mem_vals_one.1 h0 with h' | ⟨s, hs, h'⟩
      · exact absurd (h' ▸ (by norm_num : (0 : ℕ) < 2)) hhi
      · refine ⟨s, fun hsF => ?_, h'⟩
        obtain rfl := faulty_unique hr hsF hqF
        exact hdq hs.2
    -- a process that missed `q` sees exactly the inputs of the others
    have hvals : ∀ i, ¬ r.Faulty i → ¬ r.Deliv q i 0 →
        ∀ v, v ∈ vals r i 1 ↔ ∃ p, p ≠ q ∧ r.input p = v := by
      intro i hi hdi v
      rw [mem_vals_one]
      constructor
      · rintro (h' | ⟨p, hp, h'⟩)
        · exact ⟨i, fun he => hi (he ▸ hqF), h'⟩
        · exact ⟨p, fun he => hdi (he ▸ hp.2), h'⟩
      · rintro ⟨p, hpq, h'⟩
        by_cases hpi : p = i
        · exact Or.inl (hpi ▸ h')
        · have hpc : ¬ r.Faulty p := fun hpF => hpq (faulty_unique hr hpF hqF)
          exact Or.inr ⟨p, ⟨hpi, SyncCrash.Run.deliv_of_not_faulty hpc i 0⟩, h'⟩
    refine ⟨0, minHigh r h, fun i hi => ?_⟩
    unfold f
    split_ifs with hil
    · left
      have : r.input i ∈ lows 2 r h 1 := mem_lows.2 ⟨input_mem_vals_of_correct hi h, hil⟩
      rw [hlows] at this; exact mem_singleton.1 this
    · unfold g
      split_ifs with hRi
      · right
        obtain ⟨⟨q', hq'i, hdq'⟩, -⟩ := hRi
        obtain rfl := faulty_unique hr (faulty_of_not_deliv hdq') hqF
        have : vals r i 1 = vals r h 1 := by
          ext v; rw [hvals i hi hdq', hvals h hh hdq]
        have hne : ((vals r h 1).filter (2 ≤ ·)).Nonempty :=
          ⟨r.input h, mem_filter.2 ⟨input_mem_vals r h 1, by omega⟩⟩
        unfold minHigh
        rw [this, dite_eq_left hne, dite_eq_left hne]
      · left
        exact Nat.le_zero.1 (hs0 ▸ minVal_le (input_mem_vals_of_correct hs i))
  · -- case B: nobody correct uses the special rule
    push Not at hR
    by_cases h01 : (∃ p, ¬ r.Faulty p ∧ r.input p = 0) ∧ (∃ p, ¬ r.Faulty p ∧ r.input p = 1)
    · obtain ⟨⟨p0, hp0, h0⟩, -⟩ := h01
      refine ⟨0, 1, fun i hi => ?_⟩
      unfold f
      split_ifs with hil
      · omega
      · unfold g; rw [ite_eq_right (hR i hi (by omega))]
        left; exact Nat.le_zero.1 (h0 ▸ minVal_le (input_mem_vals_of_correct hp0 i))
    · by_cases hC : ∃ p, ¬ r.Faulty p
      · -- the smallest correct input `c₀` and the input of the faulty process
        set C := univ.filter fun p => ¬ r.Faulty p
        have hCne : (C.image r.input).Nonempty := by
          obtain ⟨p, hp⟩ := hC; exact ⟨r.input p, mem_image.2 ⟨p, by simp [C, hp], rfl⟩⟩
        set c₀ := (C.image r.input).min' hCne
        obtain ⟨p₀, hp₀, hc₀⟩ := mem_image.1 (min'_mem _ hCne)
        have hp₀c : ¬ r.Faulty p₀ := by simpa [C] using hp₀
        have hc₀le : ∀ p, ¬ r.Faulty p → c₀ ≤ r.input p := fun p hp =>
          min'_le _ _ (mem_image.2 ⟨p, by simp [C, hp], rfl⟩)
        set b := if h : ∃ q, r.Faulty q then r.input h.choose else c₀
        refine ⟨c₀, b, fun i hi => ?_⟩
        unfold f
        split_ifs with hil
        · left
          refine le_antisymm ?_ (hc₀le i hi)
          by_contra hlt; push Not at hlt
          replace hlt : r.input p₀ < r.input i := by rw [hc₀]; exact hlt
          have h0 : r.input p₀ = 0 := by omega
          have h1 : r.input i = 1 := by omega
          exact h01 ⟨⟨p₀, hp₀c, h0⟩, ⟨i, hi, h1⟩⟩
        · unfold g; rw [ite_eq_right (hR i hi (by omega))]
          obtain ⟨s, hs, hsv⟩ := mem_vals.1 (minVal_mem r i 1)
          by_cases hsF : r.Faulty s
          · right
            have hex : ∃ q, r.Faulty q := ⟨s, hsF⟩
            simp only [b, dite_eq_left hex, ← hsv, faulty_unique hr hsF hex.choose_spec]
          · left
            refine le_antisymm ?_ (hsv ▸ hc₀le s hsF)
            have := minVal_le (input_mem_vals_of_correct hp₀c i)
            rw [hc₀] at this; exact this
      · push Not at hC
        exact ⟨0, 0, fun i hi => absurd (hC i) hi⟩

/-- **The counterexample protocol solves nonuniform 2-set consensus** for `t = 1`. -/
theorem cexProtocol_solves : SolvesSetConsensus 2 1 D (cexProtocol : Protocol P) where
  decision r _ i hi := by
    obtain ⟨m, -, v, hv⟩ := decidesBy_of_dec (SyncCrash.Run.alive_of_not_faulty hi 1)
      (dec_ne_none (r := r) (i := i) (Or.inr le_rfl))
    exact ⟨m, v, hv⟩
  validity r _ i m v hv := by
    obtain ⟨j, -, hj⟩ := mem_vals.1 (decidesAt_val hv ▸ f_mem_vals r i)
    exact ⟨j, hj⟩
  agreement r hr := by
    obtain ⟨a, b, hab⟩ := two_values hr
    have hsub : {v | ∃ i m, ¬ r.Faulty i ∧ DecidesAt cexProtocol r i m v} ⊆ {a, b} := by
      rintro v ⟨i, m, hi, hv⟩
      rw [decidesAt_val hv]
      rcases hab i hi with h | h <;> simp [h]
    refine (Set.encard_le_encard hsub).trans ((Set.encard_insert_le _ _).trans ?_)
    rw [Set.encard_singleton]; norm_num

/-- Low processes decide at once in the counterexample protocol. -/
theorem cexProtocol_lowDecides : LowDecides 2 1 D (cexProtocol : Protocol P) := by
  intro r _ i m ha hl
  refine decidesBy_of_dec ha (dec_ne_none ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨v, hv, hvk⟩ := hl
    rw [vals_zero, mem_singleton] at hv
    exact Or.inl (hv ▸ hvk)
  · exact Or.inr hm

/-! ### The run -/

/-- The run of the counterexample on `Fin 6`. -/
def cexRun : Run (Fin 6) where
  input := ![2, 0, 0, 1, 2, 2]
  crash p := if p = 3 then some 1 else none
  reach _ := ∅

lemma cexRun_deliv (q p : Fin 6) : cexRun.Deliv q p 0 ↔ q ≠ 3 := by
  by_cases hq : q = 3
  · subst hq
    rw [deliv_of_crash_some (show cexRun.crash 3 = some 1 by simp [cexRun])]
    simp [cexRun]
  · rw [iff_true_intro (deliv_of_crash_none (show cexRun.crash q = none by simp [cexRun, hq]) p 0)]
    simp [hq]

lemma cexRun_alive (p : Fin 6) (hp : p ≠ 3) (m : ℕ) : cexRun.Alive p m :=
  alive_of_crash_none (by simp [cexRun, hp]) m

lemma cexRun_vals_zero (p : Fin 6) : vals cexRun p 0 = {cexRun.input p} := vals_zero

lemma cexRun_vals_one : vals cexRun 0 1 = {0, 2} := by
  ext v
  rw [mem_vals_one]
  simp only [comm_iff, cexRun_deliv, Fin.exists_fin_succ, mem_insert, mem_singleton]
  simp [cexRun, Fin.succ]
  omega

lemma cexRun_adm (hD : ∀ v ≤ 2, v ∈ D) : Adm 1 D cexRun := by
  classical
  refine ⟨⟨?_, fun p c hc => ?_⟩, fun p => hD _ ?_⟩
  · have : cexRun.faulty ⊆ {3} := by
      intro p hp
      rw [SyncCrash.Run.mem_faulty] at hp
      by_contra h
      exact hp (by simp [cexRun, show p ≠ 3 by simpa using h])
    exact (card_le_card this).trans (by simp)
  · simp only [cexRun] at hc; split_ifs at hc; simp_all
  · fin_cases p <;> simp [cexRun]

/-- Hypotheses 1–4 of Lemma 1 (as stated in the paper) hold for process `0` at time `1` with
`v = 0`. -/
theorem cexRun_hyp : Lemma1HypPaper 2 cexRun 0 1 0 := by
  classical
  refine ⟨cexRun_alive 0 (by decide) 1, ?_, ?_, ?_, ⟨![4, 5], ?_, fun b => ⟨?_, ?_⟩⟩⟩
  · intro M hM
    obtain rfl : M = 0 := by omega
    rw [not_low_iff, cexRun_vals_zero]
    simp [cexRun]
  · ext v; simp [lows, cexRun_vals_one]; omega
  · rw [le_hc_iff]
    intro ℓ hℓ
    rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hℓ with rfl | rfl
    · refine ⟨3, mem_hiddenAt.2 (hidden_zero_iff.2 fun hs => ?_)⟩
      rcases (seen_succ_iff le_rfl).1 hs with h | ⟨q, hq, h⟩
      · exact absurd (seen_same_time h) (by decide)
      · obtain rfl := seen_same_time h
        exact hq.2 |> (cexRun_deliv 3 0).1 |> fun h => h rfl
    · exact ⟨4, mem_hiddenAt.2 (hidden_now_of_alive (cexRun_alive 4 (by decide) 1) (by decide))⟩
  · intro a b h; fin_cases a <;> fin_cases b <;> simp_all
  · intro M hM
    obtain rfl : M = 0 := by omega
    rw [not_low_iff, cexRun_vals_zero]
    fin_cases b <;> simp [cexRun]
  · fin_cases b
    · exact hidden_now_of_alive (cexRun_alive 4 (by decide) 1) (by decide)
    · exact hidden_now_of_alive (cexRun_alive 5 (by decide) 1) (by decide)

/-- In the counterexample run, process `0` decides `2` at time `1`. -/
theorem cexRun_decides : DecidesAt cexProtocol cexRun 0 1 2 := by
  classical
  have hrule : Rule cexRun 0 := by
    refine ⟨⟨3, by decide, fun h => (cexRun_deliv 3 0).1 h rfl⟩, ?_⟩
    ext v; simp [lows, cexRun_vals_one]; omega
  have hmh : minHigh cexRun 0 = 2 := by
    unfold minHigh
    rw [dite_eq_left ⟨2, by simp [cexRun_vals_one]⟩]
    refine le_antisymm (min'_le _ _ (by simp [cexRun_vals_one])) ?_
    exact le_min' _ _ _ fun y hy => (mem_filter.1 hy).2
  refine ⟨cexRun_alive 0 (by decide) 1, ?_, fun m' hm' => ?_⟩
  · have h1 : ¬ cexRun.input 0 < 2 := by simp [cexRun]
    simp only [cexProtocol, h1, g, hrule, hmh, ↓reduceIte, one_ne_zero]
  · obtain rfl : m' = 0 := by omega
    simp [cexProtocol, cexRun]

end Cex

open Cex in
/-- **Lemma 1, as stated in the paper, is false.** For `n = 6`, `k = 2`, `t = 1` and any set of
inputs `D ⊇ {0, 1, 2}`, there is a protocol solving nonuniform 2-set consensus in which every low
process decides immediately, and a run in which process `0` satisfies hypotheses 1–4 of Lemma 1
at time `1` with its unique low value `0`, but does not decide `0` at time `1` (it decides `2`). -/
theorem lemma1_paper_false {D : Set ℕ} (hD : ∀ v ≤ 2, v ∈ D) :
    ∃ Q : Protocol (Fin 6), SolvesSetConsensus 2 1 D Q ∧ LowDecides 2 1 D Q ∧
      ∃ r : Run (Fin 6), Adm 1 D r ∧ Lemma1HypPaper 2 r 0 1 0 ∧ ¬ DecidesAt Q r 0 1 0 := by
  refine ⟨cexProtocol, cexProtocol_solves, cexProtocol_lowDecides, cexRun, cexRun_adm hD,
    cexRun_hyp, fun h => ?_⟩
  have := (h.unique cexRun_decides).2
  omega

end Podc.UnbeatableSetConsensus
