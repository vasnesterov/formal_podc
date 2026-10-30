import Podc.Computability.Distributed.SleepingCrash.Model
import Papers.PODC2025.EnergyEfficientAgreement.Committees

/-!
# Multi-value consensus (Algorithm 1 of the brief announcement)

Algorithm 1 of Mirault–Robinson, *Brief Announcement: Towards Energy-Efficient Distributed
Agreement* (PODC 2025) (= Algorithm 2 of the full version arXiv:2506.12282v1), for committees
`C : ℕ → Finset P` (`C 1, …, C f`):

* round `1`: everybody is awake and sends its value `Y` (initially its input) to `C 1`;
* round `h ∈ [2, f]`: the members of `C (h-1)` and of `C h` are awake; `C (h-1)` sends to `C h`;
* round `f + 1`: everybody is awake; the members of `C f` broadcast;
* an awake process sets `Y ← max (Y ∪ received values)`; it decides `Y` at the end of round `f + 1`.

This file proves, for any committees with more than `f` members each, the correctness part of
Theorem 1 (validity and termination = Lemma 1, the corrected Lemma 2, Lemma 3, agreement =
Lemma 4) and the energy and message bounds in terms of committee sizes and memberships; the
statement for the committees of `JoinCommittees` is `theorem_1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.EnergyEfficientAgreement

open Cslib.SleepingCrash Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- The update rule `Y ← max (Y ∪ received values)`. -/
def maxRecv (Y : V) (inbox : P → Option V) : V :=
  (insert Y (univ.image fun q => (inbox q).getD Y)).max' (insert_nonempty _ _)

/-- Rounds in which `p` is awake in Algorithm 1. -/
def mvAwake (f : ℕ) (C : ℕ → Finset P) (p : P) (r : ℕ) : Prop :=
  r = 1 ∨ r = f + 1 ∨ (2 ≤ r ∧ r ≤ f ∧ (p ∈ C (r - 1) ∨ p ∈ C r))

/-- `p` sends its value to `q` in round `r` of Algorithm 1. -/
def mvSends (f : ℕ) (C : ℕ → Finset P) (p q : P) (r : ℕ) : Prop :=
  (r = 1 ∧ q ∈ C 1) ∨ (2 ≤ r ∧ r ≤ f ∧ p ∈ C (r - 1) ∧ q ∈ C r) ∨ (r = f + 1 ∧ p ∈ C f)

instance (f : ℕ) (C : ℕ → Finset P) (p : P) (r : ℕ) : Decidable (mvAwake f C p r) := by
  unfold mvAwake; infer_instance

instance (f : ℕ) (C : ℕ → Finset P) (p q : P) (r : ℕ) : Decidable (mvSends f C p q r) := by
  unfold mvSends; infer_instance

/-- **Algorithm 1** (Multi Value Consensus) with committees `C 1, …, C f`; the state is the
variable `Y`, the decision is `Y` at the end of round `f + 1`. -/
def multiValue (f : ℕ) (C : ℕ → Finset P) : Algorithm P V V V where
  init _ x := x
  awake p r _ := decide (mvAwake f C p r)
  send p r Y q := if mvSends f C p q r then some Y else none
  recv _ _ Y inbox := maxRecv Y inbox

/-! ### The update rule -/

section maxRecv

variable {y c v : V} {inbox : P → Option V}

lemma le_maxRecv_self : y ≤ maxRecv y inbox := le_max' _ _ (mem_insert_self _ _)

lemma le_maxRecv {q : P} (h : inbox q = some v) : v ≤ maxRecv y inbox :=
  le_max' _ _ (mem_insert_of_mem (mem_image.2 ⟨q, mem_univ _, by simp [h]⟩))

lemma maxRecv_le (hY : y ≤ c) (h : ∀ q v, inbox q = some v → v ≤ c) : maxRecv y inbox ≤ c := by
  refine max'_le _ _ _ fun y hy => ?_
  rcases mem_insert.1 hy with rfl | hy
  · exact hY
  · obtain ⟨q, -, rfl⟩ := mem_image.1 hy
    cases hq : inbox q with
    | none => simpa using hY
    | some w => simpa using h q w hq

lemma maxRecv_mem : maxRecv y inbox = y ∨ ∃ q, inbox q = some (maxRecv y inbox) := by
  have := max'_mem _ (insert_nonempty y (univ.image fun q => (inbox q).getD y))
  rcases mem_insert.1 this with h | h
  · exact Or.inl h
  · obtain ⟨q, -, hq⟩ := mem_image.1 h
    cases h' : inbox q with
    | none => left; simp [h'] at hq; exact hq.symm
    | some w => right; refine ⟨q, ?_⟩; simp [h'] at hq; rw [h', hq]; rfl

lemma maxRecv_of_none (h : ∀ q, inbox q = none) : maxRecv y inbox = y :=
  le_antisymm (maxRecv_le le_rfl fun q v hq => by simp [h q] at hq) le_maxRecv_self

end maxRecv

/-! ### Basic facts about executions -/

variable {f : ℕ} {C : ℕ → Finset P} {adv : Adversary P V}

local notation "Y" => config (multiValue f C) adv

lemma mv_config_succ (r : ℕ) (q : P) : Y (r + 1) q =
    if mvAwake f C q (r + 1) then
      maxRecv (Y r q) (inbox (multiValue f C) adv (r + 1) (Y r) q)
    else Y r q := by
  rw [config_succ_apply]
  simp [multiValue]

/-- Values never decrease. -/
lemma mv_mono_succ (r : ℕ) (q : P) : Y r q ≤ Y (r + 1) q := by
  rw [mv_config_succ]
  split_ifs
  · exact le_maxRecv_self
  · exact le_rfl

lemma mv_mono {r r' : ℕ} (h : r ≤ r') (q : P) : Y r q ≤ Y r' q := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ r' _ ih => exact ih.trans (mv_mono_succ r' q)

/-- Received messages carry the sender's value, and the sender has not crashed before. -/
lemma mv_inbox_eq_some {r : ℕ} {p q : P} {v : V}
    (h : inbox (multiValue f C) adv (r + 1) (Y r) q p = some v) :
    adv.Alive p r ∧ mvSends f C p q (r + 1) ∧ v = Y r p := by
  obtain ⟨-, h2, h3⟩ := inbox_eq_some h
  simp only [multiValue] at h3
  split_ifs at h3 with hs
  · exact ⟨by simpa using h2, hs, (Option.some_injective _ h3).symm⟩

/-- A message from a sender that does not crash in round `r + 1` reaches every awake recipient. -/
lemma mv_le_of_deliver {r : ℕ} {p q : P} (hp : adv.Alive p (r + 1))
    (hpa : mvAwake f C p (r + 1)) (hs : mvSends f C p q (r + 1)) (hqa : mvAwake f C q (r + 1)) :
    Y r p ≤ Y (r + 1) q := by
  rw [mv_config_succ]
  simp only [hqa, ↓reduceIte]
  refine le_maxRecv (q := p) ?_
  rw [inbox_eq_send hp (by simpa [multiValue] using hpa)]
  simp [multiValue, hs]

/-- If nobody sends to `q` in round `r + 1`, its value does not change. -/
lemma mv_config_succ_of_not_sends {r : ℕ} {q : P} (h : ∀ p, ¬ mvSends f C p q (r + 1)) :
    Y (r + 1) q = Y r q := by
  rw [mv_config_succ]
  split_ifs
  · refine maxRecv_of_none fun p => ?_
    cases hp : inbox (multiValue f C) adv (r + 1) (Y r) q p with
    | none => rfl
    | some v => exact absurd (mv_inbox_eq_some hp).2.1 (h p)
  · rfl

/-- If every value `q` holds or receives in round `r + 1` is at most `c`, so is its new value. -/
lemma mv_le_of_forall {r : ℕ} {q : P} {c : V} (hq : Y r q ≤ c)
    (h : ∀ p, adv.Alive p r → mvSends f C p q (r + 1) → Y r p ≤ c) : Y (r + 1) q ≤ c := by
  rw [mv_config_succ]
  split_ifs
  · refine maxRecv_le hq fun p v hp => ?_
    obtain ⟨h1, h2, rfl⟩ := mv_inbox_eq_some hp
    exact h p h1 h2
  · exact hq

/-! ### Lemma 1: validity (termination at round `f + 1` holds by construction) -/

/-- Every value held at any time is the input of some process. -/
theorem mv_validity (r : ℕ) (p : P) : ∃ q, Y r p = adv.input q := by
  induction r generalizing p with
  | zero => exact ⟨p, rfl⟩
  | succ r ih =>
    rw [mv_config_succ]
    split_ifs
    · rcases maxRecv_mem (y := Y r p) (inbox := inbox (multiValue f C) adv (r + 1) (Y r) p)
        with h | ⟨q, hq⟩
      · rw [h]; exact ih p
      · rw [(mv_inbox_eq_some hq).2.2]; exact ih q
    · exact ih p

/-- Members of `C r` are awake in round `r` (`1 ≤ r ≤ f`). -/
lemma mvAwake_of_mem {r : ℕ} {q : P} (h1 : 1 ≤ r) (h2 : r ≤ f) (hq : q ∈ C r) :
    mvAwake f C q r := by
  unfold mvAwake
  rcases Nat.lt_or_ge r 2 with h | h
  · left; omega
  · right; right; exact ⟨h, h2, Or.inr hq⟩

/-- A process that does not crash in round `f + 1` receives the broadcast of every non-faulty
member of `C f`. -/
lemma mv_final_ge {c d : P} (hc : c ∈ C f) (hcf : ¬ adv.Faulty c) :
    Y f c ≤ Y (f + 1) d :=
  mv_le_of_deliver (adv.alive_of_not_faulty hcf _) (Or.inr (Or.inl rfl))
    (Or.inr (Or.inr ⟨rfl, hc⟩)) (Or.inr (Or.inl rfl))

/-! ### Committees with more than `f` members -/

section Committees

variable (hC : ∀ i, 1 ≤ i → i ≤ f → f < (C i).card) (hadm : adv.Admissible f)
include hC hadm

/-- Every committee has a non-faulty member. -/
lemma exists_correct_member {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ f) : ∃ c ∈ C i, ¬ adv.Faulty c :=
  hadm.exists_not_faulty (hC i h1 h2)

/-- A value that a process `p` (not crashing in round `r + 1`) sends to all of `C (r + 1)` in round
`r + 1 ≤ f` reaches every non-faulty member of every later committee `C j`, `j ≤ f`. -/
lemma mv_reach {r j : ℕ} {p : P} (hrj : r + 1 ≤ j) (hj : j ≤ f) (hp : adv.Alive p (r + 1))
    (hpa : mvAwake f C p (r + 1)) (hps : ∀ q ∈ C (r + 1), mvSends f C p q (r + 1)) {c : P}
    (hc : c ∈ C j) (hcf : ¬ adv.Faulty c) : Y r p ≤ Y j c := by
  induction j, hrj using Nat.le_induction generalizing c with
  | base => exact mv_le_of_deliver hp hpa (hps c hc) (mvAwake_of_mem (by omega) hj hc)
  | succ j hrj ih =>
    obtain ⟨c₀, hc₀, hc₀f⟩ := exists_correct_member hC hadm (i := j) (by omega) (by omega)
    refine (ih (by omega) hc₀ hc₀f).trans (mv_le_of_deliver (adv.alive_of_not_faulty hc₀f _) ?_ ?_
      (mvAwake_of_mem (by omega) hj hc))
    · right; right; refine ⟨by omega, hj, Or.inl (by simpa using hc₀)⟩
    · right; left; exact ⟨by omega, hj, by simpa using hc₀, hc⟩

/-- Propagation along non-faulty committee members (`i < j ≤ f`). -/
lemma mv_propagate {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ f) {c c' : P} (hc : c ∈ C i)
    (hcf : ¬ adv.Faulty c) (hc' : c' ∈ C j) (hcf' : ¬ adv.Faulty c') : Y i c ≤ Y j c' := by
  refine mv_reach hC hadm (r := i) hij hj (adv.alive_of_not_faulty hcf _) ?_ ?_ hc' hcf'
  · right; right; exact ⟨by omega, by omega, Or.inl (by simpa using hc)⟩
  · intro q hq; right; left; exact ⟨by omega, by omega, by simpa using hc, hq⟩

/-- Key invariant: at the end of round `r ∈ [1, f]`, the value of any process `p ∉ C r` that has
not crashed is at most the value of any non-faulty member of `C r`. -/
lemma mv_le_correct {r : ℕ} (hr : 1 ≤ r) (hrf : r ≤ f) {p : P} (hp : adv.Alive p r)
    (hpC : p ∉ C r) {c : P} (hc : c ∈ C r) (hcf : ¬ adv.Faulty c) : Y r p ≤ Y r c := by
  induction r, hr using Nat.le_induction generalizing p c with
  | base =>
    have h0 : Y 1 p = Y 0 p := mv_config_succ_of_not_sends fun q hq => by
      rcases hq with ⟨-, hq⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact hpC hq
      · omega
      · omega
    rw [h0]
    exact mv_le_of_deliver hp (Or.inl rfl) (Or.inl ⟨rfl, hc⟩) (Or.inl rfl)
  | succ r hr ih =>
    have h0 : Y (r + 1) p = Y r p := mv_config_succ_of_not_sends fun q hq => by
      rcases hq with ⟨h, -⟩ | ⟨-, -, -, hq⟩ | ⟨h, -⟩
      · omega
      · exact hpC hq
      · omega
    rw [h0]
    by_cases hpr : p ∈ C r
    · exact mv_le_of_deliver hp (Or.inr (Or.inr ⟨by omega, hrf, Or.inl (by simpa using hpr)⟩))
        (Or.inr (Or.inl ⟨by omega, hrf, by simpa using hpr, hc⟩))
        (mvAwake_of_mem (by omega) hrf hc)
    · obtain ⟨c₀, hc₀, hc₀f⟩ := exists_correct_member hC hadm (i := r) hr (by omega)
      exact (ih (by omega) (hp.mono (Nat.le_succ r)) hpr hc₀ hc₀f).trans
        (mv_propagate hC hadm hr (Nat.lt_succ_self r) hrf hc₀ hc₀f hc hcf)

/-- **Lemma 3** of the paper (without its unnecessary hypothesis `m ≥ δ`): at the end of round
`i ∈ [1, f]`, every process that has not crashed holds a value at most the maximum value held by
the members of `C i` that have not crashed. -/
theorem lemma_3 {i : ℕ} (hi : 1 ≤ i) (hif : i ≤ f) {p : P} (hp : adv.Alive p i) :
    ∃ q ∈ C i, adv.Alive q i ∧ Y i p ≤ Y i q := by
  by_cases hpC : p ∈ C i
  · exact ⟨p, hpC, hp, le_rfl⟩
  · obtain ⟨c, hc, hcf⟩ := exists_correct_member hC hadm hi hif
    exact ⟨c, hc, adv.alive_of_not_faulty hcf _, mv_le_correct hC hadm hi hif hp hpC hc hcf⟩

/-- **Lemma 2** of the paper, corrected: if a process sends value `v` in round `i ∈ [1, f + 1]`
and does *not crash in round `i`*, then every process that completes round `f + 1` decides a
value `≥ v` (so `v ≤ δ`, the largest decision). The paper's hypothesis "alive in round `i`" (= not
crashed in rounds `1, …, i - 1`) is too weak, see `lemma_2_as_stated_false`. -/
theorem lemma_2 (hf : 1 ≤ f) {i : ℕ} (hi : 1 ≤ i) (hif : i ≤ f + 1) {p q : P}
    (hp : adv.Alive p i) (hs : mvSends f C p q i) {d : P} :
    Y (i - 1) p ≤ Y (f + 1) d := by
  obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.lt_or_ge r f with hrf | hrf
  · -- `p` sends to all of `C (r + 1)`; the value reaches a non-faulty member of `C f`
    obtain ⟨c, hc, hcf⟩ := exists_correct_member hC hadm (i := f) hf le_rfl
    have hall : ∀ q ∈ C (r + 1), mvSends f C p q (r + 1) := by
      intro q' hq'
      rcases hs with ⟨h, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨h, -⟩
      · exact Or.inl ⟨h, by simpa [h] using hq'⟩
      · exact Or.inr (Or.inl ⟨h1, h2, h3, hq'⟩)
      · omega
    have hpa : mvAwake f C p (r + 1) := by
      rcases hs with ⟨h, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨h1, h2, Or.inl h3⟩)
      · exact Or.inr (Or.inl h)
    exact (mv_reach hC hadm (by omega) le_rfl hp hpa hall hc hcf).trans (mv_final_ge hc hcf)
  · -- round `f + 1`: `p ∈ C f` broadcasts
    have hr : f = r := by omega
    subst hr
    have hpC : p ∈ C f := by
      rcases hs with ⟨h, -⟩ | ⟨h1, h2, -⟩ | ⟨-, h⟩
      · omega
      · omega
      · exact h
    exact mv_le_of_deliver hp (Or.inr (Or.inl rfl)) (Or.inr (Or.inr ⟨rfl, hpC⟩))
      (Or.inr (Or.inl rfl))

/-- In a round `t ∈ [1, f]` without crashes, all members of `C t` that have not crashed end the
round with the same value. -/
lemma mv_clean_le {t : ℕ} (ht : 1 ≤ t) (htf : t ≤ f) (hclean : ∀ p, adv.crash p ≠ some t)
    {q q' : P} (hq : q ∈ C t) (hqa : adv.Alive q t) (hq' : q' ∈ C t) :
    Y t q ≤ Y t q' := by
  obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
  have halive : ∀ p, adv.Alive p r → adv.Alive p (r + 1) := fun p hp =>
    (Adversary.alive_iff_of_not_crash (hclean p)).2 hp
  have hq'a : mvAwake f C q' (r + 1) := mvAwake_of_mem ht htf hq'
  refine mv_le_of_forall ?_ fun p hp hs => ?_
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact mv_le_of_deliver hqa (Or.inl rfl) (Or.inl ⟨rfl, hq'⟩) hq'a
    · obtain ⟨s, hs, hsa, hle⟩ := lemma_3 hC hadm (i := r) hr (by omega) (hqa.mono (Nat.le_succ r))
      exact hle.trans (mv_le_of_deliver (halive s hsa)
        (Or.inr (Or.inr ⟨by omega, htf, Or.inl (by simpa using hs)⟩))
        (Or.inr (Or.inl ⟨by omega, htf, by simpa using hs, hq'⟩)) hq'a)
  · rcases hs with ⟨h, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨h, -⟩
    · exact mv_le_of_deliver (halive p hp) (Or.inl h) (Or.inl ⟨h, by simpa [h] using hq'⟩) hq'a
    · exact mv_le_of_deliver (halive p hp) (Or.inr (Or.inr ⟨h1, h2, Or.inl h3⟩))
        (Or.inr (Or.inl ⟨h1, h2, h3, hq'⟩)) hq'a
    · omega

/-- **Lemma 4** of the paper (agreement): all processes that complete round `f + 1` decide the
same value. -/
theorem lemma_4 (hf : 1 ≤ f) {d d' : P} (hd : adv.Alive d (f + 1)) (hd' : adv.Alive d' (f + 1)) :
    Y (f + 1) d = Y (f + 1) d' := by
  suffices ∃ V₀, ∀ d, adv.Alive d (f + 1) → Y (f + 1) d = V₀ by
    obtain ⟨V₀, h⟩ := this
    rw [h d hd, h d' hd']
  obtain ⟨t, ht1, htf, hclean⟩ := hadm.exists_clean_round
  rcases Nat.lt_or_ge f t with hft | hft
  · -- the last round is clean: everybody receives the values of all of `C f`
    have ht : t = f + 1 := by omega
    subst ht
    obtain ⟨c, hc, hcf⟩ := exists_correct_member hC hadm (i := f) hf le_rfl
    have hne : ((C f).filter fun s => adv.Alive s f).Nonempty :=
      ⟨c, by simp [hc, adv.alive_of_not_faulty hcf]⟩
    obtain ⟨s, hs, hmax⟩ := exists_max_image _ (fun s => Y f s) hne
    simp only [mem_filter] at hs hmax
    refine ⟨Y f s, fun d hd => le_antisymm ?_ ?_⟩
    · refine mv_le_of_forall ?_ fun p hp hps => ?_
      · obtain ⟨q, hq, hqa, hle⟩ := lemma_3 hC hadm hf le_rfl (hd.mono (Nat.le_succ f))
        exact hle.trans (hmax q ⟨hq, hqa⟩)
      · rcases hps with ⟨h, -⟩ | ⟨h1, h2, -⟩ | ⟨-, h⟩
        · omega
        · omega
        · exact hmax p ⟨h, hp⟩
    · exact mv_le_of_deliver ((Adversary.alive_iff_of_not_crash (hclean s)).2 hs.2)
        (Or.inr (Or.inl rfl)) (Or.inr (Or.inr ⟨rfl, hs.1⟩)) (Or.inr (Or.inl rfl))
  · -- a clean round `t ≤ f`: the non-faulty member `c` of `C t` holds the maximum from then on
    obtain ⟨c, hc, hcf⟩ := exists_correct_member hC hadm ht1 hft
    have hbound : ∀ r, t ≤ r → r ≤ f + 1 → ∀ p, adv.Alive p r → Y r p ≤ Y t c := by
      intro r htr hr
      induction r, htr using Nat.le_induction with
      | base =>
        intro p hp
        by_cases hpC : p ∈ C t
        · exact mv_clean_le hC hadm ht1 hft hclean hpC hp hc
        · exact mv_le_correct hC hadm ht1 hft hp hpC hc hcf
      | succ r htr ih =>
        intro p hp
        exact mv_le_of_forall (ih (by omega) p (hp.mono (Nat.le_succ r)))
          fun q hq _ => ih (by omega) q hq
    refine ⟨Y t c, fun d hd => le_antisymm (hbound (f + 1) (by omega) le_rfl d hd) ?_⟩
    obtain ⟨c', hc', hc'f⟩ := exists_correct_member hC hadm (i := f) hf le_rfl
    refine le_trans ?_ (mv_final_ge hc' hc'f)
    rcases Nat.lt_or_ge t f with htf' | htf'
    · exact mv_propagate hC hadm ht1 htf' le_rfl hc hcf hc' hc'f
    · have : t = f := by omega
      subst this
      exact mv_clean_le hC hadm ht1 hft hclean hc (adv.alive_of_not_faulty hcf _) hc'

end Committees

/-! ### Energy and message complexity -/

lemma mvAwake_of_awakeIn {p : P} {r : ℕ} (h : AwakeIn (multiValue f C) adv p r) :
    mvAwake f C p r := by
  simpa [AwakeIn, multiValue] using h.2

lemma mvSends_of_sendsIn {p q : P} {r : ℕ} (h : SendsIn (multiValue f C) adv p q r) :
    mvSends f C p q r := by
  have := h.2
  simp only [multiValue] at this
  split_ifs at this with hs
  · exact hs
  · simp at this

/-- Energy: a process is awake in rounds `1` and `f + 1` and in two rounds per committee it
belongs to. -/
theorem mv_awakeCount_le (p : P) :
    awakeCount (multiValue f C) adv (f + 1) p ≤
      2 + 2 * ((Icc 1 f).filter (fun i => p ∈ C i)).card := by
  set K := (Icc 1 f).filter (fun i => p ∈ C i)
  calc awakeCount (multiValue f C) adv (f + 1) p
      ≤ (({1, f + 1} ∪ K) ∪ K.image (· + 1) : Finset ℕ).card := by
        refine awakeCount_le_card fun r h1 h2 hr => ?_
        rcases mvAwake_of_awakeIn hr with rfl | rfl | ⟨h3, h4, hp | hp⟩
        · simp
        · simp
        · simp only [mem_union, mem_insert, mem_singleton, mem_image]
          right; exact ⟨r - 1, by simp [K, hp]; omega, by omega⟩
        · simp only [mem_union, mem_insert, mem_singleton]
          left; right; simp [K, hp]; omega
    _ ≤ 2 + K.card + K.card := by
        refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans
          (Nat.add_le_add_right card_le_two _)) card_image_le)
    _ = 2 + 2 * K.card := by ring

/-- Messages: in round `1` at most `|P|·|C 1|`, in round `h ∈ [2, f]` at most `|C (h-1)|·|C h|`,
in round `f + 1` at most `|C f|·|P|`; with committees of size `≤ k` this is at most
`(f + 1)·k² + 2·|P|·k`. -/
theorem mv_msgCount_le {k : ℕ} (hk : ∀ i, (C i).card ≤ k) :
    msgCount (multiValue f C) adv (f + 1) ≤
      (f + 1) * (k * k) + 2 * (Fintype.card P * k) := by
  unfold msgCount
  have hround : ∀ r ∈ Icc 1 (f + 1),
      (univ.filter fun e : P × P => SendsIn (multiValue f C) adv e.1 e.2 r).card ≤
        k * k + ((if r = 1 then Fintype.card P * k else 0) +
          (if r = f + 1 then Fintype.card P * k else 0)) := by
    intro r _
    have hsub : (univ.filter fun e : P × P => SendsIn (multiValue f C) adv e.1 e.2 r) ⊆
        (C (r - 1) ×ˢ C r) ∪ ((if r = 1 then (univ ×ˢ C 1) else ∅) ∪
          (if r = f + 1 then (C f ×ˢ univ) else ∅)) := by
      intro e he
      simp only [mem_filter, mem_univ, true_and] at he
      rcases mvSends_of_sendsIn he with ⟨h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add ?_
      ((card_union_le _ _).trans (add_le_add ?_ ?_))))
    · rw [card_product]; exact Nat.mul_le_mul (hk _) (hk _)
    · split_ifs
      · rw [card_product, card_univ]; exact Nat.mul_le_mul_left _ (hk _)
      · simp
    · split_ifs
      · rw [card_product, card_univ, mul_comm]; exact Nat.mul_le_mul_left _ (hk _)
      · simp
  refine (sum_le_sum hround).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_add_distrib, sum_const, sum_ite_eq', sum_ite_eq']
  simp [two_mul]

/-! ### Theorem 1 -/

/-- **Theorem 1** of the paper (the multi-value consensus algorithm, Algorithm 1, with the
committees `C_1, …, C_f` of size `f + 1` of `JoinCommittees(f, f + 1)`), for `n` players and
`1 ≤ f < n`, against every adversary crashing at most `f` players, with values in any linear order:

* termination: every player that does not crash by the end of round `f + 1` decides (its value
  `Y` at the end of round `f + 1`) — this is by construction of the statement;
* agreement and validity;
* energy: every player is awake in at most `2 + 2⌈f(f+1)/n⌉ = O(⌈f²/n⌉)` rounds;
* messages: at most `(f + 1)³ + 2n(f + 1) = O(f³ + nf)` messages, each a single value. -/
theorem theorem_1 {n f : ℕ} [NeZero n] (hf : 1 ≤ f) (hfn : f < n) (adv : Adversary (Fin n) V)
    (hadm : adv.Admissible f) :
    let alg := multiValue (V := V) f (joinCommittees n f (f + 1))
    (∀ d d', adv.Alive d (f + 1) → adv.Alive d' (f + 1) →
        config alg adv (f + 1) d = config alg adv (f + 1) d') ∧
      (∀ d, ∃ q, config alg adv (f + 1) d = adv.input q) ∧
      (∀ p, awakeCount alg adv (f + 1) p ≤ 2 + 2 * ((f * (f + 1)) ⌈/⌉ n)) ∧
      msgCount alg adv (f + 1) ≤ (f + 1) * ((f + 1) * (f + 1)) + 2 * (n * (f + 1)) := by
  intro alg
  have hC : ∀ i, 1 ≤ i → i ≤ f → f < (joinCommittees n f (f + 1) i).card := fun i h1 h2 => by
    rw [card_joinCommittees (by omega) h1 h2]; omega
  refine ⟨fun d d' hd hd' => lemma_4 hC hadm hf hd hd', fun d => mv_validity _ _,
    fun p => (mv_awakeCount_le p).trans ?_, ?_⟩
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (card_filter_mem_joinCommittees_le (Nat.succ_pos f) p)) 2
  · have := mv_msgCount_le (f := f) (C := joinCommittees n f (f + 1)) (adv := adv)
      (k := f + 1) fun i => by
        unfold joinCommittees
        split_ifs with h
        · exact (card_image_le).trans (by
            obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            simp [add_mul])
        · simp
    simpa using this

/-! ### Lemma 2 as stated is false -/

/-- Lemma 2 exactly as stated in the paper: if in some round `i ∈ [1, f + 1]` an awake player `p`
that is *alive in round `i`* (has not crashed in rounds `1, …, i - 1`) sends a message with a value
`v_p > δ` (`δ` = the largest decided value), then no player decides `δ`. -/
def Lemma2AsStated (n f : ℕ) [NeZero n] : Prop :=
  ∀ adv : Adversary (Fin n) ℕ, adv.Admissible f →
    let alg := multiValue (V := ℕ) f (joinCommittees n f (f + 1))
    ∀ δ : ℕ, (∃ d, adv.Alive d (f + 1) ∧ config alg adv (f + 1) d = δ) →
      (∀ d, adv.Alive d (f + 1) → config alg adv (f + 1) d ≤ δ) →
      ∀ i p q, 1 ≤ i → i ≤ f + 1 → adv.Alive p (i - 1) →
        mvAwake f (joinCommittees n f (f + 1)) p i →
        mvSends f (joinCommittees n f (f + 1)) p q i → δ < config alg adv (i - 1) p →
        ¬ ∃ d, adv.Alive d (f + 1) ∧ config alg adv (f + 1) d = δ

/-- The adversary refuting Lemma 2 as stated: `n = 2`, `f = 1`, inputs `5, 0`; player `0` crashes in
round `1` and its message (to `C 1 = {0, 1}`) reaches nobody. -/
def lemma2Adv : Adversary (Fin 2) ℕ where
  input p := if p = 0 then 5 else 0
  crash p := if p = 0 then some 1 else none
  reach _ := ∅

/-- **Lemma 2 of the paper is false as stated**: with `n = 2`, `f = 1`, player `0` (input `5`)
is alive in round `1`, awake, and sends `5` to `C 1`, but crashes in that round and its message is
lost; player `1` decides `δ = 0 < 5`. The proof of the paper assumes that `p` "successfully sends its
message", i.e. does not crash in round `i` (see the corrected `lemma_2`). -/
theorem lemma_2_as_stated_false : ¬ Lemma2AsStated 2 1 := by
  intro H
  have hadm : lemma2Adv.Admissible 1 := by
    refine ⟨by decide, fun p c hc => ?_⟩
    simp only [lemma2Adv] at hc
    split_ifs at hc; simp_all
  have hdec : config (multiValue (V := ℕ) 1 (joinCommittees 2 1 2)) lemma2Adv 2 1 = 0 := by
    decide
  have h1 : lemma2Adv.Alive 1 2 := fun c hc => by simp [lemma2Adv] at hc
  have h0 : ¬ lemma2Adv.Alive 0 2 := fun h => by
    have := h 1 (by simp [lemma2Adv]); omega
  have hall : ∀ d, lemma2Adv.Alive d 2 →
      config (multiValue (V := ℕ) 1 (joinCommittees 2 1 2)) lemma2Adv 2 d ≤ 0 := by
    intro d hd
    fin_cases d
    · exact absurd hd h0
    · exact hdec.le
  exact H lemma2Adv hadm 0 ⟨1, h1, hdec⟩ hall 1 0 1 le_rfl (by norm_num)
    (hadm.alive_zero 0) (Or.inl rfl) (Or.inl ⟨rfl, by decide⟩) (by decide) ⟨1, h1, hdec⟩

/-- Non-vacuity of `theorem_1`: crash-free adversaries are admissible. -/
example (n f : ℕ) : ({ input := fun _ => 0, crash := fun _ => none, reach := fun _ => ∅ } :
    Adversary (Fin n) ℕ).Admissible f :=
  ⟨(Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun _ _ h => h rfl)).le.trans
    (Nat.zero_le f), fun _ _ h => by cases h⟩

end Podc.EnergyEfficientAgreement
