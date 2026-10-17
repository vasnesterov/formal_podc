import Papers.PODC2022.RecursivePhaseKing.Subroutines

/-!
# Early-stopping Phase King with doubling elector sets (Section 3)

Algorithm 4 of [LS22] composes the three subroutines of Section 2 — weak validator
(Definition 2.2), electors' broadcast (Definition 2.5), termination check (Definition 2.7) — in a
loop whose `j`-th iteration uses the elector set `K_j` (`{ind, …, min{ind + 3·2^j, n}}`, the
paper's `max` is a typo). Corollary 3.2 is a statement about *any* implementations meeting these
specifications; we formalize it at that level.

* `Trace F K`: a spec-level execution. For every iteration `j` the outputs of the three
  subroutine calls are arbitrary subject to their specifications, applied to the opinions of all
  correct nodes. Terminated nodes keep taking part with their final value, which is the paper's
  convention (3) ("they will assume that `i` sends `b` in all future rounds").
  `Trace.validity`, `Trace.agreement`, `Trace.terminated_of_good`: the argument of
  Theorem 2.9 / Corollary 3.2 for an arbitrary sequence of elector sets.
* `K4 n j`: the elector sets of Algorithm 4 on nodes `Fin n` (node `i` is the paper's `i + 1`).
* `jStar f`: the least `J` with `2^(J+1) + J > f`, i.e. the least number of iterations that `f`
  faults cannot all spoil.
* Lemma 3.1 as stated is **false** for `f = 2` (`lemma_3_1_false`, `n = 7`, faulty nodes `1, 2`):
  the first elector set `{1, 2, 3, 4}` may contain both faults. Corrected version `lemma_3_1`
  (bound `jStar f`, which equals the paper's `⌈log(max{f/2, 1})⌉` except for `f = 2`, where it is
  `1`: `jStar_le_paperJ`, `jStar_two`).
* Corollary 3.2 as stated is false for `f = 2` (`corollary_3_2_false`); corrected `corollary_3_2`.
  The loop `for j = 0 to ⌈log(n/6)⌉` is long enough for `n ≥ 4` (`jStar_le_loopEnd`) and empty for
  `n ≤ 3` (`loopEnd_neg`).
* Theorem 1.1 (round and bit complexity, from Corollary 3.2, Lemma 3.4 and the bounds of the cited
  Theorem 3.3 taken as hypotheses): `theorem_1_1_rounds`, `theorem_1_1_bits`.
-/

set_option linter.unusedSectionVars false

namespace RecursivePhaseKing

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ### Spec-level executions of the iterated scheme -/

/-- A spec-level execution of Algorithm 1 / Algorithm 4 with elector sets `K j`: opinions `op j`
at the start of iteration `j`, outputs `(vo j, vs j)` of the validator, `eo j` of electors'
broadcast and `(tco j, tct j)` of the termination check, each constrained only by its specification
(Definitions 2.2, 2.5, 2.7). -/
structure Trace (F : Finset P) (K : ℕ → Finset P) where
  /-- Inputs. -/
  inp : P → Bool
  /-- `op j i`: the opinion of `i` at the beginning of iteration `j`. -/
  op : ℕ → P → Bool
  /-- Validator outputs. -/
  vo : ℕ → P → Bool
  /-- Validator `strong` bits. -/
  vs : ℕ → P → Bool
  /-- Electors' broadcast outputs. -/
  eo : ℕ → P → Bool
  /-- Termination check outputs. -/
  tco : ℕ → P → Bool
  /-- Termination check `term` bits. -/
  tct : ℕ → P → Bool
  op_zero : ∀ i, op 0 i = inp i
  op_succ : ∀ j i, op (j + 1) i = tco j i
  hv : ∀ j, WeakValidatorSpec F (op j) (vo j) (vs j)
  he : ∀ j, ElectorsBCSpec F (K j) (vo j) (vs j) (eo j)
  ht : ∀ j, WeakValidatorSpec F (eo j) (tco j) (tct j)

namespace Trace

variable {F : Finset P} {K : ℕ → Finset P} (T : Trace F K)

/-- `i` decides `v`: in the first iteration `j` in which `term_i = 1`, the output is `v`. -/
def Decides (i : P) (v : Bool) : Prop :=
  ∃ j, T.tct j i = true ∧ (∀ j' < j, T.tct j' i = false) ∧ T.tco j i = v

/-- `i` has terminated by the end of iteration `j`. -/
def TerminatedBy (i : P) (j : ℕ) : Prop := ∃ j' ≤ j, T.tct j' i = true

/-- If all correct nodes start iteration `j` with opinion `v`, they all terminate in it with
output `v` (validity of the three subroutines). -/
theorem iter_of_all {j : ℕ} {v : Bool} (h : ∀ i ∉ F, T.op j i = v) :
    ∀ i ∉ F, T.tco j i = v ∧ T.tct j i = true := by
  have h1 := (T.hv j).1 v h
  have h2 := (T.he j).1 v fun i hi => h1 i hi
  exact (T.ht j).1 v h2

theorem all_from {j : ℕ} {v : Bool} (h : ∀ i ∉ F, T.op j i = v) :
    ∀ j' ≥ j, ∀ i ∉ F, T.op j' i = v ∧ T.tco j' i = v ∧ T.tct j' i = true := by
  intro j' hj'
  induction j', hj' using Nat.le_induction with
  | base => exact fun i hi => ⟨h i hi, T.iter_of_all h i hi⟩
  | succ j' _ ih =>
    have hop : ∀ i ∉ F, T.op (j' + 1) i = v := fun i hi => by rw [T.op_succ]; exact (ih i hi).2.1
    exact fun i hi => ⟨hop i hi, T.iter_of_all hop i hi⟩

/-- Termination agreement: once a correct node passes the termination check, all correct nodes
hold its output. -/
theorem after_term {j : ℕ} {i : P} (hi : i ∉ F) (ht : T.tct j i = true) :
    ∀ k ∉ F, T.op (j + 1) k = T.tco j i := fun k hk => by
  rw [T.op_succ]; exact (T.ht j).2 i hi ht k hk

/-- Binary consensus, validity (Definition 2.1). -/
theorem validity {v : Bool} (h : ∀ i ∉ F, T.inp i = v) {i : P} (hi : i ∉ F) {w : Bool}
    (hw : T.Decides i w) : w = v := by
  obtain ⟨j, -, -, hj⟩ := hw
  rw [← hj]
  exact (T.all_from (j := 0) (fun i hi => by rw [T.op_zero]; exact h i hi) j (Nat.zero_le _)
    i hi).2.1

/-- Binary consensus, agreement (Definition 2.1). -/
theorem agreement {i k : P} (hi : i ∉ F) (hk : k ∉ F) {v w : Bool} (hv : T.Decides i v)
    (hw : T.Decides k w) : v = w := by
  classical
  have hex : ∃ j, ∃ p ∉ F, T.tct j p = true := by
    obtain ⟨j, hj, -⟩ := hv; exact ⟨j, i, hi, hj⟩
  set j₀ := Nat.find hex
  obtain ⟨p, hp, hpt⟩ := Nat.find_spec hex
  set u := T.tco j₀ p
  have hnext := T.all_from (T.after_term hp hpt)
  -- every correct decision equals `u`
  have key : ∀ q ∉ F, ∀ x, T.Decides q x → x = u := by
    rintro q hq x ⟨j, hjt, -, hjx⟩
    have hj₀ : j₀ ≤ j := Nat.find_min' hex ⟨q, hq, hjt⟩
    rcases Nat.eq_or_lt_of_le hj₀ with e | lt
    · rw [← hjx, ← e]; exact (T.ht j₀).2 p hp hpt q hq
    · rw [← hjx]; exact (hnext j lt q hq).2.1
  rw [key i hi v hv, key k hk w hw]

/-- Termination: if fewer than a third of the electors of iteration `j` are faulty, every correct
node terminates by the end of iteration `j`. -/
theorem terminated_of_good {j : ℕ} (hK : 3 * (K j ∩ F).card < (K j).card) :
    ∀ i ∉ F, T.TerminatedBy i j := by
  classical
  intro i hi
  by_contra hno
  -- no correct node terminated before iteration `j` (otherwise all terminate one later)
  have hall : ∀ k ∉ F, ∀ j' < j, T.tct j' k = false := by
    intro k hk j' hj'
    by_contra hkt
    rw [Bool.not_eq_false] at hkt
    have := (T.all_from (T.after_term hk hkt) (j' + 1) le_rfl i hi).2.2
    exact hno ⟨j' + 1, hj', this⟩
  -- electors' agreement in iteration `j`, then validity of the termination check
  have hagree := (T.he j).2 ((good_iff F (K j)).2 hK) (T.hv j).weakAgreement
  have := (T.ht j).1 (T.eo j i) fun k hk => hagree k hk i hi
  exact hno ⟨j, le_rfl, (this i hi).2⟩

/-- Every correct node that has terminated has decided. -/
theorem decides_of_terminated {i : P} {j : ℕ} (h : T.TerminatedBy i j) :
    ∃ v, T.Decides i v := by
  classical
  have hex : ∃ j, T.tct j i = true := by obtain ⟨j', -, h⟩ := h; exact ⟨j', h⟩
  refine ⟨T.tco (Nat.find hex) i, Nat.find hex, Nat.find_spec hex, fun j' hj' => ?_, rfl⟩
  have := Nat.find_min hex hj'
  simpa using this

end Trace

/-! ### The elector sets of Algorithm 4 -/

/-- The (0-based) first node of the elector set of iteration `j` (`ind - 1` in Algorithm 4). -/
def start : ℕ → ℕ
  | 0 => 0
  | j + 1 => start j + 3 * 2 ^ j + 1

theorem start_add_three (j : ℕ) : start j + 3 = 3 * 2 ^ j + j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [start, pow_succ]; omega

theorem start_mono {j j' : ℕ} (h : j < j') : start j + 3 * 2 ^ j + 1 ≤ start j' := by
  induction j', h using Nat.le_induction with
  | base => rfl
  | succ j' _ ih => simp only [start]; omega

/-- The elector set of iteration `j` of Algorithm 4 on the nodes `Fin n` (node `i` is the paper's
node `i + 1`): `{ind, …, min{ind + 3·2^j, n}}`. -/
def K4 (n j : ℕ) : Finset (Fin n) :=
  univ.filter fun i => start j ≤ i.val ∧ i.val ≤ start j + 3 * 2 ^ j

theorem K4_card_le (n j : ℕ) : (K4 n j).card ≤ 3 * 2 ^ j + 1 := by
  have : (K4 n j).map Fin.valEmbedding ⊆ Icc (start j) (start j + 3 * 2 ^ j) := by
    intro x hx
    simp only [mem_map, K4, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact mem_Icc.2 hi
  have := card_le_card this
  rw [card_map, Nat.card_Icc] at this
  omega

theorem K4_card_of_le {n j : ℕ} (h : start (j + 1) ≤ n) : (K4 n j).card = 3 * 2 ^ j + 1 := by
  have : (K4 n j).map Fin.valEmbedding = Icc (start j) (start j + 3 * 2 ^ j) := by
    ext x
    simp only [mem_map, K4, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      simp only [start] at h
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map, this, Nat.card_Icc]; omega

theorem K4_disjoint {n j j' : ℕ} (h : j ≠ j') : Disjoint (K4 n j) (K4 n j') := by
  rw [disjoint_left]
  intro i hi hi'
  simp only [K4, mem_filter, mem_univ, true_and] at hi hi'
  rcases lt_or_gt_of_ne h with h | h
  · have := start_mono (j := j) (j' := j') h; omega
  · have := start_mono (j := j') (j' := j) h; omega

/-- Nodes below `start (J + 1)` are covered by the elector sets of iterations `≤ J`. -/
theorem mem_K4_of_lt {n J : ℕ} (i : Fin n) (hi : i.val < start (J + 1)) :
    ∃ j ≤ J, i ∈ K4 n j := by
  simp only [K4, mem_filter, mem_univ, true_and]
  induction J with
  | zero => exact ⟨0, le_rfl, Nat.zero_le _, by simp only [start] at hi; simp; omega⟩
  | succ J ih =>
    by_cases h : i.val < start (J + 1)
    · obtain ⟨j, hj, hij⟩ := ih h; exact ⟨j, by omega, hij⟩
    · refine ⟨J + 1, le_rfl, by omega, ?_⟩
      have : start (J + 1 + 1) = start (J + 1) + 3 * 2 ^ (J + 1) + 1 := rfl
      omega

/-- Sum over pairwise disjoint elector sets. -/
theorem sum_card_K4_inter_le {n J : ℕ} (F : Finset (Fin n)) :
    ∑ j ∈ range (J + 1), (K4 n j ∩ F).card ≤ F.card := by
  rw [← card_biUnion]
  · exact card_le_card (biUnion_subset.2 fun j _ => inter_subset_right)
  · intro j _ j' _ h
    exact Disjoint.mono inter_subset_left inter_subset_left (K4_disjoint h)

theorem geom_two (J : ℕ) : ∑ j ∈ range J, 2 ^ j = 2 ^ J - 1 := by
  simpa using Nat.geomSum_eq le_rfl J

/-! ### `jStar`: the corrected iteration bound -/

theorem exists_jStar (f : ℕ) : ∃ J, f < 2 ^ (J + 1) + J :=
  ⟨f, lt_of_lt_of_le (Nat.lt_two_pow_self) (by rw [pow_succ]; omega)⟩

/-- The least `J` such that spoiling the iterations `0, …, J` of Algorithm 4 needs more than `f`
faults (`∑_{j ≤ J} (2^j + 1) = 2^(J+1) + J`). -/
def jStar (f : ℕ) : ℕ := Nat.find (exists_jStar f)

theorem lt_jStar (f : ℕ) : f < 2 ^ (jStar f + 1) + jStar f := Nat.find_spec (exists_jStar f)

theorem jStar_le {f J : ℕ} (h : f < 2 ^ (J + 1) + J) : jStar f ≤ J := Nat.find_min' _ h

/-- If `jStar f ≥ 1`, the iterations `0, …, jStar f - 1` can be spoiled by `f` faults. -/
theorem le_of_lt_jStar {f J : ℕ} (h : J < jStar f) : 2 ^ (J + 1) + J ≤ f := by
  have := Nat.find_min (exists_jStar f) h
  omega

theorem jStar_two : jStar 2 = 1 := by
  apply le_antisymm (jStar_le (by norm_num))
  by_contra h
  have h0 : jStar 2 = 0 := by omega
  have := lt_jStar 2
  rw [h0] at this; norm_num at this

/-- `J + 1 ≤ f + 1` and `2^(J+1) ≤ 2 (f + 1)` for `J = jStar f`. -/
theorem jStar_bounds (f : ℕ) : jStar f ≤ f ∧ 2 ^ (jStar f + 1) ≤ 2 * (f + 1) := by
  rcases Nat.eq_zero_or_pos (jStar f) with h0 | hpos
  · rw [h0]; omega
  · have := le_of_lt_jStar (show jStar f - 1 < jStar f by omega)
    rw [Nat.sub_add_cancel hpos] at this
    have h1 : 1 ≤ 2 ^ (jStar f) := Nat.one_le_two_pow
    rw [pow_succ]; omega

theorem jStar_le_log (f : ℕ) : jStar f ≤ Nat.log 2 (f + 1) := by
  rcases Nat.eq_zero_or_pos (jStar f) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have := le_of_lt_jStar (show jStar f - 1 < jStar f by omega)
    rw [Nat.sub_add_cancel hpos] at this
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)

/-- The paper's bound `⌈log(max{f/2, 1})⌉` (logarithms are binary). -/
noncomputable def paperJ (f : ℕ) : ℤ := ⌈Real.logb 2 (max ((f : ℝ) / 2) 1)⌉

theorem paperJ_two : paperJ 2 = 0 := by
  simp [paperJ]

/-- The paper's bound is correct except for `f = 2`. -/
theorem jStar_le_paperJ {f : ℕ} (hf : f ≠ 2) : (jStar f : ℤ) ≤ paperJ f := by
  set c := paperJ f with hc
  have hx : (1 : ℝ) ≤ max ((f : ℝ) / 2) 1 := le_max_right _ _
  have hc0 : 0 ≤ c := Int.ceil_nonneg (Real.logb_nonneg (by norm_num) hx)
  have hle : max ((f : ℝ) / 2) 1 ≤ (2 : ℝ) ^ (c : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) (by linarith)).1 (Int.le_ceil _)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hc0
  rw [hm, Int.cast_natCast, Real.rpow_natCast] at hle
  have hfm : (f : ℝ) ≤ 2 ^ (m + 1) := by
    rw [pow_succ]; linarith [le_max_left ((f : ℝ) / 2) 1]
  have hfm' : f ≤ 2 ^ (m + 1) := by exact_mod_cast hfm
  rw [hm]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have : f < 2 ^ (0 + 1) + 0 := by
      have : f ≤ 2 := by simpa using hfm'
      norm_num; omega
    exact_mod_cast jStar_le this
  · exact_mod_cast jStar_le (by omega)

/-- The paper's loop end `⌈log(n/6)⌉` (Algorithm 4, line 3). -/
noncomputable def loopEnd (n : ℕ) : ℤ := ⌈Real.logb 2 ((n : ℝ) / 6)⌉

/-- For `n ≥ 4` and `3f < n`, the iteration `jStar f` is inside the loop of Algorithm 4. -/
theorem jStar_le_loopEnd {n f : ℕ} (hn : 4 ≤ n) (h3 : 3 * f < n) : (jStar f : ℤ) ≤ loopEnd n := by
  have hn' : (0 : ℝ) < (n : ℝ) / 6 := by positivity
  rcases Nat.eq_zero_or_pos (jStar f) with h0 | hpos
  · rw [h0, Nat.cast_zero, loopEnd]
    apply Int.ceil_nonneg_of_neg_one_lt
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) hn']
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.rpow_neg_one]; linarith
  · have := le_of_lt_jStar (show jStar f - 1 < jStar f by omega)
    rw [Nat.sub_add_cancel hpos] at this
    have hpow : 6 * 2 ^ (jStar f - 1) < n := by
      have e : 2 ^ jStar f = 2 * 2 ^ (jStar f - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    rw [loopEnd]
    have : ((jStar f - 1 : ℕ) : ℤ) < ⌈Real.logb 2 ((n : ℝ) / 6)⌉ := by
      rw [Int.lt_ceil, Int.cast_natCast, Real.lt_logb_iff_rpow_lt (by norm_num) hn',
        Real.rpow_natCast, lt_div_iff₀ (by norm_num)]
      have : ((6 * 2 ^ (jStar f - 1) : ℕ) : ℝ) < n := by exact_mod_cast hpow
      push_cast at this; linarith
    omega

/-- For `1 ≤ n ≤ 3` the loop `for j = 0 to ⌈log(n/6)⌉` of Algorithm 4 is empty (degenerate case:
Algorithm 4 then never returns). -/
theorem loopEnd_neg {n : ℕ} (h1 : 1 ≤ n) (h3 : n ≤ 3) : loopEnd n < 0 := by
  have hn' : (0 : ℝ) < (n : ℝ) / 6 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h1
    positivity
  have : loopEnd n ≤ -1 := by
    rw [loopEnd, Int.ceil_le, Real.logb_le_iff_le_rpow (by norm_num) hn']
    have : (n : ℝ) ≤ 3 := by exact_mod_cast h3
    push_cast; rw [Real.rpow_neg_one]; linarith
  omega

/-! ### Lemma 3.1 -/

/-- Lemma 3.1 of [LS22], corrected: if `3f < n` (`f = |F|`), some iteration `j ≤ jStar f` of
Algorithm 4 has fewer than a third faulty electors. -/
theorem lemma_3_1 {n : ℕ} (F : Finset (Fin n)) (h3 : 3 * F.card < n) :
    ∃ j ≤ jStar F.card, 3 * (K4 n j ∩ F).card < (K4 n j).card := by
  by_contra hcon
  push Not at hcon
  set J := jStar F.card
  -- the iterations `0, …, J` together cover fewer than `n` nodes
  have hsum : ∑ j ∈ range (J + 1), (K4 n j).card < n := by
    have := sum_card_K4_inter_le (J := J) F
    have : ∑ j ∈ range (J + 1), (K4 n j).card ≤ ∑ j ∈ range (J + 1), 3 * (K4 n j ∩ F).card :=
      sum_le_sum fun j hj => hcon j (by simpa [Nat.lt_succ_iff] using hj)
    rw [← mul_sum] at this; omega
  -- hence all of them are full
  have hfull : start (J + 1) ≤ n := by
    by_contra hlt
    push Not at hlt
    have hcover : (univ : Finset (Fin n)) = (range (J + 1)).biUnion (K4 n) := by
      ext i
      simp only [mem_univ, mem_biUnion, mem_range, true_iff]
      obtain ⟨j, hj, hij⟩ := mem_K4_of_lt i (lt_of_lt_of_le i.isLt hlt.le)
      exact ⟨j, by omega, hij⟩
    have := congrArg card hcover
    rw [card_univ, Fintype.card_fin, card_biUnion (fun j _ j' _ h => K4_disjoint h)] at this
    omega
  -- so each spoiled iteration contains `2^j + 1` faults: more than `f` in total
  have hfaults : ∑ j ∈ range (J + 1), (2 ^ j + 1) ≤ F.card := by
    refine le_trans (sum_le_sum fun j hj => ?_) (sum_card_K4_inter_le F)
    have hj : j ≤ J := by simpa [Nat.lt_succ_iff] using hj
    have hc := hcon j hj
    rw [K4_card_of_le (le_trans (Nat.le_of_lt_succ (Nat.lt_succ_of_le
      (show start (j + 1) ≤ start (J + 1) from ?_))) hfull)] at hc
    · omega
    · rcases Nat.eq_or_lt_of_le hj with e | lt
      · rw [e]
      · have := start_mono (show j + 1 < J + 1 by omega); omega
  have hgeom : ∑ j ∈ range (J + 1), (2 ^ j + 1) = 2 ^ (J + 1) - 1 + (J + 1) := by
    rw [sum_add_distrib, geom_two]; simp
  have hlt : F.card < 2 ^ (J + 1) + J := lt_jStar F.card
  have h1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
  omega

/-- Lemma 3.1 of [LS22] as stated (bound `⌈log(max{f/2, 1})⌉`) is false: for `n = 7` with faulty
nodes `1, 2` (`f = 2`, `⌈log(max{f/2, 1})⌉ = 0`), the only admissible iteration `j = 0` has
elector set `{1, 2, 3, 4}`, half of which is faulty. -/
theorem lemma_3_1_false :
    ¬ ∀ (n : ℕ) (F : Finset (Fin n)), 3 * F.card < n →
      ∃ j : ℕ, (j : ℤ) ≤ paperJ F.card ∧ 3 * (K4 n j ∩ F).card < (K4 n j).card := by
  intro h
  obtain ⟨j, hj, hlt⟩ := h 7 {0, 1} (by decide)
  have h2 : ({0, 1} : Finset (Fin 7)).card = 2 := by decide
  rw [h2, paperJ_two] at hj
  have : j = 0 := by omega
  subst this
  revert hlt; decide

/-! ### Corollary 3.2 -/

/-- Corollary 3.2 of [LS22], corrected: in every spec-level execution of Algorithm 4 with
`3f < n`, every correct node terminates by the end of iteration `jStar f`, and the outputs
satisfy agreement and validity (`Trace.agreement`, `Trace.validity`). For `n ≥ 4` this iteration
lies inside the loop of Algorithm 4 (`jStar_le_loopEnd`). -/
theorem corollary_3_2 {n : ℕ} {F : Finset (Fin n)} (h3 : 3 * F.card < n) (T : Trace F (K4 n)) :
    ∀ i ∉ F, T.TerminatedBy i (jStar F.card) := by
  intro i hi
  obtain ⟨j, hj, hgood⟩ := lemma_3_1 F h3
  obtain ⟨j', hj', ht⟩ := T.terminated_of_good hgood i hi
  exact ⟨j', le_trans hj' hj, ht⟩

/-- The adversarial spec-level execution used in `corollary_3_2_false`: inputs alternate,
iteration 0 achieves nothing, iteration 1 agrees on `true`. -/
def badTrace : Trace ({0, 1} : Finset (Fin 7)) (K4 7) where
  inp i := decide (i.val % 2 = 0)
  op j i := if j ≤ 1 then decide (i.val % 2 = 0) else true
  vo j i := if j = 0 then decide (i.val % 2 = 0) else true
  vs j _ := decide (2 ≤ j)
  eo j i := if j = 0 then decide (i.val % 2 = 0) else true
  tco j i := if j = 0 then decide (i.val % 2 = 0) else true
  tct j _ := decide (1 ≤ j)
  op_zero _ := rfl
  op_succ j i := by
    rcases Nat.lt_or_ge j 1 with h | h
    · interval_cases j; rfl
    · simp [show ¬ j + 1 ≤ 1 by omega, show j ≠ 0 by omega]
  hv j := by
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j <;> exact weakValidatorSpec_iff.2 (by decide)
    · refine ⟨fun v hv i hi => ?_, fun i _ _ k _ => ?_⟩
      · have := hv 2 (by decide)
        simp only [show ¬ j ≤ 1 by omega, ↓reduceIte] at this
        simp [show j ≠ 0 by omega, ← this, h]
      · simp [show j ≠ 0 by omega]
  he j := by
    rcases Nat.lt_or_ge j 1 with h | h
    · interval_cases j; unfold ElectorsBCSpec WeakAgreement; decide
    · refine ⟨fun v hv i hi => ?_, fun _ _ i _ k _ => ?_⟩
      · have := (hv 2 (by decide)).1
        simp only [show j ≠ 0 by omega, ↓reduceIte] at this
        simp [show j ≠ 0 by omega, ← this]
      · simp [show j ≠ 0 by omega]
  ht j := by
    rcases Nat.lt_or_ge j 1 with h | h
    · interval_cases j; exact weakValidatorSpec_iff.2 (by decide)
    · refine ⟨fun v hv i hi => ?_, fun i _ _ k _ => ?_⟩
      · have := hv 2 (by decide)
        simp only [show j ≠ 0 by omega, ↓reduceIte] at this
        simp [show j ≠ 0 by omega, ← this, h]
      · simp [show j ≠ 0 by omega]

/-- Corollary 3.2 of [LS22] as stated ("terminates at the latest in iteration
`⌈log(max{f/2, 1})⌉`") is false for `f = 2`: in `badTrace` (`n = 7`, faulty nodes `1, 2`, all
subroutine outputs meeting their specifications) the correct node `3` has not terminated after
iteration `0 = ⌈log(max{2/2, 1})⌉`. -/
theorem corollary_3_2_false :
    ∃ (n : ℕ) (F : Finset (Fin n)) (T : Trace F (K4 n)), 3 * F.card < n ∧
      ∃ i ∉ F, ∀ j : ℕ, (j : ℤ) ≤ paperJ F.card → ¬ T.TerminatedBy i j := by
  refine ⟨7, {0, 1}, badTrace, by decide, 2, by decide, fun j hj => ?_⟩
  have h2 : ({0, 1} : Finset (Fin 7)).card = 2 := by decide
  rw [h2, paperJ_two] at hj
  have : j = 0 := by omega
  subst this
  rintro ⟨j', hj', ht⟩
  have : j' = 0 := by omega
  subst this
  revert ht; decide

/-! ### Theorem 1.1: round and bit complexity -/

/-- The number of rounds until the end of iteration `J` of Algorithm 4, when the consensus routine
called by Algorithm 5 on `k` electors runs for `R k` rounds: per iteration, 2 rounds of validator,
`R |K_j| + 1` rounds of electors' broadcast (Algorithm 5), 2 rounds of termination check and one
termination broadcast. -/
def roundsUntil (n : ℕ) (R : ℕ → ℕ) (J : ℕ) : ℕ :=
  ∑ j ∈ range (J + 1), (2 + (R (K4 n j).card + 1) + 2 + 1)

/-- Theorem 1.1 of [LS22] (running time `O(f + 1)`): if the consensus routine of Theorem 3.3 runs
for at most `a k + b` rounds on `k` nodes, then Algorithm 4 has terminated at every correct node
by the end of iteration `jStar f` (Corollary 3.2), i.e. after at most `(6 + b + 7a)(f + 1)`
rounds. -/
theorem theorem_1_1_rounds {n : ℕ} {F : Finset (Fin n)} (h3 : 3 * F.card < n) (T : Trace F (K4 n))
    {R : ℕ → ℕ} {a b : ℕ} (hR : ∀ k, R k ≤ a * k + b) :
    (∀ i ∉ F, T.TerminatedBy i (jStar F.card)) ∧
      roundsUntil n R (jStar F.card) ≤ (6 + b + 7 * a) * (F.card + 1) := by
  refine ⟨corollary_3_2 h3 T, ?_⟩
  set J := jStar F.card
  have hJb : J ≤ F.card ∧ 2 ^ (J + 1) ≤ 2 * (F.card + 1) := jStar_bounds F.card
  obtain ⟨hJ, hpow⟩ := hJb
  have hgeom : ∑ j ∈ range (J + 1), 2 ^ j = 2 ^ (J + 1) - 1 := geom_two _
  calc roundsUntil n R J ≤ ∑ j ∈ range (J + 1), ((6 + b + a) + 3 * a * 2 ^ j) := by
        refine sum_le_sum fun j _ => ?_
        have := hR (K4 n j).card
        have := K4_card_le n j
        nlinarith
    _ = (J + 1) * (6 + b + a) + 3 * a * (2 ^ (J + 1) - 1) := by
        rw [sum_add_distrib, ← mul_sum, hgeom]; simp
    _ ≤ (6 + b + 7 * a) * (F.card + 1) := by
        have h1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
        have : 3 * a * (2 ^ (J + 1) - 1) ≤ 6 * a * (F.card + 1) := by
          calc 3 * a * (2 ^ (J + 1) - 1) ≤ 3 * a * (2 * (F.card + 1)) :=
                Nat.mul_le_mul_left _ (by omega)
            _ = 6 * a * (F.card + 1) := by ring
        nlinarith

/-- The number of bits sent by correct nodes until the end of iteration `J`: per iteration at most
`5 n²` single-bit broadcast messages (validator, termination check, termination broadcast), plus
the bits `B k` of the consensus routine on the `k = |K_j|` electors and the `k n` bits of the
electors' final broadcast (Lemma 3.4). -/
def bitsUntil (n : ℕ) (B : ℕ → ℕ) (J : ℕ) : ℕ :=
  ∑ j ∈ range (J + 1), (5 * n ^ 2 + B (K4 n j).card + (K4 n j).card * n)

/-- Theorem 1.1 of [LS22] (bit complexity `O(n t log(f + 2))`): if the consensus routine of
Theorem 3.3 sends at most `c k n` bits on `k ≤ n` nodes (`O(t k)` in the paper), the correct nodes
send at most `5 n² (log₂(f + 1) + 1) + 7 (c + 1) n (f + 1)` bits until all of them have terminated. -/
theorem theorem_1_1_bits {n : ℕ} {F : Finset (Fin n)} {B : ℕ → ℕ} {c : ℕ}
    (hB : ∀ k ≤ n, B k ≤ c * k * n) :
    bitsUntil n B (jStar F.card) ≤
      5 * n ^ 2 * (Nat.log 2 (F.card + 1) + 1) + 7 * (c + 1) * n * (F.card + 1) := by
  set J := jStar F.card
  have hJb : J ≤ F.card ∧ 2 ^ (J + 1) ≤ 2 * (F.card + 1) := jStar_bounds F.card
  obtain ⟨hJ, hpow⟩ := hJb
  have hlog : J ≤ Nat.log 2 (F.card + 1) := jStar_le_log F.card
  have hK : ∀ j, (K4 n j).card ≤ n := fun j => by
    simpa using card_le_univ (K4 n j)
  have hsumK : ∑ j ∈ range (J + 1), (K4 n j).card ≤ 7 * (F.card + 1) := by
    calc ∑ j ∈ range (J + 1), (K4 n j).card ≤ ∑ j ∈ range (J + 1), (3 * 2 ^ j + 1) :=
          sum_le_sum fun j _ => K4_card_le n j
      _ = 3 * (2 ^ (J + 1) - 1) + (J + 1) := by
          rw [sum_add_distrib, ← mul_sum, geom_two]; simp
      _ ≤ 7 * (F.card + 1) := by omega
  calc bitsUntil n B J ≤ ∑ j ∈ range (J + 1), (5 * n ^ 2 + (c + 1) * n * (K4 n j).card) := by
        refine sum_le_sum fun j _ => ?_
        have := hB _ (hK j)
        have : B (K4 n j).card + (K4 n j).card * n ≤ (c + 1) * n * (K4 n j).card := by
          nlinarith
        omega
    _ = (J + 1) * (5 * n ^ 2) + (c + 1) * n * ∑ j ∈ range (J + 1), (K4 n j).card := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum]
    _ ≤ 5 * n ^ 2 * (Nat.log 2 (F.card + 1) + 1) + 7 * (c + 1) * n * (F.card + 1) := by
        have e1 : (J + 1) * (5 * n ^ 2) ≤ 5 * n ^ 2 * (Nat.log 2 (F.card + 1) + 1) := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have e2 : (c + 1) * n * ∑ j ∈ range (J + 1), (K4 n j).card ≤
            (c + 1) * n * (7 * (F.card + 1)) := Nat.mul_le_mul_left _ hsumK
        have : (c + 1) * n * (7 * (F.card + 1)) = 7 * (c + 1) * n * (F.card + 1) := by ring
        omega

end RecursivePhaseKing
