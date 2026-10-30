import Mathlib
import Podc.Foundations.Data.Multiset.OrderStatistic

/-!
# Algorithm APA on top of crusader broadcast: Lemmas 7, 8 and Theorem 9 (abstract layer)

Lenzen–Loss, *Optimal Clock Synchronization with Signatures* (PODC 2022), Section 2.1.

Every node `w` has broadcast its value with an instance of crusader broadcast (CB), so it holds a
vector `o w : P → Option ℝ` (`o w d` is the output of the CB instance with dealer `d`; `none` = `⊥`).
Algorithm APA (Figure 1) then lets `b` be the number of `⊥` outputs, sorts the non-`⊥` values,
discards the `f - b` lowest and the `f - b` highest ones and outputs the midpoint of the interval
spanned by the remaining values.

This file proves the combinatorial core, assuming only the two properties of crusader broadcast
(Definition 6): validity and crusader consistency (`IsCrusader`). The protocol-level statement
(signatures, two synchronous rounds) is in `Protocol.lean`.

* `lemma_7`: replacing one `⊥` by any value `x` shrinks the retained interval.
* `lemma_8`: the retained intervals of all honest nodes have a common point, proved by induction
  on the total number of `⊥` outputs at honest nodes, as in the paper (the induction step must
  replace a `⊥` by the value the other honest nodes received, to stay within executions satisfying
  crusader consistency).
* `apa_step`: the outputs stay in every interval containing the honest inputs and are pairwise
  within half its length (Theorem 9, step form); `theorem_9_core`: the `(ℓ, ℓ/2)` form.
-/

open Multiset

set_option linter.unusedSectionVars false

noncomputable section

namespace Podc.ClockSyncSignatures

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ### The decision rule of Algorithm APA -/

/-- The non-`⊥` values received (as a multiset). -/
def vals (o : P → Option ℝ) : Multiset ℝ := (Finset.univ : Finset P).val.filterMap o

/-- `b`: the number of CB instances that output `⊥`. -/
def numBot (o : P → Option ℝ) : ℕ := (Finset.univ.filter fun d => o d = none).card

/-- The number of discarded values on each side, `f - b`. -/
def discard (f : ℕ) (o : P → Option ℝ) : ℕ := f - numBot o

/-- Left end `a_v` of the retained interval `I_v`: the smallest value left after discarding the
`f - b` lowest values. -/
def lo (f : ℕ) (o : P → Option ℝ) : ℝ := orderStat (vals o) (discard f o)

/-- Right end `b_v` of the retained interval `I_v`: the largest value left after discarding the
`f - b` highest values. -/
def hi (f : ℕ) (o : P → Option ℝ) : ℝ :=
  orderStat (vals o) (card (vals o) - 1 - discard f o)

/-- The values retained by APA: the sorted non-`⊥` values without the `f - b` lowest and the
`f - b` highest ones. -/
def kept (f : ℕ) (o : P → Option ℝ) : Multiset ℝ :=
  ((((vals o).sort (· ≤ ·)).drop (discard f o)).take (card (vals o) - 2 * discard f o) : List ℝ)

/-- The interval `I_v = [a_v, b_v]` spanned by the retained values. -/
def interval (f : ℕ) (o : P → Option ℝ) : Set ℝ := Set.Icc (lo f o) (hi f o)

/-- The output of APA: the midpoint of the retained interval. -/
def apaOut (f : ℕ) (o : P → Option ℝ) : ℝ := (lo f o + hi f o) / 2

/-! ### Counting -/

theorem card_filterMap_filter_add (m : Multiset P) (o : P → Option ℝ) (p : ℝ → Prop)
    [DecidablePred p] :
    card ((m.filterMap o).filter p) + card (m.filter fun d => o d = none) =
      card (m.filter fun d => o d = none ∨ ∃ z, o d = some z ∧ p z) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rcases h : o a with _ | z
    · rw [filterMap_cons_none _ _ h]
      simp only [filter_cons, h, true_or, ↓reduceIte, card_add, card_singleton]
      omega
    · rw [filterMap_cons_some _ _ _ h]
      by_cases hz : p z
      · simp [h, hz]; omega
      · simp [h, hz]; omega

theorem card_filter_vals_add_numBot (o : P → Option ℝ) (p : ℝ → Prop) [DecidablePred p] :
    card ((vals o).filter p) + numBot o =
      (Finset.univ.filter fun d => o d = none ∨ ∃ z, o d = some z ∧ p z).card :=
  card_filterMap_filter_add _ o p

theorem card_vals_add_numBot (o : P → Option ℝ) : card (vals o) + numBot o = Fintype.card P := by
  have := card_filter_vals_add_numBot o (fun _ => True)
  rw [filter_true] at this
  rw [this, ← Finset.card_univ]
  congr 1
  ext d; rcases h : o d with _ | z <;> simp [h]

/-- If all `⊥` outputs and all non-`⊥` outputs satisfying `p` come from dealers in `F`, then
`#{values satisfying p} + b ≤ #F`. -/
theorem card_filter_vals_add_numBot_le (o : P → Option ℝ) (p : ℝ → Prop) [DecidablePred p]
    {F : Finset P} (hbot : ∀ d, o d = none → d ∈ F) (hp : ∀ d z, o d = some z → p z → d ∈ F) :
    card ((vals o).filter p) + numBot o ≤ F.card := by
  rw [card_filter_vals_add_numBot]
  refine Finset.card_le_card fun d hd => ?_
  rcases (Finset.mem_filter.1 hd).2 with h | ⟨z, h, hz⟩
  · exact hbot d h
  · exact hp d z h hz

/-! ### The retained values -/

/-- The retained values are exactly the order statistics between `f - b` and `#vals - 1 - (f - b)`;
in particular `lo` and `hi` are their minimum and maximum (`lo_mem_kept`, `mem_kept_bounds`). -/
theorem mem_kept {f : ℕ} {o : P → Option ℝ} (hd : 2 * discard f o < card (vals o)) {y : ℝ} :
    y ∈ kept f o ↔ ∃ j, discard f o ≤ j ∧ j ≤ card (vals o) - 1 - discard f o ∧
      orderStat (vals o) j = y := by
  have hl : ((vals o).sort (· ≤ ·)).length = card (vals o) := length_sort _
  simp only [kept, mem_coe, List.mem_iff_getElem, List.length_take, List.length_drop, hl,
    List.getElem_take, List.getElem_drop]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨discard f o + j, by omega, by omega, orderStat_eq (by omega)⟩
  · rintro ⟨j, hj1, hj2, rfl⟩
    exact ⟨j - discard f o, by omega, by rw [orderStat_eq (by omega)]; congr 1; omega⟩

theorem lo_mem_kept {f : ℕ} {o : P → Option ℝ} (hd : 2 * discard f o < card (vals o)) :
    lo f o ∈ kept f o :=
  (mem_kept hd).2 ⟨_, le_rfl, by omega, rfl⟩

theorem hi_mem_kept {f : ℕ} {o : P → Option ℝ} (hd : 2 * discard f o < card (vals o)) :
    hi f o ∈ kept f o :=
  (mem_kept hd).2 ⟨_, by omega, le_rfl, rfl⟩

theorem mem_kept_bounds {f : ℕ} {o : P → Option ℝ} (hd : 2 * discard f o < card (vals o)) {y : ℝ}
    (hy : y ∈ kept f o) : lo f o ≤ y ∧ y ≤ hi f o := by
  obtain ⟨j, h1, h2, rfl⟩ := (mem_kept hd).1 hy
  exact ⟨orderStat_mono h1 (by omega), orderStat_mono h2 (by omega)⟩

/-- At most `f` `⊥` outputs and `2f < n`: at least one value is retained. -/
theorem two_mul_discard_lt {f : ℕ} {o : P → Option ℝ} (hb : numBot o ≤ f)
    (hn : 2 * f < Fintype.card P) : 2 * discard f o < card (vals o) := by
  have := card_vals_add_numBot o
  unfold discard; omega

theorem lo_le_hi {f : ℕ} {o : P → Option ℝ} (hb : numBot o ≤ f) (hn : 2 * f < Fintype.card P) :
    lo f o ≤ hi f o := by
  have := two_mul_discard_lt hb hn
  exact orderStat_mono (by omega) (by omega)

/-! ### Lemma 7 -/

theorem filterMap_congr' {α β : Type*} {s : Multiset α} {g g' : α → Option β}
    (h : ∀ a ∈ s, g a = g' a) : s.filterMap g = s.filterMap g' := by
  induction s using Quot.inductionOn with
  | h l => exact congrArg ((↑) : List β → Multiset β) (List.filterMap_congr h)

theorem vals_update_of_eq_none {o : P → Option ℝ} {d : P} (hd : o d = none) (x : ℝ) :
    vals (Function.update o d (some x)) = x ::ₘ vals o := by
  have hu : (Finset.univ : Finset P).val = d ::ₘ (Finset.univ.erase d).val := by
    rw [Finset.erase_val, Multiset.cons_erase (Finset.mem_univ d)]
  have hcongr : (Finset.univ.erase d).val.filterMap (Function.update o d (some x)) =
      (Finset.univ.erase d).val.filterMap o :=
    filterMap_congr' fun a ha => by
      rw [Function.update_of_ne]
      rintro rfl; exact Finset.notMem_erase a _ ha
  simp only [vals]
  rw [hu, filterMap_cons_some (Function.update o d (some x)) d _ (b := x) (by simp),
    filterMap_cons_none _ _ hd, hcongr]

theorem numBot_update_of_eq_none {o : P → Option ℝ} {d : P} (hd : o d = none) (x : ℝ) :
    numBot (Function.update o d (some x)) + 1 = numBot o := by
  have h1 := card_vals_add_numBot o
  have h2 := card_vals_add_numBot (Function.update o d (some x))
  rw [vals_update_of_eq_none hd, card_cons] at h2
  omega

/-- **Lemma 7.** If node `v` received `⊥` from `d` (and at most `f < n` values `⊥` in total), then
the interval `Ĩ_v^x` it would retain if `⊥` were replaced by an arbitrary value `x` is contained in
the interval `I_v` it retains: `a_v ≤ ã_v` and `b̃_v ≤ b_v`. -/
theorem lemma_7 {f : ℕ} {o : P → Option ℝ} {d : P} (hd : o d = none) (hb : numBot o ≤ f)
    (hf : f < Fintype.card P) (x : ℝ) :
    lo f o ≤ lo f (Function.update o d (some x)) ∧
      hi f (Function.update o d (some x)) ≤ hi f o := by
  have hbot := numBot_update_of_eq_none hd x
  have hv := vals_update_of_eq_none hd x
  have hc := card_vals_add_numBot o
  set b := numBot o
  set m := card (vals o)
  have hdisc : discard f (Function.update o d (some x)) = discard f o + 1 := by
    unfold discard; omega
  have hdo : discard f o = f - b := rfl
  unfold lo hi
  rw [hdisc, hv, card_cons]
  constructor
  · exact orderStat_le_orderStat_cons_succ x (by omega)
  · rw [show m + 1 - 1 - (discard f o + 1) = m - 1 - discard f o by omega]
    exact orderStat_cons_le x (by omega)

/-- **Lemma 7**, set form: `Ĩ_v^x ⊆ I_v`. -/
theorem lemma_7_subset {f : ℕ} {o : P → Option ℝ} {d : P} (hd : o d = none) (hb : numBot o ≤ f)
    (hf : f < Fintype.card P) (x : ℝ) :
    interval f (Function.update o d (some x)) ⊆ interval f o :=
  Set.Icc_subset_Icc (lemma_7 hd hb hf x).1 (lemma_7 hd hb hf x).2

/-! ### Crusader broadcast outputs and Lemma 8 -/

/-- The outputs `o w d` (receiver `w`, dealer `d`) of `n` parallel crusader broadcast instances, in
which the dealers' inputs are `r`, satisfy the guarantees of Definition 6 for the honest nodes
(those not in `F`). -/
structure IsCrusader (F : Finset P) (r : P → ℝ) (o : P → P → Option ℝ) : Prop where
  /-- Validity: the instance of an honest dealer outputs its input at every honest node. -/
  validity : ∀ w, w ∉ F → ∀ d, d ∉ F → o w d = some (r d)
  /-- Crusader consistency: two honest nodes never output different non-`⊥` values. -/
  consistency : ∀ u, u ∉ F → ∀ w, w ∉ F → ∀ d a b, o u d = some a → o w d = some b → a = b

variable {F : Finset P} {r : P → ℝ} {o : P → P → Option ℝ} {f : ℕ}

/-- `⊥` is only output for faulty dealers, so an honest node sees at most `#F` values `⊥`. -/
theorem IsCrusader.mem_of_eq_none (h : IsCrusader F r o) {w d : P} (hw : w ∉ F)
    (hd : o w d = none) : d ∈ F := by
  by_contra hdF
  rw [h.validity w hw d hdF] at hd
  exact Option.some_ne_none _ hd

theorem IsCrusader.numBot_le (h : IsCrusader F r o) {w : P} (hw : w ∉ F) :
    numBot (o w) ≤ F.card := by
  have := card_filter_vals_add_numBot_le (o w) (fun _ => False) (F := F)
    (fun d hd => h.mem_of_eq_none hw hd) (fun _ _ _ h => h.elim)
  omega

/-- The total number `k` of `⊥` values received by honest nodes. -/
def totalBot (F : Finset P) (o : P → P → Option ℝ) : ℕ :=
  ∑ w ∈ Finset.univ.filter (· ∉ F), numBot (o w)

/-- **Lemma 8.** With at most `f` faulty nodes and `2f < n` (e.g. `f = ⌈n/2⌉ - 1`), the intervals
retained by the honest nodes have a common point. Proof by induction on the total number of `⊥`
values received by honest nodes, as in the paper. -/
theorem lemma_8 (hF : F.card ≤ f) (hn : 2 * f < Fintype.card P) (h : IsCrusader F r o) :
    ∃ x, ∀ w, w ∉ F → x ∈ interval f (o w) := by
  have hfn : f < Fintype.card P := by omega
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∉ F := by
    by_contra hall; push Not at hall
    have : (Finset.univ : Finset P) ⊆ F := fun p _ => hall p
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this; omega
  -- induction on `k = totalBot F o`, generalizing over the outputs `o` (inputs stay fixed)
  suffices ∀ k (o : P → P → Option ℝ), IsCrusader F r o → totalBot F o = k →
      ∃ x, ∀ w, w ∉ F → x ∈ interval f (o w) from this _ o h rfl
  intro k
  induction k with
  | zero =>
    -- base case: no `⊥` at honest nodes, so all honest nodes hold the same vector
    intro o h hk
    have hnb : ∀ w, w ∉ F → ∀ d, o w d ≠ none := by
      intro w hw d hd
      have hpos : 0 < numBot (o w) :=
        Finset.card_pos.2 ⟨d, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩⟩
      have : numBot (o w) ≤ totalBot F o :=
        Finset.single_le_sum (f := fun w => numBot (o w)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
      omega
    have heq : ∀ w, w ∉ F → o w = o w₀ := by
      intro w hw; funext d
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hnb w hw d)
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (hnb w₀ hw₀ d)
      rw [ha, hb, h.consistency w hw w₀ hw₀ d a b ha hb]
    refine ⟨lo f (o w₀), fun w hw => ?_⟩
    rw [heq w hw]
    exact ⟨le_rfl, lo_le_hi ((h.numBot_le hw₀).trans hF) hn⟩
  | succ k ih =>
    intro o h hk
    -- some honest `w` received `⊥` from some (faulty) dealer `d`
    obtain ⟨w, hw, hpos⟩ : ∃ w, w ∉ F ∧ 0 < numBot (o w) := by
      by_contra hall; push Not at hall
      have : totalBot F o = 0 := Finset.sum_eq_zero fun w hw =>
        Nat.le_zero.1 (hall w (Finset.mem_filter.1 hw).2)
      omega
    obtain ⟨d, hd⟩ := Finset.card_pos.1 hpos
    have hd : o w d = none := (Finset.mem_filter.1 hd).2
    -- replace this `⊥` by the value the other honest nodes received from `d` (if any)
    classical
    let c : ℝ := if hc : ∃ u, u ∉ F ∧ ∃ a, o u d = some a then hc.choose_spec.2.choose else 0
    have hc : ∀ u, u ∉ F → ∀ a, o u d = some a → a = c := by
      intro u hu a ha
      have hex : ∃ u, u ∉ F ∧ ∃ a, o u d = some a := ⟨u, hu, a, ha⟩
      simp only [c, hex, ↓reduceDIte]
      exact h.consistency u hu _ hex.choose_spec.1 d a _ ha hex.choose_spec.2.choose_spec
    let o' : P → P → Option ℝ := Function.update o w (Function.update (o w) d (some c))
    have ho'w : o' w = Function.update (o w) d (some c) := by simp [o']
    have ho'v : ∀ v, v ≠ w → o' v = o v := fun v hv => by simp [o', hv]
    have hdF : d ∈ F := h.mem_of_eq_none hw hd
    -- the modified outputs still satisfy validity and crusader consistency
    have h' : IsCrusader F r o' := by
      constructor
      · intro v hv e he
        by_cases hvw : v = w
        · subst hvw; rw [ho'w, Function.update_of_ne (by rintro rfl; exact he hdF)]
          exact h.validity v hv e he
        · rw [ho'v v hvw]; exact h.validity v hv e he
      · have key : ∀ v, v ∉ F → ∀ e a, o' v e = some a → o v e = some a ∨ (e = d ∧ a = c) := by
          intro v hv e a hva
          by_cases hvw : v = w
          · subst hvw; rw [ho'w] at hva
            by_cases hed : e = d
            · subst hed; simp at hva; exact Or.inr ⟨rfl, hva.symm⟩
            · rw [Function.update_of_ne hed] at hva; exact Or.inl hva
          · rw [ho'v v hvw] at hva; exact Or.inl hva
        intro u hu v hv e a b hua hvb
        rcases key u hu e a hua with hua | ⟨rfl, rfl⟩ <;>
          rcases key v hv e b hvb with hvb | ⟨he, rfl⟩
        · exact h.consistency u hu v hv e a b hua hvb
        · rw [he] at hua; exact hc u hu a hua
        · exact (hc v hv b hvb).symm
        · rfl
    -- it has one `⊥` less
    have hk' : totalBot F o' = k := by
      have hsplit : ∀ g : P → P → Option ℝ, totalBot F g =
          numBot (g w) + ∑ v ∈ (Finset.univ.filter (· ∉ F)).erase w, numBot (g v) := by
        intro g
        exact (Finset.add_sum_erase (Finset.univ.filter (· ∉ F)) (fun v => numBot (g v))
          (Finset.mem_filter.2 ⟨Finset.mem_univ w, hw⟩)).symm
      have hrest : ∑ v ∈ (Finset.univ.filter (· ∉ F)).erase w, numBot (o' v) =
          ∑ v ∈ (Finset.univ.filter (· ∉ F)).erase w, numBot (o v) :=
        Finset.sum_congr rfl fun v hv => by rw [ho'v v (Finset.ne_of_mem_erase hv)]
      have h1 := hsplit o
      have h2 := hsplit o'
      have h3 := numBot_update_of_eq_none hd c
      rw [ho'w] at h2
      omega
    obtain ⟨x, hx⟩ := ih o' h' hk'
    refine ⟨x, fun v hv => ?_⟩
    by_cases hvw : v = w
    · subst hvw
      have := hx v hv
      rw [ho'w] at this
      exact lemma_7_subset hd ((h.numBot_le hv).trans hF) hfn c this
    · have := hx v hv; rwa [ho'v v hvw] at this

/-! ### Theorem 9 -/

/-- Validity part of Theorem 9: if the honest inputs lie in `[a, b]`, then the interval retained by
an honest node lies in `[a, b]` (at most `f - b_v` of its values come from faulty dealers). -/
theorem interval_subset (hF : F.card ≤ f) (hn : 2 * f < Fintype.card P) (h : IsCrusader F r o)
    {a b : ℝ} (hab : ∀ p, p ∉ F → r p ∈ Set.Icc a b) {w : P} (hw : w ∉ F) :
    a ≤ lo f (o w) ∧ hi f (o w) ≤ b := by
  have hb := (h.numBot_le hw).trans hF
  have h2 := two_mul_discard_lt hb hn
  have hfaulty : ∀ (p : ℝ → Prop), (∀ z, p z → z ∉ Set.Icc a b) → ∀ d z, o w d = some z → p z →
      d ∈ F := by
    intro p hp d z hz hpz
    by_contra hdF
    rw [h.validity w hw d hdF] at hz
    cases hz
    exact hp _ hpz (hab d hdF)
  have hc := card_vals_add_numBot (o w)
  constructor
  · refine (le_orderStat_iff (by omega)).2 ?_
    have := card_filter_vals_add_numBot_le (o w) (· < a) (fun d hd => h.mem_of_eq_none hw hd)
      (hfaulty _ fun z hz hz' => (not_le.2 hz) hz'.1)
    unfold discard; omega
  · refine (orderStat_le_iff (by omega)).2 ?_
    have := card_filter_vals_add_numBot_le (o w) (b < ·) (fun d hd => h.mem_of_eq_none hw hd)
      (hfaulty _ fun z hz hz' => (not_le.2 hz) hz'.2)
    have hsplit := Multiset.filter_add_not (· ≤ b) (vals (o w))
    have hne : (vals (o w)).filter (fun z => ¬ z ≤ b) = (vals (o w)).filter (b < ·) :=
      Multiset.filter_congr fun z _ => not_le
    rw [hne] at hsplit
    have := congrArg card hsplit
    rw [card_add] at this
    unfold discard; omega

/-- **Theorem 9**, step form. With at most `f` faulty nodes, `2f < n` and crusader broadcast
outputs, if the honest inputs lie in `[a, b]` then every honest output of APA lies in `[a, b]` and
any two honest outputs differ by at most `(b - a)/2`. -/
theorem apa_step (hF : F.card ≤ f) (hn : 2 * f < Fintype.card P) (h : IsCrusader F r o)
    {a b : ℝ} (hab : ∀ p, p ∉ F → r p ∈ Set.Icc a b) :
    (∀ w, w ∉ F → apaOut f (o w) ∈ Set.Icc a b) ∧
      ∀ v, v ∉ F → ∀ w, w ∉ F → apaOut f (o v) - apaOut f (o w) ≤ (b - a) / 2 := by
  obtain ⟨x, hx⟩ := lemma_8 hF hn h
  constructor
  · intro w hw
    obtain ⟨h1, h2⟩ := interval_subset hF hn h hab hw
    have := lo_le_hi ((h.numBot_le hw).trans hF) hn
    unfold apaOut; constructor <;> linarith
  · intro v hv w hw
    obtain ⟨h1, h2⟩ := interval_subset hF hn h hab hv
    obtain ⟨h3, h4⟩ := interval_subset hF hn h hab hw
    obtain ⟨h5, h6⟩ := hx v hv
    obtain ⟨h7, h8⟩ := hx w hw
    unfold apaOut; linarith

/-- **Theorem 9** (core, abstract form). If the honest inputs have range at most `ℓ`, then every
honest output of APA lies between the smallest and the largest honest input (validity), and any two
honest outputs are at most `ℓ/2` apart (`ℓ/2`-consistency). -/
theorem theorem_9_core (hF : F.card ≤ f) (hn : 2 * f < Fintype.card P) (h : IsCrusader F r o)
    {ℓ : ℝ} (hℓ : ∀ p, p ∉ F → ∀ q, q ∉ F → r p - r q ≤ ℓ) :
    (∀ w, w ∉ F → (∃ p, p ∉ F ∧ r p ≤ apaOut f (o w)) ∧ ∃ q, q ∉ F ∧ apaOut f (o w) ≤ r q) ∧
      ∀ v, v ∉ F → ∀ w, w ∉ F → |apaOut f (o v) - apaOut f (o w)| ≤ ℓ / 2 := by
  have hne : (Finset.univ.filter (· ∉ F)).Nonempty := by
    by_contra hall
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hall
    have : (Finset.univ : Finset P) ⊆ F := fun p _ => by simpa using hall (Finset.mem_univ p)
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this; omega
  obtain ⟨pmin, hpmin, hmin⟩ := Finset.exists_min_image _ r hne
  obtain ⟨pmax, hpmax, hmax⟩ := Finset.exists_max_image _ r hne
  have hpmin' : pmin ∉ F := (Finset.mem_filter.1 hpmin).2
  have hpmax' : pmax ∉ F := (Finset.mem_filter.1 hpmax).2
  have hab : ∀ p, p ∉ F → r p ∈ Set.Icc (r pmin) (r pmax) := fun p hp =>
    ⟨hmin p (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩),
      hmax p (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)⟩
  obtain ⟨h1, h2⟩ := apa_step hF hn h hab
  have hℓ' := hℓ pmax hpmax' pmin hpmin'
  refine ⟨fun w hw => ⟨⟨pmin, hpmin', (h1 w hw).1⟩, pmax, hpmax', (h1 w hw).2⟩, fun v hv w hw => ?_⟩
  rw [abs_le]
  constructor
  · have := h2 w hw v hv; linarith
  · have := h2 v hv w hw; linarith

end Podc.ClockSyncSignatures

end
