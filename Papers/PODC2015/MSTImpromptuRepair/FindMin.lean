import Papers.PODC2015.MSTImpromptuRepair.Cut
import Cslib.Foundations.Data.Nat.CeilDiv

/-!
# `FindMin`: `w`-ary search for the lightest leaving edge (Section 3.1, Lemma 2)

Weights are distinct, so the search is over the set `L : Finset ℕ` of weights of the edges leaving
`T` (`cutWeights`). One iteration of steps 4–7 from the range `(j, k)`:

* step 5: the `w` subranges `[j_i, k_i]`, `j_i = j + i ⌈(k-j)/w⌉`, `k_i = j + (i+1) ⌈(k-j)/w⌉ - 1`,
  are tested by `TestOut` (answers `ans i`, **one-sided**: `true` only if the subrange contains
  a leaving edge, `OneSided`);
* step 6: `min` = the first subrange answering 1; `TestLow = HP-TestOut(0, j_min - 1)`,
  `TestInterval = HP-TestOut(j_min, k_min)`, modelled as **exact** (the w.h.p. event);
* step 7: (a) `TestLow = 0 ∧ TestInterval = 1`: if `j_min < k_min` narrow to
  `(j_min, k_min + 1)`, else return `j_min`; (b) both `0`: return `∅`; otherwise repeat.
  When no subrange answers 1 (the paper does not say what happens) we repeat.

`run` iterates at most `fuel` times (the paper's `Count` bound) and returns `∅` when it runs out.

* `run_sound` — whatever the `TestOut` answers, a returned weight is the minimum of `L` (given exact
  `HP-TestOut`s); `run_none_of_empty` — with no leaving edge the result is `∅`.
* `iter_of_inv` / `run_of_inv` — if the lightest leaving weight `m` lies in `[j, k)` and `TestOut`
  answers 1 on the subrange containing `m` in every iteration, `run` returns `m` within
  `⌈log_w (k - j)⌉ + 1` iterations (the range shrinks to `⌈(k - j)/w⌉`).
* `findMinFixed_correct` — hence `FindMin` started at `(1, maxWt + 1)` finds the lightest edge.
* `run_none_of_max` / `findMin_paper_misses` — **the paper's initialisation `k ← maxWt(T_x)` is off
  by one**: the subranges cover only `[j, j + w⌈(k-j)/w⌉ - 1]`, which misses `k` when `w ∣ k - j`;
  if the lightest leaving edge is the heaviest edge at `T` (e.g. `T = {u}` for a node `u` whose
  only incident edge has weight `1`), `FindMin` returns `∅` for *all* `TestOut` outcomes.
  `p3_counterexample` instantiates this on the path `0 - 1 - 2`.
-/

namespace Podc.MSTImpromptuRepair.FindMin

open Finset

variable (w : ℕ) (L : Finset ℕ)

/-- `⌈(k - j)/w⌉`, the length of the subranges. -/
def width (j k : ℕ) : ℕ := (k - j) ⌈/⌉ w

/-- `j_i = j + i ⌈(k - j)/w⌉`. -/
def lo (j k i : ℕ) : ℕ := j + i * width w j k

/-- `k_i = j + (i + 1) ⌈(k - j)/w⌉ - 1`. -/
def hi (j k i : ℕ) : ℕ := j + (i + 1) * width w j k - 1

/-- The `TestOut` answers are one-sided: `ans i = true` only if a leaving edge has its weight in
the `i`-th subrange. -/
def OneSided (j k : ℕ) (ans : ℕ → Bool) : Prop :=
  ∀ i < w, ans i = true → ∃ x ∈ L, lo w j k i ≤ x ∧ x ≤ hi w j k i

/-- Outcome of one iteration of steps 4–7. -/
inductive Outcome
  | narrow (j k : ℕ)
  | found (v : ℕ)
  | empty
  | retry
  deriving DecidableEq

/-- Step 7 for the subrange `[a, b] = [j_min, k_min]`, with exact `HP-TestOut`s
`TestLow ↔ ∃ x ∈ L, x < a` and `TestInterval ↔ ∃ x ∈ L, x ∈ [a, b]`. -/
def step7 (a b : ℕ) : Outcome :=
  if ¬ (∃ x ∈ L, x < a) ∧ (∃ x ∈ L, a ≤ x ∧ x ≤ b) then
    (if a < b then .narrow a (b + 1) else .found a)
  else if ¬ (∃ x ∈ L, x < a) ∧ ¬ (∃ x ∈ L, a ≤ x ∧ x ≤ b) then .empty
  else .retry

/-- One iteration of steps 4–7 from the range `(j, k)` with `TestOut` answers `ans`, and exact
`HP-TestOut`s: `TestLow ↔ ∃ x ∈ L, x < j_min` (i.e. `x ∈ [0, j_min - 1]`) and
`TestInterval ↔ ∃ x ∈ L, x ∈ [j_min, k_min]`. -/
def iter (j k : ℕ) (ans : ℕ → Bool) : Outcome :=
  if h : ((range w).filter fun i => ans i = true).Nonempty then
    step7 L (lo w j k (((range w).filter fun i => ans i = true).min' h))
      (hi w j k (((range w).filter fun i => ans i = true).min' h))
  else .retry

/-- Iterate at most `fuel` times (`Count`); `ans t` are the `TestOut` answers of iteration `t`,
which may depend on the current range. -/
def run : ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → Bool) → Option ℕ
  | 0, _, _, _ => none
  | n + 1, j, k, ans =>
    match iter w L j k (ans 0 j k) with
    | .narrow j' k' => run n j' k' (fun t => ans (t + 1))
    | .found v => some v
    | .empty => none
    | .retry => run n j k (fun t => ans (t + 1))

/-- `m` is the lightest leaving weight. -/
def IsMin (m : ℕ) : Prop := m ∈ L ∧ ∀ x ∈ L, m ≤ x

variable {w L}

theorem iter_found {j k : ℕ} {ans : ℕ → Bool} {v : ℕ} (h : iter w L j k ans = .found v) :
    IsMin L v := by
  unfold iter at h
  split_ifs at h with h1
  unfold step7 at h
  split_ifs at h with h2 h3 h4
  simp only [Outcome.found.injEq] at h
  subst h
  obtain ⟨hlow, x, hx, hax, hxb⟩ := h2
  refine ⟨?_, fun y hy => ?_⟩
  · have : x = lo w j k (((range w).filter fun i => ans i = true).min' h1) := by omega
    exact this ▸ hx
  · by_contra hlt; exact hlow ⟨y, hy, by omega⟩

/-- **Soundness of `FindMin`**: whatever the `TestOut` answers, a returned weight is the minimum
weight of a leaving edge (assuming the `HP-TestOut`s are correct). -/
theorem run_sound {n j k : ℕ} {ans : ℕ → ℕ → ℕ → ℕ → Bool} {v : ℕ}
    (h : run w L n j k ans = some v) : IsMin L v := by
  induction n generalizing j k ans with
  | zero => simp [run] at h
  | succ n ih =>
    unfold run at h
    split at h
    · exact ih h
    · rename_i hv; simp only [Option.some.injEq] at h; subst h; exact iter_found hv
    · simp at h
    · exact ih h

/-- If no edge leaves `T`, `FindMin` returns `∅`. -/
theorem run_none_of_empty {n j k : ℕ} {ans : ℕ → ℕ → ℕ → ℕ → Bool} (hL : L = ∅) :
    run w L n j k ans = none := by
  cases h : run w L n j k ans with
  | none => rfl
  | some v => exact absurd (run_sound h).1 (by simp [hL])

variable (L) in
/-- The invariant: the lightest leaving weight `m` lies in `[j, k)`. -/
def Inv (m j k : ℕ) : Prop := IsMin L m ∧ j ≤ m ∧ m < k

variable (w) in
/-- The index of the subrange containing `m`. -/
def idx (j k m : ℕ) : ℕ := (m - j) / width w j k

theorem width_pos {j k : ℕ} (hjk : j < k) (hw : 0 < w) : 0 < width w j k := by
  unfold width
  have := Nat.le_mul_ceilDiv (a := k - j) hw
  rcases Nat.eq_zero_or_pos ((k - j) ⌈/⌉ w) with h | h
  · rw [h] at this; omega
  · exact h

theorem idx_spec {j k m : ℕ} (hw : 0 < w) (hj : j ≤ m) (hk : m < k) :
    idx w j k m < w ∧ lo w j k (idx w j k m) ≤ m ∧ m ≤ hi w j k (idx w j k m) := by
  have hd := width_pos (w := w) (lt_of_le_of_lt hj hk) hw
  have hcov : k - j ≤ w * width w j k := Nat.le_mul_ceilDiv hw
  have h1 := Nat.div_mul_le_self (m - j) (width w j k)
  have h2 := Nat.lt_div_mul_add (a := m - j) hd
  simp only [idx, lo, hi]
  refine ⟨?_, by omega, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hd]
    have : w * width w j k = width w j k * w := Nat.mul_comm _ _
    omega
  · rw [Nat.add_mul, one_mul]; omega

/-- **One iteration under the invariant.** If `m ∈ [j, k)` is the lightest leaving weight and the
`TestOut` answers are one-sided, the iteration narrows to a range that still contains `m` (of
length `⌈(k - j)/w⌉`), returns `m`, or repeats; it repeats only if `TestOut` missed the subrange
containing `m`. -/
theorem iter_of_inv (hw : 0 < w) {m j k : ℕ} (hinv : Inv L m j k) {ans : ℕ → Bool}
    (hos : OneSided w L j k ans) :
    (iter w L j k ans = .found m) ∨
      (∃ j' k', iter w L j k ans = .narrow j' k' ∧ Inv L m j' k' ∧ k' - j' = width w j k ∧
        2 ≤ k' - j') ∨
      (iter w L j k ans = .retry ∧ ans (idx w j k m) = false) := by
  obtain ⟨⟨hmL, hmin⟩, hjm, hmk⟩ := hinv
  obtain ⟨hidx, hlo, hhi⟩ := idx_spec hw hjm hmk
  have hd := width_pos (w := w) (lt_of_le_of_lt hjm hmk) hw
  -- subranges are ordered
  have hord : ∀ a b, a < b → hi w j k a < lo w j k b := by
    intro a b hab
    unfold hi lo
    have h1 : (a + 1) * width w j k ≤ b * width w j k := Nat.mul_le_mul_right _ hab
    have h2 : width w j k ≤ (a + 1) * width w j k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  by_cases hans : ans (idx w j k m) = true
  · -- the first positive subrange is the one containing `m`
    have hne : ((range w).filter fun i => ans i = true).Nonempty :=
      ⟨idx w j k m, by simp [hidx, hans]⟩
    have hile : ((range w).filter fun i => ans i = true).min' hne ≤ idx w j k m :=
      min'_le _ _ (by simp [hidx, hans])
    have hieq : ((range w).filter fun i => ans i = true).min' hne = idx w j k m := by
      by_contra hneq
      have hlt := lt_of_le_of_ne hile hneq
      have hmem := min'_mem _ hne
      rw [mem_filter, mem_range] at hmem
      obtain ⟨x, hx, -, hxb⟩ := hos _ hmem.1 hmem.2
      have := hord _ _ hlt
      have := hmin x hx
      omega
    have hlow : ¬ ∃ x ∈ L, x < lo w j k (idx w j k m) := by
      rintro ⟨x, hx, hxa⟩; have := hmin x hx; omega
    have hint : ∃ x ∈ L, lo w j k (idx w j k m) ≤ x ∧ x ≤ hi w j k (idx w j k m) :=
      ⟨m, hmL, hlo, hhi⟩
    unfold iter
    rw [dif_pos hne, hieq]
    unfold step7
    rw [if_pos ⟨hlow, hint⟩]
    split_ifs with hab
    · right; left
      refine ⟨_, _, rfl, ⟨⟨hmL, hmin⟩, hlo, by omega⟩, ?_, by omega⟩
      unfold hi lo; rw [Nat.add_mul, one_mul]; omega
    · left
      congr 1
      omega
  · right; right
    refine ⟨?_, by simpa using hans⟩
    unfold iter
    split_ifs with hne
    · have hmem := min'_mem _ hne
      rw [mem_filter, mem_range] at hmem
      obtain ⟨y, hy, hya, hyb⟩ := hos _ hmem.1 hmem.2
      have hlow : ∃ x ∈ L, x < lo w j k (((range w).filter fun i => ans i = true).min' hne) := by
        rcases lt_trichotomy (((range w).filter fun i => ans i = true).min' hne)
          (idx w j k m) with hlt | heq | hgt
        · exfalso; have := hord _ _ hlt; have := hmin y hy; omega
        · exfalso; rw [heq] at hmem; simp [hans] at hmem
        · have := hord _ _ hgt
          exact ⟨m, hmL, by omega⟩
      unfold step7
      rw [if_neg (fun h => h.1 hlow), if_neg (fun h => h.1 hlow)]
    · rfl

variable (w L) in
/-- `TestOut` succeeds on the subrange containing the lightest leaving weight in every iteration
from a range satisfying the invariant (the event whose probability the paper bounds with Chernoff;
a single `TestOut` succeeds with probability `≥ q = 1/8`). -/
def GoodAnswers (m : ℕ) (ans : ℕ → ℕ → ℕ → ℕ → Bool) : Prop :=
  ∀ t j k, Inv L m j k → ans t j k (idx w j k m) = true

variable (w L) in
/-- All `TestOut` answers are one-sided. -/
def AllOneSided (ans : ℕ → ℕ → ℕ → ℕ → Bool) : Prop := ∀ t j k, OneSided w L j k (ans t j k)

/-- **Correctness of the search (deterministic part of Lemma 2).** If `m ∈ [j, k)` is the lightest
leaving weight, `k - j ≤ w^n`, all `TestOut` answers are one-sided and `TestOut` never misses
the subrange containing `m`, then `n + 1` iterations return `m`. -/
theorem run_of_inv (hw : 1 < w) {m : ℕ} :
    ∀ n (ans : ℕ → ℕ → ℕ → ℕ → Bool), AllOneSided w L ans → GoodAnswers w L m ans →
      ∀ j k, Inv L m j k → k - j ≤ w ^ n → run w L (n + 1) j k ans = some m := by
  intro n
  induction n with
  | zero =>
    intro ans hos hgood j k hinv hjk
    rcases iter_of_inv (by omega) hinv (hos 0 j k) with h | ⟨j', k', h, hinv', hlen, h2⟩ | ⟨-, h⟩
    · simp [run, h]
    · exfalso
      have : width w j k = 1 := by
        unfold width
        have : k - j = 1 := by
          rw [pow_zero] at hjk; have := hinv.2.1; have := hinv.2.2; omega
        rw [this, Nat.ceilDiv_eq_add_pred_div, show 1 + w - 1 = w by omega, Nat.div_self (by omega)]
      omega
    · exact absurd (hgood 0 j k hinv) (by simp [h])
  | succ n ih =>
    intro ans hos hgood j k hinv hjk
    rcases iter_of_inv (by omega) hinv (hos 0 j k) with h | ⟨j', k', h, hinv', hlen, -⟩ | ⟨-, h⟩
    · simp [run, h]
    · simp only [run, h]
      refine ih (fun t => ans (t + 1)) ?_ ?_ j' k' ?_ ?_
      · exact fun t => hos (t + 1)
      · exact fun t => hgood (t + 1)
      · exact hinv'
      · rw [hlen]; unfold width
        exact Nat.ceilDiv_le_of_le_mul (by omega) (by rw [pow_succ'] at hjk; exact hjk)
    · exact absurd (hgood 0 j k hinv) (by simp [h])

/-- **`FindMin` with the corrected initial range `(1, maxWt + 1)`**: if all leaving weights lie in
`[1, maxWt]` and `maxWt ≤ w^n`, `TestOut` answers are one-sided and never miss, then `n + 1`
iterations return the lightest leaving weight. -/
theorem findMinFixed_correct (hw : 1 < w) {maxWt n : ℕ} (hL : ∀ x ∈ L, 1 ≤ x ∧ x ≤ maxWt)
    (hmax : maxWt ≤ w ^ n) {m : ℕ} (hm : IsMin L m) {ans : ℕ → ℕ → ℕ → ℕ → Bool}
    (hos : AllOneSided w L ans) (hgood : GoodAnswers w L m ans) :
    run w L (n + 1) 1 (maxWt + 1) ans = some m :=
  run_of_inv hw n ans hos hgood 1 (maxWt + 1)
    ⟨hm, (hL m hm.1).1, by have := (hL m hm.1).2; omega⟩ (by omega)

/-- **The paper's initial range misses its upper end.** If every leaving weight is `≥ k` and
`w ∣ k - j`, the `w` subranges of every iteration lie below `k`, so (with one-sided `TestOut`s)
no subrange ever answers 1 and `FindMin` returns `∅` — for every number of iterations. -/
theorem run_none_of_max (hw : 0 < w) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (hL : ∀ x ∈ L, k ≤ x)
    (hdvd : w ∣ k - j)
    {ans : ℕ → ℕ → ℕ → ℕ → Bool} (hos : AllOneSided w L ans) :
    ∀ n, run w L n j k ans = none := by
  intro n
  induction n generalizing ans with
  | zero => rfl
  | succ n ih =>
    have hfalse : ∀ i < w, ans 0 j k i = false := by
      intro i hiw
      by_contra h
      obtain ⟨x, hx, -, hxb⟩ := hos 0 j k i hiw (by simpa using h)
      have hkx := hL x hx
      have : hi w j k i ≤ k - 1 := by
        unfold hi width
        obtain ⟨c, hc⟩ := hdvd
        have hcd : (k - j) ⌈/⌉ w = c := by
          rw [hc, Nat.ceilDiv_eq_add_pred_div, Nat.mul_comm]
          rw [show c * w + w - 1 = (w - 1) + c * w by omega, Nat.add_mul_div_right _ _ hw,
            Nat.div_eq_of_lt (by omega), zero_add]
        rw [hcd]
        have : (i + 1) * c ≤ w * c := Nat.mul_le_mul_right _ (by omega)
        omega
      omega
    have hit : iter w L j k (ans 0 j k) = .retry := by
      unfold iter
      rw [dif_neg]
      rintro ⟨i, hi⟩
      simp only [mem_filter, mem_range] at hi
      exact absurd (hfalse i hi.1) (by simp [hi.2])
    simp only [run, hit]
    exact ih (fun t => hos (t + 1))

/-- `FindMin` as written in the paper: start from `j = 1`, `k = maxWt(T_x)`. If the lightest
leaving edge is the heaviest edge at `T_x` and `w ∣ maxWt - 1` (e.g. `maxWt = 1`), `FindMin`
returns `∅` although an edge leaves `T_x`. -/
theorem findMin_paper_misses (hw : 0 < w) {maxWt : ℕ} (h1 : 1 ≤ maxWt) (hL : ∀ x ∈ L, maxWt ≤ x)
    (hdvd : w ∣ maxWt - 1) {ans : ℕ → ℕ → ℕ → ℕ → Bool} (hos : AllOneSided w L ans) (n : ℕ) :
    run w L n 1 maxWt ans = none :=
  run_none_of_max hw le_rfl h1 hL hdvd hos n

/-! ### A concrete instance: the path `0 - 1 - 2` -/

/-- The path `0 - 1 - 2`. -/
def p3 : SimpleGraph (Fin 3) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance : DecidableRel p3.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)))

/-- Distinct weights: `w({0,1}) = 1`, `w({1,2}) = 3` (the sum of the endpoints). -/
def p3wt : Sym2 (Fin 3) → ℕ :=
  Sym2.lift ⟨fun u v => u.val + v.val, fun _ _ => Nat.add_comm _ _⟩

/-- `maxWt(T)`: the maximum weight of an edge incident to a node of `T`. -/
def maxWt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (wt : Sym2 V → ℕ) (T : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => ∃ v ∈ T, v ∈ e).sup wt

/-- The weights of the edges leaving `T`. -/
def cutWeights {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (wt : Sym2 V → ℕ) (T : Finset V) : Finset ℕ :=
  (cut G T).image wt

/-- On the path `0 - 1 - 2` with `T = {0}` (a singleton fragment, as in the first phase of
`Build MST`), the leaving edge `{0, 1}` has weight `1 = maxWt(T)`, and `FindMin` as written returns
`∅` for every word size `w`, every number of iterations and all one-sided `TestOut` answers. -/
theorem p3_counterexample (hw : 0 < w) {ans : ℕ → ℕ → ℕ → ℕ → Bool}
    (hos : AllOneSided w (cutWeights p3 p3wt {0}) ans) (n : ℕ) :
    cutWeights p3 p3wt {0} = {1} ∧ maxWt p3 p3wt {0} = 1 ∧
      run w (cutWeights p3 p3wt {0}) n 1 (maxWt p3 p3wt {0}) ans = none := by
  have hc : cutWeights p3 p3wt {0} = {1} := by decide
  have hm : maxWt p3 p3wt {0} = 1 := by decide
  refine ⟨hc, hm, ?_⟩
  rw [hm]
  exact findMin_paper_misses hw le_rfl (by rw [hc]; simp) (by simp) hos n

end Podc.MSTImpromptuRepair.FindMin
