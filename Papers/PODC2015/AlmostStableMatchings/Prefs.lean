import Mathlib

/-!
# Incomplete preferences, blocking pairs and almost stability

Ostrovsky, Rosenbaum, *Fast Distributed Almost Stable Matchings*, PODC 2015 (arXiv 1408.2782v2),
Section 2.1.

* `Prefs M W`: men `M`, women `W`; every player has a preference list (a duplicate-free `List`) of
  acceptable partners; preferences are symmetric (`w` is on `m`'s list iff `m` is on `w`'s list).
* `rankM`, `rankW` (`P^v(u)`, `1` = favourite), `degM`, `degW`, the communication graph `E`.
* A (partial) matching is given by partner functions `pm : M → Option W`, `pw : W → Option M`.
  `IsBlocking`, `blockingPairs`, `IsAlmostStable` (Definition 2.1), `IsEpsBlocking` (Definition 2.3,
  with the convention `P^v(∅) = deg v + 1` of the proof of Lemma 4.3).
* `quant k d r = ⌈k r / d⌉`: the quantile (`1..k`) of the item of rank `r` in a list of length `d`
  split into `k` quantiles of (almost) equal size.
* `lemma_4_3`: at most `4|E|/k` blocking pairs are not `(2/k)`-blocking (for any partner functions).
-/

-- CSLib candidate: incomplete preferences / blocking pairs (`Cslib/Algorithms/Lean/StableMatching/`).

set_option linter.unusedSectionVars false

namespace Papers.PODC2015.AlmostStableMatchings

open Finset

/-- Symmetric incomplete preferences: `man m` is `m`'s preference list (favourite first), `woman w`
is `w`'s list; `w` appears in `man m` iff `m` appears in `woman w`. -/
structure Prefs (M W : Type*) where
  /-- Preference list of a man. -/
  man : M → List W
  /-- Preference list of a woman. -/
  woman : W → List M
  nodup_man : ∀ m, (man m).Nodup
  nodup_woman : ∀ w, (woman w).Nodup
  mem_iff : ∀ m w, w ∈ man m ↔ m ∈ woman w

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

namespace Prefs

variable (P : Prefs M W)

/-- `P^m(w)`: the rank of `w` in `m`'s list (`1` = favourite). -/
def rankM (m : M) (w : W) : ℕ := (P.man m).idxOf w + 1

/-- `P^w(m)`: the rank of `m` in `w`'s list. -/
def rankW (w : W) (m : M) : ℕ := (P.woman w).idxOf m + 1

/-- Degree of a man (length of his list). -/
def degM (m : M) : ℕ := (P.man m).length

/-- Degree of a woman. -/
def degW (w : W) : ℕ := (P.woman w).length

/-- Acceptable partners of a man. -/
def NM (m : M) : Finset W := (P.man m).toFinset

/-- Acceptable partners of a woman. -/
def NW (w : W) : Finset M := (P.woman w).toFinset

/-- The communication graph: pairs of mutually acceptable players. -/
def E : Finset (M × W) := Finset.univ.filter fun e => e.2 ∈ P.man e.1

/-- Rank of a (possible) partner, with `P^m(∅) = deg m + 1`. -/
def rankOptM (m : M) : Option W → ℕ
  | none => P.degM m + 1
  | some w => P.rankM m w

/-- Rank of a (possible) partner, with `P^w(∅) = deg w + 1`. -/
def rankOptW (w : W) : Option M → ℕ
  | none => P.degW w + 1
  | some m => P.rankW w m

@[simp] lemma mem_NM {m : M} {w : W} : w ∈ P.NM m ↔ w ∈ P.man m := List.mem_toFinset
@[simp] lemma mem_NW {m : M} {w : W} : m ∈ P.NW w ↔ m ∈ P.woman w := List.mem_toFinset

lemma mem_NM_iff_mem_NW {m : M} {w : W} : w ∈ P.NM m ↔ m ∈ P.NW w := by
  simp [P.mem_iff]

@[simp] lemma mem_E {e : M × W} : e ∈ P.E ↔ e.2 ∈ P.man e.1 := by simp [E]

lemma card_NM (m : M) : (P.NM m).card = P.degM m :=
  List.toFinset_card_of_nodup (P.nodup_man m)

lemma card_NW (w : W) : (P.NW w).card = P.degW w :=
  List.toFinset_card_of_nodup (P.nodup_woman w)

lemma one_le_rankM (m : M) (w : W) : 1 ≤ P.rankM m w := Nat.le_add_left _ _
lemma one_le_rankW (w : W) (m : M) : 1 ≤ P.rankW w m := Nat.le_add_left _ _

lemma rankM_le {m : M} {w : W} (h : w ∈ P.man m) : P.rankM m w ≤ P.degM m :=
  List.idxOf_lt_length_of_mem h

lemma rankW_le {m : M} {w : W} (h : m ∈ P.woman w) : P.rankW w m ≤ P.degW w :=
  List.idxOf_lt_length_of_mem h

lemma rankM_inj {m : M} {w w' : W} (h : w ∈ P.man m) (h' : w' ∈ P.man m)
    (e : P.rankM m w = P.rankM m w') : w = w' :=
  (List.idxOf_inj h).1 (by simpa [rankM] using e)

lemma rankW_inj {w : W} {m m' : M} (h : m ∈ P.woman w) (h' : m' ∈ P.woman w)
    (e : P.rankW w m = P.rankW w m') : m = m' :=
  (List.idxOf_inj h).1 (by simpa [rankW] using e)

lemma degM_pos {m : M} {w : W} (h : w ∈ P.man m) : 0 < P.degM m :=
  List.length_pos_of_mem h

lemma degW_pos {m : M} {w : W} (h : m ∈ P.woman w) : 0 < P.degW w :=
  List.length_pos_of_mem h

/-- `|E| = ∑_m deg m`. -/
lemma card_E_eq_sum_degM : P.E.card = ∑ m, P.degM m := by
  rw [E, card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun m _ => ?_
  rw [← P.card_NM, ← card_filter, NM]
  congr 1; ext w; simp

/-- `|E| = ∑_w deg w`. -/
lemma card_E_eq_sum_degW : P.E.card = ∑ w, P.degW w := by
  rw [E, card_filter, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun w _ => ?_
  rw [← P.card_NW, ← card_filter, NW]
  congr 1; ext m; simp [P.mem_iff]

/-! ## Blocking pairs -/

/-- `(m, w)` is a blocking pair for the partner functions `pm`, `pw`: an edge outside the matching
whose endpoints both prefer each other to their partners (an unmatched player prefers every
acceptable partner to being alone). -/
def IsBlocking (pm : M → Option W) (pw : W → Option M) (m : M) (w : W) : Prop :=
  w ∈ P.man m ∧ pm m ≠ some w ∧ P.rankM m w < P.rankOptM m (pm m) ∧
    P.rankW w m < P.rankOptW w (pw w)

instance (pm : M → Option W) (pw : W → Option M) (m : M) (w : W) :
    Decidable (P.IsBlocking pm pw m w) := by
  unfold IsBlocking; infer_instance

/-- The set of blocking pairs. -/
def blockingPairs (pm : M → Option W) (pw : W → Option M) : Finset (M × W) :=
  Finset.univ.filter fun e => P.IsBlocking pm pw e.1 e.2

@[simp] lemma mem_blockingPairs {pm : M → Option W} {pw : W → Option M} {e : M × W} :
    e ∈ P.blockingPairs pm pw ↔ P.IsBlocking pm pw e.1 e.2 := by simp [blockingPairs]

/-- Definition 2.1: a matching is `(1 - ε)`-stable if it has at most `ε |E|` blocking pairs. -/
def IsAlmostStable (ε : ℝ) (pm : M → Option W) (pw : W → Option M) : Prop :=
  ((P.blockingPairs pm pw).card : ℝ) ≤ ε * P.E.card

/-- Definition 2.3 (Kipnis–Patt-Shamir): `(m, w)` is `ε`-blocking if both rank each other at least
`ε deg` places above their partners (with `P^v(∅) = deg v + 1`). -/
def IsEpsBlocking (ε : ℝ) (pm : M → Option W) (pw : W → Option M) (m : M) (w : W) : Prop :=
  ε * P.degM m ≤ (P.rankOptM m (pm m) : ℝ) - P.rankM m w ∧
    ε * P.degW w ≤ (P.rankOptW w (pw w) : ℝ) - P.rankW w m

noncomputable instance (ε : ℝ) (pm : M → Option W) (pw : W → Option M) (m : M) (w : W) :
    Decidable (P.IsEpsBlocking ε pm pw m w) := by
  unfold IsEpsBlocking; infer_instance

/-- A matching (in partner-function form) inside the communication graph. -/
structure IsMatching (pm : M → Option W) (pw : W → Option M) : Prop where
  consistent : ∀ m w, pm m = some w ↔ pw w = some m
  mem_E : ∀ m w, pm m = some w → w ∈ P.man m

end Prefs

/-! ## Quantiles -/

/-- The quantile `⌈k r / d⌉` of rank `r` in a list of length `d` cut into `k` quantiles. -/
def quant (k d r : ℕ) : ℕ := (k * r + d - 1) / d

lemma quant_mono {k d r r' : ℕ} (h : r ≤ r') : quant k d r ≤ quant k d r' :=
  Nat.div_le_div_right (by have := Nat.mul_le_mul_left k h; omega)

lemma quant_lt {k d r r' : ℕ} (hd : 0 < d) (h : k * r + d ≤ k * r') :
    quant k d r < quant k d r' := by
  unfold quant
  have h1 : (k * r + d - 1) / d + 1 = (k * r + d - 1 + d) / d := (Nat.add_div_right _ hd).symm
  have h2 : (k * r + d - 1 + d) / d ≤ (k * r' + d - 1) / d := Nat.div_le_div_right (by omega)
  omega

lemma one_le_quant {k d r : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r) (hd : 0 < d) : 1 ≤ quant k d r := by
  unfold quant
  rw [Nat.le_div_iff_mul_le hd]
  have : 1 ≤ k * r := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

lemma quant_le {k d r : ℕ} (hr : r ≤ d) (hd : 0 < d) : quant k d r ≤ k := by
  unfold quant
  rw [Nat.div_le_iff_le_mul_add_pred hd]
  have := Nat.mul_le_mul_left k hr
  rw [Nat.mul_comm d k]; omega

/-- Rank differences inside one quantile are smaller than `d / k`. -/
lemma lt_of_quant_le {k d r r' : ℕ} (hd : 0 < d) (hq : quant k d r' ≤ quant k d r) :
    k * r' < k * r + d := by
  by_contra h
  exact absurd (quant_lt hd (not_lt.1 h)) (not_lt.2 hq)

namespace Prefs

variable (P : Prefs M W)

/-- Quantile `q^m(w)` of `w` in `m`'s list. -/
def qM (k : ℕ) (m : M) (w : W) : ℕ := quant k (P.degM m) (P.rankM m w)

/-- Quantile `q^w(m)` of `m` in `w`'s list. -/
def qW (k : ℕ) (w : W) (m : M) : ℕ := quant k (P.degW w) (P.rankW w m)

lemma qM_mem_Icc {k : ℕ} (hk : 1 ≤ k) {m : M} {w : W} (h : w ∈ P.man m) :
    P.qM k m w ∈ Finset.Icc 1 k :=
  Finset.mem_Icc.2 ⟨one_le_quant hk (P.one_le_rankM m w) (P.degM_pos h),
    quant_le (P.rankM_le h) (P.degM_pos h)⟩

lemma qW_mem_Icc {k : ℕ} (hk : 1 ≤ k) {m : M} {w : W} (h : m ∈ P.woman w) :
    P.qW k w m ∈ Finset.Icc 1 k :=
  Finset.mem_Icc.2 ⟨one_le_quant hk (P.one_le_rankW w m) (P.degW_pos h),
    quant_le (P.rankW_le h) (P.degW_pos h)⟩

/-! ## Lemma 4.3 -/

/-- Counting step of Lemma 4.3: below a reference rank `R`, fewer than `2 d / k` ranks lie within
distance `< 2d/k`. -/
lemma card_close_le {α : Type*} (s : Finset α) (r : α → ℕ) (hr : Set.InjOn r s) (R k d : ℕ)
    (hk : 0 < k) :
    k * {a ∈ s | r a < R ∧ k * (R - r a) < 2 * d}.card ≤ 2 * d := by
  have hsub : ({a ∈ s | r a < R ∧ k * (R - r a) < 2 * d}).image (fun a => R - r a) ⊆
      Finset.Icc 1 ((2 * d - 1) / k) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_filter] at hx
    obtain ⟨a, ⟨-, h1, h2⟩, rfl⟩ := hx
    refine Finset.mem_Icc.2 ⟨by omega, ?_⟩
    rw [Nat.le_div_iff_mul_le hk]; rw [Nat.mul_comm] at h2; omega
  have hinj : Set.InjOn (fun a => R - r a) ({a ∈ s | r a < R ∧ k * (R - r a) < 2 * d} : Finset α) := by
    intro a ha b hb e
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    exact hr ha.1 hb.1 (by simp only at e; omega)
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at this
  have ht : k * ((2 * d - 1) / k) ≤ 2 * d - 1 := Nat.mul_div_le _ _
  simp only [Nat.add_sub_cancel] at this
  exact (Nat.mul_le_mul_left k this).trans (by omega)

/-- **Lemma 4.3.** For any partner functions, at most `4|E|/k` blocking pairs are not
`(2/k)`-blocking. -/
theorem lemma_4_3 (k : ℕ) (hk : 0 < k) (pm : M → Option W) (pw : W → Option M) :
    (k : ℝ) * ((P.blockingPairs pm pw).filter
      (fun e : M × W => ¬ P.IsEpsBlocking (2 / k) pm pw e.1 e.2)).card ≤ 4 * P.E.card := by
  classical
  -- split into pairs failing the man's condition and pairs failing the woman's condition
  set S := (P.blockingPairs pm pw).filter (fun e : M × W => ¬ P.IsEpsBlocking (2 / k) pm pw e.1 e.2)
  set SM := (Finset.univ : Finset M).sigma fun m =>
    {w ∈ P.NM m | P.rankM m w < P.rankOptM m (pm m) ∧
      k * (P.rankOptM m (pm m) - P.rankM m w) < 2 * P.degM m}
  set SW := (Finset.univ : Finset W).sigma fun w =>
    {m ∈ P.NW w | P.rankW w m < P.rankOptW w (pw w) ∧
      k * (P.rankOptW w (pw w) - P.rankW w m) < 2 * P.degW w}
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hS : S ⊆ SM.image (fun x : (_ : M) × W => (x.1, x.2)) ∪
      SW.image (fun x : (_ : W) × M => (x.2, x.1)) := by
    intro e he
    simp only [S, mem_blockingPairs, Finset.mem_filter, IsBlocking,
      IsEpsBlocking, not_and_or, not_le] at he
    obtain ⟨⟨hmem, -, hm, hw⟩, hc⟩ := he
    rcases hc with hc | hc
    · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨⟨e.1, e.2⟩, ?_, rfl⟩)
      simp only [SM, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter, mem_NM]
      refine ⟨hmem, hm, ?_⟩
      rw [← Nat.cast_sub hm.le, div_mul_eq_mul_div, lt_div_iff₀ hkR] at hc
      have : ((k * (P.rankOptM e.1 (pm e.1) - P.rankM e.1 e.2) : ℕ) : ℝ) <
          ((2 * P.degM e.1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨e.2, e.1⟩, ?_, rfl⟩)
      simp only [SW, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter, mem_NW]
      refine ⟨(P.mem_iff _ _).1 hmem, hw, ?_⟩
      rw [← Nat.cast_sub hw.le, div_mul_eq_mul_div, lt_div_iff₀ hkR] at hc
      have : ((k * (P.rankOptW e.2 (pw e.2) - P.rankW e.2 e.1) : ℕ) : ℝ) <
          ((2 * P.degW e.2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  have hSM : k * SM.card ≤ 2 * P.E.card := by
    rw [Finset.card_sigma, Finset.mul_sum, card_E_eq_sum_degM, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    refine card_close_le _ _ ?_ _ _ _ hk
    intro a ha b hb e; exact P.rankM_inj (by simpa using ha) (by simpa using hb) e
  have hSW : k * SW.card ≤ 2 * P.E.card := by
    rw [Finset.card_sigma, Finset.mul_sum, card_E_eq_sum_degW, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine card_close_le _ _ ?_ _ _ _ hk
    intro a ha b hb e; exact P.rankW_inj (by simpa using ha) (by simpa using hb) e
  have hcard : S.card ≤ SM.card + SW.card :=
    (Finset.card_le_card hS).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
  have : k * S.card ≤ 4 * P.E.card := by
    calc k * S.card ≤ k * (SM.card + SW.card) := Nat.mul_le_mul_left k hcard
      _ ≤ 4 * P.E.card := by rw [Nat.mul_add]; omega
  exact_mod_cast this

end Prefs

end Papers.PODC2015.AlmostStableMatchings
