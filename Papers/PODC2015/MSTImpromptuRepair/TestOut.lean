import Papers.PODC2015.MSTImpromptuRepair.Cut
import Cslib.Probability.Finite.Uniform

/-!
# `TestOut`: one-bit test for a leaving edge with an odd hash function (Section 2.1, Lemma 1)

A random `h : U → {0, 1}` (drawn uniformly from a finite family `Ω`) is `ε`-*odd* on the key set
`K` (`IsOdd`) if every non-empty `S ⊆ K` contains an odd number of keys hashing to 1 with
probability at least `ε` (inequality (1)). `TestOut(x, j, k)` aggregates, up the tree, the local
parities `∑_{e ∈ E(v), weight(e) ∈ [j, k]} h(e) mod 2` (`testOut`).

* `testOut_eq_sum_cut` — the aggregate equals `∑_{e ∈ Cut(T, V \ T), weight(e) ∈ [j,k]} h(e) mod 2`.
* `testOut_eq_zero_of_no_cut`, `exists_cut_of_testOut_eq_one` — **always correct if 1 is
  returned**: with no leaving edge in the weight range the answer is 0 for every `h`.
* `testOut_prob` — with an `ε`-odd family, if a leaving edge has its weight in the range, the
  answer is 1 with probability `≥ ε`.
* `thorupHash` — the paper's family `h(x) = [(a x mod 2^w) ≤ t]` (odd `a ∈ [1, 2^w]`,
  `t ∈ [1, 2^w]`) from [33]; that it is `1/8`-odd is cited, not proved. We check it for `w = 2, 3`
  on the key range `[1, 2^w]` (`thorup_odd_two`, `thorup_odd_three`) and note that it fails for
  the degenerate `w = 1` (`thorup_not_odd_one`).
-/

namespace Podc.MSTImpromptuRepair

open Finset Cslib.Probability

/-- `h` (drawn uniformly from `Ω`) is `ε`-odd on the keys `K`: every non-empty `S ⊆ K` has an odd
number of keys hashing to `1` with probability `≥ ε` (the paper's inequality (1)). -/
def IsOdd {Ω U : Type*} [Fintype Ω] (ε : ℝ) (K : Finset U) (h : Ω → U → ZMod 2) : Prop :=
  ∀ S ⊆ K, S.Nonempty → ε ≤ uprob (fun ω => ∑ x ∈ S, h ω x = 1)

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {U : Type*} (num : Sym2 V → U) (T : Finset V) (P : Sym2 V → Prop) [DecidablePred P]

/-- `TestOut(x, j, k)` for the hash function `h` and the edge predicate `P` (`weight ∈ [j, k]`):
the parity aggregated up the tree of the local parities of the nodes of `T`. -/
def testOut (h : U → ZMod 2) : ZMod 2 :=
  ∑ v ∈ T, ∑ e ∈ (G.incidenceFinset v).filter P, h (num e)

private theorem zmod2_add_self' (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

/-- The aggregated value is the parity of the leaving edges (in the weight range) hashing to 1. -/
theorem testOut_eq_sum_cut (h : U → ZMod 2) :
    testOut G num T P h = ∑ e ∈ (cut G T).filter P, h (num e) :=
  sum_incidence_filter_eq_sum_cut G zmod2_add_self' T P _

/-- If no leaving edge has its weight in the range, `TestOut` returns 0 whatever the hash. -/
theorem testOut_eq_zero_of_no_cut (hno : ∀ e ∈ cut G T, ¬ P e) (h : U → ZMod 2) :
    testOut G num T P h = 0 := by
  rw [testOut_eq_sum_cut, filter_false_of_mem hno, sum_empty]

/-- `TestOut` is always correct when it returns 1. -/
theorem exists_cut_of_testOut_eq_one {h : U → ZMod 2} (h1 : testOut G num T P h = 1) :
    ∃ e ∈ cut G T, P e := by
  by_contra hno
  push_neg at hno
  rw [testOut_eq_zero_of_no_cut G num T P hno] at h1
  exact zero_ne_one h1

/-- **`TestOut` succeeds with probability `≥ ε`.** If edge numbers are distinct on the leaving
edges and lie in `K`, `h` is `ε`-odd on `K`, and some leaving edge has its weight in the range,
then `TestOut` returns 1 with probability at least `ε`. -/
theorem testOut_prob [DecidableEq U] {Ω : Type*} [Fintype Ω] {ε : ℝ} {K : Finset U}
    {h : Ω → U → ZMod 2} (hodd : IsOdd ε K h) (hinj : Set.InjOn num (cut G T))
    (hK : ∀ e ∈ cut G T, num e ∈ K) (hex : ∃ e ∈ cut G T, P e) :
    ε ≤ uprob (fun ω => testOut G num T P (h ω) = 1) := by
  set S := ((cut G T).filter P).image num
  have hS : S ⊆ K := by
    intro x hx; obtain ⟨e, he, rfl⟩ := mem_image.1 hx; exact hK e (mem_filter.1 he).1
  have hSne : S.Nonempty := by
    obtain ⟨e, he, hP⟩ := hex; exact ⟨num e, mem_image_of_mem _ (mem_filter.2 ⟨he, hP⟩)⟩
  refine le_trans (hodd S hS hSne) (le_of_eq ?_)
  congr 1; funext ω
  rw [testOut_eq_sum_cut, sum_image (fun a ha b hb hab =>
    hinj (mem_filter.1 ha).1 (mem_filter.1 hb).1 hab)]

/-! ### The paper's odd hash function -/

/-- The hash function of [33]: `h(x) = 1` iff `(a x mod 2^w) ≤ t`. -/
def thorupHash (w a t x : ℕ) : ZMod 2 := if (a * x) % 2 ^ w ≤ t then 1 else 0

/-- Seeds: `a = 2 i + 1` odd in `[1, 2^w]`, `t = s + 1 ∈ [1, 2^w]`. -/
def thorupFamily (w : ℕ) (ω : Fin (2 ^ w / 2) × Fin (2 ^ w)) (x : ℕ) : ZMod 2 :=
  thorupHash w (2 * ω.1 + 1) (ω.2 + 1) x

/-- Counting form of `1/8`-oddness on the keys `[1, 2^w]`. -/
def OddEighth (w : ℕ) : Prop :=
  ∀ S ∈ (Icc 1 (2 ^ w)).powerset, S.Nonempty →
    Fintype.card (Fin (2 ^ w / 2) × Fin (2 ^ w)) ≤
      8 * #(univ.filter fun ω => ∑ x ∈ S, thorupFamily w ω x = 1)

theorem isOdd_of_oddEighth {w : ℕ} (hw : 1 ≤ w) (h : OddEighth w) :
    IsOdd (1 / 8) (Icc 1 (2 ^ w)) (thorupFamily w) := by
  intro S hS hne
  classical
  rw [uprob_eq_card_filter]
  have h8 := h S (mem_powerset.2 hS) hne
  have hpos : (0 : ℝ) < Fintype.card (Fin (2 ^ w / 2) × Fin (2 ^ w)) := by
    have h1 : 1 ≤ 2 ^ w / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hw
    have : 0 < Fintype.card (Fin (2 ^ w / 2) × Fin (2 ^ w)) := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      exact Nat.mul_pos (by omega) (by positivity)
    exact_mod_cast this
  rw [le_div_iff₀ hpos]
  have : ((Fintype.card (Fin (2 ^ w / 2) × Fin (2 ^ w)) : ℕ) : ℝ) ≤
      8 * (#(univ.filter fun ω => ∑ x ∈ S, thorupFamily w ω x = 1) : ℝ) := by exact_mod_cast h8
  linarith

/-- `w = 2`: the family is `1/8`-odd on `[1, 4]` (in fact `1/4`-odd). -/
theorem thorup_odd_two : IsOdd (1 / 8) (Icc 1 (2 ^ 2)) (thorupFamily 2) :=
  isOdd_of_oddEighth (by norm_num) (by unfold OddEighth thorupFamily thorupHash; decide)

set_option maxRecDepth 100000 in
/-- `w = 3`: the family is `1/8`-odd on `[1, 8]`. -/
theorem thorup_odd_three : IsOdd (1 / 8) (Icc 1 (2 ^ 3)) (thorupFamily 3) :=
  isOdd_of_oddEighth (by norm_num) (by unfold OddEighth thorupFamily thorupHash; decide)

/-- The degenerate word size `w = 1`: on the keys `{1, 2}` both keys are always sampled, so the
family is not `ε`-odd for any `ε > 0`. -/
theorem thorup_not_odd_one {ε : ℝ} (hε : 0 < ε) : ¬ IsOdd ε (Icc 1 (2 ^ 1)) (thorupFamily 1) := by
  intro h
  have := h (Icc 1 2) (by simp) ⟨1, by simp⟩
  have h0 : uprob (fun ω => ∑ x ∈ Icc 1 2, thorupFamily 1 ω x = 1) = 0 := by
    rw [uprob_eq_card_filter]
    have : (univ.filter fun ω : Fin (2 ^ 1 / 2) × Fin (2 ^ 1) =>
        ∑ x ∈ Icc 1 2, thorupFamily 1 ω x = 1) = ∅ := by
      unfold thorupFamily thorupHash; decide
    rw [this, card_empty]; simp
  linarith

end Podc.MSTImpromptuRepair

