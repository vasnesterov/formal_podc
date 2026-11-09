import Mathlib

/-!
# The linear system `m_r = M_r s_r` of `M(DBL₂)` and its kernel (Lemmas 2–4)

Di Luna, Baldoni, *Investigating the Cost of Anonymity on Dynamic Networks* (PODC 2015 brief
announcement; full version arXiv:1505.03509v1), Section 4.2.

In a multigraph of `M(DBL₂)` every non-leader node is joined to the leader, in each round, by the
edges of one of the label sets `{1}`, `{2}`, `{1,2}` (`Lab.one`, `Lab.two`, `Lab.both`). The history
of a node over `t` rounds is a word of length `t` over `Lab` (`words t`). The leader observes, for
every label `j` and every word `p` of length `i < t`, how many nodes had history `p` before round `i`
and an edge labelled `j` in round `i`: the row `(j, p)` of the paper's matrix, i.e.
`rowSum t s j p = ∑_{w : RowMem j p w} s w`.

**Indexing.** The paper's matrix `M_r` describes the leader's knowledge at the end of round `r`
(rounds `0, …, r`); its columns are the words of length `r + 1`. We index by the number of rounds
`t = r + 1`, so the paper's `M_r`, `k_r` are our objects for `t = r + 1`.

Main results:
* `inKer_iff`: the integer (or any commutative-ring) solutions of `M_r d = 0` are exactly the
  multiples of `kvec`, where `kvec (x :: w) = sgn x * kvec w` with `sgn {1} = sgn {2} = 1`,
  `sgn {1,2} = -1` (Lemmas 2 and 3: `k_r = [k_{r-1}, k_{r-1}, -k_{r-1}]`).
* `sum_kvec`, `card_kvec_neg`, `card_kvec_pos` (Lemma 4).
* `Matrix` form over `ℚ`: `ker_mulVecLin_matrix`, `finrank_ker_matrix`, `rank_matrix`,
  `linearIndependent_rows` (Lemma 2).
-/

namespace Podc.AnonymousDynamicCounting

/-- The label set of the edges between a node and the leader in one round of an `M(DBL₂)`
multigraph: `{1}`, `{2}` or `{1,2}` (labels are `Fin 2` in Lean: `0 ↔ 1`, `1 ↔ 2`). -/
inductive Lab
  | one
  | two
  | both
  deriving DecidableEq, Repr

namespace Lab

instance : Fintype Lab := ⟨{one, two, both}, fun x => by cases x <;> simp⟩

/-- The label set as a `Finset (Fin 2)`. -/
def toFinset : Lab → Finset (Fin 2)
  | one => {0}
  | two => {1}
  | both => Finset.univ

/-- The sign of a letter in the kernel vector: `+1` for `{1}`, `{2}` and `-1` for `{1,2}`. -/
def sgn : Lab → ℤ
  | one => 1
  | two => 1
  | both => -1

theorem toFinset_nonempty (x : Lab) : x.toFinset.Nonempty := by
  cases x
  exacts [⟨0, by simp [toFinset]⟩, ⟨1, by simp [toFinset]⟩, ⟨0, Finset.mem_univ _⟩]

theorem univ_eq : (Finset.univ : Finset Lab) = {one, two, both} := by
  rfl

theorem sum_univ {R : Type*} [AddCommMonoid R] (f : Lab → R) :
    ∑ x, f x = f one + f two + f both := by
  rw [univ_eq, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton,
    add_assoc]

/-- Every nonempty subset of `{1,2}` is one of the three letters. -/
def ofFinset (s : Finset (Fin 2)) : Lab :=
  if s = {0} then one else if s = {1} then two else both

theorem toFinset_ofFinset {s : Finset (Fin 2)} (hs : s.Nonempty) : (ofFinset s).toFinset = s := by
  unfold ofFinset
  split_ifs with h0 h1
  · simp [toFinset, h0]
  · simp [toFinset, h1]
  · simp only [toFinset]
    ext a
    simp only [Finset.mem_univ, true_iff]
    by_contra ha
    obtain ⟨b, hb⟩ := hs
    have hab : a ≠ b := fun h => ha (h ▸ hb)
    have : s = {b} := by
      ext c
      simp only [Finset.mem_singleton]
      constructor
      · intro hc
        by_contra hcb
        fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
      · rintro rfl; exact hb
    fin_cases b <;> simp_all

theorem ofFinset_toFinset (x : Lab) : ofFinset x.toFinset = x := by
  cases x <;> decide

theorem sum_sgn_of_mem (j : Fin 2) : ∑ x : Lab, (if j ∈ x.toFinset then x.sgn else 0) = 0 := by
  rw [sum_univ]; fin_cases j <;> simp [toFinset, sgn]

end Lab

/-! ### Words -/

/-- The words of length `t` over `Lab` (histories of a node over `t` rounds). -/
def words : ℕ → Finset (List Lab)
  | 0 => {[]}
  | t + 1 => (Finset.univ ×ˢ words t).map
      ⟨fun p => p.1 :: p.2, fun a b h => by simpa [Prod.ext_iff] using h⟩

@[simp] theorem mem_words {t : ℕ} {w : List Lab} : w ∈ words t ↔ w.length = t := by
  induction t generalizing w with
  | zero => simp [words]
  | succ t ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      simp only [words, Finset.mem_map, Finset.mem_product, Finset.mem_univ, true_and, ih,
        Prod.exists, List.length_cons, add_left_inj]
      constructor
      · rintro ⟨_, b, hb, h⟩
        obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact hb
      · intro h; exact ⟨a, w, h, rfl⟩

theorem sum_words_zero {R : Type*} [AddCommMonoid R] (f : List Lab → R) :
    ∑ w ∈ words 0, f w = f [] := by simp [words]

theorem sum_words_succ {R : Type*} [AddCommMonoid R] (t : ℕ) (f : List Lab → R) :
    ∑ w ∈ words (t + 1), f w = ∑ x : Lab, ∑ w ∈ words t, f (x :: w) := by
  simp [words, Finset.sum_product]
  rfl

@[simp] theorem card_words (t : ℕ) : (words t).card = 3 ^ t := by
  induction t with
  | zero => simp [words]
  | succ t ih => simp [words, ih, pow_succ, mul_comm]; rfl

/-- The kernel vector `k_r`: the product of the signs of the letters. -/
def kvec (w : List Lab) : ℤ := (w.map Lab.sgn).prod

@[simp] theorem kvec_nil : kvec [] = 1 := rfl

@[simp] theorem kvec_cons (x : Lab) (w : List Lab) : kvec (x :: w) = x.sgn * kvec w := by
  simp [kvec]

theorem kvec_eq_one_or (w : List Lab) : kvec w = 1 ∨ kvec w = -1 := by
  induction w with
  | nil => simp
  | cons x w ih => cases x <;> rcases ih with h | h <;> simp [h, Lab.sgn]

/-- `w` is a column where the row `(j, p)` of `M_r` has a `1`: `w` starts with `p`, followed by a
letter containing the label `j`. -/
def RowMem (j : Fin 2) : List Lab → List Lab → Prop
  | [], [] => False
  | [], b :: _ => j ∈ b.toFinset
  | _ :: _, [] => False
  | a :: p, b :: w => a = b ∧ RowMem j p w

instance decRowMem (j : Fin 2) : ∀ p w, Decidable (RowMem j p w)
  | [], [] => isFalse id
  | [], b :: _ => inferInstanceAs (Decidable (j ∈ b.toFinset))
  | _ :: _, [] => isFalse id
  | a :: p, b :: w =>
    haveI := decRowMem j p w
    inferInstanceAs (Decidable (a = b ∧ RowMem j p w))

@[simp] theorem rowMem_nil_nil (j : Fin 2) : ¬ RowMem j [] [] := id
@[simp] theorem rowMem_nil_cons (j : Fin 2) (b w) : RowMem j [] (b :: w) ↔ j ∈ b.toFinset := Iff.rfl
@[simp] theorem rowMem_cons_nil (j : Fin 2) (a p) : ¬ RowMem j (a :: p) [] := id
@[simp] theorem rowMem_cons_cons (j : Fin 2) (a p b w) :
    RowMem j (a :: p) (b :: w) ↔ a = b ∧ RowMem j p w := Iff.rfl

/-- `RowMem` in terms of prefixes and letters. -/
theorem rowMem_iff (j : Fin 2) (p w : List Lab) :
    RowMem j p w ↔ w.take p.length = p ∧ ∃ x, w[p.length]? = some x ∧ j ∈ x.toFinset := by
  induction p generalizing w with
  | nil => cases w <;> simp
  | cons a p ih =>
    cases w with
    | nil => simp
    | cons b w => simp [ih, eq_comm, and_assoc]

/-- The row `(j, p)` of `M_r · s`, for `s` indexed by the words of length `t`. -/
def rowSum {R : Type*} [AddCommMonoid R] (t : ℕ) (s : List Lab → R) (j : Fin 2) (p : List Lab) :
    R :=
  ∑ w ∈ words t with RowMem j p w, s w

/-- `d` solves the homogeneous system `M_r d = 0` (all rows; rows with `p.length ≥ t` are zero). -/
def InKer {R : Type*} [AddCommMonoid R] (t : ℕ) (d : List Lab → R) : Prop :=
  ∀ j p, rowSum t d j p = 0

theorem rowSum_zero {R : Type*} [AddCommMonoid R] (s : List Lab → R) (j : Fin 2) (p : List Lab) :
    rowSum 0 s j p = 0 := by
  cases p <;> simp [rowSum, words, Finset.filter_singleton]

theorem rowSum_succ_nil {R : Type*} [AddCommMonoid R] (t : ℕ) (s : List Lab → R) (j : Fin 2) :
    rowSum (t + 1) s j [] = ∑ x : Lab, if j ∈ x.toFinset then ∑ w ∈ words t, s (x :: w) else 0 := by
  unfold rowSum
  rw [Finset.sum_filter, sum_words_succ]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [rowMem_nil_cons]
  split_ifs <;> simp

theorem rowSum_succ_cons {R : Type*} [AddCommMonoid R] (t : ℕ) (s : List Lab → R) (j : Fin 2)
    (a : Lab) (p : List Lab) :
    rowSum (t + 1) s j (a :: p) = rowSum t (fun w => s (a :: w)) j p := by
  unfold rowSum
  rw [Finset.sum_filter, sum_words_succ, Finset.sum_filter]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [Ne.symm hb]
  · simp

/-- Lemma 4 (first part): `∑ k_r = 1`. -/
theorem sum_kvec (t : ℕ) : ∑ w ∈ words t, kvec w = 1 := by
  induction t with
  | zero => simp [sum_words_zero]
  | succ t ih =>
    rw [sum_words_succ]
    simp only [kvec_cons, ← Finset.mul_sum, ih, mul_one]
    decide

theorem rowSum_smul_kvec {R : Type*} [CommRing R] (t : ℕ) (c : R) (j : Fin 2) (p : List Lab) :
    rowSum t (fun w => c * (kvec w : R)) j p = 0 := by
  induction t generalizing p c with
  | zero => exact rowSum_zero _ _ _
  | succ t ih =>
    cases p with
    | nil =>
      rw [rowSum_succ_nil]
      have h : ∀ x : Lab, ∑ w ∈ words t, c * (kvec (x :: w) : R) = c * x.sgn := by
        intro x
        have := sum_kvec t
        calc ∑ w ∈ words t, c * (kvec (x :: w) : R)
            = c * x.sgn * ((∑ w ∈ words t, kvec w : ℤ) : R) := by
              push_cast; rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by rw [kvec_cons]; push_cast; ring
          _ = c * x.sgn := by rw [this]; simp
      simp only [h]
      have := congrArg (fun z : ℤ => c * (z : R)) (Lab.sum_sgn_of_mem j)
      simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.mul_sum, mul_ite,
        mul_zero, Int.cast_zero] at this
      simpa using this
    | cons a p =>
      rw [rowSum_succ_cons]
      simpa [kvec_cons, ← mul_assoc] using ih (c * a.sgn) p

/-- Lemmas 2 and 3 of the paper: the solutions of `M_r d = 0` (over any commutative ring) are
exactly the multiples of the kernel vector `k_r` (`kvec`). In particular `ker M_r` has dimension one
and is spanned by `k_r`, and `k_r = [k_{r-1}, k_{r-1}, -k_{r-1}]` (`kvec_cons`). -/
theorem inKer_iff {R : Type*} [CommRing R] (t : ℕ) (d : List Lab → R) :
    InKer t d ↔ ∃ c : R, ∀ w ∈ words t, d w = c * kvec w := by
  constructor
  · intro hd
    induction t generalizing d with
    | zero => exact ⟨d [], fun w hw => by simp_all⟩
    | succ t ih =>
      have hx : ∀ x : Lab, ∃ c : R, ∀ w ∈ words t, d (x :: w) = c * kvec w := fun x =>
        ih _ fun j p => by rw [← rowSum_succ_cons]; exact hd j (x :: p)
      choose c hc using hx
      have hrow : ∀ j : Fin 2, ∑ x : Lab, (if j ∈ x.toFinset then c x else 0) = 0 := by
        intro j
        have := hd j []
        rw [rowSum_succ_nil] at this
        refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) this
        split_ifs
        · rw [Finset.sum_congr rfl (hc x), ← Finset.mul_sum, ← Int.cast_sum, sum_kvec]; simp
        · rfl
      have h0' := hrow 0
      have h1' := hrow 1
      simp only [Lab.sum_univ, Lab.toFinset] at h0' h1'
      simp at h0' h1'
      refine ⟨c Lab.one, fun w hw => ?_⟩
      cases w with
      | nil => simp at hw
      | cons x w =>
        simp only [mem_words, List.length_cons, add_left_inj] at hw
        rw [hc x w (mem_words.2 hw), kvec_cons, Int.cast_mul, ← mul_assoc]
        congr 1
        cases x
        · simp [Lab.sgn]
        · simp only [Lab.sgn, Int.cast_one, mul_one]; linear_combination h1' - h0'
        · simp only [Lab.sgn, Int.cast_neg, Int.cast_one, mul_neg, mul_one]
          linear_combination h0'
  · rintro ⟨c, hc⟩ j p
    rw [show rowSum t d j p = rowSum t (fun w => c * (kvec w : R)) j p from
      Finset.sum_congr rfl fun w hw => hc w (Finset.mem_filter.1 hw).1]
    exact rowSum_smul_kvec t c j p

/-- **Lemma 3.** `k_r` solves `M_r k_r = 0`, and `k_r = [k_{r-1}, k_{r-1}, -k_{r-1}]` (the blocks
of the lexicographic order `{1} < {2} < {1,2}` on the first letter), with `k_{-1} = 1`. -/
theorem lemma_3 (t : ℕ) :
    InKer t (fun w => (kvec w : ℤ)) ∧ kvec [] = 1 ∧
      ∀ w, kvec (Lab.one :: w) = kvec w ∧ kvec (Lab.two :: w) = kvec w ∧
        kvec (Lab.both :: w) = -kvec w := by
  refine ⟨fun j p => by simpa using rowSum_smul_kvec t (1 : ℤ) j p, rfl, fun w => ?_⟩
  simp [Lab.sgn]

/-! ### Lemma 4: positive and negative parts of `k_r` -/

theorem card_kvec_pos_add_neg (t : ℕ) :
    ((words t).filter (kvec · = 1)).card + ((words t).filter (kvec · = -1)).card = 3 ^ t := by
  rw [← card_words t, ← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_union, Finset.mem_filter]
    have := kvec_eq_one_or w
    tauto
  · rw [Finset.disjoint_filter]; intro w _ h; rw [h]; decide

theorem card_kvec_pos_sub_neg (t : ℕ) :
    (((words t).filter (kvec · = 1)).card : ℤ) - ((words t).filter (kvec · = -1)).card = 1 := by
  have h : ∀ w, kvec w = (if kvec w = 1 then 1 else 0) - (if kvec w = -1 then 1 else 0) := by
    intro w; rcases kvec_eq_one_or w with h | h <;> simp [h]
  conv_rhs => rw [← sum_kvec t]
  rw [Finset.sum_congr rfl (fun w _ => h w), Finset.sum_sub_distrib]
  simp [Finset.sum_boole]

/-- Lemma 4: the number of `-1` entries of `k_r` is `(3^(r+1) - 1)/2` (here `t = r + 1`). -/
theorem card_kvec_neg (t : ℕ) :
    2 * ((words t).filter (kvec · = -1)).card + 1 = 3 ^ t := by
  have h1 := card_kvec_pos_add_neg t
  have h2 := card_kvec_pos_sub_neg t
  omega

/-- Lemma 4: the number of `+1` entries of `k_r` is `(3^(r+1) + 1)/2` (here `t = r + 1`). -/
theorem card_kvec_pos (t : ℕ) :
    2 * ((words t).filter (kvec · = 1)).card = 3 ^ t + 1 := by
  have h1 := card_kvec_pos_add_neg t
  have h2 := card_kvec_pos_sub_neg t
  omega

/-- `Σ⁺ a`: the sum of the positive entries of a vector indexed by `words t`. -/
def posSum (t : ℕ) (a : List Lab → ℤ) : ℤ := ∑ w ∈ words t, max (a w) 0

/-- `Σ⁻ a`: the sum of (the absolute values of) the negative entries. -/
def negSum (t : ℕ) (a : List Lab → ℤ) : ℤ := ∑ w ∈ words t, max (-a w) 0

theorem posSum_kvec (t : ℕ) : posSum t kvec = ((words t).filter (kvec · = 1)).card := by
  unfold posSum
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rcases kvec_eq_one_or w with h | h <;> simp [h]

theorem negSum_kvec (t : ℕ) : negSum t kvec = ((words t).filter (kvec · = -1)).card := by
  unfold negSum
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rcases kvec_eq_one_or w with h | h <;> simp [h]

/-- **Lemma 4** (corrected exponent), in the paper's indexing `k_r` (words of length `r + 1`):
`∑ k_r = 1`, `Σ⁺ k_r = ½(3^(r+1) + 1)` and `min(Σ⁺ k_r, Σ⁻ k_r) = Σ⁻ k_r = ½(3^(r+1) + 1) - 1`. -/
theorem lemma_4 (r : ℕ) :
    ∑ w ∈ words (r + 1), kvec w = 1 ∧
    2 * posSum (r + 1) kvec = 3 ^ (r + 1) + 1 ∧
    min (posSum (r + 1) kvec) (negSum (r + 1) kvec) = negSum (r + 1) kvec ∧
    2 * (negSum (r + 1) kvec + 1) = 3 ^ (r + 1) + 1 := by
  have h1 := card_kvec_pos (r + 1)
  have h2 := card_kvec_neg (r + 1)
  rw [posSum_kvec, negSum_kvec]
  generalize ((words (r + 1)).filter (kvec · = 1)).card = P at h1 ⊢
  generalize ((words (r + 1)).filter (kvec · = -1)).card = N at h2 ⊢
  have hNP : N ≤ P := by generalize 3 ^ (r + 1) = m at h1 h2; omega
  have hN : 2 * (N + 1) = 3 ^ (r + 1) + 1 := by generalize 3 ^ (r + 1) = m at h1 h2 ⊢; omega
  refine ⟨sum_kvec _, by exact_mod_cast h1, ?_, by exact_mod_cast hN⟩
  apply min_eq_right; exact_mod_cast hNP

/-- The value printed in the *statement* of Lemma 4, `Σ⁻ k_r = ½(3^r + 1) - 1`, is wrong (the
proof derives `½(3^(r+1) + 1) - 1`): for `r = 1` the paper itself lists `Σ⁻ k_1 = 4`, while
`½(3^1 + 1) - 1 = 1`. -/
theorem lemma_4_statement_false : ¬ ∀ r : ℕ, 2 * (negSum (r + 1) kvec + 1) = 3 ^ r + 1 := by
  intro h
  have := h 1
  have h2 := (lemma_4 1).2.2.2
  norm_num at this h2
  omega


/-! ### Lemma 2 in matrix form -/

theorem rowSum_eq_zero_of_le {R : Type*} [AddCommMonoid R] {t : ℕ} (s : List Lab → R) (j : Fin 2)
    {p : List Lab} (hp : t ≤ p.length) : rowSum t s j p = 0 := by
  refine Finset.sum_eq_zero fun w hw => ?_
  rw [Finset.mem_filter, mem_words, rowMem_iff] at hw
  obtain ⟨hw, -, x, hx, -⟩ := hw
  rw [List.getElem?_eq_none (by omega)] at hx
  cases hx

/-- The rows of `M_r`: a label and a word of length `< t` (the paper has `2 · Σ_{i<t} 3^i` of
them). -/
def rowsFin (t : ℕ) : Finset (Fin 2 × List Lab) :=
  Finset.univ ×ˢ (Finset.range t).biUnion words

theorem card_rowsFin (t : ℕ) : (rowsFin t).card = 3 ^ t - 1 := by
  rw [rowsFin, Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_biUnion]
  · simp only [card_words]
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      have : 1 ≤ 3 ^ t := Nat.one_le_pow _ _ (by norm_num)
      omega
  · intro i _ i' _ hii'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    rw [mem_words] at hw hw'
    exact hii' (hw.symm.trans hw')

/-- The paper's matrix `M_r` (for `t = r + 1`): rows `(j, p)`, columns the words `w` of length
`t`; the entry is `1` iff `w` starts with `p` followed by a letter containing `j`. -/
def matrixM (t : ℕ) : Matrix (rowsFin t) (words t) ℚ :=
  fun r w => if RowMem r.1.1 r.1.2 w.1 then 1 else 0

/-- The kernel vector `k_r` as a vector indexed by the columns. -/
def kvecQ (t : ℕ) : words t → ℚ := fun w => kvec w.1

/-- Extend a vector indexed by the columns by `0` to all words. -/
def extend {t : ℕ} (v : words t → ℚ) (u : List Lab) : ℚ :=
  if h : u ∈ words t then v ⟨u, h⟩ else 0

theorem mulVec_matrixM {t : ℕ} (v : words t → ℚ) (r : rowsFin t) :
    (matrixM t).mulVec v r = rowSum t (extend v) r.1.1 r.1.2 := by
  simp only [Matrix.mulVec, dotProduct, matrixM, ite_mul, one_mul, zero_mul, rowSum,
    Finset.sum_filter]
  rw [← Finset.sum_coe_sort (words t)]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [extend, w.2]

theorem mem_ker_matrixM_iff {t : ℕ} (v : words t → ℚ) :
    (matrixM t).mulVec v = 0 ↔ InKer t (extend v) := by
  constructor
  · intro h j p
    by_cases hp : p.length < t
    · have hr : (j, p) ∈ rowsFin t := by
        simp [rowsFin, hp]
      have := congrFun h ⟨(j, p), hr⟩
      rwa [mulVec_matrixM] at this
    · exact rowSum_eq_zero_of_le _ _ (by omega)
  · intro h; funext r; rw [mulVec_matrixM]; exact h _ _

/-- **Lemma 2 and Lemma 3** (matrix form): `ker M_r` is spanned by `k_r`, so it has dimension 1; the
rank of `M_r` equals its number of rows `2 · Σ_{i ≤ r} 3^i = 3^(r+1) - 1`, i.e. the rows are
linearly independent. Here `t = r + 1`. -/
theorem lemma_2 (t : ℕ) :
    LinearMap.ker (matrixM t).mulVecLin = Submodule.span ℚ {kvecQ t} ∧
    Module.finrank ℚ (LinearMap.ker (matrixM t).mulVecLin) = 1 ∧
    (matrixM t).rank = Fintype.card (rowsFin t) ∧
    Fintype.card (rowsFin t) = 3 ^ t - 1 ∧
    LinearIndependent ℚ (matrixM t).row := by
  have hker : LinearMap.ker (matrixM t).mulVecLin = Submodule.span ℚ {kvecQ t} := by
    ext v
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, mem_ker_matrixM_iff, inKer_iff,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, funext fun w => ?_⟩
      have := hc w.1 w.2
      simp only [extend, w.2, dite_true] at this
      simp [kvecQ, this]
    · rintro ⟨c, rfl⟩
      refine ⟨c, fun w hw => ?_⟩
      simp [extend, hw, kvecQ]
  have hne : kvecQ t ≠ 0 := by
    intro h
    have hw : List.replicate t Lab.one ∈ words t := by simp
    have := congrFun h ⟨_, hw⟩
    simp only [kvecQ, Pi.zero_apply, Int.cast_eq_zero] at this
    rcases kvec_eq_one_or (List.replicate t Lab.one) with h' | h' <;> simp [h'] at this
  have hfin : Module.finrank ℚ (LinearMap.ker (matrixM t).mulVecLin) = 1 := by
    rw [hker, finrank_span_singleton hne]
  have hrank : (matrixM t).rank = Fintype.card (rowsFin t) := by
    have := LinearMap.finrank_range_add_finrank_ker (matrixM t).mulVecLin
    rw [hfin, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_words] at this
    rw [Matrix.rank, Fintype.card_coe, card_rowsFin]
    omega
  refine ⟨hker, hfin, hrank, by rw [Fintype.card_coe, card_rowsFin], ?_⟩
  rw [linearIndependent_iff_card_eq_finrank_span, ← hrank, Matrix.rank_eq_finrank_span_row]
  rfl

end Podc.AnonymousDynamicCounting
