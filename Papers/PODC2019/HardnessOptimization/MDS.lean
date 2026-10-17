import Papers.PODC2019.HardnessOptimization.MDSLocal

/-!
# Lemma 2.1: the MDS family is a family of lower bound graphs

`G_{x,y}` has a dominating set of size `4 log k + 2` iff `DISJ_{k²}(x, y) = FALSE`.
-/

namespace HardnessOptimization

open Finset

variable {L : ℕ} (x y : Idx L → Idx L → Bool)

/-! ### The canonical dominating set (`⇐`) -/

/-- The cycle vertex chosen at a bit `b` of the special index: `f` if `b = 1`, `t` if `b = 0`
(the set `bin̄` used by the paper's construction; rows are adjacent to `bin`). -/
def dsKind (b : Bool) : Fin 3 := if b then 0 else 1

/-- The dominating set of size `4 log k + 2` for an intersecting pair `(i, j)`: the rows `a^i_1`,
`b^i_1`, and in every cycle `(ℓ, h)` the two vertices `f` or `t` (of both sides) chosen by the bit
`h` of `i` (layer 1) or `j` (layer 2). -/
def canonDS (i j : Idx L) : Finset (MV L) :=
  {MV.row false false i, MV.row true false i} ∪
    (univ : Finset (Bool × Bool × Fin L)).image
      fun p => MV.gad p.1 p.2.1 p.2.2 (dsKind ((if p.2.1 then j else i) p.2.2))

lemma card_canonDS (i j : Idx L) : (canonDS i j).card = 4 * L + 2 := by
  rw [canonDS, card_union_of_disjoint]
  · rw [card_image_of_injective]
    · simp [card_univ, Fintype.card_prod]; ring
    · rintro ⟨s, ℓ, h⟩ ⟨s', ℓ', h'⟩ he
      simp only [MV.gad.injEq] at he
      obtain ⟨rfl, rfl, rfl, -⟩ := he
      rfl
  · rw [disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha
    obtain ⟨p, -, rfl⟩ := mem_image.1 hb
    rcases ha with rfl | rfl <;> simp

lemma isDominating_canonDS {i j : Idx L} (hx : x i j = true) (hy : y i j = true) :
    IsDominating (mdsGraph x y) (canonDS i j) := by
  have hmem : ∀ s ℓ h, MV.gad s ℓ h (dsKind ((if ℓ then j else i) h)) ∈ canonDS i j := by
    intro s ℓ h
    exact mem_union_right _ (mem_image.2 ⟨(s, ℓ, h), mem_univ _, rfl⟩)
  intro v
  cases v with
  | row s ℓ i' =>
    by_cases hi : i' = (if ℓ then j else i)
    · cases ℓ
      · left
        simp only [Bool.false_eq_true, ↓reduceIte] at hi
        subst hi
        cases s <;> simp [canonDS]
      · right
        simp only [↓reduceIte] at hi
        subst hi
        refine ⟨MV.row s false i, by cases s <;> simp [canonDS], ?_⟩
        rw [adj_row_row]
        refine ⟨rfl, rfl, ?_⟩
        cases s <;> simp [redge, xy, hx, hy]
    · obtain ⟨h, hh⟩ := Function.ne_iff.1 hi
      right
      refine ⟨_, hmem s ℓ h, ?_⟩
      rw [adj_row_gad]
      refine ⟨rfl, rfl, ?_⟩
      revert hh
      cases i' h <;> cases (if ℓ then j else i) h <;> simp [dsKind, bitK]
  | gad s ℓ h κ =>
    rcases cyc_dom_canon s κ ((if ℓ then j else i) h) with hk | ⟨s', hs'⟩
    · left
      rw [hk]
      exact hmem s ℓ h
    · right
      exact ⟨_, hmem s' ℓ h, (adj_gad_gad x y).2 ⟨rfl, rfl, hs'⟩⟩

/-! ### Counting vertices of `D` per cycle -/

section Count

variable (D : Finset (MV L))

/-- Number of vertices of `D` on the cycle `(ℓ, h)`. -/
def cc (p : Bool × Fin L) : ℕ := (D.filter fun v => v.cyc = some p).card

/-- Number of row vertices in `D`. -/
def ρ : ℕ := (D.filter fun v => v.cyc = none).card

/-- Excess of `D` over two vertices per cycle. -/
def exc : ℕ := ∑ p : Bool × Fin L, (cc D p - 2)

lemma card_eq_ρ_add : D.card = ρ D + ∑ p : Bool × Fin L, cc D p := by
  rw [card_eq_sum_card_fiberwise (f := MV.cyc) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _)),
    Fintype.sum_option]
  rfl

/-- Six membership bits of the cycle `(ℓ, h)`. -/
def locM (ℓ : Bool) (h : Fin L) : Bool → Fin 3 → Bool := fun s κ => decide (MV.gad s ℓ h κ ∈ D)

/-- Row bits of the cycle `(ℓ, h)`: is there a row of side `s`, layer `ℓ`, bit `b` at `h` in `D`? -/
def locR (ℓ : Bool) (h : Fin L) : Bool → Bool → Bool :=
  fun s b => decide (∃ i : Idx L, MV.row s ℓ i ∈ D ∧ i h = b)

lemma cnt6_le_cc (ℓ : Bool) (h : Fin L) : cnt6 (locM D ℓ h) ≤ cc D (ℓ, h) := by
  classical
  let S : Finset (Bool × Fin 3) := univ.filter fun q => MV.gad q.1 ℓ h q.2 ∈ D
  have h1 : cnt6 (locM D ℓ h) = S.card := by
    simp only [S, card_filter, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three,
      cnt6, locM]
    simp only [Bool.toNat, decide_eq_true_eq, cond_eq_ite]
    ring
  have h2 : (S.image fun q => MV.gad q.1 ℓ h q.2).card = S.card :=
    card_image_of_injective _ fun q q' he => by
      simp only [MV.gad.injEq] at he
      exact Prod.ext he.1 he.2.2.2
  rw [h1, ← h2]
  refine card_le_card fun v hv => ?_
  obtain ⟨q, hq, rfl⟩ := mem_image.1 hv
  simp only [S, mem_filter, mem_univ, true_and] at hq
  exact mem_filter.2 ⟨hq, rfl⟩

variable {x y}
variable {D}

lemma locOk (hD : IsDominating (mdsGraph x y) D) (ℓ : Bool) (h : Fin L) :
    LocOk (locM D ℓ h) (locR D ℓ h) := by
  intro s κ
  rcases hD (MV.gad s ℓ h κ) with hv | ⟨w, hw, hadj⟩
  · left; simpa [locM] using hv
  · right
    cases w with
    | row s' ℓ' i =>
      rw [adj_gad_row] at hadj
      obtain ⟨rfl, rfl, rfl⟩ := hadj
      right
      cases hih : i h
      · left; exact ⟨by simp [bitK], by simp only [locR]; exact decide_eq_true ⟨i, hw, hih⟩⟩
      · right; exact ⟨by simp [bitK], by simp only [locR]; exact decide_eq_true ⟨i, hw, hih⟩⟩
    | gad s' ℓ' h' κ' =>
      rw [adj_gad_gad] at hadj
      obtain ⟨rfl, rfl, hc⟩ := hadj
      left
      exact ⟨s', κ', hc, by simpa [locM] using hw⟩

lemma two_le_cc (hD : IsDominating (mdsGraph x y) D) (p : Bool × Fin L) : 2 ≤ cc D p :=
  (loc_two_le _ _ (locOk hD p.1 p.2)).trans (cnt6_le_cc D p.1 p.2)

lemma ρ_add_exc (hD : IsDominating (mdsGraph x y) D) (hcard : D.card ≤ 4 * L + 2) :
    ρ D + exc D ≤ 2 := by
  have hsum : ∑ p : Bool × Fin L, cc D p = exc D + 4 * L := by
    have : ∑ p : Bool × Fin L, cc D p = ∑ p : Bool × Fin L, ((cc D p - 2) + 2) :=
      sum_congr rfl fun p _ => (Nat.sub_add_cancel (two_le_cc hD p)).symm
    rw [this, sum_add_distrib, exc]
    simp [card_univ, Fintype.card_prod]
    ring
  have := card_eq_ρ_add D
  omega

lemma exc_ge_one (p : Bool × Fin L) : cc D p - 2 ≤ exc D :=
  single_le_sum (f := fun p => cc D p - 2) (fun _ _ => Nat.zero_le _) (mem_univ p)

lemma exc_ge_two {p q : Bool × Fin L} (hpq : p ≠ q) : (cc D p - 2) + (cc D q - 2) ≤ exc D := by
  rw [← sum_pair hpq (f := fun p => cc D p - 2)]
  exact sum_le_sum_of_subset (subset_univ _)

lemma exc_ge_three {p q r : Bool × Fin L} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (cc D p - 2) + (cc D q - 2) + (cc D r - 2) ≤ exc D := by
  have : (cc D p - 2) + (cc D q - 2) + (cc D r - 2) = ∑ s ∈ {p, q, r}, (cc D s - 2) := by
    rw [sum_insert (by simp [hpq, hpr]), sum_pair hqr]; ring
  rw [this]
  exact sum_le_sum_of_subset (subset_univ _)

lemma ρ_ge (R : Finset (MV L)) (hR : ∀ v ∈ R, v ∈ D ∧ v.cyc = none) : R.card ≤ ρ D :=
  card_le_card fun v hv => mem_filter.2 (hR v hv)

end Count

/-! ### Rows that are not dominated by gadget vertices -/

section Rows

variable {x y} {D : Finset (MV L)}

/-- A row that is neither in `D` nor dominated by a gadget vertex is dominated by a row of the
other layer (through an input edge). -/
lemma row_needs_row (hD : IsDominating (mdsGraph x y) D) {s ℓ : Bool} {i : Idx L}
    (hi : MV.row s ℓ i ∉ D) (hg : ∀ h, MV.gad s ℓ h (bitK (i h)) ∉ D) :
    ∃ j, MV.row s (!ℓ) j ∈ D ∧ redge x y s ℓ i j = true := by
  rcases hD (MV.row s ℓ i) with hv | ⟨w, hw, hadj⟩
  · exact absurd hv hi
  · cases w with
    | row s' ℓ' j =>
      rw [adj_row_row] at hadj
      obtain ⟨rfl, rfl, he⟩ := hadj
      exact ⟨j, hw, he⟩
    | gad s' ℓ' h κ =>
      rw [adj_row_gad] at hadj
      obtain ⟨rfl, rfl, rfl⟩ := hadj
      exact absurd hw (hg h)

/-- The canonical index of a row avoiding `D` at every bit where `D` does not contain both
`f` and `t`: bit `1` iff `f ∈ D`. -/
def canonIdx (D : Finset (MV L)) (s ℓ : Bool) : Idx L := fun h => decide (MV.gad s ℓ h 0 ∈ D)

lemma canonIdx_not_mem {s ℓ : Bool} (hnb : ∀ h, ¬(MV.gad s ℓ h 0 ∈ D ∧ MV.gad s ℓ h 1 ∈ D))
    (h : Fin L) : MV.gad s ℓ h (bitK (canonIdx D s ℓ h)) ∉ D := by
  by_cases hf : MV.gad s ℓ h 0 ∈ D
  · simp only [canonIdx, hf, decide_true, bitK, ↓reduceIte]
    exact fun ht => hnb h ⟨hf, ht⟩
  · simp [canonIdx, hf, bitK]

/-- (F1) If `D` has no row of side `s`, then in every layer some cycle contains both `f_s` and
`t_s`. -/
lemma exists_both_of_no_rows (hD : IsDominating (mdsGraph x y) D) {s : Bool}
    (hno : ∀ ℓ i, MV.row s ℓ i ∉ D) (ℓ : Bool) :
    ∃ h, MV.gad s ℓ h 0 ∈ D ∧ MV.gad s ℓ h 1 ∈ D := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  obtain ⟨j, hj, -⟩ := row_needs_row hD (hno ℓ (canonIdx D s ℓ))
    (canonIdx_not_mem (fun h ⟨h1, h2⟩ => hcon h h1 h2))
  exact hno _ _ hj

end Rows

/-! ### The converse direction (`⇒`) -/

section Converse

variable {x y} {D : Finset (MV L)}

lemma locM_eq {ℓ h s κ} : locM D ℓ h s κ = true ↔ MV.gad s ℓ h κ ∈ D := by simp [locM]

lemma locR_eq {ℓ h s b} : locR D ℓ h s b = true ↔ ∃ i : Idx L, MV.row s ℓ i ∈ D ∧ i h = b := by
  simp [locR]

/-- (F2) A cycle containing both `f_s` and `t_s` has at least three vertices of `D`, or `D`
contains two rows of side `¬s` in that layer, with different bits at `h`. -/
lemma both_cases (hD : IsDominating (mdsGraph x y) D) {s ℓ : Bool} {h : Fin L}
    (h0 : MV.gad s ℓ h 0 ∈ D) (h1 : MV.gad s ℓ h 1 ∈ D) :
    3 ≤ cc D (ℓ, h) ∨ ∃ i i' : Idx L, MV.row (!s) ℓ i ∈ D ∧ MV.row (!s) ℓ i' ∈ D ∧
      i h = false ∧ i' h = true := by
  by_cases hc : cnt6 (locM D ℓ h) ≤ 2
  · right
    obtain ⟨hr0, hr1⟩ := loc_both _ _ s (locOk hD ℓ h) hc (locM_eq.2 h0) (locM_eq.2 h1)
    obtain ⟨i, hi, hih⟩ := locR_eq.1 hr0
    obtain ⟨i', hi', hi'h⟩ := locR_eq.1 hr1
    exact ⟨i, i', hi, hi', hih, hi'h⟩
  · left
    exact (by omega : 3 ≤ cnt6 (locM D ℓ h)).trans (cnt6_le_cc D ℓ h)

lemma row_ne_of_bit {s ℓ s' ℓ' : Bool} {i i' : Idx L} {h : Fin L} (hb : i h ≠ i' h) :
    MV.row s ℓ i ≠ MV.row s' ℓ' i' := by
  intro he
  simp only [MV.row.injEq] at he
  exact hb (by rw [he.2.2])

/-- `D` cannot avoid all rows of side `s` while containing a row of the other side. -/
lemma false_of_no_rows_side (hD : IsDominating (mdsGraph x y) D) (hcard : D.card ≤ 4 * L + 2)
    {s : Bool} (hno : ∀ ℓ i, MV.row s ℓ i ∉ D) {ℓ₀ : Bool} {i₀ : Idx L}
    (h₀ : MV.row (!s) ℓ₀ i₀ ∈ D) : False := by
  have hρE := ρ_add_exc hD hcard
  obtain ⟨h1, h10, h11⟩ := exists_both_of_no_rows hD hno false
  obtain ⟨h2, h20, h21⟩ := exists_both_of_no_rows hD hno true
  have hne : ((false, h1) : Bool × Fin L) ≠ (true, h2) := by simp
  have hρ1 : 1 ≤ ρ D := by
    simpa using ρ_ge (D := D) {MV.row (!s) ℓ₀ i₀} (by simp [h₀, MV.cyc])
  rcases both_cases hD h10 h11 with hc1 | ⟨i, i', hi, hi', hib, hi'b⟩ <;>
  rcases both_cases hD h20 h21 with hc2 | ⟨j, j', hj, hj', hjb, hj'b⟩
  · have := exc_ge_two (D := D) hne; omega
  · have hρ2 : 2 ≤ ρ D := by
      have := ρ_ge (D := D) {MV.row (!s) true j, MV.row (!s) true j'} (by simp [hj, hj', MV.cyc])
      rwa [card_pair (row_ne_of_bit (by rw [hjb, hj'b]; decide))] at this
    have := exc_ge_one (D := D) (false, h1); omega
  · have hρ2 : 2 ≤ ρ D := by
      have := ρ_ge (D := D) {MV.row (!s) false i, MV.row (!s) false i'} (by simp [hi, hi', MV.cyc])
      rwa [card_pair (row_ne_of_bit (by rw [hib, hi'b]; decide))] at this
    have := exc_ge_one (D := D) (true, h2); omega
  · have hρ4 : 4 ≤ ρ D := by
      have := ρ_ge (D := D) {MV.row (!s) false i, MV.row (!s) false i', MV.row (!s) true j,
        MV.row (!s) true j'} (by simp [hi, hi', hj, hj', MV.cyc])
      rwa [card_insert_of_notMem (by simp [MV.row.injEq]; intro h; rw [h] at hib; simp_all),
        card_insert_of_notMem (by simp), card_pair (row_ne_of_bit (by rw [hjb, hj'b]; decide))]
        at this
    omega

/-- `D` cannot avoid all rows. -/
lemma false_of_no_rows (hD : IsDominating (mdsGraph x y) D) (hcard : D.card ≤ 4 * L + 2)
    (hno : ∀ s ℓ i, MV.row s ℓ i ∉ D) : False := by
  have hρE := ρ_add_exc hD hcard
  obtain ⟨h1, h10, h11⟩ := exists_both_of_no_rows hD (hno true) false
  obtain ⟨h2, h20, h21⟩ := exists_both_of_no_rows hD (hno true) true
  obtain ⟨h3, h30, h31⟩ := exists_both_of_no_rows hD (hno false) false
  have c3 : ∀ {s ℓ h}, MV.gad s ℓ h 0 ∈ D → MV.gad s ℓ h 1 ∈ D → 3 ≤ cc D (ℓ, h) := by
    intro s ℓ h a b
    rcases both_cases hD a b with hc | ⟨i, -, hi, -⟩
    · exact hc
    · exact absurd hi (hno _ _ _)
  have hc1 := c3 h10 h11
  have hc2 := c3 h20 h21
  have hc3 := c3 h30 h31
  by_cases h13 : h1 = h3
  · subst h13
    have hc4 : 4 ≤ cc D (false, h1) :=
      (loc_four (locM D false h1) (locM_eq.2 h30) (locM_eq.2 h31) (locM_eq.2 h10)
        (locM_eq.2 h11)).trans (cnt6_le_cc D false h1)
    have := exc_ge_two (D := D) (p := (false, h1)) (q := (true, h2)) (by simp)
    omega
  · have := exc_ge_three (D := D) (p := (false, h1)) (q := (true, h2)) (r := (false, h3))
      (by simp) (by simp [h13]) (by simp)
    omega

section Unique

/-! Step 2: `D` contains exactly one row of each side, `lay s`/`idx s` is its layer/index, and every
cycle contains exactly two vertices of `D`. -/

variable (hD : IsDominating (mdsGraph x y) D) (lay : Bool → Bool) (idx : Bool → Idx L)
  (hU : ∀ s ℓ i, MV.row s ℓ i ∈ D ↔ ℓ = lay s ∧ i = idx s)
  (hcc : ∀ ℓ h, cnt6 (locM D ℓ h) ≤ 2)
include hD hU hcc

lemma notBoth (s ℓ : Bool) (h : Fin L) : ¬(MV.gad s ℓ h 0 ∈ D ∧ MV.gad s ℓ h 1 ∈ D) := by
  rintro ⟨h0, h1⟩
  obtain ⟨hr0, hr1⟩ := loc_both _ _ s (locOk hD ℓ h) (hcc ℓ h) (locM_eq.2 h0) (locM_eq.2 h1)
  obtain ⟨i, hi, hih⟩ := locR_eq.1 hr0
  obtain ⟨i', hi', hi'h⟩ := locR_eq.1 hr1
  rw [(hU _ _ _).1 hi |>.2] at hih
  rw [(hU _ _ _).1 hi' |>.2, hih] at hi'h
  exact Bool.false_ne_true hi'h

omit hcc in
/-- A row of side `s` in layer `ℓ` avoiding all gadget vertices of `D` is the row of `D`. -/
lemma eq_of_gadget_free {s ℓ : Bool} {i : Idx L} (hg : ∀ h, MV.gad s ℓ h (bitK (i h)) ∉ D)
    (hℓ : ℓ = lay s) : i = idx s := by
  by_contra hne
  have hnot : MV.row s ℓ i ∉ D := fun hm => hne ((hU _ _ _).1 hm).2
  obtain ⟨j, hj, -⟩ := row_needs_row hD hnot hg
  have := ((hU _ _ _).1 hj).1
  rw [← hℓ] at this
  cases ℓ <;> simp at this

lemma own_layer (s : Bool) (h : Fin L) :
    MV.gad s (lay s) h 0 ∈ D ∨ MV.gad s (lay s) h 1 ∈ D := by
  by_contra hcon
  simp only [not_or] at hcon
  have hnb := notBoth hD lay idx hU hcc s (lay s)
  set w := canonIdx D s (lay s)
  set w' := Function.update w h (!w h)
  have hw : ∀ h', MV.gad s (lay s) h' (bitK (w h')) ∉ D := canonIdx_not_mem hnb
  have hw' : ∀ h', MV.gad s (lay s) h' (bitK (w' h')) ∉ D := by
    intro h'
    by_cases hh : h' = h
    · subst hh
      cases hb : w' h' <;> simp [bitK, hcon.1, hcon.2]
    · simp only [w', Function.update_of_ne hh]
      exact hw h'
  have e1 := eq_of_gadget_free hD lay idx hU hw rfl
  have e2 := eq_of_gadget_free hD lay idx hU hw' rfl
  have : w h = w' h := by rw [e1, e2]
  simp [w'] at this

lemma idx_eq (s : Bool) : idx s = canonIdx D s (lay s) :=
  (eq_of_gadget_free hD lay idx hU (canonIdx_not_mem (notBoth hD lay idx hU hcc s (lay s))) rfl).symm

/-- In the layer of the row of side `s`, each cycle meets `D` in `{f_A, f_B}` or `{t_A, t_B}`. -/
lemma own_match (s : Bool) (h : Fin L) :
    (MV.gad false (lay s) h 0 ∈ D ↔ MV.gad true (lay s) h 0 ∈ D) ∧
      (MV.gad false (lay s) h 1 ∈ D ↔ MV.gad true (lay s) h 1 ∈ D) := by
  have key : locM D (lay s) h false 0 = locM D (lay s) h true 0 ∧
      locM D (lay s) h false 1 = locM D (lay s) h true 1 := by
    by_cases hl : lay (!s) = lay s
    · have hA := own_layer hD lay idx hU hcc s h
      have hB := own_layer hD lay idx hU hcc (!s) h
      rw [hl] at hB
      cases s
      · exact loc_match_both _ _ (locOk hD _ h) (hcc _ h) (hA.imp locM_eq.2 locM_eq.2)
          (hB.imp locM_eq.2 locM_eq.2)
      · exact loc_match_both _ _ (locOk hD _ h) (hcc _ h) (hB.imp locM_eq.2 locM_eq.2)
          (hA.imp locM_eq.2 locM_eq.2)
    · have hr : ∀ b, locR D (lay s) h (!s) b = false := by
        intro b
        rw [Bool.eq_false_iff]
        intro hb
        obtain ⟨i, hi, -⟩ := locR_eq.1 hb
        exact hl ((hU _ _ _).1 hi).1.symm
      exact loc_match_one _ _ s (locOk hD _ h) (hcc _ h)
        ((own_layer hD lay idx hU hcc s h).imp locM_eq.2 locM_eq.2) (hr false) (hr true)
  simp only [locM, decide_eq_decide] at key
  exact key

/-- The row of index `idx s` in the layer `lay s` of either side is not dominated by gadgets. -/
lemma gadget_free (s s' : Bool) (h : Fin L) : MV.gad s' (lay s) h (bitK (idx s h)) ∉ D := by
  have hnb := notBoth hD lay idx hU hcc s (lay s) h
  have hm := own_match hD lay idx hU hcc s h
  rw [idx_eq hD lay idx hU hcc s]
  by_cases hf : MV.gad s (lay s) h 0 ∈ D
  · have hc : canonIdx D s (lay s) h = true := by simp [canonIdx, hf]
    rw [hc]
    have ht : MV.gad s (lay s) h 1 ∉ D := fun ht => hnb ⟨hf, ht⟩
    simp only [bitK, ↓reduceIte]
    cases s <;> cases s' <;> simp_all
  · have hc : canonIdx D s (lay s) h = false := by simp [canonIdx, hf]
    rw [hc]
    simp only [bitK, Bool.false_eq_true, ↓reduceIte]
    cases s <;> cases s' <;> simp_all

lemma redge_of_unique : ∃ i j, x i j = true ∧ y i j = true := by
  by_cases hl : lay false = lay true
  · -- both rows in the same layer `ℓ`: same index, and the other layer is matched
    set ℓ := lay false
    have hpq : idx false = idx true := by
      rw [idx_eq hD lay idx hU hcc false, idx_eq hD lay idx hU hcc true, ← hl]
      funext h
      simp only [canonIdx, decide_eq_decide]
      exact (own_match hD lay idx hU hcc false h).1
    have hr : ∀ h s b, locR D (!ℓ) h s b = false := by
      intro h s b
      rw [Bool.eq_false_iff]
      intro hb
      obtain ⟨i, hi, -⟩ := locR_eq.1 hb
      have := ((hU _ _ _).1 hi).1
      cases s
      · exact absurd this (by simp [ℓ])
      · rw [← hl] at this; exact absurd this (by simp [ℓ])
    have hmn := fun h => loc_match_none _ _ (locOk hD (!ℓ) h) (hcc (!ℓ) h) (hr h)
    have hnb : ∀ h, ¬(MV.gad false (!ℓ) h 0 ∈ D ∧ MV.gad false (!ℓ) h 1 ∈ D) := fun h =>
      notBoth hD lay idx hU hcc false (!ℓ) h
    set w := canonIdx D false (!ℓ)
    have hwA : ∀ h, MV.gad false (!ℓ) h (bitK (w h)) ∉ D := canonIdx_not_mem hnb
    have hwB : ∀ h, MV.gad true (!ℓ) h (bitK (w h)) ∉ D := by
      intro h
      obtain ⟨e0, e1, -⟩ := hmn h
      simp only [locM, decide_eq_decide] at e0 e1
      have := hwA h
      cases hb : w h <;> simp only [bitK, hb, Bool.false_eq_true, ↓reduceIte] at this ⊢
      · rwa [← e0]
      · rwa [← e1]
    have hnotA : MV.row false (!ℓ) w ∉ D := fun hm => by
      have := ((hU _ _ _).1 hm).1; simp [ℓ] at this
    have hnotB : MV.row true (!ℓ) w ∉ D := fun hm => by
      have := ((hU _ _ _).1 hm).1; rw [← hl] at this; simp [ℓ] at this
    obtain ⟨j, hj, hej⟩ := row_needs_row hD hnotA hwA
    obtain ⟨j', hj', hej'⟩ := row_needs_row hD hnotB hwB
    rw [((hU _ _ _).1 hj).2] at hej
    rw [((hU _ _ _).1 hj').2, ← hpq] at hej'
    cases hℓ : ℓ
    · rw [hℓ] at hej hej'
      exact ⟨idx false, w, by simpa [redge, xy] using hej, by simpa [redge, xy] using hej'⟩
    · rw [hℓ] at hej hej'
      exact ⟨w, idx false, by simpa [redge, xy] using hej, by simpa [redge, xy] using hej'⟩
  · -- rows in different layers: the B-row of index `p` in `A`'s layer and vice versa
    have hlB : lay true = !lay false := by
      cases h1 : lay false <;> cases h2 : lay true <;> simp_all
    have hnotB : MV.row true (lay false) (idx false) ∉ D := fun hm => by
      have := ((hU _ _ _).1 hm).1; exact hl this
    have hnotA : MV.row false (lay true) (idx true) ∉ D := fun hm => by
      have := ((hU _ _ _).1 hm).1; exact hl this.symm
    obtain ⟨j, hj, hej⟩ := row_needs_row hD hnotB (gadget_free hD lay idx hU hcc false true)
    obtain ⟨j', hj', hej'⟩ := row_needs_row hD hnotA (gadget_free hD lay idx hU hcc true false)
    rw [((hU _ _ _).1 hj).2] at hej
    rw [((hU _ _ _).1 hj').2] at hej'
    rw [hlB] at hej'
    cases hℓ : lay false
    · rw [hℓ] at hej hej'
      exact ⟨idx false, idx true, by simpa [redge, xy] using hej', by simpa [redge, xy] using hej⟩
    · rw [hℓ] at hej hej'
      exact ⟨idx true, idx false, by simpa [redge, xy] using hej', by simpa [redge, xy] using hej⟩

end Unique

variable (hD : IsDominating (mdsGraph x y) D) (hcard : D.card ≤ 4 * L + 2)
include hD hcard

/-- Step 1: a dominating set of size `≤ 4 log k + 2` contains a row of each side. -/
lemma exists_rows (s : Bool) : ∃ ℓ i, MV.row s ℓ i ∈ D := by
  by_contra hno
  simp only [not_exists] at hno
  by_cases hB : ∃ ℓ i, MV.row (!s) ℓ i ∈ D
  · obtain ⟨ℓ, i, hi⟩ := hB
    exact false_of_no_rows_side hD hcard hno hi
  · simp only [not_exists] at hB
    refine false_of_no_rows hD hcard fun s' => ?_
    cases s <;> cases s' <;> simp_all

lemma two_le_ρ : 2 ≤ ρ D := by
  obtain ⟨ℓA, p, hA⟩ := exists_rows hD hcard false
  obtain ⟨ℓB, q, hB⟩ := exists_rows hD hcard true
  have := ρ_ge (D := D) {MV.row false ℓA p, MV.row true ℓB q} (by simp [hA, hB, MV.cyc])
  rwa [card_pair (by simp)] at this

/-- The converse direction of Lemma 2.1: a dominating set of size at most `4 log k + 2` forces
an index `(i, j)` with `x(i, j) = y(i, j) = 1`. -/
theorem not_disj_of_isDominating : ∃ i j, x i j = true ∧ y i j = true := by
  have hρE := ρ_add_exc hD hcard
  have hρ2 := two_le_ρ hD hcard
  obtain ⟨ℓA, p, hA⟩ := exists_rows hD hcard false
  obtain ⟨ℓB, q, hB⟩ := exists_rows hD hcard true
  have hcc : ∀ ℓ h, cnt6 (locM D ℓ h) ≤ 2 := fun ℓ h => by
    have h1 := exc_ge_one (D := D) (ℓ, h)
    have h2 := cnt6_le_cc D ℓ h
    omega
  let lay : Bool → Bool := fun s => if s then ℓB else ℓA
  let idx : Bool → Idx L := fun s => if s then q else p
  have hU : ∀ s ℓ i, MV.row s ℓ i ∈ D ↔ ℓ = lay s ∧ i = idx s := by
    intro s ℓ i
    constructor
    · intro hm
      by_contra hne
      have h1 : MV.row s ℓ i ≠ MV.row false ℓA p := by
        intro he; simp only [MV.row.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he; exact hne ⟨rfl, rfl⟩
      have h2 : MV.row s ℓ i ≠ MV.row true ℓB q := by
        intro he; simp only [MV.row.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he; exact hne ⟨rfl, rfl⟩
      have := ρ_ge (D := D) {MV.row s ℓ i, MV.row false ℓA p, MV.row true ℓB q}
        (by simp [hm, hA, hB, MV.cyc])
      rw [card_insert_of_notMem (by simp [h1, h2]), card_pair (by simp)] at this
      omega
    · rintro ⟨rfl, rfl⟩
      cases s
      · exact hA
      · exact hB
  exact redge_of_unique hD lay idx hU hcc

end Converse

/-- Every dominating set of `G_{x,y}` has at least `4 log k + 2` vertices. -/
theorem four_mul_add_two_le_card {D : Finset (MV L)} (hD : IsDominating (mdsGraph x y) D) :
    4 * L + 2 ≤ D.card := by
  by_contra hlt
  have hcard : D.card ≤ 4 * L + 2 := by omega
  have := ρ_add_exc hD hcard
  have h2 := two_le_ρ hD hcard
  have := card_eq_ρ_add D
  have hsum : 4 * L ≤ ∑ p : Bool × Fin L, cc D p := by
    calc 4 * L = ∑ _p : Bool × Fin L, 2 := by simp [card_univ, Fintype.card_prod]; ring
      _ ≤ _ := sum_le_sum fun p _ => two_le_cc hD p
  omega

/-- **Lemma 2.1** (`≤` form): `G_{x,y}` has a dominating set of size at most `4 log k + 2` iff
`DISJ_{k²}(x, y) = FALSE`. -/
theorem lemma_2_1_le :
    (∃ D : Finset (MV L), IsDominating (mdsGraph x y) D ∧ D.card ≤ 4 * L + 2) ↔
      ∃ i j, x i j = true ∧ y i j = true := by
  constructor
  · rintro ⟨D, hD, hcard⟩
    exact not_disj_of_isDominating hD hcard
  · rintro ⟨i, j, hx, hy⟩
    exact ⟨canonDS i j, isDominating_canonDS x y hx hy, (card_canonDS i j).le⟩

/-- **Lemma 2.1.** Given `x, y ∈ {0,1}^{k²}`, the graph `G_{x,y}` has a dominating set of size
`4 log k + 2` iff `DISJ_{k²}(x, y) = FALSE`. -/
theorem lemma_2_1 :
    (∃ D : Finset (MV L), IsDominating (mdsGraph x y) D ∧ D.card = 4 * L + 2) ↔
      ∃ i j, x i j = true ∧ y i j = true := by
  constructor
  · rintro ⟨D, hD, hcard⟩
    exact not_disj_of_isDominating hD hcard.le
  · rintro ⟨i, j, hx, hy⟩
    exact ⟨canonDS i j, isDominating_canonDS x y hx hy, card_canonDS i j⟩

end HardnessOptimization
