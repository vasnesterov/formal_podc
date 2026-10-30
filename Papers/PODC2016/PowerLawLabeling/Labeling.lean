import Papers.PODC2016.PowerLawLabeling.Counting

/-!
# The labeling schemes (Theorems 1, 2) and the sparse lower bound (Proposition 4)

The fat/thin threshold scheme: a label is one fat/thin bit, an identifier of `lg n` bits, and
either the identifiers of all neighbours (thin vertex, degree `< f`) or a bit string over the fat
vertices (fat vertex, degree `≥ f`).
-/

namespace Podc.PowerLawLabeling

open Finset

namespace Scheme

/-! ### Bit strings and the decoder -/

/-- The `L` low bits of `x`. -/
def bits (L x : ℕ) : List Bool := List.ofFn fun i : Fin L => x.testBit i

@[simp] lemma length_bits (L x : ℕ) : (bits L x).length = L := by simp [bits]

lemma bits_inj {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L) (h : bits L x = bits L y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < L
  · have := congrFun (List.ofFn_injective h) ⟨i, hi⟩
    simpa using this
  · push Not at hi
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hi))]

lemma flatten_inj {α : Type*} {L : ℕ} (hL : 0 < L) : ∀ {l₁ l₂ : List (List α)},
    (∀ w ∈ l₁, w.length = L) → (∀ w ∈ l₂, w.length = L) → l₁.flatten = l₂.flatten → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: l₂, _, h₂, h => by
      have := congrArg List.length h
      simp [h₂ b (by simp)] at this
      omega
  | a :: l₁, [], h₁, _, h => by
      have := congrArg List.length h
      simp [h₁ a (by simp)] at this
      omega
  | a :: l₁, b :: l₂, h₁, h₂, h => by
      simp only [List.flatten_cons] at h
      obtain ⟨hab, h'⟩ := List.append_inj h (by rw [h₁ a (by simp), h₂ b (by simp)])
      rw [hab, flatten_inj hL (fun w hw => h₁ w (by simp [hw])) (fun w hw => h₂ w (by simp [hw])) h']

/-- Thin test: `a` is a thin label (flag `false`) whose list of neighbour identifiers contains
the identifier of `b`. -/
def thinT (L : ℕ) (a b : List Bool) : Prop :=
  ∃ (x : List Bool) (ws : List (List Bool)), a = false :: (x ++ ws.flatten) ∧ x.length = L ∧ (∀ w ∈ ws, w.length = L) ∧
    ∃ w ∈ ws, ∃ c t, b = c :: (w ++ t)

/-- Fat test: both labels are fat (flag `true`) and the bit of `a` at the identifier of `b`
is set. -/
def fatT (L : ℕ) (a b : List Bool) : Prop :=
  ∃ x s y t, a = true :: (x ++ s) ∧ b = true :: (y ++ t) ∧ x.length = L ∧ y.length = L ∧
    ∃ j < 2 ^ L, y = bits L j ∧ s.getD j false = true

/-- The decoder of the threshold scheme (it depends only on `L = lg n`). -/
def dec (L : ℕ) (a b : List Bool) : Prop := thinT L a b ∨ thinT L b a ∨ fatT L a b

/-! ### Degrees -/

lemma deg_eq_degree_aux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    deg G v = G.degree v := by
  unfold deg
  rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

lemma deg_lt_aux {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : deg G v < n := by
  classical
  rw [deg_eq_degree_aux]
  simpa using G.degree_lt_card_verts v

lemma card_fat_mul_le {n : ℕ} (G : SimpleGraph (Fin n)) (f : ℕ) :
    #{w | f ≤ deg G w} * f ≤ 2 * G.edgeSet.ncard := by
  classical
  calc #{w | f ≤ deg G w} * f = ∑ w ∈ univ.filter (fun w => f ≤ deg G w), f := by simp
    _ ≤ ∑ w ∈ univ.filter (fun w => f ≤ deg G w), deg G w :=
        sum_le_sum fun w hw => (mem_filter.1 hw).2
    _ ≤ ∑ w, deg G w := sum_le_sum_of_subset (filter_subset _ _)
    _ = ∑ w, G.degree w := by simp only [deg_eq_degree_aux]
    _ = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
    _ = 2 * G.edgeSet.ncard := by rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]

/-! ### The encoder -/

variable {n : ℕ} (G : SimpleGraph (Fin n)) (f : ℕ)

/-- The fat vertices: degree at least `f`. -/
noncomputable def fat : Finset (Fin n) := {v | f ≤ deg G v}

/-- Identifiers: the fat vertices get `0, …, k-1`, the thin ones `k, …, n-1`. -/
noncomputable def ident (v : Fin n) : ℕ :=
  if h : v ∈ fat G f then ((fat G f).equivFin ⟨v, h⟩ : ℕ)
  else #(fat G f) + ((fat G f)ᶜ.equivFin ⟨v, mem_compl.2 h⟩ : ℕ)

lemma ident_of_mem {v : Fin n} (h : v ∈ fat G f) :
    ident G f v = ((fat G f).equivFin ⟨v, h⟩ : ℕ) := by
  simp [ident, h]

lemma ident_of_not_mem {v : Fin n} (h : v ∉ fat G f) :
    ident G f v = #(fat G f) + ((fat G f)ᶜ.equivFin ⟨v, mem_compl.2 h⟩ : ℕ) := by
  simp [ident, h]

lemma ident_lt_card {v : Fin n} (h : v ∈ fat G f) : ident G f v < #(fat G f) := by
  rw [ident_of_mem _ _ h]; exact Fin.isLt _

lemma ident_lt (v : Fin n) : ident G f v < n := by
  by_cases h : v ∈ fat G f
  · exact lt_of_lt_of_le (ident_lt_card G f h) (by simpa using card_le_univ (fat G f))
  · rw [ident_of_not_mem _ _ h]
    have := Fin.isLt ((fat G f)ᶜ.equivFin ⟨v, mem_compl.2 h⟩)
    have h2 := card_add_card_compl (fat G f)
    simp only [Fintype.card_fin] at h2
    omega

lemma ident_lt_pow (v : Fin n) : ident G f v < 2 ^ lg n :=
  lt_of_lt_of_le (ident_lt G f v) (Nat.le_pow_clog (by norm_num) n)

lemma ident_injective : Function.Injective (ident G f) := by
  intro u v huv
  by_cases hu : u ∈ fat G f <;> by_cases hv : v ∈ fat G f
  · rw [ident_of_mem _ _ hu, ident_of_mem _ _ hv] at huv
    exact congrArg Subtype.val ((fat G f).equivFin.injective (Fin.ext huv))
  · have := ident_lt_card G f hu
    rw [ident_of_not_mem _ _ hv] at huv
    omega
  · have := ident_lt_card G f hv
    rw [ident_of_not_mem _ _ hu] at huv
    omega
  · rw [ident_of_not_mem _ _ hu, ident_of_not_mem _ _ hv] at huv
    have : (fat G f)ᶜ.equivFin ⟨u, mem_compl.2 hu⟩ = (fat G f)ᶜ.equivFin ⟨v, mem_compl.2 hv⟩ :=
      Fin.ext (by omega)
    exact congrArg Subtype.val ((fat G f)ᶜ.equivFin.injective this)

open Classical in
/-- The neighbours of `v`, as a list. -/
noncomputable def nbrs (v : Fin n) : List (Fin n) := (univ.filter (G.Adj v)).toList

lemma mem_nbrs {v w : Fin n} : w ∈ nbrs G v ↔ G.Adj v w := by
  classical
  simp [nbrs]

lemma length_nbrs (v : Fin n) : (nbrs G v).length = deg G v := by
  classical
  rw [nbrs, length_toList, deg]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext w
  simp

open Classical in
/-- The bit string of a fat vertex: adjacency to the fat vertices, indexed by identifier. -/
noncomputable def fatVec (v : Fin n) : List Bool :=
  List.ofFn fun j : Fin #(fat G f) => decide (∃ w, ident G f w = j ∧ G.Adj v w)

/-- The concatenated identifiers of the neighbours. -/
noncomputable def thinWs (v : Fin n) : List (List Bool) :=
  (nbrs G v).map fun w => bits (lg n) (ident G f w)

noncomputable def body (v : Fin n) : List Bool :=
  if v ∈ fat G f then fatVec G f v else (thinWs G f v).flatten

/-- The label of `v`: fat/thin flag, identifier, body. -/
noncomputable def label (v : Fin n) : List Bool :=
  decide (v ∈ fat G f) :: (bits (lg n) (ident G f v) ++ body G f v)

lemma length_thinWs (v : Fin n) : (thinWs G f v).flatten.length = deg G v * lg n := by
  rw [← length_nbrs G v, thinWs]
  generalize nbrs G v = l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.flatten_cons, List.length_append, length_bits,
      ih, List.length_cons]; ring

lemma length_label (v : Fin n) : (label G f v).length =
    1 + lg n + (if f ≤ deg G v then #{w | f ≤ deg G w} else deg G v * lg n) := by
  have hm : v ∈ fat G f ↔ f ≤ deg G v := by simp [fat]
  simp only [label, body, List.length_cons, List.length_append, length_bits]
  by_cases h : v ∈ fat G f
  · simp only [h, hm.1 h, ↓reduceIte]
    rw [fatVec, List.length_ofFn, fat]; ring
  · have h' : ¬ f ≤ deg G v := fun h' => h (hm.2 h')
    simp only [h, h', ↓reduceIte, length_thinWs]; ring

lemma thinT_of_adj {u v : Fin n} (hu : u ∉ fat G f) (h : G.Adj u v) :
    thinT (lg n) (label G f u) (label G f v) := by
  refine ⟨bits (lg n) (ident G f u), thinWs G f u, ?_, length_bits _ _, ?_,
    bits (lg n) (ident G f v), ?_, decide (v ∈ fat G f), body G f v, rfl⟩
  · simp [label, body, hu]
  · intro w hw
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hw
    exact length_bits _ _
  · exact List.mem_map.2 ⟨v, (mem_nbrs G).2 h, rfl⟩

lemma adj_of_thinT (hL : 0 < lg n) {u v : Fin n} (h : thinT (lg n) (label G f u) (label G f v)) :
    G.Adj u v := by
  obtain ⟨x, ws, ha, hx, hws, w, hw, c, t, hb⟩ := h
  simp only [label, List.cons.injEq] at ha hb
  obtain ⟨hu, ha⟩ := ha
  have hu' : u ∉ fat G f := by simpa using hu
  obtain ⟨-, ha⟩ := List.append_inj ha (by rw [hx, length_bits])
  simp only [body, hu', ↓reduceIte] at ha
  have hws' := flatten_inj hL (fun w hw => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hw; exact length_bits _ _) hws ha
  rw [← hws'] at hw
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hw
  obtain ⟨hb, -⟩ := List.append_inj hb.2 (by rw [length_bits, length_bits])
  have := ident_injective G f (bits_inj (ident_lt_pow G f v) (ident_lt_pow G f z) hb)
  subst this
  exact (mem_nbrs G).1 hz

lemma fatT_of_adj {u v : Fin n} (hu : u ∈ fat G f) (hv : v ∈ fat G f) (h : G.Adj u v) :
    fatT (lg n) (label G f u) (label G f v) := by
  classical
  refine ⟨bits (lg n) (ident G f u), fatVec G f u, bits (lg n) (ident G f v), fatVec G f v,
    by simp [label, body, hu], by simp [label, body, hv], length_bits _ _, length_bits _ _,
    ident G f v, ident_lt_pow G f v, rfl, ?_⟩
  have hlt := ident_lt_card G f hv
  rw [fatVec, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hlt, Option.getD_some, dite_true]
  exact decide_eq_true ⟨v, rfl, h⟩

lemma adj_of_fatT {u v : Fin n} (h : fatT (lg n) (label G f u) (label G f v)) : G.Adj u v := by
  obtain ⟨x, s, y, t, ha, hb, hx, hy, j, hj, rfl, hs⟩ := h
  simp only [label, List.cons.injEq] at ha hb
  have hu : u ∈ fat G f := by simpa using ha.1
  have hv : v ∈ fat G f := by simpa using hb.1
  obtain ⟨-, ha⟩ := List.append_inj ha.2 (by rw [hx, length_bits])
  obtain ⟨hb, -⟩ := List.append_inj hb.2 (by rw [hy, length_bits])
  have := bits_inj (ident_lt_pow G f v) hj hb
  subst this
  simp only [body, hu, ↓reduceIte] at ha
  rw [← ha] at hs
  have hlt := ident_lt_card G f hv
  classical
  rw [fatVec, List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hs
  simp only [hlt, Option.getD_some, dite_true, decide_eq_true_eq] at hs
  obtain ⟨w, hw, hadj⟩ := hs
  rwa [ident_injective G f hw] at hadj

end Scheme

open Scheme in
/-- The fat/thin threshold scheme (Section 3): for `n ≥ 2` there is a single decoder such that
every graph on `Fin n` and every threshold `f` admit labels of length
`1 + lg n + (#fat if fat, deg · lg n if thin)`. -/
theorem exists_threshold_scheme (n : ℕ) (hn : 2 ≤ n) : ∃ D : List Bool → List Bool → Prop,
    ∀ (G : SimpleGraph (Fin n)) (f : ℕ), ∃ lab : Fin n → List Bool,
      (∀ v, (lab v).length =
        1 + lg n + (if f ≤ deg G v then #{w | f ≤ deg G w} else deg G v * lg n)) ∧
      ∀ u v, u ≠ v → (G.Adj u v ↔ D (lab u) (lab v)) := by
  have hL : 0 < lg n := Nat.clog_pos (by norm_num) (by omega)
  refine ⟨dec (lg n), fun G f => ⟨label G f, length_label G f, fun u v _ => ⟨fun h => ?_, ?_⟩⟩⟩
  · by_cases hu : u ∈ fat G f
    · by_cases hv : v ∈ fat G f
      · exact Or.inr (Or.inr (fatT_of_adj G f hu hv h))
      · exact Or.inr (Or.inl (thinT_of_adj G f hv h.symm))
    · exact Or.inl (thinT_of_adj G f hu h)
  · rintro (h | h | h)
    · exact adj_of_thinT G f hL h
    · exact (adj_of_thinT G f hL h).symm
    · exact adj_of_fatT G f h

/-- A threshold scheme with fat count and thin neighbour-list length bounded by `B` gives labels
of `1 + lg n + B` bits. -/
theorem hasAdjLabeling_of_threshold {n : ℕ} (hn : 2 ≤ n) {F : SimpleGraph (Fin n) → Prop}
    {B X : ℝ} (hX : 1 + lg n + B ≤ X)
    (hF : ∀ G, F G → ∃ f : ℕ, (#{w | f ≤ deg G w} : ℝ) ≤ B ∧
      ∀ v, deg G v < f → (deg G v : ℝ) * lg n ≤ B) :
    HasAdjLabeling n F X := by
  obtain ⟨D, hD⟩ := exists_threshold_scheme n hn
  refine ⟨D, fun G hG => ?_⟩
  obtain ⟨f, hk, hthin⟩ := hF G hG
  obtain ⟨lab, hlen, hadj⟩ := hD G f
  refine ⟨lab, fun v => ?_, hadj⟩
  rw [hlen v]
  split_ifs with h
  · push_cast; linarith
  · push_cast; linarith [hthin v (by omega)]

lemma Scheme.le_of_lt_max {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (h : d < max 1 ⌈x⌉₊) : (d : ℝ) ≤ x := by
  by_cases hd : d = 0
  · simp [hd, hx]
  · have : d < ⌈x⌉₊ := by omega
    exact le_of_lt (Nat.lt_ceil.1 this)


/-- **Theorem 1.** There is a `√(2cn log n) + 2 log n + 1` adjacency labeling scheme for the
`c`-sparse graphs `S_{c,n}` (`log n = ⌈log₂ n⌉`). -/
theorem theorem1 (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    HasAdjLabeling n (Sparse c) (Real.sqrt (2 * c * n * lg n) + 2 * lg n + 1) := by
  rcases lt_or_ge n 2 with hn | hn
  · refine ⟨fun _ _ => False, fun G _ => ⟨fun _ => [], fun v => ?_, fun u v huv => ?_⟩⟩
    · simp only [List.length_nil, Nat.cast_zero]; positivity
    · exact absurd (Fin.ext (by omega)) huv
  have hL : 0 < lg n := Nat.clog_pos (by norm_num) (by omega)
  set L := lg n
  set B := Real.sqrt (2 * c * n * L)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hBsq : B ^ 2 = 2 * c * n * L := Real.sq_sqrt (by positivity)
  set x := B / L
  have hx0 : 0 ≤ x := div_nonneg hB0 hLpos.le
  have hxL : x * L = B := div_mul_cancel₀ _ hLpos.ne'
  refine hasAdjLabeling_of_threshold hn (B := B) (by linarith) fun G hG =>
    ⟨max 1 ⌈x⌉₊, ?_, fun v hv => ?_⟩
  · have h1 := Scheme.card_fat_mul_le G (max 1 ⌈x⌉₊)
    have hG' : (G.edgeSet.ncard : ℝ) ≤ c * n := by simpa [Sparse] using hG
    set k := #{w | max 1 ⌈x⌉₊ ≤ deg G w}
    have hfx : x ≤ ((max 1 ⌈x⌉₊ : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil x) (by exact_mod_cast le_max_right _ _)
    have hf1 : (1 : ℝ) ≤ ((max 1 ⌈x⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have h2 : (k : ℝ) * ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ 2 * c * n := by
      have : ((k * max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ ((2 * G.edgeSet.ncard : ℕ) : ℝ) := by
        exact_mod_cast h1
      simp only [Nat.cast_mul, Nat.cast_ofNat] at this; linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have h3 : (k : ℝ) * x ≤ 2 * c * n := le_trans (mul_le_mul_of_nonneg_left hfx hk0) h2
    have h4 : (k : ℝ) * B ≤ B ^ 2 := by
      rw [hBsq, ← hxL, ← mul_assoc]; exact mul_le_mul_of_nonneg_right h3 hLpos.le
    rcases hB0.lt_or_eq with hBpos | hB
    · nlinarith
    · have h5 : 2 * c * n * L = 0 := by rw [← hBsq, ← hB]; ring
      have h6 : 2 * c * n = 0 := by
        rcases mul_eq_zero.1 h5 with h | h
        · exact h
        · exact absurd h hLpos.ne'
      rw [← hB]; nlinarith
  · rw [← hxL]; exact mul_le_mul_of_nonneg_right (Scheme.le_of_lt_max hx0 hv) hLpos.le

/-- **Theorem 2.** There is a `(C' n)^{1/α} (log n)^{1-1/α} + 2 log n + 1` adjacency labeling
scheme for `P_α` (with constant `C' ≥ 2`; the paper's `C'` is at least `5^α`). -/
theorem theorem2 (α C' : ℝ) (hα : 1 < α) (hC' : 2 ≤ C') (n : ℕ) (hn : 2 ≤ n) :
    HasAdjLabeling n (IsPowerLaw α C')
      ((C' * n) ^ (1 / α) * (lg n : ℝ) ^ (1 - 1 / α) + 2 * lg n + 1) := by
  have hL : 0 < lg n := Nat.clog_pos (by norm_num) (by omega)
  have hL2 : 2 ^ (lg n).pred < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  set L := lg n
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hCn : 0 < C' * n := by positivity
  set B := (C' * n) ^ (1 / α) * (L : ℝ) ^ (1 - 1 / α)
  have hB0 : 0 ≤ B := by positivity
  set x := (C' * n / L) ^ (1 / α)
  have hx0 : 0 < x := Real.rpow_pos_of_pos (div_pos hCn hLpos) _
  have hxα : x ^ α = C' * n / L := by
    rw [← Real.rpow_mul (div_pos hCn hLpos).le, one_div_mul_cancel (by linarith), Real.rpow_one]
  have hxL : x * L = B := by
    simp only [x, B]
    rw [Real.div_rpow hCn.le hLpos.le, Real.rpow_sub hLpos, Real.rpow_one]
    have : (0 : ℝ) < (L : ℝ) ^ (1 / α) := by positivity
    field_simp
  -- `L ≤ C' log₂ n`
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 n :=
    (Real.le_logb_iff_rpow_le (by norm_num) hn0).2 (by simpa using (show (2 : ℝ) ≤ n by exact_mod_cast hn))
  have hlogL : ((L.pred : ℕ) : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hn0, Real.rpow_natCast]
    exact_mod_cast hL2.le
  have hLC : (L : ℝ) ≤ C' * Real.logb 2 n := by
    have : (L : ℝ) = ((L.pred : ℕ) : ℝ) + 1 := by
      rw [← Nat.cast_succ, Nat.succ_pred_eq_of_pos hL]
    nlinarith
  refine hasAdjLabeling_of_threshold hn (B := B) (by linarith) fun G hG =>
    ⟨max 1 ⌈x⌉₊, ?_, fun v hv => ?_⟩
  · set f := max 1 ⌈x⌉₊
    by_cases hfn : f ≤ n - 1
    · have hfx : x ≤ (f : ℝ) := le_trans (Nat.le_ceil x) (by exact_mod_cast le_max_right _ _)
      have hf1 : 1 ≤ f := le_max_left _ _
      have hfpos : (0 : ℝ) < f := by exact_mod_cast hf1
      have hthr : ((n : ℝ) / Real.logb 2 n) ^ (1 / α) ≤ f := by
        refine le_trans (Real.rpow_le_rpow (by positivity) ?_ (by positivity)) hfx
        rw [div_le_div_iff₀ (by linarith) hLpos]
        nlinarith
      have hPL := hG f hf1 (by simp only [Fintype.card_fin]; exact hthr)
        (by simp only [Fintype.card_fin]; exact hfn)
      simp only [Fintype.card_fin] at hPL
      set k := #{w | f ≤ deg G w} with hkdef
      have hk : k ≤ ∑ i ∈ Icc f (n - 1), numDeg G i := by
        classical
        rw [hkdef, Finset.card_eq_sum_card_fiberwise (f := deg G) (t := Icc f (n - 1))]
        · refine Finset.sum_le_sum fun i _ => Finset.card_le_card ?_
          intro w hw
          simp only [mem_filter, mem_univ, true_and] at hw ⊢
          exact hw.2
        · intro w hw
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_Icc,
            Set.mem_Icc] at hw ⊢
          exact ⟨hw, by have := Scheme.deg_lt_aux G w; omega⟩
      have h1 : (k : ℝ) ≤ C' * (n / (f : ℝ) ^ (α - 1)) := le_trans (by exact_mod_cast hk) hPL
      have hfα : (0 : ℝ) < (f : ℝ) ^ (α - 1) := by positivity
      have h2 : (k : ℝ) * (f : ℝ) ^ (α - 1) ≤ C' * n := by
        rw [mul_div_assoc', le_div_iff₀ hfα] at h1; exact h1
      have h3 : (k : ℝ) * x ^ (α - 1) ≤ C' * n :=
        le_trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hx0.le hfx (by linarith)) (Nat.cast_nonneg _)) h2
      have h4 : x ^ α = x ^ (α - 1) * x := by
        rw [← Real.rpow_add_one hx0.ne', sub_add_cancel]
      have h5 : (k : ℝ) * (C' * n / L) ≤ C' * n * x := by
        rw [← hxα, h4, ← mul_assoc]; exact mul_le_mul_of_nonneg_right h3 hx0.le
      have h6 : (k : ℝ) * (C' * n) ≤ (x * L) * (C' * n) := by
        rw [mul_div_assoc', div_le_iff₀ hLpos] at h5; linarith
      rw [← hxL]
      exact le_of_mul_le_mul_right h6 hCn
    · have : #{w | f ≤ deg G w} = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro w _
        have := Scheme.deg_lt_aux G w
        omega
      rw [this]; simpa using hB0
  · rw [← hxL]; exact mul_le_mul_of_nonneg_right (Scheme.le_of_lt_max hx0.le hv) hLpos.le

/-- **Proposition 4.** Any adjacency labeling scheme for `S_{c,n}` needs labels of at least
`⌊√(cn)/2⌋` bits — under the extra hypothesis `c < n` (see `prop4_false`). -/
theorem prop4 (c : ℝ) (hc : 0 < c) (n : ℕ) (hcn : c < n) {X : ℝ}
    (h : HasAdjLabeling n (Sparse c) X) : (⌊Real.sqrt (c * n) / 2⌋₊ : ℝ) ≤ X := by
  have hn0 : (0 : ℝ) < n := hc.trans hcn
  set s := Real.sqrt (c * n)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsn : s < n := by
    rw [show (n : ℝ) = Real.sqrt (n * n) from (Real.sqrt_mul_self (Nat.cast_nonneg n)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (mul_lt_mul_of_pos_right hcn hn0)
  set q := ⌊s⌋₊
  have hqn : q + 1 ≤ n := by have := (Nat.floor_lt hs0).2 hsn; omega
  have hm : HasAdjLabeling (q + 1) (fun _ => True) X := by
    refine h.of_embedding fun H _ =>
      ⟨H.map (Fin.castLEEmb hqn), ?_, ⟨SimpleGraph.Embedding.map _ H⟩⟩
    classical
    unfold Sparse
    rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _
      (Fin.castLEEmb hqn).sym2Map.injective, Fintype.card_fin,
      ← H.coe_edgeFinset, Set.ncard_coe_finset]
    have h1 : #H.edgeFinset ≤ q * q := by
      refine le_trans H.card_edgeFinset_le_card_choose_two ?_
      rw [Fintype.card_fin, Nat.choose_two_right]
      rw [Nat.add_sub_cancel]; exact Nat.div_le_of_le_mul (by nlinarith)
    have h2 : (q : ℝ) * q ≤ c * n := by
      rw [← Real.mul_self_sqrt (by positivity : 0 ≤ c * n)]
      exact mul_self_le_mul_self (Nat.cast_nonneg _) (Nat.floor_le hs0)
    calc (#H.edgeFinset : ℝ) ≤ ((q * q : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ c * n := by push_cast; exact h2
  have := moon (by omega) hm
  rw [Nat.add_sub_cancel] at this
  rw [Nat.floor_div_ofNat]
  exact this

/-- Proposition 4 fails when `c` is large compared to `n`: for `n = 2`, `c = 100` one bit
suffices, while `⌊√(cn)/2⌋ = 7`. -/
theorem prop4_false :
    HasAdjLabeling 2 (Sparse 100) 1 ∧ (1 : ℝ) < ⌊Real.sqrt (100 * 2) / 2⌋₊ := by
  classical
  refine ⟨⟨fun a b => a = [true] ∨ b = [true], fun G _ =>
    ⟨fun v => if v = 0 then [] else [decide (G.Adj 0 1)], fun v => ?_, fun u v huv => ?_⟩⟩, ?_⟩
  · dsimp only; split_ifs <;> simp
  · fin_cases u <;> fin_cases v
    · exact absurd rfl huv
    · simp
    · simp [G.adj_comm 1 0]
    · exact absurd rfl huv
  · have h14 : (14 : ℝ) ≤ Real.sqrt (100 * 2) := Real.le_sqrt_of_sq_le (by norm_num)
    have h7 : ((7 : ℕ) : ℝ) ≤ Real.sqrt (100 * 2) / 2 := by
      calc ((7 : ℕ) : ℝ) = 14 / 2 := by norm_num
        _ ≤ Real.sqrt (100 * 2) / 2 := div_le_div_of_nonneg_right h14 (by norm_num)
    have : 7 ≤ ⌊Real.sqrt (100 * 2) / 2⌋₊ := Nat.le_floor h7
    exact_mod_cast (by omega : 1 < ⌊Real.sqrt (100 * 2) / 2⌋₊)

end Podc.PowerLawLabeling
