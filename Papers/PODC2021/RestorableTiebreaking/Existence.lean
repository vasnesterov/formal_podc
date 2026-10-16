import Papers.PODC2021.RestorableTiebreaking.Theorem19

/-!
# Existence of antisymmetric tiebreaking weights (Theorems 20, 23) and the main result (Theorem 2)

Bodwin–Parter, PODC 2021, Sections 3.1–3.2.

Weights are of the form `r(u, v) = sgn(u, v) · ρ({u, v})` for a function `ρ : Sym2 V → ℝ` on
unordered pairs and `sgn(u, v) = +1` if `u < v`, `-1` otherwise (for a fixed linear order on `V`);
such `r` are antisymmetric by construction (`rOf`).

* `hasMinWalks_of_generic` — small perturbations (`|r| ≤ ε`, `(2n - 1) ε < 1`) never make a
  non-shortest walk shortest; if moreover distinct shortest walks get distinct weights, `G* \ A`
  has unique shortest walks.
* `dwt_sub_dwt_eq_sum` / `generic_of_coeff` — the weight difference of two distinct shortest
  `s ⇝ t` walks of `G \ A` is `∑ₑ cₑ ρ(e)` for a nonzero coefficient vector `c ∈ {-1, 0, 1}^E`.
* `theorem23` — the deterministic weights `ρ(e) = 2^{-i(e)} / (2n)` (IDs `i(e) ∈ {1, …, N}`)
  form an ATW function for every `f`.
* `theorem20` — for `ρ` uniform on `[-ε, ε]^{Sym2 V}` with `ε < 1/(2n)`, `rOf ρ` is an ATW
  function for every `f` with probability 1.
* `theorem2` — every finite graph has a single scheme that is, for every `f`, an `f`-RPTS which is
  consistent, stable and `f`-restorable; `theorem2_single` is the paper's one-fault phrasing.
-/

open Finset SimpleGraph SimpleGraph.Walk MeasureTheory

set_option linter.unusedSectionVars false

namespace RestorableTiebreaking

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}

/-! ### Small perturbations -/

/-- If `|r| ≤ ε` on darts with `(2n - 1) ε < 1` (e.g. `ε ≤ 1/(2n)`), a shortest walk of `G \ A`
that is strictly lighter in `G*` than every other shortest walk of `G \ A` is the unique lightest
walk of `G* \ A` (perturbations never make a longer walk lighter). -/
theorem isMinWalk_of_unique {r : V → V → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hεn : (2 * Fintype.card V - 1) * ε < 1) (hr : ∀ u v, G.Adj u v → |r u v| ≤ ε)
    {A : Set (Sym2 V)} {s t : V} {p : G.Walk s t} (hpSh : p.IsShortestIn A)
    (hmin : ∀ q : G.Walk s t, q.IsShortestIn A → q ≠ p → p.dwt (wstar r) < q.dwt (wstar r)) :
    IsMinWalk G r A p := by
  set D := p.length
  refine ⟨hpSh.1, fun q hq hne => ?_⟩
  by_cases hqD : q.length = D
  · exact hmin q ⟨hq, by rw [hqD, hpSh.2]⟩ hne
  · -- `q` is longer, hence heavier
    have hDq : D + 1 ≤ q.length := by
      have := hq.edist_le
      rw [← hpSh.2] at this
      have : D ≤ q.length := by exact_mod_cast this
      omega
    have hDn : D + 1 ≤ Fintype.card V := hpSh.isPath.length_lt
    have hup := p.dwt_le_length_mul (wstar r) (c := 1 + ε) fun a b hab => by
      simp only [wstar]; linarith [(abs_le.mp (hr a b hab)).2]
    have hlo := q.length_mul_le_dwt (wstar r) (c := 1 - ε) fun a b hab => by
      simp only [wstar]; linarith [(abs_le.mp (hr a b hab)).1]
    have hDq' : ((D : ℝ) + 1) ≤ q.length := by exact_mod_cast hDq
    have hDn' : ((D : ℝ) + 1) ≤ Fintype.card V := by exact_mod_cast hDn
    have h2D : (2 * (D : ℝ) + 1) * ε ≤ (2 * Fintype.card V - 1) * ε :=
      mul_le_mul_of_nonneg_right (by linarith) hε
    have hε1 : ε ≤ 1 := by
      have : (1 : ℝ) * ε ≤ (2 * Fintype.card V - 1) * ε :=
        mul_le_mul_of_nonneg_right (by linarith) hε
      linarith
    have : ((D : ℝ) + 1) * (1 - ε) ≤ q.length * (1 - ε) :=
      mul_le_mul_of_nonneg_right hDq' (by linarith)
    nlinarith

/-- If moreover distinct shortest walks of `G \ A` have distinct `G*`-weights, then `G* \ A` has
unique shortest walks, which are shortest in `G \ A`. -/
theorem hasMinWalks_of_generic {r : V → V → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hεn : (2 * Fintype.card V - 1) * ε < 1) (hr : ∀ u v, G.Adj u v → |r u v| ≤ ε)
    (A : Set (Sym2 V))
    (hgen : ∀ s t (p q : G.Walk s t), p.IsShortestIn A → q.IsShortestIn A → p ≠ q →
      p.dwt (wstar r) ≠ q.dwt (wstar r)) :
    HasMinWalks G r A := by
  classical
  intro s t hst
  obtain ⟨p₀, hp₀⟩ := exists_isShortestIn hst
  let S : Set (G.Walk s t) := {p | p.length = p₀.length ∧ p.Avoids A}
  have hSfin : S.Finite :=
    (Set.toFinite {p : G.Walk s t | p.length = p₀.length}).subset fun p hp => hp.1
  obtain ⟨p, hpS, hpmin⟩ := Set.exists_min_image S (fun p => p.dwt (wstar r)) hSfin
    ⟨p₀, rfl, hp₀.1⟩
  have hpSh : p.IsShortestIn A := ⟨hpS.2, by rw [hpS.1, hp₀.2]⟩
  refine ⟨p, isMinWalk_of_unique hε hεn hr hpSh fun q hq hne => ?_, hpSh⟩
  have hqS : q ∈ S := ⟨by have := hq.2.trans hp₀.2.symm; exact_mod_cast this, hq.1⟩
  exact lt_of_le_of_ne (hpmin q hqS) (hgen s t p q hpSh hq (Ne.symm hne))

/-! ### Coefficient vectors -/

section Order

variable [LinearOrder V]

/-- Orientation sign of a dart w.r.t. the linear order on `V`. -/
def sgn (a b : V) : ℤ := if a < b then 1 else -1

lemma sgn_antisymm {a b : V} (h : a ≠ b) : sgn a b = - sgn b a := by
  unfold sgn
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [h', not_lt_of_gt h']
  · simp [h', not_lt_of_gt h']

/-- The antisymmetric weight function `r(u, v) = sgn(u, v) · ρ({u, v})`. -/
def rOf (ρ : Sym2 V → ℝ) : V → V → ℝ := fun a b => (sgn a b : ℝ) * ρ s(a, b)

lemma rOf_antisymm (ρ : Sym2 V → ℝ) {u v : V} (h : G.Adj u v) : rOf ρ u v = - rOf ρ v u := by
  simp only [rOf, sgn_antisymm h.ne, Int.cast_neg, Sym2.eq_swap]; ring

lemma abs_rOf_le (ρ : Sym2 V → ℝ) {ε : ℝ} (hρ : ∀ e, |ρ e| ≤ ε) (u v : V) :
    |rOf ρ u v| ≤ ε := by
  simp only [rOf, abs_mul]
  have : |(sgn u v : ℝ)| = 1 := by unfold sgn; split_ifs <;> simp
  rw [this, one_mul]; exact hρ _

/-- Signed number of traversals of the edge `e` by a walk. -/
def cnt {s t : V} (p : G.Walk s t) (e : Sym2 V) : ℤ :=
  ((p.darts.filter fun d => d.edge = e).map fun d => sgn d.fst d.snd).sum

lemma dwt_rOf_eq {s t : V} (ρ : Sym2 V → ℝ) (p : G.Walk s t) :
    p.dwt (wstar (rOf ρ)) = p.length + ∑ e, (cnt p e : ℝ) * ρ e := by
  induction p with
  | nil => simp [cnt]
  | @cons a b c hab q ih =>
    rw [dwt_cons, ih, length_cons]
    have : ∀ e, (cnt (cons hab q) e : ℝ) =
        (if s(a, b) = e then (sgn a b : ℝ) else 0) + cnt q e := by
      intro e
      by_cases h : s(a, b) = e
      · simp [cnt, darts_cons, Dart.edge, h]
      · simp [cnt, darts_cons, Dart.edge, h]
    simp only [this, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
      wstar, rOf]
    push_cast; ring

private lemma filter_edge_eq_singleton :
    ∀ (L : List G.Dart), (L.map Dart.edge).Nodup → ∀ d ∈ L,
      L.filter (fun x => x.edge = d.edge) = [d]
  | [], _, d, hd => by simp at hd
  | x :: L, hn, d, hd => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hd with rfl | hd
    · rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.mpr]
      intro y hy hye
      exact hn.1 (by simpa using ⟨y, hy, of_decide_eq_true hye⟩)
    · have hxe : x.edge ≠ d.edge := fun h => hn.1 (h ▸ List.mem_map_of_mem hd)
      rw [List.filter_cons_of_neg (by simpa using hxe)]
      exact filter_edge_eq_singleton L hn.2 d hd

lemma cnt_of_mem {s t : V} {p : G.Walk s t} (hp : p.IsPath) {d : G.Dart} (hd : d ∈ p.darts) :
    cnt p d.edge = sgn d.fst d.snd := by
  have hn : (p.darts.map Dart.edge).Nodup := by
    rw [← edges]; exact hp.isTrail.edges_nodup
  simp [cnt, filter_edge_eq_singleton _ hn d hd]

lemma cnt_of_not_mem {s t : V} {p : G.Walk s t} {e : Sym2 V} (he : e ∉ p.edges) : cnt p e = 0 := by
  simp only [cnt]
  rw [List.filter_eq_nil_iff.mpr]
  · simp
  · intro d hd hde
    exact he (by rw [edges]; exact List.mem_map.mpr ⟨d, hd, of_decide_eq_true hde⟩)

lemma abs_sgn_le (a b : V) : |sgn a b| ≤ 1 := by unfold sgn; split_ifs <;> simp

/-- Two distinct shortest `s ⇝ t` walks of `G \ A`: the coefficient vector of their weight
difference is nonzero with entries in `{-1, 0, 1}`. -/
lemma coeff_of_ne {A : Set (Sym2 V)} {s t : V} {p q : G.Walk s t} (hp : p.IsShortestIn A)
    (hq : q.IsShortestIn A) (hne : p ≠ q) :
    (∀ e, |cnt p e - cnt q e| ≤ 1) ∧ (fun e => cnt p e - cnt q e) ≠ 0 := by
  have key : ∀ e, (e ∈ p.edges ∧ e ∈ q.edges → cnt p e = cnt q e) := by
    rintro e ⟨hep, heq⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hep
    obtain ⟨d', hd', hdd'⟩ := List.mem_map.mp heq
    have := hp.dart_eq_of_edge_eq hq hd hd' hdd'.symm
    subst this
    rw [cnt_of_mem hp.isPath hd, cnt_of_mem hq.isPath hd']
  have hval : ∀ {s' t'} (p' : G.Walk s' t'), p'.IsPath → ∀ e, cnt p' e = 0 ∨ |cnt p' e| = 1 := by
    intro s' t' p' hp' e
    by_cases he : e ∈ p'.edges
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      right; rw [cnt_of_mem hp' hd]; unfold sgn; split_ifs <;> simp
    · left; exact cnt_of_not_mem he
  refine ⟨fun e => ?_, fun h0 => ?_⟩
  · by_cases hep : e ∈ p.edges <;> by_cases heq : e ∈ q.edges
    · rw [key e ⟨hep, heq⟩]; simp
    · rw [cnt_of_not_mem heq, sub_zero]
      rcases hval p hp.isPath e with h | h <;> rw [h] <;> simp
    · rw [cnt_of_not_mem hep, zero_sub, abs_neg]
      rcases hval q hq.isPath e with h | h <;> rw [h] <;> simp
    · rw [cnt_of_not_mem hep, cnt_of_not_mem heq]; simp
  · obtain ⟨e, hep, heq⟩ := hp.exists_mem_edges_not_mem hq hne
    have h1 := congrFun h0 e
    simp only [Pi.zero_apply, cnt_of_not_mem heq, sub_zero] at h1
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hep
    rw [cnt_of_mem hp.isPath hd] at h1
    unfold sgn at h1; split_ifs at h1 <;> simp at h1

/-- If no nonzero `{-1, 0, 1}`-combination of the values of `ρ` vanishes, then distinct shortest
walks of `G \ A` (for every `A`) get distinct `G*`-weights under `rOf ρ`. -/
lemma generic_of_coeff {ρ : Sym2 V → ℝ}
    (hρ : ∀ c : Sym2 V → ℤ, (∀ e, |c e| ≤ 1) → c ≠ 0 → ∑ e, (c e : ℝ) * ρ e ≠ 0)
    (A : Set (Sym2 V)) (s t : V) (p q : G.Walk s t) (hp : p.IsShortestIn A)
    (hq : q.IsShortestIn A) (hne : p ≠ q) :
    p.dwt (wstar (rOf ρ)) ≠ q.dwt (wstar (rOf ρ)) := by
  intro h
  obtain ⟨h1, h2⟩ := coeff_of_ne hp hq hne
  apply hρ _ h1 h2
  rw [dwt_rOf_eq, dwt_rOf_eq] at h
  have hlen : p.length = q.length := by
    have := hp.2.trans hq.2.symm; exact_mod_cast this
  rw [hlen] at h
  simp only [Int.cast_sub, sub_mul, sum_sub_distrib]
  linarith

/-- Generic `ρ` with `|ρ| ≤ ε < 1/(2n)` give ATW functions for every `f`. -/
theorem isATW_of_coeff {ρ : Sym2 V → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hεn : (2 * Fintype.card V - 1) * ε < 1) (hρε : ∀ e, |ρ e| ≤ ε)
    (hρ : ∀ c : Sym2 V → ℤ, (∀ e, |c e| ≤ 1) → c ≠ 0 → ∑ e, (c e : ℝ) * ρ e ≠ 0) (f : ℕ) :
    IsATW G f (rOf ρ) :=
  ⟨fun _ _ h => rOf_antisymm ρ h, fun _ _ =>
    hasMinWalks_of_generic hε hεn (fun u v _ => abs_rOf_le ρ hρε u v) _
      (generic_of_coeff hρ _)⟩

/-! ### Theorem 23: deterministic weights -/

/-- Signed binary expansions are unique: `∑_{j<N} c_j 2^j = 0` with `c_j ∈ {-1, 0, 1}` forces
`c = 0`. -/
lemma signed_binary_eq_zero (c : ℕ → ℤ) (hc : ∀ j, |c j| ≤ 1) :
    ∀ N, ∑ j ∈ range N, c j * 2 ^ j = 0 → ∀ j < N, c j = 0 := by
  have hbound : ∀ N, |∑ j ∈ range N, c j * 2 ^ j| ≤ 2 ^ N - 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      calc |∑ j ∈ range N, c j * 2 ^ j + c N * 2 ^ N|
          ≤ |∑ j ∈ range N, c j * 2 ^ j| + |c N * 2 ^ N| := abs_add_le _ _
        _ ≤ (2 ^ N - 1) + 2 ^ N := by
          gcongr
          rw [abs_mul, abs_pow, abs_two]
          nlinarith [hc N, pow_pos (two_pos : (0 : ℤ) < 2) N]
        _ = 2 ^ (N + 1) - 1 := by ring
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    intro hsum j hj
    rw [sum_range_succ] at hsum
    have hcN : c N = 0 := by
      by_contra hne
      have h1 : 1 ≤ |c N| := Int.one_le_abs hne
      have h2 := hbound N
      have : |∑ j ∈ range N, c j * 2 ^ j| = |c N| * 2 ^ N := by
        rw [eq_neg_of_add_eq_zero_left hsum, abs_neg, abs_mul, abs_pow, abs_two]
      nlinarith [pow_pos (two_pos : (0 : ℤ) < 2) N]
    rw [hcN, zero_mul, add_zero] at hsum
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih hsum j hj
    · exact hcN

/-- The deterministic weights of Theorem 23 (with `C = 2`): `ρ(e) = 2^{-i(e)} / (2n)` where
`i(e) = N - id(e) ∈ {1, …, N}` is an arbitrary numbering of the `N` unordered pairs. -/
noncomputable def detRho {N : ℕ} (id : Sym2 V ≃ Fin N) (e : Sym2 V) : ℝ :=
  (2 : ℝ)⁻¹ ^ (N - (id e : ℕ)) / (2 * Fintype.card V)

/-- **Theorem 23 of [Bodwin–Parter]** (existence part). For any numbering of the edges, the
weights `r(u, v) = sgn(u, v) · 2^{-i(uv)} / (2n)` form an antisymmetric `f`-fault tiebreaking
weight function, for every `f`. -/
theorem theorem23 {N : ℕ} (id : Sym2 V ≃ Fin N) (f : ℕ) : IsATW G f (rOf (detRho id)) := by
  set n := Fintype.card V
  refine isATW_of_coeff (ε := 1 / (4 * n)) (by positivity) ?_ ?_ ?_ f
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp
      have : ((Fintype.card V : ℕ) : ℝ) = n := rfl
      rw [this]; linarith
  · intro e
    rw [detRho, abs_of_nonneg (by positivity)]
    have hk : 1 ≤ N - (id e : ℕ) := by have := (id e).2; omega
    have : (2 : ℝ)⁻¹ ^ (N - (id e : ℕ)) ≤ 2⁻¹ :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [n] at hn; simp [hn]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  · intro c hc hc0 hsum
    apply hc0
    -- reduce to a signed binary expansion
    have hpos : (0 : ℝ) < 2 ^ N * (2 * n) ∨ n = 0 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · right; exact hn
      · left; have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
    rcases hpos with hpos | hn0
    · have hint : ∑ e, c e * (2 : ℤ) ^ (id e : ℕ) = 0 := by
        have h2 : ∀ e : Sym2 V, (2 : ℝ)⁻¹ ^ (N - (id e : ℕ)) =
            (2 : ℝ) ^ (id e : ℕ) / 2 ^ N := by
          intro e
          have hle : (id e : ℕ) ≤ N := (id e).2.le
          generalize (id e : ℕ) = k at hle ⊢
          obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
          rw [Nat.add_sub_cancel_left, pow_add, inv_pow]
          field_simp
        simp only [detRho, h2] at hsum
        have : ∑ e, (c e : ℝ) * ((2 : ℝ) ^ (id e : ℕ)) = 0 := by
          have hk : ∑ e, (c e : ℝ) * ((2 : ℝ) ^ (id e : ℕ) / 2 ^ N / (2 * n)) =
              (∑ e, (c e : ℝ) * (2 : ℝ) ^ (id e : ℕ)) / (2 ^ N * (2 * n)) := by
            rw [sum_div]; congr 1; ext e; field_simp
          rw [hk, div_eq_zero_iff] at hsum
          exact hsum.resolve_right hpos.ne'
        exact_mod_cast this
      -- reindex along `id`
      let c' : ℕ → ℤ := fun j => if h : j < N then c (id.symm ⟨j, h⟩) else 0
      have hc' : ∀ j, |c' j| ≤ 1 := by
        intro j; simp only [c']; split_ifs
        · exact hc _
        · simp
      have hsum' : ∑ j ∈ range N, c' j * 2 ^ j = 0 := by
        rw [← hint, ← Fin.sum_univ_eq_sum_range (fun j => c' j * 2 ^ j)]
        rw [← Equiv.sum_comp id.symm]
        refine sum_congr rfl fun j _ => ?_
        simp [c', j.2]
      have := signed_binary_eq_zero c' hc' N hsum'
      ext e
      have h := this (id e) (id e).2
      simpa [c'] using h
    · -- no vertices: `Sym2 V` is empty
      ext e
      exfalso
      have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
      exact (Sym2.ind (fun a _ => this.elim a) e : False)

end Order

/-! ### Theorem 2: the main result -/

/-- **Theorem 2 of [Bodwin–Parter]** (main result, all fault-set sizes at once). Every finite graph
has a single replacement path tiebreaking scheme `π` which, for every `f`, is an `f`-RPTS that is
consistent, stable and `f`-restorable. -/
theorem theorem2 (G : SimpleGraph V) :
    ∃ π : Scheme G, ∀ f, IsRPTS G f π ∧ IsConsistent G f π ∧ IsStable G f π ∧
      IsRestorable G f π := by
  let : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  refine ⟨atwScheme G (rOf (detRho (Fintype.equivFin (Sym2 V)))), fun f => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := theorem19 (theorem23 (G := G) (Fintype.equivFin (Sym2 V)) f)
  exact ⟨h1, h3, h2, h4⟩

/-- **Theorem 2 of [Bodwin–Parter]**, the paper's one-fault phrasing: one can select a single
shortest path `π(s, t)` for each ordered pair such that for every pair `s, t` and failing edge `e`
with `s, t` still connected in `G \ {e}`, some `π(s, x) ∘ π(t, x)⁻¹` is a shortest `s ⇝ t` path
of `G \ {e}`. -/
theorem theorem2_single (G : SimpleGraph V) :
    ∃ π : ∀ s t : V, Option (G.Walk s t),
      (∀ s t p, π s t = some p → p.IsShortestIn (∅ : Set (Sym2 V))) ∧
      (∀ s t, G.Reachable s t → (π s t).isSome) ∧
      ∀ (s t : V) (e : Sym2 V), (G.deleteEdges {e}).Reachable s t →
        ∃ (x : V) (p : G.Walk s x) (q : G.Walk t x), π s x = some p ∧ π t x = some q ∧
          (p.append q.reverse).IsShortestIn {e} := by
  obtain ⟨π, hπ⟩ := theorem2 G
  obtain ⟨h1, -, -, h4⟩ := hπ 1
  refine ⟨π ∅, fun s t p hp => by simpa using (h1 ∅ (by simp)).1 s t p hp,
    fun s t hst => (h1 ∅ (by simp)).2 s t (by simpa using hst), fun s t e hst => ?_⟩
  obtain ⟨F', hF', x, p, q, hp, hq, hW⟩ := h4 {e} (by simp) (by simp) s t (by simpa using hst)
  have : F' = ∅ := by
    rcases Finset.subset_singleton_iff.mp hF'.subset with h | h
    · exact h
    · exact absurd h hF'.ne
  subst this
  exact ⟨x, p, q, hp, hq, by simpa using hW⟩

end RestorableTiebreaking
